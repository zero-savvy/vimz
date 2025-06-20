use std::{
    collections::{HashMap, HashSet},
    time::Duration,
};

use ark_bn254::Fr;
use clap::{Parser, ValueEnum};
use comfy_table::{Table, presets::UTF8_FULL};
use nova_scotia::{FileLocation, circom::reader::load_r1cs};
use paste::paste;
use rand::{SeedableRng, prelude::StdRng};
use sonobe::arith::Arith;
use vimz::{
    config::{
        Backend, Config,
        Frontend::{Arkworks, Circom},
        parse_image,
    },
    nova_snark_backend::{G1, G2, folding::verify_folded_proof, input::PreparedInputs},
    sonobe_backend::{
        circuits::{SonobeCircuit, arkworks::*, circom::*},
        folding::{fold_input, prepare_folding, verify_final_state_arkworks, verify_folding},
        input::prepare_input,
    },
    transformation::{Resolution, Transformation, Transformation::*},
};

macro_rules! circuit_match {
    (
        $pipeline:expr,
        $transformation:expr,
        $cli_config:expr,
        $stats:expr;
        $( $variant:ident ),* $(,)?
    ) => {
    paste! {
        use Pipeline::*;
        let config = config($transformation, $pipeline);

        println!(
            "Folding `{:?}` transformation with {:?}",
            $transformation, $pipeline
        );

        match $pipeline {
            NovaRsCircom => run_nova(&config, $pipeline, $cli_config.comparison, $stats),
            SonobeCircom => {
                match $transformation {
                $(Transformation::$variant => {
                    run_sonobe::<[<$variant CircomCircuit>]>(&config, $pipeline, $cli_config.comparison, $stats)
                }),*
                }
            },
            SonobeArkworks => {
                match $transformation {
                $(Transformation::$variant => {
                    run_sonobe::<[<$variant ArkworksCircuit>]<Fr>>(&config, $pipeline, $cli_config.comparison, $stats)
                }),*
            }
            },
        }
    }
    };
}

const ALL_TRANSFORMATIONS: [Transformation; 9] = [
    Blur, Brightness, Contrast, Crop, Grayscale, Hash, Redact, Resize, Sharpness,
];

#[derive(Copy, Clone, Debug, Default, Eq, PartialEq, ValueEnum)]
enum Comparison {
    #[default]
    All,
    FoldingTime,
    CircuitSize,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, ValueEnum)]
enum Pipeline {
    NovaRsCircom,
    SonobeCircom,
    SonobeArkworks,
}

#[derive(Parser)]
#[clap(about = "
Comparing the performance between different folding pipelines.

When comparing folding times, we will:
   1) prepare the folding (preprocessing, key generation)
   2) run {DEMO_STEPS} folding steps
   3) verify the folding proof
We DO NOT run proof compression.

When comparing circuit sizes, we will:
   1) generate the circuit
   2) measure the number of constraints and variables")]
struct CLIConfig {
    /// Which pipeline to run first?
    first_pipeline: Pipeline,
    /// Which pipeline to run second for comparison? If not specified, only the first pipeline will be run.
    second_pipeline: Option<Pipeline>,
    /// What to compare?
    #[clap(long, short, value_enum, default_value_t = Comparison::default())]
    comparison: Comparison,
    /// What transformations to run? If not specified, all transformations will be run.
    #[clap(long, short)]
    transformation: Option<Transformation>,
}

#[derive(Debug, Default)]
struct Stats {
    folding_times: HashMap<(Pipeline, Transformation), Duration>,
    constraint_number: HashMap<(Pipeline, Transformation), usize>,
    variable_number: HashMap<(Pipeline, Transformation), usize>,
}

fn main() {
    let cli_config = CLIConfig::parse();

    let transformations = cli_config
        .transformation
        .map_or(ALL_TRANSFORMATIONS.to_vec(), |t| vec![t]);

    let pipelines = Some(cli_config.first_pipeline)
        .into_iter()
        .chain(cli_config.second_pipeline);

    let mut stats = Stats::default();
    for p in pipelines {
        for t in &transformations {
            circuit_match!(
                p, *t, cli_config, &mut stats;
                Blur, Brightness, Contrast, Crop, Grayscale, Hash, Redact, Resize, Sharpness
            );
        }
    }
    present_stats(&cli_config, &stats);
}

fn config(transformation: Transformation, pipeline: Pipeline) -> Config {
    let path = |s: String| s.to_lowercase().into();

    let target_image = if transformation == Hash {
        None
    } else {
        Some(parse_image(&format!("../input_data/{transformation:?}.png").to_lowercase()).unwrap())
    };

    let (backend, frontend) = match pipeline {
        Pipeline::NovaRsCircom => (Backend::NovaSnark, Circom),
        Pipeline::SonobeCircom => (Backend::Sonobe, Circom),
        Pipeline::SonobeArkworks => (Backend::Sonobe, Arkworks),
    };

    let subdir = match pipeline {
        Pipeline::NovaRsCircom => "nova_snark",
        _ => "sonobe",
    };

    Config::new(
        path(format!("../input_data/{transformation:?}.json")),
        None,
        path(format!("../circuits/{subdir}/{transformation:?}_step.r1cs")),
        path(format!(
            "../circuits/{subdir}/{transformation:?}_step_js/{transformation:?}_step.wasm"
        )),
        transformation,
        Resolution::HD,
        backend,
        frontend,
        true,
        Some(parse_image("../source_image/HD.png").unwrap()),
        target_image,
    )
}

fn run_nova(config: &Config, pipeline: Pipeline, comparison: Comparison, stats: &mut Stats) {
    let PreparedInputs {
        ivc_step_inputs,
        initial_state,
        secondary_initial_state,
    } = vimz::nova_snark_backend::input::prepare_input(config);
    let num_steps = ivc_step_inputs.len();

    if comparison == Comparison::CircuitSize || comparison == Comparison::All {
        let r1cs = load_r1cs::<G1, G2>(&FileLocation::PathBuf(config.circuit_file()));
        stats
            .constraint_number
            .insert((pipeline, config.function), r1cs.constraints.len());
        stats
            .variable_number
            .insert((pipeline, config.function), r1cs.num_variables);
    }

    if comparison == Comparison::FoldingTime || comparison == Comparison::All {
        // ========================== Prepare input and folding ========================================
        let start = std::time::Instant::now();
        let (r1cs, folding_params) = vimz::nova_snark_backend::folding::prepare_folding(config);
        println!("  Circuit preparation took: {:?}", start.elapsed());

        // ========================== Run folding steps ================================================
        let start = std::time::Instant::now();
        let proof = vimz::nova_snark_backend::folding::fold_input(
            config,
            r1cs,
            ivc_step_inputs,
            initial_state.clone(),
            &folding_params,
        );
        let folding_time = start.elapsed();
        println!("  Folding took: {:?}", folding_time);
        stats
            .folding_times
            .insert((pipeline, config.function), folding_time);

        // ========================== Verify folding proof ============================================
        let start = std::time::Instant::now();
        verify_folded_proof(
            &proof,
            &folding_params,
            num_steps,
            &initial_state,
            &secondary_initial_state,
        );
        println!("  Verification took: {:?}", start.elapsed());
    }
}

fn run_sonobe<Circuit: SonobeCircuit>(
    config: &Config,
    pipeline: Pipeline,
    comparison: Comparison,
    stats: &mut Stats,
) {
    if comparison == Comparison::FoldingTime || comparison == Comparison::All {
        let folding_time = run_sonobe_folding::<Circuit>(config);
        stats
            .folding_times
            .insert((pipeline, config.function), folding_time);
    }

    if comparison == Comparison::CircuitSize || comparison == Comparison::All {
        let (constraints, variables) = build_sonobe_circuit::<Circuit>(config);
        stats
            .constraint_number
            .insert((pipeline, config.function), constraints);
        stats
            .variable_number
            .insert((pipeline, config.function), variables);
    }
}

fn run_sonobe_folding<Circuit: SonobeCircuit>(config: &Config) -> Duration {
    let mut rng = StdRng::from_seed([41; 32]);

    // ========================== Prepare input and folding ========================================
    let start = std::time::Instant::now();
    let (ivc_step_inputs, initial_state) = prepare_input(config);
    let (mut folding, folding_params) =
        prepare_folding::<Circuit>(config, initial_state.clone(), &mut rng);
    println!("  Circuit preparation took: {:?}", start.elapsed());

    // ========================== Run folding steps ================================================
    let start = std::time::Instant::now();
    fold_input(&mut folding, ivc_step_inputs, &mut rng);
    let folding_duration = start.elapsed();
    println!("  Folding took: {:?}", folding_duration);

    // ========================== Verify folding proof ============================================
    let start = std::time::Instant::now();
    verify_folding(&folding, &folding_params);
    println!("  Verification took: {:?}", start.elapsed());

    // ========================== Verify final state (if applicable) ==============================
    if config.frontend == Arkworks {
        verify_final_state_arkworks(&folding, config);
        println!("  Final state verified successfully.");
    }

    println!();
    folding_duration
}

fn build_sonobe_circuit<Circuit: SonobeCircuit>(config: &Config) -> (usize, usize) {
    let mut rng = StdRng::from_seed([41; 32]);

    let (_, initial_state) = prepare_input(config);
    let start = std::time::Instant::now();
    let (folding, _) = prepare_folding::<Circuit>(config, initial_state.clone(), &mut rng);
    println!("  Circuit preparation took: {:?}", start.elapsed());

    (folding.r1cs.n_constraints(), folding.r1cs.n_variables())
}

fn present_stats(cliconfig: &CLIConfig, stats: &Stats) {
    let mut all_transformations = HashSet::new();
    all_transformations.extend(stats.folding_times.keys().map(|&(_, t)| t));
    all_transformations.extend(stats.constraint_number.keys().map(|&(_, t)| t));
    all_transformations.extend(stats.variable_number.keys().map(|&(_, t)| t));

    if all_transformations.is_empty() {
        println!("No stats to display.");
        return;
    }

    let mut rows = Vec::new();

    let fp = cliconfig.first_pipeline;
    let sp = cliconfig.second_pipeline.unwrap_or(fp);

    for t in all_transformations {
        let fp_time = stats.folding_times.get(&(fp, t));
        let sp_time = stats.folding_times.get(&(sp, t));

        let fp_time_s = fp_time.map(|d| d.as_secs_f64());
        let sp_time_s = sp_time.map(|d| d.as_secs_f64());
        let delta_time_pct = match (fp_time_s, sp_time_s) {
            (Some(c), Some(a)) => Some((a / c - 1.0) * 100.0),
            _ => None,
        };

        let fp_constr = stats.constraint_number.get(&(fp, t)).copied();
        let sp_constr = stats.constraint_number.get(&(sp, t)).copied();
        let delta_constr_pct = match (fp_constr, sp_constr) {
            (Some(c), Some(a)) if c > 0 => Some((a as f64 / c as f64 - 1.0) * 100.0),
            _ => None,
        };

        let fp_vars = stats.variable_number.get(&(fp, t)).copied();
        let sp_vars = stats.variable_number.get(&(sp, t)).copied();
        let delta_vars_pct = match (fp_vars, sp_vars) {
            (Some(c), Some(a)) if c > 0 => Some((a as f64 / c as f64 - 1.0) * 100.0),
            _ => None,
        };

        let mut cells = vec![format!("{t:?}")];

        if let Some(x) = fp_time_s {
            cells.push(format!("{x:.3}"));
            if fp != sp {
                cells.push(format!("{:.3}", sp_time_s.unwrap()));
                cells.push(format!("{:+.1}%", delta_time_pct.unwrap()));
            }
        }

        if let Some(x) = fp_constr {
            cells.push(x.to_string());
            if fp != sp {
                cells.push(sp_constr.unwrap().to_string());
                cells.push(format!("{:+.1}%", delta_constr_pct.unwrap()));
            }
        }

        if let Some(x) = fp_vars {
            cells.push(x.to_string());
            if fp != sp {
                cells.push(sp_vars.unwrap().to_string());
                cells.push(format!("{:+.1}%", delta_vars_pct.unwrap()));
            }
        }

        rows.push(cells);
    }

    // Sort rows alphabetically by transformation name
    rows.sort_by(|a, b| a[0].cmp(&b[0]));

    // Build table
    let mut table = Table::new();

    let mut header = vec!["Transformation".into()];

    if stats.folding_times.keys().any(|(p, _)| *p == fp) {
        header.push(format!("{fp:?} Time (s)"));
        if fp != sp {
            header.push(format!("{sp:?} Time (s)"));
            header.push("Δ Time (%)".into());
        }
    }

    if stats.constraint_number.keys().any(|(p, _)| *p == fp) {
        header.push(format!("{fp:?} Constraints"));
        if fp != sp {
            header.push(format!("{sp:?} Constraints"));
            header.push("Δ Constraints (%)".into());
        }
    }

    if stats.variable_number.keys().any(|(p, _)| *p == fp) {
        header.push(format!("{fp:?} Variables"));
        if fp != sp {
            header.push(format!("{sp:?} Variables"));
            header.push("Δ Variables (%)".into());
        }
    }

    table.load_preset(UTF8_FULL).set_header(header);

    for row in rows {
        table.add_row(row);
    }

    println!("\nCircuit Benchmark Summary:");
    println!("{table}");
}
