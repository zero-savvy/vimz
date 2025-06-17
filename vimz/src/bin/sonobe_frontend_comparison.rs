use std::{
    collections::{HashMap, HashSet},
    time::Duration,
};

use ark_bn254::Fr;
use clap::{Parser, ValueEnum};
use comfy_table::{Table, presets::UTF8_FULL};
use paste::paste;
use rand::{SeedableRng, prelude::StdRng};
use sonobe::arith::Arith;
use vimz::{
    config::{
        Backend, Config, Frontend,
        Frontend::{Arkworks, Circom},
        parse_image,
    },
    sonobe_backend::{
        circuits::{SonobeCircuit, arkworks::*, circom::*},
        folding::{fold_input, prepare_folding, verify_final_state_arkworks, verify_folding},
        input::prepare_input,
    },
    transformation::{Resolution, Transformation, Transformation::*},
};

macro_rules! circuit_match {
    (
        $t:expr,
        $cli_config:expr,
        $stats:expr;
        $( $variant:ident ),* $(,)?
    ) => {
    paste! {
        let cir_config = config($t, Circom);
        let ark_config = config($t, Arkworks);
        match $t {
            $(Transformation::$variant => (
                compare::<[<$variant CircomCircuit>]>      (&cir_config, $cli_config.comparison, $stats),
                compare::<[<$variant ArkworksCircuit>]<Fr>>(&ark_config, $cli_config.comparison, $stats),
            )),*
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

#[derive(Parser)]
#[clap(about = "
This binary compares the performance between Circom and Arkworks frontends, when using Sonobe as the folding backend.

When comparing folding times, we will:
   1) prepare the folding (preprocessing, key generation)
   2) run {DEMO_STEPS} folding steps
   3) verify the folding proof
We DO NOT run Sonobe's decider (neither preprocessing nor proof compression).

When comparing circuit sizes, we will:
   1) generate the circuit
   2) measure the number of constraints and variables")]
struct CLIConfig {
    /// What to compare?
    #[clap(value_enum, default_value_t = Comparison::default())]
    comparison: Comparison,
    /// What transformations to run? If not specified, all transformations will be run.
    transformation: Option<Transformation>,
}

#[derive(Debug, Default)]
struct Stats {
    folding_times: HashMap<(Frontend, Transformation), Duration>,
    constraint_number: HashMap<(Frontend, Transformation), usize>,
    variable_number: HashMap<(Frontend, Transformation), usize>,
}

fn main() {
    let cli_config = CLIConfig::parse();

    let transformations = cli_config
        .transformation
        .map_or(ALL_TRANSFORMATIONS.to_vec(), |t| vec![t]);

    let mut stats = Stats::default();
    for t in transformations {
        circuit_match!(
            t, cli_config, &mut stats;
            Blur, Brightness, Contrast, Crop, Grayscale, Hash, Redact, Resize, Sharpness
        );
    }

    present_stats(&stats);
}

fn config(transformation: Transformation, frontend: Frontend) -> Config {
    let path = |s: String| s.to_lowercase().into();

    let target_image = if transformation == Hash {
        None
    } else {
        Some(parse_image(&format!("../input_data/{transformation:?}.png").to_lowercase()).unwrap())
    };

    Config::new(
        path(format!("../input_data/{transformation:?}.json")),
        None,
        path(format!("../circuits/sonobe/{transformation:?}_step.r1cs")),
        path(format!(
            "../circuits/sonobe/{transformation:?}_step_js/{transformation:?}_step.wasm"
        )),
        transformation,
        Resolution::HD,
        Backend::Sonobe,
        frontend,
        true,
        Some(parse_image("../source_image/HD.png").unwrap()),
        target_image,
    )
}

fn compare<Circuit: SonobeCircuit>(config: &Config, comparison: Comparison, stats: &mut Stats) {
    if comparison == Comparison::FoldingTime || comparison == Comparison::All {
        let folding_time = run_folding::<Circuit>(config);
        stats
            .folding_times
            .insert((config.frontend, config.function), folding_time);
    }

    if comparison == Comparison::CircuitSize || comparison == Comparison::All {
        let (constraints, variables) = build_circuit::<Circuit>(config);
        stats
            .constraint_number
            .insert((config.frontend, config.function), constraints);
        stats
            .variable_number
            .insert((config.frontend, config.function), variables);
    }
}

fn run_folding<Circuit: SonobeCircuit>(config: &Config) -> Duration {
    let mut rng = StdRng::from_seed([41; 32]);

    println!(
        "Folding `{:?}` transformation with {:?} frontend",
        config.function, config.frontend
    );

    // ========================== Prepare input and folding ========================================
    let start = std::time::Instant::now();
    let (ivc_step_inputs, initial_state) = prepare_input(config);
    let (mut folding, folding_params) =
        prepare_folding::<Circuit>(config, initial_state.clone(), &mut rng);
    println!("  Preparation took: {:?}", start.elapsed());

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

fn build_circuit<Circuit: SonobeCircuit>(config: &Config) -> (usize, usize) {
    let mut rng = StdRng::from_seed([41; 32]);

    println!(
        "Building circuit for `{:?}` transformation with {:?} frontend\n",
        config.function, config.frontend
    );

    let (_, initial_state) = prepare_input(config);
    let (folding, _) = prepare_folding::<Circuit>(config, initial_state.clone(), &mut rng);

    (folding.r1cs.n_constraints(), folding.r1cs.n_variables())
}

fn present_stats(stats: &Stats) {
    let mut all_transformations = HashSet::new();
    all_transformations.extend(stats.folding_times.keys().map(|&(_, t)| t));
    all_transformations.extend(stats.constraint_number.keys().map(|&(_, t)| t));
    all_transformations.extend(stats.variable_number.keys().map(|&(_, t)| t));

    if all_transformations.is_empty() {
        println!("No stats to display.");
        return;
    }

    let mut rows = Vec::new();

    for t in all_transformations {
        let cir_time = stats.folding_times.get(&(Circom, t));
        let ark_time = stats.folding_times.get(&(Arkworks, t));

        let cir_time_s = cir_time.map(|d| d.as_secs_f64());
        let ark_time_s = ark_time.map(|d| d.as_secs_f64());
        let delta_time_pct = match (cir_time_s, ark_time_s) {
            (Some(c), Some(a)) => Some((a / c - 1.0) * 100.0),
            _ => None,
        };

        let cir_constr = stats.constraint_number.get(&(Circom, t)).copied();
        let ark_constr = stats.constraint_number.get(&(Arkworks, t)).copied();
        let delta_constr_pct = match (cir_constr, ark_constr) {
            (Some(c), Some(a)) if c > 0 => Some((a as f64 / c as f64 - 1.0) * 100.0),
            _ => None,
        };

        let cir_vars = stats.variable_number.get(&(Circom, t)).copied();
        let ark_vars = stats.variable_number.get(&(Arkworks, t)).copied();
        let delta_vars_pct = match (cir_vars, ark_vars) {
            (Some(c), Some(a)) if c > 0 => Some((a as f64 / c as f64 - 1.0) * 100.0),
            _ => None,
        };

        rows.push([
            format!("{t:?}"),
            cir_time_s.map_or("-".into(), |v| format!("{v:.3}")),
            ark_time_s.map_or("-".into(), |v| format!("{v:.3}")),
            delta_time_pct.map_or("-".into(), |v| format!("{v:+.1}%")),
            cir_constr.map_or("-".into(), |v| v.to_string()),
            ark_constr.map_or("-".into(), |v| v.to_string()),
            delta_constr_pct.map_or("-".into(), |v| format!("{v:+.1}%")),
            cir_vars.map_or("-".into(), |v| v.to_string()),
            ark_vars.map_or("-".into(), |v| v.to_string()),
            delta_vars_pct.map_or("-".into(), |v| format!("{v:+.1}%")),
        ]);
    }

    // Sort rows alphabetically by transformation name
    rows.sort_by(|a, b| a[0].cmp(&b[0]));

    // Build table
    let mut table = Table::new();
    table.load_preset(UTF8_FULL).set_header([
        "Transformation",
        "Circom Time (s)",
        "Arkworks Time (s)",
        "Δ Time (%)",
        "Circom Constraints",
        "Arkworks Constraints",
        "Δ Constraints (%)",
        "Circom Variables",
        "Arkworks Variables",
        "Δ Variables (%)",
    ]);

    for row in rows {
        table.add_row(row);
    }

    println!("\nCircuit Benchmark Summary:");
    println!("{table}");
}
