use std::{collections::HashMap, time::Duration};

use ark_bn254::Fr;
use comfy_table::{presets::UTF8_FULL, Table};
use rand::{prelude::StdRng, SeedableRng};
use vimz::{
    config::{
        Backend, Config, Frontend,
        Frontend::{Arkworks, Circom},
    },
    sonobe_backend::{
        circuits::{arkworks::*, circom::*, SonobeCircuit},
        folding::{fold_input, prepare_folding, verify_folding},
        input::prepare_input,
    },
    transformation::{Resolution, Transformation, Transformation::*},
    DEMO_STEPS,
};

const TRANSFORMATIONS: [Transformation; 9] = [
    Blur, Brightness, Contrast, Crop, Grayscale, Hash, Redact, Resize, Sharpness,
];

type Stat = (Transformation, Frontend, Duration);

fn main() {
    print_bin_info();

    let mut stats = vec![];
    for t in TRANSFORMATIONS {
        let (cir, ark) = match t {
            Blur => (
                run::<BlurCircomCircuit>(&config(t, Circom)),
                run::<BlurArkworksCircuit<Fr>>(&config(t, Arkworks)),
            ),
            Brightness => (
                run::<BrightnessCircomCircuit>(&config(t, Circom)),
                run::<BrightnessArkworksCircuit<Fr>>(&config(t, Arkworks)),
            ),
            Contrast => (
                run::<ContrastCircomCircuit>(&config(t, Circom)),
                run::<ContrastArkworksCircuit<Fr>>(&config(t, Arkworks)),
            ),
            Crop => (
                run::<CropCircomCircuit>(&config(t, Circom)),
                run::<CropArkworksCircuit<Fr>>(&config(t, Arkworks)),
            ),
            Grayscale => (
                run::<GrayscaleCircomCircuit>(&config(t, Circom)),
                run::<GrayscaleArkworksCircuit<Fr>>(&config(t, Arkworks)),
            ),
            Hash => (
                run::<HashCircomCircuit>(&config(t, Circom)),
                run::<HashArkworksCircuit<Fr>>(&config(t, Arkworks)),
            ),
            Redact => (
                run::<RedactCircomCircuit>(&config(t, Circom)),
                run::<RedactArkworksCircuit<Fr>>(&config(t, Arkworks)),
            ),
            Resize => (
                run::<ResizeCircomCircuit>(&config(t, Circom)),
                run::<ResizeArkworksCircuit<Fr>>(&config(t, Arkworks)),
            ),
            Sharpness => (
                run::<SharpnessCircomCircuit>(&config(t, Circom)),
                run::<SharpnessArkworksCircuit<Fr>>(&config(t, Arkworks)),
            ),
        };

        stats.push((t, Frontend::Circom, cir));
        stats.push((t, Frontend::Arkworks, ark));
    }

    present_stats(stats);
}

fn print_bin_info() {
    println!(
        "
---------------------------------------------------------------------------------------------------------------------
This binary compares the performance between Circom and Arkworks frontends, when using Sonobe as the folding backend.

For every transformation in {TRANSFORMATIONS:?} we will:
   1) prepare the folding (preprocessing, key generation)
   2) run {DEMO_STEPS} folding steps
   3) verify the folding proof
We DO NOT run Sonobe's decider (neither preprocessing nor proof compression).
---------------------------------------------------------------------------------------------------------------------
"
    )
}

fn config(function: Transformation, frontend: Frontend) -> Config {
    let path = |s: String| s.to_lowercase().into();

    Config {
        input: path(format!("../input_data/{function:?}.json")),
        output: None,
        circuit: path(format!("../circuits/sonobe/{function:?}_step.r1cs")),
        witness_generator: path(format!(
            "../circuits/sonobe/{function:?}_step_js/{function:?}_step.wasm"
        )),
        function,
        resolution: Resolution::HD,
        backend: Backend::Sonobe,
        frontend,
        demo: true,
    }
}

fn run<Circuit: SonobeCircuit>(config: &Config) -> Duration {
    let mut rng = StdRng::from_seed([41; 32]);

    println!(
        "Running `{:?}` transformation with {:?} frontend",
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
    println!();

    folding_duration
}

fn present_stats(stats: Vec<Stat>) {
    // 1) Reorganize the stats
    let mut grouped: HashMap<Transformation, [Option<Duration>; 2]> = HashMap::new();
    for (t, f, d) in stats {
        let entry = grouped.entry(t).or_insert([None, None]);
        match f {
            Circom => entry[0] = Some(d),
            Arkworks => entry[1] = Some(d),
        }
    }

    // 2) Prepare the table
    let mut table = Table::new();
    table.load_preset(UTF8_FULL).set_header([
        "Transformation",
        "Circom (s)",
        "Arkworks (s)",
        "Δ Ark/Circ (%)",
    ]);

    // 3) Fill the table with data
    for (t, [cir_opt, ark_opt]) in grouped {
        let (cir, ark) = (cir_opt.unwrap(), ark_opt.unwrap());
        let cir_s = cir.as_secs_f64();
        let ark_s = ark.as_secs_f64();

        let delta_pct = (ark_s / cir_s - 1.0) * 100.0;

        table.add_row([
            format!("{t:?}"),
            format!("{cir_s:.3}"),
            format!("{ark_s:.3}"),
            format!("{delta_pct:+.1}%"),
        ]);
    }

    println!("{table}");
}
