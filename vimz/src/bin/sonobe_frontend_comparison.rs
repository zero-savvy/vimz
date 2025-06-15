use std::{collections::HashMap, time::Duration};

use ark_bn254::Fr;
use comfy_table::{presets::UTF8_FULL, Table};
use vimz::{
    config::Frontend,
    sonobe_backend::circuits::{arkworks::*, circom::*, SonobeCircuit},
    transformation::{Transformation, Transformation::*},
    DEMO_STEPS,
};

const TRANSFORMATIONS: [Transformation; 8] = [
    Blur, Brightness, Contrast, // Crop,
    Grayscale, Hash, Redact, Resize, Sharpness,
];

type Stat = (Transformation, Frontend, Duration);

fn main() {
    print_bin_info();

    let mut stats = vec![];
    for t in TRANSFORMATIONS {
        let (cir, ark) = match t {
            Blur => (
                run_circom::<BlurCircomCircuit>(t),
                run_arkworks::<BlurArkworksCircuit<Fr>>(t),
            ),
            Brightness => (
                run_circom::<BrightnessCircomCircuit>(t),
                run_arkworks::<BrightnessArkworksCircuit<Fr>>(t),
            ),
            Contrast => (
                run_circom::<ContrastCircomCircuit>(t),
                run_arkworks::<ContrastArkworksCircuit<Fr>>(t),
            ),
            Crop => (
                run_circom::<CropCircomCircuit>(t),
                run_arkworks::<CropArkworksCircuit<Fr>>(t),
            ),
            Grayscale => (
                run_circom::<GrayscaleCircomCircuit>(t),
                run_arkworks::<GrayscaleArkworksCircuit<Fr>>(t),
            ),
            Hash => (
                run_circom::<HashCircomCircuit>(t),
                run_arkworks::<HashArkworksCircuit<Fr>>(t),
            ),
            Redact => (
                run_circom::<RedactCircomCircuit>(t),
                run_arkworks::<RedactArkworksCircuit<Fr>>(t),
            ),
            Resize => (
                run_circom::<ResizeCircomCircuit>(t),
                run_arkworks::<ResizeArkworksCircuit<Fr>>(t),
            ),
            Sharpness => (
                run_circom::<SharpnessCircomCircuit>(t),
                run_arkworks::<SharpnessArkworksCircuit<Fr>>(t),
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

fn run_circom<C: SonobeCircuit>(transformation: Transformation) -> Duration {
    Duration::from_secs(1)
}

fn run_arkworks<C: SonobeCircuit>(transformation: Transformation) -> Duration {
    Duration::from_secs(1)
}

fn present_stats(stats: Vec<Stat>) {
    // 1) Reorganize the stats
    let mut grouped: HashMap<Transformation, [Option<Duration>; 2]> = HashMap::new();
    for (t, f, d) in stats {
        let entry = grouped.entry(t).or_insert([None, None]);
        match f {
            Frontend::Circom => entry[0] = Some(d),
            Frontend::Arkworks => entry[1] = Some(d),
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

        let delta_pct = (cir_s / ark_s - 1.0) * 100.0;

        table.add_row([
            format!("{t:?}"),
            format!("{cir_s:.0}"),
            format!("{ark_s:.0}"),
            format!("{delta_pct:+.1}%"),
        ]);
    }

    println!("{table}");
}
