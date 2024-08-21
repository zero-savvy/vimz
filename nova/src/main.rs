use std::{env::current_dir, fs::File, io::Read, time::Instant};
use std::str::FromStr;

use ark_bn254::{Bn254, constraints::GVar, Fr, G1Projective as G1};
use ark_groth16::Groth16;
use ark_grumpkin::{constraints::GVar as GVar2, Projective as G2};
use clap::{App, Arg};
use serde::Deserialize;
use sonobe::{
    frontend::{
        FCircuit,
        circom::CircomFCircuit,
    },
    folding::{
        nova::decider_eth::Decider,
        nova::{Nova, PreprocessorParam},
    },
    commitment::{
        pedersen::Pedersen,
        kzg::KZG,
    },
    Decider as _,
    FoldingScheme,
    transcript::poseidon::poseidon_canonical_config,
};

#[derive(Deserialize)]
struct ZKronoInput {
    original: Vec<Vec<String>>,
    transformed: Vec<Vec<String>>,
}

fn fold_fold_fold(selected_function: String,
                  circuit_filepath: String,
                  witness_gen_filepath: String,
                  output_file_path: String,
                  input_file_path: String,
                  resolution: String) {
    println!(
        "Running NOVA with witness generator: {} and group: {}",
        witness_gen_filepath,
        std::any::type_name::<G1>()
    );
    let mut iteration_count = 720; // HD
    if resolution == "4K" {
        iteration_count = 2160;
    }
    if resolution == "8K" {
        iteration_count = 4320;
    }
    let root = current_dir().unwrap();

    let circuit_file = root.join(circuit_filepath);
    let witness_generator_file = root.join(witness_gen_filepath);

    let mut input_file = File::open(input_file_path.clone()).expect("Failed to open the file");
    let mut input_file_json_string = String::new();
    input_file.read_to_string(&mut input_file_json_string).expect("Unable to read from the file");

    // handling code for grayscale only: START =====================================================

    let mut private_inputs = vec![];
    let start_public_input: Vec<Fr> = vec![0.into(); 2];

    use num_traits::Num;

    let input_data: ZKronoInput = serde_json::from_str(&input_file_json_string).expect("Deserialization failed");
    for i in 0..iteration_count {
        let inputs = vec![input_data.original[i].clone(), input_data.transformed[i].clone()].concat();
        let inputs = inputs.iter().map(|x| {
            let x = x.strip_prefix("0x").unwrap();
            let decoded = num_bigint::BigUint::from_str_radix(x, 16).unwrap().to_str_radix(10);
            Fr::from_str(&decoded).unwrap()
        }).collect::<Vec<_>>();
        private_inputs.push(inputs);
    }
    // handling code for grayscale only: END =======================================================

    // SONOBE code =================================================================================
    let f_circuit_params = (circuit_file, witness_generator_file, 2, 256);
    let f_circuit = CircomFCircuit::<Fr>::new(f_circuit_params).unwrap();

    pub type N = Nova<G1, GVar, G2, GVar2, CircomFCircuit<Fr>, KZG<'static, Bn254>, Pedersen<G2>, false>;
    pub type D = Decider<
        G1,
        GVar,
        G2,
        GVar2,
        CircomFCircuit<Fr>,
        KZG<'static, Bn254>,
        Pedersen<G2>,
        Groth16<Bn254>,
        N,
    >;

    let poseidon_config = poseidon_canonical_config::<Fr>();
    let mut rng = rand::rngs::OsRng;

    // prepare the Nova prover & verifier params
    let nova_preprocess_params = PreprocessorParam::new(poseidon_config, f_circuit.clone());
    let nova_params = N::preprocess(&mut rng, &nova_preprocess_params).unwrap();

    // initialize the folding scheme engine, in our case we use Nova
    let mut nova = N::init(&nova_params, f_circuit.clone(), start_public_input).unwrap();

    // prepare the Decider prover & verifier params
    let (decider_pp, decider_vp) = D::preprocess(&mut rng, &nova_params, nova.clone()).unwrap();

    // run n steps of the folding iteration
    for (i, external_inputs_at_step) in private_inputs.into_iter().enumerate() {
        let start = Instant::now();
        nova.prove_step(rng, external_inputs_at_step, None)
            .unwrap();
        println!("Nova::prove_step {}: {:?}", i, start.elapsed());
    }

    let start = Instant::now();
    let proof = D::prove(rng, decider_pp, nova.clone()).unwrap();
    println!("generated Decider proof: {:?}", start.elapsed());

    let verified = D::verify(
        decider_vp.clone(),
        nova.i,
        nova.z_0.clone(),
        nova.z_i.clone(),
        &nova.U_i,
        &nova.u_i,
        &proof,
    )
        .unwrap();
    assert!(verified);
    println!("Decider proof verification: {}", verified);
}

fn main() {
    let matches = App::new("VIMz")
        .version("v1.3.0")
        .author("Zero-Savvy")
        .about("Prove the truthfulness of your media! \n The naming rationale: Verifiable Image Manipulation based on ZKP. \n Pronunciation: /ˈwɪmzi/, just like whimsy :D")
        .arg(
            Arg::with_name("input")
            .required(true)
            .short("i")
            .long("input")
            .value_name("FILE")
            .help("The JSON file containing the original and the transformed image data to verify.")
            .takes_value(true)
        )
        .arg(
            Arg::with_name("output")
            .required(true)
            .short("o")
            .long("output")
            .value_name("FILE")
            .help("This file will contain the final Proof to be verified by others.")
            .takes_value(true)
        )
        .arg(
            Arg::with_name("circuit")
            .required(true)
            .short("c")
            .long("circuit")
            .value_name("R1CS FILE")
            .help("The R1CS file of the compiled Circom circuit.")
            .takes_value(true)
        )
        .arg(
            Arg::with_name("witnessgenerator")
            .required(true)
            .short("w")
            .long("witnessgenerator")
            .value_name("BINARY/WASM FILE")
            .help("Witness generator file of the circuit.")
            .takes_value(true)
        )
        .arg(
            Arg::with_name("function")
            .required(true)
            .short("f")
            .long("function")
            .value_name("FUNCTION")
            .help("The transformation function.")
            .takes_value(true)
            .possible_values(&["crop", "fixedcrop", "grayscale", "resize", "color_transform", "sharpness", "contrast", "blur", "brightness", "hash"])
        )
        .arg(
            Arg::with_name("resolution")
            .required(true)
            .short("r")
            .long("resolution")
            .value_name("RESOLUTION")
            .help("The resolution of the image.")
            .takes_value(true)
            .possible_values(&["SD", "HD", "FHD", "4K", "8K"])
        )
        .get_matches();

    let witness_gen_filepath = matches.value_of("witnessgenerator").unwrap();
    let circuit_filepath = matches.value_of("circuit").unwrap();
    let output_filepath = matches.value_of("output").unwrap();
    let input_filepath = matches.value_of("input").unwrap();
    let selected_function = matches.value_of("function").unwrap();
    let resolution = matches.value_of("resolution").unwrap();

    println!(" ________________________________________________________");
    println!("                                                         ");
    println!(" ██     ██  ██  ███    ███  ████████   Verifiable  Image");
    println!(" ██     ██  ██  ████  ████      ███    Manipulation from");
    println!("  ██   ██   ██  ██ ████ ██     ██      Folded   zkSNARKs");
    println!("   ██ ██    ██  ██  ██  ██   ███                         ");
    println!("    ███     ██  ██      ██  ████████████ v1.3.0 ████████");
    println!(" ________________________________________________________");
    println!("| Input file: {}", input_filepath);
    println!("| Output file: {}", output_filepath);
    println!("| Selected function: {}", selected_function);
    println!("| Circuit file: {}", circuit_filepath);
    println!("| Witness generator: {}", witness_gen_filepath);
    println!("| Image resolution: {}", resolution);
    println!(" ‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾");


    fold_fold_fold(selected_function.to_string().clone(),
                circuit_filepath.to_string().clone(),
                witness_gen_filepath.to_string(),
                output_filepath.to_string(),
                input_filepath.to_string(),
                resolution.to_string()
            );
}