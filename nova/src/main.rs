use std::{collections::HashMap, env::current_dir, fs::File, io::{Read, Write}, time::Instant};

use clap::{App, Arg};
use serde::Deserialize;
use serde_json::json;

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
    type G1 = pasta_curves::pallas::Point;
    type G2 = pasta_curves::vesta::Point;

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
    // let r1cs = load_r1cs::<G1, G2>(&FileLocation::PathBuf(circuit_file));
    let witness_generator_file = root.join(witness_gen_filepath);

    let mut input_file = File::open(input_file_path.clone()).expect("Failed to open the file");
    let mut input_file_json_string = String::new();
    input_file.read_to_string(&mut input_file_json_string).expect("Unable to read from the file");
    
    // handling code for grayscale only: START =====================================================

    let mut private_inputs = vec![];
    let start_public_input: Vec<F::<G1>> = vec![0.into(); 2];

    let input_data: ZKronoInput = serde_json::from_str(&input_file_json_string).expect("Deserialization failed");
    for i in 0..iteration_count {
        let mut private_input = HashMap::new();
        private_input.insert("row_orig".to_string(), json!(input_data.original[i]));
        private_input.insert("row_tran".to_string(), json!(input_data.transformed[i]));
        private_inputs.push(private_input);
    }
    // handling code for grayscale only: END =======================================================

    let start = Instant::now();
    let pp: PublicParams<G1, G2, _, _> = create_public_params(r1cs.clone());
    println!(
        "Creating keys from R1CS took {:?}",
        start.elapsed()
    );

    println!(
        "Number of constraints per step (primary circuit): {}",
        pp.num_constraints().0
    );
    println!(
        "Number of constraints per step (secondary circuit): {}",
        pp.num_constraints().1
    );

    println!(
        "Number of variables per step (primary circuit): {}",
        pp.num_variables().0
    );
    println!(
        "Number of variables per step (secondary circuit): {}",
        pp.num_variables().1
    );

    println!("Creating a RecursiveSNARK...");
    let start = Instant::now();
    let recursive_snark = create_recursive_circuit(
        FileLocation::PathBuf(witness_generator_file),
        r1cs,
        private_inputs,
        start_public_input.to_vec(),
        &pp,
    )
    .unwrap();
    println!("RecursiveSNARK creation took {:?}", start.elapsed());

    // TODO: empty?
    let z0_secondary = [F::<G2>::from(0)];

    // verify the recursive SNARK
    println!("Verifying a RecursiveSNARK...");
    let start = Instant::now();
    let res = recursive_snark.verify(&pp, iteration_count, &start_public_input, &z0_secondary);
    println!(
        "RecursiveSNARK::verify: {:?}, took {:?}",
        res,
        start.elapsed()
    );
    assert!(res.is_ok());

    // produce a compressed SNARK
    println!("Generating a CompressedSNARK using Spartan with IPA-PC...");
    let start = Instant::now();

    let (pk, vk) = CompressedSNARK::<_, _, _, _, S<G1>, S<G2>>::setup(&pp).unwrap();
    let res = CompressedSNARK::<_, _, _, _, S<G1>, S<G2>>::prove(&pp, &pk, &recursive_snark);
    println!(
        "CompressedSNARK::prove: {:?}, took {:?}",
        res.is_ok(),
        start.elapsed()
    );
    assert!(res.is_ok());
    let compressed_snark = res.unwrap();

    //--- dump data ---//
    // Create some data to serialize as JSON
    
    // Serialize the data to a JSON string
    let json_string = serde_json::to_string(&compressed_snark).unwrap();

    // Open a file for writing
    let mut file = File::create(output_file_path.clone()).expect("Unable to create the file");

    // Write the JSON string to the file
    file.write_all(json_string.as_bytes()).expect("Unable to write to the file");

    println!("Data has been written to output.json");

    println!("-------------- Load Data --------");
    let mut file = File::open(output_file_path.clone()).expect("Unable to open the file");
    let mut json_string = String::new();
    file.read_to_string(&mut json_string).expect("Unable to read from the file");
    
    let compressed_snark2: CompressedSNARK<_, _, _, _, _, _> = serde_json::from_str(&json_string).expect("Deserialization failed");

    // verify the compressed SNARK
    println!("Verifying a CompressedSNARK...");
    let start = Instant::now();
    let res = compressed_snark2.verify(
        &vk,
        iteration_count,
        start_public_input.to_vec(),
        z0_secondary.to_vec(),
    );
    println!(
        "CompressedSNARK::verify: {:?}, took {:?}",
        res.is_ok(),
        start.elapsed()
    );
    assert!(res.is_ok());
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