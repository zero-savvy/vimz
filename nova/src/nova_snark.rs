use std::{collections::HashMap, env::current_dir, time::Instant, fs::File, io::{Write, Read}};


use nova_scotia::{
    circom::reader::load_r1cs, create_public_params, create_recursive_circuit, FileLocation, F, S,
};
use nova_snark::{
    CompressedSNARK, PublicParams,
};
use serde::Deserialize;
use serde_json::json;

use crate::{config::Config, transformation::{Resolution, Transformation}};

#[derive(Deserialize)]
struct ZKronoInput {
    original: Vec<Vec<String>>,
    transformed: Vec<Vec<String>>,
}

#[derive(Deserialize)]
struct ZKronoInputContrast {
    original: Vec<Vec<String>>,
    transformed: Vec<Vec<String>>,
    factor: u64,
}

#[derive(Deserialize)]
struct ZKronoInputBrightness {
    original: Vec<Vec<String>>,
    transformed: Vec<Vec<String>>,
    factor: u64,
}

#[derive(Deserialize)]
struct ZKronoInputCrop {
    original: Vec<Vec<String>>,
    info: u64,
}

#[derive(Deserialize)]
struct ZKronoInputCropOpt {
    original: Vec<Vec<String>>,
    info: u64,
    hash: u64,
}


pub fn nova_snark_backend(config: &Config) {
    
    let selected_function = config.function;
    let circuit_filepath = &config.circuit;
    let witness_gen_filepath = &config.witness_generator;
    let output_file_path = &config.output;
    let input_file_path = &config.input;
    let resolution = config.resolution; 
    type G1 = nova_snark::provider::bn256_grumpkin::bn256::Point;
    type G2 = nova_snark::provider::bn256_grumpkin::grumpkin::Point;

    println!(
        "Running NOVA with witness generator: {} and group: {}",
        witness_gen_filepath.display(),
        std::any::type_name::<G1>()
    );
    let mut iteration_count = 720; // HD
    if resolution == Resolution::_4K {
        iteration_count = 2160;
    }
    if resolution == Resolution::_8K {
        iteration_count = 4320;
    }
    let root = current_dir().unwrap();

    let circuit_file = root.join(circuit_filepath);
    let r1cs = load_r1cs::<G1, G2>(&FileLocation::PathBuf(circuit_file));
    let witness_generator_file = root.join(witness_gen_filepath);

    let mut input_file = File::open(input_file_path.clone()).expect("Failed to open the file");
    let mut input_file_json_string = String::new();
    input_file.read_to_string(&mut input_file_json_string).expect("Unable to read from the file");
    
    let mut private_inputs = Vec::new();
    let mut start_public_input: Vec<F::<G1>> = Vec::new();

    if selected_function == Transformation::Hash {
        let input_data: ZKronoInputCrop = serde_json::from_str(&input_file_json_string).expect("Deserialization failed");
        start_public_input.push(F::<G1>::from(0));
        for i in 0..iteration_count {
            let mut private_input = HashMap::new();
            // private_input.insert("adder".to_string(), json!(i+2));
            private_input.insert("row_orig".to_string(), json!(input_data.original[i]));
            private_inputs.push(private_input);
        }
    } else if selected_function == Transformation::Crop {
        let input_data: ZKronoInputCrop = serde_json::from_str(&input_file_json_string).expect("Deserialization failed");
        start_public_input.push(F::<G1>::from(0));
        start_public_input.push(F::<G1>::from(0));
        start_public_input.push(F::<G1>::from(input_data.info));  // x|y|index
        for i in 0..iteration_count {
            let mut private_input = HashMap::new();
            // private_input.insert("adder".to_string(), json!(i+2));
            private_input.insert("row_orig".to_string(), json!(input_data.original[i]));
            private_inputs.push(private_input);
        }
    }
    else if selected_function == Transformation::FixedCrop {
        let input_data: ZKronoInputCropOpt = serde_json::from_str(&input_file_json_string).expect("Deserialization failed");
        start_public_input.push(F::<G1>::from(input_data.hash));
        start_public_input.push(F::<G1>::from(0));
        start_public_input.push(F::<G1>::from(input_data.info));  // x|y|index
        for i in 0..iteration_count {
            let mut private_input = HashMap::new();
            // private_input.insert("adder".to_string(), json!(i+2));
            private_input.insert("row_orig".to_string(), json!(input_data.original[i]));
            private_inputs.push(private_input);
        }
    } else if selected_function == Transformation::Resize {
        let input_data: ZKronoInput = serde_json::from_str(&input_file_json_string).expect("Deserialization failed");
        iteration_count = 240;
        if resolution == Resolution::_4K {
            iteration_count = 1080;
        }
        start_public_input.push(F::<G1>::from(0));
        start_public_input.push(F::<G1>::from(0));
        for i in 0..iteration_count {
            let mut private_input = HashMap::new();
            // private_input.insert("adder".to_string(), json!(i+2));
            if resolution == Resolution::HD {
                private_input.insert("row_orig".to_string(), json!(input_data.original[(i*3)..(i*3)+3]));
                private_input.insert("row_tran".to_string(), json!(input_data.transformed[(i*2)..(i*2)+2]));
            } else if resolution == Resolution::_4K{
                private_input.insert("row_orig".to_string(), json!(input_data.original[(i*2)..(i*2)+2]));
                private_input.insert("row_tran".to_string(), json!(input_data.transformed[i]));
            }
            private_inputs.push(private_input);

        }
    } else {
        start_public_input.push(F::<G1>::from(0));
        start_public_input.push(F::<G1>::from(0));
        if selected_function == Transformation::Contrast {
            let input_data: ZKronoInputContrast = serde_json::from_str(&input_file_json_string).expect("Deserialization failed");
            start_public_input.push(F::<G1>::from(input_data.factor));  // contrast factor
            for i in 0..iteration_count {
                let mut private_input = HashMap::new();
                // private_input.insert("adder".to_string(), json!(i+2));
                private_input.insert("row_orig".to_string(), json!(input_data.original[i]));
                private_input.insert("row_tran".to_string(), json!(input_data.transformed[i]));
                private_inputs.push(private_input);
            }
        } else if selected_function == Transformation::Brightness {
            let input_data: ZKronoInputBrightness = serde_json::from_str(&input_file_json_string).expect("Deserialization failed");
            start_public_input.push(F::<G1>::from(input_data.factor));  // brightness factor
            for i in 0..iteration_count {
                let mut private_input = HashMap::new();
                // private_input.insert("adder".to_string(), json!(i+2));
                private_input.insert("row_orig".to_string(), json!(input_data.original[i]));
                private_input.insert("row_tran".to_string(), json!(input_data.transformed[i]));
                private_inputs.push(private_input);
            }
        } else if selected_function == Transformation::Blur || selected_function == Transformation::Sharpness  {
            let input_data: ZKronoInput = serde_json::from_str(&input_file_json_string).expect("Deserialization failed");
            start_public_input.push(F::<G1>::from(0));  // row1 hash
            start_public_input.push(F::<G1>::from(0));  // row2 hash
            for i in 0..iteration_count {
                let mut private_input = HashMap::new();
                // private_input.insert("adder".to_string(), json!(i+2));
                private_input.insert("row_orig".to_string(), json!(input_data.original[i..i+3]));
                private_input.insert("row_tran".to_string(), json!(input_data.transformed[i]));
                private_inputs.push(private_input);
            }
        } else {
            let input_data: ZKronoInput = serde_json::from_str(&input_file_json_string).expect("Deserialization failed");
            for i in 0..iteration_count {
                let mut private_input = HashMap::new();
                // private_input.insert("adder".to_string(), json!(i+2));
                private_input.insert("row_orig".to_string(), json!(input_data.original[i]));
                private_input.insert("row_tran".to_string(), json!(input_data.transformed[i]));
                private_inputs.push(private_input);
            }
        }
        
    }
    
    // let reader = BufReader::new(file);

    // Deserialize the JSON data into the defined structure
    // let data: Data = serde_json::from_reader(reader).expect("Failed to parse JSON");

    

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
