use std::{env::current_dir, fs::File, io::Read, path::Path, str::FromStr, time::Instant};

use ark_bn254::{constraints::GVar, Bn254, Fr, G1Projective as G1};
use ark_groth16::Groth16;
use ark_grumpkin::{constraints::GVar as GVar2, Projective as G2};
use clap::Parser;
use num_traits::Num;
use serde::Deserialize;
use sonobe::{
    commitment::{kzg::KZG, pedersen::Pedersen},
    folding::nova::{decider_eth::Decider, Nova, PreprocessorParam},
    frontend::{circom::CircomFCircuit, FCircuit},
    transcript::poseidon::poseidon_canonical_config,
    Decider as _, FoldingScheme,
};

use crate::config::Config;

mod config;
mod transformation;

#[derive(Deserialize)]
struct ZKronoInput {
    original: Vec<Vec<String>>,
    transformed: Vec<Vec<String>>,
}

impl ZKronoInput {
    fn from_file(path: &Path) -> Self {
        let mut input_file = File::open(path).expect("Failed to open the file");
        let mut input_file_json_string = String::new();
        input_file
            .read_to_string(&mut input_file_json_string)
            .expect("Unable to read from the file");
        serde_json::from_str(&input_file_json_string).expect("Deserialization failed")
    }
}

fn fold_fold_fold(config: &Config) {
    println!(
        "Running NOVA with witness generator: {:?} and group: {}",
        config.witness_generator,
        std::any::type_name::<G1>()
    );

    let root = current_dir().unwrap();
    let circuit_file = root.join(&config.circuit);
    let witness_generator_file = root.join(&config.witness_generator);

    // handling code for grayscale only: START =====================================================

    let mut private_inputs = vec![];
    let start_public_input: Vec<Fr> = vec![0.into(); 2];

    let start = Instant::now();
    let input_data = ZKronoInput::from_file(&config.input);
    for i in 0..config.resolution.iteration_count() {
        let inputs = [
            input_data.original[i][..4].to_vec(),
            input_data.transformed[i][..4].to_vec(),
        ]
        .concat();
        let inputs = inputs
            .iter()
            .map(|x| {
                let x = x.strip_prefix("0x").unwrap();
                let decoded = num_bigint::BigUint::from_str_radix(x, 16)
                    .unwrap()
                    .to_str_radix(10);
                Fr::from_str(&decoded).unwrap()
            })
            .collect::<Vec<_>>();
        private_inputs.push(inputs);
    }
    // handling code for grayscale only: END =======================================================

    println!("Prepared private inputs in {:?}", start.elapsed());

    // SONOBE code =================================================================================
    let f_circuit_params = (circuit_file, witness_generator_file, 2, 8);
    let f_circuit = CircomFCircuit::<Fr>::new(f_circuit_params).unwrap();

    pub type N =
        Nova<G1, GVar, G2, GVar2, CircomFCircuit<Fr>, KZG<'static, Bn254>, Pedersen<G2>, false>;
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
    let start = Instant::now();
    let nova_preprocess_params = PreprocessorParam::new(poseidon_config, f_circuit.clone());
    let nova_params = N::preprocess(&mut rng, &nova_preprocess_params).unwrap();
    println!("Nova::preprocess: {:?}", start.elapsed());

    // initialize the folding scheme engine, in our case we use Nova
    let start = Instant::now();
    let mut nova = N::init(&nova_params, f_circuit.clone(), start_public_input).unwrap();
    println!("Nova::init: {:?}", start.elapsed());

    // prepare the Decider prover & verifier params
    let start = Instant::now();
    let (decider_pp, decider_vp) = D::preprocess(&mut rng, &nova_params, nova.clone()).unwrap();
    println!("Decider::preprocess: {:?}", start.elapsed());

    // run n steps of the folding iteration
    for (i, external_inputs_at_step) in private_inputs.into_iter().enumerate() {
        let start = Instant::now();
        nova.prove_step(rng, external_inputs_at_step, None).unwrap();
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
    let config = Config::parse();
    config.display();
    fold_fold_fold(&config);
}
