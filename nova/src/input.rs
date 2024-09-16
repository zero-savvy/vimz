use std::{fs::File, io::Read, path::Path, str::FromStr};

use ark_bn254::Fr;
use num_traits::Num;
use serde::Deserialize;

#[derive(Deserialize)]
pub struct ZKronoInput {
    pub original: Vec<Vec<String>>,
    pub transformed: Vec<Vec<String>>,
}

impl ZKronoInput {
    pub fn from_file(path: &Path) -> Self {
        let mut input_file = File::open(path).expect("Failed to open the file");
        let mut input_file_json_string = String::new();
        input_file
            .read_to_string(&mut input_file_json_string)
            .expect("Unable to read from the file");
        serde_json::from_str(&input_file_json_string).expect("Deserialization failed")
    }

    pub fn into_circom_input(self) -> Vec<Vec<Fr>> {
        self.original
            .iter()
            .zip(self.transformed.iter())
            .map(|(original, transformed)| {
                let original = string_seq_to_fr_seq(&original[..4]);
                let transformed = string_seq_to_fr_seq(&transformed[..4]);
                [original, transformed].concat()
            })
            .collect()
    }
}

fn string_seq_to_fr_seq(seq: &[String]) -> Vec<Fr> {
    seq.iter()
        .map(|x| {
            let x = x.strip_prefix("0x").unwrap();
            let decoded = num_bigint::BigUint::from_str_radix(x, 16)
                .unwrap()
                .to_str_radix(10);
            Fr::from_str(&decoded).unwrap()
        })
        .collect()
}
