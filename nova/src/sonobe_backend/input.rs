use std::{fs, path::Path, str::FromStr};

use ark_bn254::Fr;
use num_traits::Num;
use serde::Deserialize;

/// Universal input structure for all supported transformations in the Sonobe circuits.
#[derive(Deserialize)]
pub struct SonobeInput<ValueType = Fr> {
    /// The original image, row by row (with pixels compression).
    pub original: Vec<Vec<ValueType>>,
    /// The transformed image, row by row (with pixels compression).
    pub transformed: Vec<Vec<ValueType>>,
    /// An optional factor for tuning the transformation.
    ///
    /// For most transformations, this is just 0.
    #[serde(default)]
    pub factor: u64,
}

impl SonobeInput<Fr> {
    /// Parse `path` into a `SonobeInput` structure. Convert the hex strings into `Fr` elements.
    pub fn from_file(path: &Path) -> Self {
        let file_content = fs::read_to_string(path).expect("Failed to read file");
        let self_string: SonobeInput<String> =
            serde_json::from_str(&file_content).expect("Deserialization failed");

        Self {
            original: string_2d_seq_to_fr_2d_seq(&self_string.original),
            transformed: string_2d_seq_to_fr_2d_seq(&self_string.transformed),
            factor: self_string.factor,
        }
    }
}

/// Convert a sequence of sequences of hex strings into a sequence of sequences of `Fr` elements.
fn string_2d_seq_to_fr_2d_seq(seq: &[Vec<String>]) -> Vec<Vec<Fr>> {
    seq.iter().map(|x| string_seq_to_fr_seq(x)).collect()
}

/// Convert a sequence of hex strings into a sequence of `Fr` elements.
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
