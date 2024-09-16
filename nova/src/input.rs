use std::{fs::File, io::Read, path::Path, str::FromStr};

use ark_bn254::Fr;
use num_traits::Num;
use serde::Deserialize;

/// Universal input structure for all supported transformations.
#[derive(Deserialize)]
pub struct ZKronoInput<ValueType = Fr> {
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

impl ZKronoInput<Fr> {
    /// Parse `path` into a `ZKronoInput` structure. Convert the hex strings into `Fr` elements.
    pub fn from_file(path: &Path) -> Self {
        let mut input_file_json = String::new();
        File::open(path)
            .expect("Failed to open the file")
            .read_to_string(&mut input_file_json)
            .expect("Unable to read from the file");

        let self_string: ZKronoInput<String> =
            serde_json::from_str(&input_file_json).expect("Deserialization failed");

        Self {
            original: self_string
                .original
                .iter()
                .map(|x| string_seq_to_fr_seq(x))
                .collect(),
            transformed: self_string
                .transformed
                .iter()
                .map(|x| string_seq_to_fr_seq(x))
                .collect(),
            factor: self_string.factor,
        }
    }
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
