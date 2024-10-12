use std::{fs, path::Path, str::FromStr};

use ark_bn254::Fr;
use num_traits::Num;
use serde::Deserialize;

/// Extra information for the VIMz input.
#[derive(Deserialize)]
#[serde(untagged)]
pub enum Extra {
    /// An optional factor for tuning the transformation.
    Factor { factor: u64 },
    /// An optional scalar info and hash.
    InfoHash { info: u64, hash: u64 },
    /// An optional scalar info.
    Info { info: u64 },
    /// No extra information.
    None {},
}

/// Universal input structure for all supported transformations in the VIMz circuits.
#[derive(Deserialize)]
pub struct VIMzInput<ValueType = Fr> {
    /// The original image, row by row (with pixels compression).
    pub original: Vec<Vec<ValueType>>,
    /// The transformed image, row by row (with pixels compression).
    pub transformed: Vec<Vec<ValueType>>,
    #[serde(flatten)]
    /// Extra information for the transformation.
    pub extra: Extra,
}

impl<ValueType> VIMzInput<ValueType> {
    pub fn factor(&self) -> u64 {
        match self.extra {
            Extra::Factor { factor } => factor,
            _ => unreachable!("No factor provided"),
        }
    }

    pub fn info(&self) -> u64 {
        match self.extra {
            Extra::Info { info } => info,
            Extra::InfoHash { info, .. } => info,
            _ => unreachable!("No info provided"),
        }
    }

    pub fn hash(&self) -> u64 {
        match self.extra {
            Extra::InfoHash { hash, .. } => hash,
            _ => unreachable!("No hash provided"),
        }
    }
}

impl VIMzInput<String> {
    /// Parse `path` into a `VIMzInput` structure. Keep the hex strings as they are.
    pub fn from_file(path: &Path) -> Self {
        let file_content = fs::read_to_string(path).expect("Failed to read file");
        serde_json::from_str(&file_content).expect("Deserialization failed")
    }
}

impl VIMzInput<Fr> {
    /// Parse `path` into a `VIMzInput` structure. Convert the hex strings into `Fr` elements.
    pub fn from_file(path: &Path) -> Self {
        let self_string = VIMzInput::<String>::from_file(path);

        Self {
            original: string_2d_seq_to_fr_2d_seq(&self_string.original),
            transformed: string_2d_seq_to_fr_2d_seq(&self_string.transformed),
            extra: self_string.extra,
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
