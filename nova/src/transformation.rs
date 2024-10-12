use ark_bn254::Fr;
use clap::ValueEnum;

use crate::input::{Extra, VIMzInput};

/// Supported transformations.
#[derive(Copy, Clone, PartialEq, Eq, Debug, ValueEnum)]
pub enum Transformation {
    Blur,
    Brightness,
    Contrast,
    Crop,
    FixedCrop,
    Grayscale,
    Hash,
    Resize,
    Sharpness,
}

impl Transformation {
    /// Returns the initial state of the IVC for the given transformation, based on the input.
    pub fn ivc_initial_state<ValueOut: From<u64> + Copy>(&self, input: &Extra) -> Vec<ValueOut> {
        let zero = ValueOut::from(0);
        let zzv = |v| vec![zero, zero, ValueOut::from(v)];

        match self {
            Transformation::Blur | Transformation::Sharpness => vec![zero; 4],
            Transformation::Brightness | Transformation::Contrast => zzv(input.factor()),
            Transformation::Crop => zzv(input.info()),
            Transformation::FixedCrop => vec![
                ValueOut::from(input.hash()),
                zero,
                ValueOut::from(input.info()),
            ],
            Transformation::Grayscale | Transformation::Resize => vec![zero; 2],
            Transformation::Hash => vec![zero],
        }
    }

    /// Returns the width of the input for a single step for the given transformation.
    pub fn step_input_width(&self) -> usize {
        match self {
            // two rows of 128 entries
            Transformation::Grayscale | Transformation::Brightness => 256,
            // three rows of 128 entries for the kernel input and one for the result
            Transformation::Blur => 512,
            _ => unimplemented!(),
        }
    }

    /// Prepares the input for the given transformation.
    pub fn prepare_input(&self, input: VIMzInput<Fr>) -> Vec<Vec<Fr>> {
        match self {
            // Concatenate the original and transformed row.
            Transformation::Grayscale | Transformation::Brightness => input
                .original
                .into_iter()
                .zip(input.transformed)
                .map(|(original, transformed)| [original, transformed].concat())
                .collect(),

            // Concatenate the original rows that are taken for the kernel, and the transformed row.
            Transformation::Blur => {
                let mut prepared = vec![];
                for (i, transformed) in input.transformed.into_iter().enumerate() {
                    let mut row = input.original[i..i + 3].to_vec();
                    row.push(transformed);
                    prepared.push(row.concat());
                }
                prepared
            }
            _ => unimplemented!(),
        }
    }
}

/// Supported resolutions.
#[derive(Copy, Clone, PartialEq, Eq, Debug, ValueEnum)]
#[value(rename_all = "UPPER")]
#[allow(clippy::upper_case_acronyms)]
pub enum Resolution {
    SD,
    HD,
    FHD,
    #[value(alias("4K"))]
    _4K,
    #[value(alias("8K"))]
    _8K,
}

impl Resolution {
    /// Returns the number of iterations for the given resolution (i.e. the number of rows in the
    /// image).
    pub fn iteration_count(&self) -> usize {
        match self {
            Resolution::SD => 480,
            Resolution::HD => 720,
            Resolution::FHD => 1080,
            Resolution::_4K => 2160,
            Resolution::_8K => 4320,
        }
    }

    /// Returns the lower resolution (step by one).
    pub fn lower(&self) -> Resolution {
        match self {
            Resolution::SD => panic!("Cannot lower resolution from SD"),
            Resolution::HD => Resolution::SD,
            Resolution::FHD => Resolution::HD,
            Resolution::_4K => Resolution::FHD,
            Resolution::_8K => Resolution::_4K,
        }
    }
}
