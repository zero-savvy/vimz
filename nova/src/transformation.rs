use ark_bn254::Fr;
use clap::ValueEnum;
use num_traits::Zero;
use crate::sonobe_backend::input::SonobeInput;

/// Supported transformations.
#[derive(Copy, Clone, PartialEq, Eq, Debug, ValueEnum)]
pub enum Transformation {
    Crop,
    FixedCrop,
    Grayscale,
    Resize,
    ColorTransform,
    Sharpness,
    Contrast,
    Blur,
    Brightness,
    Hash,
}

impl Transformation {
    /// Returns the initial state of the IVC for the given transformation, based on the input.
    pub fn ivc_initial_state(&self, input: &SonobeInput) -> Vec<Fr> {
        match self {
            Transformation::Grayscale => vec![Fr::zero(); 2],
            Transformation::Brightness => vec![Fr::zero(), Fr::zero(), Fr::from(input.factor)],
            Transformation::Blur => vec![Fr::zero(); 4],
            _ => unimplemented!(),
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
    pub fn prepare_input(&self, input: SonobeInput) -> Vec<Vec<Fr>> {
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
}
