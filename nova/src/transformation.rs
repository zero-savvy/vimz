use ark_bn254::Fr;
use clap::ValueEnum;
use num_traits::Zero;

use crate::input::ZKronoInput;

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
    pub fn ivc_initial_state(&self, input: &ZKronoInput) -> Vec<Fr> {
        match self {
            Transformation::Grayscale => vec![Fr::zero(); 2],
            Transformation::Brightness => vec![Fr::zero(), Fr::zero(), Fr::from(input.factor)],
            _ => unimplemented!(),
        }
    }

    pub fn step_input_width(&self) -> usize {
        match self {
            Transformation::Grayscale | Transformation::Brightness => 256,
            _ => unimplemented!(),
        }
    }
}

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
