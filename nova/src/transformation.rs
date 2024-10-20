use clap::ValueEnum;

use crate::input::Extra;

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

    /// Returns the ratio of the current resolution to the lower resolution.
    pub fn ratio_to_lower(&self) -> (usize, usize) {
        match self {
            Resolution::SD => panic!("Cannot lower resolution from SD"),
            Resolution::HD => (3, 2),
            Resolution::FHD => (3, 2),
            Resolution::_4K => (2, 1),
            Resolution::_8K => (2, 1),
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn ratio_is_consistent_with_iteration_count() {
        use super::Resolution::*;

        for res in [HD, FHD, _4K, _8K] {
            let (num, den) = res.ratio_to_lower();
            assert_eq!(
                res.iteration_count() * den,
                res.lower().iteration_count() * num
            );
        }
    }
}
