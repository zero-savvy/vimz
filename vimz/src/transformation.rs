use clap::ValueEnum;

use crate::input::Extra;

/// Supported transformations.
#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, ValueEnum)]
pub enum Transformation {
    Blur,
    Brightness,
    Contrast,
    Crop,
    Grayscale,
    Hash,
    Redact,
    Resize,
    Sharpness,
}

use Transformation::*;

use crate::image_hash::HashMode;

impl Transformation {
    /// Returns the initial state of the IVC for the given transformation, based on the input.
    pub fn ivc_initial_state<ValueOut: From<u64> + Copy, FieldRepr>(
        &self,
        input: &Extra<FieldRepr>,
    ) -> Vec<ValueOut> {
        let zero = ValueOut::from(0);
        let zzv = |v| vec![zero, zero, ValueOut::from(v)];

        match self {
            Blur | Sharpness => vec![zero; 4],
            Brightness | Contrast => zzv(input.factor()),
            Crop => zzv(input.info()),
            Grayscale | Redact | Resize => vec![zero; 2],
            Hash => vec![zero],
        }
    }

    /// Returns the size of the IVC state.
    pub const fn ivc_state_len(&self) -> usize {
        match self {
            Blur | Sharpness => 4,
            Brightness | Contrast | Crop => 3,
            Grayscale | Redact | Resize => 2,
            Hash => 1,
        }
    }

    /// Returns the amount of the input field elements for a single step for the given transformation.
    pub const fn step_input_width(&self) -> usize {
        match self {
            // Three rows of 128 entries for the kernel input and one for the result.
            Blur | Sharpness => 512,
            // Two rows of 128 entries.
            Brightness | Contrast | Grayscale => 256,
            // Single row of 128 entries.
            Crop | Hash => 128,
            // 40 x 40 blocks (with 10-pixel compression) + 1 input indicating whether the block is redacted.
            Redact => 160 + 1,
            // Three rows of 128 entries for the original image and two of 64 entries for the transformed.
            Resize => 128 * 3 + 64 * 2,
        }
    }

    /// Returns the mode of image hashing for the given transformation.
    pub const fn hash_mode(&self) -> HashMode {
        match self {
            Redact => HashMode::BlockWise,
            _ => HashMode::RowWise,
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
    pub const fn iteration_count(&self) -> usize {
        match self {
            Resolution::SD => 480,
            Resolution::HD => 720,
            Resolution::FHD => 1080,
            Resolution::_4K => 2160,
            Resolution::_8K => 4320,
        }
    }

    /// Returns the number of iterations in block-based transformations.
    pub fn iteration_count_block_based(&self) -> usize {
        match self {
            Resolution::SD => 0, // TODO
            Resolution::HD => 576,
            Resolution::FHD => 0, // TODO
            Resolution::_4K => 0, // TODO
            Resolution::_8K => 0, // TODO
        }
    }

    /// Returns the ratio of the current resolution to the lower resolution.
    pub const fn ratio_to_lower(&self) -> (usize, usize) {
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

        for (res, lower) in [(HD, SD), (FHD, HD), (_4K, FHD), (_8K, _4K)] {
            let (num, den) = res.ratio_to_lower();
            assert_eq!(res.iteration_count() * den, lower.iteration_count() * num);
        }
    }
}
