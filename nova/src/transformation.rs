use clap::ValueEnum;

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
        return 5;
        // match self {
        //     Resolution::SD => 480,
        //     Resolution::HD => 720,
        //     Resolution::FHD => 1080,
        //     Resolution::_4K => 2160,
        //     Resolution::_8K => 4320,
        // }
    }
}
