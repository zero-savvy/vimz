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
pub enum Resolution {
    SD,
    HD,
    FHD,
    #[value(alias("4K"))]
    _4K,
    #[value(alias("8K"))]
    _8K,
}
