use ark_bn254::Fr;

use crate::{input::VIMzInput, transformation::Transformation};

/// Returns the width of the input for a single step for the given transformation.
pub fn step_input_width(transformation: Transformation) -> usize {
    match transformation {
        // three rows of 128 entries for the kernel input and one for the result
        Transformation::Blur => 512,
        // two rows of 128 entries
        Transformation::Brightness | Transformation::Grayscale => 256,
        _ => unimplemented!(),
    }
}

/// Prepares the input for the given transformation.
pub fn prepare_input(transformation: Transformation, input: VIMzInput<Fr>) -> Vec<Vec<Fr>> {
    match transformation {
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
