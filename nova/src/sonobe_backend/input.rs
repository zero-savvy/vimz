use ark_bn254::Fr;

use crate::{config::Config, input::VIMzInput, transformation::Transformation};

/// Read the input data specified in the configuration and prepare it for the folding scheme.
///
/// Returns the input data for each step and the initial state.
pub fn prepare_input(config: &Config) -> (Vec<Vec<Fr>>, Vec<Fr>) {
    let input = VIMzInput::<Fr>::from_file(&config.input_file());
    let initial_state = config.function.ivc_initial_state(&input.extra);
    let ivc_step_inputs = prepare_input_for_transformation(config.function, input);
    (ivc_step_inputs[..5].to_vec(), initial_state)
}

fn prepare_input_for_transformation(
    transformation: Transformation,
    input: VIMzInput<Fr>,
) -> Vec<Vec<Fr>> {
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
