use Transformation::*;
use ark_bn254::Fr;

use crate::{
    DEMO_STEPS,
    config::Config,
    input::VIMzInput,
    transformation::{Resolution, Transformation},
};

/// Read the input data specified in the configuration and prepare it for the folding scheme.
///
/// Returns the input data for each step and the initial state.
#[tracing::instrument(name = "Prepare input", skip_all)]
pub fn prepare_input(config: &Config) -> (Vec<Vec<Fr>>, Vec<Fr>) {
    let input = VIMzInput::<Fr>::from_file(&config.input_file());
    let initial_state = config.function.ivc_initial_state(&input.extra);
    let mut ivc_step_inputs =
        prepare_input_for_transformation(config.function, input, config.resolution);

    if config.demo {
        ivc_step_inputs.truncate(DEMO_STEPS);
    }

    (ivc_step_inputs, initial_state)
}

fn prepare_input_for_transformation(
    transformation: Transformation,
    input: VIMzInput<Fr>,
    resolution: Resolution,
) -> Vec<Vec<Fr>> {
    match transformation {
        // Concatenate the original and transformed row.
        Brightness | Contrast | Grayscale => input
            .original
            .into_iter()
            .zip(input.transformed)
            .map(|(original, transformed)| [original, transformed].concat())
            .collect(),

        // Concatenate the original rows that are taken for the kernel, and the transformed row.
        Blur | Sharpness => {
            let mut prepared = vec![];
            for (i, transformed) in input.transformed.into_iter().enumerate() {
                let mut row = input.original[i..i + 3].to_vec();
                row.push(transformed);
                prepared.push(row.concat());
            }
            prepared
        }

        // Simply rewrite the input data.
        Hash | Crop => input.original,

        // Concatenate the original block with redaction indicator.
        Redact => input
            .original
            .into_iter()
            .zip(input.extra.redact())
            .map(|(mut block, redact)| {
                block.push(redact);
                block
            })
            .collect(),

        // Concatenate the batches of original and transformed rows.
        Resize => {
            let mut prepared = vec![];
            let (o_range, t_range) = resolution.ratio_to_lower();

            for i in 0..(resolution.iteration_count() / o_range) {
                let row = [
                    input.original[i * o_range..(i + 1) * o_range].concat(),
                    input.transformed[i * t_range..(i + 1) * t_range].concat(),
                ];
                prepared.push(row.concat());
            }

            prepared
        }
    }
}
