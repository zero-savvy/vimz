use std::collections::HashMap;

use nova_scotia::F;
use serde_json::{json, Value};

use crate::{
    config::Config,
    input::VIMzInput,
    nova_snark_backend::{G1, G2},
    transformation::{Resolution, Transformation},
};

pub type PreparedInputs = (Vec<HashMap<String, Value>>, Vec<F<G1>>, Vec<F<G2>>);

/// Read the input data specified in the configuration and prepare it for the folding scheme.
///
/// Returns the input data for each step and the initial state.
#[tracing::instrument(name = "Prepare input", skip_all)]
pub fn prepare_input(config: &Config) -> PreparedInputs {
    let input = VIMzInput::<String>::from_file(&config.input_file());
    let initial_state = config.function.ivc_initial_state(&input.extra);
    let ivc_step_inputs =
        prepare_input_for_transformation(config.function, &input, config.resolution);
    (
        ivc_step_inputs[..5].to_vec(),
        initial_state,
        vec![F::<G2>::zero()],
    )
}

pub fn prepare_input_for_transformation(
    transformation: Transformation,
    input: &VIMzInput<String>,
    resolution: Resolution,
) -> Vec<HashMap<String, Value>> {
    let iter_count = match transformation {
        Transformation::Resize => resolution.lower().iteration_count(),
        _ => resolution.iteration_count(),
    };
    (0..iter_count)
        .map(|step| prepare_step_input(step, transformation, input, resolution))
        .collect()
}

fn prepare_step_input(
    step: usize,
    transformation: Transformation,
    input: &VIMzInput<String>,
    resolution: Resolution,
) -> HashMap<String, Value> {
    match transformation {
        // Handle cases where both original and transformed rows are needed.
        Transformation::Brightness | Transformation::Contrast | Transformation::Grayscale => {
            row_input(
                json!(input.original[step]),
                Some(json!(input.transformed[step])),
            )
        }

        // Handle transformations that require slices of the original and transformed rows.
        Transformation::Blur | Transformation::Sharpness => row_input(
            json!(input.original[step..step + 3]),
            Some(json!(input.transformed[step])),
        ),

        // Handle transformations that only need the original row.
        Transformation::Crop | Transformation::FixedCrop | Transformation::Hash => {
            row_input(json!(input.original[step]), None)
        }

        // Handle the Resize transformation with ranges.
        Transformation::Resize => {
            let (o_range, t_range) = resolution.ratio_to_lower();
            row_input(
                json!(input.original[step * o_range..(step * o_range) + o_range]),
                Some(json!(
                    input.transformed[step * t_range..(step * t_range) + t_range]
                )),
            )
        }
    }
}

fn row_input(row_orig: Value, row_tran: Option<Value>) -> HashMap<String, Value> {
    let mut map = HashMap::new();
    map.insert("row_orig".to_string(), row_orig);
    if let Some(row_tran) = row_tran {
        map.insert("row_tran".to_string(), row_tran);
    }
    map
}
