use std::collections::HashMap;

use serde_json::{json, Value};

use crate::{
    input::VIMzInput,
    transformation::{Resolution, Transformation},
};

/// Prepares the input for the given transformation.
pub fn prepare_input(
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
