use ark_bn254::{Bn254, Fr, G1Projective as G1};
use ark_grumpkin::Projective as G2;
use rand::{CryptoRng, RngCore};
use sonobe::{
    FoldingScheme,
    commitment::{kzg::KZG, pedersen::Pedersen},
    folding::nova::{Nova, PreprocessorParam},
    frontend::FCircuit,
    transcript::poseidon::poseidon_canonical_config,
};
use tracing::info_span;

use crate::{
    DEMO_STEPS,
    config::{Backend, Config, Frontend},
    image_hash::hash_image_arkworks,
    sonobe_backend::circuits::{SonobeCircuit, VecFT},
    transformation::Transformation::{Crop, Redact, Resize},
};

/// The folding scheme used.
pub type Folding<Circuit> = Nova<G1, G2, Circuit, KZG<'static, Bn254>, Pedersen<G2>, false>;
pub type FoldingParams<Circuit> = (
    <Folding<Circuit> as FoldingScheme<G1, G2, Circuit>>::ProverParam,
    <Folding<Circuit> as FoldingScheme<G1, G2, Circuit>>::VerifierParam,
);

/// Prepare the Nova folding scheme with the given files, parameters, and rng. Initialize it with
/// the given initial state.
#[tracing::instrument(name = "Prepare folding", skip_all)]
pub fn prepare_folding<Circuit: SonobeCircuit>(
    config: &Config,
    initial_state: Vec<Fr>,
    rng: &mut (impl RngCore + CryptoRng),
) -> (Folding<Circuit>, FoldingParams<Circuit>) {
    let f_circuit = Circuit::from_config(config);

    let nova_params = info_span!("Preprocess Nova").in_scope(|| {
        let nova_preprocess_params =
            PreprocessorParam::new(poseidon_canonical_config::<Fr>(), f_circuit.clone());
        Folding::preprocess(&mut *rng, &nova_preprocess_params).expect("Failed to preprocess Nova")
    });
    let nova = info_span!("Init Nova").in_scope(|| {
        Folding::init(&nova_params, f_circuit, initial_state).expect("Failed to init Nova")
    });

    (nova, nova_params)
}

/// Fold all the `ivc_steps_inputs` into `folding`.
#[tracing::instrument(name = "Fold input", skip_all, fields(steps = ivc_step_inputs.len()))]
pub fn fold_input<Circuit: SonobeCircuit>(
    folding: &mut Folding<Circuit>,
    ivc_step_inputs: Vec<Vec<Fr>>,
    rng: &mut impl RngCore,
) {
    for (i, ivc_step_input) in ivc_step_inputs.into_iter().enumerate() {
        info_span!("Fold step", completed = i).in_scope(|| {
            let input = Circuit::ExternalInputs::from_vec(ivc_step_input);
            folding
                .prove_step(&mut *rng, input, None)
                .expect("Failed to prove step")
        });
    }
}

#[tracing::instrument(name = "Verify folded proof", skip_all)]
pub fn verify_folding<Circuit: FCircuit<Fr>>(
    folding: &Folding<Circuit>,
    folding_params: &FoldingParams<Circuit>,
) {
    Folding::<Circuit>::verify(folding_params.1.clone(), folding.ivc_proof())
        .expect("Failed to verify folded proof");
}

#[tracing::instrument(name = "Verify final state", skip_all)]
pub fn verify_final_state_arkworks<Circuit: FCircuit<Fr>>(
    folding: &Folding<Circuit>,
    config: &Config,
) {
    assert_eq!(config.backend, Backend::Sonobe);
    assert_eq!(config.frontend, Frontend::Arkworks);

    let final_state = &folding.z_i;

    let nsteps = if config.demo {
        DEMO_STEPS
    } else if config.function == Redact {
        config.resolution.iteration_count_block_based()
    } else {
        config.resolution.iteration_count()
    };

    let source_hashing_steps = if config.function == Resize && config.demo {
        3 * nsteps
    } else {
        nsteps
    };
    let target_hashing_steps = if config.function == Resize && config.demo {
        2 * nsteps
    } else {
        nsteps
    };

    assert_eq!(folding.i, Fr::from(nsteps as u128));

    if let Some(source_image) = &config.source_image {
        let source_hash = hash_image_arkworks::<Fr>(
            source_image,
            config.function.hash_mode(),
            Some(source_hashing_steps),
        );
        assert_eq!(
            final_state[0], source_hash,
            "Source image hash does not match final state"
        );
    }

    if config.function != Crop || !config.demo {
        if let Some(target_image) = &config.target_image {
            let target_hash = hash_image_arkworks::<Fr>(
                target_image,
                config.function.hash_mode(),
                Some(target_hashing_steps),
            );
            assert_eq!(
                final_state[1], target_hash,
                "Target image hash does not match final state"
            );
        }
    }
}
