mod compression;
mod ivc_state;
mod kernel;
mod macros;
mod pixel;
mod step_input;
mod transformations;

use ark_crypto_primitives::sponge::poseidon::PoseidonConfig;
use ark_ff::PrimeField;
pub use transformations::*;

/// Generates a Poseidon configuration to be used both in the circuits and off-circuit to hash an image.
///
/// We use rate 16:1, alpha 5 (standard S-box), 8 full rounds, and 68 partial rounds (as per Circom specification:
/// https://github.com/iden3/circomlib/blob/master/circuits/poseidon.circom). This configuration should still guarantee
/// 128-bit security level.
pub fn poseidon_config<F: PrimeField>() -> PoseidonConfig<F> {
    let full_rounds = 8;
    let partial_rounds = 68;
    let alpha = 5;
    let rate = 16;

    let (ark, mds) = ark_crypto_primitives::sponge::poseidon::find_poseidon_ark_and_mds::<F>(
        F::MODULUS_BIT_SIZE as u64,
        rate,
        full_rounds,
        partial_rounds,
        0,
    );

    PoseidonConfig::new(
        full_rounds as usize,
        partial_rounds as usize,
        alpha,
        mds,
        ark,
        rate,
        1,
    )
}
