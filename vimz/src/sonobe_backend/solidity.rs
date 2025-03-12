use ark_bn254::Fr;
use sonobe::frontend::FCircuit;
use sonobe_solidity::calldata::{
    prepare_calldata_for_nova_cyclefold_verifier, NovaVerificationMode,
};

use crate::sonobe_backend::{decider::DeciderProof, folding::Folding};

/// Converts the given Nova folding and proof into calldata that can be used to call the on-chain
/// verifier.
///
/// The targeted contract function is `verifyOpaqueNovaProofWithInputs`.
pub fn prepare_contract_calldata<Circuit: FCircuit<Fr>>(
    nova: &Folding<Circuit>,
    proof: &DeciderProof<Circuit>,
) -> Vec<u8> {
    prepare_calldata_for_nova_cyclefold_verifier(
        NovaVerificationMode::OpaqueWithInputs,
        nova.i,
        nova.z_0.clone(),
        nova.z_i.clone(),
        &nova.U_i,
        &nova.u_i,
        &proof,
    )
    .expect("Failed to prepare calldata")
}
