use sonobe::folding::nova::decider_eth::prepare_calldata;
use sonobe_solidity::utils::get_function_selector_for_nova_cyclefold_verifier;

use crate::sonobe_backend::{decider::DeciderProof, folding::Folding};

/// Converts the given Nova folding and proof into calldata that can be used to call the on-chain
/// verifier.
pub fn prepare_contract_calldata(nova: &Folding, proof: DeciderProof) -> Vec<u8> {
    let function_selector =
        get_function_selector_for_nova_cyclefold_verifier(nova.z_0.len() * 2 + 1);
    prepare_calldata(
        function_selector,
        nova.i,
        nova.z_0.clone(),
        nova.z_i.clone(),
        &nova.U_i,
        &nova.u_i,
        proof,
    )
    .expect("Failed to prepare calldata")
}
