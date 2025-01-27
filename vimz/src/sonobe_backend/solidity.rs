use std::fs;
use ark_bn254::Fr;
use sonobe::{folding::nova::decider_eth::prepare_calldata, frontend::FCircuit};
use sonobe_frontends::circom::CircomFCircuit;
use sonobe_solidity::{
    get_decider_template_for_cyclefold_decider,
    utils::get_function_selector_for_nova_cyclefold_verifier, NovaCycleFoldVerifierKey,
};

use crate::sonobe_backend::{
    decider::{DeciderProof, DeciderVerifierParam},
    folding::Folding,
};

/// Converts the given Nova folding and proof into calldata that can be used to call the on-chain
/// verifier.
pub fn prepare_contract_calldata(
    f_circuit: &CircomFCircuit<Fr>,
    decider_vp: DeciderVerifierParam,
    nova: &Folding,
    proof: DeciderProof,
) -> Vec<u8> {
    let nova_cyclefold_vk = NovaCycleFoldVerifierKey::from((decider_vp, f_circuit.state_len()));
    let decider_solidity_code = get_decider_template_for_cyclefold_decider(nova_cyclefold_vk);

    fs::write("temp.sol", decider_solidity_code).expect("Failed to write calldata to file");

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
