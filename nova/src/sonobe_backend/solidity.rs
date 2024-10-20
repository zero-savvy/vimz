use ark_bn254::Fr;
use sonobe::{
    folding::nova::decider_eth::prepare_calldata,
    frontend::{circom::CircomFCircuit, FCircuit},
};
use sonobe_solidity::{
    evm::{compile_solidity, Evm},
    get_decider_template_for_cyclefold_decider,
    utils::get_function_selector_for_nova_cyclefold_verifier,
    NovaCycleFoldVerifierKey,
};

use crate::{
    sonobe_backend::{
        decider::{DeciderProof, DeciderVerifierParam},
        folding::Folding,
    },
    time::measure,
};

/// Verifies the given Nova folding and proof on-chain.
pub fn verify_on_chain(
    f_circuit: &CircomFCircuit<Fr>,
    decider_vp: DeciderVerifierParam,
    nova: Folding,
    proof: DeciderProof,
) {
    let nova_cyclefold_verifier_bytecode = measure("Generate verifier contract", || {
        generate_solidity_verifier(f_circuit, decider_vp)
    });
    let calldata = measure("Prepare calldata", || {
        prepare_contract_calldata(nova, proof)
    });

    let mut evm = Evm::default();
    let verifier_address = evm.create(nova_cyclefold_verifier_bytecode);
    let (gas, output) = evm.call(verifier_address, calldata.clone());
    println!("Gas used: {gas}");
    assert_eq!(*output.last().unwrap(), 1);
}

/// Generates the Solidity verifier for the given circom circuit and DeciderVerifierParam.
fn generate_solidity_verifier(
    f_circuit: &CircomFCircuit<Fr>,
    decider_vp: DeciderVerifierParam,
) -> Vec<u8> {
    let nova_cyclefold_vk = NovaCycleFoldVerifierKey::from((decider_vp, f_circuit.state_len()));
    let decider_solidity_code = get_decider_template_for_cyclefold_decider(nova_cyclefold_vk);
    compile_solidity(decider_solidity_code, "NovaDecider")
}

/// Converts the given Nova folding and proof into calldata that can be used to call the on-chain
/// verifier.
fn prepare_contract_calldata(nova: Folding, proof: DeciderProof) -> Vec<u8> {
    let function_selector =
        get_function_selector_for_nova_cyclefold_verifier(nova.z_0.len() * 2 + 1);
    prepare_calldata(
        function_selector,
        nova.i,
        nova.z_0,
        nova.z_i,
        &nova.U_i,
        &nova.u_i,
        proof,
    )
    .expect("Failed to prepare calldata")
}
