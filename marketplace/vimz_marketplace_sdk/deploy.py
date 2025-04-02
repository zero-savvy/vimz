from web3.middleware import SignAndSendRawMiddlewareBuilder

from vimz_marketplace_sdk.artifacts import load_artifact
from vimz_marketplace_sdk.chain import get_web3
from vimz_marketplace_sdk.types import Actor
from web3.contract.contract import Contract


def deploy_contract(contract_name: str, deployer: Actor, *constructor_args, **constructor_kwargs) -> Contract:
    print(f"Deploying contract '{contract_name}'...")
    artifact = load_artifact(contract_name)

    w3 = get_web3()
    w3.middleware_onion.inject(SignAndSendRawMiddlewareBuilder.build(deployer.account()), layer=0)
    ContractCls = w3.eth.contract(abi=artifact["abi"], bytecode=artifact["bytecode"]["object"])

    tx_hash = ContractCls.constructor(*constructor_args, **constructor_kwargs).transact()
    receipt = w3.eth.wait_for_transaction_receipt(tx_hash)

    print(f"Contract '{contract_name}' deployed at address: {receipt.contractAddress}")

    return w3.eth.contract(
        address=receipt.contractAddress,
        abi=artifact["abi"]
    )
