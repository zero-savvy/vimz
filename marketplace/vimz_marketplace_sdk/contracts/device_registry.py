from eth_typing import ChecksumAddress
from web3.contract import Contract

from vimz_marketplace_sdk.artifacts import load_artifact
from vimz_marketplace_sdk.chain import deploy_contract, get_web3
from vimz_marketplace_sdk.types import Actor


def deploy(admin: Actor) -> Contract:
    return deploy_contract("DeviceRegistry", admin)


def register_brand(registry_address: ChecksumAddress, admin: Actor, brand: Actor):
    w3 = get_web3(admin)
    registry = w3.eth.contract(address=registry_address, abi=load_artifact("DeviceRegistry")["abi"])

    tx_hash = registry.functions.registerRegistrar(brand.address()).transact()
    w3.eth.wait_for_transaction_receipt(tx_hash)

    print(f"✅ Brand '{brand.name()}' registered with DeviceRegistry.")
