from eth_typing import ChecksumAddress, Address
from web3.contract import Contract

from vimz_marketplace_sdk.artifacts import load_artifact
from vimz_marketplace_sdk.chain import deploy_contract, get_web3
from vimz_marketplace_sdk.types import Actor


def deploy(admin: Actor) -> Contract:
    return deploy_contract("DeviceRegistry", admin)


def register_brand(registry_address: ChecksumAddress, admin: Actor, brand: Actor):
    w3 = get_web3(admin)
    registry = _instance(w3, registry_address)

    tx_hash = registry.functions.registerRegistrar(brand.address()).transact()
    w3.eth.wait_for_transaction_receipt(tx_hash)

    print(f"✅ Brand '{brand.name()}' registered in DeviceRegistry.")


def register_device(registry_address: ChecksumAddress, brand: Actor, device: Address):
    w3 = get_web3(brand)
    registry = _instance(w3, registry_address)

    tx_hash = registry.functions.registerDevice(device).transact()
    w3.eth.wait_for_transaction_receipt(tx_hash)

    print(f"✅ Device '{device}' (by '{brand.name()}') registered in DeviceRegistry.")


def _instance(w3, address):
    return w3.eth.contract(address=address, abi=load_artifact("DeviceRegistry")["abi"])
