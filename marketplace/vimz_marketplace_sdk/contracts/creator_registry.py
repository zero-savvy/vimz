from eth_typing import ChecksumAddress, Address
from web3.contract import Contract

from vimz_marketplace_sdk.artifacts import load_artifact
from vimz_marketplace_sdk.chain import deploy_contract, get_web3
from vimz_marketplace_sdk.creator import Creator
from vimz_marketplace_sdk.types import Actor


def deploy(admin: Actor) -> Contract:
    return deploy_contract("CreatorRegistry", admin)


def register_creator(registry_address: ChecksumAddress, admin: Actor, creator: Creator):
    w3 = get_web3(admin)
    registry = _instance(w3, registry_address)

    function = registry.functions.registerCreator
    tx_hash = (function(creator.address(), creator.kyc_expiration(), creator.email()).transact())
    w3.eth.wait_for_transaction_receipt(tx_hash)

    print(f"✅ Creator '{creator.name()}' registered in CreatorRegistry.")


def _instance(w3, address):
    return w3.eth.contract(address=address, abi=load_artifact("CreatorRegistry")["abi"])
