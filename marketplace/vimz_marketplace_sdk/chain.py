import os

from eth_account import Account
from eth_account.signers.local import LocalAccount
from eth_typing import ChecksumAddress
from web3 import Web3
from web3.contract import Contract
from web3.middleware import SignAndSendRawMiddlewareBuilder
from web3.types import Wei

from vimz_marketplace_sdk.artifacts import load_artifact


CORNUCOPIA_NAME = "cornucopia"

# Standard endowment: 1 Ether (in wei)
STANDARD_ENDOWMENT = Web3.to_wei(1, 'ether')

# Global dictionary to store actor accounts.
ACTORS = {}


class Actor:
    def __init__(self, name: str, account: LocalAccount):
        self._name = name
        self._account = account

    def name(self):
        return self._name

    def account(self) -> LocalAccount:
        return self._account

    def address(self) -> ChecksumAddress:
        return self._account.address

    def key(self) -> bytes:
        return self._account.key


def get_cornucopia() -> Actor:
    return get_actor(CORNUCOPIA_NAME)


def get_actor(name: str, endowment: Wei = STANDARD_ENDOWMENT) -> Actor:
    actor = ACTORS.get(name)
    if actor:
        return actor

    if name == CORNUCOPIA_NAME:  # initialize cornucopia account
        cornucopia_key = os.environ["CORNUCOPIA_KEY"]
        new_actor = Actor(name, Account.from_key(cornucopia_key))
    else:
        new_actor = Actor(name, Account.create())
        if endowment > 0:
            print(f"⏳ Endowing new actor '{name}' with {endowment} wei...")
            send_eth(get_cornucopia(), new_actor, endowment)

    ACTORS[name] = new_actor
    return new_actor


def deploy_contract(contract_name: str, deployer: Actor, *constructor_args) -> Contract:
    print(f"⏳ Deploying contract '{contract_name}'...")
    artifact = load_artifact(contract_name)

    w3 = get_web3(deployer)
    ContractCls = w3.eth.contract(abi=artifact["abi"], bytecode=artifact["bytecode"]["object"])

    tx_hash = ContractCls.constructor(*constructor_args).transact()
    receipt = w3.eth.wait_for_transaction_receipt(tx_hash)

    print(f"✅ Contract '{contract_name}' deployed at address: {receipt["contractAddress"]}")

    return w3.eth.contract(
        address=receipt["contractAddress"],
        abi=artifact["abi"]
    )


def send_eth(from_actor: Actor, to_actor: Actor, value_wei: Wei):
    tx = {
        'from': from_actor.address(),
        'to': to_actor.address(),
        'value': value_wei,
    }

    w3 = get_web3(from_actor)
    tx_hash = w3.eth.send_transaction(tx)
    w3.eth.wait_for_transaction_receipt(tx_hash)

    print(
        f"✅ Sent {value_wei} wei from '{from_actor.name()}' to '{to_actor.name()}' with tx hash: '{tx_hash.to_0x_hex()}'. "
        f"Current balance of '{to_actor.name()}': {get_web3().eth.get_balance(to_actor.address())} wei.")


def get_web3(actor: Actor = None) -> Web3:
    # Use an environment variable if available; default to localhost Anvil endpoint.
    rpc_endpoint = os.getenv('RPC_ENDPOINT', 'http://localhost:8545')
    w3 = Web3(Web3.HTTPProvider(rpc_endpoint))
    if not w3.is_connected():
        raise ConnectionError(f"Unable to connect to RPC endpoint: {rpc_endpoint}")

    if actor is not None:
        w3.middleware_onion.inject(SignAndSendRawMiddlewareBuilder.build(actor.key()), "signer", layer=0)
        w3.eth.default_account = actor.address()

    return w3
