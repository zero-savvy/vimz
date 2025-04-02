import os

from web3 import Web3
from web3.middleware import SignAndSendRawMiddlewareBuilder
from web3.types import Wei

from vimz_marketplace_sdk.types import Actor


def send_eth(from_actor: Actor, to_actor: Actor, value_wei: Wei):
    tx = {
        'from': from_actor.address(),
        'to': to_actor.address(),
        'value': value_wei,
    }

    w3 = get_web3()
    w3.middleware_onion.inject(SignAndSendRawMiddlewareBuilder.build(from_actor.key()), layer=0)
    tx_hash = w3.eth.send_transaction(tx)
    w3.eth.wait_for_transaction_receipt(tx_hash)

    print(
        f"Sent {value_wei} wei from '{from_actor.name()}' to '{to_actor.name()}' with tx hash: '{tx_hash.to_0x_hex()}'. "
        f"Current balance of '{to_actor.name()}': {get_web3().eth.get_balance(to_actor.address())} wei.")


def get_web3() -> Web3:
    # Use an environment variable if available; default to localhost Anvil endpoint.
    rpc_endpoint = os.getenv('RPC_ENDPOINT', 'http://localhost:8545')
    web3 = Web3(Web3.HTTPProvider(rpc_endpoint))
    if not web3.is_connected():
        raise ConnectionError(f"Unable to connect to RPC endpoint: {rpc_endpoint}")
    return web3
