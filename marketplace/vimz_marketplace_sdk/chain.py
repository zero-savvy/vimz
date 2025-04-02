import os

from web3 import Web3
from web3.middleware import SignAndSendRawMiddlewareBuilder
from web3.types import Wei

from vimz_marketplace_sdk.types import Actor


#
# def send_transaction(tx, private_key):
#     web3 = get_web3()
#     signed_tx = web3.eth.account.sign_transaction(tx, private_key)
#     tx_hash = web3.eth.send_raw_transaction(signed_tx.rawTransaction)
#     receipt = web3.eth.wait_for_transaction_receipt(tx_hash)
#     return receipt
#
#
# def build_transaction(contract_function, sender, nonce, gas=2000000, gasPrice_gwei=20, **kwargs):
#     web3 = get_web3()
#     tx = contract_function.buildTransaction({
#         'from': sender["address"],
#         'nonce': nonce,
#         'gas': gas,
#         'gasPrice': web3.toWei(gasPrice_gwei, 'gwei'),
#         **kwargs
#     })
#     return tx


def send_eth(from_actor: Actor, to_actor: Actor, value_wei: Wei):
    tx = {
        'from': from_actor.address(),
        'to': to_actor.address(),
        'value': value_wei,
    }

    w3 = get_web3()
    w3.middleware_onion.inject(SignAndSendRawMiddlewareBuilder.build(from_actor.key()), layer=0)
    tx_hash = w3.eth.send_transaction(tx)

    print(f"Sent {value_wei} wei from '{from_actor.name}' to '{to_actor.name}' with tx hash: '{tx_hash.to_0x_hex()}'")


def get_web3() -> Web3:
    # Use an environment variable if available; default to localhost Anvil endpoint.
    rpc_endpoint = os.getenv('RPC_ENDPOINT', 'http://localhost:8545')
    web3 = Web3(Web3.HTTPProvider(rpc_endpoint))
    if not web3.is_connected():
        raise ConnectionError(f"Unable to connect to RPC endpoint: {rpc_endpoint}")
    return web3
