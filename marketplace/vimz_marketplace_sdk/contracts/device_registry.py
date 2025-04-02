from vimz_marketplace_sdk.web3_client import get_web3
from vimz_marketplace_sdk.artifacts import load_artifact
from vimz_marketplace_sdk.chain import send_transaction

def load_contract(contract_address, contract_name):
    """
    Loads a deployed contract instance using its address and the contract name.
    """
    artifact = load_artifact(contract_name)
    web3 = get_web3()
    contract = web3.eth.contract(address=contract_address, abi=artifact["abi"])
    return contract

def register_device_manufacturer(contract, registrar_account, manufacturer_address, gas=200000, gasPrice_gwei=20):
    """
    Calls the contract method to register a device manufacturer.
    """
    web3 = get_web3()
    nonce = web3.eth.get_transaction_count(registrar_account["address"])
    tx = contract.functions.registerRegistrar(manufacturer_address).buildTransaction({
        'from': registrar_account["address"],
        'nonce': nonce,
        'gas': gas,
        'gasPrice': web3.toWei(gasPrice_gwei, 'gwei')
    })
    receipt = send_transaction(tx, registrar_account["private_key"])
    return receipt

def register_device(contract, registrar_account, device_public_key, signature_scheme, gas=200000, gasPrice_gwei=20):
    """
    Calls the contract method to register a device.
    """
    web3 = get_web3()
    nonce = web3.eth.get_transaction_count(registrar_account["address"])
    tx = contract.functions.registerDevice(device_public_key, signature_scheme).buildTransaction({
        'from': registrar_account["address"],
        'nonce': nonce,
        'gas': gas,
        'gasPrice': web3.toWei(gasPrice_gwei, 'gwei')
    })
    receipt = send_transaction(tx, registrar_account["private_key"])
    return receipt
