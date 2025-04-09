from abc import ABC, abstractmethod

from eth_typing import ChecksumAddress
from web3.contract import Contract
from web3.middleware import SignAndSendRawMiddlewareBuilder

from vimz_marketplace_sdk.chain import Actor, deploy_contract


class VimzContract(ABC):
    def __init__(self, contract: Contract):
        self._contract = contract

    @classmethod
    @abstractmethod
    def contract_file_name(cls) -> str:
        pass

    @classmethod
    def contract_name(cls) -> str:
        return cls.contract_file_name()

    def address(self) -> ChecksumAddress:
        return self._contract.address

    @classmethod
    def deploy(cls, deployer: Actor, *args) -> "VimzContract":
        return cls(
            deploy_contract((cls.contract_file_name(), cls.contract_name()), deployer, *args)
        )

    def set_caller(self, caller: Actor):
        self._contract.w3.middleware_onion.remove("signer")
        self._contract.w3.middleware_onion.inject(
            SignAndSendRawMiddlewareBuilder.build(caller.key()), "signer", layer=0
        )
        self._contract.w3.eth.default_account = caller.address()

    def call(self, caller: Actor, function: str, *args):
        self.set_caller(caller)
        function = getattr(self._contract.functions, function)
        calldata = function(*args)
        tx_hash = calldata.transact()
        self._contract.w3.eth.wait_for_transaction_receipt(tx_hash)
