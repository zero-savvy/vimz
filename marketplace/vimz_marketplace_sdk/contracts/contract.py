from abc import ABC, abstractmethod

from eth_typing import ChecksumAddress
from web3.contract import Contract
from web3.middleware import SignAndSendRawMiddlewareBuilder
from web3.types import TxReceipt

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

    def call(self, caller: Actor, function: str, *args) -> TxReceipt:
        self.set_caller(caller)

        function = getattr(self._contract.functions, function)
        calldata = function(*args)

        tx_hash = calldata.transact()
        return self._contract.w3.eth.wait_for_transaction_receipt(tx_hash)

    def call_and_get_event(self, caller: Actor, function: str, event: str, *args) -> dict:
        receipt = self.call(caller, function, *args)
        event_type = getattr(self._contract.events, event)
        events = event_type.process_receipt(receipt)
        return events[0]["args"]
