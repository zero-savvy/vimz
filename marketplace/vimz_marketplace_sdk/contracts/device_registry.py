from eth_typing import ChecksumAddress, Address

from vimz_marketplace_sdk.chain import get_web3
from vimz_marketplace_sdk.contracts.contract import VimzContract
from vimz_marketplace_sdk.types import Actor


class DeviceRegistry(VimzContract):
    @classmethod
    def contract_name(cls) -> str:
        return "DeviceRegistry"

    def register_brand(self, admin: Actor, brand: Actor):
        self.set_caller(admin)

        tx_hash = self._contract.functions.registerRegistrar(brand.address()).transact()
        self._contract.w3.eth.wait_for_transaction_receipt(tx_hash)

        print(f"✅ Brand '{brand.name()}' registered in DeviceRegistry.")

    def register_device(self, brand: Actor, device: Address):
        self.set_caller(brand)

        tx_hash = self._contract.functions.registerDevice(device).transact()
        self._contract.w3.eth.wait_for_transaction_receipt(tx_hash)

        print(f"✅ Device '{device}' (by '{brand.name()}') registered in DeviceRegistry.")
