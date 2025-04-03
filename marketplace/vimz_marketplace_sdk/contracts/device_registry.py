from eth_typing import ChecksumAddress, Address

from vimz_marketplace_sdk.chain import get_web3
from vimz_marketplace_sdk.contracts.contract import VimzContract
from vimz_marketplace_sdk.types import Actor


class DeviceRegistry(VimzContract):
    @classmethod
    def contract_name(cls) -> str:
        return "DeviceRegistry"

    def register_brand(self, admin: Actor, brand: Actor):
        self.call(admin, "registerRegistrar", brand.address())
        print(f"✅ Brand '{brand.name()}' registered in DeviceRegistry.")

    def register_device(self, brand: Actor, device: Address):
        self.call(brand, "registerDevice", device)
        print(f"✅ Device '{device}' (by '{brand.name()}') registered in DeviceRegistry.")
