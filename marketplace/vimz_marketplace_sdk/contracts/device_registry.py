from eth_typing import ChecksumAddress

from vimz_marketplace_sdk.chain import Actor
from vimz_marketplace_sdk.contracts.contract import VimzContract


class DeviceRegistry(VimzContract):
    @classmethod
    def contract_name(cls) -> str:
        return "DeviceRegistry"

    def register_brand(self, admin: Actor, brand: Actor):
        self.call(admin, "registerRegistrar", brand.address())
        print(f"✅ Brand '{brand.name()}' registered in DeviceRegistry.")

    def register_device(self, brand: Actor, device: ChecksumAddress):
        self.call(brand, "registerDevice", device)
        print(f"✅ Device '{device}' (by '{brand.name()}') registered in DeviceRegistry.")
