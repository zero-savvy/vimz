from vimz_marketplace_sdk.chain import Actor
from vimz_marketplace_sdk.contracts.contract import VimzContract
from vimz_marketplace_sdk.device import Device


class DeviceRegistry(VimzContract):
    @classmethod
    def contract_name(cls) -> str:
        return "DeviceRegistry"

    def register_brand(self, admin: Actor, brand: Actor):
        self.call(admin, "registerRegistrar", brand.address())
        print(f"✅ Brand '{brand.name()}' registered in DeviceRegistry.")

    def register_device(self, brand: Actor, device: Device):
        self.call(brand, "registerDevice", device.address())
        print(f"✅ Device '{device.name()}' (by '{brand.name()}') registered in DeviceRegistry.")
