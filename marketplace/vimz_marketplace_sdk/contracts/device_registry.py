from vimz_marketplace_sdk.chain import Actor
from vimz_marketplace_sdk.contracts.contract import VimzContract
from vimz_marketplace_sdk.device import Device
from vimz_marketplace_sdk.logging_config import logger


class DeviceRegistry(VimzContract):
    @classmethod
    def contract_file_name(cls) -> str:
        return "DeviceRegistry"

    def register_brand(self, admin: Actor, brand: Actor):
        receipt = self.call(admin, "registerRegistrar", brand.address())
        logger.info(
            f"✅ Brand '{brand.name()}' registered in DeviceRegistry ({receipt['gasUsed']:_} gas)."
        )

    def register_device(self, brand: Actor, device: Device):
        receipt = self.call(brand, "registerDevice", device.address())
        logger.info(
            f"✅ Device '{device.name()}' (by '{brand.name()}') registered in DeviceRegistry ({receipt['gasUsed']:_} gas)."
        )
