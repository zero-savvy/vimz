from vimz_marketplace_sdk.chain import get_actor
from vimz_marketplace_sdk.contracts.device_registry import DeviceRegistry
from vimz_marketplace_sdk.device import default_brands, get_brand
from vimz_marketplace_sdk.logging_config import logger


def main():
    logger.start_section("Create device registry")
    device_registry_admin = get_actor("device_registry_admin")
    registry = DeviceRegistry.deploy(device_registry_admin)

    logger.start_section("Create and register custom brand and devices")
    leica = get_brand("Leica", ["SL3-S"])
    registry.register_brand(device_registry_admin, leica)
    registry.register_device(leica, leica.get_new_device())

    logger.start_section("Register default brands and devices")
    for brand in default_brands():
        registry.register_brand(device_registry_admin, brand)
        for _ in range(6):
            registry.register_device(brand, brand.get_new_device())


if __name__ == "__main__":
    main()
