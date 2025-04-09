from vimz_marketplace_sdk.chain import get_actor
from vimz_marketplace_sdk.contracts.device_registry import DeviceRegistry
from vimz_marketplace_sdk.device import default_brands, get_brand


def main():
    device_registry_admin = get_actor("device_registry_admin")
    registry = DeviceRegistry.deploy(device_registry_admin)

    # Create and register custom brand and devices
    leica = get_brand("Leica", ["SL3-S"])
    registry.register_brand(device_registry_admin, leica)
    registry.register_device(leica, leica.get_new_device())

    # or use default brands
    for brand in default_brands():
        registry.register_brand(device_registry_admin, brand)
        for _ in range(6):
            registry.register_device(brand, brand.get_new_device())


if __name__ == "__main__":
    main()
