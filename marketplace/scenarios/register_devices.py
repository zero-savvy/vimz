from vimz_marketplace_sdk.account import get_actor
from vimz_marketplace_sdk.contracts.device_registry import deploy, register_brand


def main():
    device_registry_admin = get_actor("device_registry_admin")

    registry_address = deploy(device_registry_admin).address

    camera_brand_1 = get_actor("camera_brand_1")
    camera_brand_2 = get_actor("camera_brand_2")

    register_brand(registry_address, device_registry_admin, camera_brand_1)
    register_brand(registry_address, device_registry_admin, camera_brand_2)


if __name__ == "__main__":
    main()
