from vimz_marketplace_sdk.account import get_actor
from vimz_marketplace_sdk.deploy import deploy_contract


def main():
    device_registry_admin = get_actor("device_registry_admin")
    
    deploy_contract("DeviceRegistry", device_registry_admin)

    camera_brand_1 = get_actor("camera_brand_1")
    camera_brand_2 = get_actor("camera_brand_2")


if __name__ == "__main__":
    main()
