from vimz_marketplace_sdk.account import get_actor, get_device
from vimz_marketplace_sdk.contracts.device_registry import DeviceRegistry


def main():
    device_registry_admin = get_actor("device_registry_admin")

    registry = DeviceRegistry.deploy(device_registry_admin)

    leica = get_actor("Leica")
    canon = get_actor("Canon")

    registry.register_brand(device_registry_admin, leica)
    registry.register_brand(device_registry_admin, canon)

    for leica_camera in [get_device("Leica SL3-S #1"), get_device("Leica SL3-S #2"), get_device("Leica M11-D #1")]:
        registry.register_device(leica, leica_camera.address())

    for canon_camera in [get_device("Canon EOS R1 #1"), get_device("Canon EOS R1 #2")]:
        registry.register_device(canon, canon_camera.address())


if __name__ == "__main__":
    main()
