from vimz_marketplace_sdk.account import get_actor, get_device
from vimz_marketplace_sdk.contracts.device_registry import deploy, register_brand, register_device


def main():
    device_registry_admin = get_actor("device_registry_admin")

    registry_address = deploy(device_registry_admin).address

    leica = get_actor("Leica")
    canon = get_actor("Canon")

    register_brand(registry_address, device_registry_admin, leica)
    register_brand(registry_address, device_registry_admin, canon)

    for leica_camera in [get_device("Leica SL3-S #1"), get_device("Leica SL3-S #2"), get_device("Leica M11-D #1")]:
        register_device(registry_address, leica, leica_camera.address())

    for canon_camera in [get_device("Canon EOS R1 #1"), get_device("Canon EOS R1 #2")]:
        register_device(registry_address, canon, canon_camera.address())


if __name__ == "__main__":
    main()
