from datetime import datetime, UTC

from vimz_marketplace_sdk.chain import get_actor, Actor
from vimz_marketplace_sdk.contracts.asset_gateway import AssetGateway
from vimz_marketplace_sdk.contracts.creator_registry import CreatorRegistry
from vimz_marketplace_sdk.contracts.device_registry import DeviceRegistry
from vimz_marketplace_sdk.creator import default_creators
from vimz_marketplace_sdk.device import get_device, Device, default_brands
from vimz_marketplace_sdk.types import License


def prepare_device_registry() -> (DeviceRegistry, Device):
    device_registry_admin = get_actor("device_registry_admin")
    registry = DeviceRegistry.deploy(device_registry_admin)

    brand = next(default_brands())
    registry.register_brand(device_registry_admin, brand)

    device = brand.get_new_device()
    registry.register_device(brand, device)

    return registry, device


def prepare_creator_registry() -> (CreatorRegistry, Actor):
    creator_registry_admin = get_actor("creator_registry_admin")
    registry = CreatorRegistry.deploy(creator_registry_admin)

    creator = next(default_creators())
    registry.register_creator(creator_registry_admin, creator)

    return registry, creator


def main():
    device_registry, device = prepare_device_registry()
    creator_registry, creator = prepare_creator_registry()

    gateway = AssetGateway.deploy(get_actor("gateway_deployer"),
                                  creator_registry.address(),
                                  device_registry.address())

    gateway.register_new_asset(
        creator,
        41,
        datetime.now(UTC),
        License.FULLY_FREE,
        device
    )


if __name__ == "__main__":
    main()
