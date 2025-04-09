from vimz_marketplace_sdk.chain import Actor, get_actor
from vimz_marketplace_sdk.contracts.creator_registry import CreatorRegistry
from vimz_marketplace_sdk.contracts.device_registry import DeviceRegistry
from vimz_marketplace_sdk.creator import default_creators
from vimz_marketplace_sdk.device import Device, default_brands


def prepare_device_registry() -> (DeviceRegistry, Device):
    """
    Prepare a device registry and register a default brand and device.
    :return: A tuple containing the device registry and the registered device.
    """
    device_registry_admin = get_actor("device_registry_admin")
    registry = DeviceRegistry.deploy(device_registry_admin)

    brand = next(default_brands())
    registry.register_brand(device_registry_admin, brand)

    device = brand.get_new_device()
    registry.register_device(brand, device)

    return registry, device


def prepare_creator_registry() -> (CreatorRegistry, Actor):
    """
    Prepare a creator registry and register a default creator.
    :return: A tuple containing the creator registry and the registered creator.
    """
    creator_registry_admin = get_actor("creator_registry_admin")
    registry = CreatorRegistry.deploy(creator_registry_admin)

    creator = next(default_creators())
    registry.register_creator(creator_registry_admin, creator)

    return registry, creator
