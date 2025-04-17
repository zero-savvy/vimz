import itertools

from vimz_marketplace_sdk.chain import Actor, get_actor
from vimz_marketplace_sdk.contracts.creator_registry import CreatorRegistry
from vimz_marketplace_sdk.contracts.device_registry import DeviceRegistry
from vimz_marketplace_sdk.contracts.image_gateway import ImageGateway
from vimz_marketplace_sdk.creator import Creator, default_creators
from vimz_marketplace_sdk.device import Brand, Device, default_brands


class Setup:
    def __init__(
        self,
        device_registry: DeviceRegistry,
        creator_registry: CreatorRegistry,
        gateway: ImageGateway,
        brands: list[Brand],
        devices: list[Device],
        creators: list[Creator],
    ):
        self.device_registry = device_registry
        self.creator_registry = creator_registry
        self.gateway = gateway
        self.brands = brands
        self.devices = devices
        self.creators = creators


def full_setup(
    num_actors: int = 1,
) -> Setup:
    device_registry, brands, devices = prepare_device_registry(num_actors)
    creator_registry, creators = prepare_creator_registry(num_actors)

    gateway = ImageGateway.deploy(
        get_actor("gateway_deployer"),
        creator_registry.address(),
        device_registry.address(),
    )

    return Setup(
        device_registry,
        creator_registry,
        gateway,
        brands,
        devices,
        creators,
    )


def prepare_device_registry(num_devices: int) -> (DeviceRegistry, list[Brand], list[Device]):
    device_registry_admin = get_actor("device_registry_admin")
    registry = DeviceRegistry.deploy(device_registry_admin)

    brands = list(itertools.islice(default_brands(), min(2, num_devices)))
    for brand in brands:
        registry.register_brand(device_registry_admin, brand)

    devices = []
    for i in range(num_devices):
        brand = brands[i % len(brands)]
        device = brand.get_new_device()
        registry.register_device(brand, device)
        devices.append(device)

    return registry, brands, devices


def prepare_creator_registry(num_creators) -> (CreatorRegistry, list[Actor]):
    creator_registry_admin = get_actor("creator_registry_admin")
    registry = CreatorRegistry.deploy(creator_registry_admin)

    creators = list(itertools.islice(default_creators(), num_creators))
    assert len(creators) == num_creators, "Not enough default creators available"
    for creator in creators:
        registry.register_creator(creator_registry_admin, creator)

    return registry, creators
