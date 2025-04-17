from vimz_marketplace_sdk.chain import Actor, get_actor
from vimz_marketplace_sdk.contracts.asset_gateway import AssetGateway
from vimz_marketplace_sdk.contracts.creator_registry import CreatorRegistry
from vimz_marketplace_sdk.contracts.device_registry import DeviceRegistry
from vimz_marketplace_sdk.creator import Creator, default_creators
from vimz_marketplace_sdk.device import Brand, Device, default_brands


def prepare_device_registry(num_devices: int) -> (DeviceRegistry, list[Brand], list[Device]):
    device_registry_admin = get_actor("device_registry_admin")
    registry = DeviceRegistry.deploy(device_registry_admin)

    num_brands = min(num_devices, 2)  # we have only 2 default brands
    brands = []
    for _ in range(num_brands):
        brand = next(default_brands())
        registry.register_brand(device_registry_admin, brand)
        brands.append(brand)

    devices = []
    for i in range(num_devices):
        brand = brands[i % num_brands]
        device = brand.get_new_device()
        registry.register_device(brand, device)
        devices.append(device)

    return registry, brands, devices


def prepare_creator_registry(num_creators) -> (CreatorRegistry, list[Actor]):
    creator_registry_admin = get_actor("creator_registry_admin")
    registry = CreatorRegistry.deploy(creator_registry_admin)

    creators = []
    for _ in range(num_creators):
        creator = next(default_creators())
        registry.register_creator(creator_registry_admin, creator)
        creators.append(creator)

    return registry, creators


class Setup:
    def __init__(
        self,
        device_registry: DeviceRegistry,
        creator_registry: CreatorRegistry,
        gateway: AssetGateway,
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

    gateway = AssetGateway.deploy(
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
