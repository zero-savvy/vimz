from datetime import datetime, UTC

from scenarios import prepare_device_registry, prepare_creator_registry
from vimz_marketplace_sdk.chain import get_actor
from vimz_marketplace_sdk.contracts.asset_gateway import AssetGateway
from vimz_marketplace_sdk.types import License


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
