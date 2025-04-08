from datetime import datetime, UTC

from scenarios import prepare_device_registry, prepare_creator_registry
from vimz_marketplace_sdk.artifacts import get_image_hash
from vimz_marketplace_sdk.chain import get_actor
from vimz_marketplace_sdk.contracts.asset_gateway import AssetGateway
from vimz_marketplace_sdk.types import License, Transformation


def main():
    device_registry, device = prepare_device_registry()
    creator_registry, creator = prepare_creator_registry()

    gateway = AssetGateway.deploy(get_actor("gateway_deployer"),
                                  creator_registry.address(),
                                  device_registry.address())

    gateway.register_new_asset(
        creator,
        get_image_hash("img1"),
        datetime.now(UTC),
        License.FULLY_FREE,
        device
    )

    gateway.register_edited_asset(
        creator,
        get_image_hash("img1-grayscale"),
        1,
        Transformation.GRAYSCALE,
        License.FULLY_FREE
    )


if __name__ == "__main__":
    main()
