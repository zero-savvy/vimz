from datetime import UTC, datetime

from scenarios import prepare_creator_registry, prepare_device_registry
from vimz_marketplace_sdk.artifacts import get_image_hash, get_proof
from vimz_marketplace_sdk.chain import get_actor
from vimz_marketplace_sdk.contracts.asset_gateway import AssetGateway
from vimz_marketplace_sdk.logging_config import logger
from vimz_marketplace_sdk.types import License, Transformation


def main():
    logger.start_section("Prepare device and creator registries")
    device_registry, device = prepare_device_registry()
    creator_registry, creator = prepare_creator_registry()

    logger.start_section("Prepare asset gateway")
    gateway = AssetGateway.deploy(
        get_actor("gateway_deployer"),
        creator_registry.address(),
        device_registry.address(),
    )

    logger.start_section("Register new asset")
    original_asset_id = gateway.register_new_asset(
        creator, get_image_hash("img1"), datetime.now(UTC), License.FULLY_FREE, device
    )

    logger.start_section("Register edited asset")
    gateway.register_edited_asset(
        creator,
        get_image_hash("img1-grayscale"),
        original_asset_id,
        Transformation.GRAYSCALE,
        get_proof("img1-grayscale"),
        License.FULLY_FREE,
    )


if __name__ == "__main__":
    main()
