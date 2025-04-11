from datetime import UTC, datetime

from scenarios import prepare_creator_registry, prepare_device_registry
from vimz_marketplace_sdk.artifacts import get_image_hash, get_proof
from vimz_marketplace_sdk.chain import get_actor
from vimz_marketplace_sdk.contracts.asset_gateway import AssetGateway
from vimz_marketplace_sdk.logging_config import logger
from vimz_marketplace_sdk.types import License, Transformation


def main():
    logger.start_section("Prepare devices and creators")
    device_registry, device = prepare_device_registry()
    creator_registry, creator = prepare_creator_registry()

    logger.start_section("Prepare asset gateway")
    gateway = AssetGateway.deploy(
        get_actor("gateway_deployer"),
        creator_registry.address(),
        device_registry.address(),
    )

    logger.start_section("Register assets")
    original_asset_id = gateway.register_new_asset(
        creator, get_image_hash("img1"), datetime.now(UTC), License.FULLY_FREE, device
    )
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
