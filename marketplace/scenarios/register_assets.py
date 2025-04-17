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

    logger.start_section("Register original assets")
    img1_asset_id = gateway.register_new_asset(
        creator, get_image_hash("img1"), datetime.now(UTC), License.FULLY_FREE, device
    )
    img2_asset_id = gateway.register_new_asset(
        creator, get_image_hash("img2"), datetime.now(UTC), License.FULLY_FREE, device
    )

    logger.start_section("Register editions of `img1`")
    for asset_name, transformation in [
        ("img1-grayscale", Transformation.GRAYSCALE),
        # ("img1-sharpness", Transformation.SHARPNESS),
    ]:
        gateway.register_edited_asset(
            creator,
            get_image_hash(asset_name),
            img1_asset_id,
            transformation,
            get_proof(asset_name),
            License.FULLY_FREE,
        )

    logger.start_section("Register editions of `img2`")
    for asset_name, transformation in [
        ("img2-contrast", Transformation.CONTRAST),
    ]:
        gateway.register_edited_asset(
            creator,
            get_image_hash(asset_name),
            img2_asset_id,
            transformation,
            get_proof(asset_name),
            License.FULLY_FREE,
        )


if __name__ == "__main__":
    main()
