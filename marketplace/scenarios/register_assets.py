from datetime import UTC, datetime

from web3.exceptions import ContractLogicError

from scenarios import prepare_creator_registry, prepare_device_registry
from vimz_marketplace_sdk.artifacts import get_image_hash, get_proof
from vimz_marketplace_sdk.chain import get_actor
from vimz_marketplace_sdk.contracts.asset_gateway import AssetGateway
from vimz_marketplace_sdk.creator import Creator
from vimz_marketplace_sdk.device import Device
from vimz_marketplace_sdk.logging_config import logger
from vimz_marketplace_sdk.types import License, Transformation


def main():
    (gateway, creator, device) = setup()
    [img1_asset_id, img2_asset_id] = register_originals(gateway, creator, device)

    ################################################################################################

    logger.start_section("Register editions of `img1`")
    register_edition(gateway, creator, img1_asset_id, "img1-grayscale", Transformation.GRAYSCALE)
    sharpness_id = register_edition(
        gateway, creator, img1_asset_id, "img1-sharpness", Transformation.SHARPNESS
    )
    register_edition(
        gateway, creator, sharpness_id, "img1-sharpness-grayscale", Transformation.GRAYSCALE
    )

    ################################################################################################

    logger.start_section("Register editions of `img2`")
    contrast_id = register_edition(
        gateway, creator, img2_asset_id, "img2-contrast", Transformation.CONTRAST
    )
    register_edition(
        gateway, creator, contrast_id, "img2-contrast-sharpness", Transformation.SHARPNESS
    )

    ################################################################################################

    logger.start_section("Try to register the same original asset twice")
    try:
        gateway.register_new_asset(
            creator, get_image_hash("img1"), datetime.now(UTC), License.FULLY_FREE, device
        )
    except ContractLogicError as err:
        assert "revert: Image hash already registered" in err.message
        logger.info("Cannot register the same original asset twice: ✅")

    try:
        register_edition(
            gateway,
            creator,
            img1_asset_id,
            "img1-grayscale",
            Transformation.GRAYSCALE,
        )
    except ContractLogicError as err:
        assert "revert: Image hash already registered" in err.message
        logger.info("Cannot register the same edited asset twice: ✅")


def setup() -> tuple[AssetGateway, Creator, Device]:
    logger.start_section("Prepare devices and creators")
    device_registry, device = prepare_device_registry()
    creator_registry, creator = prepare_creator_registry()

    logger.start_section("Prepare asset gateway")
    gateway = AssetGateway.deploy(
        get_actor("gateway_deployer"),
        creator_registry.address(),
        device_registry.address(),
    )

    return (gateway, creator, device)


def register_originals(gateway: AssetGateway, creator: Creator, device: Device) -> list[int]:
    logger.start_section("Register original assets")
    return [
        gateway.register_new_asset(
            creator, get_image_hash(title), datetime.now(UTC), License.FULLY_FREE, device
        )
        for title in ["img1", "img2"]
    ]


def register_edition(
    gateway: AssetGateway,
    creator: Creator,
    parent_id: int,
    image_title: str,
    transformation: Transformation,
) -> int:
    return gateway.register_edited_asset(
        creator,
        get_image_hash(image_title),
        parent_id,
        transformation,
        get_proof(image_title),
        License.FULLY_FREE,
    )


if __name__ == "__main__":
    main()
