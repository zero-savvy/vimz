from datetime import UTC, datetime

from web3.exceptions import ContractLogicError

from scenarios import full_setup
from vimz_marketplace_sdk.artifacts import get_image_hash, get_proof
from vimz_marketplace_sdk.contracts.image_gateway import ImageGateway
from vimz_marketplace_sdk.creator import Creator
from vimz_marketplace_sdk.device import Device
from vimz_marketplace_sdk.logging_config import logger
from vimz_marketplace_sdk.types import Transformation, closed_license


def main():
    logger.start_section("Prepare environment")
    setup = full_setup()
    gateway, creator, device = setup.gateway, setup.creators[0], setup.devices[0]

    ################################################################################################

    logger.start_section("Register original images")
    register_originals(gateway, creator, device)

    ################################################################################################

    logger.start_section("Register editions of `img1`")
    register_edition(
        gateway, creator, get_image_hash("img1"), "img1-grayscale", Transformation.GRAYSCALE
    )
    register_edition(
        gateway, creator, get_image_hash("img1"), "img1-sharpness", Transformation.SHARPNESS
    )
    register_edition(
        gateway,
        creator,
        get_image_hash("img1-sharpness"),
        "img1-sharpness-grayscale",
        Transformation.GRAYSCALE,
    )

    ################################################################################################

    logger.start_section("Register editions of `img2`")
    register_edition(
        gateway, creator, get_image_hash("img2"), "img2-contrast", Transformation.CONTRAST
    )
    register_edition(
        gateway,
        creator,
        get_image_hash("img2-contrast"),
        "img2-contrast-sharpness",
        Transformation.SHARPNESS,
    )

    ################################################################################################

    logger.start_section("Try to register the same original image twice")
    try:
        gateway.register_new_image(
            creator, get_image_hash("img1"), datetime.now(UTC), closed_license(), device
        )
        raise Exception("Registration should have failed")
    except ContractLogicError as err:
        assert "revert: Image already registered" in err.message
        logger.info("Cannot register the same original image twice: ✅")

    try:
        register_edition(
            gateway,
            creator,
            get_image_hash("img1"),
            "img1-grayscale",
            Transformation.GRAYSCALE,
        )
        raise Exception("Registration should have failed")
    except ContractLogicError as err:
        assert "revert: Image already registered" in err.message
        logger.info("Cannot register the same edited image twice: ✅")


def register_originals(gateway: ImageGateway, creator: Creator, device: Device):
    logger.start_section("Register original images")
    for title in ["img1", "img2"]:
        gateway.register_new_image(
            creator, get_image_hash(title), datetime.now(UTC), closed_license(), device
        )


def register_edition(
    gateway: ImageGateway,
    creator: Creator,
    parent_id: int,
    image_title: str,
    transformation: Transformation,
):
    gateway.register_edited_image(
        creator,
        get_image_hash(image_title),
        parent_id,
        transformation,
        get_proof(image_title),
    )


if __name__ == "__main__":
    main()
