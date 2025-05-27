from datetime import UTC, datetime

import web3

from scenarios import full_setup
from vimz_marketplace_sdk.artifacts import get_image_hash
from vimz_marketplace_sdk.chain import get_actor
from vimz_marketplace_sdk.contracts.marketplace import Marketplace
from vimz_marketplace_sdk.logging_config import logger
from vimz_marketplace_sdk.types import open_license


def main():
    logger.start_section("Setup environment")
    setup = full_setup(1)

    logger.start_section("Register image")

    creator = setup.creators[0]
    setup.gateway.register_new_image(
        creator,
        get_image_hash("img1"),
        datetime.now(UTC),
        open_license(),
        setup.devices[0],
    )

    logger.start_section("Setup marketplace")

    marketplace_admin = get_actor("marketplace_admin")
    marketplace = Marketplace.deploy(
        marketplace_admin,
        setup.gateway.address(),
    )

    logger.start_section("Setting and buying license")

    marketplace.set_licence_price(creator, get_image_hash("img1"), 1000, 3)
    buyer = get_actor("buyer")
    marketplace.buy_timed_licence(buyer, get_image_hash("img1"), 4, web3.Web3.to_wei(4000, "wei"))


if __name__ == "__main__":
    main()
