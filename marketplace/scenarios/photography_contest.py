from datetime import UTC, datetime

import web3

from scenarios import prepare_creator_registry, prepare_device_registry
from vimz_marketplace_sdk.artifacts import get_image_hash, get_proof
from vimz_marketplace_sdk.chain import get_actor
from vimz_marketplace_sdk.contracts.asset_gateway import AssetGateway
from vimz_marketplace_sdk.contracts.photography_contest import PhotographyContest
from vimz_marketplace_sdk.logging_config import logger
from vimz_marketplace_sdk.types import License, Transformation


def main():
    logger.start_section("Prepare devices and creators")
    device_registry, device = prepare_device_registry()
    creator_registry, creator = prepare_creator_registry()

    logger.start_section("Prepare asset gateway and register assets")
    gateway = AssetGateway.deploy(
        get_actor("gateway_deployer"),
        creator_registry.address(),
        device_registry.address(),
    )

    original_asset_id = gateway.register_new_asset(
        creator, get_image_hash("img1"), datetime.now(UTC), License.FULLY_FREE, device
    )

    edited_asset_id = gateway.register_edited_asset(
        creator,
        get_image_hash("img1-grayscale"),
        original_asset_id,
        Transformation.GRAYSCALE,
        get_proof("img1-grayscale"),
        License.FULLY_FREE,
    )

    logger.start_section("Photography Contest")

    contest_admin = get_actor("contest_admin")
    contest = PhotographyContest.deploy(
        contest_admin,
        web3.Web3.to_wei(0.1, "ether"),
        [Transformation.GRAYSCALE],
        gateway.address(),
    )

    contest.submit(creator, edited_asset_id)
    contest.close_submissions(contest_admin)
    contest.announce_winner(contest_admin, 0)


if __name__ == "__main__":
    main()
