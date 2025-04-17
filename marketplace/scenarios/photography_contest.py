from datetime import UTC, datetime

import web3
from web3.exceptions import ContractLogicError

from scenarios import Setup, full_setup
from vimz_marketplace_sdk.artifacts import get_image_hash, get_proof
from vimz_marketplace_sdk.chain import get_actor
from vimz_marketplace_sdk.contracts.photography_contest import PhotographyContest
from vimz_marketplace_sdk.creator import Creator
from vimz_marketplace_sdk.logging_config import logger
from vimz_marketplace_sdk.types import License, Transformation


def main():
    logger.start_section("Setup environment")
    setup = full_setup(2)

    logger.start_section("Setup contest")
    contest_admin = get_actor("contest_admin")
    contest = PhotographyContest.deploy(
        contest_admin,
        web3.Web3.to_wei(0.1, "ether"),
        [Transformation.GRAYSCALE],
        setup.gateway.address(),
    )

    participant_1(contest, setup)
    participant_2(contest, setup)

    logger.start_section("Announce winner")
    contest.close_submissions(contest_admin)
    contest.announce_winner(contest_admin, get_image_hash("img1-grayscale"))


def participant_1(contest: PhotographyContest, setup: Setup):
    participant = setup.creators[0]
    device = setup.devices[0]

    logger.start_section(f"Participant {participant.name()}: registering images in Gateway")
    setup.gateway.register_new_image(
        participant, get_image_hash("img1"), datetime.now(UTC), License.CLOSED, device
    )
    setup.gateway.register_edited_image(
        participant,
        get_image_hash("img1-sharpness"),
        get_image_hash("img1"),
        Transformation.SHARPNESS,
        get_proof("img1-sharpness"),
        License.CLOSED,
    )
    setup.gateway.register_edited_image(
        participant,
        get_image_hash("img1-grayscale"),
        get_image_hash("img1"),
        Transformation.GRAYSCALE,
        get_proof("img1-grayscale"),
        License.CLOSED,
    )
    setup.gateway.register_edited_image(
        participant,
        get_image_hash("img1-sharpness-grayscale"),
        get_image_hash("img1-sharpness"),
        Transformation.GRAYSCALE,
        get_proof("img1-sharpness-grayscale"),
        License.CLOSED,
    )

    logger.start_section(f"Participant {participant.name()}: submitting images to contest")
    # Unmodified image is allowed
    contest.submit(participant, get_image_hash("img1"))
    # Cannot submit the same image twice
    repeat_submission(participant, contest, get_image_hash("img1"))
    # Sharpness is not allowed
    invalid_submission(participant, contest, get_image_hash("img1-sharpness"))
    # Grayscale is allowed
    contest.submit(participant, get_image_hash("img1-grayscale"))
    # Sharpness is not allowed, even if grayscale is lay
    invalid_submission(participant, contest, get_image_hash("img1-sharpness-grayscale"))


def participant_2(contest: PhotographyContest, setup: Setup):
    participant = setup.creators[1]
    device = setup.devices[1]

    logger.start_section(f"Participant {participant.name()}: registering images in Gateway")
    setup.gateway.register_new_image(
        participant, get_image_hash("img2"), datetime.now(UTC), License.CLOSED, device
    )
    setup.gateway.register_edited_image(
        participant,
        get_image_hash("img2-contrast"),
        get_image_hash("img2"),
        Transformation.CONTRAST,
        get_proof("img2-contrast"),
        License.CLOSED,
    )
    setup.gateway.register_edited_image(
        participant,
        get_image_hash("img1-blur"),
        get_image_hash("img1"),
        Transformation.BLUR,
        get_proof("img1-blur"),
        License.CLOSED,
    )

    logger.start_section(f"Participant {participant.name()}: submitting images to contest")
    # Unmodified image is allowed
    contest.submit(participant, get_image_hash("img2"))
    # Contrast is not allowed
    invalid_submission(participant, contest, get_image_hash("img2-contrast"))
    # Cannot submit other's work
    someone_elses_submission(participant, contest, get_image_hash("img1-blur"))


def repeat_submission(participant: Creator, contest: PhotographyContest, image_hash: int):
    _fail_submission(participant, contest, image_hash, "Image already submitted")


def invalid_submission(participant: Creator, contest: PhotographyContest, image_hash: int):
    _fail_submission(participant, contest, image_hash, "Image violates contest rules")


def someone_elses_submission(participant: Creator, contest: PhotographyContest, image_hash: int):
    _fail_submission(
        participant, contest, image_hash, "Participant is not the only creator of the image"
    )


def _fail_submission(
    participant: Creator,
    contest: PhotographyContest,
    image_hash: int,
    message: str,
):
    try:
        contest.submit(participant, image_hash)
        raise Exception("Submission should have failed")
    except ContractLogicError as err:
        assert message in err.message


if __name__ == "__main__":
    main()
