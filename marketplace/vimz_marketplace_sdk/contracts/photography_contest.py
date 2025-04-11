from datetime import datetime
from typing import cast

from eth_typing import ChecksumAddress

from vimz_marketplace_sdk.chain import Actor, _eth
from vimz_marketplace_sdk.contracts.contract import VimzContract
from vimz_marketplace_sdk.logging_config import logger
from vimz_marketplace_sdk.types import Transformation


class PhotographyContest(VimzContract):
    @classmethod
    def contract_file_name(cls) -> str:
        return "PhotographyContest"

    @classmethod
    def deploy(
        cls,
        deployer: Actor,
        submission_deadline: datetime,
        reward: int,
        permissible_transformations: list[Transformation],
        asset_gateway_address: ChecksumAddress,
    ) -> "PhotographyContest":
        vimz_contract = super().deploy(
            deployer,
            int(submission_deadline.timestamp()),
            [t.value for t in permissible_transformations],
            asset_gateway_address,
        )
        # TODO PAY
        return cast(PhotographyContest, vimz_contract)

    def submit(self, creator: Actor, asset_id: int):
        event = self.call_and_get_event(
            creator,
            "submit",
            "SubmissionReceived",
            asset_id,
        )
        logger.info(f"Submission created: {event['submissionIndex']}")

    def announce_winner(self, admin: Actor, submission_id: int):
        event = self.call_and_get_event(admin, "announceWinner", "WinnerAnnounced", submission_id)
        logger.info(
            f"Winner announced: {event['winner']} and paid {_eth(event['reward'])} ETH. Contest completed."
        )
