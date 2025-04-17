from typing import cast

from eth_typing import ChecksumAddress
from web3.types import Wei

from vimz_marketplace_sdk.chain import Actor, _eth, get_actor_by_address
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
        reward: Wei,
        permissible_transformations: list[Transformation],
        asset_gateway_address: ChecksumAddress,
    ) -> "PhotographyContest":
        vimz_contract = super().deploy(
            deployer,
            [t.value for t in permissible_transformations],
            asset_gateway_address,
            value=reward,
        )
        return cast(PhotographyContest, vimz_contract)

    def submit(self, creator: Actor, asset_id: int):
        event = self.call_and_get_event(
            creator,
            "submit",
            "SubmissionReceived",
            asset_id,
        )
        logger.info(f"Submission created with id {event['submissionIndex']}")

    def close_submissions(self, admin: Actor):
        self.call(admin, "closeSubmissions")
        logger.info("Submissions closed")

    def announce_winner(self, admin: Actor, submission_id: int):
        event = self.call_and_get_event(admin, "announceWinner", "WinnerAnnounced", submission_id)
        winner = get_actor_by_address(event["winner"])
        logger.info(
            f"Winner announced: {winner.name()} and paid {_eth(event['reward'])} ETH. Contest completed."
        )
