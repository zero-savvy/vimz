from vimz_marketplace_sdk.chain import Actor
from vimz_marketplace_sdk.contracts.contract import VimzContract
from vimz_marketplace_sdk.creator import Creator
from vimz_marketplace_sdk.logging_config import logger


class CreatorRegistry(VimzContract):
    @classmethod
    def contract_file_name(cls) -> str:
        return "CreatorRegistry"

    def register_creator(self, admin: Actor, creator: Creator):
        receipt = self.call(
            admin,
            "registerCreator",
            creator.address(),
            creator.kyc_expiration(),
            creator.email(),
        )
        logger.info(
            f"✅ Creator '{creator.name()}' registered in CreatorRegistry ({receipt['gasUsed']:_} gas)."
        )
