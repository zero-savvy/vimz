from typing import cast

from eth_typing import ChecksumAddress
from web3.types import Wei

from vimz_marketplace_sdk.chain import Actor
from vimz_marketplace_sdk.contracts.contract import VimzContract
from vimz_marketplace_sdk.logging_config import logger


class Marketplace(VimzContract):
    @classmethod
    def contract_file_name(cls) -> str:
        return "Marketplace"

    @classmethod
    def deploy(
        cls,
        deployer: Actor,
        image_gateway_address: ChecksumAddress,
        license_token_address: ChecksumAddress,
    ) -> "Marketplace":
        vimz_contract = super().deploy(
            deployer,
            image_gateway_address,
            license_token_address,
            "0x0000000000000000000000000000000000000000",  # collection - TODO
        )
        return cast(Marketplace, vimz_contract)

    def set_licence_price(self, owner: Actor, image_hash: int, per_block: int, min_duration: int):
        receipt = self.call(owner, "setLicencePrice", image_hash, per_block, min_duration)
        logger.info(f"License price set ({receipt['gasUsed']:_} gas).")

    def buy_timed_licence(self, buyer: Actor, image_hash: int, blocks_duration: int, payment: Wei):
        receipt = self.call(buyer, "buyTimedLicence", image_hash, blocks_duration, value=payment)
        logger.info(f"License bought ({receipt['gasUsed']:_} gas).")
