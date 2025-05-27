from eth_typing import ChecksumAddress

from vimz_marketplace_sdk.chain import Actor
from vimz_marketplace_sdk.contracts.contract import VimzContract
from vimz_marketplace_sdk.logging_config import logger


class LicenseToken(VimzContract):
    @classmethod
    def contract_file_name(cls) -> str:
        return "LicenseToken"

    def set_marketplace(self, admin: Actor, marketplace_address: ChecksumAddress):
        self.call(admin, "setMarketplace", marketplace_address)
        logger.info("Marketplace address set")
