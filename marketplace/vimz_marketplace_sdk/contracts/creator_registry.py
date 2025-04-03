from eth_typing import ChecksumAddress, Address
from web3.contract import Contract

from vimz_marketplace_sdk.artifacts import load_artifact
from vimz_marketplace_sdk.chain import deploy_contract, get_web3
from vimz_marketplace_sdk.contracts.contract import VimzContract
from vimz_marketplace_sdk.creator import Creator
from vimz_marketplace_sdk.types import Actor


class CreatorRegistry(VimzContract):
    @classmethod
    def contract_name(cls) -> str:
        return "CreatorRegistry"

    def register_creator(self, admin: Actor, creator: Creator):
        self.call(admin, "registerCreator", creator.address(), creator.kyc_expiration(), creator.email())
        print(f"✅ Creator '{creator.name()}' registered in CreatorRegistry.")
