from vimz_marketplace_sdk.chain import Actor
from vimz_marketplace_sdk.contracts.contract import VimzContract
from vimz_marketplace_sdk.creator import Creator


class CreatorRegistry(VimzContract):
    @classmethod
    def contract_name(cls) -> str:
        return "CreatorRegistry"

    def register_creator(self, admin: Actor, creator: Creator):
        self.call(admin, "registerCreator", creator.address(), creator.kyc_expiration(), creator.email())
        print(f"✅ Creator '{creator.name()}' registered in CreatorRegistry.")
