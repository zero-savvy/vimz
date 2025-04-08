from datetime import datetime
from typing import List, cast

from eth_typing import ChecksumAddress

from vimz_marketplace_sdk.chain import Actor
from vimz_marketplace_sdk.contracts.contract import VimzContract
from vimz_marketplace_sdk.contracts.verifiers import BrightnessVerifier, RedactVerifier, ResizeVerifier, \
    SharpnessVerifier, BlurVerifier, ContrastVerifier, CropVerifier, GrayscaleVerifier
from vimz_marketplace_sdk.creator import Creator
from vimz_marketplace_sdk.device import Device
from vimz_marketplace_sdk.logging_config import logger
from vimz_marketplace_sdk.types import License


class AssetGateway(VimzContract):
    @classmethod
    def contract_file_name(cls) -> str:
        return "AssetGateway"

    @classmethod
    def deploy(cls,
               deployer: Actor,
               creator_registry_address: ChecksumAddress,
               device_registry_address: ChecksumAddress
               ) -> "AssetGateway":
        verifiers = cls._deploy_verifiers(deployer)
        vimz_contract = super().deploy(deployer, creator_registry_address, device_registry_address, verifiers)
        return cast(AssetGateway, vimz_contract)

    @classmethod
    def _deploy_verifiers(cls, deployer: Actor) -> List[ChecksumAddress]:
        verifiers = []
        for verifier in [BlurVerifier, BrightnessVerifier,
                         ContrastVerifier, CropVerifier, GrayscaleVerifier,
                         RedactVerifier, ResizeVerifier, SharpnessVerifier]:
            verifier_contract = verifier.deploy(deployer)
            verifiers.append(verifier_contract.address())
        return verifiers

    def register_new_asset(self, creator: Creator, image_hash: int, capture_time: datetime, license: License,
                           device: Device):
        self.call(creator,
                  "registerNewAsset",
                  creator.address(),
                  image_hash,
                  int(capture_time.timestamp()),
                  license.value,
                  device.address(),
                  device.sign(creator, image_hash, capture_time))
        logger.info(f"✅ Asset {image_hash} registered")
