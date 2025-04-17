from datetime import datetime
from typing import List, cast

from eth_typing import ChecksumAddress

from vimz_marketplace_sdk.artifacts import ProofData
from vimz_marketplace_sdk.chain import Actor
from vimz_marketplace_sdk.contracts.contract import VimzContract
from vimz_marketplace_sdk.contracts.verifiers import (
    BlurVerifier,
    BrightnessVerifier,
    ContrastVerifier,
    CropVerifier,
    GrayscaleVerifier,
    RedactVerifier,
    ResizeVerifier,
    SharpnessVerifier,
)
from vimz_marketplace_sdk.creator import Creator
from vimz_marketplace_sdk.device import Device
from vimz_marketplace_sdk.logging_config import logger
from vimz_marketplace_sdk.types import License, Transformation, transformation_parameters


class AssetGateway(VimzContract):
    @classmethod
    def contract_file_name(cls) -> str:
        return "AssetGateway"

    @classmethod
    def deploy(
        cls,
        deployer: Actor,
        creator_registry_address: ChecksumAddress,
        device_registry_address: ChecksumAddress,
    ) -> "AssetGateway":
        verifiers = cls._deploy_verifiers(deployer)
        vimz_contract = super().deploy(
            deployer, creator_registry_address, device_registry_address, verifiers
        )
        return cast(AssetGateway, vimz_contract)

    @classmethod
    def _deploy_verifiers(cls, deployer: Actor) -> List[ChecksumAddress]:
        verifiers = []
        for verifier in [
            BlurVerifier,
            BrightnessVerifier,
            ContrastVerifier,
            CropVerifier,
            GrayscaleVerifier,
            RedactVerifier,
            ResizeVerifier,
            SharpnessVerifier,
        ]:
            verifier_contract = verifier.deploy(deployer)
            verifiers.append(verifier_contract.address())
        return verifiers

    def register_new_asset(
        self,
        creator: Creator,
        image_hash: int,
        capture_time: datetime,
        license: License,
        device: Device,
    ) -> int:
        event = self.call_and_get_event(
            creator,
            "registerNewAsset",
            "NewAssetRegistered",
            image_hash,
            int(capture_time.timestamp()),
            license.value,
            device.address(),
            device.sign(creator, image_hash, capture_time),
        )
        return self._handle_creation_event(image_hash, event)

    def register_edited_asset(
        self,
        creator: Creator,
        image_hash: int,
        source_id: int,
        transformation: Transformation,
        proof: ProofData,
        license: License,
    ):
        event = self.call_and_get_event(
            creator,
            "registerEditedAsset",
            "EditedAssetRegistered",
            image_hash,
            source_id,
            transformation.value,
            transformation_parameters(transformation),
            proof.proof,
            license.value,
        )
        return self._handle_creation_event(image_hash, event)

    @staticmethod
    def _handle_creation_event(image_hash: int, event: dict) -> int:
        asset_id = event["assetId"]
        logger.info(f"✅ Asset {image_hash} registered with ID {asset_id}")
        return asset_id
