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
from vimz_marketplace_sdk.types import Transformation, transformation_parameters, LicenseTerms


class ImageGateway(VimzContract):
    @classmethod
    def contract_file_name(cls) -> str:
        return "ImageGateway"

    @classmethod
    def deploy(
        cls,
        deployer: Actor,
        creator_registry_address: ChecksumAddress,
        device_registry_address: ChecksumAddress,
    ) -> "ImageGateway":
        verifiers = cls._deploy_verifiers(deployer)
        vimz_contract = super().deploy(
            deployer, creator_registry_address, device_registry_address, verifiers
        )
        return cast(ImageGateway, vimz_contract)

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

    def register_new_image(
        self,
        creator: Creator,
        image_hash: int,
        capture_time: datetime,
        license_terms: LicenseTerms,
        device: Device,
        public_good: bool = False,
    ):
        self.call(
            creator,
            "registerNewImage",
            image_hash,
            int(capture_time.timestamp()),
            license_terms.encode(),
            device.address(),
            device.sign(creator, image_hash, capture_time),
            public_good,
        )
        logger.info(f"✅ Image {image_hash} registered successfully.")

    def register_edited_image(
        self,
        creator: Creator,
        image_hash: int,
        source_id: int,
        transformation: Transformation,
        proof: ProofData,
    ):
        self.call(
            creator,
            "registerEditedImage",
            image_hash,
            source_id,
            transformation.value,
            transformation_parameters(transformation, proof),
            proof.proof,
        )
        logger.info(f"✅ Image {image_hash} registered successfully.")
