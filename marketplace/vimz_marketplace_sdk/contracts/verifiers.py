from vimz_marketplace_sdk.artifacts import ProofData
from vimz_marketplace_sdk.chain import Actor
from vimz_marketplace_sdk.contracts.contract import VimzContract
from vimz_marketplace_sdk.logging_config import logger


class VerifierContract(VimzContract):
    def verify(self, caller: Actor, proof: ProofData):
        receipt = self.call(
            caller,
            "verifyOpaqueNovaProofWithInputs",
            proof.steps,
            proof.initial_state,
            proof.final_state,
            proof.proof,
        )
        logger.info(f"✅ Proof verified successfully ({receipt['gasUsed']:_} gas)")


class BlurVerifier(VerifierContract):
    @classmethod
    def contract_file_name(cls) -> str:
        return "BlurVerifier"

    @classmethod
    def contract_name(cls) -> str:
        return "NovaDecider"


class BrightnessVerifier(VerifierContract):
    @classmethod
    def contract_file_name(cls) -> str:
        return "BrightnessVerifier"

    @classmethod
    def contract_name(cls) -> str:
        return "NovaDecider"


class ContrastVerifier(VerifierContract):
    @classmethod
    def contract_file_name(cls) -> str:
        return "ContrastVerifier"

    @classmethod
    def contract_name(cls) -> str:
        return "NovaDecider"


class CropVerifier(VerifierContract):
    @classmethod
    def contract_file_name(cls) -> str:
        return "CropVerifier"

    @classmethod
    def contract_name(cls) -> str:
        return "NovaDecider"


class GrayscaleVerifier(VerifierContract):
    @classmethod
    def contract_file_name(cls) -> str:
        return "GrayscaleVerifier"

    @classmethod
    def contract_name(cls) -> str:
        return "NovaDecider"


class RedactVerifier(VerifierContract):
    @classmethod
    def contract_file_name(cls) -> str:
        return "RedactVerifier"

    @classmethod
    def contract_name(cls) -> str:
        return "NovaDecider"


class ResizeVerifier(VerifierContract):
    @classmethod
    def contract_file_name(cls) -> str:
        return "ResizeVerifier"

    @classmethod
    def contract_name(cls) -> str:
        return "NovaDecider"


class SharpnessVerifier(VerifierContract):
    @classmethod
    def contract_file_name(cls) -> str:
        return "SharpnessVerifier"

    @classmethod
    def contract_name(cls) -> str:
        return "NovaDecider"
