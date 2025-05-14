from vimz_marketplace_sdk.artifacts import get_proof
from vimz_marketplace_sdk.chain import get_actor
from vimz_marketplace_sdk.contracts.verifiers import (
    BlurVerifier,
    ContrastVerifier,
    GrayscaleVerifier,
    SharpnessVerifier,
)
from vimz_marketplace_sdk.logging_config import logger


def main():
    logger.start_section("Deploy verifier contracts")

    admin = get_actor("admin")

    blur = BlurVerifier.deploy(admin)
    contrast = ContrastVerifier.deploy(admin)
    grayscale = GrayscaleVerifier.deploy(admin)
    sharpness = SharpnessVerifier.deploy(admin)

    logger.start_section("Verify proofs")

    for proof, contract in (
        ("img1-blur", blur),
        ("img2-contrast", contrast),
        ("img1-grayscale", grayscale),
        ("img1-sharpness", sharpness),
    ):
        contract.verify(admin, get_proof(proof))


if __name__ == "__main__":
    main()
