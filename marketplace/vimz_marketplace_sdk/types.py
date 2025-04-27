from enum import Enum

from vimz_marketplace_sdk.artifacts import ProofData


class EditionPolicy(Enum):
    SEALED = 0
    ONLY_OWNER = 1
    FREE = 2


class LicenseTerms:
    def __init__(self, edition_policy: EditionPolicy, commercial_use: bool, attribution: str = ""):
        self.edition_policy = edition_policy
        self.commercial_use = commercial_use
        self.attribution = attribution

    def encode(self) -> (int, bool, str):
        return self.edition_policy.value, self.commercial_use, self.attribution


def closed_license() -> LicenseTerms:
    return LicenseTerms(EditionPolicy.SEALED, False)


def open_license() -> LicenseTerms:
    return LicenseTerms(EditionPolicy.FREE, True)


class Transformation(Enum):
    BLUR = 0
    BRIGHTNESS = 1
    CONTRAST = 2
    CROP = 3
    GRAYSCALE = 4
    REDACT = 5
    RESIZE = 6
    SHARPNESS = 7


def transformation_parameters(t: Transformation, proof: ProofData) -> list[int]:
    if t in [
        Transformation.GRAYSCALE,
        Transformation.REDACT,
        Transformation.RESIZE,
    ]:
        return []
    elif t in [Transformation.BRIGHTNESS, Transformation.CONTRAST]:
        return [14]
    elif t in [Transformation.BLUR, Transformation.SHARPNESS]:
        return [proof.final_state[2], proof.final_state[3]]

    elif t == Transformation.CROP:
        raise ValueError("Crop transformation not supported yet")
    else:
        raise ValueError(f"Unknown transformation: {t}")
