from enum import Enum

from vimz_marketplace_sdk.artifacts import ProofData


class License(Enum):
    CLOSED = 0
    FREE = 1
    FULLY_FREE = 2
    FREE_FOR_EDITIONS = 3


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
