from enum import Enum


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
