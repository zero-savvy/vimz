from vimz_marketplace_sdk.contracts.contract import VimzContract


class BlurVerifier(VimzContract):
    @classmethod
    def contract_file_name(cls) -> str: return "BlurVerifier"

    @classmethod
    def contract_name(cls) -> str: return "NovaDecider"


class BrightnessVerifier(VimzContract):
    @classmethod
    def contract_file_name(cls) -> str: return "BrightnessVerifier"

    @classmethod
    def contract_name(cls) -> str: return "NovaDecider"


class ContrastVerifier(VimzContract):
    @classmethod
    def contract_file_name(cls) -> str: return "ContrastVerifier"

    @classmethod
    def contract_name(cls) -> str: return "NovaDecider"


class CropVerifier(VimzContract):
    @classmethod
    def contract_file_name(cls) -> str: return "CropVerifier"

    @classmethod
    def contract_name(cls) -> str: return "NovaDecider"


class GrayscaleVerifier(VimzContract):
    @classmethod
    def contract_file_name(cls) -> str: return "GrayscaleVerifier"

    @classmethod
    def contract_name(cls) -> str: return "NovaDecider"


class RedactVerifier(VimzContract):
    @classmethod
    def contract_file_name(cls) -> str: return "RedactVerifier"

    @classmethod
    def contract_name(cls) -> str: return "NovaDecider"


class ResizeVerifier(VimzContract):
    @classmethod
    def contract_file_name(cls) -> str: return "ResizeVerifier"

    @classmethod
    def contract_name(cls) -> str: return "NovaDecider"


class SharpnessVerifier(VimzContract):
    @classmethod
    def contract_file_name(cls) -> str: return "SharpnessVerifier"

    @classmethod
    def contract_name(cls) -> str: return "NovaDecider"
