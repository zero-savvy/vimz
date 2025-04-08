import json
import os


def load_contract_artifact(contract_file_name: str, contract_name: str) -> dict:
    path = os.path.join(_contract_artifacts_dir(), f"{contract_file_name}.sol", f"{contract_name}.json")
    with open(path, "r") as f:
        return json.load(f)


def _contract_artifacts_dir():
    return os.path.join(os.path.dirname(__file__), "../out/")


def get_image_hash(img: str) -> int:
    path = os.path.join(_image_dir(), f"{img}.hash")
    with open(path, "r") as f:
        return int(f.read().strip())


def _image_dir():
    return os.path.join(os.path.dirname(__file__), "../image-data/")
