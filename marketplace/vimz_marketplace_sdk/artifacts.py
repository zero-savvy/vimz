import json
import os


def load_artifact(contract_file_name: str, contract_name: str) -> dict:
    path = os.path.join(_artifacts_dir(), f"{contract_file_name}.sol", f"{contract_name}.json")
    with open(path, "r") as f:
        artifact = json.load(f)
    return artifact


def _artifacts_dir():
    return os.path.join(os.path.dirname(__file__), "../out/")
