import json
import os


def get_contract_artifact(contract_file_name: str, contract_name: str) -> dict:
    path = os.path.join(
        _contract_artifacts_dir(), f"{contract_file_name}.sol", f"{contract_name}.json"
    )
    with open(path, "r") as f:
        return json.load(f)


def get_image_hash(img: str) -> int:
    path = os.path.join(_image_dir(), f"{img}.hash")
    with open(path, "r") as f:
        return int(f.read().strip())


class ProofData:
    def __init__(self, bytes):
        bytes = bytes[4:]  # remove the first 4 bytes - selector
        assert len(bytes) % 32 == 0, "Invalid proof file"

        # first U256 is the number of steps
        self.steps = int.from_bytes(bytes[0:32])

        # last 32 bytes are the proof itself
        proof_len = 32 * 25
        self.proof = [
            int.from_bytes(bytes[s : s + 32]) for s in range(len(bytes) - proof_len, len(bytes), 32)
        ]

        # the rest is the state encoding (initial and final state)
        state_encoding_len = (len(bytes) - proof_len - 32) // 2
        self.state_len = state_encoding_len // 32
        self.initial_state = [
            int.from_bytes(bytes[s : s + 32]) for s in range(32, 32 + state_encoding_len, 32)
        ]
        self.final_state = [
            int.from_bytes(bytes[s : s + 32])
            for s in range(32 + state_encoding_len, 32 + 2 * state_encoding_len, 32)
        ]


def get_proof(edited_img: str) -> ProofData:
    path = os.path.join(_proof_dir(), f"{edited_img}.proof")
    with open(path, "rb") as f:
        return ProofData(f.read())


def _contract_artifacts_dir():
    return os.path.join(os.path.dirname(__file__), "../out/")


def _image_dir():
    return os.path.join(os.path.dirname(__file__), "../image-data/")


def _proof_dir():
    return os.path.join(os.path.dirname(__file__), "../proofs/")
