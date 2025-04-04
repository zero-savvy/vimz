from datetime import datetime

import web3
from eth_account import Account
from eth_account.datastructures import SignedMessage
from web3.types import Wei

from vimz_marketplace_sdk.account import get_actor
from vimz_marketplace_sdk.creator import Creator
from vimz_marketplace_sdk.types import Actor


class Device(Actor):
    def __init__(self, name: str, account: Account):
        super().__init__(name, account)

    def sign(self, creator: Creator, image_hash: int, capture_time: datetime) -> SignedMessage:
        message_hash = web3.Web3.solidity_keccak(
            ["address", "uint256", "uint256"],
            [creator.address(), image_hash, int(capture_time.timestamp())]
        )
        return self.account().unsafe_sign_hash(message_hash)["signature"]


def get_device(name: str) -> Device:
    return Device(name, get_actor(name, Wei(0)).account())
