import random
from collections import defaultdict
from datetime import datetime
from typing import cast, Generator

import web3
from eth_account.datastructures import SignedMessage
from eth_account.signers.local import LocalAccount
from web3.types import Wei

from vimz_marketplace_sdk.chain import Actor, get_actor
from vimz_marketplace_sdk.creator import Creator


class Device(Actor):
    def __init__(self, name: str, account: LocalAccount):
        super().__init__(name, account)

    def sign(self, creator: Creator, image_hash: int, capture_time: datetime) -> SignedMessage:
        message_hash = web3.Web3.solidity_keccak(
            ["address", "uint256", "uint256"],
            [creator.address(), image_hash, int(capture_time.timestamp())]
        )
        return self.account().unsafe_sign_hash(message_hash)["signature"]


def get_device(name: str) -> Device:
    return Device(name, get_actor(name, Wei(0)).account())


########################################################################################################################

class Brand(Actor):
    def __init__(self, name: str, models: list[str], account: LocalAccount):
        super().__init__(name, account)
        self._models = models
        self._devices = defaultdict(int)

    def get_new_device(self) -> Device:
        model = random.choice(self._models)
        self._devices[model] += 1
        return get_device(f'{self.name()} {model} #{self._devices[model]}')


def get_brand(name: str, models: list[str]) -> Brand:
    return Brand(name, models, get_actor(name).account())


def default_brands() -> Generator[Brand, None, None]:
    galileo = get_brand("Galileo Optics", ["Celestia", "Nova", "Orbit"])
    yield galileo

    newton = get_brand("Newtonic Imaging", ["Gravity", "Momentum", "Inertia"])
    yield newton
