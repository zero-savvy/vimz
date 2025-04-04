import random
from datetime import datetime, UTC, timedelta
from typing import Generator

from eth_account.signers.local import LocalAccount

from vimz_marketplace_sdk.chain import Actor, get_actor


class Creator(Actor):
    def __init__(self, name: str, email: str, kyc_expiration: datetime, account: LocalAccount):
        super().__init__(name, account)
        self._email = email
        self._kyc_expiration = kyc_expiration

    def email(self) -> str:
        return self._email

    def kyc_expiration(self) -> int:
        return int(self._kyc_expiration.timestamp())


def get_creator(name: str, mail: str, kyc_expiry: datetime) -> Creator:
    actor = get_actor(name)
    return Creator(name, mail, kyc_expiry, actor.account())


def default_creators() -> Generator[Creator, None, None]:
    data = [
        ("Ada Lovelace", "ada.lovelace@analyticalengine.fun",),
        ("Alan Turing", "alan.turing@bombe.io"),
        ("Grace Hopper", "grace.hopper@debugging.de"),
        ("John von Neumann", "john.vonneumann@gameoflife.party"),
        ("Claude Shannon", "claude.shannon@bitwise.buzz"),
        ("George Boole", "george.boole@boolean.boo"),
        ("Blaise Pascal", "blaise.pascal@pascal.pie"),
        ("Leonardo Fibonacci", "leonardo.fibonacci@fibonacci.farm"),
        ("Carl Friedrich Gauss", "carl.friedrich.gauss@gauss.guru"),
        ("René Descartes", "rene.descartes@cogito.cool")
    ]

    now = datetime.now(UTC)

    for (name, mail) in data:
        yield get_creator(name, mail, now + timedelta(days=random.randint(2, 10)))
