from enum import Enum

from eth_account import Account
from eth_keys.datatypes import PrivateKey
from eth_typing import Address


class Actor(Account):
    def __init__(self, name: str, account: Account):
        self._name = name
        self._account = account

    def name(self):
        return self._name

    def account(self) -> Account:
        return self._account

    def address(self) -> Address:
        return self._account.address

    def key(self) -> PrivateKey:
        return self._account.key


class License(Enum):
    CLOSED = 0
    FREE = 1
    FULLY_FREE = 2
    FREE_FOR_EDITIONS = 3
