from eth_account import Account
from eth_keys.datatypes import PrivateKey
from eth_typing import Address


class Actor(Account):
    def __init__(self, name, account):
        self._name = name
        self._account = account

    def name(self):
        return self._name

    def account(self):
        return self._account

    def address(self) -> Address:
        return self._account.address

    def key(self) -> PrivateKey:
        return self._account.key
