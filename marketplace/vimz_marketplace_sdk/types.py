from eth_account import Account
from eth_keys.datatypes import PrivateKey
from eth_typing import Address


class Actor(Account):
    def __init__(self, name, account):
        self.name = name
        self.account = account

    def address(self) -> Address:
        return self.account.address

    def key(self) -> PrivateKey:
        return self.account.key
