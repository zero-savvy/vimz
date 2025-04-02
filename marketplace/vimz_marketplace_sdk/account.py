import os

from web3 import Account, Web3
from web3.types import Wei

from vimz_marketplace_sdk.chain import send_eth
from vimz_marketplace_sdk.types import Actor

CORNUCOPIA_NAME = "cornucopia"

# Standard endowment: 1 Ether (in wei)
STANDARD_ENDOWMENT = Web3.to_wei(1, 'ether')

# Global dictionary to store actor accounts.
ACTORS = {}


def get_cornucopia() -> Actor:
    return get_actor(CORNUCOPIA_NAME)


def get_actor(name: str, endowment: Wei = STANDARD_ENDOWMENT) -> Actor:
    name = name.lower()  # be case-insensitive

    actor = ACTORS.get(name)
    if actor:
        return actor

    if name == CORNUCOPIA_NAME:  # initialize cornucopia account
        cornucopia_key = os.environ["CORNUCOPIA_KEY"]
        new_actor = Actor(name, Account.from_key(cornucopia_key))
    else:
        new_actor = Actor(name, Account.create())
        print(f"Endowing new actor '{name}' with {endowment} wei...")
        send_eth(get_cornucopia(), new_actor, endowment)

    ACTORS[name] = new_actor
    return new_actor
