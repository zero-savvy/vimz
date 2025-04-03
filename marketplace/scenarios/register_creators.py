from datetime import datetime, UTC, timedelta

from vimz_marketplace_sdk.account import get_actor
from vimz_marketplace_sdk.contracts.creator_registry import deploy, register_creator
from vimz_marketplace_sdk.creator import get_creator, default_creators


def main():
    creator_registry_admin = get_actor("creator_registry_admin")

    registry_address = deploy(creator_registry_admin).address

    # Create and register custom creator
    alice = get_creator("Alice", "alice@example.com", datetime.now(UTC) + timedelta(days=1))
    register_creator(registry_address, creator_registry_admin, alice)

    # or use default set
    for creator in default_creators():
        register_creator(registry_address, creator_registry_admin, creator)


if __name__ == "__main__":
    main()
