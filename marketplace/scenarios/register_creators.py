from datetime import datetime, UTC, timedelta

from vimz_marketplace_sdk.chain import get_actor
from vimz_marketplace_sdk.contracts.creator_registry import CreatorRegistry
from vimz_marketplace_sdk.creator import get_creator, default_creators


def main():
    creator_registry_admin = get_actor("creator_registry_admin")
    registry = CreatorRegistry.deploy(creator_registry_admin)

    # Create and register custom creator
    alice = get_creator("Alice", "alice@example.com", datetime.now(UTC) + timedelta(days=1))
    registry.register_creator(creator_registry_admin, alice)

    # or use default set
    for creator in default_creators():
        registry.register_creator(creator_registry_admin, creator)


if __name__ == "__main__":
    main()
