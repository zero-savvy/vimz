from datetime import UTC, datetime, timedelta

from vimz_marketplace_sdk.chain import get_actor
from vimz_marketplace_sdk.contracts.creator_registry import CreatorRegistry
from vimz_marketplace_sdk.creator import default_creators, get_creator
from vimz_marketplace_sdk.logging_config import logger


def main():
    logger.start_section("Create creator registry")
    creator_registry_admin = get_actor("creator_registry_admin")
    registry = CreatorRegistry.deploy(creator_registry_admin)

    logger.start_section("Create and register custom creator")
    alice = get_creator("Alice", "alice@example.com", datetime.now(UTC) + timedelta(days=1))
    registry.register_creator(creator_registry_admin, alice)

    logger.start_section("Register default creators")
    for creator in default_creators():
        registry.register_creator(creator_registry_admin, creator)


if __name__ == "__main__":
    main()
