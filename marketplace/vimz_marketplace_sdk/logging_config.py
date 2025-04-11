import logging
import os
import sys


class ColorFormatter(logging.Formatter):
    COLORS = {
        "DEBUG": "\033[0;36m",  # Cyan
        "INFO": "\033[0;32m",  # Green
        "WARNING": "\033[0;33m",  # Yellow
        "ERROR": "\033[0;31m",  # Red
        "CRITICAL": "\033[1;31m",  # Bold Red
    }
    RESET = "\033[0m"

    def format(self, record):
        color = self.COLORS.get(record.levelname, self.RESET)
        record.levelname = f"{color}{record.levelname}{self.RESET}"
        return super().format(record)


logger = logging.getLogger(os.environ.get("SCENARIO_NAME", __name__))
logger.setLevel(logging.DEBUG)
ch = logging.StreamHandler(sys.stdout)
formatter = ColorFormatter("[%(name)s] %(levelname)s: %(message)s")
ch.setFormatter(formatter)
logger.addHandler(ch)

logger.start_section = lambda name: logger.info(
    f"\n\n==================== {name} ======================\n"
)
