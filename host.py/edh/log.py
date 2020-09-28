"""
Environment variable controlled logger tree from root package.

"""
__all__ = ()

import logging
import os
import sys


ROOT_NAME = __package__.split(".", 1)[0]

root_logger = None


def get_logger(name: str):
    global root_logger

    if root_logger is None:
        ctrl_env_prefix = ROOT_NAME.upper()
        LOG_LEVEL_ENV_VAR = f"{ctrl_env_prefix}_LOG_LEVEL"

        root_logger = logging.getLogger(ROOT_NAME)
        handler = logging.StreamHandler(sys.stderr)
        handler.setFormatter(
            logging.Formatter(
                "[%(asctime)s %(process)d](%(name)s) %(message)s\n"
                ' -%(levelname)s- File "%(pathname)s", line %(lineno)d, in %(funcName)s',
                "%FT%T",
            )
        )
        root_logger.handlers.append(handler)
        log_level = logging.INFO
        log_level_name = os.environ.get(LOG_LEVEL_ENV_VAR, "INFO")
        try:
            log_level = getattr(logging, log_level_name.upper())
        except AttributeError:
            root_logger.error(f"Failed setting log level to [{log_level_name}]")
        root_logger.setLevel(log_level)

    if name is None or name == "":
        name = ROOT_NAME
    elif not name.startswith(f"{ROOT_NAME}.") and name != ROOT_NAME:
        raise ValueError(f"Can NOT get logger [{name}] from root [{ROOT_NAME}]!")

    return logging.getLogger(name)


root_logger = get_logger(None)
