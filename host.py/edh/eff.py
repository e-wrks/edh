__all__ = [
    "effect",
    "effect_import",
]

from typing import *
import inspect

from . import log

logger = log.get_logger(__name__)


NOT_SPECIFIED = object()

EFFSKEY = "__effects__"


def effect(
    key2get_or_dict2put: Optional[Union[dict, object]] = NOT_SPECIFIED,
    def_val: Optional[object] = NOT_SPECIFIED,
    **kws2put,
):
    if key2get_or_dict2put is NOT_SPECIFIED:
        key2get = None
        dict2put = None
    elif isinstance(key2get_or_dict2put, dict):
        key2get = None
        dict2put = key2get_or_dict2put
    else:
        key2get = key2get_or_dict2put
        dict2put = None

    # get direct caller's frame thus local scope
    frame = inspect.currentframe().f_back
    scope = frame.f_locals
    if kws2put or dict2put:
        effs = scope.get(EFFSKEY, None)
        if effs is None:
            effs = {}
            scope[EFFSKEY] = effs
        if dict2put:
            effs.update(dict2put)
        if kws2put:
            effs.update(kws2put)

    if key2get is None:
        return None  # not meant to extract an effectful artifact

    # meant to extract an effectful artifact by key `key2get`

    # need CPython 3.8 or later to have frames of async coroutines in the stack
    # searched this way
    while True:
        effs = scope.get(EFFSKEY, None)
        if effs is not None:
            art = effs.get(key2get, effs)
            if art is not effs:
                return art
        frame = frame.f_back
        if frame is None:
            if def_val is NOT_SPECIFIED:
                raise ValueError(f"No such effect: {key2get!r}")
            return def_val
        scope = frame.f_locals


def effect_import(modu: Union["module", Dict[str, object]]):
    try:
        modu = vars(modu)
    except TypeError:
        pass

    # get direct caller's frame thus local scope
    frame = inspect.currentframe().f_back
    scope = frame.f_locals
    effs = scope.get(EFFSKEY, None)
    if effs is None:
        effs = {}
        scope[EFFSKEY] = effs

    exported_names = modu.get("__all__", None)
    if exported_names is not None:
        for art_name in exported_names:
            effs[art_name] = modu[art_name]

    symbolic_arts = modu.get("__all_symbolic__", None)
    if symbolic_arts is not None:
        effs.update(symbolic_arts)
