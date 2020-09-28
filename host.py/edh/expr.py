"""
An expr() function at par to expr construct in Edh

Unlike in Edh, expr values in Python stay of string type

"""
__all__ = ["expr"]
import asyncio

from typing import *

import re
import inspect


SPLITER = re.compile(r"\{\$(.*?)\$\}", re.S)


def expr(isrc: str) -> str:
    """
    Generate source with possible interpolations from caller's context

    """
    caller_frame = inspect.currentframe().f_back
    globals_ = caller_frame.f_globals
    locals_ = caller_frame.f_locals

    segs_out, segs_in = [], SPLITER.split(isrc)
    while True:
        lit_seg, *segs_in = segs_in
        segs_out.append(lit_seg)
        if not segs_in:
            return "".join(segs_out)
        intpl_seg, *segs_in = segs_in
        segs_out.append(repr(eval(intpl_seg, globals_, locals_)))
