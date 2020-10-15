"""
The expr class at par to expr construct in Edh

The interpolation happens just once at time of construction of an expr object,
an expr object responds to `repr()` without quoted, otherwise it is not
different to the vanilla string of the interpolated result.

"""
__all__ = ["expr"]
import asyncio

from typing import *

import re
import inspect


SPLITER = re.compile(r"\{\$(.*?)\$\}", re.S)


class expr:
    """
    Generate source of an expression with possible interpolations of values
    from caller's context
    """

    __slots__ = ("interpolated",)

    def __init__(self, isrc: str):
        caller_frame = inspect.currentframe().f_back
        globals_ = caller_frame.f_globals
        locals_ = caller_frame.f_locals

        segs_out, segs_in = [], SPLITER.split(isrc)
        while True:
            lit_seg, *segs_in = segs_in
            segs_out.append(lit_seg)
            if not segs_in:
                self.interpolated = "".join(segs_out)
                break
            intpl_seg, *segs_in = segs_in
            segs_out.append(repr(eval(intpl_seg, globals_, locals_)))

    def __str__(self):
        return self.interpolated

    # don't get quoted when converting to repr string
    __repr__ = __str__

