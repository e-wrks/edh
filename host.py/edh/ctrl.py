__all__ = ["EndOfStream", "nil", "EdhPeerError", "read_stream"]
import asyncio
from typing import *

from .log import *

from .adt import *

logger = get_logger(__name__)


class _EndOfStream:
    __slots__ = ()

    @staticmethod
    def __repr__():
        return "EndOfStream"


# Edh uses nil to mark end-of-stream, it's improper in Python to use
# None for that purpose, so here we use an explicit singleton object
EndOfStream = _EndOfStream()

# nil in Edh means this, eval nil to EndOfStream in Python for interop
nil = EndOfStream


class EdhPeerError(RuntimeError):
    __slots__ = ("peer_site", "details")

    def __init__(self, peer_site: str, details: str):
        self.peer_site = peer_site
        self.details = details

    def __repr__(self):
        return f"EdhPeerError({self.peer_site!r}, {self.details!r})"

    def __str__(self):
        return f"🏗️ {self.peer_site!s}\n{self.details!s}"


async def read_stream(eos: asyncio.Future, rdr: Coroutine) -> Union[_EndOfStream, Any]:
    try:
        done, _pending = await asyncio.wait(
            {eos, asyncio.create_task(rdr)}, return_when=asyncio.FIRST_COMPLETED
        )
        if len(done) <= 1 and eos in done:
            # done without unprocessed item
            await eos  # reraise exception if that caused eos
            return EndOfStream
        for fut in done:
            if fut is not eos:
                if fut.cancelled():
                    if eos.done():
                        return EndOfStream
                return await fut
    except asyncio.CancelledError:
        if eos.done():
            await eos  # reraise exception if that caused eos
            return EndOfStream
        logger.debug(
            f"stream reading cancelled before eos: {eos!s}",
            exc_info=True,
            stack_info=True,
        )
        raise  # reraise as is, if not at eos yet

    assert False, "impossible to reach here"
