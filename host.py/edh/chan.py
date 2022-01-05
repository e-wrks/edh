"""
Blocking Channel at par to Edh's

"""
__all__ = ["BChan"]

import asyncio

from typing import *

from .ctrl import *
from .adt import *


class BChanSitter:
    pass


BChanEOS = BChanSitter()
BChanIdle = BChanSitter()


class BChanReader(BChanSitter):
    __slots__ = ("rcvr",)

    def __init__(self):
        loop = asyncio.get_running_loop()
        self.rcvr = loop.create_future()


class BChanWriter(BChanSitter):
    __slots__ = ("v", "taken")

    def __init__(self, v):
        loop = asyncio.get_running_loop()
        self.v = v
        self.taken = loop.create_future()


class BChan:
    """
    Blocking Channel at par to Edh's

    """

    __slots__ = ("sitter",)

    def __init__(self):
        self.sitter = BChanIdle

    @property
    def eos(self) -> bool:
        return self.sitter is BChanEOS

    def close(self) -> bool:
        """
        Close the channel

        """
        try:
            sitter = self.sitter

            if isinstance(sitter, BChanReader):
                sitter.rcvr.set_result(EndOfStream)
                return True
            elif sitter is BChanIdle:
                return True
            elif isinstance(sitter, BChanWriter):
                sitter.taken.set_result(False)
                return True
            elif sitter is BChanEOS:
                return False

            assert False, f"unexpected BChan sitter: {sitter}"

        finally:
            self.sitter = BChanEOS

    async def stream(self):
        while True:
            v = await self.get()
            if v is EndOfStream:
                return
            yield v

    async def get(self):
        """
        Read a value out of a channel, blocking until some writer actually send
        a value through the channel.

        `EndOfStream` will be returned indicating the channel has reached
        end-of-stream, either after blocking read or the channel has already
        been so before the attempt.

        """

        while True:
            sitter = self.sitter

            if isinstance(sitter, BChanWriter):
                v = sitter.v
                sitter.taken.set_result(True)
                self.sitter = BChanIdle
                return v
            elif sitter is BChanIdle:
                self.sitter = BChanReader()
                return await self.sitter.rcvr
            elif isinstance(sitter, BChanReader):
                v = await sitter.rcvr
                if v is EndOfStream:
                    return EndOfStream
                continue
            elif sitter is BChanEOS:
                return EndOfStream

            assert False, f"unexpected BChan sitter: {sitter}"

    async def put(self, v) -> bool:
        """
        Write a value into the channel, blocking until some reader is ready and
        actually receives the value.

        Writing an `EndOfStream` carries the special semantics as marking the
        channel end-of-stream, and will NOT block. Otherwise `True` will be
        returned if the value is actually received by some reader, or 'False'
        if the channel reached eos before that can happen.

        """

        if v is EndOfStream:
            return self.close()

        while True:
            sitter = self.sitter

            if isinstance(sitter, BChanReader):
                sitter.rcvr.set_result(v)
                self.sitter = BChanIdle
                return True
            elif sitter is BChanIdle:
                self.sitter = BChanWriter(v)
                return await self.sitter.taken
            elif isinstance(sitter, BChanWriter):
                await sitter.taken
                continue
            elif sitter is BChanEOS:
                return False

            assert False, f"unexpected BChan sitter: {sitter}"
