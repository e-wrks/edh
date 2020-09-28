"""
Some ADTs on par with Haskell idioms

"""
__all__ = ["Maybe", "Nothing", "Just"]

from typing import *


class _Nothing:
    __slots__ = ()

    def __repr__(self):
        return "Nothing"


Nothing = _Nothing()


class JustMeta(type):
    elemType = Any

    def __getitem__(cls, ty):
        class SomeJust(metaclass=JustMeta):
            elemType = ty
            __slots__ = ("data",)

            def __init__(self, data):
                elemType = type(self).elemType
                if elemType != Any and not isinstance(data, elemType):
                    raise TypeError(
                        f"Invalid data type [{type(data)!r}] while [{type(self.elemType)!r}] expected."
                    )
                self.data = data

            def __repr__(self):
                return f"{type(self)!r}({self.data!r})"

        return SomeJust

    def __repr__(cls):
        try:
            typeName = cls.elemType.__name__
        except (TypeError, AttributeError, ValueError):
            typeName = repr(cls.elemType)
        return f"Just[{typeName!s}]"


class _Just(metaclass=JustMeta):
    pass


Just = _Just[Any]


class MaybeMeta(type):

    elemType = Any

    def __instancecheck__(cls, obj) -> bool:
        if obj is Nothing:
            return True
        if cls.elemType == Any:
            return True
        if isinstance(type(obj), JustMeta):
            if cls.elemType == type(obj).elemType:
                return True
        return False

    def __getitem__(cls, ty):
        class SomeMaybe(metaclass=MaybeMeta):
            elemType = ty

        return SomeMaybe

    def __repr__(cls):
        try:
            typeName = cls.elemType.__name__
        except (TypeError, AttributeError, ValueError):
            typeName = repr(cls.elemType)
        return f"Maybe[{typeName!s}]"


class _Maybe(metaclass=MaybeMeta):
    pass


Maybe = _Maybe[Any]


def maybe(defaultValue, maybeValue: Maybe[Any]):
    if isinstance(type(maybeValue), JustMeta):
        return maybeValue.data
    return defaultValue
