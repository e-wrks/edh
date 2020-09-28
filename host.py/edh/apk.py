__all__ = [
    "ArgsPack",
]


class ArgsPack:
    __slots__ = "args", "kwargs"

    def __init__(self, *args, **kwargs):
        self.args = args
        self.kwargs = kwargs

    def __repr__(self):
        return "".join(
            (
                "ArgsPack( ",
                *(repr(arg) + ", " for arg in self.args),
                *(str(k) + "=" + repr(v) + ", " for (k, v) in self.kwargs.items()),
                ")",
            )
        )

