"""
Pygments syntax support for Edh

"""

__all__ = [
    "EdhLexer",
]


import re

from pygments.lexer import (
    RegexLexer,
    include,
    bygroups,
    default,
    using,
    this,
    words,
    combined,
)
from pygments.token import (
    Text,
    Comment,
    Operator,
    Keyword,
    Name,
    String,
    Number,
    Punctuation,
    Other,
)
from pygments.util import get_bool_opt
import pygments.unistring as uni


def setup(app):
    app.add_lexer("edh", EdhLexer)


EDH_IDENT_START = (
    "(?:[_" + uni.combine("Lu", "Ll", "Lt", "Lm", "Lo", "Nl") + "]|\\\\u[a-fA-F0-9]{4})"
)
EDH_IDENT_PART = (
    "(?:[_'"
    + uni.combine("Lu", "Ll", "Lt", "Lm", "Lo", "Nl", "Mn", "Mc", "Nd", "Pc")
    + "\u200c\u200d]|\\\\u[a-fA-F0-9]{4})"
)
EDH_IDENT = EDH_IDENT_START + "(?:" + EDH_IDENT_PART + ")*"


class EdhLexer(RegexLexer):
    """
    For Edh source code.
    """

    name = "Edh"
    aliases = [
        "edh",
    ]
    filenames = [
        "*.edh",
    ]
    mimetypes = [
        "application/edh",
        "text/edh",
    ]

    flags = re.DOTALL | re.UNICODE | re.MULTILINE

    tokens = {
        "commentsandwhitespace": [
            (r"\s+", Text),
            (r"#.*?\n", Comment.Single),
            (r"{#.*?#}", Comment.Multiline),
        ],
        "root": [
            include("commentsandwhitespace"),
            # Numeric literal
            (r"([0-9]+\.[0-9]*|[0-9]+)([eE][-+]?[0-9]+)?", Number.Float),
            (r"[\=\~\!\@\#\$\%\^\&\|\:\<\>\?\+\-\*/\[\]]+", Operator,),
            (r"[{(\[;,})\].]", Punctuation),
            (
                r"(while|for|from|do|break|continue|return|default|case|of|if|then|else|"
                r"throw|rethrow|ai|go|expr|sink|void|is|not|yield|this|that)\b",
                Keyword,
            ),
            (r"(effect|let|as)\b", Keyword.Declaration),
            (
                r"(export|data|class|method|generator|producer|interpreter|operator|"
                r"extends|super|import|into|perform|behave|new)\b",
                Keyword.Reserved,
            ),
            (
                r"(true|false|nil|nan|inf|Nothing|None|NA|All|Any|EQ|LT|GT)\b",
                Keyword.Constant,
            ),
            (
                r"(namespace|module|scope|null|type|constructor|supers|property|setter|dict|"
                r"error|assert|print|abs|max|min|Symbol|id|blob|str|repr|show|desc|cap|"
                r"grow|len|mark|range|enumerate|replicate|zip|zip3|scope|makeOp|makeExpr|"
                r"partial|console|batteries|debug)\b",
                Name.Builtin,
            ),
            (EDH_IDENT, Name.Other),
            (r'"""', String.Double, "triple-double"),
            (r"'''", String.Single, "triple-single"),
            (r"```", String.Backtick, "triple-backtick"),
            (r'"(\\\\|\\"|[^"])*"', String.Double),
            (r"'(\\\\|\\'|[^'])*'", String.Single),
            (r"`(\\\\|\\'|[^`])*'", String.Backtick),
        ],
        "triple-double": [
            (r'"""', String.Double, "#pop"),
            (r'\\"', String.Double),
            (r'[^"\\$]+', String.Double),
        ],
        "triple-single": [
            (r"'''", String.Single, "#pop"),
            (r"\\'", String.Single),
            (r"[^'\\$]+", String.Single),
        ],
        "triple-backtick": [
            (r"```", String.Backtick, "#pop"),
            (r"\\`", String.Backtick),
            (r"[^`\\$]+", String.Backtick),
        ],
    }
