# Things Đ (Edh) improved over Python

## Value Identity

```python
>>> x=2
>>> y=2
>>> x is y
True
>>> x=1000
>>> y=1000
>>> x is y
False
```

```edh
(repl)Đ: x=1000
1000
(repl)Đ: y=1000
1000
(repl)Đ: x is y
true
```

## Safty with `import *`

- You'd better define `__all__ = [ ... ]` for every **Python** module, in case
  others do `import *` from a module without the whitelist, all artifacts it
  ever imported will go overwrite the importer's scope as well.

- In Đ (Edh), artifacts not explicitly marked `export` are not eligible for
  `import *`, the concern is eliminated.
