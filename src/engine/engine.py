"""PyOptimize engine loader.

The implementation is split into ordered parts to keep concerns separated while
preserving a single shared namespace.  Importing this module executes the parts
in order; the Pyodide worker also loads the same parts in order.
"""
from pathlib import Path

_PARTS = [
    "engine_01_foundation.py",
    "engine_02_runtime.py",
    "engine_03_rules.py",
    "engine_04_optimize.py",
    "engine_05_pipeline.py",
]

_dir = Path(__file__).resolve().parent
for _name in _PARTS:
    _code = (_dir / _name).read_text()
    exec(compile(_code, str(_dir / _name), "exec"), globals())

del _PARTS, _dir, _name, _code
