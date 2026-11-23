"""Surgical, AST-aware edits to engine.py. Temporary tooling; deleted before the final build."""
import ast

P = "src/engine/engine.py"


def load():
    return open(P).read()


def save(src):
    ast.parse(src)  # refuse to write broken syntax
    open(P, "w").write(src)


def top_defs(src, name):
    tree = ast.parse(src)
    return [(n.lineno, n.end_lineno) for n in tree.body
            if isinstance(n, (ast.FunctionDef, ast.ClassDef)) and n.name == name]


def _cut(src, a, b, new_lines):
    lines = src.split("\n")
    lines[a - 1:b] = new_lines
    return "\n".join(lines)


def replace_nth(src, name, nth, new_code):
    spans = top_defs(src, name)
    assert len(spans) > nth, f"{name}[{nth}] missing (have {len(spans)})"
    a, b = spans[nth]
    return _cut(src, a, b, new_code.strip("\n").split("\n"))


def delete_nth(src, name, nth):
    spans = top_defs(src, name)
    assert len(spans) > nth, f"{name}[{nth}] missing"
    a, b = spans[nth]
    return _cut(src, a, b, [])


def replace_between(src, start_marker, end_marker, new_code):
    a = src.index(start_marker)
    b = src.index(end_marker, a + len(start_marker))
    return src[:a] + new_code.strip("\n") + "\n\n\n" + src[b:]


def sub1(src, old, new):
    assert src.count(old) == 1, f"want exactly 1 match, have {src.count(old)}: {old[:100]!r}"
    return src.replace(old, new, 1)


def duplicates(src):
    """Top-level names defined more than once (functions/classes/assignments)."""
    from collections import Counter
    tree = ast.parse(src)
    c = Counter()
    where = {}
    for n in tree.body:
        names = []
        if isinstance(n, (ast.FunctionDef, ast.ClassDef)):
            names = [n.name]
        elif isinstance(n, ast.Assign):
            names = [t.id for t in n.targets if isinstance(t, ast.Name)]
        for nm in names:
            c[nm] += 1
            where.setdefault(nm, []).append(n.lineno)
    return {k: v for k, v in c.items() if k.startswith("_") is False and c[k] > 1 or (k.startswith("_") and c[k] > 1)}, where
