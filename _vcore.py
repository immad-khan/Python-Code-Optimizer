# ---- input generation ------------------------------------------------------------
# The pool is adversarial on purpose: empty, singleton, all-equal, duplicates, sorted, reversed,
# negatives, 0, big ints, floats (0.1, -0.0, inf, nan), None, bool, bytes, tuples, nested lists.
# Argument *shapes* are inferred from how the function uses its parameters, and user "test hints"
# are mixed INTO the pool (never replacing it): first test is the hint verbatim, then every 4th.
SHAPE_KEY = "_arg%d"


def _list_for(tag, shape, k, test_idx, rng, cap=None):
    """ordered pool of adversarial list contents"""
    k = min(k, cap) if cap else k
    mode = test_idx % 14
    if mode == 0:
        items = []
    elif mode == 1:
        items = [0]
    elif mode == 2:
        items = [0] * k
    elif mode == 3:
        items = [1] * k
    elif mode == 4:
        items = list(range(k, 0, -1))
    elif mode == 5:
        items = list(range(k))
    elif mode == 6:
        items = [-1 - i for i in range(k)]
    elif mode == 7:
        items = [2 ** 64, -(2 ** 64), 0, 1, -1] + [2 ** 64] * max(0, k - 5)
    elif mode == 8:
        items = [0.1, -0.0, float("inf"), float("nan"), 1e308] + [0.1] * max(0, k - 5)
    elif mode == 9:
        items = [True, False, 1, 0] + [True] * max(0, k - 4)
    elif mode == 10:
        items = [(1,), (2,), (1,)] + [(1,)] * max(0, k - 3)
    elif mode == 11:
        items = [[1], [2], [1]] + [[1]] * max(0, k - 3)
    elif mode == 12:
        items = [1, "1", 1.0, None, b"x"][:max(0, k)]
    else:
        items = [rng.randint(-3, 6) for _ in range(k)]
    items = items[:k] if k else (items if mode in (0,) else [])
    if shape == "matrix":
        return [[x] for x in items]
    if shape == "pairs":
        return [[items[i], items[(i + 1) % len(items)]] for i in range(len(items))] if items else []
    return items


def make_graph(k, rng, dense=False):
    """graph = dict node -> list of neighbours.  Every node is a key; every neighbour id is < node count."""
    k = max(1, k)
    nodes = list(range(k))
    g = {}
    for u in nodes:
        if dense:
            g[u] = [v for v in nodes if v != u]
        else:
            deg = rng.randint(0, min(3, k - 1))
            g[u] = rng.sample(nodes, deg) if k > 1 else []
    return g


def make_small_args(tags, seed, test_idx=0, int_cap=None, hints=None, shapes=None, fn_name=None):
    """One test input.  Hints ADD to the pool: test 0 is the first hint verbatim, then every 4th test
    is a lightly mutated hint; everything else comes from the adversarial pool."""
    rng = random.Random(seed)
    seeds = parse_hint_calls(hints, fn_name, len(tags)) if (fn_name and hints) else []
    if seeds:
        if test_idx == 0:
            return copy.deepcopy(seeds[0])
        if test_idx % 4 == 0:
            base = copy.deepcopy(seeds[(test_idx // 4) % len(seeds)])
            try:
                i = rng.randrange(len(base))
                if isinstance(base[i], list) and base[i]:
                    base[i] = list(base[i])
                    if isinstance(base[i][0], int):
                        base[i][0] = rng.randint(-5, 9)
                elif isinstance(base[i], int) and not isinstance(base[i], bool):
                    base[i] = base[i] + rng.randint(-2, 2)
            except Exception:
                pass
            return base
    sizes = [0, 1, 2, 3, 4, 5, 6, 8]
    n = sizes[test_idx % len(sizes)] + (test_idx // len(sizes)) % 4
    if int_cap:
        n = min(n, max(0, int_cap // 4))
    out = []
    caps = [1, 10, 100, 0, -1, -7, 5, 2, 3]
    graph = None
    for i, t in enumerate(tags):
        shape = (shapes or {}).get(SHAPE_KEY % i)
        if t == "int":
            # A node id that indexes a graph argument must be one of its keys, or nearly every run
            # is a KeyError (a "both raised" run, which does not count as a normal run).
            if graph is not None and test_idx % 5 != 4:
                out.append(list(graph)[test_idx % len(graph)])
                continue
            if int_cap is not None and int_cap <= 10:
                vals = list(range(1, int_cap + 1)) + [0, -1, -2]
            else:
                vals = caps + [2 ** 64, -(2 ** 64), 2 ** 31]
            out.append(vals[test_idx % len(vals)])
        elif t == "float":
            out.append([0.1, -0.0, float("inf"), float("-inf"), float("nan"), 3.5, 0.0, -2.0][test_idx % 8])
        elif t == "bool":
            out.append(bool(test_idx % 2))
        elif t == "str":
            out.append(["", "a", "aa", "ab", "aba", "racecar", "A man, a plan, a canal: Panama", None,
                        "élan", "日本語日", "12321", "hello world", " a ", "   ", "No 'x' in Nixon"][test_idx % 15])
        elif t == "bytes":
            out.append([b"", b"abc", b"\x00\x01"][test_idx % 3])
        elif t == "any":
            out.append(None if test_idx % 7 == 0 else test_idx)
        elif t == "dict":
            if shape == "dictlists":
                graph = make_graph(max(1, n), rng, dense=(test_idx % 3 == 0))
                out.append(graph)
            elif shape == "pairsdict":
                out.append({u: [rng.randint(-2, 4), rng.randint(-2, 4)] for u in range(max(1, n))})
            else:
                out.append({i: rng.randint(0, 9) for i in range(n)})
        elif t == "set":
            out.append(set(rng.randint(0, 5) for _ in range(n)))
        else:
            out.append(_list_for(t, shape, n, test_idx, rng, int_cap))
    return out


# ---- argument shapes ---------------------------------------------------------------
def _usage_tag(fn, p):
    """Type tag for parameter p from how it is used (graph before generic subscripting)."""
    subscripted = double_sub = arith = iterated = False
    str_methods = {"lower", "upper", "split", "join", "strip", "isalpha", "isdigit", "replace", "startswith", "endswith", "isalnum"}
    list_methods = {"append", "sort", "pop", "extend", "insert", "index", "count", "remove"}
    dict_methods = {"items", "keys", "values", "get"}
    for n in ast.walk(fn):
        if isinstance(n, ast.Subscript) and isinstance(n.value, ast.Subscript) and is_name(n.value.value, p):
            double_sub = True
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute) and is_name(n.func.value, p):
            if n.func.attr in str_methods:
                return "str"
            if n.func.attr in list_methods:
                return "list"
            if n.func.attr in dict_methods:
                return "dict"
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute) and isinstance(n.func.value, ast.Subscript) and is_name(n.func.value.value, p) \
                and n.func.attr in ("append", "add", "extend"):
            return "dict"                      # adj[u].append(v)  -> graph
        if isinstance(n, ast.For) and isinstance(n.iter, ast.Subscript) and is_name(n.iter.value, p):
            return "dict"                      # for v in adj[u]   -> graph
        if isinstance(n, ast.Call) and is_name(n.func, "len") and n.args and isinstance(n.args[0], ast.Subscript) and is_name(n.args[0].value, p):
            return "dict"                      # len(adj[u])
        if isinstance(n, ast.Subscript) and is_name(n.value, p):
            subscripted = True
        if isinstance(n, ast.Call) and is_name(n.func, "len") and n.args and is_name(n.args[0], p):
            iterated = True
        if isinstance(n, ast.For) and is_name(n.iter, p):
            iterated = True
        if isinstance(n, ast.Call) and is_name(n.func, "range") and any(is_name(a, p) for a in n.args):
            arith = True
        if isinstance(n, ast.BinOp) and (is_name(n.left, p) or is_name(n.right, p)) and isinstance(n.op, (ast.Mod, ast.FloorDiv, ast.Pow, ast.Sub, ast.Mult)):
            arith = True
        if isinstance(n, ast.Compare) and is_name(n.left, p) and all(is_const_int(c) for c in n.comparators):
            arith = True
    if double_sub:
        return "matrix"
    if subscripted or iterated:
        return "list"
    if arith:
        return "int"
    return None


def shape_hints(fn):
    """Per-argument shape refinements used by the generator: matrix / pairs / dictlists / pairsdict."""
    params = [a.arg for a in fn.args.args]
    shapes = {p: None for p in params}
    for n in ast.walk(fn):
        if isinstance(n, ast.Subscript) and isinstance(n.value, ast.Subscript) and is_name(n.value.value) and n.value.value.id in shapes:
            shapes[n.value.value.id] = "matrix"
        if isinstance(n, ast.For) and isinstance(n.iter, ast.Name) and isinstance(n.target, ast.Tuple) and len(n.target.elts) == 2 and n.iter.id in shapes:
            shapes[n.iter.id] = "pairs"
        if isinstance(n, ast.For) and isinstance(n.iter, ast.Subscript) and is_name(n.iter.value) and n.iter.value.id in shapes \
                and isinstance(n.target, ast.Tuple):
            shapes[n.iter.value.id] = "pairsdict"
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute) and isinstance(n.func.value, ast.Subscript) \
                and is_name(n.func.value.value) and n.func.value.value.id in shapes and n.func.attr in ("append", "add", "extend"):
            shapes[n.func.value.value.id] = "dictlists"
    return shapes


def shape_map(fn, tags=None):
    """{SHAPE_KEY % index: shape} for the generator, aligned with positional parameters.
    A parameter used as `adj[u]` / `for v in adj[u]` is a GRAPH: its values must be lists of
    in-range neighbour ids, which the generic dict generator does not produce."""
    hints = shape_hints(fn)
    out = {SHAPE_KEY % i: hints.get(a.arg) for i, a in enumerate(fn.args.args)}
    for i, a in enumerate(fn.args.args):
        if out[SHAPE_KEY % i] is None and _usage_tag(fn, a.arg) == "dict" and (tags is None or tags[i] == "dict"):
            out[SHAPE_KEY % i] = "dictlists"
    return out


def parse_hint_calls(hints, fn_name, arity):
    """`f([1,2], 3)` lines pasted by the user -> list of argument lists."""
    out = []
    if not hints:
        return out
    try:
        tree = ast.parse(hints)
    except SyntaxError:
        return out
    for n in ast.walk(tree):
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == fn_name and len(n.args) == arity and not n.keywords:
            try:
                out.append([ast.literal_eval(a) for a in n.args])
            except Exception:
                continue
    return out


# ---- strict equality -----------------------------------------------------------------
def strict_equal(a, b):
    """same type and same value.  Floats bit-exact, NaN == NaN, -0.0 != 0.0, 1 != True.  Containers recursive."""
    if type(a) is not type(b):
        return False
    if isinstance(a, float):
        if a != a and b != b:
            return True
        return struct.pack(">d", a) == struct.pack(">d", b)
    if isinstance(a, (int, str, bytes, bool, type(None), complex)):
        return a == b
    if isinstance(a, (list, tuple)):
        return len(a) == len(b) and all(strict_equal(x, y) for x, y in zip(a, b))
    if isinstance(a, (set, frozenset)):
        if len(a) != len(b):
            return False
        rest = list(b)
        for x in a:
            for i, y in enumerate(rest):
                if strict_equal(x, y):
                    rest.pop(i)
                    break
            else:
                return False
        return True
    if isinstance(a, dict):
        if len(a) != len(b):
            return False
        ka, kb = list(a), list(b)
        used = [False] * len(kb)
        for k in ka:
            for j, k2 in enumerate(kb):
                if not used[j] and strict_equal(k, k2) and strict_equal(a[k], b[k2]):
                    used[j] = True
                    break
            else:
                return False
        return True
    try:
        return type(a) is type(b) and a == b
    except Exception:
        return False


def _strict_returns(a, b):
    """Return values must match strictly.  No loose fallback: [0.0] is NOT [0]."""
    return strict_equal(a, b)
