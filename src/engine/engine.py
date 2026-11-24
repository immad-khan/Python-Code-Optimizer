"""
PyOptimize engine
-----------------
Runs inside Pyodide (or CPython). Pure standard library.

Pipeline:
  1. Parse user code -> AST
  2. Static complexity analysis (loop nesting, recursion / master theorem,
     halving loops, builtin costs, membership tests, etc.)
  3. Empirical benchmark of the whole program + growth benchmark of the
     "hot" function with generated inputs of increasing size; least-squares
     fit against canonical growth models.
  4. Rule-based optimizer: a sequence of AST transformations.  Every
     transformation is applied, compiled and then *verified* against the
     original using randomized differential testing.  Transformations that
     change behaviour are reverted automatically.
  5. Re-analyze + re-benchmark optimized code.
"""
import ast
import sys
import io
import time
import math
import random
import json
import copy
import traceback
import functools
import collections
import itertools
import bisect
import gc
import types

# Under Pyodide (Emscripten) the WebAssembly stack overflows *before* CPython's
# default recursion limit is reached, which kills the interpreter.  Python 3.12
# does not count C-level frames (e.g. lru_cache wrappers), so stay conservative.
SANDBOX_RECURSION_LIMIT = 240
if sys.platform == "emscripten":
    sys.setrecursionlimit(SANDBOX_RECURSION_LIMIT)

# --------------------------------------------------------------------------
# progress reporting (js_progress is injected by the worker, optional)
# --------------------------------------------------------------------------
def _progress(stage, message, payload=None):
    try:
        fn = globals().get("js_progress")
        if fn is not None:
            fn(json.dumps({"stage": stage, "message": message, "payload": payload}))
    except Exception:
        pass


# --------------------------------------------------------------------------
# Complexity algebra
# --------------------------------------------------------------------------
class Cx:
    """n^p * (log n)^l * e^n  (fact => n!)"""
    __slots__ = ("p", "l", "e", "fact")

    def __init__(self, p=0.0, l=0, e=0, fact=False):
        self.p = float(p)
        self.l = int(l)
        self.e = int(e)
        self.fact = bool(fact)

    def key(self):
        return (1 if self.fact else 0, self.e, self.p, self.l)

    def __mul__(self, other):
        e = 0
        if self.e and other.e:
            e = self.e * other.e
        else:
            e = self.e or other.e
        return Cx(self.p + other.p, self.l + other.l, e, self.fact or other.fact)

    def __or__(self, other):  # max
        return self if self.key() >= other.key() else other

    def is_const(self):
        return self.key() == (0, 0, 0.0, 0)

    def __str__(self):
        if self.fact:
            return "O(n!)"
        parts = []
        if self.e:
            parts.append(f"{self.e}^n")
        if self.p:
            if self.p == 0.5:
                parts.append("√n")
            elif self.p == 1:
                parts.append("n")
            elif self.p == 1.5:
                parts.append("n√n")
            elif float(self.p).is_integer():
                parts.append("n" + _sup(int(self.p)))
            else:
                parts.append(f"n^{self.p:g}")
        if self.l:
            parts.append("log n" if self.l == 1 else "log" + _sup(self.l) + " n")
        if not parts:
            return "O(1)"
        return "O(" + " · ".join(parts) + ")"

    def rank(self):
        """numeric rank for comparison in the UI (bigger = slower)"""
        if self.fact:
            return 100
        if self.e:
            return 50 + self.e
        return self.p * 10 + self.l


def _sup(n):
    return str(n).translate(str.maketrans("0123456789", "⁰¹²³⁴⁵⁶⁷⁸⁹"))


C1 = Cx()
CLOG = Cx(0, 1)
CSQRT = Cx(0.5)
CN = Cx(1)
CNLOGN = Cx(1, 1)
CN2 = Cx(2)


# --------------------------------------------------------------------------
# AST helpers
# --------------------------------------------------------------------------
LIST_NAMES = {"arr", "array", "nums", "numbers", "lst", "list", "items", "values", "data",
              "elements", "a", "b", "seq", "sequence", "l", "xs", "ys", "vals", "vector",
              "numbers_list", "input_list", "words", "lists", "collection", "prices", "heights",
              "weights", "scores", "points", "intervals", "digits"}
INT_NAMES = {"n", "num", "number", "k", "x", "y", "m", "target", "limit", "size", "count",
             "total", "value", "v", "i", "j", "p", "q", "amount", "steps", "length", "depth",
             "max_value", "capacity", "sum_", "goal", "index", "idx", "base", "exp", "power",
             "exponent", "rows", "cols", "r", "c", "num1", "num2", "low", "high"}
STR_NAMES = {"s", "string", "text", "word", "str_", "s1", "s2", "pattern", "sentence", "txt",
             "t", "needle", "haystack", "name", "message", "line", "chars"}
MATRIX_NAMES = {"matrix", "grid", "board", "mat", "table", "graph_matrix"}
DICT_NAMES = {"d", "dct", "mapping", "dictionary", "graph", "adj", "memo", "cache", "freq",
              "counts", "hashmap", "lookup"}
SET_LIKE_CALLS = {"set", "frozenset", "dict", "Counter", "defaultdict", "OrderedDict"}
MUTATING_METHODS = {"append", "extend", "insert", "pop", "remove", "sort", "reverse", "clear",
                    "update", "add", "discard", "setdefault", "popitem", "appendleft", "popleft",
                    "push", "put"}


def node_names(node):
    return {n.id for n in ast.walk(node) if isinstance(n, ast.Name)}


def names_written(node):
    """names assigned, mutated via method call, or subscript-assigned inside node"""
    out = set()
    for n in ast.walk(node):
        if isinstance(n, (ast.Assign, ast.AugAssign, ast.AnnAssign)):
            targets = n.targets if isinstance(n, ast.Assign) else [n.target]
            for t in targets:
                for sub in ast.walk(t):
                    if isinstance(sub, ast.Name):
                        out.add(sub.id)
        elif isinstance(n, (ast.For, ast.comprehension)):
            for sub in ast.walk(n.target):
                if isinstance(sub, ast.Name):
                    out.add(sub.id)
        elif isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute):
            if n.func.attr in MUTATING_METHODS:
                base = n.func.value
                while isinstance(base, (ast.Subscript, ast.Attribute)):
                    base = base.value
                if isinstance(base, ast.Name):
                    out.add(base.id)
        elif isinstance(n, ast.Delete):
            for t in n.targets:
                for sub in ast.walk(t):
                    if isinstance(sub, ast.Name):
                        out.add(sub.id)
        elif isinstance(n, ast.NamedExpr) and isinstance(n.target, ast.Name):
            out.add(n.target.id)
    return out


def is_const_int(node):
    return isinstance(node, ast.Constant) and isinstance(node.value, (int, float)) and not isinstance(node.value, bool)


def is_name(node, name=None):
    return isinstance(node, ast.Name) and (name is None or node.id == name)


def call_name(node):
    """'sorted' for sorted(x);  '.sort' for x.sort()"""
    if not isinstance(node, ast.Call):
        return None
    if isinstance(node.func, ast.Name):
        return node.func.id
    if isinstance(node.func, ast.Attribute):
        return "." + node.func.attr
    return None


def attr_base_name(node):
    if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name):
        return node.value.id
    return None


def set_parents(tree):
    for parent in ast.walk(tree):
        for child in ast.iter_child_nodes(parent):
            child._parent = parent
    return tree


def iter_stmt_lists(node):
    for field in ("body", "orelse", "finalbody"):
        lst = getattr(node, field, None)
        if isinstance(lst, list):
            yield field, lst
    if isinstance(node, ast.Try):
        for h in node.handlers:
            yield "handler", h.body
    if isinstance(node, ast.Match) if hasattr(ast, "Match") else False:
        for c in node.cases:
            yield "case", c.body


def enclosing_loops(node):
    out = []
    cur = getattr(node, "_parent", None)
    while cur is not None:
        if isinstance(cur, (ast.For, ast.While)):
            out.append(cur)
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            break
        cur = getattr(cur, "_parent", None)
    return out  # innermost first


def dump_src(tree):
    ast.fix_missing_locations(tree)
    return ast.unparse(tree)


def contains_node_type(node, types):
    return any(isinstance(n, types) for n in ast.walk(node))


# --------------------------------------------------------------------------
# Type inference for parameters (used for benchmarks & differential testing)
# --------------------------------------------------------------------------
def infer_param_types(fn, tree, source_calls):
    """Return list of type tags for params: int | list | str | matrix | dict | float | any"""
    params = [a.arg for a in fn.args.args]
    tags = {}
    # 1) annotations
    for a in fn.args.args:
        if a.annotation is not None:
            ann = ast.unparse(a.annotation).lower()
            if "list" in ann or "sequence" in ann or "iterable" in ann:
                tags[a.arg] = "matrix" if ann.count("list") >= 2 else "list"
            elif "int" in ann:
                tags[a.arg] = "int"
            elif "str" in ann:
                tags[a.arg] = "str"
            elif "dict" in ann or "mapping" in ann:
                tags[a.arg] = "dict"
            elif "float" in ann:
                tags[a.arg] = "float"
            elif "set" in ann:
                tags[a.arg] = "set"
    # 2) literal arguments at call sites
    for call in source_calls.get(fn.name, []):
        for i, arg in enumerate(call.args):
            if i >= len(params) or params[i] in tags:
                continue
            try:
                val = ast.literal_eval(arg)
            except Exception:
                continue
            tags[params[i]] = _tag_of_value(val)
    # 3) usage inside function body
    for p in params:
        if p in tags:
            continue
        usage = _usage_tag(fn, p)
        if usage:
            tags[p] = usage
    # 4) names
    for p in params:
        if p in tags:
            continue
        lp = p.lower()
        if lp in MATRIX_NAMES:
            tags[p] = "matrix"
        elif lp in LIST_NAMES or lp.endswith("list") or lp.endswith("arr") or lp.endswith("s") and lp not in STR_NAMES and lp not in INT_NAMES:
            tags[p] = "list"
        elif lp in STR_NAMES or "str" in lp or "text" in lp or "word" in lp:
            tags[p] = "str"
        elif lp in DICT_NAMES or "dict" in lp or "map" in lp:
            tags[p] = "dict"
        elif lp in INT_NAMES or lp.startswith("n") or lp.startswith("num"):
            tags[p] = "int"
        else:
            tags[p] = "int"
    return [tags[p] for p in params]


def _tag_of_value(val):
    if isinstance(val, bool):
        return "int"
    if isinstance(val, int):
        return "int"
    if isinstance(val, float):
        return "float"
    if isinstance(val, str):
        return "str"
    if isinstance(val, (list, tuple)):
        if val and isinstance(val[0], (list, tuple)):
            return "matrix"
        if val and isinstance(val[0], str):
            return "strlist"
        return "list"
    if isinstance(val, dict):
        return "dict"
    if isinstance(val, set):
        return "set"
    return "any"





# ordered most-adversarial first: a value no pair/element can match forces full scans
SECONDARY_STRATEGIES = {
    "big": lambda n: 3 * n + 7,
    "half": lambda n: max(1, n // 2),
    "n": lambda n: n,
    "zero": lambda n: 0,
    "one": lambda n: 1,
}


def _largest_prime_leq(n):
    if n < 2:
        return 2
    c = n
    while c > 2:
        if all(c % p for p in range(2, math.isqrt(c) + 1)):
            return c
        c -= 1
    return 2


PRIMARY_INT_STRATEGIES = {
    "n": lambda n: n,
    "prime": _largest_prime_leq,
    "odd": lambda n: n | 1,
}


def _list_unique(n, rng):
    lst = list(range(n))
    rng.shuffle(lst)
    return lst


LIST_STRATEGIES = {
    "reversed": lambda n, rng: list(range(n, 0, -1)),
    "unique": _list_unique,
    "random": lambda n, rng: [rng.randint(-n, 2 * n + 1) for _ in range(n)],
    "sorted": lambda n, rng: list(range(n)),
}

def _make_palindrome_str(n, rng):
    if n <= 0:
        return ""
    letters = "abcdefghijklmnopqrstuvwxyz"
    half = "".join(rng.choice(letters) for _ in range(n // 2))
    mid = rng.choice(letters) if n % 2 else ""
    return half + mid + half[::-1]

STR_STRATEGIES = {
    "random": lambda n, rng: "".join(rng.choice("abcdefghij") for _ in range(n)),
    "palindrome": _make_palindrome_str,
    "words": lambda n, rng: " ".join("".join(rng.choice("abcdef") for _ in range(rng.randint(2, 6))) for _ in range(max(1, n // 5))),
}

STRATEGY = {"secondary": "half", "primary": "n", "list": "unique", "str": "random"}


def set_strategy(**kw):
    STRATEGY.update(kw)


def make_value(tag, n, rng, secondary=False):
    if tag == "int":
        if secondary:
            return SECONDARY_STRATEGIES[STRATEGY["secondary"]](n)
        return PRIMARY_INT_STRATEGIES[STRATEGY["primary"]](n)
    if tag == "float":
        return float(n)
    if tag == "list":
        return LIST_STRATEGIES[STRATEGY["list"]](n, rng)
    if tag == "strlist":
        return ["".join(rng.choice("abcdefgh") for _ in range(rng.randint(1, 6))) for _ in range(n)]
    if tag == "str":
        return STR_STRATEGIES.get(STRATEGY.get("str", "random"), STR_STRATEGIES["random"])(n, rng)
    if tag == "matrix":
        m = max(1, int(math.sqrt(n)))
        return [[rng.randint(0, 9) for _ in range(m)] for _ in range(m)]
    if tag == "dict":
        return {i: rng.randint(0, n) for i in range(n)}
    if tag == "set":
        return set(rng.randint(0, 2 * n) for _ in range(n))
    return n



PROBE_CANDIDATES = {
    "str": "racecar",
    "list": [1, 2, 3, 2, 1],
    "strlist": ["hello", "world"],
    "int": 5,
    "matrix": [[1, 2], [3, 4]],
    "dict": {1: 2, 3: 4},
    "set": {1, 2, 3},
    "float": 3.14,
}


def probe_signature_prioritized(fn, initial_tags):
    """Safely probes the function with small candidate inputs.
    If initial_tags fail with TypeError, ValueError, or AttributeError,
    tries candidate combinations until a compatible signature is found."""
    if not callable(fn) or not initial_tags:
        return list(initial_tags)
    # 1. Try initial_tags first
    try:
        args = [copy.deepcopy(PROBE_CANDIDATES.get(t, 5)) for t in initial_tags]
        fn(*args)
        return list(initial_tags)
    except (TypeError, ValueError, AttributeError):
        pass
    except Exception:
        return list(initial_tags)

    # 2. Try alternatives: prioritize str, list, int, strlist, matrix
    import itertools
    types = ["str", "list", "int", "strlist", "matrix", "dict"]
    for combo in itertools.product(types, repeat=len(initial_tags)):
        if list(combo) == list(initial_tags):
            continue
        try:
            args = [copy.deepcopy(PROBE_CANDIDATES[t]) for t in combo]
            fn(*args)
            return list(combo)
        except (TypeError, ValueError, AttributeError, IndexError):
            continue
        except Exception:
            return list(combo)
    return list(initial_tags)


def make_args(tags, n, seed, shapes=None):
    """Benchmark-size inputs.  `shapes` ({SHAPE_KEY % index: shape}) makes structured arguments valid:
    pairs reference a sibling list, graphs are dicts of in-range neighbours, node ids come from the graph."""
    rng = random.Random(seed)
    args = []
    primary_done = False
    has_collection = any(t in ("list", "str", "matrix", "dict", "set", "strlist") for t in tags)
    graph = None
    span = n
    # build graphs first: node parameters are drawn from their keys
    graph_by_arg = {}
    for i, t in enumerate(tags):
        if t == "dict" and (shapes or {}).get(SHAPE_KEY % i) in ("dictlists", "pairsdict"):
            graph_by_arg[i] = make_graph(n, rng, dense=False)
    for i, t in enumerate(tags):
        shape = (shapes or {}).get("_arg%d" % i)
        if shape == "node" and graph_by_arg:
            graph = next(iter(graph_by_arg.values()))
            args.append(list(graph)[n % len(graph)])
            continue
        if t in ("int", "float"):
            if graph is not None and t == "int":
                args.append(list(graph)[n % len(graph)])
                continue
            if has_collection:
                args.append(make_value(t, n, rng, secondary=True))
            else:
                args.append(make_value(t, n, rng, secondary=primary_done))
                primary_done = True
        elif shape == "pairs" and t in ("list", "matrix"):
            # shape wins over the tag: the probe often (mis)tags a list-of-pairs as "matrix" because a
            # 2x2 probe happens to unpack. Pairs must be valid queries into a sibling list of length ~span.
            qs = []
            for j in range(max(1, n // 4)):
                lo = rng.randint(0, max(0, span - 1))
                qs.append([lo, rng.randint(lo, span)])
            args.append(qs)
        elif shape == "matrix" and t == "list":
            m = max(1, int(math.sqrt(n)))
            args.append([[rng.randint(0, 9) for _ in range(m)] for _ in range(m)])
        elif shape in ("dictlists", "pairsdict") and t == "dict":
            graph = graph_by_arg.get(i) or make_graph(n, rng, dense=False)
            graph_by_arg[i] = graph
            args.append(graph)
        else:
            v = make_value(t, n, rng)
            if isinstance(v, list) and v:
                span = len(v)
            args.append(v)
    return args




# --------------------------------------------------------------------------
# Static complexity analyzer
# --------------------------------------------------------------------------
_ELEM_METHODS = {".lower", ".upper", ".strip", ".isalnum", ".isalpha", ".isdigit", ".isspace", ".startswith", ".endswith",
                 ".casefold", ".title", ".capitalize", ".swapcase", ".islower", ".isupper", ".isnumeric"}


def _inframe_memo(fn):
    """True when a function keeps its memo lookup inside its own frame
    (`_hit = _memo[key]` inside try/except KeyError/TypeError) — the depth-preserving memo."""
    return any(isinstance(n, ast.Subscript) and isinstance(n.value, ast.Name) and n.value.id.endswith("_memo")
               for n in ast.walk(fn))


class StaticAnalyzer:
    def __init__(self, tree):
        self.tree = tree
        self.functions = {}  # name -> FunctionDef
        for n in ast.walk(tree):
            if isinstance(n, ast.FunctionDef):
                self.functions[n.name] = n
        self.fn_cost = {}
        self.fn_space = {}
        self.fn_notes = {}
        self.set_like = set()
        self._collect_set_like(tree)
        self._stack = []
        self._elem = []

    # -- helpers -----------------------------------------------------------
    def _collect_set_like(self, tree):
        for n in ast.walk(tree):
            if isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name):
                v = n.value
                if isinstance(v, (ast.Set, ast.Dict, ast.SetComp, ast.DictComp)):
                    self.set_like.add(n.targets[0].id)
                elif isinstance(v, ast.Call) and call_name(v) in SET_LIKE_CALLS:
                    self.set_like.add(n.targets[0].id)
            if isinstance(n, ast.FunctionDef):
                for a in n.args.args:
                    lp = a.arg.lower()
                    if lp in DICT_NAMES or (a.annotation is not None and any(k in ast.unparse(a.annotation).lower() for k in ("dict", "set", "mapping"))):
                        self.set_like.add(a.arg)

    def is_memoized(self, fn):
        if _is_memo_wrapper(fn) or _inframe_memo(fn):
            return True
        for d in fn.decorator_list:
            s = ast.unparse(d)
            if "cache" in s or "memo" in s.lower():
                return True
        src = ast.unparse(fn)
        for n in ast.walk(fn):
            if isinstance(n, ast.Compare) and len(n.ops) == 1 and isinstance(n.ops[0], (ast.In, ast.NotIn)):
                rhs = n.comparators[0]
                if isinstance(rhs, ast.Name) and (rhs.id.lower() in ("memo", "cache", "dp", "seen", "table", "lookup") or rhs.id in self.set_like):
                    if ".get(" in src or rhs.id + "[" in src:
                        return True
        return False

    def iter_count(self, iter_node, fn):
        """how many iterations does `for _ in iter_node` run (as Cx)"""
        if isinstance(iter_node, ast.Call) and is_name(iter_node.func, "range"):
            args = iter_node.args
            if all(is_const_int(a) for a in args):
                return C1
            src = ast.unparse(iter_node)
            if "** 0.5" in src or "sqrt(" in src or "isqrt(" in src:
                return CSQRT
            if "log" in src:
                return CLOG
            # range(len(x)//2) etc are still linear
            return CN
        if isinstance(iter_node, (ast.List, ast.Tuple, ast.Set)):
            return C1
        if isinstance(iter_node, ast.Constant):
            return C1
        if isinstance(iter_node, ast.Call):
            cn = call_name(iter_node)
            if cn in ("permutations",):
                return Cx(fact=True)
            if cn in ("combinations",):
                return Cx(2)
            if cn in ("product",):
                return Cx(len(iter_node.args) or 2)
        return CN

    def while_count(self, node):
        test_names = node_names(node.test)
        src_body = node.body
        log_like = False
        linear_like = False
        for n in ast.walk(ast.Module(body=src_body, type_ignores=[])):
            if isinstance(n, ast.AugAssign) and isinstance(n.target, ast.Name) and n.target.id in test_names:
                if isinstance(n.op, (ast.FloorDiv, ast.Div, ast.RShift, ast.LShift, ast.Mult)):
                    log_like = True
                else:
                    linear_like = True
            if isinstance(n, ast.Assign):
                for t in n.targets:
                    if isinstance(t, ast.Name) and t.id in test_names:
                        v = n.value
                        if isinstance(v, ast.BinOp) and isinstance(v.op, (ast.FloorDiv, ast.Div, ast.RShift, ast.LShift, ast.Mult)):
                            log_like = True
                        elif isinstance(v, ast.BinOp) and isinstance(v.op, (ast.Add, ast.Sub)):
                            # binary search: lo = mid + 1 / hi = mid - 1
                            if "mid" in ast.unparse(v).lower():
                                log_like = True
                            else:
                                linear_like = True
                        elif isinstance(v, ast.Call) and call_name(v) in (".pop", ".popleft"):
                            linear_like = True
                        else:
                            linear_like = True
        body_src = ast.unparse(ast.Module(body=src_body, type_ignores=[]))
        if ("// 2" in body_src or "/ 2" in body_src or ">> 1" in body_src or "* 2" in body_src) and not linear_like:
            log_like = True
        if log_like and not linear_like:
            return CLOG
        # `while n % i == 0: n //= i` style factorization, GCD -> log
        if "%" in ast.unparse(node.test) and log_like:
            return CLOG
        return CN

    # -- expression cost ----------------------------------------------------
    def expr_cost(self, node, fn):
        cost = C1
        for n in ast.walk(node):
            if isinstance(n, ast.Call):
                cost = cost | self.call_cost(n, fn)
            elif isinstance(n, ast.Compare):
                for op, rhs in zip(n.ops, n.comparators):
                    if isinstance(op, (ast.In, ast.NotIn)):
                        cost = cost | self.membership_cost(rhs)
            elif isinstance(n, (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)):
                cost = cost | self.comp_cost(n, fn)
            elif isinstance(n, ast.Subscript) and isinstance(n.slice, ast.Slice):
                cost = cost | CN
            elif isinstance(n, ast.BinOp) and isinstance(n.op, ast.Pow):
                cost = cost | CLOG
            elif isinstance(n, ast.BinOp) and isinstance(n.op, ast.Add) and (
                    isinstance(n.left, (ast.List, ast.ListComp)) or isinstance(n.right, (ast.List, ast.ListComp))):
                cost = cost | CN
        return cost

    def membership_cost(self, rhs):
        if isinstance(rhs, (ast.Set, ast.Dict, ast.SetComp, ast.DictComp)):
            return C1
        if isinstance(rhs, ast.Name):
            return C1 if rhs.id in self.set_like else CN
        if isinstance(rhs, ast.Call):
            cn = call_name(rhs)
            if cn in (".keys", "set", "dict", "range", "frozenset"):
                return C1
            return CN
        if isinstance(rhs, ast.Constant):
            return C1 if not isinstance(rhs.value, str) else CN
        if isinstance(rhs, (ast.List, ast.Tuple)):
            return C1
        return CN

    def comp_cost(self, node, fn):
        elem = set()
        for gen in node.generators:
            elem |= node_names(gen.target)
        self._elem.append(elem)
        try:
            return self._comp_cost_inner(node, fn)
        finally:
            self._elem.pop()

    def _comp_cost_inner(self, node, fn):
        total = C1
        for gen in node.generators:
            total = total * self.iter_count(gen.iter, fn)
            for cond in gen.ifs:
                total = total * self.expr_cost(cond, fn)
        if isinstance(node, ast.DictComp):
            inner = self.expr_cost(node.key, fn) | self.expr_cost(node.value, fn)
        else:
            inner = self.expr_cost(node.elt, fn)
        return total * inner

    def call_cost(self, node, fn):
        cn = call_name(node)
        if cn is None:
            return C1
        if (cn in _ELEM_METHODS and isinstance(node.func, ast.Attribute) and isinstance(node.func.value, ast.Name)
                and any(node.func.value.id in e for e in self._elem)):
            return C1          # per-element string method: elements are pieces of the input, O(1) in the input size
        if cn in self.functions and isinstance(node.func, ast.Name):
            return self.function_cost(cn)
        if cn in ("sorted", ".sort"):
            return CNLOGN
        if cn in ("sum", "max", "min", "len", "list", "tuple", "set", "any", "all", "reversed",
                  "enumerate", "zip", "map", "filter", "dict", "frozenset", ".copy", ".join",
                  ".count", ".index", ".remove", ".extend", ".split", ".replace", ".find", ".reverse",
                  ".values", ".keys", ".items", ".lower", ".upper", ".strip", "Counter", "deepcopy",
                  ".union", ".intersection", ".difference", "isinstance", ".startswith", ".endswith"):
            if cn == "len":
                return C1
            if cn in ("enumerate", "zip", "map", "filter", "reversed", "isinstance"):
                return C1
            if cn in ("sum", "max", "min") and node.args and isinstance(node.args[0], ast.GeneratorExp):
                return self.comp_cost(node.args[0], fn)
            if cn in ("max", "min") and len(node.args) >= 2:
                return C1
            return CN
        if cn in (".insert", ".pop") and node.args and not (cn == ".pop" and not node.args):
            # pop(0)/insert(0, x) are linear; pop() constant
            if cn == ".pop" and node.args and is_const_int(node.args[0]) and node.args[0].value == -1:
                return C1
            return CN
        if cn in ("factorial",):
            return CN
        if cn in ("pow", "gcd", "isqrt", "bisect", "bisect_left", "bisect_right", "insort", "heappush", "heappop", "log", "log2"):
            return CLOG
        if cn in ("permutations",):
            return Cx(fact=True)
        if cn == "range":
            return C1
        if cn in self.functions and isinstance(node.func, ast.Name):
            return self.function_cost(cn)
        return C1

    # -- statement cost ------------------------------------------------------
    def stmts_cost(self, stmts, fn):
        total = C1
        for s in stmts:
            total = total | self.stmt_cost(s, fn)
        return total

    def stmt_cost(self, s, fn):
        if isinstance(s, ast.For):
            iters = self.iter_count(s.iter, fn)
            self._elem.append(node_names(s.target))
            try:
                body = self.stmts_cost(s.body, fn)
            finally:
                self._elem.pop()
            setup = self.expr_cost(s.iter, fn)
            cost = (iters * body) | setup | self.stmts_cost(s.orelse, fn)
            # recursion inside a loop:  for i in range(n): f(n-1)  => n!
            if fn is not None and self._recursive_call_in(s.body, fn.name) and iters.p >= 1:
                self.fn_notes.setdefault(fn.name, []).append("recursive call inside a loop over n (factorial growth)")
                cost = cost | Cx(fact=True)
            return cost
        if isinstance(s, ast.While):
            return (self.while_count(s) * (self.stmts_cost(s.body, fn) | self.expr_cost(s.test, fn))) | self.stmts_cost(s.orelse, fn)
        if isinstance(s, ast.If):
            return self.expr_cost(s.test, fn) | self.stmts_cost(s.body, fn) | self.stmts_cost(s.orelse, fn)
        if isinstance(s, (ast.With, ast.Try)):
            c = self.stmts_cost(s.body, fn)
            for _, lst in iter_stmt_lists(s):
                c = c | self.stmts_cost(lst, fn)
            return c
        if isinstance(s, ast.FunctionDef):
            return C1  # defining is O(1); cost is accounted at call sites
        if isinstance(s, ast.ClassDef):
            return C1
        if isinstance(s, (ast.Expr, ast.Return, ast.Assign, ast.AugAssign, ast.AnnAssign)):
            c = C1
            for n in ast.iter_child_nodes(s):
                c = c | self.expr_cost(n, fn)
            # string concatenation in a loop: both s += x and s = s + x (linear copy O(n²))
            is_str_concat = False
            if isinstance(s, ast.AugAssign) and isinstance(s.op, ast.Add) and isinstance(s.target, ast.Name):
                if self._looks_like_str(s.target.id, fn):
                    is_str_concat = True
            elif isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name):
                target_id = s.targets[0].id
                if isinstance(s.value, ast.BinOp) and isinstance(s.value.op, ast.Add):
                    if (is_name(s.value.left, target_id) or is_name(s.value.right, target_id)) and self._looks_like_str(target_id, fn):
                        is_str_concat = True
            if is_str_concat and enclosing_loops(s):
                c = c | CN
                if fn is not None:
                    self.fn_notes.setdefault(fn.name, []).append("repeated string concatenation inside loop copies string (O(n²) total)")
            if isinstance(s, ast.AugAssign) and isinstance(s.op, ast.Add) and isinstance(s.value, (ast.List, ast.ListComp)):
                c = c | CN
            return c
        return C1

    def _looks_like_str(self, name, fn):
        scope = fn if fn is not None else self.tree
        name_lower = name.lower()
        if "str" in name_lower or "text" in name_lower or "word" in name_lower or "chars" in name_lower or "orig" in name_lower:
            return True
        for n in ast.walk(scope):
            if isinstance(n, ast.Assign) and any(is_name(t, name) for t in n.targets):
                if isinstance(n.value, ast.Constant) and isinstance(n.value.value, str):
                    return True
                if isinstance(n.value, ast.JoinedStr):
                    return True
                if isinstance(n.value, ast.Call) and call_name(n.value) in (".join", "str", "chr", ".lower", ".upper", ".strip"):
                    return True
            if isinstance(n, ast.AugAssign) and is_name(n.target, name):
                if isinstance(n.value, (ast.Constant,)) and isinstance(n.value.value, str):
                    return True
                if isinstance(n.value, ast.JoinedStr):
                    return True
                if isinstance(n.value, ast.Call) and call_name(n.value) in ("str", "chr"):
                    return True
        return False

    def _recursive_call_in(self, stmts, name):
        for s in stmts:
            for n in ast.walk(s):
                if isinstance(n, ast.Call) and is_name(n.func, name):
                    return True
        return False

    # -- recursion ----------------------------------------------------------
    def recursion_info(self, fn):
        calls = []
        for n in ast.walk(fn):
            if isinstance(n, ast.Call) and is_name(n.func, fn.name):
                # ignore calls in nested defs
                calls.append(n)
        if not calls:
            return None
        params = [a.arg for a in fn.args.args]
        reductions = []
        for c in calls:
            red = "unknown"
            for a in c.args:
                src = ast.unparse(a)
                if isinstance(a, ast.BinOp) and isinstance(a.op, (ast.FloorDiv, ast.Div, ast.RShift)):
                    red = "halve"
                elif isinstance(a, ast.Subscript) and isinstance(a.slice, ast.Slice):
                    sl = a.slice
                    if ("mid" in src.lower()) or ("// 2" in src) or ("len(" in src and "/" in src):
                        red = "halve"
                    else:
                        red = "subtract"
                elif isinstance(a, ast.BinOp) and isinstance(a.op, (ast.Sub, ast.Add)) and any(is_name(x) and x.id in params for x in (a.left, a.right)):
                    red = "subtract"
                elif "mid" in src.lower():
                    red = "halve"
                elif isinstance(a, ast.Name) and a.id in params:
                    continue
                elif isinstance(a, ast.BinOp):
                    red = "subtract"
                if red != "unknown":
                    break
            reductions.append(red)
        return {"count": len(calls), "reductions": reductions}

    def function_cost(self, name):
        if name in self._stack:
            return C1   # recursion handled separately: while costing X, a self-call is a memo hit / base step
        if name in self.fn_cost:
            return self.fn_cost[name]
        fn = self.functions[name]
        self._stack.append(name)
        # memo wrapper (`try: _cached() except TypeError: _orig()`): cost = states × per-state work,
        # where states come from the ORIGINAL body's recursive calls (which target this wrapper)
        _wrap_pair = _is_memo_wrapper(fn)
        _impl = None
        if _wrap_pair is not None and _wrap_pair[0] in self.functions:
            _impl = self.functions[_wrap_pair[0]]
        elif _inframe_memo(fn):
            _impl = fn
        if _impl is not None:
            # memoised recursion: O(n^k) distinct states x per-state work. Recursive self-calls inside
            # the memoised body are O(1) (cache hit), so they must be suppressed while costing it.
            _rcalls = [n for n in ast.walk(_impl) if isinstance(n, ast.Call) and isinstance(n.func, ast.Name)
                       and n.func.id in (name, _impl.name)]
            _k = len(_varying_params(_impl, _rcalls)) or 1
            self._stack.append(_impl.name)
            try:
                _work = self.stmts_cost(_impl.body, _impl)
            finally:
                self._stack.pop()
            total = Cx(_k) * _work
            self.fn_notes.setdefault(name, []).append(f"memoized recursion: O(n^{_k}) distinct states x {_work} work each")
            space = Cx(_k)
            self.fn_cost[name] = total
            self.fn_space[name] = space
            self._stack.pop()
            return total
        # body cost excluding recursive calls
        body = self.stmts_cost(fn.body, fn)
        rec = self.recursion_info(fn)
        notes = self.fn_notes.setdefault(name, [])
        space = C1
        if rec:
            a = rec["count"]
            reds = rec["reductions"]
            memo = self.is_memoized(fn)
            halve = all(r == "halve" for r in reds) and reds
            if memo:
                rec_calls = [n for n in ast.walk(fn) if isinstance(n, ast.Call) and is_name(n.func, fn.name)]
                int_args = [a.arg for a in fn.args.args if a.arg in ("n", "num", "m", "k", "x", "size", "count")]
                k = len(_varying_params(fn, rec_calls) or int_args) or 1
                total = Cx(k) * body
                notes.append(f"memoized recursion: O(n^{k}) distinct states × {body} work each")
                space = Cx(k)
            elif halve:
                d = body.p
                logb_a = math.log2(max(a, 1))
                if abs(d - logb_a) < 1e-9:
                    total = Cx(d, body.l + 1)
                elif d > logb_a:
                    total = Cx(d, body.l)
                else:
                    total = Cx(logb_a, body.l)
                notes.append(f"divide & conquer: {a} call(s) on half-size input, {body} work per level (master theorem)")
                space = CLOG if a == 1 else CN
            elif a == 1:
                total = CN * body
                notes.append(f"linear recursion: depth n, {body} work per call")
                space = CN
            elif self._has_loop_recursion(fn):
                total = Cx(fact=True)
                notes.append("recursive call inside a loop over n (factorial growth)")
                space = CN
            else:
                total = Cx(e=a) * Cx(body.p, body.l)
                notes.append(f"{a} recursive calls per invocation, each reducing n by a constant → {a}^n call tree")
                space = CN
        else:
            total = body
        # space heuristics
        for n in ast.walk(fn):
            if isinstance(n, (ast.ListComp, ast.SetComp, ast.DictComp)):
                space = space | Cx(len(n.generators))
            if isinstance(n, ast.Call) and call_name(n) in ("list", "set", "dict", "sorted", "Counter", "defaultdict", "deque"):
                space = space | CN
            if isinstance(n, ast.Call) and call_name(n) in (".append", ".add") and len(enclosing_loops(n)) >= 1:
                space = space | Cx(min(len(enclosing_loops(n)), 2)) if self._is_2d_build(n) else space | CN
        self.fn_cost[name] = total
        self.fn_space[name] = space
        self._stack.pop()
        return total

    def _is_2d_build(self, call):
        return False

    def _has_loop_recursion(self, fn):
        for n in ast.walk(fn):
            if isinstance(n, (ast.For, ast.While)):
                if self._recursive_call_in(n.body, fn.name):
                    return True
        return False

    def analyze(self):
        result = {"functions": [], "overall": None, "overall_space": None, "notes": []}
        overall = C1
        overall_space = C1
        for name in list(self.functions):
            c = self.function_cost(name)
            fn = self.functions[name]
            result["functions"].append({
                "name": name,
                "time": str(c),
                "rank": c.rank(),
                "space": str(self.fn_space.get(name, C1)),
                "params": [a.arg for a in fn.args.args],
                "notes": self.fn_notes.get(name, []),
                "line": fn.lineno,
                "conditional": self._conditional_costs(fn),
            })
            overall = overall | c
            overall_space = overall_space | self.fn_space.get(name, C1)
        top = [s for s in self.tree.body if not isinstance(s, (ast.FunctionDef, ast.ClassDef, ast.Import, ast.ImportFrom))]
        top_cost = self.stmts_cost(top, None)
        result["top_level"] = str(top_cost)
        overall = overall | top_cost
        result["overall"] = str(overall)
        result["overall_rank"] = overall.rank()
        result["overall_space"] = str(overall_space)
        return result


# --------------------------------------------------------------------------
# Program execution / benchmarking
# --------------------------------------------------------------------------
class ExecResult:
    def __init__(self):
        self.ok = True
        self.error = None
        self.stdout = ""
        self.times = []
        self.namespace = None


def run_program(code, repeats=5, budget=1.0, stdin=""):
    res = ExecResult()
    try:
        compiled = compile(code, "<user_code>", "exec")
    except SyntaxError as e:
        res.ok = False
        res.error = f"SyntaxError: {e.msg} (line {e.lineno})"
        return res
    total = 0.0
    for i in range(repeats):
        ns = {"__name__": "__main__"}
        buf = io.StringIO()
        old = sys.stdout
        old_in = sys.stdin
        sys.stdout = buf
        sys.stdin = io.StringIO(stdin)
        t0 = time.perf_counter()
        try:
            exec(compiled, ns)
            dt = time.perf_counter() - t0
        except RecursionError:
            dt = time.perf_counter() - t0
            res.ok = False
            res.error = f"RecursionError: maximum recursion depth exceeded (sandbox limit ≈ {sys.getrecursionlimit()} frames)"
        except BaseException as e:  # noqa
            dt = time.perf_counter() - t0
            res.ok = False
            res.error = f"{type(e).__name__}: {e}"
        finally:
            sys.stdout = old
            sys.stdin = old_in
        if i == 0:
            res.stdout = buf.getvalue()
            res.namespace = ns
        res.times.append(dt)
        total += dt
        if not res.ok or total > budget:
            break
    return res


MODELS = [
    ("O(1)", lambda n: 1.0, 0),
    ("O(log n)", lambda n: math.log2(n + 1), 1),
    ("O(√n)", lambda n: math.sqrt(n), 5),
    ("O(n)", lambda n: n, 10),
    ("O(n log n)", lambda n: n * math.log2(n + 1), 11),
    ("O(n²)", lambda n: n * n, 20),
    ("O(n³)", lambda n: n ** 3, 30),
    ("O(2^n)", lambda n: 2.0 ** min(n, 1000), 52),
]


def fit_growth(points):
    """Robust empirical growth estimation.

    1. Compute the log-log slope between consecutive measurements.
    2. Take the median slope (robust to single outliers such as cache-miss cliffs).
    3. Compare against the slope each canonical model would produce over the
       same sizes and pick the closest one, with a slight preference for
       simpler models (Occam).  Also reports R² of a least-squares fit.
    """
    pts = sorted((n, t) for n, t in points if t > 0 and n > 0)
    if len(pts) < 3:
        return None
    nmax = pts[-1][0]

    def slopes(fn_vals):
        out = []
        for (n1, v1), (n2, v2) in zip(fn_vals, fn_vals[1:]):
            if n2 > n1 and v1 > 0 and v2 > 0:
                out.append(math.log(v2 / v1) / math.log(n2 / n1))
        return out

    def median(xs):
        xs = sorted(xs)
        k = len(xs)
        return xs[k // 2] if k % 2 else 0.5 * (xs[k // 2 - 1] + xs[k // 2])

    meas = slopes(pts)
    if not meas:
        return None
    m_slope = median(meas)
    # trimmed mean of the upper half of the series (less start-up overhead)
    tail = meas[len(meas) // 2:] if len(meas) >= 4 else meas
    t_slope = median(tail)
    use_slope = 0.5 * (m_slope + t_slope)

    details = []
    best = None
    tmax = pts[-1][1]
    for label, g, rank in MODELS:
        if label == "O(2^n)" and nmax > 64:
            continue
        try:
            gv = [(n, g(n)) for n, _ in pts]
        except OverflowError:
            continue
        ms = slopes(gv)
        if not ms:
            continue
        model_slope = median(ms)
        dist = abs(model_slope - use_slope)
        # least squares (with intercept) for an R² figure
        gmax = max(v for _, v in gv) or 1.0
        gs = [v / gmax for _, v in gv]
        ts = [t / tmax for _, t in pts]
        k = len(pts)
        sg = sum(gs); st = sum(ts); sgg = sum(x * x for x in gs); sgt = sum(x * y for x, y in zip(gs, ts))
        den = k * sgg - sg * sg
        if abs(den) < 1e-12:
            c, b = 0.0, st / k
        else:
            c = (k * sgt - sg * st) / den
            b = (st - c * sg) / k
        resid = sum((t - (c * x + b)) ** 2 for x, t in zip(gs, ts))
        tot = sum((t - st / k) ** 2 for t in ts) or 1e-12
        r2 = max(0.0, 1 - resid / tot)
        score = dist + 0.004 * rank
        details.append({"model": label, "r2": round(r2, 4), "rank": rank, "score": round(score, 4), "model_slope": round(model_slope, 2)})
        if best is None or score < best["score"]:
            best = details[-1]
    if best is None:
        return None
    return {"label": best["model"], "r2": best["r2"], "rank": best["rank"], "slope": round(use_slope, 2),
            "candidates": sorted(details, key=lambda d: d["score"])[:4]}


def time_call(fn, args_factory, min_time=0.012, max_reps=2000, batches=3):
    """returns best per-call time in seconds (min over batches)."""
    def prep():
        a = args_factory()
        if hasattr(fn, "cache_clear"):
            fn.cache_clear()
        return a
    a = prep()
    t0 = time.perf_counter()
    fn(*a)
    dt = time.perf_counter() - t0
    if dt >= min_time:
        best = dt
        extra = 2 if dt < 0.1 else (1 if dt < 0.3 else 0)
        if extra:  # slow call: min of several single-call samples instead of one noisy sample
            for _ in range(extra):
                a2 = prep()
                t1 = time.perf_counter()
                fn(*a2)
                best = min(best, time.perf_counter() - t1)
        return best
    # does the function mutate its arguments? (if not we can reuse one input set)
    try:
        mutates = _normalize(a) != _normalize(args_factory())
    except Exception:
        mutates = True
    reps = min(max_reps, max(3, int(min_time / max(dt, 1e-7))))
    if mutates:
        size = _approx_size(a)
        reps = max(2, min(reps, int(4_000_000 // max(size, 1))))
    samples = []
    clear = hasattr(fn, "cache_clear")
    gc.collect()
    gc_was = gc.isenabled()
    gc.disable()
    try:
        return _timed_batches(fn, prep, reps, mutates, clear, samples, batches)
    finally:
        if gc_was:
            gc.enable()


def _timed_batches(fn, prep, reps, mutates, clear, samples, batches=3):
    a = None
    for _ in range(batches):
        argsets = [prep() for _ in range(reps)] if mutates else None
        if not mutates:
            a = prep()
        t0 = time.perf_counter()
        if mutates:
            for a in argsets:
                if clear:
                    fn.cache_clear()
                fn(*a)
        elif clear:
            for _ in range(reps):
                fn.cache_clear()
                fn(*a)
        else:
            for _ in range(reps):
                fn(*a)
        dt = (time.perf_counter() - t0) / reps
        samples.append(dt)
        if sum(samples) * reps > 0.4:
            break
    return min(samples)


def _approx_size(args):
    total = 1
    for a in args:
        try:
            if isinstance(a, (list, str, dict, set, tuple)):
                total += len(a)
                if isinstance(a, list) and a and isinstance(a[0], list):
                    total += len(a) * len(a[0])
        except Exception:
            pass
    return total



class _Deadline(BaseException):
    pass


def with_deadline(fn, seconds):
    """Wrap fn so a single call is aborted after `seconds` (works for pure-Python loops; used only for probing)."""
    def wrapper(*a, **k):
        end = time.perf_counter() + seconds
        cnt = [0]

        def tracer(frame, event, arg):
            cnt[0] += 1
            if (cnt[0] & 511) == 0 and time.perf_counter() > end:
                raise _Deadline()
            return tracer
        old = sys.gettrace()
        sys.settrace(tracer)
        try:
            return fn(*a, **k)
        finally:
            sys.settrace(old)
    wrapper.__wrapped__ = fn
    return wrapper


def choose_adversarial_strategy(fn, tags, exp_like=False):
    """Adversarial input search: try several input shapes at a calibration size and
    keep the combination that makes the function work hardest (≈ worst case).
    The chosen strategy is reused for the optimized code so both see identical inputs."""
    has_collection = any(t in ("list", "str", "matrix", "dict", "set", "strlist") for t in tags)
    has_int = any(t in ("int", "float") for t in tags)
    has_list = "list" in tags
    list_opts = list(LIST_STRATEGIES) if has_list else ["unique"]
    sec_opts = list(SECONDARY_STRATEGIES) if (has_collection and has_int) else ["half"]
    prim_opts = list(PRIMARY_INT_STRATEGIES) if (has_int and not has_collection) else ["n"]
    n = 12 if exp_like else 64
    best, best_t = None, -1.0
    scored = []
    deadline = time.perf_counter() + 0.25
    for lo in list_opts:
        for so in sec_opts:
            for po in prim_opts:
                if time.perf_counter() > deadline:
                    break
                set_strategy(list=lo, secondary=so, primary=po)
                try:
                    with_deadline(fn, 0.4)(*make_args(tags, n, 1000 + n))   # probe: skip inputs that explode
                    fn(*make_args(tags, n, 1000 + n))                      # warm-up so the first candidate is not penalised
                    t = time_call(fn, lambda: make_args(tags, n, 1000 + n), min_time=0.003, max_reps=150)
                except (Exception, _Deadline):
                    continue
                scored.append((t, (lo, so, po)))
                if t > best_t * 1.05:
                    best, best_t = (lo, so, po), t
    # Small sizes are dominated by per-call overhead (e.g. a window of size 1 makes many cheap calls).
    # Re-time the top candidates at a larger size, where the asymptotic work dominates, and keep the slowest there.
    if not exp_like and len(scored) > 1:
        n2 = 128                      # enough to separate shapes; 256 made cubic inputs cost 0.4s each
        top = [c for _, c in sorted(scored, key=lambda x: -x[0])[:2]]
        best2, best2_t = None, -1.0
        stop2 = time.perf_counter() + 0.25
        for cand in top:
            if time.perf_counter() > stop2:
                break
            set_strategy(list=cand[0], secondary=cand[1], primary=cand[2])
            try:
                with_deadline(fn, 0.25)(*make_args(tags, n2, 1000 + n2))
                t2 = time_call(fn, lambda: make_args(tags, n2, 1000 + n2), min_time=0.003, max_reps=50)
            except (Exception, _Deadline):
                continue
            if t2 > best2_t:
                best2, best2_t = cand, t2
        if best2 is not None:
            best = best2
    if best is None:
        best = ("reversed", "big", "n")
    set_strategy(list=best[0], secondary=best[1], primary=best[2])
    return {"list": best[0], "secondary": best[1], "primary": best[2], "complete": time.perf_counter() <= deadline}


def growth_benchmark(ns, fn_name, tags, static_cx, budget=1.2, sizes=None, label="original", start_points=None):
    """Benchmark function at increasing sizes; returns list of {n, t_ms}."""
    fn = ns.get(fn_name)
    if not callable(fn):
        return [], "function not found in namespace"
    tags = probe_signature_prioritized(fn, tags)
    points = list(start_points) if start_points else []
    err = None
    start = time.perf_counter()
    exp_like = static_cx is not None and (static_cx.e or static_cx.fact)
    has_collection = any(t in ("list", "str", "matrix", "dict", "set", "strlist") for t in tags)
    max_n = 60_000 if has_collection else 5_000_000
    if sizes is None:
        n = 4 if exp_like else 32
        planned = None
    else:
        planned = list(sizes)
    idx = 0
    last_t = None
    last_n = None
    guard = 0
    while True:
        guard += 1
        if guard > 40:
            break
        if planned is not None:
            if idx >= len(planned):
                # continue growing after planned sizes if budget allows
                if time.perf_counter() - start > budget * 0.5 or not points:
                    break
                n = _next_size(points, exp_like)
                if n is None or n > max_n:
                    break
            else:
                n = planned[idx]
                idx += 1
        elif points:
            n = _next_size(points, exp_like)
            if n is None or n > max_n:
                break
        # predict cost of this size from previous points
        if len(points) >= 2:
            (n1, t1), (n2, t2) = points[-2], points[-1]
            if t1 > 0 and t2 > t1 and n2 > n1:
                if exp_like or t2 / t1 > 6:
                    # exponential model: ratio per +1
                    r = (t2 / t1) ** (1.0 / max(n2 - n1, 1))
                    pred = t2 * r ** (n - n2)
                else:
                    slope = math.log(t2 / t1) / math.log(n2 / n1)
                    pred = t2 * (n / n2) ** slope
                if pred > 0.15 and planned is None:
                    break          # a point is only worth running if it stays under ~0.3s
                if pred > 0.4:
                    break
        def factory(n=n):
            return make_args(tags, n, 1000 + n)
        try:
            t = time_call(fn, factory)
        except (TypeError, AttributeError, ValueError) as te:
            repaired = probe_signature_prioritized(fn, tags)
            if repaired != tags:
                tags = repaired
                _progress("bench", f"[{label}] Parameter types adapted to {tags}")
                points = []
                idx = 0
                continue
            err = f"{type(te).__name__}: {te} (n={n})"
            break
        except RecursionError:
            err = f"RecursionError at n={n}"
            break
        except Exception as e:  # noqa
            err = f"{type(e).__name__}: {e} (n={n})"
            break
        points.append((n, t))
        _progress("bench", f"[{label}] {fn_name}(n={n}) → {t*1000:.3f} ms", {"which": label, "n": n, "t_ms": t * 1000})
        last_t, last_n = t, n
        if time.perf_counter() - start > budget or t > 0.12:
            if planned is None or idx >= len(planned):
                break
    return points, err


def _next_size(points, exp_like):
    n, t = points[-1]
    if exp_like:
        return n + max(1, n // 4) if t > 0.002 else n + max(2, n // 2)
    if len(points) >= 2:
        (n1, t1), (n2, t2) = points[-2], points[-1]
        if t1 > 0 and t2 / t1 > 6:
            return n2 + max(1, n2 // 3)
    return n * 2


# --------------------------------------------------------------------------
# Differential testing
# --------------------------------------------------------------------------
def _normalize(v):
    try:
        if isinstance(v, float) and math.isnan(v):
            return "nan"
        if isinstance(v, (set, frozenset)):
            return ("set", sorted(map(repr, v)))
        if isinstance(v, dict):
            return ("dict", sorted((repr(k), _normalize(x)) for k, x in v.items()))
        if isinstance(v, (list, tuple)):
            return (type(v).__name__, [_normalize(x) for x in v])
        if hasattr(v, "__iter__") and not isinstance(v, (str, bytes)):
            return ("iter", [_normalize(x) for x in list(v)])
        if isinstance(v, float):
            return ("float", round(v, 9))
        return v
    except Exception:
        return repr(v)




def _short(v):
    s = repr(v)
    return s if len(s) < 60 else s[:57] + "..."


# ==========================================================================
# v2 correctness + honest measurement layer
# ==========================================================================
import struct

NONDET_MODULES = {"random", "time", "uuid", "secrets", "os"}
NONDET_CALLS = {"input", "open", "id", "urandom", "random", "randint", "randrange", "choice", "shuffle", "time", "uuid1", "uuid4", "token_hex"}
PURE_BUILTINS = {"len", "abs", "min", "max", "int", "str", "range", "float", "bool", "ord", "chr", "round", "sorted", "sum"}
HASH_RULES = {"membership", "shadow_set", "counter", "pairs", "nested_eq", "count_diff"}
HASHSAFE = "all(isinstance(v, (int, str, bytes, bool)) or (isinstance(v, float) and v == v) for v in {var})"
INTSAFE = "all(type(v) is int for v in {var})"
LISTLIKE = "isinstance({var}, (list, tuple, str))"   # set()/Counter()/.count() semantics the rules rely on




def _globals_snapshot(ns):
    """Module globals after a call.  Cache cells owned by the memo rewrite are excluded: a memo
    dict filling in is the intended side effect of that rewrite, not a behavioural difference.
    Every other global is compared, so rules that leak state are still caught."""
    out = {}
    for k, v in list(ns.items()):
        if k.startswith("__") or k in ("js_progress",):
            continue
        if k.endswith("_memo") or k.endswith("_miss") or k.endswith("_cached") or "cache" in k.lower():
            continue
        if isinstance(v, (types.FunctionType, types.ModuleType, type)):
            continue
        try:
            out[k] = ("v", repr(v))
        except Exception:
            out[k] = ("?", type(v).__name__)
    return out








def _nan_pool():
    return float("nan")


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
    # graphs are generated before their node parameters so `adj[s]` is a valid key on every test
    graph_by_arg = {}
    for i, t in enumerate(tags):
        if t == "dict" and (shapes or {}).get(SHAPE_KEY % i) in ("dictlists", "pairsdict"):
            graph_by_arg[i] = make_graph(max(1, n), rng, dense=(test_idx % 3 == 0))
    for i, t in enumerate(tags):
        shape = (shapes or {}).get(SHAPE_KEY % i)
        if shape == "node" and graph is not None:
            out.append(list(graph)[test_idx % len(graph)])
            continue
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
            v = vals[test_idx % len(vals)]
            if int_cap is not None and isinstance(v, int) and not isinstance(v, bool) and v > int_cap:
                # the cap MEANS it: a value known to be too slow for this function is replaced by an
                # in-cap value (deterministic rotation), never emitted again
                v = test_idx % (int_cap + 1)
            out.append(v)
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
                graph = graph_by_arg.get(i) or make_graph(max(1, n), rng, dense=(test_idx % 3 == 0))
                graph_by_arg[i] = graph
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
    """{SHAPE_KEY % index: shape} for both generators (differential tests AND benchmarks).

    Shapes come from structure, not names:
      * `x[i][j]`            -> matrix
      * `for l, r in xs`      -> pairs
      * `adj[u].append(...)`  -> dictlists (graph: node -> in-range neighbours)
      * `adj[s]` / element flow -> node (a scalar that must be one of the graph's keys)
    Names are never consulted for shapes."""
    hints = shape_hints(fn)
    params = list(fn.args.args)
    out = {SHAPE_KEY % i: hints.get(a.arg) for i, a in enumerate(params)}
    # a dict-typed parameter indexed by a parameter (or with in-range neighbour lists) is a graph
    for i, a in enumerate(params):
        if out[SHAPE_KEY % i] is None and _usage_tag(fn, a.arg) == "dict" and (tags is None or tags[i] == "dict"):
            out[SHAPE_KEY % i] = "dictlists"
    graph_params = [a.arg for i, a in enumerate(params) if out[SHAPE_KEY % i] == "dictlists"]
    if graph_params:
        reachable = set()
        for node in ast.walk(fn):
            if isinstance(node, ast.Subscript) and isinstance(node.value, ast.Name) and node.value.id in graph_params:
                sl = node.slice
                for e in (list(sl.elts) if isinstance(sl, (ast.Tuple, ast.List)) else ([sl] if isinstance(sl, ast.Name) else [])):
                    if isinstance(e, ast.Name):
                        reachable.add(e.id)

        # `u = q.pop(0)` (u came from q) and `q = [s]` (q came from s): a reachable name makes
        # the names its own assignment reads reachable. Only element-preserving forms propagate.
        def add_from_value(value, hop):
            added = False
            for n in ast.walk(value):
                if isinstance(n, ast.Name) and n.id not in reachable and n.id != hop:
                    reachable.add(n.id)
                    added = True
            return added

        for _ in range(8):
            grew = False
            for node in ast.walk(fn):
                if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
                    tgt = node.targets[0].id
                    if tgt in reachable and add_from_value(node.value, tgt):
                        grew = True
                elif isinstance(node, ast.For):
                    it = node.iter
                    it_is_graph = isinstance(it, ast.Subscript) and isinstance(it.value, ast.Name) and it.value.id in graph_params
                    if it_is_graph or any(isinstance(n, ast.Name) and n.id in reachable for n in ast.walk(it)):
                        for t in ast.walk(node.target):
                            if isinstance(t, ast.Name) and t.id not in reachable:
                                reachable.add(t.id)
                                grew = True
                elif isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr in ("append", "add") \
                        and isinstance(node.func.value, ast.Name) and node.func.value.id in reachable:
                    for e in node.args:
                        if isinstance(e, ast.Name) and e.id not in reachable:
                            reachable.add(e.id)
                            grew = True
            if not grew:
                break
        for i, a in enumerate(params):
            if a.arg in reachable and out[SHAPE_KEY % i] is None:
                out[SHAPE_KEY % i] = "node"
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






def static_nondeterminism(scope):
    for n in ast.walk(scope):
        if isinstance(n, ast.Import):
            for a in n.names:
                if a.name.split(".")[0] in NONDET_MODULES:
                    return a.name
        if isinstance(n, ast.ImportFrom) and n.module and n.module.split(".")[0] in NONDET_MODULES:
            return n.module
        if isinstance(n, ast.Call):
            fn = n.func
            if isinstance(fn, ast.Name) and fn.id in NONDET_CALLS:
                return fn.id + "()"
            if isinstance(fn, ast.Attribute) and fn.attr in NONDET_CALLS:
                return "." + fn.attr + "()"
            if isinstance(fn, ast.Attribute) and isinstance(fn.value, ast.Name) and fn.value.id in NONDET_MODULES:
                return f"{fn.value.id}.{fn.attr}"
    return None


def purity_problem(fn, memo=False, tags=None):
    """Reason the function is not safe to rewrite (None if pure)."""
    for n in ast.walk(fn):
        if isinstance(n, (ast.Global, ast.Nonlocal)):
            return "writes global"
        if isinstance(n, ast.Call):
            if isinstance(n.func, ast.Name) and n.func.id in ("print", "input", "open", "exec", "eval", "compile", "id"):
                return f"calls {n.func.id}()"
            if isinstance(n.func, ast.Attribute) and n.func.attr in ("write", "writelines", "read", "readline", "flush"):
                return f"does I/O ({n.func.attr})"
            nd = static_nondeterminism(ast.Module(body=[n], type_ignores=[]))
            if nd:
                return f"calls non-deterministic {nd}"
    for n in ast.walk(fn):
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == "random":
            return "calls random()"
    if memo:
        # unhashable evidence (structural or inferred-type), never parameter NAME guessing:
        # an int named `a` must memoize; a list named `x` must not.
        tagmap = {}
        if tags:
            for a, t in zip(fn.args.args, tags):
                tagmap[a.arg] = t
        for a in fn.args.args:
            if tagmap.get(a.arg) in ("list", "matrix", "dict", "set", "strlist", "dictlists", "pairsdict"):
                return f"unhashable arg {a.arg}"
            if any(isinstance(n, ast.Subscript) and isinstance(n.value, ast.Name) and n.value.id == a.arg for n in ast.walk(fn)):
                return f"unhashable arg {a.arg}"
            if any(isinstance(n, ast.For) and isinstance(n.iter, ast.Name) and n.iter.id == a.arg for n in ast.walk(fn)):
                return f"unhashable arg {a.arg}"
    return None


# ---- strict differential testing ----------------------------------------------
def _run_isolated(f, args):
    """call f(*args) with stdout captured; never raises"""
    buf = io.StringIO()
    old = sys.stdout
    sys.stdout = buf
    try:
        return ("ok", f(*args)), buf.getvalue()
    except _Deadline:
        raise                      # a timed-out probe is neither a result nor an exception of the user's code
    except BaseException as e:  # noqa
        return ("exc", type(e).__name__), buf.getvalue()
    finally:
        sys.stdout = old


def differential_test(orig_code, new_code, fn_name, tags, n_tests=120, int_cap=None, _full=False,
                      budget=4.0, slow=0.01, hints=None, source_tree=None, min_valid=40, stop_at=100, per_call=0.75):
    """Strict randomised differential test of `fn_name`: original vs candidate.

    valid  = BOTH versions returned normally and are strictly equal (return value, arguments after the
             call, stdout, module globals).  ONLY these runs count toward the evidence threshold.
    exc    = both raised the SAME exception type (parity kept; does NOT count as evidence).
    A candidate is kept only with >= min_valid normal runs, else it is "inconclusive" and not applied.
    Stops after stop_at normal runs (or the time budget)."""
    st = {"ok": False, "run": 0, "valid": 0, "exc": 0, "msg": "", "capped": False, "budget_hit": False,
          "skipped": None, "inconclusive": False}
    na = load_namespace(orig_code, "__diff_a__", full=_full)
    nb = load_namespace(new_code, "__diff_b__", full=_full)
    if na is None or nb is None:
        st["msg"] = "failed to load module"
        st["inconclusive"] = True
        return st
    fa, fb = na.get(fn_name), nb.get(fn_name)
    if not callable(fa) or not callable(fb):
        st["msg"] = "function missing"
        st["inconclusive"] = True
        return st
    tags = probe_signature_prioritized(fa, tags)
    try:
        tree_a = source_tree if source_tree is not None else set_parents(ast.parse(orig_code))
        fn_a = next(n for n in ast.walk(tree_a) if isinstance(n, ast.FunctionDef) and n.name == fn_name)
        shapes = shape_map(fn_a, tags)
    except Exception:
        shapes = {}
    for f in (fa, fb):
        if hasattr(f, "cache_clear"):
            f.cache_clear()
    t_start = time.perf_counter()
    best_ok = 0   # largest int input that completed quickly: timeouts shrink the cap toward this
    for i in range(n_tests * 3):
        if st["valid"] >= stop_at or time.perf_counter() - t_start > budget:
            if st["valid"] < stop_at:
                st["budget_hit"] = True
            break
        args = make_small_args(tags, 991 + i * 17, test_idx=i, int_cap=int_cap, hints=hints, shapes=shapes, fn_name=fn_name)
        a1, a2 = copy.deepcopy(args), copy.deepcopy(args)
        g0a, g0b = _globals_snapshot(na), _globals_snapshot(nb)
        t_call = time.perf_counter()
        try:
            (ka, ra), outa = _run_isolated(with_deadline(fa, per_call), a1)
        except _Deadline:
            # the original itself is too slow on this input: drop the cap to the largest size known
            # to complete quickly (geometric shrink, not -1: 2**64 - 1 is still unusable) and skip it
            int_cap = max(1, best_ok) if int_cap is None else min(int_cap, max(1, best_ok, 8))
            st["capped"] = True
            continue
        dt = time.perf_counter() - t_call
        ints = [v for v in args if type(v) is int]
        if dt <= slow and ints:
            best_ok = max(best_ok, max(ints))
        if dt > slow and ints:
            cap = max(1, max(ints) - 1)
            int_cap = cap if int_cap is None else min(int_cap, cap)
            st["capped"] = True
        for f in (fa, fb):
            if hasattr(f, "cache_clear"):
                f.cache_clear()
        try:
            (kb, rb), outb = _run_isolated(with_deadline(fb, per_call), a2)
        except _Deadline:
            st["msg"] = f"optimized version exceeded {per_call}s on {_short(args)} where the original finished"
            return st
        st["run"] += 1
        if ka == "exc" or kb == "exc":
            if ka != kb:
                which = "original raised %s but optimized returned" % ra if ka == "exc" else "optimized raised %s where original returned" % rb
                st["msg"] = f"{which} on {_short(args)}"
                return st
            if ra != rb:
                st["msg"] = f"exception type changed on {_short(args)}: {ra} vs {rb}"
                return st
            if outa != outb:
                st["msg"] = f"stdout differs on a run where both raise ({ra}) on {_short(args)}"
                return st
            if not strict_equal(a1, a2):
                st["msg"] = f"argument mutation differs on a run where both raise ({ra}) on {_short(args)}"
                return st
            st["exc"] += 1
            continue
        if not _strict_returns(ra, rb):
            st["msg"] = f"return mismatch on {_short(args)}: {_short(ra)} vs {_short(rb)}"
            return st
        if outa != outb:
            st["msg"] = f"stdout differs on {_short(args)}"
            return st
        if not strict_equal(a1, a2):
            st["msg"] = f"argument mutation differs on {_short(args)}"
            return st
        if _globals_snapshot(na) != g0a or _globals_snapshot(nb) != g0b:
            st["msg"] = f"module globals changed after the call on {_short(args)}"
            return st
        st["valid"] += 1
    if st["valid"] < min_valid:
        st["msg"] = f"inconclusive: only {st['valid']} normal runs (need {min_valid}); {st['exc']} both-raised runs"
        st["skipped"] = st["msg"]
        st["inconclusive"] = True
        return st
    st["ok"] = True
    st["msg"] = f"{st['valid']} normal runs, {st['exc']} both-raised"
    return st


# ---- honest benchmark protocol -------------------------------------------------
def _mad(xs):
    if not xs:
        return 0.0
    m = _median(xs)
    return _median([abs(x - m) for x in xs])


def _clear_caches(ns):
    """clear lru_cache on the benchmarked function and on every cached callable in its namespace"""
    for v in list(ns.values()):
        if hasattr(v, "cache_clear"):
            try:
                v.cache_clear()
            except Exception:
                pass


def _timed_round(f, ns, argsets, min_sample=0.004, max_reps=4000):
    """One timed sample.  Every call gets a fresh deepcopy of its arguments (made BEFORE the timer starts,
    so a function that mutates its input sees identical input each time) and an empty cache."""
    fresh, reps = [], 0
    while reps < max_reps:
        batch = [copy.deepcopy(a) for a in argsets]
        t0 = time.perf_counter()
        _clear_caches(ns)
        for a in batch:
            f(*a)
        dt = time.perf_counter() - t0
        fresh.append(dt)
        reps += len(batch)
        if sum(fresh) >= min_sample:
            break
    return sum(fresh) / reps


def bench_pair(fa, fb, argsets, rounds=15, warm=3, min_sample=0.004, ns_a=None, ns_b=None, budget=None):
    """15 rounds, random A/B order each round, 3 discarded warm-ups, median of per-round ratios + MAD.
    Caches are cleared and arguments re-copied for every timed call, on both sides."""
    for _ in range(warm):
        fa(*copy.deepcopy(argsets[0]))
        fb(*copy.deepcopy(argsets[0]))
    _clear_caches(ns_a or {})
    _clear_caches(ns_b or {})
    ta, tb = [], []
    t0_bench = time.perf_counter()
    target_rounds = rounds
    i = 0
    while i < target_rounds:
        i += 1
        order = [("a", fa, ns_a), ("b", fb, ns_b)]
        random.shuffle(order)
        pair_t = 0.0
        for tag, f, ns in order:
            t0_pair = time.perf_counter()
            t = _timed_round(f, ns or {}, argsets, min_sample)
            pair_t += time.perf_counter() - t0_pair
            (ta if tag == "a" else tb).append(t)
        if budget is not None and len(ta) == 1 and pair_t > 0:
            # slow function: fewer, longer rounds still give a stable median (>=3 A/B pairs)
            target_rounds = max(3, min(rounds, int(budget / pair_t)))
        if budget is not None and time.perf_counter() - t0_bench > budget and len(ta) >= 3:
            break
    ratios = [a / b for a, b in zip(ta, tb) if b]
    ratio = _median(ratios) if ratios else None
    spread = (_mad(ratios) / ratio) if ratio else 0.0
    return {"a": _median(ta), "b": _median(tb), "ratio": ratio, "spread": spread,
            "a_spread": (_mad(ta) / _median(ta)) if ta else 0, "b_spread": (_mad(tb) / _median(tb)) if tb else 0,
            "rounds": rounds}


def bench_changed(orig_src, new_src, changed, fn_types, hints, sizes_by_fn, budget=1.5):
    """One honest measurement per CHANGED function, with a per-function time budget.
    `a` / `b` are real per-call seconds; the A/A control times the original against a second,
    freshly compiled copy of itself.  A function that could not be measured records WHY:
    rows[name] = {"error": "no valid inputs" | "time budget" | "measurement failed: ..." }."""
    rows = {}
    if not changed:
        return rows
    na = load_namespace(orig_src, "__bench_a__")
    nb = load_namespace(new_src, "__bench_b__")
    naa = load_namespace(orig_src, "__bench_aa__")
    if na is None or nb is None or naa is None:
        for name in changed:
            rows[name] = {"error": "no valid inputs (module failed to load)"}
        return rows
    gc.disable()
    try:
        for name in changed:
            t_fn = time.perf_counter()
            fa, fb, fa2 = na.get(name), nb.get(name), naa.get(name)
            if not (callable(fa) and callable(fb) and callable(fa2)):
                rows[name] = {"error": "no valid inputs (function missing from a namespace)"}
                continue
            tags = probe_signature_prioritized(fa, fn_types.get(name, []))
            try:
                _t = set_parents(ast.parse(defs_only_source(orig_src)))
                _fn = next(x for x in ast.walk(_t) if isinstance(x, ast.FunctionDef) and x.name == name)
                _shapes = shape_map(_fn, tags)     # the same shapes the differential tests use
            except Exception:
                _shapes = {}
            sizes = sorted({int(x) for x in (sizes_by_fn.get(name) or [64, 256]) if 0 < int(x) <= 4096}) or [64]
            size = None
            for cand in sizes:
                if time.perf_counter() - t_fn > budget * 0.6:
                    break
                try:
                    with_deadline(fa, 0.4)(*copy.deepcopy(make_args(tags, cand, 4242, _shapes)))
                    size = cand
                    if cand >= 128:
                        break
                except (Exception, _Deadline):
                    continue
            if size is None:
                rows[name] = {"error": "no valid inputs (every generated input raised)"}
                continue
            if time.perf_counter() - t_fn > budget * 0.75:
                rows[name] = {"error": "time budget"}
                continue
            try:
                argsets = [make_args(tags, size, 1000 + size + j, _shapes) for j in range(4)]
                left = max(0.3, budget - (time.perf_counter() - t_fn))
                row = bench_pair(fa, fb, argsets, rounds=15, ns_a=na, ns_b=nb, budget=left * 0.6)
                if time.perf_counter() - t_fn > budget:
                    rows[name] = {"error": "time budget"}
                    continue
                left = max(0.2, budget - (time.perf_counter() - t_fn))
                aa = bench_pair(fa, fa2, argsets, rounds=7, ns_a=na, ns_b=naa, budget=left * 0.7)
                rows[name] = {"n": size, **row, "aa": aa, "aa_dev": abs((aa.get("ratio") or 1.0) - 1.0)}
            except _Deadline:
                rows[name] = {"error": "time budget"}
            except Exception as e:  # noqa
                rows[name] = {"error": f"measurement failed: {type(e).__name__}"}
    finally:
        gc.enable()
    return rows


def verdict_for(row):
    """Claim a speed-up for THIS function only if
        ratio >= max(1.15, 1 + 3 * spread, 1 + 2 * |A/A - 1|)
    where `spread` is the run-to-run MAD and the A/A term is that function's own control deviation.
    Returns (verdict, spread, claimed, threshold)."""
    ratio = row.get("ratio")
    spread = max(row.get("spread", 0.0), 0.0)
    aa_dev = abs(row.get("aa_dev") or 0.0)
    if not ratio:
        return "no measurable change", spread, False, None
    floor = max(1.15, 1 + 3 * spread, 1 + 2 * aa_dev)
    if ratio >= floor:
        return f"faster at n={row['n']}", spread, True, floor
    if ratio <= 1 / floor:
        return f"slower at n={row['n']}", spread, False, floor
    return f"no measurable change (needs {floor:.2f}x)", spread, False, floor


def run_program_stdin(code, stdin="", repeats=1):
    res = ExecResult()
    try:
        compiled = compile(code, "<user_code>", "exec")
    except SyntaxError as e:
        res.ok = False
        res.error = f"SyntaxError: {e.msg} (line {e.lineno})"
        return res
    for i in range(repeats):
        ns = {"__name__": "__main__"}
        buf, inbuf = io.StringIO(), io.StringIO(stdin)
        old_out, old_in = sys.stdout, sys.stdin
        sys.stdout, sys.stdin = buf, inbuf
        t0 = time.perf_counter()
        try:
            exec(compiled, ns)
            dt = time.perf_counter() - t0
        except BaseException as e:  # noqa
            dt = time.perf_counter() - t0
            res.ok = False
            res.error = f"{type(e).__name__}: {e}"
        finally:
            sys.stdout, sys.stdin = old_out, old_in
        if i == 0:
            res.stdout = buf.getvalue()
            res.namespace = ns
        res.times.append(dt)
    return res


def compare_programs(orig_src, new_src, stdin="", rounds=5):
    """Alternate order, at least 5 runs, median. Never compares if the original fails."""
    ra = run_program_stdin(orig_src, stdin, 1)
    if not ra.ok:
        return {"status": "original_failed", "message": f"original failed, no comparison ({ra.error})",
                "orig_ms": None, "opt_ms": None, "median_ms": None, "shown": False}
    rb = run_program_stdin(new_src, stdin, 1)
    ta, tb = [], []
    for r in range(rounds):
        order = ["a", "b"] if r % 2 == 0 else ["b", "a"]
        for which in order:
            if which == "a":
                out = run_program_stdin(orig_src, stdin, 1)
                if not out.ok:
                    return {"status": "original_failed", "message": f"original failed, no comparison ({out.error})",
                            "orig_ms": None, "opt_ms": None, "median_ms": None, "shown": False}
                ta.append(out.times[0])
            else:
                out = run_program_stdin(new_src, stdin, 1)
                if not out.ok:
                    return {"status": "optimized_failed", "message": f"optimized failed ({out.error})",
                            "orig_ms": _median(ta) * 1000 if ta else None, "opt_ms": None, "median_ms": None, "shown": False}
                tb.append(out.times[0])
    ma, mb = _median(ta), _median(tb)
    shown = ma >= 0.0005 and mb >= 0.0005
    return {"status": "ok" if ra.stdout == rb.stdout else "stdout_differs",
            "message": "stdout identical" if ra.stdout == rb.stdout else "stdout differs",
            "orig_ms": ma * 1000, "opt_ms": mb * 1000,
            "ratio": (ma / mb) if mb else None, "median_ms": ma * 1000, "shown": shown,
            "stdout_match": ra.stdout == rb.stdout, "stdin": stdin[:200]}


# --------------------------------------------------------------------------
# Optimizer transformations
# --------------------------------------------------------------------------
class Change:
    def __init__(self, title, detail, fn, before, after, kind="complexity"):
        self.title = title
        self.detail = detail
        self.fn = fn
        self.before = before
        self.after = after
        self.kind = kind  # complexity | constant | advice
        self.status = "pending"
        self.message = ""
        self.rule = None
        self.verification = None  # {"method", "inputs", "valid", "exception_parity"}
        self.ab = None            # {"ratio", "noise", "n"} from the regression guard
        self.portable = False
        self.portable_note = None

    def to_json(self):
        return {"title": self.title, "detail": self.detail, "function": self.fn,
                "before": self.before, "after": self.after, "kind": self.kind,
                "status": self.status, "message": self.message, "rule": self.rule,
                "verification": self.verification, "ab": self.ab,
                "portable": self.portable, "portable_note": self.portable_note}


def _enclosing_function(node):
    cur = getattr(node, "_parent", None)
    while cur is not None:
        if isinstance(cur, ast.FunctionDef):
            return cur
        cur = getattr(cur, "_parent", None)
    return None


def _parent_stmt_list(stmt):
    """(container_list, index) where stmt lives"""
    parent = getattr(stmt, "_parent", None)
    if parent is None:
        return None, -1
    for _, lst in iter_stmt_lists(parent):
        for i, s in enumerate(lst):
            if s is stmt:
                return lst, i
    return None, -1


def _outermost_invariant_loop(node, name):
    """Walk up loops while `name` is not written in the loop; return outermost such loop."""
    loops = enclosing_loops(node)
    chosen = None
    for lp in loops:
        if name in names_written(lp) or name in _loop_targets(lp):
            break
        chosen = lp
    return chosen


def _loop_targets(lp):
    if isinstance(lp, ast.For):
        return node_names(lp.target)
    return set()


def _ensure_import(tree, module, name=None):
    for s in tree.body:
        if name is None and isinstance(s, ast.Import) and any(a.name == module for a in s.names):
            return
        if name is not None and isinstance(s, ast.ImportFrom) and s.module == module and any(a.name == name for a in s.names):
            return
    if name is None:
        node = ast.Import(names=[ast.alias(name=module, asname=None)])
    else:
        node = ast.ImportFrom(module=module, names=[ast.alias(name=name, asname=None)], level=0)
    idx = 0
    if tree.body and isinstance(tree.body[0], ast.Expr) and isinstance(tree.body[0].value, ast.Constant) and isinstance(tree.body[0].value.value, str):
        idx = 1
    tree.body.insert(idx, node)


def _fresh(name, used):
    base = name
    i = 1
    while name in used:
        i += 1
        name = f"{base}{i}"
    used.add(name)
    return name


def _all_names(tree):
    return node_names(tree) | {n.name for n in ast.walk(tree) if isinstance(n, (ast.FunctionDef, ast.ClassDef))}


def _stmts_src(stmts):
    return ast.unparse(ast.Module(body=stmts, type_ignores=[]))


# ---- T1: sort algorithm detection -------------------------------------------
def t_sort_detection(tree):
    changes = []
    for fn in [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]:
        if not fn.args.args:
            continue
        arr = fn.args.args[0].arg
        loops = [n for n in ast.walk(fn) if isinstance(n, (ast.For, ast.While))]
        if len(loops) < 2:
            continue
        nested = any(len(enclosing_loops(lp)) >= 1 for lp in loops)
        if not nested:
            continue
        # swap or shift into arr
        swap = False
        for n in ast.walk(fn):
            if isinstance(n, ast.Assign) and len(n.targets) == 1:
                t, v = n.targets[0], n.value
                if isinstance(t, ast.Tuple) and isinstance(v, ast.Tuple) and len(t.elts) == 2 == len(v.elts):
                    if all(isinstance(e, ast.Subscript) and is_name(e.value, arr) for e in t.elts + v.elts):
                        swap = True
                if isinstance(t, ast.Subscript) and is_name(t.value, arr) and isinstance(v, ast.Subscript) and is_name(v.value, arr):
                    swap = True  # insertion-sort shift
        if not swap:
            continue
        # must compare elements of arr
        cmp = any(isinstance(n, ast.Compare) and isinstance(n.left, ast.Subscript) and is_name(n.left.value, arr) and n.comparators and isinstance(n.comparators[0], ast.Subscript) and is_name(n.comparators[0].value, arr) for n in ast.walk(fn))
        if not cmp:
            continue
        # no other outputs / prints
        if any(isinstance(n, ast.Call) and is_name(n.func, "print") for n in ast.walk(fn)):
            continue
        returns = [n for n in ast.walk(fn) if isinstance(n, ast.Return)]
        returns_arr = any(r.value is not None and is_name(r.value, arr) for r in returns)
        returns_other = any(r.value is not None and not is_name(r.value, arr) for r in returns)
        if returns_other:
            continue
        for reverse in (False, True):
            new_body = [ast.Expr(value=ast.Call(func=ast.Attribute(value=ast.Name(id=arr, ctx=ast.Load()), attr="sort", ctx=ast.Load()), args=[], keywords=([ast.keyword(arg="reverse", value=ast.Constant(value=True))] if reverse else [])))]
            if returns_arr:
                new_body.append(ast.Return(value=ast.Name(id=arr, ctx=ast.Load())))
            doc = ast.get_docstring(fn)
            if doc:
                new_body.insert(0, fn.body[0])
            before = _stmts_src(fn.body)
            # Timsort and a hand-written comparison sort order NaN / unorderable elements differently,
            # so the fast path is taken only for orderable scalars; otherwise the original sort runs.
            orderable = (f"all(isinstance(v, (int, str, bytes, bool)) or (isinstance(v, float) and v == v) "
                         f"or (type(v).__name__ == 'Decimal' and v == v) for v in {arr})")
            keep = [x for x in new_body]
            fallback = list(fn.body)
            if ast.get_docstring(fn) and fallback and isinstance(fallback[0], ast.Expr):
                pass
            doc = ast.get_docstring(fn, clean=False)
            fast = ([] if doc is None else [fn.body[0]]) + ast.parse(_stmts_src(keep)).body
            slow = list(fn.body)
            new_body = [ast.fix_missing_locations(ast.If(test=ast.parse(orderable, mode="eval").body, body=fast, orelse=slow))]
            changes.append(("fn_body", fn.name, (fn.name, new_body), Change(
                "Replace hand-written O(n²) sort with Timsort (orderable items only, fallback kept)",
                f"`{fn.name}` implements a quadratic comparison sort (nested loops + element swaps). Python's built-in `list.sort()` is an O(n log n) Timsort written in C.",
                fn.name, before, _stmts_src(new_body))))
            # only the first candidate that verifies will be kept (handled by caller)
    return changes


# ---- T2: two-sum / duplicate pair patterns ----------------------------------
def _resolve_len_name(node, fn_body_stmts):
    """If node is Name n assigned as `n = len(A)` earlier, return A name."""
    if isinstance(node, ast.Call) and is_name(node.func, "len") and len(node.args) == 1 and isinstance(node.args[0], ast.Name):
        return node.args[0].id
    if isinstance(node, ast.Name):
        for s in fn_body_stmts:
            if isinstance(s, ast.Assign) and len(s.targets) == 1 and is_name(s.targets[0], node.id):
                v = s.value
                if isinstance(v, ast.Call) and is_name(v.func, "len") and len(v.args) == 1 and isinstance(v.args[0], ast.Name):
                    return v.args[0].id
    return None


def _match_pair_loops(outer, fn_stmts):
    """match: for i in range(len(A)): for j in range(i+1, len(A)) [or range(len(A)) w/ i!=j]: if COND: return X"""
    if not (isinstance(outer, ast.For) and isinstance(outer.target, ast.Name)):
        return None
    if not (isinstance(outer.iter, ast.Call) and is_name(outer.iter.func, "range") and len(outer.iter.args) == 1):
        return None
    A = _resolve_len_name(outer.iter.args[0], fn_stmts)
    if A is None or len(outer.body) != 1 or not isinstance(outer.body[0], ast.For):
        return None
    inner = outer.body[0]
    if not isinstance(inner.target, ast.Name):
        return None
    i, j = outer.target.id, inner.target.id
    if not (isinstance(inner.iter, ast.Call) and is_name(inner.iter.func, "range")):
        return None
    ia = inner.iter.args
    strict_guard = False
    if len(ia) == 2:
        lo, hi = ia
        if not (isinstance(lo, ast.BinOp) and isinstance(lo.op, ast.Add) and ((is_name(lo.left, i) and is_const_int(lo.right) and lo.right.value == 1) or (is_name(lo.right, i) and is_const_int(lo.left) and lo.left.value == 1))):
            return None
        if _resolve_len_name(hi, fn_stmts) != A:
            return None
    elif len(ia) == 1:
        if _resolve_len_name(ia[0], fn_stmts) != A:
            return None
        strict_guard = True
    else:
        return None
    if len(inner.body) != 1 or not isinstance(inner.body[0], ast.If):
        return None
    iff = inner.body[0]
    if iff.orelse or len(iff.body) != 1:
        return None
    action = iff.body[0]
    acc = None
    if isinstance(action, ast.AugAssign) and isinstance(action.target, ast.Name) and isinstance(action.op, ast.Add) and is_const_int(action.value) and action.value.value == 1:
        acc = action.target.id
    elif not isinstance(action, ast.Return):
        return None
    cond = iff.test
    if strict_guard:
        # expect: i != j and COND
        if not (isinstance(cond, ast.BoolOp) and isinstance(cond.op, ast.And) and len(cond.values) == 2):
            return None
        g, cond = cond.values
        if not (isinstance(g, ast.Compare) and len(g.ops) == 1 and isinstance(g.ops[0], ast.NotEq) and {ast.unparse(g.left), ast.unparse(g.comparators[0])} == {i, j}):
            return None
    ret = iff.body[0].value if acc is None else None
    return {"A": A, "i": i, "j": j, "cond": cond, "ret": ret, "acc": acc}


def _is_sub(node, A, idx):
    return isinstance(node, ast.Subscript) and is_name(node.value, A) and is_name(node.slice, idx)


def t_pair_patterns(tree):
    changes = []
    for fn in [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]:
        for lst_field, stmts in list(iter_stmt_lists(fn)):
            for k, s in enumerate(list(stmts)):
                m = _match_pair_loops(s, fn.body)
                if not m:
                    continue
                A, i, j, cond, ret, acc = m["A"], m["i"], m["j"], m["cond"], m["ret"], m["acc"]
                ret_src = ast.unparse(ret) if ret is not None else "None"
                if not (isinstance(cond, ast.Compare) and len(cond.ops) == 1 and isinstance(cond.ops[0], ast.Eq)):
                    continue
                L, R = cond.left, cond.comparators[0]
                used = _all_names(tree)
                if acc is not None:
                    # ---- counting pairs
                    cnt = _fresh(f"{A}_counts", used)
                    if (_is_sub(L, A, i) and _is_sub(R, A, j)) or (_is_sub(L, A, j) and _is_sub(R, A, i)):
                        body = f"{cnt} = collections.Counter({A})\n{acc} += sum(c * (c - 1) // 2 for c in {cnt}.values())"
                        title = "Count equal pairs with a Counter"
                        detail = f"Instead of comparing all pairs (O(n²)), count each value once: a value occurring c times forms c·(c−1)/2 equal pairs."
                    else:
                        T = None
                        for X, Y in ((L, R), (R, L)):
                            if isinstance(X, ast.BinOp) and isinstance(X.op, ast.Add):
                                a1, a2 = X.left, X.right
                                if ((_is_sub(a1, A, i) and _is_sub(a2, A, j)) or (_is_sub(a1, A, j) and _is_sub(a2, A, i))) and not (node_names(Y) & {i, j}):
                                    T = Y
                        if T is None:
                            continue
                        tsrc = ast.unparse(T)
                        body = (f"{cnt} = collections.Counter({A})\n"
                                f"for {cnt}_v, {cnt}_c in {cnt}.items():\n"
                                f"    {cnt}_need = {tsrc} - {cnt}_v\n"
                                f"    if {cnt}_need == {cnt}_v:\n"
                                f"        {acc} += {cnt}_c * ({cnt}_c - 1) // 2\n"
                                f"    elif {cnt}_need > {cnt}_v:\n"
                                f"        {acc} += {cnt}_c * {cnt}.get({cnt}_need, 0)")
                        title = "Count pairs with a given sum via Counter"
                        detail = f"All pairs are enumerated (O(n²)). With value frequencies, the number of pairs summing to `{tsrc}` is Σ count(v)·count({tsrc}−v) over distinct values: O(n)."
                    new_stmts = ast.parse(body).body
                    fallback = copy.deepcopy(stmts[k])
                    wrapped = [ast.fix_missing_locations(ast.If(test=ast.parse(INTSAFE.format(var=A), mode="eval").body,
                                                                 body=new_stmts, orelse=[fallback]))]
                    changes.append(("replace_stmt_import", fn.name, (stmts, k, wrapped, ("collections", None)), Change(
                        title + " (ints only, fallback kept)", detail, fn.name, ast.unparse(s), _stmts_src(wrapped))))
                    continue
                # --- duplicates: A[i] == A[j] -> return True/..
                if (_is_sub(L, A, i) and _is_sub(R, A, j)) or (_is_sub(L, A, j) and _is_sub(R, A, i)):
                    if ret_src in ("True", "False", "None") or isinstance(ret, ast.Constant):
                        new = ast.parse(f"if len(set({A})) != len({A}):\n    return {ret_src}").body[0]
                        guarded = ast.If(test=ast.parse(LISTLIKE.format(var=A) + " and " + HASHSAFE.format(var=A), mode="eval").body,
                                         body=[new], orelse=[copy.deepcopy(s)])
                        changes.append(("replace_stmt", fn.name, (stmts, k, [ast.fix_missing_locations(guarded)]), Change(
                            "Duplicate detection via set instead of O(n²) pair scan (hashable items only, fallback kept)",
                            f"Comparing every pair `{A}[{i}] == {A}[{j}]` is quadratic. For hashable scalars a set answers it in O(n); lists/NaN keep the original pair scan.",
                            fn.name, ast.unparse(s), _stmts_src([guarded]))))
                        continue
                # --- two-sum: A[i] + A[j] == T
                T = None
                for X, Y in ((L, R), (R, L)):
                    if isinstance(X, ast.BinOp) and isinstance(X.op, ast.Add):
                        a1, a2 = X.left, X.right
                        if (_is_sub(a1, A, i) and _is_sub(a2, A, j)) or (_is_sub(a1, A, j) and _is_sub(a2, A, i)):
                            if i not in node_names(Y) and j not in node_names(Y):
                                T = Y
                if T is None:
                    continue
                tsrc = ast.unparse(T)
                ret_names = node_names(ret) if ret is not None else set()
                first = _fresh("first_idx", used)
                second = _fresh("second_idx", used)
                if ret_names & {i, j}:
                    # single dict, single right-to-left pass; returns exactly the pair the nested loops return
                    # (smallest i, then smallest j > i): pos[v] is always the smallest index > current i holding v.
                    pos = _fresh("pos", used)
                    found = _fresh("found", used)
                    ret_src_clean = ret_src
                    if isinstance(ret, (ast.List, ast.Tuple)) and len(ret.elts) == 2 and {ast.unparse(e) for e in ret.elts} == {i, j} and all(is_name(e) and e.id == i or e.id == j for e in ret.elts):
                        ret_src_clean = ("list(found)" if isinstance(ret, ast.List) else "found")
                    body = f"""
{pos} = {{}}
{found} = None
for {i} in range(len({A}) - 1, -1, -1):
    {j} = {pos}.get({tsrc} - {A}[{i}])
    if {j} is not None:
        {found} = ({i}, {j})
    {pos}[{A}[{i}]] = {i}
if {found} is not None:
    return {ret_src_clean}
"""
                    detail = (f"The nested loops test every pair (O(n²)). One right-to-left pass with a dict mapping value → smallest index to the right "
                              f"answers `{tsrc} - value` in O(1) and yields the same (lexicographically smallest) pair.")
                else:
                    seen = _fresh("seen", used)
                    body = f"""
{seen} = set()
for {first}_v in {A}:
    if {tsrc} - {first}_v in {seen}:
        return {ret_src}
    {seen}.add({first}_v)
"""
                    detail = f"The nested loops test every pair (O(n²)). A hash set of previously seen values answers `{tsrc} - value in seen` in O(1), giving O(n) total."
                new_stmts = ast.parse(body.strip("\n")).body
                fallback = copy.deepcopy(stmts[k])
                wrapped = [ast.fix_missing_locations(ast.If(test=ast.parse(INTSAFE.format(var=A), mode="eval").body,
                                                             body=new_stmts, orelse=[fallback]))]
                changes.append(("replace_stmt", fn.name, (stmts, k, wrapped), Change(
                    "Pair-sum search: nested loops → hash lookup (ints only, fallback kept)",
                    detail, fn.name, ast.unparse(s), _stmts_src(wrapped))))
    return changes


# ---- T3: primality trial division up to sqrt ---------------------------------
def t_prime_sqrt(tree):
    changes = []
    for fn in [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]:
        if len(fn.args.args) != 1:
            continue
        n_name = fn.args.args[0].arg
        for lp in [x for x in ast.walk(fn) if isinstance(x, ast.For)]:
            it = lp.iter
            if not (isinstance(it, ast.Call) and is_name(it.func, "range") and len(it.args) == 2 and is_const_int(it.args[0]) and it.args[0].value == 2):
                continue
            hi = it.args[1]
            hi_src = ast.unparse(hi)
            if hi_src not in (n_name, f"{n_name} - 1", f"{n_name} // 2 + 1", f"{n_name} // 2"):
                continue
            # body has `if n % i == 0: return False`
            var = lp.target.id if isinstance(lp.target, ast.Name) else None
            if var is None:
                continue
            found = False
            for s in lp.body:
                if isinstance(s, ast.If) and isinstance(s.test, ast.Compare) and len(s.body) == 1 and isinstance(s.body[0], ast.Return):
                    t = s.test
                    if isinstance(t.left, ast.BinOp) and isinstance(t.left.op, ast.Mod) and is_name(t.left.left, n_name) and is_name(t.left.right, var) and isinstance(t.ops[0], ast.Eq) and is_const_int(t.comparators[0]) and t.comparators[0].value == 0:
                        rv = s.body[0].value
                        if isinstance(rv, ast.Constant) and rv.value is False:
                            found = True
            if not found:
                continue
            before = ast.unparse(lp.iter)
            new_iter = ast.parse(f"range(2, math.isqrt(max({n_name}, 0)) + 1)").body[0].value
            changes.append(("replace_iter", fn.name, (lp, new_iter, ("math", None)), Change(
                "Trial division only up to √n",
                f"If `{n_name}` has a divisor larger than √{n_name}, it also has one smaller than √{n_name}, so checking up to `isqrt({n_name})` is sufficient: O(n) → O(√n).",
                fn.name, before, ast.unparse(new_iter))))
    return changes


# ---- T4: memoize recursive functions ------------------------------------------
def t_memoize(tree, analyzer):
    changes = []
    for fn in [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]:
        rec = analyzer.recursion_info(fn)
        if not rec:
            continue
        if analyzer.is_memoized(fn):
            continue
        loop_rec = analyzer._has_loop_recursion(fn)
        if rec["count"] < 2 and not loop_rec:
            continue
        if any(r == "halve" for r in rec["reductions"]) and rec["count"] >= 2 and not loop_rec:
            continue  # divide & conquer, no overlapping subproblems
        if not fn.args.args or fn.args.vararg or fn.args.kwarg:
            continue
        # The GATE (purity / tags) decides skip vs apply and logs the reason; the finder only checks shape.
        changes.append(("memo_guard", fn.name, (fn, rec), Change(
            "Memoize overlapping recursive calls (unhashable inputs fall back to the original)",
            f"`{fn.name}` calls itself {rec['count']} time(s) per invocation on smaller inputs, so the same sub-problems are recomputed exponentially often. Caching results with `functools.lru_cache` makes each distinct input compute once.",
            fn.name, f"def {fn.name}(...)", f"@functools.lru_cache(maxsize=None)\ndef {fn.name}(...)")))
    return changes


# ---- T5: membership tests on lists inside loops → set --------------------------
def _is_list_like(name, scope, analyzer, fn):
    if name in analyzer.set_like:
        return False
    for n in ast.walk(scope):
        if isinstance(n, ast.Assign) and any(is_name(t, name) for t in n.targets):
            v = n.value
            if isinstance(v, (ast.List, ast.ListComp)):
                return True
            if isinstance(v, ast.Call) and call_name(v) in ("list", "sorted", ".split", "range") and call_name(v) != "range":
                return True
            if isinstance(v, (ast.Set, ast.Dict, ast.SetComp, ast.DictComp, ast.Constant, ast.JoinedStr)):
                return False
            if isinstance(v, ast.Call) and call_name(v) in SET_LIKE_CALLS:
                return False
            if isinstance(v, ast.Call) and call_name(v) == "range":
                return False
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute) and is_name(n.func.value, name):
            if n.func.attr in ("append", "sort", "extend", "insert"):
                return True
            if n.func.attr in ("add", "keys", "items", "values", "get", "lower", "split"):
                return False
    if fn is not None:
        for a in fn.args.args:
            if a.arg == name:
                if a.annotation is not None:
                    ann = ast.unparse(a.annotation).lower()
                    return "list" in ann or "sequence" in ann
                lp = name.lower()
                return lp in LIST_NAMES or lp.endswith("list") or lp.endswith("arr") or lp.endswith("s") and lp not in STR_NAMES
    return False


def t_membership_set(tree, analyzer):
    changes = []
    seen_keys = set()
    for cmp_node in [n for n in ast.walk(tree) if isinstance(n, ast.Compare)]:
        if len(cmp_node.ops) != 1 or not isinstance(cmp_node.ops[0], (ast.In, ast.NotIn)):
            continue
        rhs = cmp_node.comparators[0]
        if not isinstance(rhs, ast.Name):
            continue
        name = rhs.id
        fn = _enclosing_function(cmp_node)
        scope = fn if fn is not None else tree
        if not _is_list_like(name, scope, analyzer, fn):
            continue
        loop = _outermost_invariant_loop(cmp_node, name)
        if loop is None:
            continue
        # the compare must be inside the loop body, not the iter
        key = (id(scope), name, id(loop))
        if key in seen_keys:
            continue
        seen_keys.add(key)
        lst, idx = _parent_stmt_list(loop)
        if lst is None:
            continue
        used = _all_names(tree)
        set_name = _fresh(f"{name}_set", used)
        changes.append(("membership", fn.name if fn else None, (scope, name, loop, lst, idx, set_name), Change(
            f"Membership test on list `{name}` inside a loop → set lookup",
            f"`x in {name}` scans the whole list (O(n)) on every iteration. Building `{set_name} = set({name})` once before the loop makes each test O(1).",
            fn.name if fn else "<module>", ast.unparse(cmp_node), ast.unparse(cmp_node).replace(f" {name}", f" {set_name}"))))
    return changes


def _varying_params(fn, rec_calls):
    """params whose value differs between a call site and at least one recursive call (they span the cache states)"""
    params = [a.arg for a in fn.args.args]
    varying = set()
    for c in rec_calls:
        for p, a in zip(params, c.args):
            if not (isinstance(a, ast.Name) and a.id == p):
                varying.add(p)
    return varying


def _is_memo_wrapper(fn):
    """Recognise the generated wrapper -> (orig_name, memo_name) or None.

        def f(a, b):
            try:
                hash((a, b))
            except TypeError:
                return _f_orig(a, b)     # unhashable arguments: run uncached
            return _f_orig(a, b)         # NO try/except around the call

    `_f_orig` holds the original body and its memo lookup, so it IS the cached implementation;
    self-calls target it directly (one Python frame per level, no C-stack nesting)."""
    if len(fn.body) != 2:
        return None
    tr, ret = fn.body[0], fn.body[1]
    if not isinstance(tr, ast.Try) or len(tr.handlers) != 1 or len(tr.body) != 1 or not isinstance(tr.body[0], ast.Expr):
        return None
    h = tr.body[0].value
    if not (isinstance(h, ast.Call) and isinstance(h.func, ast.Name) and h.func.id == "hash"):
        return None
    hd = tr.handlers[0]
    if not (isinstance(hd.type, ast.Name) and hd.type.id == "TypeError" or
            (isinstance(hd.type, (ast.Tuple, ast.List)) and any(isinstance(x, ast.Name) and x.id == "TypeError" for x in hd.type.elts))):
        return None
    if len(hd.body) != 1 or not isinstance(hd.body[0], ast.Return):
        return None
    for r in (hd.body[0], ret):
        if not (isinstance(r, ast.Return) and isinstance(r.value, ast.Call) and isinstance(r.value.func, ast.Name)
                and r.value.func.id.endswith("_orig")):
            return None
    oname = ret.value.func.id
    memo = oname[: -len("_orig")] + "_memo"
    return oname, memo


def apply_memo_guard(tree, payload):
    """Memoisation that costs ONE Python frame per recursion level.

    Why a dict instead of functools.lru_cache: routing a recursive self-call through an
    `lru_cache` wrapper nests C -> Python -> C at every level, and CPython's C-stack guard
    then raises RecursionError around n=600 even though Python-frame depth is unchanged
    (verified: plain recursion returns 601 at n=600, lru_cache recursion raises). So the
    memo lookup lives INSIDE the frame that runs the body:

        _f_memo = {}
        _f_miss = object()

        def _f_orig(a, b):
            try:
                _hit = _f_memo[(a, b)]
            except KeyError:
                _hit = _f_miss
            except TypeError:                 # unhashable arguments: never memoise them
                _hit = _f_miss
                _key = None
            if _hit is not _f_miss:
                return _hit
            ...original body (self-calls -> _f_orig), returns captured...
            finally: store the result

        def f(a, b):                          # public wrapper
            try:
                hash((a, b))
            except TypeError:
                return _f_orig(a, b)          # unhashable: uncached path
            return _f_orig(a, b)              # no try/except around the call

        f.cache_clear = _f_memo.clear
    """
    fn, rec = payload
    used = _all_names(tree)
    orig_name = _fresh(f"_{fn.name}_orig", used)
    memo_name = orig_name[: -len("_orig")] + "_memo"
    miss_name = orig_name[: -len("_orig")] + "_miss"
    res_var = _fresh("_result", used)
    done_var = _fresh("_done", used)
    hit_var = _fresh("_hit", used)
    key_var = _fresh("_key", used)
    args_src = ", ".join(a.arg for a in fn.args.args)
    key_src = f"({args_src})" if len(fn.args.args) != 1 else f"({args_src},)"

    # 1. self-calls target _f_orig (the memoised frame) -> one Python frame per level
    class _Reroute(ast.NodeTransformer):
        def visit_Call(self, node):
            if isinstance(node.func, ast.Name) and node.func.id == fn.name:
                node.func = ast.copy_location(ast.Name(id=orig_name, ctx=ast.Load()), node.func)
                return node
            return self.generic_visit(node)

        def visit_FunctionDef(self, node):
            return node

        visit_AsyncFunctionDef = visit_FunctionDef

        def visit_Lambda(self, node):
            return node

    # 2. capture the return value so the memo can store base cases too
    class _Capture(ast.NodeTransformer):
        def __init__(self):
            self.done = False

        def visit_FunctionDef(self, node):
            return node

        visit_AsyncFunctionDef = visit_FunctionDef

        def visit_Lambda(self, node):
            return node

        def visit_Return(self, node):
            self.done = True
            value = node.value if node.value is not None else ast.Constant(value=None)
            set_assign = ast.Assign(targets=[ast.Name(id=res_var, ctx=ast.Store())], value=value)
            flag_assign = ast.Assign(targets=[ast.Name(id=done_var, ctx=ast.Store())],
                                     value=ast.Constant(value=True))
            ret_stmt = ast.Return(value=ast.Name(id=res_var, ctx=ast.Load()))
            return [ast.fix_missing_locations(x) for x in (set_assign, flag_assign, ret_stmt)]

    rerouted = [_Reroute().visit(b) for b in copy.deepcopy(fn.body)]
    cap = _Capture()
    body = []
    for b in rerouted:
        out = cap.visit(b)
        body.extend(out if isinstance(out, list) else [out])
    body = [ast.fix_missing_locations(x) for x in body]

    prelude_src = (
        f"def {orig_name}({ast.unparse(fn.args)}):\n"
        f"    {key_var} = {key_src}\n"
        f"    try:\n"
        f"        {hit_var} = {memo_name}[{key_var}]\n"
        f"    except KeyError:\n"
        f"        {hit_var} = {miss_name}\n"
        f"    except TypeError:\n"
        f"        {hit_var} = {miss_name}\n"
        f"        {key_var} = None\n"
        f"    if {hit_var} is not {miss_name}:\n"
        f"        return {hit_var}\n"
        f"    {res_var} = None\n"
        f"    {done_var} = False\n")
    prelude = ast.parse(prelude_src).body[0]
    prelude.args = copy.deepcopy(fn.args)
    inner = prelude.body
    try_stmt = ast.Try(body=body, handlers=[], orelse=[],
                       finalbody=[ast.parse(
                           f"if {done_var} and {key_var} is not None:\n"
                           f"    {memo_name}[{key_var}] = {res_var}").body[0]])
    inner.append(ast.fix_missing_locations(try_stmt))
    memo_assign = ast.parse(f"{memo_name} = {{}}\n{miss_name} = object()").body
    args_src_all = ", ".join(a.arg for a in fn.args.args)
    hash_args = f"({args_src_all})" if len(fn.args.args) != 1 else f"({args_src_all},)"
    wrap_src = (f"def {fn.name}({ast.unparse(fn.args)}):\n"
                f"    try:\n        hash({hash_args})\n"
                f"    except TypeError:\n        return {orig_name}({args_src_all})\n"
                f"    return {orig_name}({args_src_all})")
    wrap = ast.parse(wrap_src).body[0]
    wrap.args = copy.deepcopy(fn.args)
    expose = ast.parse(f"{fn.name}.cache_clear = {memo_name}.clear").body[0]

    parent = getattr(fn, "_parent", tree)
    lst = None
    if parent is not tree:
        for _, cand in iter_stmt_lists(parent):
            if fn in cand:
                lst = cand
                break
    if lst is None and fn in tree.body:
        lst = tree.body
    if lst is None:
        return
    i = lst.index(fn)
    lst[i:i + 1] = [ast.fix_missing_locations(x) for x in (memo_assign[0], memo_assign[1], prelude, wrap, expose)]


def apply_membership(tree, payload):
    scope, name, loop, lst, idx, set_name = payload
    for n in list(ast.walk(loop)):
        if isinstance(n, ast.Compare) and len(n.ops) == 1 and isinstance(n.ops[0], (ast.In, ast.NotIn)) and is_name(n.comparators[0], name):
            left = ast.unparse(n.left)
            expr = ast.parse(f"(({left} in {set_name}) if {set_name} is not None else ({left} in {name}))", mode="eval").body
            if isinstance(n.ops[0], ast.NotIn):
                expr = ast.UnaryOp(op=ast.Not(), operand=expr)
            _replace_node(tree, n, expr)
    guard = HASHSAFE.format(var=name)
    lst.insert(idx, ast.parse(f"{set_name} = set({name}) if {guard} else None").body[0])


# ---- T5b: list used purely as a membership collection → set --------------------
def t_list_as_set(tree):
    """seen = []  …  if x not in seen: seen.append(x)   =>   seen = set() / seen.add(x)
    Only when the list is *never* indexed, iterated, sliced, returned or passed on."""
    changes = []
    for scope in [tree] + [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]:
        for k, s in enumerate(scope.body):
            if not (isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name)):
                continue
            if not (isinstance(s.value, ast.List) and not s.value.elts):
                continue
            name = s.targets[0].id
            member_tests = 0
            appends = 0
            ok = True
            for n in ast.walk(scope):
                if isinstance(n, ast.FunctionDef) and n is not scope:
                    continue
                if isinstance(n, ast.Name) and n.id == name:
                    parent = getattr(n, "_parent", None)
                    if parent is s:
                        continue
                    if isinstance(parent, ast.Compare) and len(parent.ops) == 1 and isinstance(parent.ops[0], (ast.In, ast.NotIn)) and parent.comparators[0] is n:
                        member_tests += 1
                    elif isinstance(parent, ast.Attribute) and parent.attr == "append" and isinstance(getattr(parent, "_parent", None), ast.Call):
                        appends += 1
                    elif isinstance(parent, ast.Call) and is_name(parent.func, "len") and parent.args and parent.args[0] is n:
                        pass
                    else:
                        ok = False
            if not ok or member_tests == 0 or appends == 0:
                continue
            # the membership test should be inside a loop for this to matter
            in_loop = any(isinstance(n, ast.Compare) and len(n.ops) == 1 and isinstance(n.ops[0], (ast.In, ast.NotIn)) and is_name(n.comparators[0], name) and enclosing_loops(n) for n in ast.walk(scope))
            if not in_loop:
                continue
            fn = scope if isinstance(scope, ast.FunctionDef) else None
            changes.append(("list_as_set", fn.name if fn else None, (scope, s, name), Change(
                f"`{name}` is only used for membership → make it a set",
                f"`{name}` is appended to and tested with `in`, but never indexed or iterated. As a list each `in` test is O(n); as a set it is O(1).",
                fn.name if fn else "<module>", f"{name} = []\n… if x not in {name}: {name}.append(x)", f"{name} = set()\n… if x not in {name}: {name}.add(x)")))
    return changes


def apply_list_as_set(tree, payload):
    scope, s, name = payload
    s.value = ast.Call(func=ast.Name(id="set", ctx=ast.Load()), args=[], keywords=[])
    for n in ast.walk(scope):
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute) and is_name(n.func.value, name) and n.func.attr == "append":
            n.func.attr = "add"


# ---- T5c: membership on a list that is also appended to → shadow set ------------
def t_shadow_set(tree):
    """result = [] … if x not in result: result.append(x) … return result
    => keep the list, but mirror its contents in a set used for the membership tests."""
    changes = []
    for scope in [tree] + [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]:
        for s in scope.body:
            if not (isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name) and isinstance(s.value, ast.List) and not s.value.elts):
                continue
            name = s.targets[0].id
            tests, appends = [], []
            ok = True
            if any(isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name)
                   and n.targets[0].id.startswith(f"{name}_seen") for n in ast.walk(scope)):
                continue
            for n in ast.walk(scope):
                if isinstance(n, ast.FunctionDef) and n is not scope:
                    continue
                if isinstance(n, ast.Compare) and len(n.ops) == 1 and isinstance(n.ops[0], (ast.In, ast.NotIn)) and is_name(n.comparators[0], name):
                    if enclosing_loops(n):
                        tests.append(n)
                if isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute) and is_name(n.func.value, name):
                    if n.func.attr == "append" and len(n.args) == 1:
                        appends.append(n)
                    elif n.func.attr in MUTATING_METHODS:
                        ok = False
                if isinstance(n, (ast.Assign, ast.AugAssign)) and n is not s:
                    tg = n.targets if isinstance(n, ast.Assign) else [n.target]
                    for t in tg:
                        if is_name(t, name) or (isinstance(t, ast.Subscript) and is_name(t.value, name)):
                            ok = False
                if isinstance(n, ast.Delete) and any(name in node_names(t) for t in n.targets):
                    ok = False
            if not ok or not tests or not appends:
                continue
            # appends must be expression statements (so we can add a sibling statement)
            if not all(isinstance(getattr(a, "_parent", None), ast.Expr) for a in appends):
                continue
            fn = scope if isinstance(scope, ast.FunctionDef) else None
            used = _all_names(tree)
            sname = _fresh(f"{name}_seen", used)
            changes.append(("shadow_set", fn.name if fn else None, (scope, s, name, sname, tests, appends), Change(
                f"Mirror `{name}` in a set for O(1) membership tests",
                f"`x in {name}` scans the growing list on every iteration (O(n²) overall). Keeping a parallel set `{sname}` that is updated on each append makes the test O(1) while preserving the list and its order.",
                fn.name if fn else "<module>", f"if x not in {name}:\n    {name}.append(x)", f"if x not in {sname}:\n    {name}.append(x)\n    {sname}.add(x)")))
    return changes


def apply_shadow_set(tree, payload):
    scope, s, name, sname, tests, appends = payload
    guard_src = HASHSAFE.format(var=name)
    _src_iter = None
    if tests:
        loops = enclosing_loops(tests[0])
        if loops and isinstance(loops[0], ast.For) and isinstance(loops[0].iter, ast.Name):
            guard_src = "isinstance(%s, (list, tuple)) and " % loops[0].iter.id + HASHSAFE.format(var=loops[0].iter.id)
    for t in tests:
        left = ast.unparse(t.left)
        expr = ast.parse(f"(({left} in {sname}) if {sname} is not None else ({left} in {name}))", mode="eval").body
        if isinstance(t.ops[0], ast.NotIn):
            expr = ast.UnaryOp(op=ast.Not(), operand=expr)
        _replace_node(tree, t, expr)
    for a in appends:
        expr_stmt = a._parent
        lst, idx = _parent_stmt_list(expr_stmt)
        if lst is None:
            continue
        add = ast.parse(f"if {sname} is not None:\n    {sname}.add({ast.unparse(a.args[0])})").body[0]
        lst.insert(idx + 1, ast.fix_missing_locations(add))
    lst, idx = _parent_stmt_list(s)
    if lst is not None:
        lst.insert(idx + 1, ast.parse(f"{sname} = set() if {guard_src} else None").body[0])


# ---- T6: list.count inside loop → Counter --------------------------------------
def t_count_counter(tree):
    changes = []
    done = set()
    for call in [n for n in ast.walk(tree) if isinstance(n, ast.Call)]:
        if call_name(call) != ".count" or not isinstance(call.func.value, ast.Name) or len(call.args) != 1:
            continue
        name = call.func.value.id
        loop = _outermost_invariant_loop(call, name)
        if loop is None:
            continue
        # be sure it's a list-ish count (not str.count with substring): arg should be a Name/Subscript
        if not isinstance(call.args[0], (ast.Name, ast.Subscript)):
            continue
        fn = _enclosing_function(call)
        key = (name, id(loop))
        if key in done:
            continue
        done.add(key)
        lst, idx = _parent_stmt_list(loop)
        if lst is None:
            continue
        used = _all_names(tree)
        cname = _fresh(f"{name}_counts", used)
        changes.append(("counter", fn.name if fn else None, (name, loop, lst, idx, cname), Change(
            f"`{name}.count(x)` inside a loop → precomputed Counter",
            f"Each `{name}.count(...)` call scans the whole list (O(n)), so calling it inside a loop is O(n²). A `collections.Counter` built once gives O(1) frequency lookups.",
            fn.name if fn else "<module>", ast.unparse(call), f"{cname}[{ast.unparse(call.args[0])}]")))
    return changes


def apply_counter(tree, payload):
    name, loop, lst, idx, cname = payload
    class R(ast.NodeTransformer):
        def visit_Call(self, node):
            self.generic_visit(node)
            if call_name(node) == ".count" and is_name(node.func.value, name) and len(node.args) == 1 and isinstance(node.args[0], (ast.Name, ast.Subscript)):
                inner = ast.Subscript(value=ast.Name(id=cname, ctx=ast.Load()), slice=node.args[0], ctx=ast.Load())
                cond = ast.Compare(left=ast.Name(id=cname, ctx=ast.Load()), ops=[ast.IsNot()], comparators=[ast.Constant(value=None)])
                return ast.copy_location(ast.IfExp(test=cond, body=inner, orelse=node), node)
            return node
    R().visit(loop)
    guard = LISTLIKE.format(var=name) + " and " + HASHSAFE.format(var=name)
    lst.insert(idx, ast.parse(f"{cname} = collections.Counter({name}) if {guard} else None").body[0])
    _ensure_import(tree, "collections")


# ---- T7: nested loop equality search → membership ------------------------------
def t_nested_equality(tree):
    """for x in A: for y in B: if x == y: <stmts>; break   =>  for x in A: if x in B_set: <stmts>"""
    changes = []
    for inner in [n for n in ast.walk(tree) if isinstance(n, ast.For)]:
        outer_loops = enclosing_loops(inner)
        if not outer_loops or not isinstance(outer_loops[0], ast.For):
            continue
        outer = outer_loops[0]
        if not (isinstance(inner.target, ast.Name) and isinstance(inner.iter, ast.Name) and isinstance(outer.target, ast.Name)):
            continue
        x, y, B = outer.target.id, inner.target.id, inner.iter.id
        if len(inner.body) != 1 or not isinstance(inner.body[0], ast.If) or inner.body[0].orelse or inner.orelse:
            continue
        iff = inner.body[0]
        t = iff.test
        if not (isinstance(t, ast.Compare) and len(t.ops) == 1 and isinstance(t.ops[0], ast.Eq) and {ast.unparse(t.left), ast.unparse(t.comparators[0])} == {x, y}):
            continue
        body = iff.body
        has_break = isinstance(body[-1], ast.Break)
        ends_return = isinstance(body[-1], ast.Return)
        if not (has_break or ends_return):
            continue
        inner_stmts = body[:-1] if has_break else body
        if y in set().union(*[node_names(s) for s in inner_stmts]) if inner_stmts else False:
            continue
        if B in names_written(outer):
            continue
        fn = _enclosing_function(inner)
        lst, idx = _parent_stmt_list(outer)
        if lst is None:
            continue
        used = _all_names(tree)
        set_name = _fresh(f"{B}_set", used)
        changes.append(("nested_eq", fn.name if fn else None, (inner, outer, lst, idx, B, set_name, x, inner_stmts), Change(
            "Nested equality scan → set membership",
            f"Scanning `{B}` for every element of the outer loop is O(n·m). A set built once turns the inner loop into an O(1) `in` check.",
            fn.name if fn else "<module>", ast.unparse(inner), f"if {x} in {set_name}:\n    ...")))
        break  # one at a time; re-run picks up more
    return changes


def apply_nested_eq(tree, payload):
    inner, outer, lst, idx, B, set_name, x, inner_stmts = payload
    yv = "_y_guard"
    fast = ast.Compare(left=ast.Name(id=x, ctx=ast.Load()), ops=[ast.In()], comparators=[ast.Name(id=set_name, ctx=ast.Load())])
    slow = ast.Call(func=ast.Name(id="any", ctx=ast.Load()), args=[ast.GeneratorExp(
        elt=ast.Compare(left=ast.Name(id=x, ctx=ast.Load()), ops=[ast.Eq()], comparators=[ast.Name(id=yv, ctx=ast.Load())]),
        generators=[ast.comprehension(target=ast.Name(id=yv, ctx=ast.Store()), iter=ast.Name(id=B, ctx=ast.Load()), ifs=[], is_async=0)])], keywords=[])
    test = ast.IfExp(test=ast.Compare(left=ast.Name(id=set_name, ctx=ast.Load()), ops=[ast.IsNot()], comparators=[ast.Constant(value=None)]),
                     body=fast, orelse=slow)
    new_if = ast.If(test=test, body=inner_stmts or [ast.Pass()], orelse=[])
    plist, pidx = _parent_stmt_list(inner)
    if plist is None:
        return
    plist[pidx] = ast.fix_missing_locations(new_if)
    guard = HASHSAFE.format(var=B)
    lst.insert(idx, ast.parse(f"{set_name} = set({B}) if {guard} else None").body[0])


# ---- T8: loop-invariant hoisting -----------------------------------------------
def t_hoist(tree):
    changes = []
    done = set()
    for call in [n for n in ast.walk(tree) if isinstance(n, ast.Call)]:
        cn = call_name(call)
        if cn not in ("max", "min", "sum", "sorted", "len") or len(call.args) != 1 or call.keywords or not isinstance(call.args[0], ast.Name):
            continue
        if cn == "len":
            continue  # O(1) anyway
        name = call.args[0].id
        loop = _outermost_invariant_loop(call, name)
        if loop is None:
            continue
        # ensure call isn't in the loop header
        if any(call is n or call in list(ast.walk(loop.iter if isinstance(loop, ast.For) else loop.test)) for n in []):
            continue
        hdr = loop.iter if isinstance(loop, ast.For) else loop.test
        if any(n is call for n in ast.walk(hdr)):
            continue
        key = (cn, name, id(loop))
        if key in done:
            continue
        done.add(key)
        fn = _enclosing_function(call)
        lst, idx = _parent_stmt_list(loop)
        if lst is None:
            continue
        used = _all_names(tree)
        hname = _fresh(f"{name}_{cn}", used)
        changes.append(("hoist", fn.name if fn else None, (cn, name, loop, lst, idx, hname), Change(
            f"Hoist loop-invariant `{cn}({name})` out of the loop",
            f"`{name}` is not modified inside the loop, yet `{cn}({name})` (an O(n) scan) is recomputed every iteration. Computing it once removes a factor of n.",
            fn.name if fn else "<module>", ast.unparse(call), hname)))
    return changes


def apply_hoist(tree, payload):
    cn, name, loop, lst, idx, hname = payload
    class R(ast.NodeTransformer):
        def visit_Call(self, node):
            self.generic_visit(node)
            if call_name(node) == cn and len(node.args) == 1 and is_name(node.args[0], name) and not node.keywords:
                return ast.Name(id=hname, ctx=ast.Load())
            return node
    for s in loop.body:
        R().visit(s)
    if cn in ("max", "min"):
        lst.insert(idx, ast.parse(f"{hname} = {cn}({name}) if {name} else None").body[0])
    else:
        lst.insert(idx, ast.parse(f"{hname} = {cn}({name})").body[0])


# ---- T8b: palindrome idiom collapse -------------------------------------------
def t_palindrome_idiom(tree):
    """Recognize manual palindrome checks and collapse to sequence == sequence[::-1]."""
    changes = []
    for fn in [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]:
        stmts = fn.body
        if not stmts:
            continue
        last = stmts[-1]
        seq_target = None
        redundant_vars = set()
        # Pattern 1: `return original == reversed_str` where reversed_str is built with reversed(...)
        if isinstance(last, ast.Return) and isinstance(last.value, ast.Compare) and len(last.value.ops) == 1 and isinstance(last.value.ops[0], ast.Eq):
            L = ast.unparse(last.value.left)
            R = ast.unparse(last.value.comparators[0])
            for s in stmts:
                if isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name):
                    var = s.targets[0].id
                    if var in (L, R):
                        src = ast.unparse(s.value)
                        import re
                        m = re.search(r"reversed\((\w+)\)", src)
                        if m:
                            seq_target = m.group(1)
                            redundant_vars.add(L)
                            redundant_vars.add(R)
                            break
        # Pattern 2: two-pointer while loop or half-range for loop
        if seq_target is None:
            for s in stmts:
                if isinstance(s, ast.While) and "<" in ast.unparse(s.test):
                    for b in s.body:
                        if isinstance(b, ast.If) and len(b.body) == 1 and isinstance(b.body[0], ast.Return) and isinstance(b.body[0].value, ast.Constant) and b.body[0].value.value is False:
                            cmp = b.test
                            if isinstance(cmp, ast.Compare) and len(cmp.ops) == 1 and isinstance(cmp.ops[0], ast.NotEq):
                                if isinstance(cmp.left, ast.Subscript) and isinstance(cmp.left.value, ast.Name):
                                    seq_target = cmp.left.value.id
                                    break
                elif isinstance(s, ast.For) and isinstance(s.target, ast.Name):
                    it_src = ast.unparse(s.iter)
                    if ("len(" in it_src) and ("// 2" in it_src or "/ 2" in it_src or ">> 1" in it_src):
                        if len(s.body) == 1 and isinstance(s.body[0], ast.If):
                            iff = s.body[0]
                            if len(iff.body) == 1 and isinstance(iff.body[0], ast.Return) and isinstance(iff.body[0].value, ast.Constant) and iff.body[0].value.value is False:
                                cmp = iff.test
                                if isinstance(cmp, ast.Compare) and len(cmp.ops) == 1 and isinstance(cmp.ops[0], ast.NotEq):
                                    if isinstance(cmp.left, ast.Subscript) and isinstance(cmp.left.value, ast.Name):
                                        seq_target = cmp.left.value.id
                                        break
        if seq_target is not None:
            # Build cleaned body: keep preparation steps (like chars = [c for c in s.lower() if ...])
            keep = []
            for s in stmts[:-1]:
                # Discard redundant variables like original and reversed_str
                if isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name) and s.targets[0].id in redundant_vars:
                    continue
                # Discard manual loops if seq_target is checked
                if isinstance(s, (ast.For, ast.While)):
                    continue
                # Discard length guards on redundant variables
                if isinstance(s, ast.If) and any(rv in node_names(s) for rv in redundant_vars):
                    continue
                keep.append(s)
            keep.append(ast.parse(f"return {seq_target} == {seq_target}[::-1]").body[0])
            before_src = _stmts_src(stmts)
            after_src = _stmts_src(keep)
            if before_src != after_src:
                changes.append(("fn_body", fn.name, (fn.name, keep), Change(
                    "Idiomatic palindrome check: s == s[::-1]",
                    f"Redundant string copies, length checks, and character comparison loops collapsed into idiomatic `{seq_target} == {seq_target}[::-1]`: O(n) time, single pass in C.",
                    fn.name, before_src, after_src)))
    return changes


# ---- T8c: manual sequence equality loop → native equality ---------------------
def _match_neq_subscripts(cmp, ivar):
    if not (isinstance(cmp, ast.Compare) and len(cmp.ops) == 1 and isinstance(cmp.ops[0], ast.NotEq)):
        return None
    L, R = cmp.left, cmp.comparators[0]
    if (isinstance(L, ast.Subscript) and isinstance(R, ast.Subscript)
            and isinstance(L.value, ast.Name) and isinstance(R.value, ast.Name)
            and is_name(L.slice, ivar) and is_name(R.slice, ivar)):
        return L.value.id, R.value.id
    return None


def t_manual_seq_eq(tree):
    """Recognise manual element-by-element equality checks:
      1) `for i in range(len(A)): if A[i] != B[i]: return False` + `return True` -> `return A == B`
      2) `flag = True` + `for i in range(len(A)): if A[i] != B[i]: flag = False` -> `flag = A == B`
      3) mismatch-count (`count = sum([1 for i in range(len(A)) if A[i] != B[i]])` + `if count > 0: ...`) -> `if A != B: ...`"""
    changes = []
    for fn in [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]:
        alias = len_aliases(fn)
        der = derivations(fn)
        counts = _scope_assign_counts(fn)
        for node in ast.walk(fn):
            for _, stmts in iter_stmt_lists(node):
                for i in range(len(stmts) - 1):
                    s1, s2 = stmts[i], stmts[i + 1]
                    if _enclosing_function(s1) is not fn:
                        continue
                    # Form 1: early-return loop + `return True`
                    if (isinstance(s2, ast.Return) and isinstance(s2.value, ast.Constant) and s2.value.value is True
                            and isinstance(s1, ast.For) and isinstance(s1.target, ast.Name) and not s1.orelse
                            and len(s1.body) == 1 and isinstance(s1.body[0], ast.If) and not s1.body[0].orelse):
                        iff = s1.body[0]
                        if (len(iff.body) == 1 and isinstance(iff.body[0], ast.Return)
                                and isinstance(iff.body[0].value, ast.Constant) and iff.body[0].value.value is False):
                            pair = _match_neq_subscripts(iff.test, s1.target.id)
                            if pair:
                                A, B = pair
                                new_node = ast.parse(f"return {A} == {B}").body[0]
                                changes.append(("replace_pair", fn.name, (stmts, i, new_node), Change(
                                    f"Sequence equality loop → `{A} == {B}`",
                                    f"Bytecode index-by-index comparison loop replaced by Python's built-in `{A} == {B}`, which compares buffers in C.",
                                    fn.name, _stmts_src([s1, s2]), ast.unparse(new_node))))
                                break
                    # Form 2: `flag = True` + `for i in range(len(A)): if A[i] != B[i]: flag = False`
                    if (isinstance(s1, ast.Assign) and len(s1.targets) == 1 and isinstance(s1.targets[0], ast.Name)
                            and isinstance(s1.value, ast.Constant) and s1.value.value is True
                            and isinstance(s2, ast.For) and isinstance(s2.target, ast.Name) and not s2.orelse
                            and len(s2.body) == 1 and isinstance(s2.body[0], ast.If) and not s2.body[0].orelse):
                        flag = s1.targets[0].id
                        iff = s2.body[0]
                        if (len(iff.body) == 1 and isinstance(iff.body[0], ast.Assign) and len(iff.body[0].targets) == 1
                                and is_name(iff.body[0].targets[0], flag) and isinstance(iff.body[0].value, ast.Constant)
                                and iff.body[0].value.value is False):
                            pair = _match_neq_subscripts(iff.test, s2.target.id)
                            rng_t = _is_plain_range_len(s2.iter, alias)
                            if pair and rng_t in pair and same_length(pair[0], pair[1], der):
                                A, B = pair
                                new_node = ast.parse(f"{flag} = {A} == {B}").body[0]
                                changes.append(("replace_pair", fn.name, (stmts, i, new_node), Change(
                                    f"Flag equality loop → `{flag} = {A} == {B}`",
                                    f"`{A}` and `{B}` have provably equal length; scanning every index to clear `{flag}` is `{flag} = {A} == {B}`.",
                                    fn.name, _stmts_src([s1, s2]), ast.unparse(new_node))))
                                break
                    # Form 3: `count = sum([1 for i in range(len(A)) if A[i] != B[i]])` + `if count > 0: body`
                    if (isinstance(s1, ast.Assign) and len(s1.targets) == 1 and isinstance(s1.targets[0], ast.Name)
                            and isinstance(s2, ast.If) and not s2.orelse and isinstance(s2.test, ast.Compare)
                            and len(s2.test.ops) == 1 and isinstance(s2.test.ops[0], (ast.Gt, ast.NotEq))
                            and is_name(s2.test.left, s1.targets[0].id) and is_const_int(s2.test.comparators[0]) and s2.test.comparators[0].value == 0):
                        cname = s1.targets[0].id
                        if counts.get(cname, 0) == 1 and _load_count(fn, cname) == 1:
                            v = s1.value
                            if isinstance(v, ast.Call) and is_name(v.func, "sum") and len(v.args) == 1 and isinstance(v.args[0], (ast.ListComp, ast.GeneratorExp)):
                                lc = v.args[0]
                                if (is_const_int(lc.elt) and lc.elt.value == 1 and len(lc.generators) == 1
                                        and len(lc.generators[0].ifs) == 1 and isinstance(lc.generators[0].target, ast.Name)):
                                    g = lc.generators[0]
                                    pair = _match_neq_subscripts(g.ifs[0], g.target.id)
                                    rng_t = _is_plain_range_len(g.iter, alias)
                                    if pair and rng_t in pair and same_length(pair[0], pair[1], der):
                                        A, B = pair
                                        new_if = ast.If(test=ast.parse(f"{A} != {B}", mode="eval").body, body=copy.deepcopy(s2.body), orelse=[])
                                        new_if = ast.fix_missing_locations(new_if)
                                        changes.append(("replace_pair", fn.name, (stmts, i, new_if), Change(
                                            f"Mismatch count > 0 → `{A} != {B}`",
                                            f"Counting index mismatches just to check `> 0` is `{A} != {B}` (equal lengths proven).",
                                            fn.name, _stmts_src([s1, s2]), ast.unparse(new_if))))
                                        break
    return changes


# ---- T8d: dead length comparison elimination ----------------------------------
def t_dead_len_check(tree):
    """Eliminate if len(A) != len(B): return False where A and B are provably equal length."""
    changes = []
    for fn in [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]:
        stmts = fn.body
        seq_sources = {}
        for s in stmts:
            if isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name):
                var = s.targets[0].id
                src = ast.unparse(s.value)
                import re
                m_rev = re.search(r"reversed\((\w+)\)", src)
                if m_rev:
                    seq_sources[var] = m_rev.group(1)
                else:
                    m_join = re.search(r"\.join\((\w+)\)", src)
                    if m_join:
                        seq_sources[var] = m_join.group(1)
        for i, s in enumerate(stmts):
            if isinstance(s, ast.If) and isinstance(s.test, ast.Compare) and len(s.body) == 1 and isinstance(s.body[0], ast.Return):
                t = s.test
                if len(t.ops) == 1 and isinstance(t.ops[0], ast.NotEq):
                    L, R = t.left, t.comparators[0]
                    if isinstance(L, ast.Call) and getattr(L.func, "id", None) == "len" and isinstance(R, ast.Call) and getattr(R.func, "id", None) == "len":
                        a = ast.unparse(L.args[0])
                        b = ast.unparse(R.args[0])
                        src_a = seq_sources.get(a, a)
                        src_b = seq_sources.get(b, b)
                        if src_a == src_b:
                            pass_node = ast.Pass()
                            changes.append(("replace_stmt", fn.name, (stmts, i, []), Change(
                                f"Eliminate dead length guard: `len({a}) != len({b})`",
                                f"`{a}` and `{b}` are both constructed from `{src_a}`, so their lengths are identically equal. The guard is unreachable dead code.",
                                fn.name, ast.unparse(s), "# Dead guard removed")))
    return changes


# ---- T8e: direct join for loop concatenation -----------------------------------
def t_direct_join(tree):
    """original = '' 
 for c in chars: original = original + c  =>  original = ''.join(chars)"""
    changes = []
    for scope in [tree] + [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]:
        stmts = scope.body
        i = 0
        while i < len(stmts) - 1:
            s1 = stmts[i]
            s2 = stmts[i + 1]
            if isinstance(s1, ast.Assign) and len(s1.targets) == 1 and isinstance(s1.targets[0], ast.Name) and isinstance(s1.value, ast.Constant) and s1.value.value == "":
                var = s1.targets[0].id
                if isinstance(s2, ast.For) and isinstance(s2.target, ast.Name) and len(s2.body) == 1 and not s2.orelse:
                    act = s2.body[0]
                    rhs = None
                    if isinstance(act, ast.AugAssign) and isinstance(act.target, ast.Name) and act.target.id == var and isinstance(act.op, ast.Add):
                        rhs = act.value
                    elif isinstance(act, ast.Assign) and len(act.targets) == 1 and isinstance(act.targets[0], ast.Name) and act.targets[0].id == var:
                        v = act.value
                        if isinstance(v, ast.BinOp) and isinstance(v.op, ast.Add) and isinstance(v.left, ast.Name) and v.left.id == var:
                            rhs = v.right
                    if rhs is not None:
                        loop_var = s2.target.id
                        it_src = ast.unparse(s2.iter)
                        rhs_src = ast.unparse(rhs)
                        if rhs_src == loop_var:
                            new_code = f"{var} = ''.join({it_src})"
                        else:
                            new_code = f"{var} = ''.join({rhs_src} for {loop_var} in {it_src})"
                        new_node = ast.parse(new_code).body[0]
                        fn = scope if isinstance(scope, ast.FunctionDef) else None
                        changes.append(("replace_pair", fn.name if fn else None, (stmts, i, new_node), Change(
                            f"Build string `{var}` with `''.join(...)` instead of loop concatenation",
                            f"String concatenation in a loop reallocates and copies the string on each iteration (O(n²) total). `''.join(...)` pre-allocates a single contiguous buffer in C (O(n)).",
                            fn.name if fn else "<module>", _stmts_src([s1, s2]), new_code)))
                        break
            i += 1
    return changes


# ---- T8f: ICPC Fast I/O --------------------------------------------------------
def t_fast_io(tree):
    """input() -> sys.stdin.readline for competitive programming speed."""
    changes = []
    has_input = False
    for n in ast.walk(tree):
        if isinstance(n, ast.Call) and is_name(n.func, "input"):
            has_input = True
            break
    if has_input:
        # Check if sys.stdin.readline is already assigned
        already = any(isinstance(s, ast.Assign) and any(is_name(t, "input") for t in s.targets) for s in tree.body)
        if not already:
            node = ast.parse("import sys\ninput = sys.stdin.readline").body
            changes.append(("insert_top", None, (tree, node), Change(
                "Consider sys.stdin.readline for bulk input (advice only, not measured)",
                "sys.stdin.readline avoids one layer of interpreter overhead per line versus input(). This tool does not measure I/O; the rewrite is never applied automatically because it changes semantics.",
                "<module>", "input()", "import sys; input = sys.stdin.readline", kind="advice")))
    return changes



# ---- T9: string building with += in loop → join ---------------------------------
def t_string_join(tree):
    changes = []
    for scope in [tree] + [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]:
        for _, stmts in iter_stmt_lists(scope):
            for k, s in enumerate(stmts):
                if not (isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name) and isinstance(s.value, ast.Constant) and s.value.value == ""):
                    continue
                name = s.targets[0].id
                # find the next statement (loop) that mentions name via string concatenation
                nxt = None
                for k2 in range(k + 1, len(stmts)):
                    cand = stmts[k2]
                    if isinstance(cand, (ast.For, ast.While)):
                        nxt = cand
                        break
                    if name in node_names(cand):
                        break
                if nxt is None:
                    continue
                # collect string-concat augs in the loop (with their conditioning if any)
                augs = []          # list of (aug_node, rhs_node, if_node|None)
                misuse = False
                for n in ast.walk(nxt):
                    if isinstance(n, ast.AugAssign) and is_name(n.target, name):
                        if not isinstance(n.op, ast.Add):
                            misuse = True
                        else:
                            p = getattr(n, "_parent", None)
                            augs.append((n, n.value, p if isinstance(p, ast.If) else None))
                    elif isinstance(n, ast.Assign) and len(n.targets) == 1 and is_name(n.targets[0], name) and isinstance(n.value, ast.BinOp) and isinstance(n.value.op, ast.Add) and is_name(n.value.left, name):
                        p = getattr(n, "_parent", None)
                        augs.append((n, n.value.right, p if isinstance(p, ast.If) else None))
                    elif isinstance(n, ast.Name) and n.id == name and isinstance(n.ctx, ast.Load):
                        p = getattr(n, "_parent", None)
                        legit = (isinstance(p, ast.AugAssign) and p.target is n) or (isinstance(p, ast.BinOp) and (p.left is n or p.right is n))
                        if not legit:
                            misuse = True
                if misuse or not augs:
                    continue
                if not all(any(len(enclosing_loops(a)) >= 1 for a in (augs[0][0],)) for _ in [0]):
                    continue
                cond_if = augs[0][2]
                cond = cond_if.test if cond_if is not None else None
                consistent = True
                for _, _, ifnode in augs:
                    if (ifnode is None) != (cond_if is None):
                        consistent = False
                    elif ifnode is not None and ast.unparse(ifnode.test) != ast.unparse(cond_if.test):
                        consistent = False
                if not consistent:
                    continue
                if cond is None:
                    # unconditional rewrite (parts list + join)
                    fn = scope if isinstance(scope, ast.FunctionDef) else None
                    used = _all_names(tree)
                    parts = _fresh(f"{name}_parts", used)
                    plain_augs = [a for a, _, _ in augs]
                    changes.append(("strjoin", fn.name if fn else None, (stmts, k, name, parts, plain_augs, nxt), Change(
                        f"Build string `{name}` with a list and `''.join()`",
                        f"`{name} += ...` inside a loop copies the growing string each time (O(n²) in the worst case). Collecting parts in a list and joining once is O(n).",
                        fn.name if fn else "<module>", f"{name} = ''\n...\n{name} += ...", f"{parts} = []\n...\n{parts}.append(...)\n{name} = ''.join({parts})")))
                    continue
                # conditional rewrite: result = ''.join(transform(var) for var in iter if cond)
                if not isinstance(nxt, ast.For) or not isinstance(nxt.target, ast.Name):
                    continue
                if nxt.orelse or nxt.body != [cond_if]:
                    continue
                if name in node_names(cond):
                    continue
                rhs_nodes = [r for _, r, _ in augs]
                if any(name in node_names(r) for r in rhs_nodes):
                    continue
                if len(rhs_nodes) != 1:
                    continue
                if not (len(cond_if.body) == 1 and cond_if.body[0] in [a for a, _, _ in augs]):
                    continue
                loop_var = nxt.target.id
                iter_src = ast.unparse(nxt.iter)
                rhs_src = ast.unparse(rhs_nodes[0])
                if loop_var in node_names(cond) and False:
                    pass
                new_src = f"{name} = ''.join({rhs_src} for {loop_var} in {iter_src} if {ast.unparse(cond)})"
                new_stmt = ast.parse(new_src).body[0]
                changes.append(("replace_pair", scope.name if isinstance(scope, ast.FunctionDef) else None, (stmts, k, new_stmt), Change(
                    f"Build string `{name}` with `''.join()` (conditional)",
                    f"`{name} += ...` inside a conditional inside a loop copies the growing string on every iteration. Collecting the transformed parts in one generator and joining once is O(n).",
                    scope.name if isinstance(scope, ast.FunctionDef) else "<module>", f"{name} = ''\n{ast.unparse(nxt)}", new_src)))
    return changes


def apply_strjoin(tree, payload):
    stmts, k, k2, name, parts, augs, loop = payload
    stmts[k] = ast.parse(f"{parts} = []").body[0]
    for a in augs:
        plist, pidx = _parent_stmt_list(a)
        plist[pidx] = ast.parse(f"{parts}.append(str({ast.unparse(a.value)}))").body[0] if not _is_str_expr(a.value) else ast.parse(f"{parts}.append({ast.unparse(a.value)})").body[0]
    # insert join right after loop
    for i, s in enumerate(stmts):
        if s is loop:
            stmts.insert(i + 1, ast.parse(f"{name} = ''.join({parts})").body[0])
            break


def _is_str_expr(node):
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return True
    if isinstance(node, ast.JoinedStr):
        return True
    if isinstance(node, ast.Call) and call_name(node) in ("str", "chr", ".upper", ".lower", ".join", ".strip", "repr", ".format"):
        return True
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add) and (_is_str_expr(node.left) or _is_str_expr(node.right)):
        return True
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mod) and _is_str_expr(node.left):
        return True
    return False


# ---- T10: list used as queue → deque -------------------------------------------
def t_deque(tree):
    changes = []
    for scope in [tree] + [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]:
        body_stmts = scope.body
        for k, s in enumerate(body_stmts):
            if not (isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name)):
                continue
            if not (isinstance(s.value, ast.List) or (isinstance(s.value, ast.Call) and call_name(s.value) == "list")):
                continue
            name = s.targets[0].id
            front_ops = 0
            ok = True
            for n in ast.walk(scope):
                if isinstance(n, ast.FunctionDef) and n is not scope:
                    continue
                if isinstance(n, ast.Name) and n.id == name:
                    parent = getattr(n, "_parent", None)
                    if parent is s:
                        continue
                    if isinstance(parent, ast.Attribute) and isinstance(getattr(parent, "_parent", None), ast.Call) and parent._parent.func is parent:
                        call = parent._parent
                        attr = parent.attr
                        if attr == "pop" and call.args and is_const_int(call.args[0]) and call.args[0].value == 0:
                            front_ops += 1
                        elif attr == "insert" and len(call.args) == 2 and is_const_int(call.args[0]) and call.args[0].value == 0:
                            front_ops += 1
                        elif attr in ("append", "extend", "popleft", "appendleft", "clear"):
                            pass
                        elif attr == "pop" and not call.args:
                            pass
                        else:
                            ok = False
                    elif isinstance(parent, ast.Call) and is_name(parent.func, "len"):
                        pass
                    elif isinstance(parent, (ast.While, ast.If)) and parent.test is n:
                        pass
                    elif isinstance(parent, ast.UnaryOp) and isinstance(parent.op, ast.Not):
                        pass
                    elif isinstance(parent, ast.For) and parent.iter is n:
                        pass
                    elif isinstance(parent, ast.Subscript) and isinstance(parent.slice, ast.Constant) and parent.slice.value in (0, -1):
                        pass
                    elif isinstance(parent, ast.BoolOp):
                        pass
                    else:
                        ok = False
            if not ok or front_ops == 0:
                continue
            # the front op must be in a loop to matter
            fn = scope if isinstance(scope, ast.FunctionDef) else None
            changes.append(("deque", fn.name if fn else None, (scope, s, name), Change(
                f"Use `collections.deque` for queue `{name}`",
                f"`{name}.pop(0)` / `{name}.insert(0, …)` shift every element (O(n) each). `deque.popleft()` / `appendleft()` are O(1), removing a factor of n from the loop.",
                fn.name if fn else "<module>", f"{name}.pop(0)", f"{name}.popleft()")))
    return changes


def apply_deque(tree, payload):
    scope, s, name = payload
    if isinstance(s.value, ast.List):
        s.value = ast.Call(func=ast.Name(id="deque", ctx=ast.Load()), args=[s.value] if s.value.elts else [], keywords=[])
    else:
        s.value = ast.Call(func=ast.Name(id="deque", ctx=ast.Load()), args=s.value.args, keywords=[])
    for n in ast.walk(scope):
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute) and is_name(n.func.value, name):
            if n.func.attr == "pop" and n.args and is_const_int(n.args[0]) and n.args[0].value == 0:
                n.func.attr = "popleft"
                n.args = []
            elif n.func.attr == "insert" and len(n.args) == 2 and is_const_int(n.args[0]) and n.args[0].value == 0:
                n.func.attr = "appendleft"
                n.args = [n.args[1]]
    _ensure_import(tree, "collections", "deque")


# ---- T11: closed-form arithmetic loops -----------------------------------------
def t_closed_form(tree):
    changes = []
    for scope in [tree] + [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]:
        for _, stmts in iter_stmt_lists(scope):
            for k, s in enumerate(stmts):
                if not (isinstance(s, ast.For) and isinstance(s.target, ast.Name) and len(s.body) == 1 and isinstance(s.body[0], ast.AugAssign) and not s.orelse):
                    continue
                it = s.iter
                if not (isinstance(it, ast.Call) and is_name(it.func, "range") and 1 <= len(it.args) <= 2):
                    continue
                aug = s.body[0]
                if not isinstance(aug.target, ast.Name):
                    continue
                acc, var = aug.target.id, s.target.id
                lo = "0" if len(it.args) == 1 else ast.unparse(it.args[0])
                hi = ast.unparse(it.args[-1])
                fn = scope if isinstance(scope, ast.FunctionDef) else None
                vsrc = ast.unparse(aug.value)
                new = None
                if isinstance(aug.op, ast.Add) and vsrc == var:
                    new = f"{acc} += ({hi} - ({lo})) * (({lo}) + {hi} - 1) // 2 if {hi} > ({lo}) else 0"
                    title = "Arithmetic series in closed form"
                    detail = f"`sum(range({lo}, {hi}))` equals (count × (first + last)) / 2 — a constant-time formula replaces the O(n) loop."
                elif isinstance(aug.op, ast.Add) and vsrc in (f"{var} * {var}", f"{var} ** 2") and lo in ("0", "1"):
                    new = f"{acc} += ({hi} - 1) * {hi} * (2 * {hi} - 1) // 6 if {hi} > 1 else 0"
                    title = "Sum of squares in closed form"
                    detail = "Σ i² = (n−1)·n·(2n−1)/6 — constant time instead of a linear loop."
                elif isinstance(aug.op, ast.Mult) and var not in node_names(aug.value) and acc not in node_names(aug.value) and lo == "0" and _pure(aug.value):
                    new = f"{acc} *= ({vsrc}) ** ({hi}) if {hi} > 0 else 1"
                    title = "Repeated multiplication → exponentiation"
                    detail = "Multiplying by the same factor n times is just `base ** n`, which Python computes with O(log n) squarings."
                elif isinstance(aug.op, ast.Add) and var not in node_names(aug.value) and acc not in node_names(aug.value) and _pure(aug.value):
                    new = f"{acc} += ({vsrc}) * ({hi} - ({lo})) if {hi} > ({lo}) else 0"
                    title = "Repeated addition → multiplication"
                    detail = "Adding a loop-invariant value n times is `value * n`: O(n) → O(1)."
                if new is None:
                    continue
                new_stmt = ast.parse(new).body[0]
                changes.append(("replace_stmt", fn.name if fn else None, (stmts, k, [new_stmt]), Change(
                    title, detail, fn.name if fn else "<module>", ast.unparse(s), new)))
    return changes


# ---- T12: idiomatic constant-factor rewrites ----------------------------------
def t_idioms(tree):
    changes = []
    # x in d.keys()  -> x in d
    for cmp_node in [n for n in ast.walk(tree) if isinstance(n, ast.Compare)]:
        if len(cmp_node.ops) == 1 and isinstance(cmp_node.ops[0], (ast.In, ast.NotIn)):
            rhs = cmp_node.comparators[0]
            if isinstance(rhs, ast.Call) and call_name(rhs) == ".keys" and not rhs.args:
                fn = _enclosing_function(cmp_node)
                changes.append(("keys", fn.name if fn else None, (cmp_node, rhs.func.value), Change(
                    "`x in d.keys()` → `x in d`", "Dictionary membership is already a hash lookup; `.keys()` creates an unnecessary view object.",
                    fn.name if fn else "<module>", ast.unparse(cmp_node), ast.unparse(cmp_node).replace(".keys()", ""), kind="constant")))
            elif isinstance(rhs, (ast.List, ast.Tuple)) and len(rhs.elts) >= 3 and all(isinstance(e, ast.Constant) and not isinstance(e.value, float) for e in rhs.elts) and enclosing_loops(cmp_node):
                fn = _enclosing_function(cmp_node)
                changes.append(("literal_set", fn.name if fn else None, (cmp_node, rhs), Change(
                    "Membership in a literal list → set literal", "Checking membership in a constant list is a linear scan; a set literal is hashed and folded into a constant by the compiler.",
                    fn.name if fn else "<module>", ast.unparse(cmp_node), ast.unparse(cmp_node).replace(ast.unparse(rhs), "{" + ", ".join(ast.unparse(e) for e in rhs.elts) + "}"), kind="constant")))
    # accumulation loops
    for scope in [tree] + [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]:
        for _, stmts in iter_stmt_lists(scope):
            for k in range(len(stmts) - 1):
                init, lp = stmts[k], stmts[k + 1]
                if not (isinstance(init, ast.Assign) and len(init.targets) == 1 and isinstance(init.targets[0], ast.Name) and isinstance(lp, ast.For) and not lp.orelse):
                    continue
                acc = init.targets[0].id
                fn = scope if isinstance(scope, ast.FunctionDef) else None
                tgt = ast.unparse(lp.target)
                it = ast.unparse(lp.iter)
                if acc in node_names(lp.iter) or acc in node_names(lp.target):
                    continue
                body = lp.body
                cond = None
                if len(body) == 1 and isinstance(body[0], ast.If) and not body[0].orelse and len(body[0].body) == 1:
                    cond = ast.unparse(body[0].test)
                    inner = body[0].body[0]
                    if acc in node_names(body[0].test):
                        continue
                elif len(body) == 1:
                    inner = body[0]
                else:
                    continue
                suffix = f" for {tgt} in {it}" + (f" if {cond}" if cond else "")
                new = None
                # sum
                if isinstance(init.value, ast.Constant) and init.value.value == 0 and isinstance(inner, ast.AugAssign) and is_name(inner.target, acc) and isinstance(inner.op, ast.Add) and acc not in node_names(inner.value):
                    v = ast.unparse(inner.value)
                    if not _pure(inner.value):
                        continue
                    if any(isinstance(x, ast.Constant) and isinstance(x.value, float) for x in ast.walk(inner.value)):
                        continue
                    if v == tgt and not cond:
                        new = f"{acc} = sum({it})"
                    else:
                        new = f"{acc} = sum([{v}{suffix}])"
                    title, detail = "Accumulation loop → `sum()`", "The built-in `sum` iterates in C, avoiding per-iteration bytecode dispatch."
                # list append
                elif isinstance(init.value, ast.List) and not init.value.elts and isinstance(inner, ast.Expr) and isinstance(inner.value, ast.Call) and call_name(inner.value) == ".append" and is_name(inner.value.func.value, acc) and len(inner.value.args) == 1 and acc not in node_names(inner.value.args[0]):
                    v = ast.unparse(inner.value.args[0])
                    new = f"{acc} = [{v}{suffix}]"
                    title, detail = "Append loop → list comprehension", "List comprehensions build the list with a specialised bytecode path (~30% faster) and avoid repeated attribute lookups."
                # any()
                elif (isinstance(init.value, ast.Constant) and init.value.value is False and isinstance(inner, ast.Assign) and len(inner.targets) == 1 and is_name(inner.targets[0], acc) and isinstance(inner.value, ast.Constant) and inner.value.value is True and cond):
                    new = f"{acc} = any({cond} for {tgt} in {it})"
                    title, detail = "Flag loop → `any()`", "`any` short-circuits in C as soon as the condition is met."
                if new is None:
                    continue
                new_stmt = ast.parse(new).body[0]
                changes.append(("replace_pair", fn.name if fn else None, (stmts, k, new_stmt), Change(
                    title, detail, fn.name if fn else "<module>", _stmts_src([init, lp]), new, kind="constant")))
    # linear search for max/min
    return changes


# ==========================================================================
# Layer 1 — algorithm library
#   * template unification engine (metavariables `Q_*`)
#   * linear-inequality prover (proves 0 <= lo <= hi <= len(a) from loop bounds)
#   * prefix-sum / sliding-window rewriting
#   * namespace helpers, paired benchmarking and A/B regression guard
# ==========================================================================

# ---- purity / alias / name-flow helpers -----------------------------------
def _is_pure_expr(node):
    for n in ast.walk(node):
        if isinstance(n, (ast.Name, ast.Constant, ast.BinOp, ast.UnaryOp, ast.operator, ast.unaryop, ast.expr_context)):
            continue
        if isinstance(n, ast.Call) and is_name(n.func, "len") and len(n.args) == 1 and isinstance(n.args[0], ast.Name):
            continue
        return False
    return True


def _scope_assign_counts(scope):
    counts = {}

    def add(t):
        for s in ast.walk(t):
            if isinstance(s, ast.Name):
                counts[s.id] = counts.get(s.id, 0) + 1

    for n in ast.walk(scope):
        if isinstance(n, ast.Assign):
            for t in n.targets:
                add(t)
        elif isinstance(n, (ast.AugAssign, ast.AnnAssign)):
            add(n.target)
        elif isinstance(n, (ast.For, ast.comprehension)):
            add(n.target)
        elif isinstance(n, ast.NamedExpr):
            add(n.target)
    return counts


def len_aliases(scope):
    """{name: array} for `n = len(a)` when n is assigned once and `a` is never mutated/rebound in scope."""
    counts = _scope_assign_counts(scope)
    written = mutated_names(scope)
    params = set()
    if isinstance(scope, ast.FunctionDef):
        params = {a.arg for a in scope.args.args + scope.args.kwonlyargs}
    out = {}
    for n in ast.walk(scope):
        if isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name):
            v = n.value
            if isinstance(v, ast.Call) and is_name(v.func, "len") and len(v.args) == 1 and isinstance(v.args[0], ast.Name):
                name, arr = n.targets[0].id, v.args[0].id
                if counts.get(name, 0) == 1 and name not in params and arr not in written and counts.get(arr, 0) <= 1:
                    out[name] = arr
    return out


def _is_len_of(expr, arr, alias):
    if isinstance(expr, ast.Call) and is_name(expr.func, "len") and len(expr.args) == 1 and is_name(expr.args[0], arr):
        return True
    return isinstance(expr, ast.Name) and alias.get(expr.id) == arr


def _ancestors(node):
    cur = getattr(node, "_parent", None)
    while cur is not None:
        yield cur
        cur = getattr(cur, "_parent", None)


def _names_used_after(scope, region, names):
    """Conservative: is any of `names` read after the region (or elsewhere inside an enclosing loop)?"""
    region_ids = {id(x) for r in region for x in ast.walk(r)}
    end = max(getattr(n, "end_lineno", 0) or 0 for n in region)
    for n in ast.walk(scope):
        if isinstance(n, ast.Name) and n.id in names and isinstance(n.ctx, ast.Load) and id(n) not in region_ids:
            if (getattr(n, "lineno", 0) or 0) > end:
                return True
    loops = enclosing_loops(region[0])
    if loops:
        outer = loops[-1]
        for n in ast.walk(outer):
            if isinstance(n, ast.Name) and n.id in names and isinstance(n.ctx, ast.Load) and id(n) not in region_ids:
                return True
    return False


def _replace_node(root, old, new):
    for parent in ast.walk(root):
        for field, value in ast.iter_fields(parent):
            if value is old:
                setattr(parent, field, new)
                return True
            if isinstance(value, list):
                for i, item in enumerate(value):
                    if item is old:
                        value[i] = new
                        return True
    return False


# ---- linear forms + inequality prover ---------------------------------------
def lin_add(a, b, sign=1):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, 0) + sign * v
    return out


def lin_parse(node, alias):
    """expr -> {symbol: coeff, '#': const}  (None if not affine)"""
    if isinstance(node, ast.Constant) and isinstance(node.value, int) and not isinstance(node.value, bool):
        return {"#": node.value}
    if isinstance(node, ast.Name):
        if node.id in alias:
            return {"len:" + alias[node.id]: 1}
        return {node.id: 1}
    if isinstance(node, ast.Call) and is_name(node.func, "len") and len(node.args) == 1 and isinstance(node.args[0], ast.Name):
        return {"len:" + node.args[0].id: 1}
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        f = lin_parse(node.operand, alias)
        return None if f is None else {k: -v for k, v in f.items()}
    if isinstance(node, ast.BinOp):
        l, r = lin_parse(node.left, alias), lin_parse(node.right, alias)
        if l is None or r is None:
            return None
        if isinstance(node.op, ast.Add):
            return lin_add(l, r, 1)
        if isinstance(node.op, ast.Sub):
            return lin_add(l, r, -1)
        if isinstance(node.op, ast.Mult):
            if set(l) <= {"#"}:
                return {k: v * l.get("#", 0) for k, v in r.items()}
            if set(r) <= {"#"}:
                return {k: v * r.get("#", 0) for k, v in l.items()}
    return None


def loop_bounds(node, alias, scope):
    """Facts from enclosing `for v in range(..)` loops: v >= lo, v <= hi.  Innermost loop first."""
    counts = _scope_assign_counts(scope)
    order, bounds = [], {}
    loop_vars = set()
    cand = []
    for lp in enclosing_loops(node):
        if not (isinstance(lp, ast.For) and isinstance(lp.target, ast.Name)):
            continue
        it = lp.iter
        if not (isinstance(it, ast.Call) and is_name(it.func, "range") and 1 <= len(it.args) <= 3 and not it.keywords):
            continue
        v = lp.target.id
        if v in names_written(ast.Module(body=lp.body, type_ignores=[])) or v in loop_vars:
            continue
        a = it.args
        if len(a) == 3 and not (is_const_int(a[2]) and a[2].value > 0):
            continue
        start = lin_parse(a[0], alias) if len(a) >= 2 else {"#": 0}
        stop = lin_parse(a[1] if len(a) >= 2 else a[0], alias)
        hi = None if stop is None else lin_add(stop, {"#": 1}, -1)
        loop_vars.add(v)
        cand.append((v, start, hi))
    for v, lo, hi in cand:
        def stable(f):
            if f is None:
                return None
            for s in f:
                if s == "#" or s.startswith("len:") or s in loop_vars:
                    continue
                if counts.get(s, 0) == 0:  # parameter / global never rebound here
                    continue
                return None
            return f
        bounds[v] = (stable(lo), stable(hi))
        order.append(v)
    return order, bounds


from fractions import Fraction


def lin_src(f):
    """Render a linear form {sym: coeff, '#': const} as Python source."""
    parts = []
    for s in sorted((k for k in f if k != "#" and f[k] != 0), key=lambda k: (k.startswith("len:"), k)):
        c = f[s]
        c = int(c) if float(c).is_integer() else c
        name = f"len({s[4:]})" if s.startswith("len:") else s
        mag = abs(c)
        parts.append(("-" if c < 0 else "+", name if mag == 1 else f"{mag} * {name}"))
    const = f.get("#", 0)
    const = int(const) if float(const).is_integer() else const
    if const or not parts:
        parts.append(("-" if const < 0 else "+", str(abs(const))))
    out = ""
    for i, (sign, term) in enumerate(parts):
        out = (("-" if sign == "-" else "") + term) if i == 0 else out + f" {sign} {term}"
    return out


def _cmp_leaves(test):
    if not isinstance(test, ast.Compare):
        return []
    parts = [test.left] + list(test.comparators)
    return list(zip(parts, test.ops, parts[1:]))


def _m1(f):
    g = dict(f)
    g["#"] = g.get("#", 0) - 1
    return g


def _neg(f):
    return {k: -v for k, v in f.items()}


_FLIP = {ast.Lt: ast.GtE, ast.LtE: ast.Gt, ast.Gt: ast.LtE, ast.GtE: ast.Lt, ast.Eq: ast.NotEq, ast.NotEq: ast.Eq}


def _leaf_forms(L, op, R, alias, positive=True):
    """Linear facts (each form >= 0) implied by `L op R` (or by its negation).  Integer semantics."""
    lf, rf = lin_parse(L, alias), lin_parse(R, alias)
    if lf is None or rf is None:
        return []
    d = lin_add(lf, rf, -1)
    nd = _neg(d)
    t = type(op) if positive else _FLIP.get(type(op))
    if t is ast.Lt:
        return [_m1(nd)]
    if t is ast.LtE:
        return [nd]
    if t is ast.Gt:
        return [_m1(d)]
    if t is ast.GtE:
        return [d]
    if t is ast.Eq:
        return [d, nd]
    if t is ast.NotEq:
        syms = [k for k, v in d.items() if k != "#" and v != 0]
        if len(syms) == 1 and syms[0].startswith("len:") and d.get("#", 0) == 0:   # len(x) != 0  =>  len(x) >= 1
            return [_m1(d)] if d[syms[0]] == 1 else ([_m1(nd)] if d[syms[0]] == -1 else [])
    return []


def test_facts(test, alias, positive=True):
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        return test_facts(test.operand, alias, not positive)
    if isinstance(test, ast.BoolOp):
        if (isinstance(test.op, ast.And) and positive) or (isinstance(test.op, ast.Or) and not positive):
            out = []
            for v in test.values:
                out += test_facts(v, alias, positive)
            return out
        return []
    if isinstance(test, ast.Name):
        return [{"len:" + test.id: 1, "#": -1}] if positive else []    # truthy sequence => len >= 1
    if isinstance(test, ast.Compare):
        leaves = _cmp_leaves(test)
        if positive:
            out = []
            for L, op, R in leaves:
                out += _leaf_forms(L, op, R, alias, True)
            return out
        if len(leaves) == 1:
            return _leaf_forms(leaves[0][0], leaves[0][1], leaves[0][2], alias, False)
    return []


def _exits(stmts):
    return bool(stmts) and isinstance(stmts[-1], (ast.Return, ast.Raise, ast.Continue, ast.Break))


def collect_facts(node, alias):
    """Facts that hold at `node`: earlier `if C: return/raise`, asserts, enclosing if/else/ternary branches."""
    facts = []
    cur = node
    while True:
        parent = getattr(cur, "_parent", None)
        if parent is None:
            break
        if isinstance(parent, ast.IfExp):
            if cur is parent.body:
                facts += test_facts(parent.test, alias, True)
            elif cur is parent.orelse:
                facts += test_facts(parent.test, alias, False)
        for field, lst in iter_stmt_lists(parent):
            idx = next((i for i, st in enumerate(lst) if st is cur), None)
            if idx is None:
                continue
            for q in lst[:idx]:
                if isinstance(q, ast.If) and _exits(q.body) and not q.orelse:
                    facts += test_facts(q.test, alias, False)
                elif isinstance(q, ast.Assert):
                    facts += test_facts(q.test, alias, True)
            if isinstance(parent, ast.If) and field in ("body", "orelse"):
                facts += test_facts(parent.test, alias, field == "body")
        if isinstance(parent, (ast.FunctionDef, ast.Lambda)):
            break
        cur = parent
    return facts


def _stable_facts(facts, scope):
    """Keep only facts about names that are never rebound / containers that are never mutated in scope."""
    counts = _scope_assign_counts(scope)
    mut = mutated_names(scope)
    out = []
    for f in facts:
        ok = True
        for s, cf in f.items():
            if s == "#" or cf == 0:
                continue
            base = s[4:] if s.startswith("len:") else s
            if counts.get(base, 0) > 0 or (s.startswith("len:") and base in mut):
                ok = False
        if ok:
            out.append(f)
    return out


def prove_nonneg(form, order, bounds, allow_zero=True, strict=False, facts=()):
    f = dict(form)
    for _ in range(40):
        syms = [s for s, c in f.items() if s != "#" and c != 0]
        if not syms:
            return f.get("#", 0) > 0 if strict else f.get("#", 0) >= 0
        pick = None
        for v in order:
            if v in syms and bounds[v][0 if f[v] > 0 else 1] is not None:
                pick = v
                break
        if pick is None:
            return _prove_with_facts(f, facts, strict)
        c = f.pop(pick)
        repl = bounds[pick][0 if c > 0 else 1]
        for k, val in repl.items():
            f[k] = f.get(k, 0) + c * val
    return False


def _prove_with_facts(f, facts, strict, depth=0):
    f = {k: v for k, v in f.items() if v != 0 or k == "#"}
    syms = [s for s in f if s != "#"]
    const = f.get("#", 0)
    if not syms:
        return const > 0 if strict else const >= 0
    if all(s.startswith("len:") and f[s] > 0 for s in syms) and (const > 0 if strict else const >= 0):
        return True                                   # len(x) >= 0 always
    if depth >= 6:
        return False
    for s in syms:
        c = f[s]
        for g in facts:
            gs = g.get(s, 0)
            if gs == 0:
                continue
            lam = Fraction(c) / Fraction(gs)
            if lam <= 0:
                continue
            f2 = dict(f)
            for kk, vv in g.items():
                f2[kk] = f2.get(kk, 0) - lam * vv
            f2[s] = 0
            if _prove_with_facts(f2, facts, strict, depth + 1):
                return True
    return False


def prove_leaf(L, op, R, alias, order, bounds, facts, mut=frozenset()):
    """True / False if `L op R` is provably true / false at this point, else None."""
    lf, rf = lin_parse(L, alias), lin_parse(R, alias)
    if lf is None or rf is None:
        return None
    if any(s.startswith("len:") and s[4:] in mut for s in list(lf) + list(rf)):
        return None
    d = lin_add(lf, rf, -1)
    nd = _neg(d)

    def P(f):
        return prove_nonneg(f, order, bounds, facts=facts)
    t = type(op)
    if t is ast.Lt:
        tr, fl = P(_m1(nd)), P(d)
    elif t is ast.LtE:
        tr, fl = P(nd), P(_m1(d))
    elif t is ast.Gt:
        tr, fl = P(_m1(d)), P(nd)
    elif t is ast.GtE:
        tr, fl = P(d), P(_m1(nd))
    elif t is ast.Eq:
        tr, fl = (P(d) and P(nd)), (P(_m1(d)) or P(_m1(nd)))
    elif t is ast.NotEq:
        tr, fl = (P(_m1(d)) or P(_m1(nd))), (P(d) and P(nd))
    else:
        return None
    return True if tr else (False if fl else None)


def simplify_guard(test, node, alias, scope):
    """Use loop bounds + dominating guards to simplify `test` at `node`.
    Returns (mode, dropped_conjuncts, extra): mode in keep|true|false|new."""
    order, bounds = loop_bounds(node, alias, scope)
    facts = _stable_facts(collect_facts(node, alias), scope)
    mut = mutated_names(scope)
    conj = list(test.values) if isinstance(test, ast.BoolOp) and isinstance(test.op, ast.And) else [test]
    kept, dropped = [], []
    for c in conj:
        leaves = _cmp_leaves(c)
        if not leaves:
            kept.append(c)
            continue
        verdicts = [prove_leaf(a, op, b, alias, order, bounds, facts, mut) for a, op, b in leaves]
        if any(v is False for v in verdicts):
            return "false", [], ast.unparse(c)
        if all(v is True for v in verdicts):
            dropped.append(ast.unparse(c))
            continue
        if len(leaves) > 1 and all(_is_pure_expr(a) and _is_pure_expr(b) for a, _, b in leaves):
            for (a, op, b), v in zip(leaves, verdicts):
                leaf = ast.Compare(left=a, ops=[op], comparators=[b])
                if v is True:
                    dropped.append(ast.unparse(leaf))
                else:
                    kept.append(leaf)
        else:
            kept.append(c)
    if not dropped:
        return "keep", [], None
    if not kept:
        return "true", dropped, None
    return "new", dropped, (kept[0] if len(kept) == 1 else ast.BoolOp(op=ast.And(), values=kept))


# ---- template unification engine ----------------------------------------------
def _is_mv(n):
    return isinstance(n, ast.Name) and n.id.startswith("Q_")


def unify(p, n, b):
    """Structural match of pattern AST `p` against code AST `n`; `Q_*` names are metavariables."""
    if _is_mv(p):
        if p.id in b:
            return ast.unparse(b[p.id]) == ast.unparse(n)
        b[p.id] = n
        return True
    if isinstance(p, list):
        return isinstance(n, list) and len(p) == len(n) and all(unify(x, y, b) for x, y in zip(p, n))
    if isinstance(p, ast.AST):
        if (isinstance(p, ast.AugAssign) and isinstance(p.op, ast.Add) and isinstance(n, ast.Assign)
                and len(n.targets) == 1 and isinstance(n.value, ast.BinOp) and isinstance(n.value.op, ast.Add)):
            return unify(p.target, n.targets[0], b) and unify(p.target, n.value.left, b) and unify(p.value, n.value.right, b)
        if type(p) is not type(n):
            return False
        for f in p._fields:
            if f in ("ctx", "type_comment"):
                continue
            if not unify(getattr(p, f, None), getattr(n, f, None), b):
                return False
        return True
    return p == n and type(p) is type(n)


def _pat(lines):
    return ast.parse("\n".join(lines)).body


def _upd_variants(expr, ind):
    pad = " " * ind
    return [
        [f"{pad}if {expr} > Q_best:", f"{pad}    Q_best = {expr}"],
        [f"{pad}Q_best = max(Q_best, {expr})"],
        [f"{pad}Q_best = max({expr}, Q_best)"],
    ]


def _kadane_patterns():
    pats = []
    for form in ("incl", "excl"):
        if form == "incl":
            jl, kl, sl, run = "    for Q_j in range(Q_i, Q_N2):", "range(Q_i, Q_j + 1)", "Q_A[Q_i:Q_j + 1]", "Q_A[Q_j]"
        else:
            jl, kl, sl, run = "    for Q_j in range(Q_i + 1, Q_N2 + 1):", "range(Q_i, Q_j)", "Q_A[Q_i:Q_j]", "Q_A[Q_j - 1]"
        outer = "for Q_i in range(Q_N1):"
        for upd in _upd_variants("Q_s", 8):
            pats.append(("cubic loop", _pat([outer, jl, "        Q_s = 0", f"        for Q_k in {kl}:", "            Q_s += Q_A[Q_k]"] + upd)))
            pats.append(("cubic sum()", _pat([outer, jl, f"        Q_s = sum(Q_A[Q_k] for Q_k in {kl})"] + upd)))
            pats.append(("slice sum", _pat([outer, jl, f"        Q_s = sum({sl})"] + upd)))
        for upd in _upd_variants("Q_s", 8):
            pats.append(("running sum", _pat([outer, "    Q_s = 0", jl, f"        Q_s += {run}"] + upd)))
        for upd in _upd_variants(f"sum({sl})", 8):
            pats.append(("inline slice sum", _pat([outer, jl] + upd)))
    return pats


def _kadane_check(b, scope, alias, region):
    A = b.get("Q_A")
    if not isinstance(A, ast.Name):
        return False
    for key in ("Q_N1", "Q_N2"):
        if key in b and not _is_len_of(b[key], A.id, alias):
            return False
    loopvars = []
    for key in ("Q_i", "Q_j", "Q_k", "Q_s"):
        if key in b:
            if not isinstance(b[key], ast.Name):
                return False
            loopvars.append(b[key].id)
    if len(set(loopvars)) != len(loopvars) or A.id in loopvars:
        return False
    best = b["Q_best"]
    if node_names(best) & set(loopvars):
        return False
    return not _names_used_after(scope, region, set(loopvars))


def _kadane_build(b, used):
    A = b["Q_A"].id
    best = ast.unparse(b["Q_best"])
    cur, x = _fresh("cur", used), _fresh("x", used)
    return ast.parse(
        f"{cur} = 0\nfor {x} in {A}:\n    {cur} = {x} + ({cur} if {cur} > 0 else 0)\n"
        f"    if {cur} > {best}:\n        {best} = {cur}").body


def _lis_patterns():
    pats = []
    for strict in (True, False):
        op, flip = ("<", ">") if strict else ("<=", ">=")
        conds = [f"Q_A[Q_j] {op} Q_A[Q_i]", f"Q_A[Q_i] {flip} Q_A[Q_j]"]
        for init in ("Q_dp = [1] * Q_N", "Q_dp = [1 for _ in range(Q_N)]"):
            for iloop in ("for Q_i in range(Q_N):", "for Q_i in range(1, Q_N):"):
                for cond in conds:
                    for upd in range(2):
                        if upd == 0:
                            body = [f"        if {cond}:", "            Q_dp[Q_i] = max(Q_dp[Q_i], Q_dp[Q_j] + 1)"]
                        else:
                            body = [f"        if {cond} and Q_dp[Q_j] + 1 > Q_dp[Q_i]:", "            Q_dp[Q_i] = Q_dp[Q_j] + 1"]
                        for ret in ("raise", "default", "ifelse"):
                            rl = {"raise": "return max(Q_dp)", "default": "return max(Q_dp, default=Q_D)",
                                  "ifelse": "return max(Q_dp) if Q_dp else Q_D"}[ret]
                            lines = [init, iloop, "    for Q_j in range(Q_i):"] + body + [rl]
                            pats.append(((strict, ret), _pat(lines)))
    return pats


def _lis_check(b, scope, alias, region):
    A = b.get("Q_A")
    if not isinstance(A, ast.Name) or not _is_len_of(b["Q_N"], A.id, alias):
        return False
    names = [b[k].id for k in ("Q_dp", "Q_i", "Q_j") if isinstance(b.get(k), ast.Name)]
    if len(names) != 3 or len(set(names)) != 3 or A.id in names:
        return False
    return True


def _lis_build(b, used, info):
    strict, ret = info
    A = b["Q_A"].id
    tails, x, pos = _fresh("tails", used), _fresh("x", used), _fresh("pos", used)
    fn = "bisect_left" if strict else "bisect_right"
    core = (f"{tails} = []\nfor {x} in {A}:\n    {pos} = bisect.{fn}({tails}, {x})\n"
            f"    if {pos} == len({tails}):\n        {tails}.append({x})\n    else:\n        {tails}[{pos}] = {x}\n")
    if ret == "raise":
        core = f"if len({A}) == 0:\n    raise ValueError('max() arg is an empty sequence')\n" + core + f"return len({tails})"
    else:
        d = ast.unparse(b["Q_D"])
        core += f"return len({tails}) if {A} else {d}"
    return ast.parse(core).body


def _sumk_patterns():
    pats = []
    for form in ("incl", "excl"):
        if form == "incl":
            jl, kl, sl, run = "    for Q_j in range(Q_i, Q_N2):", "range(Q_i, Q_j + 1)", "Q_A[Q_i:Q_j + 1]", "Q_A[Q_j]"
        else:
            jl, kl, sl, run = "    for Q_j in range(Q_i + 1, Q_N2 + 1):", "range(Q_i, Q_j)", "Q_A[Q_i:Q_j]", "Q_A[Q_j - 1]"
        head = ["Q_c = 0", "for Q_i in range(Q_N1):"]
        for flip in (False, True):
            def ifl(x, flip=flip):
                return [f"        if {('Q_K == ' + x) if flip else (x + ' == Q_K')}:", "            Q_c += 1"]
            pats.append(("slice sum", _pat(head + [jl, f"        Q_s = sum({sl})"] + ifl("Q_s"))))
            pats.append(("cubic loop", _pat(head + [jl, "        Q_s = 0", f"        for Q_k in {kl}:", "            Q_s += Q_A[Q_k]"] + ifl("Q_s"))))
            pats.append(("cubic sum()", _pat(head + [jl, f"        Q_s = sum(Q_A[Q_k] for Q_k in {kl})"] + ifl("Q_s"))))
            pats.append(("running sum", _pat(head + ["    Q_s = 0", jl, f"        Q_s += {run}"] + ifl("Q_s"))))
            pats.append(("inline slice sum", _pat(head + [jl] + ifl(f"sum({sl})"))))
    return pats


def _sumk_check(b, scope, alias, region):
    A, C = b.get("Q_A"), b.get("Q_c")
    if not (isinstance(A, ast.Name) and isinstance(C, ast.Name)):
        return False
    for key in ("Q_N1", "Q_N2"):
        if key in b and not _is_len_of(b[key], A.id, alias):
            return False
    loopvars = []
    for key in ("Q_i", "Q_j", "Q_k", "Q_s"):
        if key in b:
            if not isinstance(b[key], ast.Name):
                return False
            loopvars.append(b[key].id)
    names = loopvars + [C.id]
    if len(set(names)) != len(names) or A.id in names:
        return False
    K = b["Q_K"]
    written = names_written(ast.Module(body=list(region), type_ignores=[]))
    if not _is_pure_expr(K) or (node_names(K) & written) or A.id in written:
        return False
    return not _names_used_after(scope, region, set(loopvars))


def _sumk_build(b, used, info):
    A, C, K = b["Q_A"].id, b["Q_c"].id, ast.unparse(b["Q_K"])
    seen, pref, x = _fresh("seen", used), _fresh("pref", used), _fresh("x", used)
    return ast.parse(f"{C} = 0\n{seen} = collections.Counter({{0: 1}})\n{pref} = 0\nfor {x} in {A}:\n"
                     f"    {pref} += {x}\n    {C} += {seen}[{pref} - {K}]\n    {seen}[{pref}] += 1").body


_ALGO_TEMPLATES = None


def _algo_templates():
    global _ALGO_TEMPLATES
    if _ALGO_TEMPLATES is None:
        t = []
        for label, pat in _kadane_patterns():
            t.append({
                "pattern": pat, "check": _kadane_check, "build": lambda b, used, info=None: _kadane_build(b, used),
                "imports": [], "info": label,
                "title": "Max-subarray brute force → Kadane's algorithm",
                "detail": ("Recognised the all-subarrays scan (" + label + "). The best sum ending at each element is "
                           "cur = x + max(0, cur_prev), and the maximum over all non-empty subarrays is the maximum of those values. "
                           "The initial value of the result variable is left untouched, so empty-input and negative-only behaviour are preserved."),
            })
        for info, pat in _lis_patterns():
            t.append({
                "pattern": pat, "check": _lis_check, "build": _lis_build, "imports": ["bisect"], "info": info,
                "title": "O(n²) LIS dynamic programme → patience sorting with bisect",
                "detail": ("dp[i] = 1 + max dp[j] over earlier smaller elements is the textbook quadratic LIS. Keeping the smallest tail of an "
                           "increasing subsequence of every length and binary-searching it gives the same length in O(n log n)."),
            })
        for label, pat in _sumk_patterns():
            t.append({"pattern": pat, "check": _sumk_check, "build": _sumk_build, "imports": ["collections"], "info": label,
                      "title": "Subarray sum == K → Counter of prefix sums (O(n))",
                      "detail": ("A subarray a[i..j] sums to K iff prefix[j+1] - prefix[i] == K. One pass keeps a Counter of the prefix sums seen so far "
                                 "and adds seen[prefix - K] for each element: O(n) instead of O(n²)/O(n³). Matched shape: " + label + ". "
                                 "Exact for ints; with floats equality of differences of prefix sums can differ from direct sums.")})
        _ALGO_TEMPLATES = t
    return _ALGO_TEMPLATES


def t_algo_templates(tree):
    changes = []
    scopes = [tree] + [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]
    for scope in scopes:
        fn = scope if isinstance(scope, ast.FunctionDef) else None
        alias = len_aliases(scope)
        for tpl in _algo_templates():
            pat = tpl["pattern"]
            L = len(pat)
            for node in ast.walk(scope):
                for _, lst in iter_stmt_lists(node):
                    for st in range(len(lst) - L + 1):
                        region = lst[st:st + L]
                        if _enclosing_function(region[0]) is not fn:
                            continue
                        b = {}
                        if not unify(pat, region, b):
                            continue
                        if not tpl["check"](b, scope, alias, region):
                            continue
                        new_stmts = tpl["build"](b, _all_names(tree), tpl["info"])
                        changes.append(("replace_region", fn.name if fn else None,
                                        (lst, st, L, new_stmts, tpl["imports"]),
                                        Change(tpl["title"], tpl["detail"], fn.name if fn else "<module>",
                                               _stmts_src(region), _stmts_src(new_stmts))))
    return changes


# ---- prefix sums / sliding windows ----------------------------------------------
def _range_args(it):
    if isinstance(it, ast.Call) and is_name(it.func, "range") and not it.keywords:
        if len(it.args) == 1:
            return ast.Constant(value=0), it.args[0]
        if len(it.args) == 2:
            return it.args[0], it.args[1]
    return None


def _find_prefix_var(scope, A):
    want = f"list(itertools.accumulate({A}, initial=0))"
    for n in ast.walk(scope):
        if isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name) and ast.unparse(n.value) == want:
            return n.targets[0].id, n
    return None, None


def _ind(src, n=1):
    pad = "    " * n
    return "\n".join(pad + ln if ln.strip() else ln for ln in src.split("\n"))


def t_prefix_sum(tree):
    """sum(a[lo:hi]) / `s = 0; for k in range(lo, hi): s += a[k]` inside loops → prefix array lookups.
    Guard conjuncts (0 <= lo, lo <= hi, hi <= len(a)) are proven from loop bounds and dominating guards;
    only the unproven ones remain as a runtime check."""
    changes = []
    scopes = [tree] + [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]
    for scope in scopes:
        fn = scope if isinstance(scope, ast.FunctionDef) else None
        alias = len_aliases(scope)
        mut = mutated_names(scope)
        cands = []
        for call in ast.walk(scope):
            if not (isinstance(call, ast.Call) and is_name(call.func, "sum") and len(call.args) == 1 and not call.keywords):
                continue
            if _enclosing_function(call) is not fn:
                continue
            arg = call.args[0]
            A = lo = hi = None
            if isinstance(arg, ast.Subscript) and isinstance(arg.value, ast.Name) and isinstance(arg.slice, ast.Slice) and arg.slice.step is None:
                A = arg.value.id
                lo = arg.slice.lower if arg.slice.lower is not None else ast.Constant(value=0)
                hi = arg.slice.upper if arg.slice.upper is not None else ast.Call(func=ast.Name(id="len", ctx=ast.Load()), args=[ast.Name(id=A, ctx=ast.Load())], keywords=[])
            elif isinstance(arg, ast.GeneratorExp) and len(arg.generators) == 1 and not arg.generators[0].ifs and not arg.generators[0].is_async:
                g = arg.generators[0]
                ra = _range_args(g.iter)
                if (ra and isinstance(g.target, ast.Name) and isinstance(arg.elt, ast.Subscript) and isinstance(arg.elt.value, ast.Name)
                        and is_name(arg.elt.slice, g.target.id)):
                    A = arg.elt.value.id
                    lo, hi = ra
            if A is not None:
                cands.append(("expr", call, A, lo, hi, None))
        for node in ast.walk(scope):
            for _, lst in iter_stmt_lists(node):
                for k in range(len(lst) - 1):
                    init, lp = lst[k], lst[k + 1]
                    if _enclosing_function(init) is not fn:
                        continue
                    if not (isinstance(init, ast.Assign) and len(init.targets) == 1 and isinstance(init.targets[0], ast.Name)
                            and isinstance(init.value, ast.Constant) and isinstance(init.value.value, (int, float)) and not isinstance(init.value.value, bool)):
                        continue
                    s = init.targets[0].id
                    if not (isinstance(lp, ast.For) and isinstance(lp.target, ast.Name) and not lp.orelse and len(lp.body) == 1):
                        continue
                    ra = _range_args(lp.iter)
                    body, kv = lp.body[0], lp.target.id
                    if ra is None:
                        continue
                    if isinstance(body, ast.AugAssign) and isinstance(body.op, ast.Add) and is_name(body.target, s):
                        val = body.value
                    elif (isinstance(body, ast.Assign) and len(body.targets) == 1 and is_name(body.targets[0], s)
                          and isinstance(body.value, ast.BinOp) and isinstance(body.value.op, ast.Add) and is_name(body.value.left, s)):
                        val = body.value.right
                    else:
                        continue
                    if not (isinstance(val, ast.Subscript) and isinstance(val.value, ast.Name) and is_name(val.slice, kv)):
                        continue
                    cands.append(("stmt", init, val.value.id, ra[0], ra[1], (lst, k, s, kv, lp)))
        for kind, node, A, lo, hi, extra in cands:
            loop = _outermost_invariant_loop(node, A)
            if loop is None or not (_is_pure_expr(lo) and _is_pure_expr(hi)):
                continue
            lvars = set()
            for lp_ in enclosing_loops(node):
                if isinstance(lp_, ast.For):
                    lvars |= node_names(lp_.target)
            if not ((node_names(lo) | node_names(hi)) & lvars):
                continue
            P, P_assign = _find_prefix_var(scope, A)
            if P and any(P in node_names(anc) for anc in _ancestors(node) if isinstance(anc, (ast.If, ast.IfExp))):
                continue  # already inside a generated guard
            if P_assign is not None and (getattr(P_assign, "lineno", 0) or 0) > (getattr(loop, "lineno", 0) or 0):
                continue
            if extra is not None and _names_used_after(scope, [extra[4]], {extra[3]}):
                continue
            order, bounds = loop_bounds(node, alias, scope)
            facts = _stable_facts(collect_facts(node, alias), scope)
            lo_l, hi_l = lin_parse(lo, alias), lin_parse(hi, alias)
            lo_s, hi_s = ast.unparse(lo), ast.unparse(hi)
            if lo_l is not None and hi_l is not None and not any(sy.startswith("len:") and sy[4:] in mut for sy in list(lo_l) + list(hi_l)):
                forms = [lo_l, lin_add(hi_l, lo_l, -1), lin_add({"len:" + A: 1}, hi_l, -1)]
                if any(prove_nonneg(_m1(_neg(f)), order, bounds, facts=facts) for f in forms):
                    continue                       # a conjunct is provably FALSE here: the fast path can never apply
                remaining = [f for f in forms if not prove_nonneg(f, order, bounds, facts=facts)]
                # an invariant condition that an enclosing branch already specialised on (e.g. we are inside `if k < 1:`)
                def _sy(form):
                    return {k for k, v in form.items() if k != "#" and v != 0}
                if any(_sy(f) and not (_sy(f) & lvars) and any(_sy(f) & _sy(g) for g in facts) for f in remaining):
                    continue
                guard_src = " and ".join(f"{lin_src(f)} >= 0" for f in remaining)
                proven = not remaining
            else:
                remaining, proven = None, False
                guard_src = f"0 <= {lo_s} <= {hi_s} <= len({A})"
            used = _all_names(tree)
            need_assign = P is None
            if need_assign:
                P = _fresh(f"{A}_prefix", used)
            # The fast path ALWAYS requires P is not None (P is None exactly when the input is not all-int,
            # because summation order can change float results). The ORIGINAL range computation is the fallback.
            fast = f"{P}[{hi_s}] - {P}[{lo_s}]"
            full_guard = f"{P} is not None" + ("" if proven else f" and ({guard_src})")
            if kind == "expr":
                orig_src = ast.unparse(node)
                new_src = f"({fast}) if {full_guard} else ({orig_src})"
                new_node = ast.parse(new_src, mode="eval").body
                payload = ("expr", node, new_node, P, A, loop, need_assign)
                before, after = orig_src, ast.unparse(new_node)
            else:
                lst, k, s_name, kv, lp = extra
                cval = node.value.value
                total = fast if (cval == 0 and isinstance(cval, int)) else f"{ast.unparse(node.value)} + ({fast})"
                assign = ast.parse(f"{s_name} = {total}").body[0]
                new_stmt = ast.If(test=ast.parse(full_guard, mode="eval").body, body=[assign], orelse=[node, lp])
                payload = ("stmt", (lst, k), new_stmt, P, A, loop, need_assign)
                before, after = _stmts_src([node, lp]), ast.unparse(new_stmt)
            how = ("bounds proven from loop ranges / earlier guards (0 ≤ lo ≤ hi ≤ len)" if proven else
                   f"bounds `{guard_src}` checked at runtime")
            changes.append(("prefix", fn.name if fn else None, payload, Change(
                "Range sums via a prefix array (O(1) per query)",
                (f"`{A}` is not modified inside the loop, but every iteration re-adds a contiguous range of it. "
                 f"`{P}` is built once in O(n) when every element is an int; each range sum becomes `{P}[hi] - {P}[lo]` — {how}. "
                 f"Non-int input keeps the original loop (`{P} is None` falls back), because summation order affects floats."),
                fn.name if fn else "<module>", before, after)))
    return changes


def apply_prefix(tree, payload):
    """The prefix array is built ONLY when every element is an int, so P[hi]-P[lo] is exact.
    For floats or mixed input P is None and the original range-sum loop runs (sum order matters)."""
    kind, target, new, P, A, loop, need_assign = payload
    if kind == "expr":
        _replace_node(tree, target, new)
    else:
        lst, k = target
        lst[k:k + 2] = [new]
    if need_assign:
        lst, idx = _parent_stmt_list(loop)
        cond = INTSAFE.format(var=A)
        body = ast.parse(f"{P} = list(itertools.accumulate({A}, initial=0))").body[0]
        fb = ast.parse(f"{P} = None").body[0]
        lst.insert(idx, ast.fix_missing_locations(ast.If(test=ast.parse(cond, mode="eval").body, body=[body], orelse=[fb])))
    _ensure_import(tree, "itertools")


# ---- namespaces ---------------------------------------------------------------------
_SAFE_CALLS = {"float", "int", "set", "dict", "list", "tuple", "range", "str", "len", "max", "min", "abs", "frozenset", "bool", "bytes", "sorted", "sum", "object"}


def defs_only_source(source):
    """Imports, defs, classes and constant-ish globals only — no top-level side effects or heavy calls."""
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return source
    keep = []
    for s in tree.body:
        if isinstance(s, (ast.Import, ast.ImportFrom, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            keep.append(s)
        elif isinstance(s, (ast.Assign, ast.AnnAssign)) and s.value is not None:
            def _safe_call(n):
                if not isinstance(n, ast.Call):
                    return True
                if isinstance(n.func, ast.Name) and n.func.id in _SAFE_CALLS:
                    return True
                # the memo wrapper's cache cell: _f_cached = functools.lru_cache(maxsize=None)(_f_orig).
                # The outer call's func is itself a call, so unwrap to the root before checking.
                f = n.func
                while isinstance(f, ast.Call):
                    f = f.func
                if isinstance(f, ast.Attribute) and isinstance(f.value, ast.Name) and f.value.id == "functools" and f.attr == "lru_cache":
                    return True
                if isinstance(f, ast.Name) and f.id == "object":      # the memo miss sentinel
                    return True
                return False
            if all(_safe_call(n) for n in ast.walk(s.value)):
                keep.append(s)
    tree.body = keep
    return ast.unparse(tree)


def load_namespace(source, name="__bench__", full=False):
    srcs = [source] if full else [defs_only_source(source), source]
    for src in srcs:
        ns = {"__name__": name}
        old = sys.stdout
        sys.stdout = io.StringIO()
        try:
            exec(compile(src, "<ns>", "exec"), ns)
            return ns
        except BaseException:  # noqa
            continue
        finally:
            sys.stdout = old
    return None


# ---- paired benchmarking + regression guard ----------------------------------------
def _median(xs):
    xs = sorted(xs)
    k = len(xs)
    return xs[k // 2] if k % 2 else 0.5 * (xs[k // 2 - 1] + xs[k // 2])


def calibrate_n(fn, tags, target=0.003, start=16, cap=4096, exp_like=False):
    n = 6 if exp_like else start
    cap = 20 if exp_like else cap
    while n <= cap:
        try:
            a = make_args(tags, n, 1000 + n)
            t0 = time.perf_counter()
            fn(*a)
            dt = time.perf_counter() - t0
        except Exception:
            return None
        if dt >= target:
            return n
        n = n + 2 if exp_like else n * 2
    return min(n, cap)


def _guard_argsets(tags, n):
    """Small, deterministic argset pool for in-loop regression guards.
    bench_pair deepcopies every call, so the same logical inputs are safe to reuse."""
    n = max(1, int(n))
    return [make_args(tags, n, 1000 + n + j) for j in range(4)]


def ab_guard(cur_src, new_src, fn_name, tags, exp_like=False):
    """Fast in-loop regression guard using the same measurement discipline as bench_pair.

    Returns {ratio, noise, n, a, b} where ratio = median(orig)/median(opt) (>1 means faster),
    and noise is the MAD-based relative spread of per-round ratios.  None means unmeasurable."""
    try:
        na, nb = load_namespace(cur_src, "__guard_a__"), load_namespace(new_src, "__guard_b__")
        if na is None or nb is None:
            return None
        fa, fb = na.get(fn_name), nb.get(fn_name)
        if not callable(fa) or not callable(fb):
            return None
        tags = probe_signature_prioritized(fa, tags)
        n = calibrate_n(fa, tags, exp_like=exp_like)
        if n is None:
            return None
        argsets = _guard_argsets(tags, n)
        # Guard profile: same primitive/discipline as bench_pair, cheaper budget.
        row = bench_pair(fa, fb, argsets, rounds=5, warm=1, min_sample=0.003,
                         ns_a=na, ns_b=nb, budget=0.35)
        ratio = row.get("ratio")
        if not ratio:
            return None
        return {"ratio": ratio, "noise": float(row.get("spread") or 0.0),
                "n": n, "a": row.get("a"), "b": row.get("b")}
    except Exception:
        return None


def ab_guard_regression(ab):
    """True when an ab_guard result shows a measurable slowdown.

    Uses the same spread semantics as bench_pair (MAD of per-round ratios): reject only when
    the candidate is at least 10% slower AND the slowdown is outside 3*spread (3% floor).
    This keeps the guard conservative while aligning its decision with the reported benchmark."""
    if not ab or not ab.get("ratio"):
        return False
    ratio = float(ab["ratio"])
    spread = max(float(ab.get("noise") or 0.0), 0.03)
    return ratio <= 1.0 / 1.10 and ratio < 1.0 / (1.0 + 3.0 * spread)


# ---- rule library metadata (shown in the UI; nothing here is marketing — see KNOWN_GAPS) ----
RULES = [
    {"id": "algo", "layer": "algorithm", "name": "Algorithm templates",
     "desc": "Maximum-subarray brute force (30 loop shapes) → Kadane; subarray-sum-equals-K (20 loop shapes) → Counter of prefix sums; O(n²) LIS DP (strict & non-strict) → bisect."},
    {"id": "prefix_sum", "layer": "algorithm", "name": "Range sums → prefix array",
     "desc": "sum(a[lo:hi]) and accumulate-loops inside loops → O(1) lookups; covers fixed-size sliding windows. Bounds are proven with a linear-inequality prover or guarded at runtime."},
    {"id": "sort", "layer": "algorithm", "name": "Hand-written sort → Timsort", "desc": "Bubble/insertion/selection patterns."},
    {"id": "count_diff", "layer": "algorithm", "name": "Count difference pairs → running Counter", "desc": "Nested pairs with a[j]-a[i] == k in one pass; ints only, fallback kept."},
    {"id": "reverse_build", "layer": "algorithm", "name": "insert(0) loop → reversed copy", "desc": "Quadratic front insertion → one O(n) reversed copy."},
    {"id": "sliding_window_loop", "layer": "algorithm", "name": "Window-sum inner loop → sliding window + edge guards", "desc": "s = 0; for j in range(i, i+k): s += a[j] per window → O(1) update, O(1) space, exact `k <= 0` / `k > len(a)` guards."},
    {"id": "sliding_window", "layer": "algorithm", "name": "Fixed-size window sums → sliding window", "desc": "sum(a[i:i+k]) per window → O(1) update; keeps the original loop as a fallback only when k >= 1 cannot be proven."},
    {"id": "dead_branch", "layer": "idiom", "name": "Reachability / dead-branch elimination", "desc": "Linear integer facts from loop bounds, earlier `if C: return/raise` guards and asserts prove guards true/false; dead branches are removed, true conjuncts dropped."},
    {"id": "dead_code", "layer": "idiom", "name": "Unused pure variables", "desc": "Pure assignments (and mutation-only statements on them) that are never read."},
    {"id": "pairs", "layer": "algorithm", "name": "Pair search → hash", "desc": "Two-sum, duplicate detection, pair counting."},
    {"id": "memo", "layer": "algorithm", "name": "Memoization", "desc": "Overlapping recursion → lru_cache."},
    {"id": "prime", "layer": "algorithm", "name": "√n trial division", "desc": "Primality loops."},
    {"id": "membership", "layer": "algorithm", "name": "List membership → set", "desc": "`x in list` inside loops."},
    {"id": "shadow_set", "layer": "algorithm", "name": "Shadow set", "desc": "Order-preserving dedupe."},
    {"id": "counter", "layer": "algorithm", "name": "count() in loop → Counter", "desc": "Frequency lookups."},
    {"id": "nested_eq", "layer": "algorithm", "name": "Nested equality scan → set", "desc": "for x: for y: if x == y."},
    {"id": "hoist", "layer": "algorithm", "name": "Loop-invariant hoisting", "desc": "max/min/sum/sorted of an unchanged list."},
    {"id": "deque", "layer": "algorithm", "name": "list queue → deque", "desc": "pop(0) / insert(0)."},
    {"id": "closed_form", "layer": "algorithm", "name": "Closed forms", "desc": "Arithmetic series, sum of squares, repeated multiply."},
    {"id": "strjoin", "layer": "algorithm", "name": "String += in loop → join", "desc": "Quadratic copying."},
    {"id": "direct_join", "layer": "algorithm", "name": "Concat loop → ''.join", "desc": "s = s + c forms."},
    {"id": "manual_seq_eq", "layer": "idiom", "name": "Index loop → ==", "desc": "Element-wise comparison loops."},
    {"id": "dead_len", "layer": "idiom", "name": "Dead length guards", "desc": "len(a) != len(b) when b derives from a."},
    {"id": "canon_reverse", "layer": "idiom", "name": "Canonicalize copies/reversals", "desc": "append-gathers, reversed index lists → list(x) / list(reversed(x))."},
    {"id": "canon_revrange", "layer": "idiom", "name": "Sorted index list → reversed range", "desc": "list(range(n)); sort(reverse=True) → range(n-1,-1,-1)."},
    {"id": "canon_diagonal", "layer": "algorithm", "name": "Diagonal nested loop → single loop", "desc": "for i: for j: if i == j: … → one O(n) pass."},
    {"id": "palindrome_general", "layer": "algorithm", "name": "Palindrome idiom (provenance-based)", "desc": "A == B where A, B derive from one sequence with opposite orientation → root == root[::-1]; hoists through copies."},
    {"id": "cleanup", "layer": "idiom", "name": "Cleanup", "desc": "if X: return True/False → return X; temp-before-return; unused pure assignments."},
    {"id": "idioms", "layer": "idiom", "name": "Loop idioms", "desc": "append→comprehension, accumulate→sum, flag→any."},
    {"id": "fast_io", "layer": "advisory", "name": "Fast input() (advice only)", "desc": "Never applied automatically: sys.stdin.readline keeps the newline and returns '' at EOF."},
]

KNOWN_GAPS = [
    "No general asymptotic search: there is no IR / transformation lattice — only the fixed rules above fire.",
    "Algorithm templates: max-subarray, subarray-sum-equals-K, LIS and fixed-window sums only. None yet for interval scheduling, sliding-window maximum, two-pointer sweeps, knapsack/DP rolling arrays, ternary search.",
    "Reachability reasoning uses linear integer facts only (loop bounds, early returns, asserts). It cannot prove k >= 0 from nothing — an unvalidated parameter keeps a live fallback branch, reported as conditional complexity.",
    "Join rewrites are kept even when CPython shows no gain (CPython hides quadratic str concatenation); their PyPy benefit is not measured here.",
    "No deferred-modulo, bulk stdin/stdout rewriting, or recursion → iteration conversion.",
    "No PyPy / Numba / Cython backends. Nothing here is benchmarked on a JIT.",
    "Prefix sums are exact for ints; float data can differ in the last bits.",
    "Verification is randomized differential testing on small inputs, not a proof.",
]



# ==========================================================================
# Canonicalization + cleanup layer
#   derivation tracking (copy / reversal provenance), reversed-index shapes,
#   equal-index nested loops, generalized palindrome collapse, dead/unused code.
# ==========================================================================

def mutated_names(scope):
    out = set()
    for n in ast.walk(scope):
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute) and n.func.attr in MUTATING_METHODS and isinstance(n.func.value, ast.Name):
            out.add(n.func.value.id)
        if isinstance(n, (ast.Assign, ast.AugAssign, ast.AnnAssign)):
            tg = n.targets if isinstance(n, ast.Assign) else [n.target]
            for t in tg:
                if isinstance(t, (ast.Subscript, ast.Attribute)):
                    base = t
                    while isinstance(base, (ast.Subscript, ast.Attribute)):
                        base = base.value
                    if isinstance(base, ast.Name):
                        out.add(base.id)
            if isinstance(n, ast.AugAssign) and isinstance(n.target, ast.Name):
                out.add(n.target.id)
        if isinstance(n, ast.Delete):
            out |= set().union(*[node_names(t) for t in n.targets]) if n.targets else set()
    return out


def _load_count(scope, name):
    return sum(1 for n in ast.walk(scope) if isinstance(n, ast.Name) and n.id == name and isinstance(n.ctx, ast.Load))


def _derive_expr(e):
    """expr -> (base_name, 'copy'|'reverse') if expr is a pure copy / reversal of a name."""
    if isinstance(e, ast.Call) and isinstance(e.func, ast.Name) and e.func.id in ("list", "tuple") and len(e.args) == 1 and not e.keywords:
        a = e.args[0]
        if isinstance(a, ast.Name):
            return (a.id, "copy")
        if isinstance(a, ast.Call) and is_name(a.func, "reversed") and len(a.args) == 1 and isinstance(a.args[0], ast.Name):
            return (a.args[0].id, "reverse")
        return _derive_expr(a)
    if isinstance(e, ast.Subscript) and isinstance(e.value, ast.Name) and isinstance(e.slice, ast.Slice):
        s = e.slice
        if s.lower is None and s.upper is None:
            if s.step is None:
                return (e.value.id, "copy")
            if isinstance(s.step, ast.UnaryOp) and isinstance(s.step.op, ast.USub) and is_const_int(s.step.operand) and s.step.operand.value == 1:
                return (e.value.id, "reverse")
            if is_const_int(s.step) and s.step.value == -1:
                return (e.value.id, "reverse")
    if isinstance(e, ast.ListComp) and len(e.generators) == 1 and not e.generators[0].ifs:
        g = e.generators[0]
        if isinstance(g.target, ast.Name) and is_name(e.elt, g.target.id):
            if isinstance(g.iter, ast.Name):
                return (g.iter.id, "copy")
            if isinstance(g.iter, ast.Call) and is_name(g.iter.func, "reversed") and len(g.iter.args) == 1 and isinstance(g.iter.args[0], ast.Name):
                return (g.iter.args[0].id, "reverse")
    return None


def _char_list(scope, name):
    """name is assigned once from a comprehension / list() over a string-typed expression (elements are 1-char strings)."""
    for n in ast.walk(scope):
        if isinstance(n, ast.Assign) and len(n.targets) == 1 and is_name(n.targets[0], name):
            v = n.value
            src = None
            if isinstance(v, ast.ListComp) and len(v.generators) == 1 and isinstance(v.generators[0].target, ast.Name) and is_name(v.elt, v.generators[0].target.id):
                src = v.generators[0].iter
            elif isinstance(v, ast.Call) and is_name(v.func, "list") and len(v.args) == 1:
                src = v.args[0]
            if src is None:
                return False
            if isinstance(src, ast.Call) and isinstance(src.func, ast.Attribute) and src.func.attr in ("lower", "upper", "strip", "casefold", "replace"):
                return True
            if isinstance(src, ast.Name):
                tags = _CURRENT_FN_TYPES.get(scope.name) if isinstance(scope, ast.FunctionDef) else None
                params = [a.arg for a in scope.args.args] if isinstance(scope, ast.FunctionDef) else []
                return bool(tags and src.id in params and tags[params.index(src.id)] == "str")
    return False


def _derive_join(e, scope):
    if isinstance(e, ast.Call) and isinstance(e.func, ast.Attribute) and e.func.attr == "join" and isinstance(e.func.value, ast.Constant) \
            and e.func.value.value == "" and len(e.args) == 1:
        a = e.args[0]
        if isinstance(a, ast.Name) and _char_list(scope, a.id):
            return (a.id, "copy")
        if isinstance(a, ast.Call) and is_name(a.func, "reversed") and len(a.args) == 1 and isinstance(a.args[0], ast.Name) and _char_list(scope, a.args[0].id):
            return (a.args[0].id, "reverse")
        if isinstance(a, ast.Subscript) and isinstance(a.value, ast.Name) and _char_list(scope, a.value.id):
            d = _derive_expr(a)
            if d:
                return d
    return None


def derivations(scope):
    """var -> (base, kind) for single-assignment variables whose base is never mutated/rebound."""
    counts = _scope_assign_counts(scope)
    mut = mutated_names(scope)
    params = {a.arg for a in scope.args.args} if isinstance(scope, ast.FunctionDef) else set()
    out = {}
    for n in ast.walk(scope):
        if not (isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name)):
            continue
        v = n.targets[0].id
        if counts.get(v, 0) != 1 or v in mut:
            continue
        d = _derive_expr(n.value) or _derive_join(n.value, scope)
        if d is None:
            continue
        base = d[0]
        if base in mut or (counts.get(base, 0) > 1) or (base in params and counts.get(base, 0) > 0):
            continue
        out[v] = d
    return out


def resolve_chain(name, der):
    chain = [(name, 0)]
    seen = {name}
    par = 0
    while name in der:
        base, kind = der[name]
        if base in seen:
            break
        par ^= 1 if kind == "reverse" else 0
        name = base
        seen.add(name)
        chain.append((name, par))
    return chain


def same_length(a, b, der):
    ca = {n for n, _ in resolve_chain(a, der)}
    return any(n in ca for n, _ in resolve_chain(b, der))


def _seq_evidence(scope, name, tags=None):
    for n in ast.walk(scope):
        if isinstance(n, ast.Subscript) and is_name(n.value, name):
            return True
        if isinstance(n, ast.Call) and is_name(n.func, "len") and n.args and is_name(n.args[0], name):
            return True
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute) and is_name(n.func.value, name) and n.func.attr in (
                "lower", "upper", "strip", "split", "isalnum", "isalpha", "sort", "index", "count", "join", "replace"):
            return True
    if tags and isinstance(scope, ast.FunctionDef):
        params = [a.arg for a in scope.args.args]
        if name in params and tags[params.index(name)] in ("str", "list", "strlist"):
            return True
    return False


# ---- reversed-range recognisers ------------------------------------------------------
def _len_target(e, alias):
    if isinstance(e, ast.Call) and is_name(e.func, "len") and len(e.args) == 1 and isinstance(e.args[0], ast.Name):
        return e.args[0].id
    if isinstance(e, ast.Name) and e.id in alias:
        return alias[e.id]
    return None


def _is_plain_range_len(e, alias):
    """range(len(L)) -> L"""
    if isinstance(e, ast.Call) and is_name(e.func, "range") and len(e.args) == 1 and not e.keywords:
        return _len_target(e.args[0], alias)
    return None


def rev_range_target(e, alias):
    """Does e iterate len(L)-1 .. 0 ?  Returns L or None."""
    if isinstance(e, ast.Call) and is_name(e.func, "range") and len(e.args) == 3 and not e.keywords:
        a0, a1, a2 = e.args
        neg1 = (isinstance(a2, ast.UnaryOp) and isinstance(a2.op, ast.USub) and is_const_int(a2.operand) and a2.operand.value == 1)
        if neg1 and isinstance(a1, ast.UnaryOp) and isinstance(a1.op, ast.USub) and is_const_int(a1.operand) and a1.operand.value == 1:
            if isinstance(a0, ast.BinOp) and isinstance(a0.op, ast.Sub) and is_const_int(a0.right) and a0.right.value == 1:
                return _len_target(a0.left, alias)
    if isinstance(e, ast.Call) and is_name(e.func, "reversed") and len(e.args) == 1:
        return _is_plain_range_len(e.args[0], alias)
    if isinstance(e, ast.Call) and is_name(e.func, "sorted") and len(e.args) == 1 and len(e.keywords) == 1 and e.keywords[0].arg == "reverse" \
            and isinstance(e.keywords[0].value, ast.Constant) and e.keywords[0].value.value is True:
        return _is_plain_range_len(e.args[0], alias)
    if isinstance(e, ast.Subscript) and isinstance(e.slice, ast.Slice) and e.slice.lower is None and e.slice.upper is None:
        st = e.slice.step
        if (is_const_int(st) and st.value == -1) or (isinstance(st, ast.UnaryOp) and isinstance(st.op, ast.USub) and is_const_int(st.operand) and st.operand.value == 1):
            inner = e.value
            if isinstance(inner, ast.Call) and is_name(inner.func, "list") and len(inner.args) == 1:
                inner = inner.args[0]
            return _is_plain_range_len(inner, alias)
    if isinstance(e, ast.Call) and is_name(e.func, "list") and len(e.args) == 1:
        return rev_range_target(e.args[0], alias)
    return None


def _index_list_range_arg(v):
    """`list(range(E))` or `[i for i in range(E)]` -> E, else None."""
    if isinstance(v, ast.Call) and is_name(v.func, "list") and len(v.args) == 1 and not v.keywords:
        r = v.args[0]
        if isinstance(r, ast.Call) and is_name(r.func, "range") and len(r.args) == 1 and not r.keywords:
            return r.args[0]
    if isinstance(v, ast.ListComp) and len(v.generators) == 1 and not v.generators[0].ifs:
        g = v.generators[0]
        if isinstance(g.target, ast.Name) and is_name(v.elt, g.target.id) and isinstance(g.iter, ast.Call) and is_name(g.iter.func, "range") \
                and len(g.iter.args) == 1 and not g.iter.keywords:
            return g.iter.args[0]
    return None


def _is_list_var(scope, name):
    if _scope_assign_counts(scope).get(name, 0) != 1:
        return False
    if isinstance(scope, ast.FunctionDef) and name in {a.arg for a in scope.args.args}:
        return False
    for n in ast.walk(scope):
        if isinstance(n, ast.Assign) and len(n.targets) == 1 and is_name(n.targets[0], name):
            v = n.value
            return isinstance(v, (ast.List, ast.ListComp)) or (isinstance(v, ast.Call) and isinstance(v.func, ast.Name) and v.func.id in ("list", "sorted"))
    return False


def _rev_src(scope, L):
    return f"{L}[::-1]" if _is_list_var(scope, L) else f"list(reversed({L}))"


def _named_rev_range(name, lst, upto, scope, alias):
    """`name` is a reversed index range of L built in statement list `lst` before index `upto`:
       name = <rev-range expr>              or
       name = list(range(len(L))) ; name.sort(reverse=True) | name.reverse()
       Returns (L, [stmts_to_remove]) or None.  `name` must have no other uses in scope."""
    assign = None
    sort_stmt = None
    for s in lst[:upto]:
        if isinstance(s, ast.Assign) and len(s.targets) == 1 and is_name(s.targets[0], name):
            assign, sort_stmt = s, None
        elif assign is not None and isinstance(s, ast.Expr) and isinstance(s.value, ast.Call) and isinstance(s.value.func, ast.Attribute) \
                and is_name(s.value.func.value, name):
            c = s.value
            if c.func.attr == "reverse" and not c.args:
                sort_stmt = s
            elif c.func.attr == "sort" and not c.args and len(c.keywords) == 1 and c.keywords[0].arg == "reverse" \
                    and isinstance(c.keywords[0].value, ast.Constant) and c.keywords[0].value.value is True:
                sort_stmt = s
            else:
                return None
    if assign is None:
        return None
    other_uses = _load_count(scope, name) - (1 if sort_stmt is not None else 0) - 1  # minus the for-iter use
    if other_uses != 0 or _scope_assign_counts(scope).get(name, 0) != 1:
        return None
    if sort_stmt is None:
        L = rev_range_target(assign.value, alias)
        return (L, [assign]) if L else None
    E = _index_list_range_arg(assign.value)
    if E is not None:
        L = _len_target(E, alias)
        if L:
            return (L, [assign, sort_stmt])
    return None


# ---- C1/C2: build-by-append / reversed gather → list(...) ---------------------------------
def t_canon_reverse(tree):
    changes = []
    for scope in [tree] + [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]:
        fn = scope if isinstance(scope, ast.FunctionDef) else None
        alias = len_aliases(scope)
        der = derivations(scope)
        for node in ast.walk(scope):
            for _, lst in iter_stmt_lists(node):
                for k, s in enumerate(lst):
                    if _enclosing_function(s) is not fn:
                        continue
                    # form A: rev = [L[i] for i in R]   (after idiom pass)   form B: rev = []; for i in R: rev.append(L[i])
                    target = iter_expr = elt = loop_var = None
                    region = [s]
                    if isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name) and isinstance(s.value, ast.ListComp) \
                            and len(s.value.generators) == 1 and not s.value.generators[0].ifs and isinstance(s.value.generators[0].target, ast.Name):
                        target = s.targets[0].id
                        g = s.value.generators[0]
                        iter_expr, elt, loop_var = g.iter, s.value.elt, g.target.id
                    elif isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name) and isinstance(s.value, ast.List) \
                            and not s.value.elts and k + 1 < len(lst) and isinstance(lst[k + 1], ast.For):
                        lp = lst[k + 1]
                        target = s.targets[0].id
                        if isinstance(lp.target, ast.Name) and len(lp.body) == 1 and not lp.orelse and isinstance(lp.body[0], ast.Expr) \
                                and isinstance(lp.body[0].value, ast.Call) and call_name(lp.body[0].value) == ".append" \
                                and is_name(lp.body[0].value.func.value, target) and len(lp.body[0].value.args) == 1:
                            iter_expr, elt, loop_var = lp.iter, lp.body[0].value.args[0], lp.target.id
                            region = [s, lp]
                    if target is None or iter_expr is None:
                        continue
                    new_expr = None
                    remove = []
                    # gather L[i] over reversed index range
                    if isinstance(elt, ast.Subscript) and isinstance(elt.value, ast.Name) and is_name(elt.slice, loop_var):
                        L = elt.value.id
                        if isinstance(iter_expr, ast.Name):
                            got = _named_rev_range(iter_expr.id, lst, k, scope, alias)
                            if got and (got[0] == L or same_length(got[0], L, der)):
                                remove = got[1]
                                new_expr = _rev_src(scope, L)
                        elif rev_range_target(iter_expr, alias) == L:
                            new_expr = _rev_src(scope, L)
                        elif _is_plain_range_len(iter_expr, alias) == L:
                            new_expr = f"list({L})"
                    elif is_name(elt, loop_var):
                        if isinstance(iter_expr, ast.Name):
                            new_expr = f"list({iter_expr.id})"
                        elif isinstance(iter_expr, ast.Call) and is_name(iter_expr.func, "reversed") and len(iter_expr.args) == 1 and isinstance(iter_expr.args[0], ast.Name):
                            new_expr = f"list(reversed({iter_expr.args[0].id}))"
                    if new_expr is None:
                        continue
                    new_stmt = ast.parse(f"{target} = {new_expr}").body[0]
                    before = _stmts_src(remove + region) if remove else _stmts_src(region)
                    changes.append(("canon", fn.name if fn else None, (lst, region, remove, new_stmt), Change(
                        f"Canonicalize construction of `{target}` → `{new_expr}`",
                        "Element-by-element gathering (optionally through a reversed index list) is the same as a single C-level copy/reversal. "
                        "This exposes the provenance of the sequence to later rules.",
                        fn.name if fn else "<module>", before, ast.unparse(new_stmt), kind="constant")))
        # Copy-chain collapse: `a = list(X)` / `tuple(X)` followed by `b = list(a)` / `tuple(a)` where `a` is read nowhere else
        counts = _scope_assign_counts(scope)
        mut = mutated_names(scope)
        for node in ast.walk(scope):
            for _, lst in iter_stmt_lists(node):
                for k in range(len(lst) - 1):
                    s1, s2 = lst[k], lst[k + 1]
                    if _enclosing_function(s1) is not fn:
                        continue
                    if not (isinstance(s1, ast.Assign) and len(s1.targets) == 1 and isinstance(s1.targets[0], ast.Name)
                            and isinstance(s2, ast.Assign) and len(s2.targets) == 1 and isinstance(s2.targets[0], ast.Name)):
                        continue
                    a, b = s1.targets[0].id, s2.targets[0].id
                    if counts.get(a, 0) != 1 or a in mut or _load_count(scope, a) != 1:
                        continue
                    if not (isinstance(s1.value, ast.Call) and isinstance(s1.value.func, ast.Name) and s1.value.func.id in ("list", "tuple")
                            and len(s1.value.args) == 1 and not s1.value.keywords and isinstance(s1.value.args[0], ast.Name)):
                        continue
                    if not (isinstance(s2.value, ast.Call) and isinstance(s2.value.func, ast.Name) and s2.value.func.id in ("list", "tuple")
                            and len(s2.value.args) == 1 and not s2.value.keywords and is_name(s2.value.args[0], a)):
                        continue
                    X = s1.value.args[0].id
                    outer_ctor = s2.value.func.id
                    new_stmt = ast.parse(f"{b} = {outer_ctor}({X})").body[0]
                    changes.append(("replace_pair", fn.name if fn else None, (lst, k, new_stmt), Change(
                        f"Collapse redundant copy `{a}` → `{b} = {outer_ctor}({X})`",
                        f"`{a}` is only created to be immediately copied into `{b}`.",
                        fn.name if fn else "<module>", _stmts_src([s1, s2]), ast.unparse(new_stmt), kind="constant")))
    return changes


def apply_canon(tree, payload):
    lst, region, remove, new_stmt = payload
    idx = next(i for i, s in enumerate(lst) if s is region[0])
    lst[idx:idx + len(region)] = [new_stmt]
    for r in remove:
        for i, s in enumerate(lst):
            if s is r:
                del lst[i]
                break


# ---- C3: index list sorted descending, only iterated → range(n-1, -1, -1) ----------------
def t_canon_revrange(tree):
    changes = []
    for scope in [tree] + [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]:
        fn = scope if isinstance(scope, ast.FunctionDef) else None
        for node in ast.walk(scope):
            for _, lst in iter_stmt_lists(node):
                for k in range(len(lst) - 1):
                    a, b = lst[k], lst[k + 1]
                    if _enclosing_function(a) is not fn:
                        continue
                    if not (isinstance(a, ast.Assign) and len(a.targets) == 1 and isinstance(a.targets[0], ast.Name)):
                        continue
                    name = a.targets[0].id
                    v = a.value
                    E_node = _index_list_range_arg(v)
                    if E_node is None:
                        continue
                    if not (isinstance(b, ast.Expr) and isinstance(b.value, ast.Call) and isinstance(b.value.func, ast.Attribute)
                            and is_name(b.value.func.value, name) and b.value.func.attr == "sort" and not b.value.args
                            and len(b.value.keywords) == 1 and b.value.keywords[0].arg == "reverse"
                            and isinstance(b.value.keywords[0].value, ast.Constant) and b.value.keywords[0].value.value is True):
                        continue
                    # every other use must be `for _ in name`
                    ok = True
                    for n in ast.walk(scope):
                        if isinstance(n, ast.Name) and n.id == name and isinstance(n.ctx, ast.Load):
                            p = getattr(n, "_parent", None)
                            if p is b.value.func:
                                continue
                            if not (isinstance(p, ast.For) and p.iter is n):
                                ok = False
                    if not ok or name in mutated_names(scope) - {name} and False:
                        continue
                    E = ast.unparse(E_node)
                    new_stmt = ast.parse(f"{name} = range({E} - 1, -1, -1)").body[0]
                    changes.append(("replace_pair", fn.name if fn else None, (lst, k, new_stmt), Change(
                        f"`{name}` = sorted descending index list → `range({E} - 1, -1, -1)`",
                        "Building a list of indices and sorting it (O(n log n), O(n) memory) just to iterate downwards is a lazy reversed range.",
                        fn.name if fn else "<module>", _stmts_src([a, b]), ast.unparse(new_stmt), kind="constant")))
    return changes


# ---- C4: nested loops that only act on the diagonal i == j --------------------------------
class _Rename(ast.NodeTransformer):
    def __init__(self, old, new):
        self.old, self.new = old, new

    def visit_Name(self, node):
        if node.id == self.old:
            return ast.copy_location(ast.Name(id=self.new, ctx=node.ctx), node)
        return node


def t_canon_diagonal(tree):
    changes = []
    for scope in [tree] + [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]:
        fn = scope if isinstance(scope, ast.FunctionDef) else None
        alias = len_aliases(scope)
        der = derivations(scope)
        for outer in [n for n in ast.walk(scope) if isinstance(n, ast.For)]:
            if _enclosing_function(outer) is not fn or outer.orelse or len(outer.body) != 1:
                continue
            inner = outer.body[0]
            if not (isinstance(inner, ast.For) and not inner.orelse and len(inner.body) == 1 and isinstance(inner.body[0], ast.If)):
                continue
            if not (isinstance(outer.target, ast.Name) and isinstance(inner.target, ast.Name)):
                continue
            i, j = outer.target.id, inner.target.id
            r1, r2 = _range_args(outer.iter), _range_args(inner.iter)
            if not (r1 and r2 and is_const_int(r1[0]) and r1[0].value == 0 and is_const_int(r2[0]) and r2[0].value == 0):
                continue
            iff = inner.body[0]
            if iff.orelse:
                continue
            t = iff.test
            rest = None
            if isinstance(t, ast.Compare) and len(t.ops) == 1 and isinstance(t.ops[0], ast.Eq) and {ast.unparse(t.left), ast.unparse(t.comparators[0])} == {i, j}:
                rest = None
            elif isinstance(t, ast.BoolOp) and isinstance(t.op, ast.And) and len(t.values) >= 2:
                g = t.values[0]
                if isinstance(g, ast.Compare) and len(g.ops) == 1 and isinstance(g.ops[0], ast.Eq) and {ast.unparse(g.left), ast.unparse(g.comparators[0])} == {i, j}:
                    rest = t.values[1] if len(t.values) == 2 else ast.BoolOp(op=ast.And(), values=t.values[1:])
                else:
                    continue
            else:
                continue
            body = iff.body
            if {i, j} & names_written(ast.Module(body=body, type_ignores=[])):
                continue
            if any(isinstance(n, (ast.Break, ast.Continue)) for b in body for n in ast.walk(b)):
                continue
            N1, N2 = r1[1], r2[1]
            A, B = _len_target(N1, alias), _len_target(N2, alias)
            if A and B and (A == B or same_length(A, B, der)):
                bound = ast.unparse(N1)
            else:
                bound = f"min({ast.unparse(N1)}, {ast.unparse(N2)})"
            new_body = [_Rename(j, i).visit(copy.deepcopy(b)) for b in body]
            if rest is not None:
                new_body = [ast.If(test=_Rename(j, i).visit(copy.deepcopy(rest)), body=new_body, orelse=[])]
            new_loop = ast.For(target=ast.Name(id=i, ctx=ast.Store()), iter=ast.parse(f"range({bound})", mode="eval").body, body=new_body, orelse=[])
            new_loop = ast.fix_missing_locations(ast.copy_location(new_loop, outer))
            new_loop.type_comment = None
            lst, k = _parent_stmt_list(outer)
            if lst is None:
                continue
            changes.append(("replace_stmt", fn.name if fn else None, (lst, k, [new_loop]), Change(
                "Nested loop that only acts on the diagonal (i == j) → single loop",
                "The inner loop does nothing except when i == j, so the O(n²) scan is a single O(n) pass over the shared index."
                + ("" if "min(" in bound else " Lengths are provably equal, so the bound is the plain length."),
                fn.name if fn else "<module>", ast.unparse(outer), ast.unparse(new_loop))))
    return changes


# ---- C5: generalized palindrome collapse -------------------------------------------------
def _common_root(a, b, der):
    ca = resolve_chain(a, der)
    cb = resolve_chain(b, der)
    pos = {n: p for n, p in cb}
    for n, p in ca:
        if n in pos:
            return n, p, pos[n]
    return None, None, None


def t_palindrome_general(tree, fn_types=None):
    """Fully collapse palindrome constructions in a function body.
    Supported shape: `return A == B` (or `if A != B: return False / return True`)
    where A and B are derived from one common root sequence by pure copies/reversals.
    Collapses the entire construction down to `return root == root[::-1]` and removes the
    intermediate assignments when they are pure, single-assignment and never read elsewhere."""
    changes = []
    for fn in [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]:
        der = derivations(fn)
        for node in ast.walk(fn):
            for _, lst in iter_stmt_lists(node):
                for k, s in enumerate(lst):
                    if _enclosing_function(s) is not fn:
                        continue
                    if not (isinstance(s, ast.Return) and isinstance(s.value, ast.Compare)
                            and len(s.value.ops) == 1 and isinstance(s.value.ops[0], (ast.Eq, ast.NotEq))):
                        continue
                    cmp = s.value
                    negate = isinstance(cmp.ops[0], ast.NotEq)
                    L, R = cmp.left, cmp.comparators[0]
                    # normalize: `R = X[::-1]` means reversed copy of X
                    R_name = None
                    if isinstance(R, ast.Subscript) and isinstance(R.value, ast.Name) and isinstance(R.slice, ast.Slice):
                        sl = R.slice
                        step = sl.step
                        reversed_slice = (sl.lower is None and sl.upper is None
                                          and (is_const_int(step) and step.value == -1
                                               or (isinstance(step, ast.UnaryOp) and isinstance(step.op, ast.USub) and is_const_int(step.operand) and step.operand.value == 1)))
                        if reversed_slice:
                            R_name = R.value.id
                    elif isinstance(R, ast.Name):
                        R_name = R.id
                    if R_name is None or not isinstance(L, ast.Name):
                        continue
                    root, pa, pb = _common_root(L.id, R_name, der)
                    if root is None or pa == pb:
                        continue
                    # propagate the collapse target down to the outermost common pure-copy ancestor
                    while root in der:
                        base, kind = der[root]
                        if kind != "copy":
                            break
                        root = base
                    names = set()
                    for v in (L.id, R_name):
                        names |= {n for n, _ in resolve_chain(v, der)}
                    names.discard(root)
                    if not names:
                        continue
                    # chain-assign statement indices (pure single assignments to chain names)
                    removable_idx = []
                    for idx, st in enumerate(lst):
                        if idx == k:
                            continue
                        if not (isinstance(st, ast.Assign) and len(st.targets) == 1 and isinstance(st.targets[0], ast.Name)):
                            continue
                        nm = st.targets[0].id
                        if nm not in names:
                            continue
                        if not _pure(st.value):
                            continue
                        removable_idx.append(idx)
                    removable_idx = sorted(i for i in removable_idx if i < k)
                    if not removable_idx:
                        # nothing removable — minimal collapse of the comparison
                        new = ast.parse(f"return {root} {'!=' if negate else '=='} {root}[::-1]").body[0]
                        changes.append(("replace_region", fn.name, (lst, k, 1, [new], []), Change(
                            "Sequence compared with its own reversal → palindrome idiom",
                            f"`{L.id}` and `{R.id if isinstance(R, ast.Name) else R_name}` are copies of `{root}` with opposite orientation.",
                            fn.name, _stmts_src([s]), ast.unparse(new))))
                        continue
                    # every Load of a chain name must be:
                    #   - inside the return statement (will be replaced), or
                    #   - inside the value of a chain-assign (it will be deleted)
                    safe = True
                    for nm in names:
                        for n in ast.walk(fn):
                            if not (isinstance(n, ast.Name) and n.id == nm and isinstance(n.ctx, ast.Load)):
                                continue
                            anc = getattr(n, "_parent", None)
                            inside_return = False
                            seen = set()
                            while anc is not None and id(anc) not in seen:
                                seen.add(id(anc))
                                if anc is s:
                                    inside_return = True
                                    break
                                anc = getattr(anc, "_parent", None)
                            if inside_return:
                                continue
                            anc = getattr(n, "_parent", None)
                            seen = set()
                            inside_assign = False
                            while anc is not None and id(anc) not in seen:
                                seen.add(id(anc))
                                if isinstance(anc, ast.Assign) and len(anc.targets) == 1 and isinstance(anc.targets[0], ast.Name):
                                    if anc.targets[0].id in names:
                                        inside_assign = True
                                        break
                                anc = getattr(anc, "_parent", None)
                            if not inside_assign:
                                safe = False
                                break
                        if not safe:
                            break
                    # no statements other than the return referencing a chain name before the return
                    bad = False
                    region_start = min(removable_idx)
                    for idx, q in enumerate(lst[region_start:k]):
                        q_idx = region_start + idx
                        if q_idx in removable_idx:
                            continue
                        if node_names(q) & names:
                            bad = True
                            break
                    if bad:
                        continue
                    new = ast.parse(f"return {root} {'!=' if negate else '=='} {root}[::-1]").body[0]
                    before_src = _stmts_src(lst[region_start:k + 1])
                    changes.append(("replace_multi", fn.name, (lst, region_start, k, removable_idx, [new], []), Change(
                        "Palindrome construction collapsed → root == root[::-1]",
                        f"`{L.id}` and `{R.id if isinstance(R, ast.Name) else R_name}` are pure copies/reversals of `{root}` — the intermediate lists and the one O(n) scan are removed.",
                        fn.name, before_src, ast.unparse(new))))
    return changes


def t_cleanup(tree):
    changes = []
    for scope in [tree] + [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]:
        fn = scope if isinstance(scope, ast.FunctionDef) else None
        counts = _scope_assign_counts(scope)
        for node in ast.walk(scope):
            for _, lst in iter_stmt_lists(node):
                for k, s in enumerate(lst):
                    if _enclosing_function(s) is not fn:
                        continue
                    nxt = lst[k + 1] if k + 1 < len(lst) else None
                    # K1: if X: return True / return False  -> return X
                    if (isinstance(s, ast.If) and not s.orelse and len(s.body) == 1 and isinstance(s.body[0], ast.Return)
                            and isinstance(s.body[0].value, ast.Constant) and isinstance(s.body[0].value.value, bool)
                            and isinstance(nxt, ast.Return) and isinstance(nxt.value, ast.Constant) and isinstance(nxt.value.value, bool)
                            and nxt.value.value != s.body[0].value.value):
                        x = ast.unparse(s.test)
                        if s.body[0].value.value is True:
                            expr = x if _is_boolish(s.test) else f"bool({x})"
                        else:
                            expr = f"not ({x})" if not isinstance(s.test, (ast.Compare, ast.Name, ast.Call)) else f"not {x}"
                        new = ast.parse(f"return {expr}").body[0]
                        changes.append(("replace_pair", fn.name if fn else None, (lst, k, new), Change(
                            "Boolean branch → direct return", "`if X: return True` followed by `return False` is just `return X`.",
                            fn.name if fn else "<module>", _stmts_src([s, nxt]), ast.unparse(new), kind="constant")))
                        continue
                    # K2: x = expr ; return x   (x used nowhere else)
                    if (isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name)
                            and isinstance(nxt, ast.Return) and is_name(nxt.value, s.targets[0].id)
                            and counts.get(s.targets[0].id, 0) == 1 and _load_count(scope, s.targets[0].id) == 1):
                        new = ast.Return(value=s.value)
                        changes.append(("replace_pair", fn.name if fn else None, (lst, k, new), Change(
                            "Temporary before return removed", "The value is returned immediately; the temporary is not used anywhere else.",
                            fn.name if fn else "<module>", _stmts_src([s, nxt]), ast.unparse(new), kind="constant")))
                        continue
                    # K4: `if C: x = E1; else: x = E2` -> ternary expression `x = E1 if C else E2`
                    if (isinstance(s, ast.If) and len(s.body) == 1 and len(s.orelse) == 1
                            and isinstance(s.body[0], ast.Assign) and isinstance(s.orelse[0], ast.Assign)
                            and len(s.body[0].targets) == 1 and len(s.orelse[0].targets) == 1
                            and isinstance(s.body[0].targets[0], ast.Name) and isinstance(s.orelse[0].targets[0], ast.Name)
                            and s.body[0].targets[0].id == s.orelse[0].targets[0].id):
                        vname = s.body[0].targets[0].id
                        e1, e2 = ast.unparse(s.body[0].value), ast.unparse(s.orelse[0].value)
                        new_src = f"{vname} = {e1}" if e1 == e2 else f"{vname} = {e1} if {ast.unparse(s.test)} else {e2}"
                        new = ast.parse(new_src).body[0]
                        changes.append(("replace_stmt", fn.name if fn else None, (lst, k, [new]), Change(
                            "Single-assignment if/else → conditional expression",
                            f"Both branches only assign `{vname}`.",
                            fn.name if fn else "<module>", ast.unparse(s), new_src, kind="constant")))
                        continue
                    # K5: `flag = A == B` followed by `if A != B: flag = False` -> redundant check removed
                    if (isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name)
                            and isinstance(s.value, ast.Compare) and len(s.value.ops) == 1 and isinstance(s.value.ops[0], ast.Eq)
                            and isinstance(nxt, ast.If) and not nxt.orelse and len(nxt.body) == 1
                            and isinstance(nxt.body[0], ast.Assign) and len(nxt.body[0].targets) == 1
                            and is_name(nxt.body[0].targets[0], s.targets[0].id)
                            and isinstance(nxt.body[0].value, ast.Constant) and nxt.body[0].value.value is False
                            and isinstance(nxt.test, ast.Compare) and len(nxt.test.ops) == 1 and isinstance(nxt.test.ops[0], ast.NotEq)):
                        p1 = {ast.unparse(s.value.left), ast.unparse(s.value.comparators[0])}
                        p2 = {ast.unparse(nxt.test.left), ast.unparse(nxt.test.comparators[0])}
                        if p1 == p2:
                            changes.append(("replace_pair", fn.name if fn else None, (lst, k, copy.deepcopy(s)), Change(
                                "Redundant mismatch check removed",
                                f"`{s.targets[0].id}` is already `False` whenever `{ast.unparse(nxt.test)}` holds.",
                                fn.name if fn else "<module>", _stmts_src([s, nxt]), ast.unparse(s), kind="constant")))
                            continue
                    # K6: `if len(X) == 0: return True` right before `return X == X[::-1]` -> redundant (empty sequence equals its reverse)
                    if (isinstance(s, ast.If) and not s.orelse and len(s.body) == 1 and isinstance(s.body[0], ast.Return)
                            and isinstance(s.body[0].value, ast.Constant) and s.body[0].value.value is True
                            and isinstance(s.test, ast.Compare) and len(s.test.ops) == 1 and isinstance(s.test.ops[0], ast.Eq)
                            and isinstance(s.test.left, ast.Call) and is_name(s.test.left.func, "len") and len(s.test.left.args) == 1
                            and isinstance(s.test.left.args[0], ast.Name) and is_const_int(s.test.comparators[0]) and s.test.comparators[0].value == 0
                            and isinstance(nxt, ast.Return) and isinstance(nxt.value, ast.Compare) and len(nxt.value.ops) == 1
                            and isinstance(nxt.value.ops[0], ast.Eq) and is_name(nxt.value.left, s.test.left.args[0].id)
                            and ast.unparse(nxt.value.comparators[0]) == f"{s.test.left.args[0].id}[::-1]"):
                        changes.append(("replace_pair", fn.name if fn else None, (lst, k, copy.deepcopy(nxt)), Change(
                            "Redundant empty-length guard removed",
                            f"For any sequence with `len({s.test.left.args[0].id}) == 0`, `{s.test.left.args[0].id} == {s.test.left.args[0].id}[::-1]` is already `True`.",
                            fn.name if fn else "<module>", _stmts_src([s, nxt]), ast.unparse(nxt), kind="constant")))
                        continue
                    # K3: unused pure assignment — moved to t_dead_code (phase 4); skip here
                    if False:
                        name = s.targets[0].id
                        if fn is None and name in _all_names(tree) and any(isinstance(n, ast.FunctionDef) and name in node_names(n) for n in ast.walk(tree)):
                            continue
                        mut_only = []
                        other = False
                        for n in ast.walk(scope):
                            if isinstance(n, ast.Name) and n.id == name and isinstance(n.ctx, ast.Load):
                                p = getattr(n, "_parent", None)
                                pp = getattr(p, "_parent", None)
                                ppp = getattr(pp, "_parent", None)
                                if (isinstance(p, ast.Attribute) and isinstance(pp, ast.Call) and pp.func is p and isinstance(ppp, ast.Expr)
                                        and p.attr in ("sort", "reverse", "append", "extend", "clear") and all(_pure(a) for a in pp.args)):
                                    mut_only.append(ppp)
                                else:
                                    other = True
                        if other or counts.get(name, 0) != 1:
                            continue
                        if isinstance(scope, ast.FunctionDef) and name in {a.arg for a in scope.args.args}:
                            continue
                        if any(isinstance(n, (ast.Global, ast.Nonlocal)) for n in ast.walk(scope)):
                            continue
                        region = [s] + mut_only
                        changes.append(("remove_stmts", fn.name if fn else None, (scope, region), Change(
                            f"Unused variable `{name}` removed",
                            "The value is pure (no side effects) and never read after the preceding rewrites made it redundant.",
                            fn.name if fn else "<module>", _stmts_src(region), "# removed", kind="constant")))
    return changes


def apply_remove_stmts(tree, payload):
    scope, region = payload
    ids = {id(r) for r in region}
    for node in ast.walk(scope):
        for field, lst in iter_stmt_lists(node):
            new_list = [s for s in lst if id(s) not in ids]
            if new_list:
                lst[:] = new_list
            elif field == "orelse":
                lst[:] = []  # empty orelse is valid (loop/if has no else)
            else:
                lst[:] = [ast.Pass()]  # body must not be empty


# ==========================================================================
# Algorithmic additions
# ==========================================================================
def _step_vars(x):
    return [a for a in ("count", "total", "c", "k", "found", "best") for a in x] if isinstance(x, list) else []

# ---- S1: subarray-sum-equals-K via Counter prefix sums ----------------------



# ---- S2: fixed-window maximum sum → sliding window --------------------------
def _match_window_update(upd, sv):
    """`if s > best: best = s` | `best = max(best, s)` | `best = max(s, best)`  -> best name"""
    if (isinstance(upd, ast.If) and not upd.orelse and len(upd.body) == 1 and isinstance(upd.test, ast.Compare)
            and len(upd.test.ops) == 1 and isinstance(upd.test.ops[0], ast.Gt) and is_name(upd.test.left, sv)
            and isinstance(upd.test.comparators[0], ast.Name)):
        b = upd.test.comparators[0].id
        a = upd.body[0]
        if isinstance(a, ast.Assign) and len(a.targets) == 1 and is_name(a.targets[0], b) and is_name(a.value, sv):
            return b
    if (isinstance(upd, ast.Assign) and len(upd.targets) == 1 and isinstance(upd.targets[0], ast.Name)
            and isinstance(upd.value, ast.Call) and is_name(upd.value.func, "max") and len(upd.value.args) == 2 and not upd.value.keywords):
        b = upd.targets[0].id
        if {ast.unparse(x) for x in upd.value.args} == {b, sv}:
            return b
    return None




def t_count_diff_pairs(tree):
    """for i: for j>i: if a[j] - a[i] == k: c += 1  ->  one pass with a Counter of earlier values.
    Exact for all integer k (k = 0 and negatives included thanks to the sign-dependent lookup)."""
    changes = []
    for fn in [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]:
        alias = len_aliases(fn)
        for node in ast.walk(fn):
            for _, lst in iter_stmt_lists(node):
                for k, s in enumerate(lst):
                    if not (isinstance(s, ast.For) and isinstance(s.target, ast.Name) and not s.orelse and len(s.body) == 1):
                        continue
                    if _enclosing_function(s) is not fn:
                        continue
                    i_name = s.target.id
                    A = _is_plain_range_len(s.iter, alias)
                    if A is None:
                        continue
                    inner = s.body[0]
                    if not (isinstance(inner, ast.For) and isinstance(inner.target, ast.Name) and not inner.orelse and len(inner.body) == 1):
                        continue
                    j_name = inner.target.id
                    ib = _range_args(inner.iter)
                    if not (ib and isinstance(ib[0], ast.BinOp) and isinstance(ib[0].op, ast.Add)
                            and is_name(ib[0].left, i_name) and is_const_int(ib[0].right) and ib[0].right.value == 1):
                        continue
                    iff = inner.body[0]
                    if not (isinstance(iff, ast.If) and not iff.orelse and len(iff.body) == 1 and isinstance(iff.test, ast.Compare)):
                        continue
                    cmp = iff.test
                    if not (len(cmp.ops) == 1 and isinstance(cmp.ops[0], ast.Eq)):
                        continue
                    L, R = cmp.left, cmp.comparators[0]
                    if not (isinstance(L, ast.BinOp) and isinstance(L.op, ast.Sub) and isinstance(L.left, ast.Subscript)
                            and is_name(L.left.value, A) and is_name(L.left.slice, j_name)
                            and isinstance(L.right, ast.Subscript) and is_name(L.right.value, A) and is_name(L.right.slice, i_name)):
                        continue
                    # the difference is a[j] - a[i]; for a_i - a_j, flip the sign of the lookup
                    sign = 1
                    if not (isinstance(R, ast.Name) and True):
                        if is_const_int(R):
                            sign = 1
                    K = R
                    act = iff.body[0]
                    if not (isinstance(act, ast.AugAssign) and isinstance(act.op, ast.Add) and is_const_int(act.value) and act.value.value == 1):
                        continue
                    C = act.target.id if isinstance(act.target, ast.Name) else None
                    if C is None or C in (A, i_name, j_name):
                        continue
                    # K must be loop-invariant and independent of the match: it may not use the loop
                    # indices, the counter, or the array (else the Counter lookup is wrong)
                    if (node_names(K) & {i_name, j_name, C}) or (A in node_names(K)) or not _is_pure_expr(K):
                        continue
                    # R may be a negative constant (a[j] - a[i] == -2) -> lookup x + 2
                    kexpr = ast.unparse(K)
                    k_is_name = isinstance(K, ast.Name)
                    used = _all_names(tree)
                    seen, x = _fresh("seen_diff", used), _fresh("x_diff", used)
                    # a[j] - a[i] == K  =>  earlier value a[i] == a[j] - K
                    body = (f"{seen} = {{}}\nfor {x} in {A}:\n    {C} += {seen}.get({x} - ({kexpr}), 0)\n"
                            f"    {seen}[{x}] = {seen}.get({x}, 0) + 1")
                    fast = ast.parse(body).body
                    fallback = copy.deepcopy(s)
                    guard = INTSAFE.format(var=A) + (f" and type({ast.unparse(K)}) is int" if k_is_name else "")
                    wrapped = [ast.fix_missing_locations(ast.If(test=ast.parse(guard, mode="eval").body, body=fast, orelse=[fallback]))]
                    changes.append(("replace_stmt", fn.name, (lst, k, wrapped), Change(
                        "Count value-difference pairs → running Counter (ints only, fallback kept)",
                        f"Pairs with `{A}[{j_name}] - {A}[{i_name}] == {kexpr}` can be counted in one pass: keep a dict of values seen so far and add "
                        f"`seen[x - ({kexpr})]` for each element. Works for k = 0, k < 0 and duplicates. Exact for ints; "
                        "non-int items fall back to the original nested loop.",
                        fn.name, ast.unparse(s), _stmts_src(wrapped))))
    return changes


def t_reverse_build(tree):
    """res = [] ; for x in items: res.insert(0, x)  ->  res = list(reversed(items))."""
    changes = []
    for fn in [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]:
        stmts = fn.body
        for k in range(len(stmts) - 1):
            init, lp = stmts[k], stmts[k + 1]
            if not (isinstance(init, ast.Assign) and len(init.targets) == 1 and isinstance(init.targets[0], ast.Name)
                    and isinstance(init.value, ast.List) and not init.value.elts):
                continue
            res = init.targets[0].id
            if not (isinstance(lp, ast.For) and isinstance(lp.target, ast.Name) and not lp.orelse and len(lp.body) == 1
                    and isinstance(lp.body[0], ast.Expr) and isinstance(lp.body[0].value, ast.Call)
                    and call_name(lp.body[0].value) == ".insert"):
                continue
            call = lp.body[0].value
            if not (is_name(call.func.value, res) and len(call.args) == 2 and is_const_int(call.args[0]) and call.args[0].value == 0
                    and is_name(call.args[1], lp.target.id)):
                continue
            if not isinstance(lp.iter, ast.Name):
                continue
            fast = ast.parse(f"{res} = list(reversed({lp.iter.id}))").body[0]
            guarded = ast.If(test=ast.parse(f"isinstance({lp.iter.id}, (list, tuple))", mode="eval").body,
                             body=[fast], orelse=[init, lp])
            changes.append(("replace_pair", fn.name, (stmts, k, ast.fix_missing_locations(guarded)), Change(
                "Repeated insert(0) → one reversed copy (list/tuple input, fallback kept)",
                f"`{res}.insert(0, x)` shifts every element on each iteration (O(n²)). For list/tuple input the reversed copy is built once in O(n); "
                f"any other iterable keeps the original loop.",
                fn.name, _stmts_src([init, lp]), ast.unparse(guarded))))
    return changes


def t_sliding_window_loop(tree):
    """for i in range(len(a) - k + 1):
           s = 0
           for j in range(i, i + k): s += a[j]
           <best = max(best, s)>
       return best
    -> edge guards + O(n) time / O(1) extra space sliding window.
    Guards are exact: for k <= 0 every window sum is 0 (empty inner range), for k > len(a) the loop never runs."""
    changes = []
    for fn in [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]:
        alias = len_aliases(fn)
        counts = _scope_assign_counts(fn)
        mut = mutated_names(fn)
        stmts = fn.body
        for idx, lp in enumerate(stmts):
            if not (isinstance(lp, ast.For) and isinstance(lp.target, ast.Name) and not lp.orelse and len(lp.body) == 3):
                continue
            it = lp.iter
            if not (isinstance(it, ast.Call) and is_name(it.func, "range") and not it.keywords):
                continue
            args = list(it.args)
            if len(args) == 2 and is_const_int(args[0]) and args[0].value == 0:
                args = args[1:]
            if len(args) != 1:
                continue
            stop = args[0]
            if not (isinstance(stop, ast.BinOp) and isinstance(stop.op, ast.Add) and is_const_int(stop.right) and stop.right.value == 1
                    and isinstance(stop.left, ast.BinOp) and isinstance(stop.left.op, ast.Sub)):
                continue
            arr = _len_target(stop.left.left, alias)
            K = stop.left.right
            if arr is None or not _is_pure_expr(K):
                continue
            iv = lp.target.id
            init, inner, upd = lp.body
            if not (isinstance(init, ast.Assign) and len(init.targets) == 1 and isinstance(init.targets[0], ast.Name)
                    and is_const_int(init.value) and init.value.value == 0):
                continue
            sv = init.targets[0].id
            if not (isinstance(inner, ast.For) and isinstance(inner.target, ast.Name) and not inner.orelse and len(inner.body) == 1):
                continue
            ra = _range_args(inner.iter)
            jv = inner.target.id
            if not (ra and is_name(ra[0], iv) and isinstance(ra[1], ast.BinOp) and isinstance(ra[1].op, ast.Add)
                    and is_name(ra[1].left, iv) and ast.unparse(ra[1].right) == ast.unparse(K)):
                continue
            b0 = inner.body[0]
            if isinstance(b0, ast.AugAssign) and isinstance(b0.op, ast.Add) and is_name(b0.target, sv):
                val = b0.value
            elif (isinstance(b0, ast.Assign) and len(b0.targets) == 1 and is_name(b0.targets[0], sv)
                  and isinstance(b0.value, ast.BinOp) and isinstance(b0.value.op, ast.Add) and is_name(b0.value.left, sv)):
                val = b0.value.right
            else:
                continue
            if not (isinstance(val, ast.Subscript) and is_name(val.value, arr) and is_name(val.slice, jv)):
                continue
            best = _match_window_update(upd, sv)
            if best is None or best in (sv, iv, jv, arr):
                continue
            if not (idx + 1 < len(stmts) and isinstance(stmts[idx + 1], ast.Return) and is_name(stmts[idx + 1].value, best)):
                continue
            c = None
            for q in stmts[:idx]:
                if isinstance(q, ast.Assign) and len(q.targets) == 1 and is_name(q.targets[0], best):
                    c = q.value
            if not (isinstance(c, ast.Constant) and isinstance(c.value, (int, float)) and not isinstance(c.value, bool)):
                continue
            if counts.get(best, 0) != 2 or arr in mut or counts.get(arr, 0) > 0:
                continue
            if any(counts.get(nm, 0) > 0 for nm in node_names(K)):
                continue
            c_val = c.value
            g0 = max(c_val, 0)
            ksrc = ast.unparse(K)
            kp = ksrc if isinstance(K, (ast.Name, ast.Constant)) else f"({ksrc})"
            upd_src = ast.unparse(upd)
            src = (f"if {kp} <= 0:\n    return {g0!r}\n"
                   f"if {kp} > len({arr}):\n    return {c_val!r}\n"
                   f"{sv} = sum(itertools.islice({arr}, {kp}))\n{upd_src}\n"
                   f"for {iv} in range(1, len({arr}) - {kp} + 1):\n"
                   f"    {sv} = {sv} - {arr}[{iv} - 1] + {arr}[{iv} + {kp} - 1]\n{_ind(upd_src)}")
            new = ast.parse(src).body
            changes.append(("replace_stmt_import", fn.name, (stmts, idx, new, ("itertools", None)), Change(
                "Fixed-size window sum → sliding window (O(n) time, O(1) space)",
                (f"Each window differs from the previous by one element out and one in, so `{sv}` is updated in O(1). "
                 f"Edge guards are exact, not assumed: for `{ksrc} <= 0` the inner `range(i, i + {ksrc})` is empty, so every window sum is 0 "
                 f"and the result is max({c_val!r}, 0) = {g0!r}; for `{ksrc} > len({arr})` the outer loop never runs, so the result is {c_val!r}. "
                 "The first window uses itertools.islice (no slice copy). Exact for ints; floats can differ in the last bits."),
                fn.name, _stmts_src([lp]), _stmts_src(new))))
    return changes


def t_sliding_window(tree):
    """for i in range(len(a) - K + 1): w = sum(a[i:i+K]); <update best from w>   →  O(n) sliding window.
    The original loop is kept as a fallback only when K >= 1 cannot be proven (negative K wraps around in slices)."""
    changes = []
    for fn in [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]:
        alias = len_aliases(fn)
        for node in list(ast.walk(fn)):
            for _, lst in iter_stmt_lists(node):
                for idx, lp in enumerate(lst):
                    if _enclosing_function(lp) is not fn:
                        continue
                    if not (isinstance(lp, ast.For) and isinstance(lp.target, ast.Name) and not lp.orelse and len(lp.body) == 2):
                        continue
                    it = lp.iter
                    if not (isinstance(it, ast.Call) and is_name(it.func, "range") and not it.keywords):
                        continue
                    args = list(it.args)
                    if len(args) == 2 and is_const_int(args[0]) and args[0].value == 0:
                        args = args[1:]
                    if len(args) != 1:
                        continue
                    stop = args[0]
                    if not (isinstance(stop, ast.BinOp) and isinstance(stop.op, ast.Add) and is_const_int(stop.right) and stop.right.value == 1
                            and isinstance(stop.left, ast.BinOp) and isinstance(stop.left.op, ast.Sub)):
                        continue
                    arr = _len_target(stop.left.left, alias)
                    K = stop.left.right
                    if arr is None or not _is_pure_expr(K):
                        continue
                    iv = lp.target.id
                    assign, upd = lp.body
                    if not (isinstance(assign, ast.Assign) and len(assign.targets) == 1 and isinstance(assign.targets[0], ast.Name)
                            and isinstance(assign.value, ast.Call) and is_name(assign.value.func, "sum") and len(assign.value.args) == 1
                            and not assign.value.keywords and isinstance(assign.value.args[0], ast.Subscript)):
                        continue
                    wv = assign.targets[0].id
                    sub = assign.value.args[0]
                    sl = sub.slice
                    if not (is_name(sub.value, arr) and isinstance(sl, ast.Slice) and sl.step is None and sl.lower is not None and is_name(sl.lower, iv)
                            and isinstance(sl.upper, ast.BinOp) and isinstance(sl.upper.op, ast.Add)
                            and is_name(sl.upper.left, iv) and ast.unparse(sl.upper.right) == ast.unparse(K)):
                        continue
                    if iv in node_names(upd) or wv not in node_names(upd):
                        continue
                    written = names_written(ast.Module(body=[upd], type_ignores=[]))
                    if len(written) != 1 or wv in written or iv in written:
                        continue
                    if (node_names(K) | {arr}) & names_written(ast.Module(body=lp.body, type_ignores=[])):
                        continue
                    if _names_used_after(fn, [lp], {iv, wv}):
                        continue
                    kform = lin_parse(K, alias)
                    order, bounds = loop_bounds(lp, alias, fn)
                    facts = _stable_facts(collect_facts(lp, alias), fn)
                    k_pos = kform is not None and prove_nonneg(_m1(kform), order, bounds, facts=facts)
                    ksrc = ast.unparse(K)
                    kp = ksrc if isinstance(K, (ast.Name, ast.Constant)) else f"({ksrc})"
                    upd_src = ast.unparse(upd)
                    fast = (f"{wv} = sum({arr}[:{kp}])\n{upd_src}\n"
                            f"for {iv} in range(1, len({arr}) - {kp} + 1):\n"
                            f"    {wv} = {wv} - {arr}[{iv} - 1] + {arr}[{iv} + {kp} - 1]\n{_ind(upd_src)}")
                    if k_pos:
                        src = f"if len({arr}) >= {kp}:\n{_ind(fast)}"
                        why = f"`{ksrc} >= 1` is proven from earlier guards, so no fallback is needed."
                    else:
                        src = f"if {kp} < 1:\n{_ind(ast.unparse(lp))}\nelif len({arr}) >= {kp}:\n{_ind(fast)}"
                        why = (f"`{ksrc} >= 1` is NOT provable here (a negative window size makes Python slices wrap around), so the original loop is kept "
                               f"as the `{kp} < 1` fallback. Add a guard such as `if {kp} <= 0: return …` and the fallback disappears.")
                    new_node = ast.parse(src).body[0]
                    changes.append(("replace_stmt", fn.name, (lst, idx, [new_node]), Change(
                        "Sliding window for fixed-size window sums",
                        f"Each window sum differs from the previous by one element in and one out ({wv} -= a[i-1]; {wv} += a[i+k-1]): O(n) time, O(1) extra space. "
                        f"{why} Exact for ints; floats can differ in the last bits.",
                        fn.name, _stmts_src([lp]), ast.unparse(new_node))))
    return changes


# ---- S3: reachability / dead-branch elimination -----------------------------
def _splice_stmts(stmt, new):
    parent = getattr(stmt, "_parent", None)
    if parent is None:
        return False
    for field, lst in iter_stmt_lists(parent):
        for i, s in enumerate(lst):
            if s is stmt:
                lst[i:i + 1] = list(new)
                if not lst and field not in ("orelse", "finalbody"):
                    lst.append(ast.Pass())
                return True
    return False


def t_dead_branch(tree):
    """Reachability pass.  Uses enclosing loop bounds, dominating `if C: return/raise` guards and asserts to
    (a) delete branches whose guard is provably false, (b) drop provably-true conjuncts / inline provably-true branches."""
    changes = []
    for scope in [tree] + [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]:
        fn = scope if isinstance(scope, ast.FunctionDef) else None
        alias = len_aliases(scope)
        for n in list(ast.walk(scope)):
            if not isinstance(n, (ast.If, ast.IfExp)) or _enclosing_function(n) is not fn:
                continue
            mode, dropped, extra = simplify_guard(n.test, n, alias, scope)
            if mode == "keep":
                continue
            is_stmt = isinstance(n, ast.If)
            fname = fn.name if fn else "<module>"
            test_src = ast.unparse(n.test)
            before = f"if {test_src}: …" if is_stmt else ast.unparse(n)
            if mode == "true":
                title = "Guard provably true — else branch removed" if n.orelse else "Guard provably true — test removed"
                after = _stmts_src(n.body) if is_stmt else ast.unparse(n.body)
                detail = f"Proved from enclosing loop bounds and earlier guards: {', '.join(dropped)}. The else branch can never run."
            elif mode == "false":
                title = "Dead branch removed — guard provably false"
                after = ((_stmts_src(n.orelse) if n.orelse else "# removed") if is_stmt else ast.unparse(n.orelse))
                detail = f"`{extra}` is provably false here (loop bounds / an earlier `if … : return`), so this branch is unreachable."
            else:
                title = "Guard simplified — provably-true conjuncts dropped"
                after = ast.unparse(extra)
                before = test_src
                detail = f"Proved from loop bounds / earlier guards and dropped: {', '.join(dropped)}."
            changes.append(("dead_branch", fname if fn else None, (n, mode, extra if mode == "new" else None),
                            Change(title, detail, fname, before, after, kind="constant")))
        # Empty-range loop elimination: `for j in range(lo, hi): ...` where lo >= hi is provably true
        # (e.g. inside `else:` of `if k >= 0:`, `range(i, i + k)` has i - (i + k) = -k >= 1 >= 0 -> 0 iterations).
        mut = mutated_names(scope)
        for lp in list(ast.walk(scope)):
            if not isinstance(lp, ast.For) or _enclosing_function(lp) is not fn:
                continue
            ra = _range_args(lp.iter)
            if ra is None:
                continue
            lo, hi = ra
            lo_l, hi_l = lin_parse(lo, alias), lin_parse(hi, alias)
            if lo_l is None or hi_l is None:
                continue
            if any(sy.startswith("len:") and sy[4:] in mut for sy in list(lo_l) + list(hi_l)):
                continue
            order, bounds = loop_bounds(lp, alias, scope)
            facts = _stable_facts(collect_facts(lp, alias), scope)
            if prove_nonneg(lin_add(lo_l, hi_l, -1), order, bounds, facts=facts):
                fname = fn.name if fn else "<module>"
                after = _stmts_src(lp.orelse) if lp.orelse else "# empty range loop removed"
                changes.append(("dead_branch", fname if fn else None, (lp, "empty_loop", None),
                                Change("Empty-range loop removed",
                                       f"`{ast.unparse(lp.iter)}` is provably empty here (`{ast.unparse(lo)} >= {ast.unparse(hi)}`), so the loop never executes.",
                                       fname, ast.unparse(lp), after, kind="complexity")))
    return changes


def apply_dead_branch(tree, payload):
    node, mode, new_test = payload
    if mode == "empty_loop":
        _splice_stmts(node, node.orelse)
        return
    if isinstance(node, ast.IfExp):
        if mode == "true":
            _replace_node(tree, node, node.body)
        elif mode == "false":
            _replace_node(tree, node, node.orelse)
        else:
            node.test = new_test
        return
    if mode == "new":
        node.test = new_test
    elif mode == "true":
        _splice_stmts(node, node.body)
    else:
        _splice_stmts(node, node.orelse)


def apply_if_true(tree, payload):
    lst, idx, s = payload
    # guard is provably true: else is unreachable — keep only the body
    new_body = list(s.body)
    lst[idx:idx + 1] = new_body if new_body else [ast.Pass()]


def apply_dead_branch_remove(tree, payload):
    lst, idx, s = payload
    del lst[idx]


def _false_branch_guard(guard, lst, idx, alias, fn):
    """True if the guard is provably false at lst[idx]."""
    earlier = lst[:idx]
    if not (isinstance(guard, ast.Compare) and len(guard.ops) == 1 and isinstance(guard.ops[0], ast.Eq)):
        return False
    L, R = guard.left, guard.comparators[0]
    for q in earlier:
        if not (isinstance(q, ast.If) and not q.orelse and len(q.body) == 1 and isinstance(q.body[0], ast.Return)):
            continue
        test = q.test
        # `if not arr: return`  (arr is a Name)  → afterwards len(arr) >= 1
        if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not) and isinstance(test.operand, ast.Name):
            n = test.operand.id
            if isinstance(L, ast.Call) and is_name(L.func, "len") and len(L.args) == 1 and is_name(L.args[0], n) and isinstance(R, ast.Constant) and R.value == 0:
                return True
            if is_name(L, n) and isinstance(R, ast.Constant) and R.value is False:
                return True
            # `if not len(arr): return`  → afterwards len(arr) >= 1
            if isinstance(L, ast.Call) and is_name(L.func, "len") and len(L.args) == 1 and is_name(L.args[0], n):
                if isinstance(R, ast.Constant) and R.value == 0:
                    return True
        # `if len(arr) == 0: return` → afterwards len(arr) >= 1
        if isinstance(test, ast.Compare) and len(test.ops) == 1 and isinstance(test.ops[0], ast.Eq):
            lt, rr = test.left, test.comparators[0]
            if isinstance(lt, ast.Call) and is_name(lt.func, "len") and len(lt.args) == 1 and isinstance(lt.args[0], ast.Name):
                arr2 = lt.args[0].id
                if isinstance(rr, ast.Constant) and rr.value == 0:
                    if isinstance(L, ast.Call) and is_name(L.func, "len") and len(L.args) == 1 and is_name(L.args[0], arr2) and isinstance(R, ast.Constant) and R.value == 0:
                        return True
                    if isinstance(L, ast.Call) and is_name(L.func, "len") and len(L.args) == 1 and is_name(L.args[0], arr2) and isinstance(R, ast.Constant) and R.value == 0:
                        return True
    return False


def _guard_always_true(guard, idx, lst, alias, fn):
    """True if the whole guard expression can be shown to hold at this point in the list."""
    # collect loop bounds for the enclosing loop of the guard
    call = _enclosing_function(lst[idx]) if isinstance(lst[idx], ast.expr_context) else None
    # walk enclosing loops of the statement
    loops = enclosing_loops(lst[idx])
    order, bounds = loop_bounds(lst[idx], alias, fn) if isinstance(lst[idx], ast.AST) else ([], {})
    # guard = sequence of comparisons joined by And
    comparisons = []
    if isinstance(guard, ast.BoolOp) and isinstance(guard.op, ast.And):
        comparisons = [v for v in guard.values if isinstance(v, ast.Compare)]
    elif isinstance(guard, ast.Compare):
        comparisons = [guard]
    else:
        return False
    # split chained comparisons into pairwise leaves
    leaves = []
    for cg in comparisons:
        if isinstance(cg, ast.Compare) and len(cg.ops) > 1:
            parts = [cg.left] + list(cg.comparators)
            for op, a, b in zip(cg.ops, parts, parts[1:]):
                leaves.append((a, op, b))
        else:
            leaves.append((cg.left, cg.ops[0], cg.comparators[0]))
    for a, op, b in leaves:
        # reconstruct a single-op Compare
        leaf = ast.Compare(left=a, ops=[op], comparators=[b])
        if not _cmp_proven(leaf, order, bounds, alias):
            return False
    return True


def _cmp_proven(cg, order, bounds, alias):
    Lt, R = cg.left, cg.comparators[0]
    ops = cg.ops
    form = lin_parse(Lt, alias)
    if form is None or len(cg.ops) != 1:
        return False
    op = ops[0]
    rf = lin_parse(R, alias)
    if rf is None:
        return False
    delta = lin_add(form, rf, -1)
    if isinstance(op, ast.Gt):
        return prove_nonneg(delta, order, bounds, strict=True)
    if isinstance(op, ast.Lt):
        return prove_nonneg({k: -v for k, v in delta.items()}, order, bounds, strict=True)
    if isinstance(op, ast.GtE):
        return prove_nonneg(delta, order, bounds)
    if isinstance(op, ast.LtE):
        return prove_nonneg({k: -v for k, v in delta.items()}, order, bounds)
    if isinstance(op, ast.Eq):
        return all(abs(v) < 1e-12 for v in delta.values())
    return False

# ---- S5: unused pure variable elimination (dead_code rule) -------------------

# ---- cleanup helpers: purity / structure ----
_PURE_CALLS = {"list", "tuple", "set", "dict", "range", "len", "reversed", "sorted", "str", "int", "float", "abs",
               "min", "max", "sum", "enumerate", "zip", "bool", "frozenset"}


def _pure(e):
    """Expression with no side effects and no resolvable handles to user-defined/global functions."""
    for n in ast.walk(e):
        if isinstance(n, ast.Call):
            if isinstance(n.func, ast.Attribute) and n.func.attr == "join" and isinstance(n.func.value, ast.Constant):
                continue
            if not (isinstance(n.func, ast.Name) and n.func.id in _PURE_CALLS):
                return False
        elif isinstance(n, ast.Subscript):
            if not isinstance(n.slice, ast.Slice):
                return False
        elif isinstance(n, ast.Attribute):
            if n.attr == "join" and isinstance(n.value, ast.Constant):
                continue
            return False
        elif isinstance(n, (ast.Await, ast.Yield, ast.YieldFrom, ast.NamedExpr, ast.Lambda)):
            return False
    return True


def _is_boolish(e):
    """True if the expression is already a boolean-ish (given the 'not' handling in the caller)."""
    if isinstance(e, ast.Compare):
        return True
    if isinstance(e, ast.UnaryOp) and isinstance(e.op, ast.Not):
        return True
    if isinstance(e, ast.BoolOp):
        return all(_is_boolish(v) for v in e.values)
    if isinstance(e, ast.Constant) and isinstance(e.value, bool):
        return True
    if isinstance(e, ast.Call) and (
        (isinstance(e.func, ast.Attribute) and e.func.attr.startswith("is"))
        or (isinstance(e.func, ast.Name) and e.func.id in ("isinstance", "any", "all", "bool", "callable", "hasattr"))
        or (isinstance(e.func, ast.Attribute) and e.func.attr in ("startswith", "endswith"))):
        return True
    return False


def t_dead_code(tree):
    """Remove pure assignments (and mutation-only statements on them) that are never read."""
    changes = []
    for scope in [tree] + [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]:
        fn = scope if isinstance(scope, ast.FunctionDef) else None
        for node in ast.walk(scope):
            for _, lst in iter_stmt_lists(node):
                for k, s in enumerate(lst):
                    if _enclosing_function(s) is not fn:
                        continue
                    if not (isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name) and _pure(s.value)):
                        continue
                    name = s.targets[0].id
                    if fn is not None and name in {a.arg for a in fn.args.args}:
                        continue
                    if fn is None and name in _all_names(tree) and any(isinstance(n, ast.FunctionDef) and name in node_names(n) for n in ast.walk(tree)):
                        continue
                    if any(isinstance(n, (ast.Global, ast.Nonlocal)) for n in ast.walk(scope)):
                        continue
                    # find all loads of the name — the only acceptable context is inside
                    # a call whose attribute is one of the mutation methods (sort/reverse/append/extend/clear)
                    other = False
                    for n in ast.walk(scope):
                        if not (isinstance(n, ast.Name) and n.id == name and isinstance(n.ctx, ast.Load)):
                            continue
                        p = getattr(n, "_parent", None)
                        pp = getattr(p, "_parent", None)
                        a = getattr(p, "_parent", None) if False else None
                        if not (isinstance(p, ast.Attribute) and isinstance(pp, ast.Call) and pp.func is p
                                and isinstance(pp._parent, ast.Expr)
                                and p.attr in ("sort", "reverse", "append", "extend", "clear")
                                and all(_pure(aa) for aa in pp.args)):
                            other = True
                            break
                    if other:
                        continue
                    if _load_count(scope, name) == 0:
                        pass  # truly unused
                    extra = []
                    for n in ast.walk(scope):
                        if isinstance(n, ast.Expr) and isinstance(n.value, ast.Call) and isinstance(n.value.func, ast.Attribute):
                            if is_name(n.value.func.value, name) and n.value.func.attr in ("sort", "reverse", "append", "extend", "clear") and all(_pure(a) for a in n.value.args):
                                extra.append(n)
                    changes.append(("remove_stmts", fn.name if fn else None, (scope, [s] + extra), Change(
                        f"Unused variable `{name}` removed",
                        "The value is pure and never read after earlier rewrites.",
                        fn.name if fn else "<module>", _stmts_src([s] + extra), "# removed", kind="constant")))
    return changes


# ---- self-matching protection -------------------------------------------------------
# A rewrite keeps the ORIGINAL code as a runtime fallback (inside `if <guard>: … else: <original>`).
# Finders must never match inside that fallback, or a rule rewrites its own output and nests forever.
_GUARD_CALLS = {"all", "any"}


def _is_guard_test(test):
    """True for the runtime guards this engine generates:
    an `all(...)` type guard, an `isinstance(...)` element guard, a `type(x) is <type>` check,
    `X is (not) None`, or a conjunction containing one of those (e.g. `all(int items) and type(k) is int`)."""
    if isinstance(test, ast.BoolOp):
        if isinstance(test.op, ast.And):
            return any(_is_guard_test(v) for v in test.values)   # one guarded conjunct makes the whole test a guard
        return all(_is_guard_test(v) for v in test.values)
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        return False                                            # our guards are never negated
    if isinstance(test, ast.Call):
        if isinstance(test.func, ast.Name) and test.func.id in _GUARD_CALLS:
            return True
        if isinstance(test.func, ast.Name) and test.func.id == "isinstance":
            return True
        if isinstance(test.func, ast.Name) and test.func.id == "type" and len(test.args) == 1:
            return True
    if isinstance(test, ast.Compare) and len(test.ops) == 1 and len(test.comparators) == 1:
        if isinstance(test.ops[0], (ast.Is, ast.IsNot)):
            if isinstance(test.comparators[0], ast.Constant) and test.comparators[0].value is None:
                return True
            # `type(x) is int` / `type(x) is str`
            if isinstance(test.left, ast.Call) and isinstance(test.left.func, ast.Name) and test.left.func.id == "type" \
                    and isinstance(test.comparators[0], ast.Constant) and isinstance(test.comparators[0].value, str):
                return True
        if isinstance(test.ops[0], ast.Eq):
            # `type(x) == int`
            if isinstance(test.left, ast.Call) and isinstance(test.left.func, ast.Name) and test.left.func.id == "type":
                return True
    return False


def in_generated_fallback(node, _root=None):
    """True if `node` sits inside the `orelse` of an If whose test is an engine-generated guard."""
    cur = getattr(node, "_parent", None)
    hops = 0
    while cur is not None and hops < 400:
        hops += 1
        if isinstance(cur, ast.If) and cur.orelse and _is_guard_test(cur.test):
            for st in cur.orelse:
                if any(st is node for node in [st]) or _contains(st, node):
                    return True
        cur = getattr(cur, "_parent", None)
    return False


def _contains(root, node):
    return any(n is node for n in ast.walk(root))


_REWRITE_TREE = {}


def _set_rewrite_tree(tree):
    """the tree finders are currently looking at (for kinds whose payload carries no AST node)"""
    _REWRITE_TREE["tree"] = tree


def _already_guarded_fn(fn_name):
    tree = _REWRITE_TREE.get("tree")
    if tree is None or not fn_name:
        return False
    fn = next((n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef) and n.name == fn_name), None)
    return bool(fn is not None and fn.body and isinstance(fn.body[0], ast.If) and _is_guard_test(fn.body[0].test) and fn.body[0].orelse)


def _filter_generated(cands):
    """Drop candidates whose payload statements are inside a generated fallback, and drop whole-function
    rewrites of a function that is already wrapped in a generated guard (it would wrap itself again)."""
    out = []
    for kind, fn_name, payload, change in cands:
        nodes = []
        for p in (payload if isinstance(payload, tuple) else (payload,)):
            if isinstance(p, ast.AST):
                nodes.append(p)
            elif isinstance(p, (list, tuple)):
                nodes += [x for x in p if isinstance(x, ast.AST)]
        if any(in_generated_fallback(n) for n in nodes):
            continue
        if kind == "fn_body" and _already_guarded_fn(fn_name):
            continue
        out.append((kind, fn_name, payload, change))
    return out


def apply_change(tree, kind, payload, analyzer):
    if kind == "fn_body":
        fn_name, new_body = payload
        for n in ast.walk(tree):
            if isinstance(n, ast.FunctionDef) and n.name == fn_name:
                n.body = new_body
    elif kind == "replace_stmt":
        stmts, k, new = payload
        stmts[k:k + 1] = new
    elif kind == "replace_stmt_import":
        stmts, k, new, imp = payload
        stmts[k:k + 1] = new
        _ensure_import(tree, *imp)
    elif kind == "list_as_set":
        apply_list_as_set(tree, payload)
    elif kind == "shadow_set":
        apply_shadow_set(tree, payload)
    elif kind == "insert_top":
        t, nodes = payload
        t.body = nodes + t.body
    elif kind == "replace_pair":
        stmts, k, new = payload
        stmts[k:k + 2] = [new]
    elif kind == "replace_iter":
        lp, new_iter, imp = payload
        lp.iter = new_iter
        _ensure_import(tree, *imp)
    elif kind == "decorate":
        fn, deco, imp = payload
        fn.decorator_list.insert(0, deco)
        _ensure_import(tree, *imp)
    elif kind == "memo_guard":
        apply_memo_guard(tree, payload)
    elif kind == "membership":
        apply_membership(tree, payload)
    elif kind == "counter":
        apply_counter(tree, payload)
    elif kind == "nested_eq":
        apply_nested_eq(tree, payload)
    elif kind == "hoist":
        apply_hoist(tree, payload)
    elif kind == "strjoin":
        apply_strjoin(tree, payload)
    elif kind == "deque":
        apply_deque(tree, payload)
    elif kind == "replace_region":
        lst, st, L, new_stmts, imports = payload
        lst[st:st + L] = new_stmts
        for imp in imports:
            _ensure_import(tree, imp)
    elif kind == "replace_multi":
        lst, min_idx, k, removable_idx, new_stmts, imports = payload
        del_positions = set(removable_idx)
        for idx in sorted(del_positions, reverse=True):
            del lst[idx]
        deleted_before_k = sum(1 for i in del_positions if i < k)
        new_k = k - deleted_before_k
        assert isinstance(lst[new_k], ast.Return)
        lst[new_k:new_k + 1] = new_stmts
        for imp in imports:
            _ensure_import(tree, imp)
    elif kind == "prefix":
        apply_prefix(tree, payload)
    elif kind == "canon":
        apply_canon(tree, payload)
    elif kind == "remove_stmts":
        apply_remove_stmts(tree, payload)
    elif kind == "dead_branch":
        apply_dead_branch(tree, payload)
    elif kind == "if_true":
        apply_if_true(tree, payload)
    elif kind == "dead_branch_remove":
        apply_dead_branch_remove(tree, payload)
    elif kind == "keys":
        cmp_node, d = payload
        cmp_node.comparators[0] = d
    elif kind == "literal_set":
        cmp_node, rhs = payload
        cmp_node.comparators[0] = ast.Set(elts=rhs.elts)


_CURRENT_FN_TYPES = {}
PORTABLE_RULES = {"direct_join", "strjoin"}
_LAST_GATE = {}

_FINDERS = {
    "algo": lambda t, a: t_algo_templates(t),
    "pairs": lambda t, a: t_pair_patterns(t),
    "memo": lambda t, a: t_memoize(t, a),
    "prime": lambda t, a: t_prime_sqrt(t),
    "sort": lambda t, a: t_sort_detection(t),
    "membership": lambda t, a: t_membership_set(t, a),
    "shadow_set": lambda t, a: t_shadow_set(t),
    "counter": lambda t, a: t_count_counter(t),
    "nested_eq": lambda t, a: t_nested_equality(t),
    "deque": lambda t, a: t_deque(t),
    "closed_form": lambda t, a: t_closed_form(t),
    "direct_join": lambda t, a: t_direct_join(t),
    "strjoin": lambda t, a: t_string_join(t),
    "prefix_sum": lambda t, a: t_prefix_sum(t),
    "count_diff": lambda t, a: t_count_diff_pairs(t),
    "reverse_build": lambda t, a: t_reverse_build(t),
    "sliding_window_loop": lambda t, a: t_sliding_window_loop(t),
    "sliding_window": lambda t, a: t_sliding_window(t),
    "idioms": lambda t, a: t_idioms(t),
    "canon_reverse": lambda t, a: t_canon_reverse(t),
    "canon_revrange": lambda t, a: t_canon_revrange(t),
    "canon_diagonal": lambda t, a: t_canon_diagonal(t),
    "palindrome_general": lambda t, a: t_palindrome_general(t, _CURRENT_FN_TYPES),
    "manual_seq_eq": lambda t, a: t_manual_seq_eq(t),
    "dead_len": lambda t, a: t_dead_len_check(t),
    "hoist": lambda t, a: t_hoist(t),
    "dead_branch": lambda t, a: t_dead_branch(t),
    "dead_code": lambda t, a: t_dead_code(t),
    "cleanup": lambda t, a: t_cleanup(t),
    "fast_io": lambda t, a: t_fast_io(t),
}

_CONSTANT_FACTOR_MULTI_PASS = {
    "nested_eq", "direct_join", "dead_len", "manual_seq_eq", "algo", "prefix_sum",
    "canon_reverse", "canon_revrange", "canon_diagonal", "palindrome_general", "cleanup",
    "idioms", "dead_branch", "dead_code", "subarray_sum_k", "sliding_window", "strjoin", "pairs", "membership",
}

# Phased pipeline (do NOT interleave; complete one phase before the next):
#   1. algorithmic — asymptotic wins (Kadane/LIS/hashmap/prefix-sum/Counter/memoize/sort/queues)
#   2. canonicalization — normalize code into forms Phase 3 can recognize
#   3. idiom — recognize palindrome / seq-eq / dead length / hoisting
#   4. dead-code — reachability elimination + unused variables
#   5. cleanup — booleans, temps, single-expression collapse
PHASES = [
    "algorithmic",
    "canonicalization",
    "idiom",
    "dead_code",
    "cleanup",
]
PHASE_ORDER = {
    "algorithmic": ["algo", "count_diff", "reverse_build", "pairs", "memo", "prime", "sort", "membership",
                    "shadow_set", "counter", "nested_eq", "deque", "closed_form", "direct_join", "strjoin",
                    "sliding_window_loop", "sliding_window", "prefix_sum", "hoist", "idioms"],
    "canonicalization": ["canon_reverse", "canon_revrange", "canon_diagonal"],
    "idiom": ["manual_seq_eq", "palindrome_general", "dead_len"],
    "dead_code": ["dead_branch", "dead_code"],
    "cleanup": ["cleanup", "fast_io"],
}
_ALGO_PHASES = {"algorithmic"}
_MULTI_PASS = _CONSTANT_FACTOR_MULTI_PASS


class _quiet:
    def __enter__(self):
        self.old = sys.stdout
        sys.stdout = io.StringIO()

    def __exit__(self, *a):
        sys.stdout = self.old


# Explicit differential-verification input-size cap table by static complexity class.
# Super-exponential functions MUST be capped so verification finishes in milliseconds:
#   fib(10) = 55 (~0.1 ms) vs fib(28) = 317,811 (~780 ms; 100 cases = 78 s).
VERIFICATION_CAPS = {
    "O(n!)":  7,      # range(1, 8)
    "O(2^n)": 10,     # range(1, 11)
    "O(n^3)": 50,     # n <= 50
    "O(n^2)": 200,    # n <= 200
    "O(n)":   None,   # no cap
}


def _fn_int_cap(analyzer, fn_name):
    """Return the integer input cap for differential testing from VERIFICATION_CAPS,
    computed on the ORIGINAL (unmutated) AST.  Any recursive function is capped hard:
    a bad argument can turn a 0.1 ms call into minutes."""
    try:
        if fn_name in analyzer.functions:
            fn = analyzer.functions[fn_name]
            if analyzer.recursion_info(fn) and not analyzer.is_memoized(fn):
                return min(VERIFICATION_CAPS["O(2^n)"], 12)
            c = analyzer.function_cost(fn_name)
            if c.fact:
                return VERIFICATION_CAPS["O(n!)"]
            if c.e:
                return VERIFICATION_CAPS["O(2^n)"]
            if c.p >= 3:
                return VERIFICATION_CAPS["O(n^3)"]
            if c.p >= 2:
                return VERIFICATION_CAPS["O(n^2)"]
            return VERIFICATION_CAPS["O(n)"]
    except Exception:
        pass
    return None


def _fn_is_exp(analyzer, fn_name):
    """True iff static analysis classifies fn_name as O(2^n) or worse (O(n!))."""
    try:
        if fn_name in analyzer.functions:
            c = analyzer.function_cost(fn_name)
            return bool(c.fact or c.e)
    except Exception:
        pass
    return False


def _run_finder(tname, tree, analyzer):
    """Every finder goes through here: generated fallbacks are invisible to it."""
    _set_rewrite_tree(tree)
    return _filter_generated(_FINDERS[tname](tree, analyzer))


WHOLE_FUNCTION_KINDS = {"fn_body", "decorate", "memo_guard"}


def gate_candidate(tname, fn_name, tree, analyzer, fn_types, change):
    """The single decision point for skip-vs-attempt. Returns a reason string, or None to proceed.
    Used by the main loop and, identically, by the convergence check."""
    targets = [fn_name] if fn_name else [n.name for n in ast.walk(tree) if isinstance(n, ast.FunctionDef) and change.before in ast.unparse(n)]
    for tgt in (targets or [None]):
        node = analyzer.functions.get(tgt) if tgt else tree
        if node is None:
            continue
        nd = static_nondeterminism(node)
        if nd:
            return f"non-deterministic ({nd})"
        pp = purity_problem(node, memo=(tname == "memo"), tags=fn_types.get(tgt) if tgt else None)
        if pp:
            return pp
    tags_here = fn_types.get(fn_name) if fn_name else None
    if tname in ("idioms", "closed_form"):
        tgt_node = analyzer.functions.get(fn_name) if fn_name else tree
        if isinstance(tgt_node, ast.FunctionDef):
            ftags = dict(zip([a.arg for a in tgt_node.args.args], tags_here or []))
            try:
                region = ast.parse(change.before) if change.before else None
            except SyntaxError:
                region = None
            accumulates_float = bool(
                (region and any(isinstance(x, ast.Constant) and isinstance(x.value, float) for x in ast.walk(region)))
                or any(v == "float" for v in ftags.values()))
            if accumulates_float:
                return "may accumulate floats (sum()/closed forms change rounding)"
    if tname == "closed_form" and any(x in change.before for x in ("random", "time.", "input(", "open(")):
        return "loop term is not loop-invariant"
    return None



class _Phases:
    """Wall-clock phase log: every phase reports its own delta, so no part of a run is silent."""

    def __init__(self):
        self.marks = [time.perf_counter()]
        self.rows = []

    def done(self, name):
        now = time.perf_counter()
        dt = now - self.marks[0]
        self.marks[0] = now
        self.rows.append((name, dt))
        _progress("phase", f"{name}: {dt:.2f}s")


def optimize(source, fn_types, program_stdout, program_fast, hints=None):
    """Return (optimized_source, [Change], notes).
    A rewrite is kept only if (1) it compiles, (2) it is behaviour-identical on the verification inputs and
    (3) an interleaved A/B timing does not show it to be measurably slower."""
    global _CURRENT_FN_TYPES
    _CURRENT_FN_TYPES = fn_types
    _ph = _Phases()
    # Pre-scan: record why whole-class rules cannot apply, even when no candidate is produced.
    prescan = []
    try:
        _ptree = set_parents(ast.parse(source))
        _pan = StaticAnalyzer(_ptree)
        for _fn in [n for n in ast.walk(_ptree) if isinstance(n, ast.FunctionDef)]:
            _nd = static_nondeterminism(_fn)
            if _nd:
                prescan.append({"function": _fn.name, "rule": "all rules", "reason": f"non-deterministic ({_nd})"})
            if _pan.recursion_info(_fn):
                _pp = purity_problem(_fn, memo=True, tags=fn_types.get(_fn.name))
                if _pp:
                    prescan.append({"function": _fn.name, "rule": "memo", "reason": _pp})
    except Exception:
        pass
    current = source
    changes_out = []
    notes = []
    skipped = []
    rejected_keys = set()
    # Each rewrite SITE (rule + function + code being replaced) is rewritten at most once, so a rule
    # can never re-match its own output; a rule may still fire on several distinct sites in one function.
    applied_keys = set()
    for outer in range(3):
        before_outer = current
        for phase_name in PHASES:
            for tname in PHASE_ORDER[phase_name]:
                finder = _FINDERS[tname]
                for attempt in range(8):
                    tree = set_parents(ast.parse(current))
                    analyzer = StaticAnalyzer(tree)
                    try:
                        cands = _run_finder(tname, tree, analyzer)
                    except Exception as e:  # noqa
                        notes.append(f"{tname}: finder error {type(e).__name__}: {e}")
                        break
                    if not cands:
                        break
                    applied_any = False
                    for kind, fn_name, payload, change in cands:
                        tree = set_parents(ast.parse(current))
                        an2 = StaticAnalyzer(tree)
                        fresh = _run_finder(tname, tree, an2)
                        match = None
                        for fk, ffn, fpayload, fchange in fresh:
                            if fchange.title == change.title and fchange.before == change.before and fchange.after == change.after:
                                match = (fk, ffn, fpayload, fchange)
                                break
                        if match is None:
                            continue
                        kind, fn_name, payload, change = match
                        if (change.title, change.before) in rejected_keys:
                            continue
                        if (tname, fn_name, change.before) in applied_keys:
                            continue
                        change.rule = tname
                        # whole-function rewrites apply at most once per (rule, function); statement rules
                        # apply at most once per rewrite SITE (a function may legitimately have two `s +=` loops)
                        if kind in WHOLE_FUNCTION_KINDS and (tname, fn_name) in applied_keys:
                            continue
                        if (tname, fn_name, change.before) in applied_keys:
                            continue
                        gate = gate_candidate(tname, fn_name, tree, analyzer, fn_types, change)
                        if gate:
                            change.status = "skipped"
                            change.message = gate
                            skipped.append({"function": fn_name or "<module>", "rule": tname, "reason": gate})
                            changes_out.append(change)
                            notes.append(f"skipped {tname} on {fn_name or '<module>'}: {gate}")
                            continue
                        if change.kind == "advice":
                            change.status = "suggested"
                            change.message = ("Advice only — never applied automatically: it changes semantics "
                                              "(trailing newline is kept, EOF returns '' instead of raising EOFError) and cannot be verified without stdin.")
                            changes_out.append(change)
                            continue
                        orig_cap = _fn_int_cap(analyzer, fn_name) if fn_name else None
                        orig_exp = _fn_is_exp(analyzer, fn_name) if fn_name else False
                        try:
                            apply_change(tree, kind, payload, an2)
                            new_src = dump_src(tree)
                            compile(new_src, "<opt>", "exec")
                        except Exception as e:  # noqa
                            change.status = "rejected"
                            change.message = f"could not apply: {type(e).__name__}: {e}"
                            changes_out.append(change)
                            continue
                        _progress("optimize", f"rule `{tname}` matched in {fn_name or '<module>'}: {change.title}", {"title": change.title, "rule": tname})
                        ok, msg, cap, ab = True, "", orig_cap, None
                        res_inconclusive = False
                        ver = {"method": "none", "inputs": 0, "valid": 0, "exception_parity": 0}
                        if fn_name and fn_name in fn_types:
                            res = differential_test(current, new_src, fn_name, fn_types[fn_name], int_cap=cap,
                                                    slow=(0.001 if orig_exp else 0.01), hints=hints,
                                                    source_tree=set_parents(ast.parse(current)))
                            res_inconclusive = bool(res.get("inconclusive"))
                            ok, msg = res["ok"], res["msg"]
                            ver = {"method": "differential testing", "inputs": res["run"], "valid": res["valid"], "exception_parity": res["exc"], "capped": res.get("capped", False), "budget_hit": res.get("budget_hit", False)}
                            if ok and res["valid"] == 0:
                                if program_fast and program_stdout.strip():
                                    r = run_program(new_src, repeats=1)
                                    ok = r.ok and r.stdout == program_stdout
                                    ver = {"method": "program output (no valid generated inputs)", "inputs": 1, "valid": 1 if ok else 0, "exception_parity": 0}
                                    msg = "program output identical" if ok else "program output differs"
                                else:
                                    ok = False
                                    msg = "no valid inputs could be generated for this signature, so equivalence cannot be checked — not applied"
                        elif program_fast and program_stdout.strip():
                            r = run_program(new_src, repeats=1)
                            ok = r.ok and r.stdout == program_stdout
                            ver = {"method": "program output", "inputs": 1, "valid": 1 if ok else 0, "exception_parity": 0}
                            msg = "program output identical" if ok else ("program output differs" if r.ok else r.error)
                        else:
                            ok = False
                            msg = "top-level rewrite cannot be verified (program is slow or prints nothing) — not applied"
                        if ok and fn_name and fn_name in fn_types:
                            with _quiet():
                                ab = ab_guard(current, new_src, fn_name, fn_types[fn_name], exp_like=orig_exp)
                            if ab_guard_regression(ab) and tname not in PORTABLE_RULES:
                                saved = dict(STRATEGY)
                                set_strategy(list="unique", secondary="half", primary="n")
                                with _quiet():
                                    ab2 = ab_guard(current, new_src, fn_name, fn_types[fn_name], exp_like=orig_exp)
                                STRATEGY.update(saved)
                                if ab2 and ab2.get("ratio") and not ab_guard_regression(ab2):
                                    notes.append(f"{change.title}: slower on the worst-case input shape ({1 / ab['ratio']:.2f}× slower) "
                                                 f"but {ab2['ratio']:.2f}× faster on the default shape — kept")
                                    ab = ab2
                                else:
                                    ok = False
                                    msg = (f"measured {1 / ab['ratio']:.2f}× SLOWER at n={ab['n']} (spread ±{ab['noise'] * 100:.1f}%) "
                                           "on both the worst-case and default input shapes — rejected by the regression guard")
                        change.verification = ver
                        change.ab = ({"ratio": ab["ratio"], "noise": ab["noise"], "n": ab["n"]} if ab and ab["ratio"] else None)
                        if ok:
                            change.status = "applied"
                            if ver["method"] == "differential testing":
                                change.message = (f"verified against the previous version on {ver['valid']} valid inputs" + ("; integer inputs capped where the original exceeded 10 ms per call" if ver.get("capped") else "") + ("; stopped at the 1.5 s verification budget" if ver.get("budget_hit") else "")
                                                + (f" (+{ver['exception_parity']} inputs where both raise the same exception)" if ver["exception_parity"] else ""))
                            else:
                                change.message = msg
                            if change.ab:
                                change.message += (f"; A/B at n={change.ab['n']}: {change.ab['ratio']:.2f}× "
                                                   f"(noise ±{change.ab['noise'] * 100:.0f}%)")
                            elif fn_name and fn_name in fn_types:
                                change.message += "; A/B timing unavailable for this function"
                            if tname in PORTABLE_RULES:
                                change.portable = True
                                change.portable_note = _portable_note(change)
                            current = new_src
                            applied_keys.add((tname, fn_name, change.before))
                            if kind in WHOLE_FUNCTION_KINDS:
                                applied_keys.add((tname, fn_name))
                            changes_out.append(change)
                            applied_any = True
                            _progress("optimize", f"✔ Applied: {change.title}", {"title": change.title, "status": "applied"})
                            if kind == "fn_body":
                                break
                        elif res_inconclusive:
                            change.status = "inconclusive"
                            change.message = f"not applied — {msg}"
                            skipped.append({"function": fn_name or "<module>", "rule": tname, "reason": msg})
                            rejected_keys.add((change.title, change.before))
                            changes_out.append(change)
                            _progress("optimize", f"? Inconclusive: {change.title} ({msg})", {"title": change.title, "status": "inconclusive"})
                        else:
                            change.status = "rejected"
                            change.message = f"reverted — {msg}"
                            rejected_keys.add((change.title, change.before))
                            changes_out.append(change)
                            _progress("optimize", f"✘ Reverted: {change.title} ({msg})", {"title": change.title, "status": "rejected"})
                    if not applied_any or tname not in _MULTI_PASS:
                        break
        if _same_code(before_outer, current):
            break
    # final cleanup pass: dead branches / unused variables / trivial returns left behind by earlier rewrites.
    # Semantics-preserving by construction; run_pipeline re-verifies the FINAL program against the original.
    for tname in ["dead_branch", "dead_code", "cleanup"]:
        finder = _FINDERS[tname]
        for attempt in range(8):
            tree = set_parents(ast.parse(current))
            done = False
            for kind, fn_name, payload, change in _run_finder(tname, tree, StaticAnalyzer(tree)):
                if (change.title, change.before) in rejected_keys:
                    continue
                try:
                    apply_change(tree, kind, payload, None)
                    new_src = dump_src(tree)
                    compile(new_src, "<opt>", "exec")
                except Exception:
                    continue
                if _same_code(current, new_src):
                    continue
                current = new_src
                change.rule = tname
                change.status = "applied"
                change.message = "final cleanup pass (covered by the end-to-end verification of the final program)"
                changes_out.append(change)
                done = True
                break
            if not done:
                break
    _ph.done("rewrite search")
    _ph.done("final cleanup pass")
    # convergence gate: would any rule still fire on the final output?  (idempotency check)
    remaining = []
    tree = set_parents(ast.parse(current))
    an_final = StaticAnalyzer(tree)
    for phase_name in PHASES:
        for tname in PHASE_ORDER[phase_name]:
            try:
                cands = _run_finder(tname, tree, an_final)
            except Exception:
                continue
            for kind, fn_name, payload, change in cands:
                # same gates as the main loop: gated (rejected/skipped/inconclusive) rules do not count as "would fire"
                if change.kind == "advice" or (change.title, change.before) in rejected_keys:
                    continue
                if any(sk_["rule"] == tname and sk_["function"] == (fn_name or "<module>") for sk_ in skipped):
                    continue
                if gate_candidate(tname, fn_name, tree, an_final, fn_types, change) is not None:
                    continue
                remaining.append(f"{tname}: {change.title}")
    literal = sum(1 for n in ast.walk(tree) if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id in ("max", "min")
                  and len(n.args) == 1 and isinstance(n.args[0], (ast.Tuple, ast.List)) and not n.args[0].elts)
    _LAST_GATE.clear()
    _LAST_GATE.update({"converged": not remaining, "remaining": remaining[:8], "literal_errors": literal})
    _ph.done("convergence check")
    seen = set()
    final = []
    for c in changes_out:
        key = (c.title, c.before, c.status)
        if key in seen:
            continue
        seen.add(key)
        final.append(c)
    seen_skip = {(x["function"], x["rule"], x["reason"]) for x in prescan}
    for x in skipped:
        key = (x["function"], x["rule"], x["reason"])
        if key not in seen_skip:
            prescan.append(x)
            seen_skip.add(key)
    return current, final, notes, prescan


# --------------------------------------------------------------------------
# Pipeline
# --------------------------------------------------------------------------
def _variant_cost(self, fn, node, take_true):
    """Cost of `fn` when the branch `node` is replaced by one of its arms (used for conditional complexity)."""
    try:
        fn2 = ast.parse(ast.unparse(fn)).body[0]
        a, b = list(ast.walk(fn)), list(ast.walk(fn2))
        if len(a) != len(b):
            return None
        idx = next(i for i, x in enumerate(a) if x is node)
        n2 = b[idx]
        if type(n2) is not type(node):
            return None
        mod = ast.Module(body=[fn2], type_ignores=[])
        set_parents(mod)
        if isinstance(n2, ast.IfExp):
            _replace_node(mod, n2, n2.body if take_true else n2.orelse)
        else:
            _splice_stmts(n2, n2.body if take_true else n2.orelse)
        set_parents(mod)
        return StaticAnalyzer(mod).function_cost(fn2.name)
    except Exception:
        return None


def _conditional_costs(self, fn):
    import builtins
    _BUILTIN_NAMES = set(dir(builtins)) | {"None", "True", "False"}   # isinstance(a, (list, tuple, str)) etc.
    """Guarded rewrites keep a fallback branch, so the class has two answers. Report them:
        {'guard': ..., 'guard_true_is_worst': bool, 'worst': O(...), 'otherwise': O(...)}
    The condition shown is the PARAMETER-level one: a local test of the form
    `X is not None` where `X = ... if G else None` displays as `G` (they are equivalent)."""
    params = {a.arg for a in fn.args.args}
    overall = self.function_cost(fn.name)
    out = []

    def free_names(test):
        bound = set()
        for c in ast.walk(test):
            if isinstance(c, ast.comprehension):
                bound |= {t.id for t in ast.walk(c.target) if isinstance(t, ast.Name)}
            if isinstance(c, (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)):
                for g in c.generators:
                    bound |= {t.id for t in ast.walk(g.target) if isinstance(t, ast.Name)}
        calls = {n.func.id for n in ast.walk(test) if isinstance(n, ast.Call) and isinstance(n.func, ast.Name)}
        return {x.id for x in ast.walk(test)
                if isinstance(x, ast.Name) and x.id not in bound and x.id not in calls}

    # locals assigned from an expression over a param (`X = f(a) if G else None`) and loop targets
    # are derived from parameters, so a guard on them is still a condition on the input
    loop_vars = set()

    def collect_loop_targets(node):
        cur = getattr(node, "_parent", None)
        while cur is not None:
            if isinstance(cur, ast.For):
                loop_vars.update(t.id for t in ast.walk(cur.target) if isinstance(t, ast.Name))
            cur = getattr(cur, "_parent", None)

    param_derived = set()
    param_ids = params
    for n in ast.walk(fn):
        if isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name):
            if any(isinstance(x, ast.Name) and x.id in param_ids for x in ast.walk(n.value)):
                param_derived.add(n.targets[0].id)
    # local defined as `X = expr if G else None`  ->  `X is not None` means G
    local_guard = {}
    for n in ast.walk(fn):
        if isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name) \
                and isinstance(n.value, ast.IfExp) and isinstance(n.value.orelse, ast.Constant) \
                and n.value.orelse.value is None:
            local_guard[n.targets[0].id] = ast.unparse(n.value.test)

    def display_guard(test):
        parts = []
        for conj in (test.values if isinstance(test, ast.BoolOp) and isinstance(test.op, ast.And) else [test]):
            if isinstance(conj, ast.Compare) and len(conj.ops) == 1 and isinstance(conj.ops[0], (ast.Is, ast.IsNot)) \
                    and isinstance(conj.left, ast.Name) and isinstance(conj.comparators[0], ast.Constant) \
                    and conj.comparators[0].value is None and conj.left.id in local_guard:
                parts.append(local_guard[conj.left.id])
            else:
                parts.append(ast.unparse(conj))
        return " and ".join(parts)

    for n in ast.walk(fn):
        if len(out) >= 2:
            break
        if not isinstance(n, (ast.If, ast.IfExp)):
            continue
        if not isinstance(n.test, (ast.Compare, ast.BoolOp, ast.UnaryOp, ast.Call)):
            continue        # guards may be a bare call: isinstance(x, (list, tuple)) / all(...)
        collect_loop_targets(n)
        names = free_names(n.test) - loop_vars - _BUILTIN_NAMES
        unknown = {x for x in names if x not in params and x not in param_derived}
        if not names or unknown:
            continue
        ct, cf = self._variant_cost(fn, n, True), self._variant_cost(fn, n, False)
        if ct is None or cf is None or ct.key() == cf.key():
            continue
        worst, other, exp_true = (ct, cf, True) if ct.key() > cf.key() else (cf, ct, False)
        if worst.key() != overall.key():
            continue
        g = display_guard(n.test)
        out.append({"when": g if exp_true else f"not ({g})",
                    "guard": g, "guard_true_is_worst": bool(exp_true),
                    "worst": str(worst), "otherwise": str(other),
                    "rank_worst": worst.rank(), "rank_other": other.rank()})
    return out


StaticAnalyzer._variant_cost = _variant_cost
StaticAnalyzer._conditional_costs = _conditional_costs


def _rank_of(label):
    """numeric rank of a complexity label such as 'O(n²)' / 'O(n · log n)' (higher = slower)"""
    try:
        table = {"O(1)": 0, "O(log n)": 1, "O(√n)": 5, "O(n)": 10, "O(n · log n)": 11, "O(n²)": 20, "O(n³)": 30}
        if label in table:
            return table[label]
        import re as _re
        m = _re.match(r"O\((\d+)\^n\)", label or "")
        return 50 + int(m.group(1)) if m else 10
    except Exception:
        return 10


def consistency_check(static, static2, target, speed, fit_o, fit_p):
    """Cross-check the static complexity claim against what the benchmark actually showed, for ONE function."""
    if not speed:
        return {"status": "n/a", "message": "no measurement to compare against"}
    big = speed[-1]["speedup"] or 0
    ro = static.get("overall_rank", _rank_of(static.get("overall")))
    rp = static2.get("overall_rank", _rank_of(static2.get("overall")))
    f2 = next((f for f in static2["functions"] if f["name"] == target), None) or {}
    cond = f2.get("conditional") or []
    if cond:
        c0 = cond[0]
        return {"status": "conditional",
                "message": (f"worst case stays {f2.get('time')} because a fallback branch is live ({c0.get('when')}); "
                            f"otherwise {c0.get('otherwise')}. The measured {big:.1f}× is for inputs that take the fast path.")}
    if big and big > 5 and rp >= ro:
        return {"status": "static_mismatch",
                "message": (f"measured {big:.1f}× faster while the static class is unchanged ({static.get('overall')} → {static2.get('overall')}); "
                            "a fallback branch keeps the worst case, so the class is right and the speed-up is input-dependent")}
    if big and big < 1.15 and rp < ro:
        return {"status": "static_over_optimistic",
                "message": (f"static class improves {static.get('overall')} → {static2.get('overall')} but the measured speed-up is only {big:.2f}×; "
                            "the static claim is unconfirmed at this input size")}
    return {"status": "agree", "message": "static class and measurement are consistent"}


def _portable_note(change):
    r = (change.ab or {}).get("ratio")
    seen = ("no measurable difference" if r is None or 0.9 <= r <= 1.1 else (f"{r:.2f}× faster" if r > 1 else f"{1 / r:.2f}× slower"))
    return (f"Portable rewrite kept: `{change.title}`. CPython measured {seen} here — CPython special-cases `s = s + x` when the string has a single "
            "reference, which hides the quadratic copying, but that is an implementation detail: ''.join(...) is O(n) on every interpreter. "
            "The speed-up on PyPy was not measured by this tool.")


def _collect_calls(tree):
    calls = collections.defaultdict(list)
    for n in ast.walk(tree):
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Name):
            calls[n.func.id].append(n)
    return calls


def pick_target_function(tree, static, calls):
    fns = {n.name: n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)}
    if not fns:
        return None
    top_called = []
    for s in tree.body:
        if isinstance(s, ast.FunctionDef):
            continue
        for n in ast.walk(s):
            if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id in fns:
                top_called.append(n.func.id)
    ranks = {f["name"]: f["rank"] for f in static["functions"]}
    cands = top_called or list(fns)
    cands = [c for c in cands if fns[c].args.args]
    if not cands:
        return None
    return max(cands, key=lambda c: (ranks.get(c, 0), c in top_called))


def _same_code(a, b):
    try:
        return ast.dump(ast.parse(a)) == ast.dump(ast.parse(b))
    except Exception:
        return a == b


def _run_json(r, times=None):
    ts = times if times else r.times
    return {"ok": r.ok, "error": r.error, "stdout": r.stdout[-4000:],
            "times_ms": [t * 1000 for t in ts],
            "best_ms": min(ts) * 1000 if ts else None,
            "median_ms": _median(ts) * 1000 if ts else None}


def paired_program_times(src_a, src_b, rounds=4, budget=1.5):
    ta, tb = [], []
    start = time.perf_counter()
    for i in range(rounds):
        order = (("a", src_a), ("b", src_b)) if i % 2 == 0 else (("b", src_b), ("a", src_a))
        for tag, s in order:
            res = run_program(s, repeats=1)
            if not res.ok or not res.times:
                return None
            (ta if tag == "a" else tb).append(res.times[0])
        if time.perf_counter() - start > budget:
            break
    return ta, tb


def contest_template(code):
    return ("# Contest scaffold — generic boilerplate, NOT verified or benchmarked by the engine.\n"
            "import sys\n"
            "input = sys.stdin.readline          # keeps the trailing newline; returns '' at EOF\n"
            "sys.setrecursionlimit(10**6)        # raise only if you need deep recursion\n\n" + code.strip() + "\n")


def _program_failure_message(program, stdin):
    msg = (program or {}).get("message", "") or ""
    if "EOFError" in msg and not (stdin or "").strip():
        return "program reads input but the stdin box is empty"
    return msg


def run_pipeline(source, stdin="", hints=""):
    out = {"ok": True}
    t_start = time.perf_counter()
    try:
        tree = set_parents(ast.parse(source))
    except SyntaxError as e:
        return json.dumps({"ok": False, "error": f"SyntaxError: {e.msg} (line {e.lineno})"})
    _phase = _Phases()
    warnings = []          # initialised up-front: phases below append to it as they run
    _progress("parse", "Parsed source into AST")
    _phase.done("parse")

    analyzer = StaticAnalyzer(tree)
    static = analyzer.analyze()
    out["original"] = {"code": source, "static": static}
    _progress("static", f"Static analysis: {static['overall']}", static)
    _phase.done("static analysis + input-shape inference")

    calls = _collect_calls(tree)
    fn_types = {}
    for n in ast.walk(tree):
        if isinstance(n, ast.FunctionDef):
            try:
                fn_types[n.name] = infer_param_types(n, tree, calls)
            except Exception:
                pass
    target = pick_target_function(tree, static, calls)
    out["target_function"] = target
    out["param_types"] = fn_types.get(target) if target else None

    _progress("run", "Executing original program…")
    r = run_program(source, stdin=stdin)
    out["original"]["run"] = _run_json(r)
    _progress("run", f"Original program: {min(r.times)*1000:.3f} ms" if r.times else "Original program failed", out["original"]["run"])
    program_fast = bool(r.ok and r.times and min(r.times) < 1.5)
    if not r.ok and r.error and "EOFError" in r.error and not (stdin or "").strip():
        out["stdin_hint"] = "program reads input but the stdin box is empty"
        warnings.append("program reads input but the stdin box is empty")
    _phase.done("original program run")

    # ---- discovery benchmark of the original (chooses sizes + adversarial input shape)
    orig_ns = r.namespace if r.ok else load_namespace(source)
    static_cx = None
    orig_points, bench_err = [], None
    if target and orig_ns is not None and callable(orig_ns.get(target)):
        fcx = next((f for f in static["functions"] if f["name"] == target), None)
        static_cx = _cx_from_rank(fcx["rank"]) if fcx else None
        _progress("bench", f"Growth benchmark of `{target}` with generated inputs ({', '.join(fn_types[target])})")
        with _quiet():
            try:
                strat = choose_adversarial_strategy(orig_ns.get(target), fn_types[target], exp_like=bool(static_cx and (static_cx.e or static_cx.fact)))
                out["input_strategy"] = strat
                _progress("bench", f"Adversarial input search → list: {strat['list']}, int: {strat['primary']}, scalar arg: {strat['secondary']}")
            except Exception:
                pass
            orig_points, bench_err = growth_benchmark(orig_ns, target, fn_types[target], static_cx, budget=0.5, label="original")
    out["original"]["bench"] = {"points": [{"n": n, "t_ms": t * 1000} for n, t in orig_points],
                                "fit": fit_growth(orig_points), "error": bench_err}
    _phase.done("growth benchmark (original)")

    # ---- optimise
    _progress("optimize", "Searching for optimizations…")
    try:
        new_src, changes, notes, skipped = optimize(source, fn_types, r.stdout, program_fast, hints=hints)
    except Exception as e:  # noqa
        new_src, changes, notes, skipped = source, [], [f"optimizer crashed: {type(e).__name__}: {e}", traceback.format_exc()[-800:]], []
    final_ver = {"functions": [], "ok": True}
    if not _same_code(source, new_src):
        try:
            old_f = {n.name: ast.dump(n) for n in ast.parse(source).body if isinstance(n, ast.FunctionDef)}
            new_f = {n.name: ast.dump(n) for n in ast.parse(new_src).body if isinstance(n, ast.FunctionDef)}
            for fname, tags in fn_types.items():
                if fname in old_f and fname in new_f and old_f[fname] != new_f[fname]:
                    with _quiet():
                        e_cap = _fn_int_cap(analyzer, fname)
                        e_exp = _fn_is_exp(analyzer, fname)
                        rv = differential_test(source, new_src, fname, tags, n_tests=100, int_cap=e_cap, budget=0.9, slow=(0.001 if e_exp else 0.01))
                    final_ver["functions"].append({"name": fname, "inputs": rv["run"], "valid": rv["valid"], "exception_parity": rv["exc"], "ok": rv["ok"], "msg": rv["msg"]})
                    if not rv["ok"]:
                        final_ver["ok"] = False
        except Exception as e:  # noqa
            notes.append(f"end-to-end verification error: {type(e).__name__}: {e}")
        bad_names = {f["name"] for f in final_ver["functions"] if not f["ok"]}
        if bad_names:
            # Revert ONLY the functions whose final form failed.  Every other function keeps its verified rewrites.
            for c in changes:
                if c.status == "applied" and c.fn in bad_names:
                    c.status = "rejected"
                    bad = next(f for f in final_ver["functions"] if f["name"] == c.fn)
                    c.message = f"reverted by the final check (original vs final `{c.fn}`): {bad['msg']}"
            try:
                t_keep = set_parents(ast.parse(new_src))
                t_orig = set_parents(ast.parse(source))
                for nm in bad_names:
                    o_fn = next(n for n in t_orig.body if isinstance(n, ast.FunctionDef) and n.name == nm)
                    k_fn = next(n for n in t_keep.body if isinstance(n, ast.FunctionDef) and n.name == nm)
                    k_fn.body = copy.deepcopy(o_fn.body)
                    k_fn.decorator_list = copy.deepcopy(o_fn.decorator_list)
                new_src = dump_src(t_keep)
                compile(new_src, "<kept>", "exec")
            except Exception:
                # could not restore surgically -> fall back to restoring the whole function set
                new_src = source
    out["final_verification"] = final_ver
    out["gate"] = dict(_LAST_GATE)
    applied = [c for c in changes if c.status == "applied"]
    rejected = [c for c in changes if c.status == "rejected"]
    suggested = [c for c in changes if c.status == "suggested"]
    inconclusive = [c for c in changes if c.status == "inconclusive"]
    out["changes"] = [c.to_json() for c in changes]
    _phase.done("optimise + final end-to-end verification")
    out["optimizer_notes"] = notes
    out["changed"] = bool(applied)
    identical = _same_code(source, new_src)
    out["identical"] = identical
    infos = []
    for c in changes:
        if c.status == "applied" and c.portable and c.portable_note:
            warnings.append(c.portable_note)
    if out["gate"] and not out["gate"].get("converged", True):
        warnings.append("Pipeline did not fully converge — rules would still fire on the output: " + "; ".join(out["gate"]["remaining"][:3]))

    if identical:
        # Nothing to compare: do NOT time the same code twice and report the difference.
        _progress("static", "No rewrite was applied — optimized code is identical to the input; skipping A/B comparison")
        out["optimized"] = {"code": new_src, "static": static, "run": out["original"]["run"], "bench": out["original"]["bench"]}
        out["noise"] = {"control_pct": None, "method": "nothing was timed — the code is unchanged"}
        out["output_status"] = "unchanged"
        out["output_match"] = True
        out["program_measurable"] = False
        out["report"] = [{"function": f["name"], "applied": [], "skipped": [x for x in skipped if x["function"] == f["name"]],
                          "static_before": f.get("time"), "static_after": f.get("time"), "speedup": None, "aa": None,
                          "verdict": "unchanged"} for f in static["functions"]]
        out["skipped"] = skipped
        out["changed_count"] = 0
        out["per_function"] = []
        out["program"] = None
        if program_fast:
            try:
                with _quiet():
                    out["program"] = compare_programs(source, source, stdin, rounds=5)
                out["program"]["shown"] = False
                out["program"]["message"] = "code unchanged — no comparison"
            except Exception:
                out["program"] = None
        warnings.append("No optimizations applicable: the output is byte-for-byte the input program, so no speed-up is claimed."
                        + (" Already optimal with respect to the rule library — no scaffold offered." if not rejected else f" ({len(rejected)} candidate rewrite(s) were tried and reverted.)"))
    else:
        try:
            tree2 = set_parents(ast.parse(new_src))
            static2 = StaticAnalyzer(tree2).analyze()
        except Exception as e:  # noqa
            static2 = static
            notes.append(f"static analysis of optimized code failed: {e}")
        _progress("static", f"Optimized static analysis: {static2['overall']}", static2)
        _progress("run", "Executing optimized program…")
        r2 = run_program(new_src, stdin=stdin)
        orun, nrun = _run_json(r), _run_json(r2)
        pt = paired_program_times(source, new_src) if (r.ok and r2.ok and program_fast) else None
        if pt:
            orun, nrun = _run_json(r, pt[0]), _run_json(r2, pt[1])
        out["original"]["run"] = orun
        out["optimized"] = {"code": new_src, "static": static2, "run": nrun}
        out["output_match"] = bool(r.ok and r2.ok and r.stdout == r2.stdout)
        if not r.ok or not r2.ok:
            out["output_status"] = "error"
        elif not r.stdout.strip() and not r2.stdout.strip():
            out["output_status"] = "no_output"
        elif r.stdout == r2.stdout:
            out["output_status"] = "identical"
        else:
            out["output_status"] = "differs"
        out["program_measurable"] = bool(orun["best_ms"] and nrun["best_ms"] and min(orun["best_ms"], nrun["best_ms"]) >= 0.5)
        if not out["program_measurable"]:
            warnings.append("Whole-program runtime is below ~0.5 ms — dominated by interpreter/timer noise; use the per-size function benchmark instead.")

        # ---- honest per-function measurement (CHANGED functions only) ---------------------
        # One row per changed function.  `a` / `b` are real per-call seconds from the benchmark.
        # There is deliberately no single headline number and no max() across functions.
        # ---- honest per-function measurement (CHANGED functions only) ---------------------
        changed_names = list(dict.fromkeys(f["name"] for f in final_ver["functions"] if f.get("ok")))
        static_by_fn = {}
        try:
            after_res = StaticAnalyzer(set_parents(ast.parse(new_src))).analyze()
            for f in after_res["functions"]:
                static_by_fn.setdefault(f["name"], {})["after"] = f.get("time")
                static_by_fn[f["name"]]["after_fit"] = (f.get("conditional") or [None])[0]
            for f in static["functions"]:
                static_by_fn.setdefault(f["name"], {})["before"] = f.get("time")
        except Exception:
            pass
        sizes_by_fn = {target: [n for n, _ in orig_points]} if target and orig_points else {}
        rows = {}
        try:
            with _quiet():
                rows = bench_changed(source, new_src, changed_names, fn_types, hints, sizes_by_fn, budget=1.5)
        except Exception as e:  # noqa
            notes.append(f"per-function benchmark failed: {type(e).__name__}: {e}")
        changed_set = set(changed_names)
        report, per_function, consistency_by_fn = [], [], {}

        def _static_display(nm):
            """`O(n) when <guard>, else O(n²)` when the rewrite kept a guarded fallback."""
            st = static_by_fn.get(nm, {})
            cond = st.get("after_fit")
            if isinstance(cond, dict) and cond.get("worst") and cond.get("otherwise") and cond["worst"] != cond["otherwise"]:
                guard = cond.get("guard") or cond.get("when")
                disp = guard if not cond.get("guard_true_is_worst") else f"not ({guard})"
                return f"{cond['otherwise']} when {disp}, else {cond['worst']}", cond
            return st.get("after"), cond

        for nm in changed_names:
            row = rows.get(nm) or {}
            applied_titles = [c.title for c in applied if c.fn == nm]          # ONLY this function's rewrites
            sk = [x for x in skipped if x["function"] == nm]
            st = static_by_fn.get(nm, {})
            static_display, cond = _static_display(nm)
            base = {"function": nm, "applied": applied_titles, "skipped": sk,
                    "static_before": st.get("before"), "static_after": static_display}
            if row.get("error") or not row.get("a") or not row.get("b"):
                reason = row.get("error") or "no valid inputs"
                report.append({**base, "ratio": None, "spread": None, "n": None, "aa": None, "verdict": reason})
                continue
            verdict, spread, is_claim, _floor = verdict_for(row)
            pf = {"name": nm, "n": row["n"], "orig_ms": row["a"] * 1000, "opt_ms": row["b"] * 1000,
                  "ratio": row["ratio"], "spread": spread, "aa": row["aa"]["ratio"],
                  "verdict": verdict, "claimed": is_claim, "threshold": _floor}
            per_function.append(pf)
            report.append({**base, "ratio": row["ratio"], "spread": spread, "n": row["n"],
                           "orig_ms": pf["orig_ms"], "opt_ms": pf["opt_ms"], "aa": row["aa"]["ratio"],
                           "verdict": verdict})
            # consistency of the static claim vs what was actually measured, PER FUNCTION
            try:
                fo = {"overall": st.get("before") or "O(?)", "functions": [{"name": nm, "time": st.get("before") or "O(?)"}]}
                worst = (cond or {}).get("worst") or st.get("after") or "O(?)"
                fb = {"overall": worst, "functions": [{"name": nm, "time": worst, "conditional": [cond] if cond else []}]}
                consistency_by_fn[nm] = consistency_check(fo, fb, nm, [{"n": row["n"], "speedup": row["ratio"], "significant": is_claim}], None, None)
            except Exception as e:  # noqa
                consistency_by_fn[nm] = {"status": "n/a", "message": f"consistency check failed: {e}"}

        # item 6: EVERY function in the file appears in the report; unchanged ones say why
        for f in static["functions"]:
            nm = f["name"]
            if nm in changed_set:
                continue
            sk = [x for x in skipped if x["function"] == nm]
            rel = [c for c in changes if c.fn == nm and c.status in ("rejected", "inconclusive")]
            if sk:
                reason = f"unchanged - {sk[0]['reason']}"
            elif rel:
                reason = f"unchanged - {rel[0].status}: {rel[0].message[:110]}"
            elif identical:
                reason = "unchanged - already optimal (no rule matched)" if not rejected else "unchanged - no rewrite survived verification"
            else:
                reason = "unchanged - no rule matched"
            report.append({"function": nm, "applied": [], "skipped": sk,
                           "static_before": f.get("time"), "static_after": f.get("time"),
                           "ratio": None, "spread": None, "n": None, "aa": None, "verdict": reason})
        _phase.done("per-function A/B + A/A benchmark")
        out["report"] = report
        out["per_function"] = per_function
        out["consistency_by_fn"] = consistency_by_fn
        out["skipped"] = skipped
        out["changed_count"] = len(changed_names)
        out["measured_count"] = len(per_function)
        out["function_total"] = len(static["functions"])
        out["skipped_count"] = len(skipped)
        # ---- the ONE noise number: control_pct = max |A/A ratio - 1| over the measured functions ----------
        aa_devs = [abs(r["aa_dev"]) for r in rows.values() if r.get("aa_dev") is not None]
        control_pct = max(aa_devs) if aa_devs else None
        out["noise"] = {"control_pct": control_pct,
                        "method": "A/A control: the original timed against a second freshly compiled copy of itself, "
                                  "same protocol (15 rounds, random order, cache cleared, fresh deepcopy of args per call)"}
        for nm, c in consistency_by_fn.items():
            if isinstance(c, dict) and c.get("status") in ("static_mismatch", "static_over_optimistic"):
                infos.append(f"{nm}: {c['message']}")
        out["program"] = None
        if program_fast:
            try:
                with _quiet():
                    out["program"] = compare_programs(source, new_src, stdin, rounds=5)
            except Exception as e:  # noqa
                out["program"] = {"status": "error", "message": str(e), "shown": False}
        if out["program"] and out["program"].get("status") == "original_failed":
            warnings.append(_program_failure_message(out["program"], stdin))
        _phase.done("program comparison (same stdin)")

    # ---- summary: derived only from what actually ran ------------------------------------------------
    items = [{"title": c.title, "status": c.status, "rule": c.rule, "function": c.fn,
              **(c.verification or {"method": "none", "inputs": 0, "valid": 0, "exception_parity": 0})} for c in changes]
    app_items = [i for i in items if i["status"] == "applied"]
    per_candidate_verified = [c for c in applied if c.verification and c.verification.get("method") not in (None, "none")]
    cleanup_only_applied = [c for c in applied if not (c.verification and c.verification.get("method") not in (None, "none"))]
    out["verification"] = {
        "applied": len(applied), "reverted": len(rejected), "suggested": len(suggested), "inconclusive": len(inconclusive),
        "skipped": len(skipped),
        "per_candidate_verified": len(per_candidate_verified),
        "cleanup_only_applied": len(cleanup_only_applied),
        "normal_runs_min": min((i["valid"] for i in app_items), default=None),
        "normal_runs_total": sum(i["valid"] for i in items),
        "both_raised_total": sum(i["exception_parity"] for i in items),
        "items": items,
    }
    fired = {c.rule for c in applied}
    advised = {c.rule for c in suggested}
    out["rules"] = [dict(rl, fired=rl["id"] in fired, suggested=rl["id"] in advised,
                         skipped=any(s["rule"] == rl["id"] for s in skipped)) for rl in RULES]
    out["verification_policy"] = [
        {"class": "O(n!) — factorial or worse", "cap": "n ≤ 7"},
        {"class": "O(2^n) — exponential", "cap": "n ≤ 10"},
        {"class": "O(n³)", "cap": "n ≤ 50"},
        {"class": "O(n²)", "cap": "n ≤ 200"},
        {"class": "O(n log n) and below", "cap": "no cap"},
    ]
    out["known_gaps"] = KNOWN_GAPS
    out["warnings"] = warnings
    out["infos"] = infos
    out["contest_template"] = None if identical else contest_template(new_src)
    # ---- the trust line: ONE number, ONE key.  benchmark_trustworthy is derived from it, nothing else.
    control_pct = (out.get("noise") or {}).get("control_pct")
    if identical:
        trustworthy = None                      # nothing was timed, so there is nothing to trust or distrust
    elif control_pct is None:
        trustworthy = False                     # changed code but the control could not be measured
    else:
        trustworthy = bool(control_pct <= 0.05)
    per_function_all = out.get("per_function") or []
    if identical:
        out.setdefault("report", [
            {"function": f["name"], "applied": [], "skipped": [x for x in skipped if x["function"] == f["name"]],
             "static_before": f.get("time"), "static_after": f.get("time"), "ratio": None, "spread": None,
             "n": None, "aa": None,
             "verdict": (f"unchanged - {[x for x in skipped if x['function'] == f['name']][0]['reason']}"
                         if [x for x in skipped if x["function"] == f["name"]]
                         else "unchanged - no rule matched")}
            for f in static["functions"]])
        out.setdefault("per_function", [])
        out.setdefault("consistency_by_fn", {})
        out.setdefault("changed_count", 0)
        out.setdefault("measured_count", 0)
        out.setdefault("function_total", len(static["functions"]))
        out.setdefault("skipped", skipped)
        out.setdefault("noise", {"control_pct": None, "method": "nothing was timed"})
    best_row = None
    if per_function_all:
        cands = [r for r in per_function_all if r.get("claimed") and r.get("ratio")]
        if cands:
            best_row = max(cands, key=lambda r: r["ratio"])   # picks the ROW to show; its own real ms are displayed
    out["protocol"] = {
        "functions_changed": out.get("changed_count", 0),
        "functions_skipped": out.get("skipped_count", 0),
        "measured_count": out.get("measured_count", 0),
        "function_total": out.get("function_total", 0),
        "stdin_hint": out.get("stdin_hint"),
        "best_function": best_row,
        "control_pct": control_pct,
        "benchmark_trustworthy": trustworthy,
        "trust_reason": ("no code was changed, so nothing was timed" if identical else
                         "the A/A control could not be measured" if control_pct is None else
                         ("A/A control within 5%" if trustworthy else "A/A control outside 5% — timings unreliable")),
        "normal_runs_min": out["verification"]["normal_runs_min"],
        "normal_runs_total": out["verification"]["normal_runs_total"],
        "both_raised_total": out["verification"]["both_raised_total"],
        "converged": bool(out.get("gate", {}).get("converged", True)),
        "final_verification_ok": out["final_verification"]["ok"],
        "final_verification_functions": [f["name"] for f in out["final_verification"]["functions"]],
        "per_candidate_verified": out["verification"].get("per_candidate_verified", 0),
        "cleanup_only_applied": out["verification"].get("cleanup_only_applied", 0),
        "verification_scope": (
            "per-candidate rewrites are differentially tested before applying; "
            "cleanup-only rewrites have no per-candidate differential test and rely on final end-to-end verification of changed functions"
        ),
        "consistency": {nm: c.get("status") for nm, c in (out.get("consistency_by_fn") or {}).items()},
        "has_run_error": bool(out["optimized"].get("run", {}).get("error") or out["original"]["run"].get("error")),
    }
    out["elapsed_ms"] = (time.perf_counter() - t_start) * 1000
    return json.dumps(out, default=str)
    return json.dumps(out, default=str)


def _cx_from_rank(rank):
    if rank >= 100:
        return Cx(fact=True)
    if rank >= 50:
        return Cx(e=max(2, int(rank - 50)))
    return Cx(rank // 10, int(rank % 10))
