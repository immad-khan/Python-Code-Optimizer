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


