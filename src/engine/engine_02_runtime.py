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

