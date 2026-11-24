
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


