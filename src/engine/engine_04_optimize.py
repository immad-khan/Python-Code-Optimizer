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


