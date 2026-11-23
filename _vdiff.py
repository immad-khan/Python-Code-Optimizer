def _run_isolated(f, args):
    """call f(*args) with stdout captured; never raises"""
    buf = io.StringIO()
    old = sys.stdout
    sys.stdout = buf
    try:
        return ("ok", f(*args)), buf.getvalue()
    except BaseException as e:  # noqa
        return ("exc", type(e).__name__), buf.getvalue()
    finally:
        sys.stdout = old


def differential_test(orig_code, new_code, fn_name, tags, n_tests=120, int_cap=None, _full=False,
                      budget=4.0, slow=0.01, hints=None, source_tree=None, min_valid=40, stop_at=100):
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
    for i in range(n_tests * 3):
        if st["valid"] >= stop_at or time.perf_counter() - t_start > budget:
            if st["valid"] < stop_at:
                st["budget_hit"] = True
            break
        args = make_small_args(tags, 991 + i * 17, test_idx=i, int_cap=int_cap, hints=hints, shapes=shapes, fn_name=fn_name)
        a1, a2 = copy.deepcopy(args), copy.deepcopy(args)
        g0a, g0b = _globals_snapshot(na), _globals_snapshot(nb)
        t_call = time.perf_counter()
        (ka, ra), outa = _run_isolated(fa, a1)
        dt = time.perf_counter() - t_call
        ints = [v for v in args if type(v) is int]
        if dt > slow and ints:
            cap = max(1, max(ints) - 1)
            int_cap = cap if int_cap is None else min(int_cap, cap)
            st["capped"] = True
        for f in (fa, fb):
            if hasattr(f, "cache_clear"):
                f.cache_clear()
        (kb, rb), outb = _run_isolated(fb, a2)
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
