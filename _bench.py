def _clear_caches(ns):
    """clear lru_cache on the benchmarked function and on every cached callable in its namespace"""
    for v in list(ns.values()):
        if hasattr(v, "cache_clear"):
            try:
                v.cache_clear()
            except Exception:
                pass


def _timed_round(f, ns, argsets, min_sample=0.005, max_reps=4000):
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


def bench_pair(fa, fb, argsets, rounds=15, warm=3, min_sample=0.005, ns_a=None, ns_b=None):
    """15 rounds, random A/B order each round, 3 discarded warm-ups, median of per-round ratios + MAD.
    Caches are cleared and arguments re-copied for every timed call, on both sides."""
    for _ in range(warm):
        fa(*copy.deepcopy(argsets[0]))
        fb(*copy.deepcopy(argsets[0]))
    _clear_caches(ns_a or {})
    _clear_caches(ns_b or {})
    ta, tb = [], []
    for _ in range(rounds):
        order = [("a", fa, ns_a), ("b", fb, ns_b)]
        random.shuffle(order)
        for tag, f, ns in order:
            t = _timed_round(f, ns or {}, argsets, min_sample)
            (ta if tag == "a" else tb).append(t)
    ratios = [a / b for a, b in zip(ta, tb) if b]
    ratio = _median(ratios) if ratios else None
    spread = (_mad(ratios) / ratio) if ratio else 0.0
    return {"a": _median(ta), "b": _median(tb), "ratio": ratio, "spread": spread,
            "a_spread": (_mad(ta) / _median(ta)) if ta else 0, "b_spread": (_mad(tb) / _median(tb)) if tb else 0,
            "rounds": rounds}


def bench_changed(orig_src, new_src, changed, fn_types, hints, sizes_by_fn, aa_factor=0.03, budget=8.0):
    """One honest measurement per CHANGED function.  `a`/`b` are real per-call seconds.
    The A/A control times the original against a second, freshly compiled copy of itself."""
    rows = {}
    if not changed:
        return rows
    na = load_namespace(orig_src, "__bench_a__")
    nb = load_namespace(new_src, "__bench_b__")
    naa = load_namespace(orig_src, "__bench_aa__")
    if na is None or nb is None or naa is None:
        return rows
    t_all = time.perf_counter()
    gc.disable()
    try:
        for name in changed:
            if time.perf_counter() - t_all > budget:
                break
            fa, fb, fa2 = na.get(name), nb.get(name), naa.get(name)
            if not (callable(fa) and callable(fb) and callable(fa2)):
                continue
            tags = probe_signature_prioritized(fa, fn_types.get(name, []))
            sizes = sorted({int(x) for x in (sizes_by_fn.get(name) or [64, 256]) if 0 < int(x) <= 4096}) or [64]
            size = None
            for cand in sizes:
                try:
                    with_deadline(fa, 0.75)(*copy.deepcopy(make_args(tags, cand, 4242)))
                except (Exception, _Deadline):
                    continue
                size = cand
                if cand >= 128:
                    break
            if size is None:
                size = 64
            try:
                argsets = [make_args(tags, size, 1000 + size + j) for j in range(4)]
                row = bench_pair(fa, fb, argsets, rounds=15, ns_a=na, ns_b=nb)
                aa = bench_pair(fa, fa2, argsets, rounds=15, ns_a=na, ns_b=naa)
                rows[name] = {"n": size, **row, "aa": aa, "aa_dev": abs((aa.get("ratio") or 1.0) - 1.0)}
            except (Exception, _Deadline):
                continue
    finally:
        gc.enable()
    return rows


def verdict_for(row):
    """A speed-up is claimed only if ratio >= 1.15 AND ratio > 1 + 3 * spread, where spread is the
    larger of the run-to-run MAD and the A/A control deviation (floor 3%)."""
    ratio = row.get("ratio")
    aa_dev = row.get("aa_dev", 0.0)
    spread = max(row.get("spread", 0.0), aa_dev, 0.03)
    if not ratio:
        return "no measurable change", spread, False
    if ratio >= 1.15 and ratio > 1 + 3 * spread:
        return f"faster at n={row['n']}", spread, True
    if ratio <= 1 / 1.15 and ratio < 1 / (1 + 3 * spread):
        return f"slower at n={row['n']}", spread, False
    return "no measurable change", spread, False
