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
