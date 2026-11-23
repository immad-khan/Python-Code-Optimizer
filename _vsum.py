    # ---- summary: derived only from what actually ran ------------------------------------------------
    items = [{"title": c.title, "status": c.status, "rule": c.rule, "function": c.fn,
              **(c.verification or {"method": "none", "inputs": 0, "valid": 0, "exception_parity": 0})} for c in changes]
    app_items = [i for i in items if i["status"] == "applied"]
    out["verification"] = {
        "applied": len(applied), "reverted": len(rejected), "suggested": len(suggested), "inconclusive": len(inconclusive),
        "skipped": len(skipped),
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
    best_row = None
    if per_function_all:
        cands = [r for r in per_function_all if r.get("claimed") and r.get("ratio")]
        if cands:
            best_row = max(cands, key=lambda r: r["ratio"])   # picks the ROW to show; its own real ms are displayed
    out["protocol"] = {
        "functions_changed": out.get("changed_count", 0),
        "functions_skipped": out.get("skipped_count", 0),
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
        "consistency": {nm: c.get("status") for nm, c in (out.get("consistency_by_fn") or {}).items()},
        "has_run_error": bool(out["optimized"].get("run", {}).get("error") or out["original"]["run"].get("error")),
    }
    out["elapsed_ms"] = (time.perf_counter() - t_start) * 1000
    return json.dumps(out, default=str)
