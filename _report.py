        # ---- honest per-function measurement (CHANGED functions only) ---------------------
        # One row per changed function.  `a` / `b` are real per-call seconds from the benchmark.
        # There is deliberately no single headline number and no max() across functions.
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
                rows = bench_changed(source, new_src, changed_names, fn_types, hints, sizes_by_fn)
        except Exception as e:  # noqa
            notes.append(f"per-function benchmark failed: {type(e).__name__}: {e}")
        report, per_function, consistency_by_fn = [], [], {}
        for nm in changed_names:
            row = rows.get(nm)
            applied_titles = [c.title for c in applied if c.fn == nm]          # ONLY this function's rewrites
            sk = [x for x in skipped if x["function"] == nm]
            st = static_by_fn.get(nm, {})
            base = {"function": nm, "applied": applied_titles, "skipped": sk,
                    "static_before": st.get("before"), "static_after": st.get("after")}
            if not row or not row.get("a") or not row.get("b"):
                report.append({**base, "ratio": None, "spread": None, "n": None, "aa": None,
                               "verdict": "changed; no measurement available"})
                continue
            verdict, spread, is_claim = verdict_for(row)
            pf = {"name": nm, "n": row["n"], "orig_ms": row["a"] * 1000, "opt_ms": row["b"] * 1000,
                  "ratio": row["ratio"], "spread": spread, "aa": row["aa"]["ratio"],
                  "verdict": verdict, "claimed": is_claim}
            per_function.append(pf)
            report.append({**base, "ratio": row["ratio"], "spread": spread, "n": row["n"],
                           "orig_ms": pf["orig_ms"], "opt_ms": pf["opt_ms"], "aa": row["aa"]["ratio"],
                           "verdict": verdict})
            # consistency of the static claim vs what was actually measured, PER FUNCTION
            try:
                fo = {"overall": st.get("before") or "O(?)", "functions": [{"name": nm, "time": st.get("before") or "O(?)"}]}
                fb = {"overall": st.get("after") or "O(?)", "functions": [{"name": nm, "time": st.get("after") or "O(?)",
                                                                       "conditional": [st["after_fit"]] if st.get("after_fit") else []}]}
                consistency_by_fn[nm] = consistency_check(fo, fb, nm, [{"n": row["n"], "speedup": row["ratio"], "significant": is_claim}], None, None)
            except Exception as e:  # noqa
                consistency_by_fn[nm] = {"status": "n/a", "message": f"consistency check failed: {e}"}
        out["report"] = report
        out["per_function"] = per_function
        out["consistency_by_fn"] = consistency_by_fn
        out["skipped"] = skipped
        out["changed_count"] = len(changed_names)
        out["skipped_count"] = len(skipped)
        # ---- the ONE noise number: control_pct = max |A/A ratio - 1| over the measured functions ----------
        aa_devs = [abs(r["aa_dev"]) for r in rows.values() if r.get("aa_dev") is not None]
        control_pct = max(aa_devs) if aa_devs else None
        out["noise"] = {"control_pct": control_pct,
                        "method": "A/A control: the original timed against a second freshly compiled copy of itself, "
                                  "same protocol (15 rounds, random order, cache cleared, fresh deepcopy of args per call)"}
        # functions whose rewrites were measured "faster" AND whose static class did not improve are flagged,
        # because a kept fallback branch keeps the worst-case class the same.
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
            warnings.append(out["program"]["message"])

