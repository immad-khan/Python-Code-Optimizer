"""Dev probe: run every corpus program, print one line each.  Not part of `npm test`."""
import sys, os, json, io, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "src", "engine"))
import engine
import corpus


def run(code, **kw):
    old = sys.stdout
    sys.stdout = io.StringIO()
    try:
        return json.loads(engine.run_pipeline(code, **kw))
    finally:
        sys.stdout = old


names = sys.argv[1:] or list(corpus.C)
T = 0
for k in names:
    t0 = time.time()
    try:
        r = run(corpus.C[k])
    except Exception as e:  # noqa
        print("%-15s CRASH %s: %s" % (k, type(e).__name__, str(e)[:100]))
        continue
    dt = time.time() - t0
    T += dt
    p = r.get("protocol", {})
    rows = [(x["function"], x.get("static_before"), x.get("static_after"), x.get("verdict")) for x in r.get("report", [])]
    pf = [(x["name"], round(x["ratio"], 1), x["n"]) for x in r.get("per_function", [])]
    fv = [(f["name"], f.get("valid"), f.get("exception_parity"), f.get("ok")) for f in r.get("final_verification", {}).get("functions", [])]
    same = r["original"]["run"]["stdout"] == r["optimized"]["run"]["stdout"]
    print("%-15s %5.1fs changed=%s trust=%s rows=%s perf=%s final=%s same=%s" % (
        k, dt, p.get("functions_changed"), p.get("benchmark_trustworthy"), rows, pf, fv, same))
print("TOTAL %.1fs" % T)
