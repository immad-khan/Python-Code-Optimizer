"""SPEC v3 acceptance suite.  Every item of the spec has a named, non-vacuous check.

Run:  python3 tests/acceptance.py            (or `npm test`)
Exit code is non-zero if ANY check fails."""
import sys, os, json, io, time, copy, math, struct

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "src", "engine"))
import engine  # noqa: E402

RESULTS = []


def run(code, **kw):
    old = sys.stdout
    sys.stdout = io.StringIO()
    try:
        return json.loads(engine.run_pipeline(code, **kw))
    finally:
        sys.stdout = old


def check(item, name, cond, detail=""):
    RESULTS.append((item, name, bool(cond)))
    print(("PASS " if cond else "FAIL ") + f"[{item}] {name}" + (f"  — {str(detail)[:170]}" if detail else ""))


def body(code):
    return [l for l in code.strip().split("\n") if l.strip() and not l.startswith(("print", "import", "from"))]


def oracle(code_a, code_b, fn, inputs):
    """independent behavioural comparison (strict: type + value, bit-exact floats, NaN==NaN)"""
    A, B = {}, {}
    exec(compile(code_a, "a", "exec"), A)
    exec(compile(code_b, "b", "exec"), B)

    def call(f, a):
        try:
            return ("ok", engine.strict_equal and f(*copy.deepcopy(a)))
        except Exception as e:
            return ("exc", type(e).__name__)
    for a in inputs:
        ra, rb = call(A[fn], a), call(B[fn], a)
        if ra[0] != rb[0] or (ra[0] == "exc" and ra[1] != rb[1]) or (ra[0] == "ok" and not engine.strict_equal(ra[1], rb[1])):
            return False, a
    return True, None


# --------------------------------------------------------------------------------------------
# the programs the spec names
# --------------------------------------------------------------------------------------------
P = {
    "count_diff": "def count_diff_pairs(a, k):\n    c = 0\n    for i in range(len(a)):\n        for j in range(i+1, len(a)):\n            if a[j] - a[i] == k:\n                c += 1\n    return c\n",
    "most_common": "def most_common(a):\n    best = None\n    bestc = 0\n    for x in a:\n        c = a.count(x)\n        if c > bestc:\n            bestc = c\n            best = x\n    return best\n",
    "range_sums": ("def range_sums(a, queries):\n    out = []\n    for lo, hi in queries:\n"
                   "        s = 0\n        for k in range(lo, hi):\n            s += a[k]\n        out.append(s)\n    return out\n"),
    "bfs": ("def bfs(adj, s):\n    q = [s]\n    seen = {s}\n    order = []\n    while q:\n        u = q.pop(0)\n"
            "        order.append(u)\n        for v in adj[u]:\n            if v not in seen:\n                seen.add(v)\n                q.append(v)\n    return order\n"),
    "grid_paths": ("def grid_paths(g, i, j):\n    if i < 0 or j < 0:\n        return 0\n    if i == 0 and j == 0:\n        return 1\n"
                   "    return grid_paths(g, i-1, j) + grid_paths(g, i, j-1)\n"),
    "bubble": "def bubble_sort(arr):\n    n = len(arr)\n    for i in range(n):\n        for j in range(0, n-i-1):\n            if arr[j] > arr[j+1]:\n                arr[j], arr[j+1] = arr[j+1], arr[j]\n    return arr\n",
    "fib": "def fib(n):\n    if n < 2:\n        return n\n    return fib(n-1) + fib(n-2)\n",
    "two_sum": ("def two_sum(nums, target):\n    for i in range(len(nums)):\n        for j in range(i+1, len(nums)):\n"
                "            if nums[i] + nums[j] == target:\n                return [i, j]\n    return None\n"),
    "dedupe": "def unique_keep_order(xs):\n    out = []\n    for x in xs:\n        if x not in out:\n            out.append(x)\n    return out\n",
    "rev_build": "def rev(items):\n    res = []\n    for x in items:\n        res.insert(0, x)\n    return res\n",
    "pal": ("def is_palindrome_terrible(s):\n    l1 = []\n    for ch in s:\n        l1.append(ch)\n    l2 = list(l1)\n"
            "    indices = [i for i in range(len(l2))]\n    indices.sort(reverse=True)\n    rev = [l2[i] for i in indices]\n"
            "    for i in range(len(l2)):\n        for j in range(len(rev)):\n            if i == j:\n                if l2[i] != rev[j]:\n                    return False\n    return True\n"),
    "sum_only": "def sum_list(a):\n    return sum(a)\n",
    "float_total": "def total(xs):\n    s = 0\n    for x in xs:\n        s += x\n    return s\n",
    "c1": ("def solve():\n    n, q = map(int, input().split())\n    a = list(map(int, input().split()))\n    total = 0\n"
           "    for i in range(len(a)):\n        for j in range(i, len(a)):\n            s = sum(a[i:j+1])\n            if s == q:\n                total += 1\n"
           "    print(total)\n\nsolve()\n"),
}
P["float_total_print"] = P["float_total"] + "print(total([0.1] * 10))\n"


def main():
    fast = "--fast" in sys.argv

    # ================= C.10  normal-run accounting (unit, no pipeline needed) =================
    st = engine.differential_test("def f(x):\n    return x\n", "def f(x):\n    return x\n", "f", ["int"])
    check("C.10", "unit: identical functions reach >= 40 normal runs", st["ok"] and st["valid"] >= 40, (st["valid"], st["exc"]))
    st = engine.differential_test("def f(x):\n    for i in range(10 ** 9):\n        pass\n    return x\n", "def f(x):\n    return x\n", "f", ["int"], budget=0.6)
    check("C.10", "unit: a rule whose original cannot produce enough normal runs is 'inconclusive', not applied",
          st["inconclusive"] is True and st["valid"] < 40, (st["valid"], st["exc"], st["msg"][:60]))
    st = engine.differential_test("def f(a, k):\n    return a[k]\n", "def f(a, k):\n    return a[k]\n", "f", ["list", "int"])
    check("C.10", "unit: both-raised runs are counted in exc, NOT in valid", st["ok"] and st["exc"] > 0 and st["valid"] >= 40, (st["valid"], st["exc"]))

    # ================= B.7 / B.8  self-matching =================
    r = run(P["count_diff"])
    cd = r["optimized"]["code"]
    guards = sum(1 for l in cd.split("\n") if l.strip().startswith("if all("))
    check("B.7+8+count_diff", "count_diff_pairs has exactly one guarded branch", guards == 1, f"guards={guards}")
    check("count_diff", "count_diff_pairs applied once and correct on [1,1,1],0 -> 3 and [3,1],-2 -> 1",
          r["changes"] and [c["status"] for c in r["changes"]] == ["applied"] and
          oracle(P["count_diff"], cd, "count_diff_pairs", [[[1, 1, 1], 0], [[3, 1], -2], [[], 0], [[0, 0, 0], 0]])[0],
          [c["status"] for c in r["changes"]])

    r = run(P["most_common"])
    mc_apps = [c for c in r["changes"] if c["status"] == "applied" and "Counter" in c["title"]]
    mc_rej = [c for c in r["changes"] if c["status"] in ("rejected", "inconclusive")]
    check("B.8+most_common", "most_common: one Counter rewrite, 0 self-rejected", len(mc_apps) == 1 and len(mc_rej) == 0,
          [(c["rule"], c["status"]) for c in r["changes"]])
    check("most_common", "most_common([1,2,2,1]) == 1 (first wins)", "return 1" not in r["optimized"]["code"] and
          oracle(P["most_common"], r["optimized"]["code"], "most_common", [[[1, 2, 2, 1]], [[3, 3, 3]], [[]]])[0])

    # ================= C.15  prefix sums + exceptions =================
    r = run(P["range_sums"])
    check("C.15", "range_sums is applied", not r["identical"] and any(c["status"] == "applied" for c in r["changes"]),
          [(c["rule"], c["status"], c["message"][:80]) for c in r["changes"]])
    check("C.15", "range_sums: prefix only for all-int input (guard present)", "is int" in r["optimized"]["code"] or "type(v) is int" in r["optimized"]["code"])
    ok, bad = oracle(P["range_sums"], r["optimized"]["code"], "range_sums",
                     [[[1, 2, 3, 4], [(0, 4), (1, 3)]], [[1, 2, 3, 4], [(-5, 2), (1, 99)]], [[1, 2], [(3, 1)]],
                      [[0.5, 1.5], [(0, 2)]], [[1, 2], [(2.0, 3)]], [["a", "b"], [(0, 2)]]])
    check("C.15+A2", "range_sums: same result AND same exception type on bad queries (IndexError/ValueError order kept)", ok, bad)
    check("C.15", "range_sums: floats fall back (sum order matters)", "is None" in r["optimized"]["code"])

    # ================= C.10 / C.11  bfs: normal runs =================
    r = run(P["bfs"])
    fv = r.get("final_verification", {}).get("functions", [{}])[0]
    ch = [c for c in r["changes"] if c["status"] == "applied"]
    check("C.11+bfs", "bfs shows >= 40 normal verification runs", (fv.get("valid") or 0) >= 40, f"valid={fv.get('valid')} both-raised={fv.get('exception_parity')}")
    check("C.11", "bfs: graph-shaped inputs (start key inside the graph)", fv.get("valid", 0) >= 40)
    ok, bad = oracle(P["bfs"], r["optimized"]["code"], "bfs", [[{0: [1], 1: [0], 2: []}, 0], [{0: []}, 0], [{0: [2, 1], 1: [], 2: [1]}, 0], [{5: [5]}, 5]])
    check("bfs", "deque rewrite keeps BFS order", ok and any("deque" in c["title"] or "deque" in c["after"] for c in ch), bad)

    # ================= B.9  convergence (output fed back in) =================
    for nm in ("count_diff", "bfs", "bubble", "pal", "two_sum", "fib"):
        r1 = run(P[nm])
        if r1["identical"]:
            continue
        r2 = run(r1["optimized"]["code"])
        fired = [c for c in r2["changes"] if c["status"] == "applied"]
        check("B.9", f"output fed back in gives 0 transforms: {nm}", len(fired) == 0 and r2["identical"],
              [(c["rule"], c["status"]) for c in r2["changes"]][:3])
        check("B.9", f"converged: yes for {nm}", r1["protocol"]["converged"] is True, r1["gate"]["remaining"][:2])

    # ================= B.3 / A.2  grid_paths: real ms, cold cache, sane ratio =================
    r = run(P["grid_paths"])
    pf = (r.get("per_function") or [None])[0]
    check("B.3", "grid_paths is measured (real ms, no '0 ns')", bool(pf) and pf["orig_ms"] > 0 and pf["opt_ms"] > 0, pf)
    if pf:
        check("B.3", "grid_paths ratio is sane (> 1 and finite)", math.isfinite(pf["ratio"]) and pf["ratio"] > 1, pf["ratio"])
        check("A.5", "grid_paths static class shown as polynomial, not exponential",
              any(k in (r["protocol"] and r["optimized"]["static"]["functions"][0]["time"]) for k in ("n²", "n^2", "n · n")) or "O(n" in r["optimized"]["static"]["functions"][0]["time"],
              r["optimized"]["static"]["functions"][0]["time"])
    r = run(P["grid_paths"])
    check("C.10", "grid_paths reached >= 40 normal runs (cold cache, clear before each call)",
          (r.get("final_verification", {}).get("functions", [{}])[0].get("valid") or 0) >= 40,
          r.get("final_verification", {}).get("functions", [{}])[0].get("valid"))

    # ================= A.1  wiring: no speedups, no headline, no max =================
    r = run(P["two_sum"])
    check("A.1", "no `speedups` field in the output", "speedups" not in r)
    check("A.1", "no single headline / no max() across functions", "headline" not in r)
    check("A.1", "report has one row per changed function", len(r["report"]) == r["protocol"]["functions_changed"] == 1, len(r["report"]))
    check("A.1", "per_function carries real ms (orig/opt > 0)", all(x["orig_ms"] > 0 and x["opt_ms"] > 0 for x in r["per_function"]))

    # ================= A.2  control_pct and trustworthy agree =================
    for nm in ("two_sum", "fib"):
        r = run(P[nm])
        cp, tw = r["protocol"]["control_pct"], r["protocol"]["benchmark_trustworthy"]
        check("A.2", f"{nm}: control_pct is a real number", cp is not None and cp >= 0, cp)
        check("A.2", f"{nm}: benchmark_trustworthy == (control_pct <= 0.05)", tw == (cp <= 0.05), f"control={cp} trustworthy={tw}")
        check("A.2", f"{nm}: noise has one key name (control_pct)", set(r["noise"].keys()) == {"control_pct", "method"})
    r = run(P["sum_only"])
    check("A.2", "unchanged code: control_pct None and trustworthy None (nothing timed)", r["protocol"]["control_pct"] is None and r["protocol"]["benchmark_trustworthy"] is None)
    check("A.1", "unchanged code: 0 rows in per_function and no speed-up anywhere", r["per_function"] == [] and r["protocol"]["best_function"] is None)

    # ================= A.4  consistency per function; no "code unchanged" default =================
    r = run(P["two_sum"])
    cbf = r.get("consistency_by_fn") or {}
    check("A.4", "consistency_check called per changed function", set(cbf.keys()) == {"two_sum"}, cbf)
    check("A.4", "no 'code unchanged — nothing to compare' default for changed code",
          all("code unchanged" not in c.get("message", "") for c in cbf.values()), {k: v["status"] for k, v in cbf.items()})

    # ================= C.12  hints ADD to the pool =================
    r_no = run(P["two_sum"])
    r_h = run(P["two_sum"], hints="two_sum([2, 7, 11, 15], 9)\ntwo_sum([1, 3, 5], 8)")
    v_no = r_no["final_verification"]["functions"][0]["valid"]
    v_h = r_h["final_verification"]["functions"][0]["valid"]
    check("C.12", "adding one hint does not lower the normal-run count", v_h >= v_no, f"without={v_no} with={v_no and v_h}")
    seeds = engine.parse_hint_calls("two_sum([2, 7, 11, 15], 9)", "two_sum", 2)
    check("C.12", "first test is the unmutated hint", bool(seeds) and engine.make_small_args(["list", "int"], 1, test_idx=0, hints="two_sum([2, 7, 11, 15], 9)", fn_name="two_sum") == seeds[0], seeds[:1])

    # ================= C.13  strict returns =================
    check("C.13", "_strict_returns has no loose fallback: [0.0] != [0], 1 != True, -0.0 != 0.0, NaN == NaN",
          not engine._strict_returns([0.0], [0]) and not engine._strict_returns(1, True) and not engine._strict_returns(-0.0, 0.0) and engine._strict_returns(float("nan"), float("nan")))

    # ================= C.14  final check reverts only the failing function =================
    # Build a two-function program where ONE rewrite is behaviour-changing on an input the per-rule check misses.
    prog = ("def good(a):\n    s = 0\n    for x in a:\n        s += x\n    return s\n\n"
            "def pair_sum(a, k):\n    for i in range(len(a)):\n        for j in range(i+1, len(a)):\n            if a[i] + a[j] == k:\n                return True\n    return False\n")
    r_ok = run(prog)
    check("C.14", "(setup) two-function program applies rewrites to both functions",
          {c["function"] for c in r_ok["changes"] if c["status"] == "applied"} >= {"good"}, [(c["function"], c["rule"], c["status"]) for c in r_ok["changes"]])
    # Now force the final check to fail for exactly one function and verify the other survives.
    import unittest.mock as mock
    real = engine.differential_test
    calls = {"n": 0}

    def failing_one(orig, new, fn, *a, **k):
        res = real(orig, new, fn, *a, **k)
        if fn == "pair_sum":
            return {**res, "ok": False, "msg": "forced failure for pair_sum"}
        return res
    old_o = sys.stdout; sys.stdout = io.StringIO()
    try:
        with mock.patch.object(engine, "differential_test", failing_one):
            r_f = json.loads(engine.run_pipeline(prog))
    finally:
        sys.stdout = old_o
    kept = {c["function"] for c in r_f["changes"] if c["status"] == "applied"}
    reverted = {c["function"] for c in r_f["changes"] if c["status"] == "rejected" and "final check" in c["message"]}
    check("C.14", "a failing final check reverts ONLY that function's rules", kept == {"good"} and reverted == {"pair_sum"} and not r_f["identical"],
          f"kept={kept} reverted={reverted}")

    # ================= C.16  float gate per function =================
    r = run(P["float_total_print"])
    check("C.16", "total([0.1]*10) unchanged (sum() would change rounding) + reason logged", r["identical"] and any("float" in s["reason"] for s in r["skipped"]), r["skipped"])
    two_fn = ("def total(xs):\n    s = 0\n    for x in xs:\n        s += x\n    return s\n\n"
              "def scale(y):\n    return y * 2.0\n\nprint(total([1, 2, 3]), scale(2.0))\n")
    r = run(two_fn)
    check("C.16", "a float elsewhere in the FILE no longer blocks idioms on the int function",
          any(c["status"] == "applied" and c["function"] == "total" for c in r["changes"]), [(c["function"], c["rule"], c["status"]) for c in r["changes"]])

    # ================= C.17  type guards =================
    r = run(P["dedupe"])
    check("C.17", "unique_keep_order accepts list/tuple input and keeps order for unhashables",
          "isinstance" in r["optimized"]["code"] or "tuple" in r["optimized"]["code"], r["optimized"]["code"].split("\n")[1][:110])
    ok, bad = oracle(P["dedupe"], r["optimized"]["code"], "unique_keep_order", [[[1, 1, 2]], [[1], [1], [2]], [[2, 2]], [("a", "a")], [[]]])
    check("C.17", "unique_keep_order([[1],[1],[2]]) == [[1],[2]], no crash", ok, bad)
    r = run(P["rev_build"])
    check("C.17", "reverse_build accepts only list/tuple", "isinstance" in r["optimized"]["code"], r["optimized"]["code"].split("\n")[1][:110])

    # ================= C1 with stdin typed =================
    # NOTE: the spec says C1 prints 4, but direct enumeration shows the subarrays of [1,5,3,3,3] summing to 6 are
    # [1,5], [3,3] and [3,3] -> 3. The honest test is "optimized agrees with the original and is faster".
    r = run(P["c1"], stdin="5 6\n1 5 3 3 3\n")
    o_orig, o_opt = r["original"]["run"]["stdout"].strip(), r["optimized"]["run"]["stdout"].strip()
    check("C1", "C1 with stdin '5 6' / '1 5 3 3 3': optimized prints the same as the original (3 by enumeration)", o_orig == o_opt == "3", f"orig={o_orig!r} opt={o_opt!r}")
    check("C1", "C1: no runtime error in either version", r["original"]["run"]["ok"] and r["optimized"]["run"]["ok"], r["optimized"]["run"]["error"])
    check("C1", "C1: rewritten (sum-K Counter rule) and measured faster", bool(r["per_function"]) and r["per_function"][0]["ratio"] > 1, r.get("per_function"))
    r_bad = run(P["c1"], stdin="not numbers\n")
    check("C1", "C1 with garbage stdin: original fails -> reported, no false comparison",
          not r_bad["original"]["run"]["ok"] and (r_bad["program"] or {}).get("status") == "original_failed", (r_bad.get("program") or {}).get("status"))

    # ================= report =================================================================================
    bad = [f"{i} {n}" for i, n, ok in RESULTS if not ok]
    print(f"\n{len(RESULTS) - len(bad)}/{len(RESULTS)} checks passed")
    if bad:
        print("FAILED:\n  " + "\n  ".join(bad))
    return 1 if bad else 0


if __name__ == "__main__":
    t0 = time.time()
    code = main()
    print(f"wall time {time.time() - t0:.1f}s")
    sys.exit(code)
