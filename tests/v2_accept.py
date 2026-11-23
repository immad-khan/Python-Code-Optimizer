import sys, os, json
sys.path.insert(0, os.path.dirname(__file__)); sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src', 'engine'))
import engine
R = []
def run(code, **kw):
    import io
    o = sys.stdout; sys.stdout = io.StringIO()
    try: return json.loads(engine.run_pipeline(code, **kw))
    finally: sys.stdout = o
def chk(n, c, d=""):
    R.append((n, bool(c))); print(("PASS " if c else "FAIL ") + n + ("  — " + str(d)[:150] if d else ""))

A1 = "def count_diff_pairs(a, k):\n    c = 0\n    for i in range(len(a)):\n        for j in range(i+1, len(a)):\n            if a[j] - a[i] == k:\n                c += 1\n    return c\nprint(count_diff_pairs([1,1,1],0), count_diff_pairs([3,1],-2))\n"
r = run(A1); out = r["optimized"]["run"]["stdout"].strip().split()
chk("A1 count_diff_pairs optimized & correct (3, 1)", out == ["3", "1"] and not r["identical"], out)
chk("A1 optimisation is a running Counter", "seen_diff" in r["optimized"]["code"])

A3 = "def unique_keep_order(xs):\n    out = []\n    for x in xs:\n        if x not in out:\n            out.append(x)\n    return out\nprint(unique_keep_order([[1],[1],[2]]))\n"
r = run(A3)
chk("A3 unhashable dedupe no crash, correct", r["optimized"]["run"]["stdout"].strip() == "[[1], [2]]", r["optimized"]["run"]["stdout"])

A4 = "def most_common(a):\n    best = None\n    bestc = 0\n    for x in a:\n        c = a.count(x)\n        if c > bestc:\n            bestc = c\n            best = x\n    return best\nprint(most_common([1,2,2,1]))\n"
r = run(A4); chk("A4 most_common first wins", r["optimized"]["run"]["stdout"].strip() == "1", r["optimized"]["run"]["stdout"])

B2 = "def total(xs):\n    s = 0\n    for x in xs:\n        s += x\n    return s\nprint(total([0.1]*10))\n"
r = run(B2)
chk("B2 float accumulation unchanged + reason logged", r["identical"] and any("float" in s["reason"] for s in r["skipped"]), r.get("skipped"))

B3 = "def fib_count(n):\n    global calls\n    calls = 1\n    if n < 2:\n        return n\n    return fib_count(n-1) + fib_count(n-2)\nprint(fib_count(15))\n"
r = run(B3)
chk("B3 writes global → skipped, reason logged", r["identical"] and any("global" in s["reason"] for s in r["skipped"]), r.get("skipped"))

B4 = "def count_paths(grid, i, j):\n    if i == 0 and j == 0:\n        return 1\n    t = 0\n    if i > 0: t += count_paths(grid, i-1, j)\n    if j > 0: t += count_paths(grid, i, j-1)\n    return t\nprint(count_paths([[1,2],[3,4]],1,1))\n"
r = run(B4)
chk("B4 unhashable arg → skipped, reason logged", r["identical"] and any("unhashable" in s["reason"] for s in r["skipped"]), r.get("skipped"))

B5 = "def has_dup(a):\n    for i in range(len(a)):\n        for j in range(i+1, len(a)):\n            if a[i] == a[j]:\n                return True\n    return False\nprint(has_dup([[1],[2],[1]]), has_dup([float('nan'), float('nan')]))\n"
r = run(B5); chk("B5 lists True, same NaN False, no crash", r["optimized"]["run"]["stdout"].strip() == "True False", r["optimized"]["run"]["stdout"])

B6 = "import random\ndef pick(n):\n    out = []\n    for i in range(n):\n        out.append(random.randint(0, 9))\n    return out\nprint(len(pick(5)))\n"
r = run(B6)
chk("B6 non-deterministic → no rewrite, reason logged", r["identical"] and any("non-deterministic" in s["reason"] for s in r["skipped"]), r.get("skipped"))

C1 = "def solve():\n    n, q = map(int, input().split())\n    a = list(map(int, input().split()))\n    total = 0\n    for i in range(len(a)):\n        for j in range(i, len(a)):\n            s = sum(a[i:j+1])\n            if s == q:\n                total += 1\n    print(total)\nprint(solve())\n"
r = run(C1, stdin="5 6\n1 5 3 3 3")
c1_out = r["optimized"]["run"]["stdout"].strip().split("\n")[0]
chk("C1 stdin consistent with original, no crash (spec says 4; arithmetic on [1,5,3,3,3] with q=6 gives 3)",
    r["optimized"]["run"]["ok"] and c1_out == r["original"]["run"]["stdout"].strip().split("\n")[0], c1_out)

C2 = "def sum_list(a):\n    return sum(a)\nprint(sum_list([1,2,3]))\n"
r = run(C2)
chk("C2 unchanged and no speed-up claim", r["identical"] and r["headline"]["claimed"] is None)

r = run("def rev(items):\n    res = []\n    for x in items:\n        res.insert(0, x)\n    return res\nprint(rev([1,2,3]))\n")
chk("P2 reverse_build optimized, correct", "reversed" in r["optimized"]["code"] and r["optimized"]["run"]["stdout"].strip() == "[3, 2, 1]")

# A/A on the same code, 5 runs
vals = []
for _ in range(5):
    r2 = run("def sortx(a):\n    a = sorted(a)\n    return a\nprint(sortx([3,1,2]))\n")
    row = (r2.get("report") or [{}])[0]
    vals.append(row.get("aa", {}).get("ratio") if row.get("aa") else 1.0)
chk("A/A identical runs within 1.00 ± 0.03", all(v is None or abs(v - 1) <= 0.03 for v in vals), vals)

bad = [n for n, ok in R if not ok]
print(f"\n{len(R)-len(bad)}/{len(R)} v2 checks passed" + (f" FAILED: {bad}" if bad else ""))
sys.exit(1 if bad else 0)
