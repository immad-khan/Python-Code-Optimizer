import sys, os, json, random, copy, time
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src', 'engine'))
import engine

CASES = {
"A3_listcomp_indices": '''
def is_palindrome_terrible(s):
    l1 = []
    for ch in s:
        l1.append(ch)
    l2 = list(l1)
    n = len(l2)
    indices = [i for i in range(n)]
    indices.sort(reverse=True)
    rev = [l2[i] for i in indices]
    for i in range(len(l2)):
        for j in range(len(rev)):
            if i == j:
                if l2[i] != rev[j]:
                    return False
    return True
print(is_palindrome_terrible("racecar"), is_palindrome_terrible("abc"))
''',
"A8_subarray_sum_k": '''
def subarray_sum_k(a, k):
    count = 0
    for i in range(len(a)):
        for j in range(i, len(a)):
            s = sum(a[i:j+1])
            if s == k:
                count += 1
    return count
print(subarray_sum_k([1, 2, 3, -1, 2, 1, 1], 3))
''',
"A9_max_sum_k_unvalidated": '''
def max_sum_k(a, k):
    best = None
    for i in range(len(a) - k + 1):
        w = sum(a[i:i+k])
        if best is None or w > best:
            best = w
    return best
print(max_sum_k([4, -1, 2, 9, -3, 5, 1], 3))
''',
"A9_max_sum_k_validated": '''
def max_sum_k(a, k):
    if k <= 0 or k > len(a):
        return None
    best = None
    for i in range(len(a) - k + 1):
        w = sum(a[i:i+k])
        if best is None or w > best:
            best = w
    return best
print(max_sum_k([4, -1, 2, 9, -3, 5, 1], 3))
''',
"A10_pal_case_insensitive": '''
def is_pal_case_insensitive(s):
    cleaned = ""
    for c in s:
        if c.isalnum():
            cleaned = cleaned + c.lower()
    return cleaned == cleaned[::-1]
print(is_pal_case_insensitive("A man, a plan, a canal: Panama"))
''',
"LIS_guarded": '''
def lis(a):
    if not a:
        return 0
    n = len(a)
    dp = [1] * n
    for i in range(n):
        for j in range(i):
            if a[j] < a[i]:
                dp[i] = max(dp[i], dp[j] + 1)
    return max(dp)
print(lis([10, 9, 2, 5, 3, 7, 101, 18]))
''',
"LIS_unguarded": '''
def lis(a):
    n = len(a)
    dp = [1] * n
    for i in range(n):
        for j in range(i):
            if a[j] < a[i]:
                dp[i] = max(dp[i], dp[j] + 1)
    return max(dp)
print(lis([3, 1, 2]))
''',
}

def oracle(fn, orig, opt, tags, n=300):
    A, B = {}, {}
    exec(compile(orig, "o", "exec"), A); exec(compile(opt, "n", "exec"), B)
    for i in range(n):
        args = engine.make_small_args(tags, 4242 + i * 11, test_idx=i % 45, int_cap=12)
        def call(f, a):
            try: return ("ok", engine._normalize(f(*a)))
            except Exception as e: return ("exc", type(e).__name__)
        if call(A[fn], copy.deepcopy(args)) != call(B[fn], copy.deepcopy(args)):
            return "MISMATCH %r" % (args,)
    return "OK"

if __name__ == "__main__":
    names = sys.argv[1:] or list(CASES)
    for name in names:
        t0 = time.time()
        res = json.loads(engine.run_pipeline(CASES[name]))
        p = res["protocol"]
        f = next((x for x in res["optimized"]["static"]["functions"] if x["name"] == res["target_function"]), {})
        orc = oracle(res["target_function"], res["original"]["code"], res["optimized"]["code"], res["param_types"]) if not res["identical"] else "n/a"
        lg = p["speedup_largest_n"]
        print("=== %s  (%.1fs)  %s -> %s  cond=%s  speedup=%s  oracle=%s" % (name, time.time() - t0, p["original_static"], p["optimized_static"], f.get("conditional"), ("%.1fx" % lg[1]) if lg else "-", orc))
        print("   rules:", [(c["rule"], c["status"]) for c in res["changes"]])
        print("    " + res["optimized"]["code"].strip().replace("\n", "\n    "))
        if res["optimizer_notes"]: print("   notes:", res["optimizer_notes"][:2])
