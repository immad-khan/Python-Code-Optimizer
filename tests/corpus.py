"""Engine test corpus. Run: python3 tests/corpus.py [names...]"""
import sys, json, time, random, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src', 'engine'))
import engine

C = {
"fib": "def fib(n):\n    if n < 2:\n        return n\n    return fib(n-1) + fib(n-2)\nprint(fib(20))\n",
"two_sum": "def two_sum(nums, target):\n    for i in range(len(nums)):\n        for j in range(i+1, len(nums)):\n            if nums[i] + nums[j] == target:\n                return [i, j]\n    return None\nprint(two_sum([2,7,11,15], 9))\n",
"bubble": "def bubble_sort(arr):\n    n = len(arr)\n    for i in range(n):\n        for j in range(0, n-i-1):\n            if arr[j] > arr[j+1]:\n                arr[j], arr[j+1] = arr[j+1], arr[j]\n    return arr\nprint(bubble_sort([5,2,9,1]))\n",
"dups": "def has_duplicates(items):\n    for i in range(len(items)):\n        for j in range(i+1, len(items)):\n            if items[i] == items[j]:\n                return True\n    return False\nprint(has_duplicates([1,2,3,1]))\n",
"prime": "def is_prime(n):\n    if n < 2:\n        return False\n    for i in range(2, n):\n        if n % i == 0:\n            return False\n    return True\nprint([x for x in range(30) if is_prime(x)])\n",
"common": "def common_elements(a, b):\n    result = []\n    for x in a:\n        if x in b:\n            result.append(x)\n    return result\nprint(common_elements([1,2,3,4],[3,4,5]))\n",
"count": "def most_frequent(nums):\n    best = None\n    best_count = 0\n    for x in nums:\n        c = nums.count(x)\n        if c > best_count:\n            best_count = c\n            best = x\n    return best\nprint(most_frequent([1,3,3,2,3,1]))\n",
"queue": "def bfs_order(n):\n    queue = [0]\n    visited = {0}\n    order = []\n    while queue:\n        node = queue.pop(0)\n        order.append(node)\n        for nxt in (2*node+1, 2*node+2):\n            if nxt < n and nxt not in visited:\n                visited.add(nxt)\n                queue.append(nxt)\n    return order\nprint(bfs_order(15))\n",
"sumrange": "def total(n):\n    s = 0\n    for i in range(n):\n        s += i\n    return s\nprint(total(1000))\n",
"hoist": "def normalize(values):\n    out = []\n    for v in values:\n        out.append(v / max(values) if max(values) else 0)\n    return out\nprint(normalize([1,2,4]))\n",
"binsearch": "def binary_search(arr, target):\n    lo, hi = 0, len(arr) - 1\n    while lo <= hi:\n        mid = (lo + hi) // 2\n        if arr[mid] == target:\n            return mid\n        elif arr[mid] < target:\n            lo = mid + 1\n        else:\n            hi = mid - 1\n    return -1\nprint(binary_search([1,3,5,7], 5))\n",
"dedupe": "def remove_duplicates(items):\n    result = []\n    for item in items:\n        if item not in result:\n            result.append(item)\n    return result\nprint(remove_duplicates([3,1,3,2,1]))\n",
"palindrome": "def is_palindrome(s):\n    chars = [c for c in s.lower() if c.isalnum()]\n    original = ''\n    for c in chars:\n        original = original + c\n    reversed_str = ''\n    for c in reversed(chars):\n        reversed_str = reversed_str + c\n    if len(original) != len(reversed_str):\n        return False\n    for i in range(len(original)):\n        if original[i] != reversed_str[i]:\n            return False\n    return True\nprint(is_palindrome('A man, a plan, a canal: Panama'))\nprint(is_palindrome('race a car'))\n",
"terrible": "def is_palindrome_terrible(s):\n    l1 = []\n    for ch in s:\n        l1.append(ch)\n    l2 = list(l1)\n    indices = list(range(len(l2)))\n    indices.sort(reverse=True)\n    rev = []\n    for i in indices:\n        rev.append(l2[i])\n    for i in range(len(l2)):\n        for j in range(len(rev)):\n            if i == j:\n                if l2[i] != rev[j]:\n                    return False\n    return True\nprint(is_palindrome_terrible('racecar'), is_palindrome_terrible('abc'))\n",
"max_subarray": "def max_subarray(a):\n    best = 0\n    for i in range(len(a)):\n        for j in range(i, len(a)):\n            s = 0\n            for k in range(i, j + 1):\n                s = s + a[k]\n            if s > best:\n                best = s\n    return best\nprint(max_subarray([1, -2, 3, 4, -1, 2]))\n",
"kadane_running": "def best_sum(nums):\n    best = nums[0] if nums else 0\n    for i in range(len(nums)):\n        s = 0\n        for j in range(i, len(nums)):\n            s += nums[j]\n            best = max(best, s)\n    return best\n",
"count_subarrays": "def count_subarrays(a, target):\n    c = 0\n    for i in range(len(a)):\n        for j in range(i + 1, len(a) + 1):\n            if sum(a[i:j]) == target:\n                c += 1\n    return c\n",
"window": "def best_window(a, k):\n    best = None\n    for i in range(len(a) - k + 1):\n        w = sum(a[i:i + k])\n        if best is None or w > best:\n            best = w\n    return best\n",
"lis": "def lis(nums):\n    n = len(nums)\n    dp = [1] * n\n    for i in range(n):\n        for j in range(i):\n            if nums[j] < nums[i]:\n                dp[i] = max(dp[i], dp[j] + 1)\n    return max(dp) if dp else 0\n",
"toplevel": "nums = list(range(300))\ntotal = 0\nfor x in nums:\n    if x in nums:\n        total += x\nprint(total)\n",
"class_pairs": "class S:\n    def __init__(self):\n        self.items = []\ndef count_pairs(arr):\n    count = 0\n    for i in range(len(arr)):\n        for j in range(i+1, len(arr)):\n            if arr[i] == arr[j]:\n                count += 1\n    return count\nprint(count_pairs([1,1,2]))\n",
"input_fn": "def solve(n):\n    return sum(range(n))\nn = int(input())\nprint(solve(n))\n",
"already_tight": "def solve_prefix(arr, mod=1000000007):\n    total = 0\n    for x in arr:\n        total = (total + x) % mod\n    return total\nprint(solve_prefix([1,2,3,4,5]))\n",
"fib2arg": "def f(n, k):\n    if n < 2:\n        return n + k\n    return f(n-1, k) + f(n-2, k)\nprint(f(18, 1))\n",
}

# independent equivalence oracle: original vs optimized on random inputs (separate from the engine's own check)
def _oracle(fn_name, orig, opt, tags, rng, n=300):
    A, B = {}, {}
    exec(compile(orig, "o", "exec"), A); exec(compile(opt, "n", "exec"), B)
    fa, fb = A.get(fn_name), B.get(fn_name)
    if not callable(fa) or not callable(fb):
        return "n/a"
    for i in range(n):
        args = engine.make_small_args(tags, 99991 + i * 7, test_idx=i % 40, int_cap=14)
        def call(f, a):
            try: return ("ok", engine._normalize(f(*a)))
            except Exception as e: return ("exc", type(e).__name__)
        import copy
        if call(fa, copy.deepcopy(args)) != call(fb, copy.deepcopy(args)):
            return f"MISMATCH on {args!r}"
    return "OK"

if __name__ == "__main__":
    names = sys.argv[1:] or list(C)
    bad = 0
    rng = random.Random(0)
    for name in names:
        code = C[name]; t0 = time.time()
        old = sys.stdout
        try:
            res = json.loads(engine.run_pipeline(code))
        except Exception as e:
            print("CRASH", name, e); bad += 1; continue
        finally:
            sys.stdout = old
        if not res["ok"]:
            print("ERR", name, res["error"]); bad += 1; continue
        app = [c["rule"] for c in res["changes"] if c["status"] == "applied"]
        rej = [c["rule"] for c in res["changes"] if c["status"] == "rejected"]
        p = res["protocol"]
        orc = "n/a"
        if res["target_function"] and not res["identical"]:
            orc = _oracle(res["target_function"], res["original"]["code"], res["optimized"]["code"], res["param_types"], rng)
        stdout_same = res["original"]["run"]["stdout"] == res["optimized"]["run"]["stdout"]
        flag = ""
        if orc.startswith("MISMATCH") or not stdout_same: flag = "  <<<<< CHECK"; bad += 1
        lg = p["speedup_largest_n"]; sm = p["speedup_smallest_n"]
        print("%-15s %4.1fs %-9s -> %-9s | applied=%d %s | rej=%d | large n: %s | small n: %s | trust=%s | min_valid=%s | oracle=%s%s" % (
            name, time.time()-t0, p["original_static"], p["optimized_static"], len(app), sorted(set(app)), len(rej),
            ("%.1fx%s" % (lg[1], "" if lg[2] else "~")) if lg else "-", ("%.1fx%s" % (sm[1], "" if sm[2] else "~")) if sm else "-",
            p["benchmark_trustworthy"], p["verification_min_valid"], orc, flag))
        if name in ("palindrome", "terrible", "two_sum", "max_subarray", "already_tight"):
            print("    " + res["optimized"]["code"].strip().replace("\n", "\n    "))
            if res["warnings"]: print("    warnings:", res["warnings"])
    print("\nBAD:", bad)
