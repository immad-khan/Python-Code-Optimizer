import { useState } from "react";
import { CodeEditor } from "./components/CodeEditor";
import { ProgressLog } from "./components/ProgressLog";
import { Results, ResultsBoundary } from "./components/Results";
import { useOptimizer } from "./engine/useOptimizer";

const EXAMPLES: { name: string; code: string }[] = [
  {
    name: "Recursive Fibonacci",
    code: `def fib(n):
    if n < 2:
        return n
    return fib(n - 1) + fib(n - 2)

print(fib(22))
`,
  },
  {
    name: "Two-sum (nested loops)",
    code: `def two_sum(nums, target):
    for i in range(len(nums)):
        for j in range(i + 1, len(nums)):
            if nums[i] + nums[j] == target:
                return [i, j]
    return None

print(two_sum([2, 7, 11, 15, 1, 8], 9))
`,
  },
  {
    name: "Bubble sort",
    code: `def bubble_sort(arr):
    n = len(arr)
    for i in range(n):
        for j in range(0, n - i - 1):
            if arr[j] > arr[j + 1]:
                arr[j], arr[j + 1] = arr[j + 1], arr[j]
    return arr

print(bubble_sort([5, 2, 9, 1, 5, 6]))
`,
  },
  {
    name: "Common elements",
    code: `def common_elements(a, b):
    result = []
    for x in a:
        if x in b:
            result.append(x)
    return result

print(common_elements([1, 2, 3, 4, 5], [4, 5, 6, 7]))
`,
  },
  {
    name: "Primality test",
    code: `def is_prime(n):
    if n < 2:
        return False
    for i in range(2, n):
        if n % i == 0:
            return False
    return True

print([x for x in range(30) if is_prime(x)])
`,
  },
  {
    name: "BFS with list queue",
    code: `def bfs_order(n):
    queue = [0]
    visited = {0}
    order = []
    while queue:
        node = queue.pop(0)
        order.append(node)
        for nxt in (2 * node + 1, 2 * node + 2):
            if nxt < n and nxt not in visited:
                visited.add(nxt)
                queue.append(nxt)
    return order

print(bfs_order(15))
`,
  },
  {
    name: "Palindrome check (nested concats & loops)",
    code: `def is_palindrome(s):
    chars = [c for c in s.lower() if c.isalnum()]
    original = ""
    for c in chars:
        original = original + c
    reversed_str = ""
    for c in reversed(chars):
        reversed_str = reversed_str + c
    if len(original) != len(reversed_str):
        return False
    for i in range(len(original)):
        if original[i] != reversed_str[i]:
            return False
    return True

print(is_palindrome("A man, a plan, a canal: Panama"))
print(is_palindrome("race a car"))
print(is_palindrome("racecar"))
`,
  },
  {
    name: "Max subarray (cubic brute force)",
    code: `def max_subarray(a):
    best = 0
    for i in range(len(a)):
        for j in range(i, len(a)):
            s = 0
            for k in range(i, j + 1):
                s = s + a[k]
            if s > best:
                best = s
    return best

print(max_subarray([1, -2, 3, 4, -1, 2, -5, 4]))
`,
  },
  {
    name: "Count subarrays with sum = target (slices)",
    code: `def count_subarrays(a, target):
    c = 0
    for i in range(len(a)):
        for j in range(i + 1, len(a) + 1):
            if sum(a[i:j]) == target:
                c += 1
    return c

print(count_subarrays([1, 2, 3, -1, 2, 1, 1], 3))
`,
  },
  {
    name: "Best window of size k (sliding window)",
    code: `def best_window(a, k):
    best = None
    for i in range(len(a) - k + 1):
        w = sum(a[i:i + k])
        if best is None or w > best:
            best = w
    return best

print(best_window([4, -1, 2, 9, -3, 5, 1], 3))
`,
  },
  {
    name: "Longest increasing subsequence (O(n²) DP)",
    code: `def lis(nums):
    n = len(nums)
    dp = [1] * n
    for i in range(n):
        for j in range(i):
            if nums[j] < nums[i]:
                dp[i] = max(dp[i], dp[j] + 1)
    return max(dp) if dp else 0

print(lis([10, 9, 2, 5, 3, 7, 101, 18]))
`,
  },
  {
    name: "Palindrome — obfuscated (index list + diagonal loops)",
    code: `def is_palindrome_terrible(s):
    l1 = []
    for ch in s:
        l1.append(ch)
    l2 = list(l1)
    indices = list(range(len(l2)))
    indices.sort(reverse=True)
    rev = []
    for i in indices:
        rev.append(l2[i])
    for i in range(len(l2)):
        for j in range(len(rev)):
            if i == j:
                if l2[i] != rev[j]:
                    return False
    return True

print(is_palindrome_terrible("racecar"), is_palindrome_terrible("abc"))
`,
  },
  {
    name: "Subarray sum equals K (nested loops)",
    code: `def subarray_sum_k(a, k):
    count = 0
    for i in range(len(a)):
        for j in range(i, len(a)):
            s = sum(a[i:j + 1])
            if s == k:
                count += 1
    return count

print(subarray_sum_k([1, 2, 3, -1, 2, 1, 1], 3))
`,
  },
  {
    name: "max_sum_k — k validated (clean sliding window)",
    code: `def max_sum_k(a, k):
    if k <= 0 or k > len(a):
        return None
    best = None
    for i in range(len(a) - k + 1):
        w = sum(a[i:i + k])
        if best is None or w > best:
            best = w
    return best

print(max_sum_k([4, -1, 2, 9, -3, 5, 1], 3))
`,
  },
  {
    name: "Palindrome — obfuscated with [i for i in range(n)] index list",
    code: `def is_palindrome_terrible(s):
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
`,
  },
  {
    name: "Case-insensitive palindrome (conditional string concat)",
    code: `def is_pal_case_insensitive(s):
    cleaned = ""
    for c in s:
        if c.isalnum():
            cleaned = cleaned + c.lower()
    return cleaned == cleaned[::-1]

print(is_pal_case_insensitive("A man, a plan, a canal: Panama"))
`,
  },
  {
    name: "Already tight (expect: no change, 1.00×)",
    code: `def solve_prefix(arr, mod=1000000007):
    total = 0
    for x in arr:
        total = (total + x) % mod
    return total

print(solve_prefix([1, 2, 3, 4, 5, 6, 7, 8, 9, 10]))
`,
  },
];

export default function App() {
  const [code, setCode] = useState("");
  const [hints, setHints] = useState("");
  const [stdin, setStdin] = useState("");
  const { status, statusMessage, log, result, error, elapsed, analyze, cancel } = useOptimizer();
  const running = status === "running";
  const canRun = status === "ready" && code.trim().length > 0;

  return (
    <div className="min-h-screen bg-[#070b14] text-slate-200 selection:bg-sky-500/30">
      {/* header */}
      <header className="sticky top-0 z-20 border-b border-slate-800/80 bg-[#070b14]/85 backdrop-blur">
        <div className="mx-auto flex max-w-[1500px] items-center justify-between px-5 py-3">
          <div className="flex items-center gap-3">
            <div className="flex h-9 w-9 items-center justify-center rounded-lg bg-gradient-to-br from-emerald-400 to-sky-500 font-mono text-sm font-bold text-slate-900 shadow-lg shadow-emerald-500/20">
              O(n)
            </div>
            <div>
              <h1 className="text-base font-semibold tracking-tight text-white">PyOptimize</h1>
              <p className="text-[11px] text-slate-500">Realtime complexity analysis · benchmarking · verified rewriting — runs entirely in your browser</p>
            </div>
          </div>
          <div className="flex items-center gap-2 rounded-full border border-slate-800 bg-slate-900/60 px-3 py-1 text-xs">
            <span
              className={`h-2 w-2 rounded-full ${
                status === "ready" ? "bg-emerald-400" : status === "error" ? "bg-rose-400" : "animate-pulse bg-amber-400"
              }`}
            />
            <span className="text-slate-400">{running ? `Analyzing… ${(elapsed / 1000).toFixed(1)}s` : statusMessage}</span>
          </div>
        </div>
      </header>

      <main className="mx-auto grid max-w-[1500px] gap-6 px-5 py-6 lg:grid-cols-[minmax(0,5fr)_minmax(0,7fr)]">
        {/* left: input */}
        <section className="space-y-3 lg:sticky lg:top-[64px] lg:self-start">
          <div className="flex items-center justify-between">
            <h2 className="text-sm font-semibold uppercase tracking-wider text-slate-300">Python source</h2>
            <div className="flex items-center gap-2 text-xs">
              <select
                className="rounded-lg border border-slate-700 bg-slate-900 px-2 py-1 text-slate-300 outline-none"
                value=""
                onChange={(e) => {
                  const ex = EXAMPLES.find((x) => x.name === e.target.value);
                  if (ex) setCode(ex.code);
                }}
              >
                <option value="" disabled>
                  Insert example…
                </option>
                {EXAMPLES.map((ex) => (
                  <option key={ex.name} value={ex.name}>
                    {ex.name}
                  </option>
                ))}
              </select>
              <button onClick={() => setCode("")} className="rounded-lg border border-slate-700 px-2 py-1 text-slate-400 hover:bg-slate-800">
                Clear
              </button>
            </div>
          </div>
          <CodeEditor
            value={code}
            onChange={setCode}
            onRun={() => canRun && analyze(code, hints, stdin)}
            placeholder={"# Paste any Python code here.\n# Define functions and (optionally) call them at the top level.\n# Press Ctrl/⌘ + Enter to analyze."}
            minHeight={380}
          />
          <div className="grid gap-2 sm:grid-cols-2">
            <label className="text-xs text-slate-400">
              Test hints <span className="text-slate-600">(example calls, used as seeds)</span>
              <textarea
                value={hints}
                onChange={(e) => setHints(e.target.value)}
                placeholder={"solve([1, 2, 3], 5)\ncount_pairs([3, 1], -2)   (example calls, typed in white)"}
                spellCheck={false}
                className="mt-1 h-20 w-full resize-y rounded-lg border border-slate-700 bg-[#0b1120] p-2 font-mono text-[12px] text-white placeholder:text-slate-600 outline-none"
              />
            </label>
            <label className="text-xs text-slate-400">
              Program input (stdin) <span className="text-slate-600">(same input for both versions)</span>
              <textarea
                value={stdin}
                onChange={(e) => setStdin(e.target.value)}
                placeholder={"5 6\n1 5 3 3 3   (example: type it in to run the program)"}
                spellCheck={false}
                className="mt-1 h-20 w-full resize-y rounded-lg border border-slate-700 bg-[#0b1120] p-2 font-mono text-[12px] text-white placeholder:text-slate-600 outline-none"
              />
            </label>
          </div>
          {result?.stdin_hint && (
            <div className="rounded-lg border border-amber-500/30 bg-amber-500/5 px-3 py-2 text-xs text-amber-200">
              ⚠ {result.stdin_hint}
            </div>
          )}
          <div className="flex items-center gap-3">
            {running ? (
              <button onClick={cancel} className="rounded-lg border border-rose-500/50 bg-rose-500/10 px-4 py-2 text-sm font-medium text-rose-200 hover:bg-rose-500/20">
                Cancel
              </button>
            ) : (
              <button
                onClick={() => analyze(code, hints, stdin)}
                disabled={!canRun}
                className="rounded-lg bg-gradient-to-r from-emerald-400 to-sky-500 px-4 py-2 text-sm font-semibold text-slate-900 shadow-lg shadow-emerald-500/20 transition hover:brightness-110 disabled:cursor-not-allowed disabled:opacity-40"
              >
                {status === "booting" ? "Loading Python runtime…" : "Analyze & Optimize"}
              </button>
            )}
            <span className="text-[11px] text-slate-500">
              Ctrl/⌘ + Enter · code executes in a sandboxed WebAssembly interpreter in a Web Worker
            </span>
          </div>
          <ProgressLog log={log} running={running} />
          <details className="rounded-xl border border-slate-800 bg-slate-900/40 p-3 text-xs text-slate-400">
            <summary className="cursor-pointer select-none font-medium text-slate-300">How the engine works</summary>
            <ol className="mt-2 list-decimal space-y-1 pl-5">
              <li>
                <b className="text-slate-300">Static analysis</b> — the AST is walked; loop nesting, halving loops, recursion (master theorem / branching
                factor), membership tests, slicing and builtin costs are composed into a Big-O term per function.
              </li>
              <li>
                <b className="text-slate-300">Execution</b> — the program runs as-is (stdout captured) to measure real wall-clock runtime.
              </li>
              <li>
                <b className="text-slate-300">Growth benchmark</b> — the hot function is called with generated inputs of increasing size (adversarial
                search picks worst-case shapes); the log–log slope is matched to canonical growth models.
              </li>
              <li>
                <b className="text-slate-300">Verified rewriting</b> — a rule library (see the “Rule library” tab for exactly what exists and what doesn’t):
                algorithm templates matched by AST unification (max-subarray → Kadane, LIS → bisect), prefix-sum / sliding-window rewriting with a
                linear-inequality prover for the bounds, plus hash/set/deque/memoization/closed-form/idiom rules. Each candidate must (1) match the
                previous version on generated inputs incl. exception parity, and (2) not be measurably slower in an interleaved A/B timing — otherwise it is reverted.
              </li>
              <li>
                <b className="text-slate-300">Re-measure honestly</b> — if no rewrite survives, the output is byte-identical and the speed-up is reported as exactly
                1.00×. Otherwise original and optimized are timed interleaved (A/B/B/A) at every size, an A/A control measures the harness’s own noise,
                and speed-ups inside that noise floor are labelled “≈ 1×”.
              </li>
            </ol>
          </details>
        </section>

        {/* right: results */}
        <section className="min-w-0">
          {error && (
            <div className="mb-4 rounded-xl border border-rose-500/40 bg-rose-500/10 p-4 text-sm text-rose-200">
              <div className="font-semibold">Error</div>
              <pre className="mt-1 whitespace-pre-wrap font-mono text-xs">{error}</pre>
            </div>
          )}
          {result && result.ok ? (
            <ResultsBoundary resetKey={code}>
              <Results r={result} />
            </ResultsBoundary>
          ) : running ? (
            <div className="flex h-72 flex-col items-center justify-center gap-3 rounded-xl border border-dashed border-slate-800 text-slate-500">
              <div className="h-8 w-8 animate-spin rounded-full border-2 border-slate-700 border-t-emerald-400" />
              <div className="text-sm">Running analysis pipeline…</div>
              <div className="font-mono text-xs text-slate-600">{log[log.length - 1]?.message}</div>
            </div>
          ) : (
            !error && (
              <div className="flex h-72 flex-col items-center justify-center rounded-xl border border-dashed border-slate-800 text-center text-slate-500">
                <div className="text-3xl">⏱️</div>
                <div className="mt-2 text-sm">Results will appear here: complexity before/after, measured runtimes, growth curves, and the optimized code.</div>
                <div className="mt-1 text-xs text-slate-600">
                  Nothing is precomputed — every number is produced live from the code you submit.
                </div>
              </div>
            )
          )}
        </section>
      </main>
    </div>
  );
}
