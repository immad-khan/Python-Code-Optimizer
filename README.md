# Python Code Optimizer

A browser-based Python optimization tool. It analyzes Python source, applies rule-based rewrites, verifies candidates with randomized differential testing, and reports per-function benchmark results. The engine runs inside Pyodide (CPython on WebAssembly) in a Web Worker.

## How it works

1. **Parse & static analysis** — builds AST, infers parameter types/shapes, and estimates complexity.
2. **Original run & growth benchmark** — executes the input program, probes adversarial input shapes, and measures growth for the target function.
3. **Rewrite search** — tries rule-based transformations (algorithm templates, idioms, cleanup). Candidates are compile-checked, differentially tested against the previous version, and regression-guarded with a bench-pair A/B measurement before being applied.
4. **Final verification** — changed functions are end-to-end differentially tested against the original source. If a function fails final verification, only that function's rewrites are reverted.
5. **Reporting** — emits per-function measurements, A/A control noise, verification counts, and protocol metadata. No single headline speedup is reported across unrelated functions.

## Trust / verification model

- **Not a proof.** Verification is randomized differential testing on generated inputs, not formal equivalence proof.
- **Strict comparison.** Normal runs compare return value (type-sensitive, NaN==-NaN, `-0.0 != 0.0`, `1 != True`), stdout, argument mutation, and module globals. Same exception type is parity, not positive evidence.
- **Per-candidate vs cleanup.** Per-candidate rewrites are differentially tested before applying. Final cleanup rewrites (`dead_branch`, `dead_code`, `cleanup`) are covered by final end-to-end verification of changed functions; the protocol reports this scope explicitly.
- **Benchmarks.** Reported benchmarks use interleaved A/B rounds, warmups, fresh deepcopy per call, cache clearing, MAD spread, and an A/A control. A speedup claim requires ratio and spread confidence thresholds.

## Runtime / sandboxing

- User Python code is executed by design. In this app, execution happens inside **Pyodide/WASM in a browser worker**, which is the intended isolation boundary.
- Do **not** reuse `load_namespace`/`exec` engine paths as a host-side security sandbox outside Pyodide.
- The worker loads Pyodide from the versioned jsDelivr CDN URL; version pinning is present, but there is no SRI hash pinning.

## Development

Requirements: Node.js 18+ and npm.

```bash
npm install
npm run dev      # local Vite dev server
npm run build    # production build
npm run preview  # preview production build
```

## Key files

- `src/engine/engine.py` — Python analysis/optimization/verification/benchmark pipeline (runs in Pyodide).
- `src/engine/pyodide.worker.ts` — Web Worker bootstrap; loads Pyodide and calls `run_pipeline`.
- `src/engine/useOptimizer.ts` — React hook for worker lifecycle, timeout, logs, and results.
- `src/engine/types.ts` — worker/result TypeScript contract.
- `src/App.tsx`, `src/components/*` — UI.
- `tests/` — acceptance/probe/corpus scripts.

## Known gaps

The engine exposes its known gaps in the result payload (`known_gaps`) and rule metadata (`rules`). See `RULES` and `KNOWN_GAPS` in `src/engine/engine.py` for the current source of truth.
