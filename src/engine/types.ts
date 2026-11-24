export interface FunctionComplexity {
  name: string;
  time: string;
  rank: number;
  space: string;
  params: string[];
  notes: string[];
  line: number;
  conditional?: { when: string; worst: string; otherwise: string; rank_worst: number; rank_other: number }[];
}

export interface StaticResult {
  functions: FunctionComplexity[];
  overall: string;
  overall_rank: number;
  overall_space: string;
  top_level: string;
  notes: string[];
}

export interface RunResult {
  ok: boolean;
  error: string | null;
  stdout: string;
  times_ms: number[];
  best_ms: number | null;
  median_ms: number | null;
}

export interface FitCandidate {
  model: string;
  r2: number;
  rank: number;
  score: number;
  model_slope?: number;
}

export interface Fit {
  label: string;
  r2: number;
  rank: number;
  slope: number | null;
  candidates: FitCandidate[];
}

export interface BenchPoint {
  n: number;
  t_ms: number;
}

export interface BenchResult {
  points: BenchPoint[];
  fit: Fit | null;
  error: string | null;
}

export interface Variant {
  code: string;
  static: StaticResult;
  run: RunResult;
  bench?: BenchResult; // optional: the engine may legitimately omit it
}

export interface ChangeVerification {
  method: string;
  inputs: number;
  valid: number; // BOTH versions returned normally and are strictly equal
  exception_parity: number; // both raised the same exception type
  capped?: boolean;
  budget_hit?: boolean;
}

export interface ChangeAB {
  ratio: number;
  noise: number;
  n: number;
}

export type ChangeStatus = "applied" | "rejected" | "pending" | "suggested" | "skipped" | "inconclusive";

export interface Change {
  title: string;
  detail: string;
  function: string | null;
  before: string;
  after: string;
  kind: "complexity" | "constant" | "advice";
  status: ChangeStatus;
  message: string;
  rule?: string | null;
  verification?: ChangeVerification | null;
  ab?: ChangeAB | null;
  portable?: boolean;
  portable_note?: string | null;
}

/** One measured, CHANGED function. All timings are real per-call milliseconds. */
export interface PerFunction {
  name: string;
  n: number;
  orig_ms: number;
  opt_ms: number;
  ratio: number; // median of per-round orig/opt ratios (>1 means faster)
  spread: number; // max(MAD, A/A deviation, 0.03)
  aa: number; // A/A control ratio (1.0 = unbiased)
  verdict: string;
  claimed: boolean;
}

export interface VerificationItem extends ChangeVerification {
  title: string;
  status: ChangeStatus;
  rule?: string | null;
  function?: string | null;
  ab?: ChangeAB | null;
}

export interface VerificationSummary {
  applied: number;
  reverted: number;
  suggested: number;
  inconclusive?: number;
  skipped?: number;
  per_candidate_verified?: number;
  cleanup_only_applied?: number;
  normal_runs_min: number | null;
  normal_runs_total: number;
  both_raised_total: number;
  items: VerificationItem[];
}

export interface RuleInfo {
  id: string;
  layer: "algorithm" | "idiom" | "advisory";
  name: string;
  desc: string;
  fired: boolean;
  suggested: boolean;
  skipped?: boolean;
}

export interface ReportRow {
  function: string;
  applied: string[];
  skipped: { function: string; rule: string; reason: string }[];
  static_before: string | null;
  static_after: string | null;
  ratio: number | null;
  spread: number | null;
  n: number | null;
  orig_ms?: number | null;
  opt_ms?: number | null;
  aa: number | null;
  verdict: string;
}

export interface Protocol {
  functions_changed: number;
  functions_skipped: number;
  measured_count: number;
  function_total: number;
  stdin_hint?: string | null;
  best_function: PerFunction | null;
  control_pct: number | null; // max |A/A ratio - 1| over measured functions
  benchmark_trustworthy: boolean | null; // == control_pct <= 0.05 (null: nothing was timed)
  trust_reason: string;
  normal_runs_min: number | null;
  normal_runs_total: number;
  both_raised_total: number;
  converged: boolean;
  final_verification_ok: boolean;
  final_verification_functions: string[];
  per_candidate_verified?: number;
  cleanup_only_applied?: number;
  verification_scope?: string;
  consistency: Record<string, string>;
  has_run_error: boolean;
}

export interface PipelineResult {
  ok: boolean;
  error?: string;
  original: Variant;
  optimized: Variant;
  target_function: string | null;
  param_types: string[] | null;
  input_strategy?: { list: string; secondary: string; primary: string; complete?: boolean };
  changes: Change[];
  optimizer_notes: string[];
  changed: boolean;
  output_match: boolean;
  identical?: boolean;
  output_status?: "identical" | "differs" | "no_output" | "error" | "unchanged";
  noise?: { control_pct: number | null; method: string };
  warnings?: string[];
  infos?: string[];
  consistency_by_fn?: Record<string, { status: string; message: string }>;
  gate?: { converged: boolean; remaining: string[]; literal_errors: number };
  final_verification?: { ok: boolean; functions: { name: string; inputs: number; valid: number; exception_parity: number; ok: boolean; msg: string }[] };
  protocol?: Protocol;
  verification?: VerificationSummary;
  rules?: RuleInfo[];
  known_gaps?: string[];
  verification_policy?: { class: string; cap: string }[];
  skipped?: { function: string; rule: string; reason: string }[];
  report?: ReportRow[];
  per_function?: PerFunction[];
  changed_count?: number;
  skipped_count?: number;
  measured_count?: number;
  function_total?: number;
  stdin_hint?: string | null;
  program?: { status: string; message: string; orig_ms: number | null; opt_ms: number | null; ratio?: number | null; shown: boolean } | null;
  contest_template?: string | null;
  elapsed_ms: number;
}

export interface ProgressEvent {
  stage: string;
  message: string;
  payload?: unknown;
}

export interface LogEntry extends ProgressEvent {
  id: number;
  at: number;
}

export type EngineStatus = "booting" | "ready" | "running" | "error";

export type WorkerOut =
  | { type: "status"; message: string }
  | { type: "ready" }
  | { type: "progress"; data: ProgressEvent }
  | { type: "result"; id: number; result: PipelineResult }
  | { type: "error"; id?: number; message: string };

export type WorkerIn = { type: "init" } | { type: "analyze"; id: number; code: string; hints?: string; stdin?: string };
