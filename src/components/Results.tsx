import { Component, useState, type ReactNode } from "react";
import type { Change, PipelineResult, RuleInfo, Variant } from "../engine/types";
import { CodeBlock } from "./CodeEditor";
import { DiffView } from "./DiffView";
import { fmtMs, fmtN, GrowthChart } from "./GrowthChart";

/* ------------------------------------------------------------------ error boundary */
export class ResultsBoundary extends Component<{ children: ReactNode; resetKey?: string }, { error: Error | null }> {
  state = { error: null as Error | null };
  static getDerivedStateFromError(error: Error) {
    return { error };
  }
  componentDidUpdate(prev: { resetKey?: string }) {
    if (prev.resetKey !== this.props.resetKey && this.state.error) this.setState({ error: null });
  }
  render() {
    if (!this.state.error) return this.props.children;
    return (
      <div className="rounded-xl border border-rose-500/40 bg-rose-500/10 p-4 text-sm text-rose-100">
        <div className="font-semibold">The results view failed to render.</div>
        <div className="mt-1 text-xs">The analysis finished, but the panel could not display it. The engine was not affected.</div>
        <pre className="mt-2 overflow-auto rounded bg-black/30 p-2 font-mono text-[11px] text-rose-200">{String(this.state.error.message)}</pre>
        <button onClick={() => this.setState({ error: null })} className="mt-3 rounded-lg border border-rose-500/40 px-3 py-1 text-xs hover:bg-rose-500/20">
          Try again
        </button>
      </div>
    );
  }
}

/* ------------------------------------------------------------------ helpers */
function rankTone(label: string | null | undefined) {
  // classify a Big-O label by scanning characters (no regex literals: '/' inside JSX text confuses the parser)
  const r = label ?? "";
  const exp = r.includes("^n") || r.includes("n!") || r.includes("k^n");
  if (exp) return "text-rose-300 border-rose-500/40 bg-rose-500/10";
  const cube = r.includes("³");
  const sq = r.includes("²");
  const log = r.includes("log");
  if (cube) return "text-orange-300 border-orange-500/40 bg-orange-500/10";
  if (sq) return "text-amber-300 border-amber-500/40 bg-amber-500/10";
  if (log) return "text-amber-300 border-amber-500/40 bg-amber-500/10";
  if (r.includes("n")) return "text-lime-300 border-lime-500/40 bg-lime-500/10";
  return "text-emerald-300 border-emerald-500/40 bg-emerald-500/10";
}

function fmtRatio(ratio: number | null | undefined) {
  if (ratio == null || !Number.isFinite(ratio)) return "—";
  return ratio >= 1 ? `${ratio.toFixed(ratio >= 100 ? 0 : 2)}×` : `${(1 / ratio).toFixed(2)}× slower`;
}

const STATUS_STYLE: Record<string, { box: string; badge: string; label: string; icon: string; msg: string }> = {
  applied: { box: "border-emerald-500/30 bg-emerald-500/5", badge: "bg-emerald-500/20 text-emerald-300", label: "applied", icon: "✓", msg: "text-emerald-400/80" },
  inconclusive: { box: "border-amber-500/40 bg-amber-500/5", badge: "bg-amber-500/25 text-amber-200", label: "inconclusive", icon: "?", msg: "text-amber-200/80" },
  rejected: { box: "border-slate-800 bg-slate-900/40", badge: "bg-rose-500/20 text-rose-300", label: "reverted", icon: "✘", msg: "text-rose-300/80" },
  skipped: { box: "border-slate-800 bg-slate-900/30", badge: "bg-slate-700/60 text-slate-300", label: "skipped", icon: "⏭", msg: "text-slate-400" },
  suggested: { box: "border-sky-500/30 bg-sky-500/5", badge: "bg-sky-500/20 text-sky-300", label: "advice only", icon: "ℹ", msg: "text-sky-300/80" },
};

/* ------------------------------------------------------------------ small pieces */
function RunError({ run }: { run?: { ok?: boolean; error?: string | null } }) {
  if (!run?.error) return null;
  return <div className="mt-3 rounded bg-rose-500/10 p-2 font-mono text-[11px] text-rose-200">{run.error}</div>;
}

function VariantCard({ title, v, accent }: { title: string; v?: Variant; accent: string }) {
  if (!v) {
    return (
      <div className={`rounded-xl border bg-[#0b1120] p-4 ${accent} text-xs text-slate-500`}>
        <span>{title}</span>: no data
      </div>
    );
  }
  const fit = v.bench?.fit ?? null;
  const best = v.run?.best_ms;
  const fns = v.static?.functions ?? [];
  return (
    <div className={`rounded-xl border bg-[#0b1120] p-4 ${accent}`}>
      <div className="mb-3 flex items-center justify-between gap-2">
        <h3 className="text-sm font-semibold uppercase tracking-wider text-slate-300">{title}</h3>
        {!v.run?.ok && <span className="rounded bg-rose-500/20 px-2 py-0.5 text-[11px] text-rose-300">runtime error</span>}
      </div>
      <RunError run={v.run} />
      <div className="grid grid-cols-2 gap-2">
        <div className="rounded-lg border border-slate-800 bg-slate-900/60 p-3">
          <div className="text-[10px] uppercase tracking-wider text-slate-500">Measured growth (fit)</div>
          <div className={`mt-1 inline-block rounded-md border px-2 py-0.5 font-mono text-lg font-semibold ${fit ? rankTone(fit.label) : "border-slate-700 text-slate-400"}`}>
            {fit ? fit.label : "n/a"}
          </div>
          <div className="mt-1 text-[11px] text-slate-500">
            {fit ? `log–log slope ${fit.slope ?? "?"} · R² ${fit.r2.toFixed(3)}` : v.bench?.error ?? "no benchmark data"}
          </div>
        </div>
        <div className="rounded-lg border border-slate-800 bg-slate-900/60 p-3">
          <div className="text-[10px] uppercase tracking-wider text-slate-500">Program runtime</div>
          <div className="mt-1 inline-block rounded-md border border-slate-700 px-2 py-0.5 font-mono text-lg font-semibold text-slate-100">
            {!v.run?.ok ? "failed" : best != null && best >= 0.5 ? fmtMs(best) : "< 0.5 ms"}
          </div>
          <div className="mt-1 text-[11px] text-slate-500">{best != null && best < 0.5 ? "below timer resolution" : `best of ${v.run?.times_ms?.length ?? 0} runs`}</div>
        </div>
      </div>
      {fns.length > 0 && (
        <table className="mt-3 w-full text-left text-xs">
          <thead className="text-[10px] uppercase tracking-wider text-slate-500">
            <tr>
              <th className="py-1 font-medium">function</th>
              <th className="py-1 font-medium">static (per function)</th>
            </tr>
          </thead>
          <tbody className="font-mono">
            {fns.map((f) => (
              <tr key={f.name} className="border-t border-slate-800/80 align-top">
                <td className="py-1 pr-2 text-slate-300">{f.name}</td>
                <td className="py-1 text-slate-300">
                  {f.time}
                  {f.conditional?.[0] && (
                    <span className="ml-2 font-sans text-[10px] text-amber-200/80">
                      {f.conditional[0].otherwise} when {f.conditional[0].when}, else {f.conditional[0].worst}
                    </span>
                  )}
                </td>
              </tr>
            ))}
          </tbody>
        </table>
      )}
    </div>
  );
}

function ChangeItem({ c }: { c: Change }) {
  const [open, setOpen] = useState(c.status === "applied" || c.status === "inconclusive");
  const st = STATUS_STYLE[c.status] ?? STATUS_STYLE.skipped;
  return (
    <div className={`rounded-lg border p-3 ${st.box}`}>
      <button onClick={() => setOpen(!open)} className="flex w-full items-start gap-3 text-left">
        <span className={`mt-0.5 shrink-0 rounded px-1.5 py-0.5 text-[10px] font-semibold uppercase tracking-wider ${st.badge}`}>{st.label}</span>
        <span className="flex-1">
          <span className="text-sm font-medium text-slate-100">{c.title}</span>
          {c.function && <span className="ml-2 rounded bg-slate-800 px-1.5 py-0.5 font-mono text-[10px] text-slate-400">{c.function}</span>}
          {c.rule && <span className="ml-2 rounded border border-sky-500/30 bg-sky-500/10 px-1.5 py-0.5 font-mono text-[10px] text-sky-300">rule: {c.rule}</span>}
        </span>
        <span className="text-slate-500">{open ? "−" : "+"}</span>
      </button>
      {open && (
        <div className="mt-2 space-y-2 pl-1 text-xs">
          <p className="text-slate-300">{c.detail}</p>
          <div className="grid gap-2 md:grid-cols-2">
            <pre className="overflow-auto rounded bg-rose-500/10 p-2 font-mono text-[11px] text-rose-200">{c.before}</pre>
            <pre className="overflow-auto rounded bg-emerald-500/10 p-2 font-mono text-[11px] text-emerald-200">{c.after}</pre>
          </div>
          <p className={`text-[11px] ${st.msg}`}>
            {st.icon} {c.message}
          </p>
        </div>
      )}
    </div>
  );
}

function RuleRow({ r }: { r: RuleInfo }) {
  const tag = r.fired ? "fired" : r.suggested ? "advised" : (r as { skipped?: boolean }).skipped ? "skipped" : "not fired";
  const tone = r.fired ? "bg-emerald-500/20 text-emerald-300" : r.suggested ? "bg-sky-500/20 text-sky-300" : (r as { skipped?: boolean }).skipped ? "bg-slate-600/50 text-slate-200" : "bg-slate-800 text-slate-500";
  return (
    <div className="flex items-start gap-3 border-t border-slate-800/80 py-2 first:border-t-0">
      <span className={`mt-0.5 w-24 shrink-0 rounded px-1.5 py-0.5 text-center text-[10px] font-semibold uppercase tracking-wider ${tone}`}>{tag}</span>
      <div className="text-xs">
        <div className="font-medium text-slate-200">{r.name}</div>
        <div className="text-slate-500">{r.desc}</div>
      </div>
    </div>
  );
}

/* ------------------------------------------------------------------ report table */
type Row = NonNullable<PipelineResult["report"]>[number];

function ReportTable({ rows }: { rows: Row[] }) {
  return (
    <div className="overflow-auto rounded-xl border border-slate-700/70 bg-[#0b1120]">
      <table className="w-full text-left text-xs">
        <thead className="text-[10px] uppercase tracking-wider text-slate-500">
          <tr>
            <th className="px-3 py-2 font-medium">function</th>
            <th className="px-3 py-2 font-medium">applied</th>
            <th className="px-3 py-2 font-medium">skipped (reason)</th>
            <th className="px-3 py-2 font-medium">static before → after</th>
            <th className="px-3 py-2 font-medium">speed-up (median ± spread)</th>
            <th className="px-3 py-2 font-medium">verdict</th>
          </tr>
        </thead>
        <tbody>
          {rows.map((row) => (
            <tr key={row.function} className="border-t border-slate-800/80 align-top">
              <td className="px-3 py-2 font-mono text-slate-200">{row.function}</td>
              <td className="px-3 py-2 text-slate-300">{row.applied?.length ? row.applied.join("; ") : "—"}</td>
              <td className="px-3 py-2 text-amber-200/90">{row.skipped?.length ? row.skipped.map((x) => `${x.rule}: ${x.reason}`).join("; ") : "—"}</td>
              <td className={`px-3 py-2 font-mono ${row.static_before !== row.static_after ? "text-lime-200" : "text-slate-300"}`}>
                {row.static_before ?? "?"} → {row.static_after ?? "?"}
              </td>
              <td className="px-3 py-2 font-mono text-slate-200">
                {row.ratio != null ? `${fmtRatio(row.ratio)} ± ${((row.spread ?? 0) * 100).toFixed(0)}%` : "—"}
                {row.orig_ms != null && row.opt_ms != null && (
                  <div className="text-[10px] text-slate-500">
                    {fmtMs(row.orig_ms)} → {fmtMs(row.opt_ms)} at n={fmtN(row.n ?? 0)}
                  </div>
                )}
              </td>
              <td className={`px-3 py-2 ${row.verdict?.startsWith("faster") ? "text-emerald-300" : "text-slate-400"}`}>
                {row.verdict}
                {row.aa != null && <div className="text-[10px] text-slate-500">A/A {row.aa.toFixed(3)}</div>}
              </td>
            </tr>
          ))}
          {rows.length === 0 && (
            <tr>
              <td colSpan={6} className="px-3 py-6 text-center text-slate-500">No functions were found.</td>
            </tr>
          )}
        </tbody>
      </table>
    </div>
  );
}

/* ------------------------------------------------------------------ main */
export function Results({ r }: { r: PipelineResult }) {
  const [tab, setTab] = useState<"report" | "overview" | "transforms" | "skipped" | "rules" | "code">("report");
  const [codeTab, setCodeTab] = useState<"diff" | "pure" | "template">("diff");
  const [copied, setCopied] = useState(false);

  const identical = !!r.identical;
  const report: Row[] = r.report ?? [];
  const perFn = r.per_function ?? [];
  const skipped = r.skipped ?? [];
  const changes: Change[] = r.changes ?? [];
  const applied = changes.filter((c) => c.status === "applied");
  const inconclusive = changes.filter((c) => c.status === "inconclusive");
  const rejected = changes.filter((c) => c.status === "rejected");
  const p = r.protocol;
  const best = p?.best_function ?? null;
  const control = p?.control_pct ?? null;
  const trustworthy = p?.benchmark_trustworthy ?? null;
  const claimedCount = perFn.filter((x) => x.claimed).length;
  const aaVals = perFn.map((x) => x.aa).filter((v) => typeof v === "number" && Number.isFinite(v));
  const aaRange =
    aaVals.length > 0
      ? `${Math.min(...aaVals).toFixed(3)}–${Math.max(...aaVals).toFixed(3)}`
      : null;
  const origErr = r.original?.run?.error, optErr = r.optimized?.run?.error;

  const activeCode = codeTab === "template" && r.contest_template ? r.contest_template : r.optimized?.code ?? "";
  const copy = async () => {
    try {
      await navigator.clipboard.writeText(activeCode);
      setCopied(true);
      setTimeout(() => setCopied(false), 1500);
    } catch {
      /* clipboard unavailable */
    }
  };
  const btn = (id: typeof tab, label: string) => (
    <button key={id} onClick={() => setTab(id)} className={`rounded-lg px-3 py-1.5 font-medium transition ${tab === id ? "bg-slate-800 text-white" : "text-slate-400 hover:text-slate-200"}`}>
      {label}
    </button>
  );

  return (
    <div className="space-y-5">
      {/* ---- two cards + the trust line. No file-level complexity class, no single headline number. ---- */}
      <div className="grid gap-3 sm:grid-cols-3">
        <div className="rounded-xl border border-slate-800 bg-gradient-to-br from-slate-900 to-[#0b1120] p-4">
          <div className="text-[10px] uppercase tracking-wider text-slate-500">Functions</div>
          <div className="mt-1 font-mono text-xl text-slate-100">
            {p?.functions_changed ?? 0} <span className="text-sm text-slate-400">changed</span>
            <span className="mx-2 text-slate-600">·</span>
            {p?.functions_skipped ?? skipped.length} <span className="text-sm text-slate-400">skipped</span>
          </div>
          <div className="mt-1 text-[11px] text-slate-500">
            {p?.measured_count ?? 0} of {p?.functions_changed ?? 0} changed functions measured
            <span className="mx-1 text-slate-600">·</span>
            {p?.function_total ?? 0} in file
          </div>
          <div className="mt-1 text-[11px] text-slate-500">
            {applied.length} rewrites applied, {inconclusive.length} inconclusive, {rejected.length} reverted
          </div>
        </div>
        <div className="rounded-xl border border-slate-800 bg-gradient-to-br from-slate-900 to-[#0b1120] p-4">
          <div className="text-[10px] uppercase tracking-wider text-slate-500">Best changed function</div>
          {best ? (
            <>
              <div className="mt-1 font-mono text-xl text-emerald-300">{fmtRatio(best.ratio)}</div>
              <div className="mt-1 text-[11px] text-slate-500">
                <span className="font-mono text-slate-300">{best.name}</span>: {fmtMs(best.orig_ms)} → {fmtMs(best.opt_ms)} at n={fmtN(best.n)}
              </div>
            </>
          ) : (
            <>
              <div className="mt-1 font-mono text-xl text-slate-400">{identical ? "unchanged" : "no measurable change"}</div>
              <div className="mt-1 text-[11px] text-slate-500">{identical ? "no function was rewritten" : "no changed function showed a speed-up above the noise floor"}</div>
            </>
          )}
        </div>
        <div className="rounded-xl border border-slate-800 bg-gradient-to-br from-slate-900 to-[#0b1120] p-4">
          <div className="text-[10px] uppercase tracking-wider text-slate-500">Are the timings trustworthy?</div>
          <div className={`mt-1 font-mono text-xl ${trustworthy == null ? "text-slate-400" : trustworthy ? "text-emerald-300" : "text-rose-300"}`}>
            {trustworthy == null ? "n/a" : trustworthy ? "yes" : "no"}
          </div>
          <div className="mt-1 text-[11px] text-slate-500">
            {control != null ? (
              <>
                A/A control <span className="font-mono text-slate-300">{(control * 100).toFixed(1)}%</span> (limit 5%) ·
                per function:{" "}
                {aaRange ? <span className="font-mono text-slate-300">{aaRange}</span> : "—"}
              </>
            ) : (
              p?.trust_reason ?? "not measured"
            )}
          </div>
          <div className="mt-1 text-[11px] text-slate-500">
            {claimedCount} of {perFn.length} measured functions pass their own threshold
            {perFn.length > 0 && (
              <span className="text-slate-600"> ({perFn.filter((x) => x.claimed).map((x) => x.name).join(", ") || "none"})</span>
            )}
          </div>
        </div>
      </div>

      {(origErr || optErr) && (
        <div className="rounded-xl border border-rose-500/40 bg-rose-500/10 p-3 text-xs text-rose-100">
          <b>Runtime error</b>
          {origErr && (
            <div className="mt-1">
              <span className="text-slate-300">original:</span> <span className="font-mono">{origErr}</span>
            </div>
          )}
          {optErr && (
            <div className="mt-1">
              <span className="text-slate-300">optimized:</span> <span className="font-mono">{optErr}</span>
            </div>
          )}
        </div>
      )}

      {(r.warnings ?? []).length > 0 && (
        <ul className="space-y-1 rounded-xl border border-amber-500/20 bg-amber-500/5 px-4 py-2 text-xs text-amber-200/90">
          {(r.warnings ?? []).map((w, i) => (
            <li key={i}>⚠ {w}</li>
          ))}
        </ul>
      )}
      {(r.infos ?? []).length > 0 && (
        <ul className="space-y-1 rounded-xl border border-slate-700/60 bg-slate-900/40 px-4 py-2 text-xs text-slate-300">
          {(r.infos ?? []).map((w, i) => (
            <li key={i}>ℹ {w}</li>
          ))}
        </ul>
      )}

      <div className="flex flex-wrap items-center gap-2 border-b border-slate-800 pb-2 text-xs">
        {btn("report", "🧾 Report")}
        {btn("overview", "📊 Overview & growth")}
        {btn("transforms", `⚡ Transformations (${changes.length})`)}
        {btn("skipped", `⏭ Skipped (${skipped.length})`)}
        {btn("rules", "🧰 Rule library")}
        {btn("code", "💻 Code")}
      </div>

      {tab === "report" && (
        <section className="space-y-3">
          <ReportTable rows={report} />
          <div className="rounded-xl border border-slate-800 bg-slate-900/40 px-4 py-2 text-xs text-slate-300">
            <b>Verification:</b>{" "}
            {applied.length === 0
              ? "no rewrite was kept, so nothing needed verifying."
              : `every kept rewrite passed ≥ ${p?.normal_runs_min ?? "?"} normal runs (strict return/argument/stdout/globals equality); ` +
                `${p?.normal_runs_total ?? 0} normal runs and ${p?.both_raised_total ?? 0} both-raised runs in total.`}{" "}
            <span className="text-slate-500">Randomised differential testing is evidence, not proof.</span>
            {p?.converged != null && <div className="mt-1 text-slate-400">Converged: {p.converged ? "yes — feeding the output back fires 0 rewrites" : "no — some rule would still fire on the output"}</div>}
          </div>
          {r.program && (
            <div className="rounded-xl border border-slate-800 bg-slate-900/40 px-4 py-2 text-xs text-slate-300">
              <b>Program (same stdin):</b> {r.program.message}
              {r.program.shown && r.program.orig_ms != null && r.program.opt_ms != null
                ? ` — ${fmtMs(r.program.orig_ms)} → ${fmtMs(r.program.opt_ms)} (median of 5 alternating runs)`
                : r.program.status === "ok"
                  ? " — under 0.5 ms, not reported"
                  : ""}
            </div>
          )}
        </section>
      )}

      {tab === "overview" && (
        <div className="space-y-4">
          <div className="grid gap-4 lg:grid-cols-2">
            <VariantCard title="Original" v={r.original} accent="border-rose-500/30" />
            <VariantCard title={identical ? "Optimized (identical)" : "Optimized"} v={r.optimized} accent="border-emerald-500/30" />
          </div>
          <div className="grid gap-4 lg:grid-cols-5">
            <div className="lg:col-span-3">
              <GrowthChart
                original={r.original?.bench?.points ?? []}
                optimized={identical ? [] : r.optimized?.bench?.points ?? []}
                fnName={r.target_function ?? null}
              />
              <p className="mt-2 px-1 text-[11px] text-slate-500">
                {identical
                  ? "The code is unchanged, so there is nothing to compare."
                  : r.noise?.method ?? ""}
              </p>
            </div>
            <div className="overflow-auto rounded-xl border border-slate-700/70 bg-[#0b1120] lg:col-span-2">
              <table className="w-full text-left font-mono text-xs">
                <thead className="text-[10px] uppercase tracking-wider text-slate-500">
                  <tr>
                    <th className="px-3 py-2 font-medium">function</th>
                    <th className="px-3 py-2 font-medium">original</th>
                    <th className="px-3 py-2 font-medium">optimized</th>
                    <th className="px-3 py-2 font-medium">ratio</th>
                  </tr>
                </thead>
                <tbody>
                  {perFn.map((x) => (
                    <tr key={x.name} className="border-t border-slate-800/80">
                      <td className="px-3 py-1.5 text-slate-300">{x.name}</td>
                      <td className="px-3 py-1.5 text-rose-200">{fmtMs(x.orig_ms)}</td>
                      <td className="px-3 py-1.5 text-emerald-200">{fmtMs(x.opt_ms)}</td>
                      <td className={`px-3 py-1.5 ${x.claimed ? "text-emerald-300" : "text-slate-500"}`}>{fmtRatio(x.ratio)}</td>
                    </tr>
                  ))}
                  {perFn.length === 0 && (
                    <tr>
                      <td colSpan={4} className="px-3 py-6 text-center font-sans text-slate-500">
                        {identical ? "No function was changed." : "No changed function could be measured."}
                      </td>
                    </tr>
                  )}
                </tbody>
              </table>
            </div>
          </div>
        </div>
      )}

      {tab === "transforms" && (
        <section className="space-y-2">
          <p className="text-xs text-slate-400">
            A rewrite is kept only if it compiles, is strictly equal to the previous version on ≥ 40 normal runs, and is not measurably slower.
            <span className="ml-2 text-amber-200/80">“Inconclusive”</span> means fewer than 40 normal runs could be generated; that rewrite alone is not applied.
          </p>
          {changes.length === 0 ? (
            <div className="rounded-lg border border-slate-800 bg-slate-900/40 p-4 text-sm text-slate-400">No rule matched this code.</div>
          ) : (
            changes.map((c, i) => <ChangeItem key={i} c={c} />)
          )}
          {(r.optimizer_notes ?? []).length > 0 && (
            <pre className="whitespace-pre-wrap rounded bg-slate-900/60 p-2 font-mono text-[10px] text-slate-500">{(r.optimizer_notes ?? []).join("\n")}</pre>
          )}
        </section>
      )}

      {tab === "skipped" && (
        <section className="space-y-2">
          {skipped.length === 0 ? (
            <div className="rounded-lg border border-slate-800 bg-slate-900/40 p-4 text-sm text-slate-400">No rule was skipped.</div>
          ) : (
            skipped.map((x, i) => (
              <div key={i} className="rounded-lg border border-amber-500/20 bg-amber-500/5 px-3 py-2 text-xs text-amber-100/90">
                <span className="font-mono text-amber-300">{x.rule}</span> on <span className="font-mono">{x.function}</span> — {x.reason}
              </div>
            ))
          )}
        </section>
      )}

      {tab === "rules" && (
        <section className="space-y-4">
          <div className="rounded-xl border border-slate-800 bg-[#0b1120] p-4">
            {(["algorithm", "idiom", "advisory"] as const).map((layer) => (
              <div key={layer} className="mb-3">
                <div className="mb-1 text-[10px] uppercase tracking-wider text-sky-300/80">
                  {layer === "algorithm" ? "Algorithmic" : layer === "idiom" ? "Idiom & cleanup" : "Advice (never auto-applied)"}
                </div>
                {(r.rules ?? []).filter((x) => x.layer === layer).map((x) => (
                  <RuleRow key={x.id} r={x} />
                ))}
              </div>
            ))}
          </div>
          <div className="rounded-xl border border-slate-800 bg-[#0b1120] p-4">
            <h4 className="mb-2 text-xs font-semibold uppercase tracking-wider text-slate-400">Verification size policy (integer inputs, by static class of the original)</h4>
            <table className="w-full text-left text-xs">
              <tbody>
                {(r.verification_policy ?? []).map((x) => (
                  <tr key={x.class} className="border-t border-slate-800/80 first:border-t-0">
                    <td className="py-1.5 pr-4 font-mono text-slate-300">{x.class}</td>
                    <td className="py-1.5 font-mono text-emerald-300">{x.cap}</td>
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
          <div className="rounded-xl border border-amber-500/20 bg-amber-500/5 p-4">
            <h4 className="mb-2 text-xs font-semibold uppercase tracking-wider text-amber-300">Known gaps</h4>
            <ul className="list-disc space-y-1 pl-5 text-xs text-amber-100/80">
              {(r.known_gaps ?? []).map((g, i) => (
                <li key={i}>{g}</li>
              ))}
            </ul>
          </div>
        </section>
      )}

      {tab === "code" && (
        <section className="space-y-3">
          <div className="flex items-center justify-between">
            <div className="flex rounded-lg border border-slate-700 p-0.5 text-xs">
              {(
                [
                  ["diff", "Diff"],
                  ["pure", "Optimized code"],
                  ...(r.contest_template ? [["template", "Contest scaffold (unverified)"] as const] : []),
                ] as const
              ).map(([k, label]) => (
                <button key={k} onClick={() => setCodeTab(k)} className={`rounded-md px-3 py-1 ${codeTab === k ? "bg-slate-700 text-white" : "text-slate-400 hover:text-slate-200"}`}>
                  {label}
                </button>
              ))}
            </div>
            <button onClick={copy} className="rounded-lg border border-slate-700 bg-slate-800 px-3 py-1 text-xs text-slate-200 hover:bg-slate-700">
              {copied ? "Copied ✓" : "Copy"}
            </button>
          </div>
          {codeTab === "diff" ? (
            identical ? (
              <div className="rounded-lg border border-slate-800 bg-slate-900/40 p-4 text-sm text-slate-400">The optimized code is identical to the input — no diff.</div>
            ) : (
              <DiffView before={r.original?.code ?? ""} after={r.optimized?.code ?? ""} />
            )
          ) : (
            <CodeBlock code={activeCode} />
          )}
        </section>
      )}
    </div>
  );
}
