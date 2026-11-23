import { useEffect, useRef } from "react";
import type { LogEntry } from "../engine/types";

const STAGE_STYLE: Record<string, { dot: string; label: string }> = {
  start: { dot: "bg-slate-400", label: "INIT" },
  parse: { dot: "bg-sky-400", label: "PARSE" },
  static: { dot: "bg-violet-400", label: "STATIC" },
  run: { dot: "bg-amber-400", label: "RUN" },
  bench: { dot: "bg-cyan-400", label: "BENCH" },
  optimize: { dot: "bg-emerald-400", label: "OPT" },
  done: { dot: "bg-emerald-300", label: "DONE" },
  error: { dot: "bg-rose-400", label: "ERR" },
};

export function ProgressLog({ log, running }: { log: LogEntry[]; running: boolean }) {
  const endRef = useRef<HTMLDivElement>(null);
  useEffect(() => {
    endRef.current?.scrollIntoView({ block: "nearest" });
  }, [log.length]);

  return (
    <div className="flex h-56 flex-col overflow-hidden rounded-xl border border-slate-700/70 bg-[#0b1120]">
      <div className="flex items-center justify-between border-b border-slate-800 px-3 py-2 text-xs uppercase tracking-wider text-slate-400">
        <span>Live engine trace</span>
        <span className="flex items-center gap-2">
          {running && <span className="h-2 w-2 animate-pulse rounded-full bg-emerald-400" />}
          {log.length} events
        </span>
      </div>
      <div className="flex-1 overflow-auto p-2 font-mono text-[12px] leading-5">
        {log.length === 0 && (
          <div className="px-2 py-6 text-center text-slate-600">
            Events will stream here while the engine parses, benchmarks and rewrites your code.
          </div>
        )}
        {log.map((e) => {
          const s = STAGE_STYLE[e.stage] ?? STAGE_STYLE.start;
          return (
            <div key={e.id} className="flex items-start gap-2 px-2 py-0.5 hover:bg-slate-800/40">
              <span className="w-14 shrink-0 text-right text-slate-600">{(e.at / 1000).toFixed(2)}s</span>
              <span className={`mt-2 h-1.5 w-1.5 shrink-0 rounded-full ${s.dot}`} />
              <span className="w-12 shrink-0 text-[10px] font-semibold tracking-wider text-slate-500">{s.label}</span>
              <span className={e.stage === "error" ? "text-rose-300" : "text-slate-300"}>{e.message}</span>
            </div>
          );
        })}
        <div ref={endRef} />
      </div>
    </div>
  );
}
