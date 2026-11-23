import { useMemo } from "react";
import { highlightPython } from "./highlight";

type Op = { type: "same" | "add" | "del"; text: string; a?: number; b?: number };

function diffLines(a: string[], b: string[]): Op[] {
  const n = a.length, m = b.length;
  // LCS table
  const dp: Uint32Array[] = Array.from({ length: n + 1 }, () => new Uint32Array(m + 1));
  for (let i = n - 1; i >= 0; i--) {
    for (let j = m - 1; j >= 0; j--) {
      dp[i][j] = a[i] === b[j] ? dp[i + 1][j + 1] + 1 : Math.max(dp[i + 1][j], dp[i][j + 1]);
    }
  }
  const ops: Op[] = [];
  let i = 0, j = 0;
  while (i < n && j < m) {
    if (a[i] === b[j]) {
      ops.push({ type: "same", text: a[i], a: i + 1, b: j + 1 });
      i++; j++;
    } else if (dp[i + 1][j] >= dp[i][j + 1]) {
      ops.push({ type: "del", text: a[i], a: i + 1 });
      i++;
    } else {
      ops.push({ type: "add", text: b[j], b: j + 1 });
      j++;
    }
  }
  while (i < n) ops.push({ type: "del", text: a[i], a: ++i });
  while (j < m) ops.push({ type: "add", text: b[j], b: ++j });
  return ops;
}

export function DiffView({ before, after }: { before: string; after: string }) {
  const ops = useMemo(() => diffLines(before.split("\n"), after.split("\n")), [before, after]);
  return (
    <div className="overflow-auto rounded-xl border border-slate-700/70 bg-[#0b1120] font-mono text-[12.5px] leading-6">
      {ops.map((op, idx) => {
        const bg =
          op.type === "add" ? "bg-emerald-500/15" : op.type === "del" ? "bg-rose-500/15" : "";
        const sign = op.type === "add" ? "+" : op.type === "del" ? "−" : " ";
        const signColor = op.type === "add" ? "text-emerald-400" : op.type === "del" ? "text-rose-400" : "text-slate-700";
        return (
          <div key={idx} className={`flex ${bg}`}>
            <span className="w-10 shrink-0 select-none border-r border-slate-800 pr-2 text-right text-slate-600">{op.a ?? ""}</span>
            <span className="w-10 shrink-0 select-none border-r border-slate-800 pr-2 text-right text-slate-600">{op.b ?? ""}</span>
            <span className={`w-6 shrink-0 select-none text-center ${signColor}`}>{sign}</span>
            <pre className={`m-0 flex-1 whitespace-pre pr-4 ${op.type === "del" ? "text-slate-400 line-through decoration-rose-500/40" : "text-slate-200"}`}>
              {highlightPython(op.text || " ")}
            </pre>
          </div>
        );
      })}
    </div>
  );
}
