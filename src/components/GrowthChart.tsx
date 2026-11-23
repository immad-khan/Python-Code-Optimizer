import type { BenchPoint } from "../engine/types";

interface Props {
  original: BenchPoint[];
  optimized: BenchPoint[];
  fnName: string | null;
}

function fmtMs(ms: number) {
  if (ms >= 1000) return (ms / 1000).toFixed(2) + " s";
  if (ms >= 1) return ms.toFixed(2) + " ms";
  if (ms >= 0.001) return (ms * 1000).toFixed(1) + " µs";
  return (ms * 1e6).toFixed(0) + " ns";
}

function fmtN(n: number) {
  if (n >= 1e6) return (n / 1e6).toFixed(1) + "M";
  if (n >= 1000) return (n / 1000).toFixed(n % 1000 === 0 ? 0 : 1) + "k";
  return String(n);
}

export function GrowthChart({ original, optimized, fnName }: Props) {
  const all = [...original, ...optimized].filter((p) => p.t_ms > 0 && p.n > 0);
  if (all.length < 2) {
    return (
      <div className="flex h-64 items-center justify-center rounded-xl border border-dashed border-slate-700 text-sm text-slate-500">
        Not enough benchmark points to draw a growth curve.
      </div>
    );
  }
  const W = 640, H = 280, padL = 64, padR = 20, padT = 16, padB = 40;
  const xs = all.map((p) => Math.log10(p.n));
  const ys = all.map((p) => Math.log10(p.t_ms));
  const xmin = Math.min(...xs), xmax = Math.max(...xs);
  const ymin = Math.floor(Math.min(...ys)), ymax = Math.ceil(Math.max(...ys));
  const sx = (n: number) => padL + ((Math.log10(n) - xmin) / Math.max(xmax - xmin, 1e-9)) * (W - padL - padR);
  const sy = (t: number) => padT + (1 - (Math.log10(t) - ymin) / Math.max(ymax - ymin, 1e-9)) * (H - padT - padB);

  const path = (pts: BenchPoint[]) =>
    pts
      .filter((p) => p.t_ms > 0)
      .map((p, i) => `${i === 0 ? "M" : "L"}${sx(p.n).toFixed(1)},${sy(p.t_ms).toFixed(1)}`)
      .join(" ");

  const yTicks: number[] = [];
  for (let e = ymin; e <= ymax; e++) yTicks.push(e);
  const xTickSet = new Set<number>();
  for (const p of all) xTickSet.add(p.n);
  let xTicks = [...xTickSet].sort((a, b) => a - b);
  if (xTicks.length > 8) {
    const step = Math.ceil(xTicks.length / 8);
    xTicks = xTicks.filter((_, i) => i % step === 0 || i === xTicks.length - 1);
  }

  return (
    <div className="rounded-xl border border-slate-700/70 bg-[#0b1120] p-3">
      <div className="mb-1 flex items-center justify-between px-1 text-xs text-slate-400">
        <span>
          Runtime vs input size{fnName ? ` — ${fnName}(n)` : ""} <span className="text-slate-600">(log–log)</span>
        </span>
        <span className="flex gap-4">
          <span className="flex items-center gap-1.5">
            <span className="h-0.5 w-4 bg-rose-400" /> original
          </span>
          <span className="flex items-center gap-1.5">
            <span className="h-0.5 w-4 bg-emerald-400" /> optimized
          </span>
        </span>
      </div>
      <svg viewBox={`0 0 ${W} ${H}`} className="h-auto w-full">
        {yTicks.map((e) => (
          <g key={e}>
            <line x1={padL} x2={W - padR} y1={sy(10 ** e)} y2={sy(10 ** e)} stroke="#1e293b" strokeDasharray="3 3" />
            <text x={padL - 8} y={sy(10 ** e) + 4} textAnchor="end" fontSize="10" fill="#64748b">
              {fmtMs(10 ** e)}
            </text>
          </g>
        ))}
        {xTicks.map((n) => (
          <g key={n}>
            <line x1={sx(n)} x2={sx(n)} y1={padT} y2={H - padB} stroke="#1e293b" strokeDasharray="3 3" />
            <text x={sx(n)} y={H - padB + 16} textAnchor="middle" fontSize="10" fill="#64748b">
              {fmtN(n)}
            </text>
          </g>
        ))}
        <text x={(W + padL) / 2} y={H - 6} textAnchor="middle" fontSize="10" fill="#475569">
          input size n
        </text>
        <path d={path(original)} fill="none" stroke="#fb7185" strokeWidth="2" />
        <path d={path(optimized)} fill="none" stroke="#34d399" strokeWidth="2" />
        {original.filter((p) => p.t_ms > 0).map((p) => (
          <circle key={"o" + p.n} cx={sx(p.n)} cy={sy(p.t_ms)} r="3" fill="#fb7185">
            <title>{`original n=${p.n}: ${fmtMs(p.t_ms)}`}</title>
          </circle>
        ))}
        {optimized.filter((p) => p.t_ms > 0).map((p) => (
          <circle key={"p" + p.n} cx={sx(p.n)} cy={sy(p.t_ms)} r="3" fill="#34d399">
            <title>{`optimized n=${p.n}: ${fmtMs(p.t_ms)}`}</title>
          </circle>
        ))}
      </svg>
    </div>
  );
}

export { fmtMs, fmtN };
