import { useMemo, useRef } from "react";
import { highlightPython } from "./highlight";

interface Props {
  value: string;
  onChange: (v: string) => void;
  onRun?: () => void;
  placeholder?: string;
  minHeight?: number;
}

export function CodeEditor({ value, onChange, onRun, placeholder, minHeight = 360 }: Props) {
  const preRef = useRef<HTMLPreElement>(null);
  const gutterRef = useRef<HTMLDivElement>(null);
  const lines = useMemo(() => value.split("\n").length, [value]);
  const highlighted = useMemo(() => highlightPython(value + (value.endsWith("\n") ? " " : "")), [value]);

  const sync = (el: HTMLTextAreaElement) => {
    if (preRef.current) {
      preRef.current.scrollTop = el.scrollTop;
      preRef.current.scrollLeft = el.scrollLeft;
    }
    if (gutterRef.current) gutterRef.current.scrollTop = el.scrollTop;
  };

  const onKeyDown = (e: React.KeyboardEvent<HTMLTextAreaElement>) => {
    const ta = e.currentTarget;
    if ((e.ctrlKey || e.metaKey) && e.key === "Enter") {
      e.preventDefault();
      onRun?.();
      return;
    }
    if (e.key === "Tab") {
      e.preventDefault();
      const start = ta.selectionStart;
      const end = ta.selectionEnd;
      const next = value.slice(0, start) + "    " + value.slice(end);
      onChange(next);
      requestAnimationFrame(() => {
        ta.selectionStart = ta.selectionEnd = start + 4;
      });
      return;
    }
    if (e.key === "Enter") {
      // keep indentation, add one level after ':'
      const start = ta.selectionStart;
      const before = value.slice(0, start);
      const lineStart = before.lastIndexOf("\n") + 1;
      const line = before.slice(lineStart);
      const indent = (line.match(/^\s*/) ?? [""])[0];
      const extra = line.trimEnd().endsWith(":") ? "    " : "";
      e.preventDefault();
      const insert = "\n" + indent + extra;
      const next = before + insert + value.slice(ta.selectionEnd);
      onChange(next);
      requestAnimationFrame(() => {
        ta.selectionStart = ta.selectionEnd = start + insert.length;
      });
    }
  };

  return (
    <div
      className="relative flex overflow-hidden rounded-xl border border-slate-700/70 bg-[#0b1120] font-mono text-[13px] leading-6 shadow-inner shadow-black/40"
      style={{ minHeight }}
    >
      <div
        ref={gutterRef}
        className="select-none overflow-hidden border-r border-slate-800 bg-[#0a0f1c] px-3 py-3 text-right text-slate-600"
        aria-hidden
      >
        {Array.from({ length: lines }, (_, i) => (
          <div key={i}>{i + 1}</div>
        ))}
      </div>
      <div className="relative flex-1">
        <pre
          ref={preRef}
          aria-hidden
          className="pointer-events-none absolute inset-0 m-0 overflow-hidden whitespace-pre px-4 py-3 text-slate-200"
        >
          {value ? highlighted : <span className="text-slate-600">{placeholder}</span>}
        </pre>
        <textarea
          value={value}
          onChange={(e) => onChange(e.target.value)}
          onScroll={(e) => sync(e.currentTarget)}
          onKeyDown={onKeyDown}
          spellCheck={false}
          autoCapitalize="off"
          autoCorrect="off"
          className="absolute inset-0 h-full w-full resize-none overflow-auto whitespace-pre bg-transparent px-4 py-3 text-transparent caret-sky-300 outline-none selection:bg-sky-500/30"
          style={{ minHeight }}
        />
      </div>
    </div>
  );
}

export function CodeBlock({ code, className = "" }: { code: string; className?: string }) {
  const nodes = useMemo(() => highlightPython(code), [code]);
  const lines = code.split("\n").length;
  return (
    <div
      className={`flex overflow-auto rounded-xl border border-slate-700/70 bg-[#0b1120] font-mono text-[12.5px] leading-6 ${className}`}
    >
      <div className="select-none border-r border-slate-800 bg-[#0a0f1c] px-3 py-3 text-right text-slate-600" aria-hidden>
        {Array.from({ length: lines }, (_, i) => (
          <div key={i}>{i + 1}</div>
        ))}
      </div>
      <pre className="m-0 flex-1 whitespace-pre px-4 py-3 text-slate-200">{nodes}</pre>
    </div>
  );
}
