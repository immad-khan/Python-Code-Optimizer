import type { ReactNode } from "react";

const KEYWORDS = new Set([
  "False", "None", "True", "and", "as", "assert", "async", "await", "break", "class", "continue",
  "def", "del", "elif", "else", "except", "finally", "for", "from", "global", "if", "import", "in",
  "is", "lambda", "nonlocal", "not", "or", "pass", "raise", "return", "try", "while", "with", "yield",
]);
const BUILTINS = new Set([
  "print", "len", "range", "enumerate", "zip", "sorted", "sum", "max", "min", "set", "dict", "list",
  "tuple", "str", "int", "float", "bool", "any", "all", "map", "filter", "abs", "isinstance", "reversed",
  "input", "open", "type", "iter", "next", "round", "divmod", "pow", "hash", "id", "ord", "chr", "super",
  "self", "object", "Exception", "ValueError", "TypeError", "KeyError", "IndexError",
]);

const TOKEN_RE =
  /(#[^\n]*)|("""[\s\S]*?"""|'''[\s\S]*?'''|"(?:\\.|[^"\\\n])*"|'(?:\\.|[^'\\\n])*')|(\b\d+(?:\.\d+)?(?:e[+-]?\d+)?\b)|(@\w+(?:\.\w+)*)|(\b[A-Za-z_]\w*\b)|(\s+)|(.)/g;

export function highlightPython(code: string): ReactNode[] {
  const out: ReactNode[] = [];
  let m: RegExpExecArray | null;
  let i = 0;
  TOKEN_RE.lastIndex = 0;
  while ((m = TOKEN_RE.exec(code)) !== null) {
    const [tok, comment, str, num, deco, ident] = m;
    let cls = "";
    if (comment) cls = "text-slate-500 italic";
    else if (str) cls = "text-emerald-300";
    else if (num) cls = "text-amber-300";
    else if (deco) cls = "text-fuchsia-300";
    else if (ident) {
      if (KEYWORDS.has(ident)) cls = "text-sky-300 font-medium";
      else if (BUILTINS.has(ident)) cls = "text-violet-300";
      else {
        // function name after def
        const prev = code.slice(Math.max(0, m.index - 4), m.index);
        if (/def\s$/.test(prev)) cls = "text-yellow-200";
      }
    }
    out.push(
      cls ? (
        <span key={i++} className={cls}>
          {tok}
        </span>
      ) : (
        tok
      )
    );
  }
  return out;
}
