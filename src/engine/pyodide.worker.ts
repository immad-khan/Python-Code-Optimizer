/// <reference lib="webworker" />
import enginePart1 from "./engine_01_foundation.py?raw";
import enginePart2 from "./engine_02_runtime.py?raw";
import enginePart3 from "./engine_03_rules.py?raw";
import enginePart4 from "./engine_04_optimize.py?raw";
import enginePart5 from "./engine_05_pipeline.py?raw";
import type { WorkerIn, WorkerOut } from "./types";

const ENGINE_PARTS = [enginePart1, enginePart2, enginePart3, enginePart4, enginePart5];

const PYODIDE_VERSION = "0.26.4";
const PYODIDE_BASE = `https://cdn.jsdelivr.net/pyodide/v${PYODIDE_VERSION}/full/`;

// eslint-disable-next-line @typescript-eslint/no-explicit-any
let pyodide: any = null;
// eslint-disable-next-line @typescript-eslint/no-explicit-any
let loading: Promise<any> | null = null;

function post(msg: WorkerOut) {
  (self as unknown as Worker).postMessage(msg);
}

async function ensurePyodide() {
  if (pyodide) return pyodide;
  if (!loading) {
    loading = (async () => {
      post({ type: "status", message: "Downloading Python runtime (Pyodide / WebAssembly)…" });
      // Hide the import from the bundler – it must be resolved at runtime from the CDN.
      const dynamicImport = new Function("u", "return import(u)") as (u: string) => Promise<{
        // eslint-disable-next-line @typescript-eslint/no-explicit-any
        loadPyodide: (opts: { indexURL: string }) => Promise<any>;
      }>;
      const mod = await dynamicImport(PYODIDE_BASE + "pyodide.mjs");
      post({ type: "status", message: "Instantiating CPython 3.12 in WebAssembly…" });
      const py = await mod.loadPyodide({ indexURL: PYODIDE_BASE });
      post({ type: "status", message: "Loading analysis & optimization engine…" });
      py.globals.set("js_progress", (s: string) => {
        try {
          post({ type: "progress", data: JSON.parse(s) });
        } catch {
          /* ignore */
        }
      });
      for (const part of ENGINE_PARTS) {
        py.runPython(part);
      }
      pyodide = py;
      return py;
    })();
  }
  return loading;
}

self.onmessage = async (e: MessageEvent<WorkerIn>) => {
  const msg = e.data;
  try {
    if (msg.type === "init") {
      await ensurePyodide();
      post({ type: "ready" });
      return;
    }
    if (msg.type === "analyze") {
      const py = await ensurePyodide();
      const run = py.globals.get("run_pipeline");
      const json: string = run(msg.code, msg.stdin ?? "", msg.hints ?? "");
      run.destroy?.();
      const parsed: unknown = JSON.parse(json);
      if (!parsed || typeof parsed !== "object" || typeof (parsed as { ok?: unknown }).ok !== "boolean") {
        throw new Error("Engine returned an invalid result payload.");
      }
      post({ type: "result", id: msg.id, result: parsed as import("./types").PipelineResult });
    }
  } catch (err) {
    const message = err instanceof Error ? err.message : String(err);
    post({ type: "error", id: msg.type === "analyze" ? msg.id : undefined, message });
  }
};
