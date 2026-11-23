import { useCallback, useEffect, useRef, useState } from "react";
import EngineWorker from "./pyodide.worker?worker&inline";
import type { EngineStatus, LogEntry, PipelineResult, WorkerOut } from "./types";

const ANALYSIS_TIMEOUT_MS = 150_000;

export function useOptimizer() {
  const workerRef = useRef<Worker | null>(null);
  const idRef = useRef(0);
  const startRef = useRef(0);
  const timeoutRef = useRef<number | null>(null);
  const logIdRef = useRef(0);
  const spawnRef = useRef<(() => void) | null>(null);

  const [status, setStatus] = useState<EngineStatus>("booting");
  const [statusMessage, setStatusMessage] = useState("Starting engine…");
  const [log, setLog] = useState<LogEntry[]>([]);
  const [result, setResult] = useState<PipelineResult | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [elapsed, setElapsed] = useState(0);

  const pushLog = useCallback((stage: string, message: string, payload?: unknown) => {
    setLog((prev) => [
      ...prev,
      { id: ++logIdRef.current, stage, message, payload, at: performance.now() - startRef.current },
    ]);
  }, []);

  const clearTimer = () => {
    if (timeoutRef.current) {
      window.clearTimeout(timeoutRef.current);
      timeoutRef.current = null;
    }
  };

  const spawn = useCallback(() => {
    if (workerRef.current) workerRef.current.terminate();
    const w = new EngineWorker();
    workerRef.current = w;
    setStatus("booting");
    w.onmessage = (e: MessageEvent<WorkerOut>) => {
      const m = e.data;
      switch (m.type) {
        case "status":
          setStatusMessage(m.message);
          break;
        case "ready":
          setStatus("ready");
          setStatusMessage("Engine ready — CPython 3.12 (WebAssembly)");
          break;
        case "progress":
          pushLog(m.data.stage, m.data.message, m.data.payload);
          break;
        case "result":
          clearTimer();
          setResult(m.result);
          if (!m.result.ok) setError(m.result.error ?? "Unknown error");
          setStatus("ready");
          setElapsed(performance.now() - startRef.current);
          pushLog("done", `Finished in ${(m.result.elapsed_ms / 1000).toFixed(2)} s (engine time)`);
          break;
        case "error": {
          clearTimer();
          const fatal = /fatal|call stack|out of memory|Aborted/i.test(m.message);
          setError(
            fatal
              ? `The Python interpreter crashed (${m.message.slice(0, 160)}). This usually means very deep recursion or memory exhaustion. The engine has been restarted.`
              : m.message
          );
          pushLog("error", m.message);
          if (fatal) {
            setTimeout(() => spawnRef.current?.(), 0);
          } else {
            setStatus("ready");
          }
          break;
        }
      }
    };
    w.onerror = (ev) => {
      setError(ev.message || "Worker crashed");
      setStatus("error");
    };
    w.postMessage({ type: "init" });
  }, [pushLog]);

  spawnRef.current = spawn;

  useEffect(() => {
    spawn();
    return () => workerRef.current?.terminate();
  }, [spawn]);

  // live elapsed timer while running
  useEffect(() => {
    if (status !== "running") return;
    const t = window.setInterval(() => setElapsed(performance.now() - startRef.current), 100);
    return () => window.clearInterval(t);
  }, [status]);

  const analyze = useCallback(
    (code: string, hints = "", stdin = "") => {
      if (!workerRef.current || status === "running") return;
      const id = ++idRef.current;
      startRef.current = performance.now();
      setLog([]);
      setResult(null);
      setError(null);
      setElapsed(0);
      setStatus("running");
      pushLog("start", "Sending code to the engine…");
      workerRef.current.postMessage({ type: "analyze", id, code, hints, stdin });
      clearTimer();
      timeoutRef.current = window.setTimeout(() => {
        setError(
          `Analysis exceeded ${ANALYSIS_TIMEOUT_MS / 1000}s — the code probably contains a very long or infinite loop. The engine was restarted.`
        );
        pushLog("error", "Timeout — engine restarted");
        spawn();
      }, ANALYSIS_TIMEOUT_MS);
    },
    [pushLog, spawn, status]
  );

  const cancel = useCallback(() => {
    clearTimer();
    pushLog("error", "Cancelled by user — engine restarting");
    setError("Cancelled.");
    spawn();
  }, [pushLog, spawn]);

  return { status, statusMessage, log, result, error, elapsed, analyze, cancel };
}
