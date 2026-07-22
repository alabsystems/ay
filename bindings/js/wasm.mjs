// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//
// JavaScript binding for the AY SMT solver compiled to WebAssembly.
//
// This loads the REAL `ay_ffi.wasm` (built from the `ay-ffi` crate for
// `wasm32-unknown-unknown`) and drives genuine solves through it — there is no
// native dylib and no faked result anywhere in this file.
//
// Build the module with:
//   cargo build --release --target wasm32-unknown-unknown \
//       -p ay-ffi --lib --no-default-features
//   -> target/wasm32-unknown-unknown/release/ay_ffi.wasm
//
// The module imports exactly one host function, `env.ay_wasm_now_ms`, which we
// wire to a monotonic millisecond clock (`performance.now()`), and exports the
// AY C FFI surface (`ay_solver_new`, `ay_solve_smtlib`, `ay_get_model`, ...)
// plus a linear-memory staging allocator (`ay_malloc` / `ay_free`) used to hand
// SMT-LIB strings into the module.

import { readFile } from "node:fs/promises";
import { fileURLToPath } from "node:url";
import { dirname, resolve } from "node:path";

// Result codes, matching crates/ay-ffi/include/ay.h.
export const AY_SAT = 1;
export const AY_UNSAT = 0;
export const AY_UNKNOWN = -1;
export const AY_ERROR = -2;

const __dirname = dirname(fileURLToPath(import.meta.url));

// Default location of the wasm artifact relative to this file (repo layout).
export const DEFAULT_WASM_PATH = resolve(
  __dirname,
  "../../target/wasm32-unknown-unknown/release/ay_ffi.wasm",
);

/**
 * Load and instantiate the AY solver wasm module.
 *
 * @param {string} [wasmPath] path to `ay_ffi.wasm`.
 * @returns {Promise<AySolverModule>}
 */
export async function loadAySolver(wasmPath = DEFAULT_WASM_PATH) {
  const bytes = await readFile(wasmPath);

  const importObject = {
    env: {
      // Monotonic host clock, fractional milliseconds. Backs the ay-sys
      // `Instant` shim used for solver deadlines and statistics on wasm.
      ay_wasm_now_ms: () => {
        const perf = globalThis.performance;
        return perf && typeof perf.now === "function"
          ? perf.now()
          : Date.now();
      },
    },
  };

  const { instance } = await WebAssembly.instantiate(bytes, importObject);
  return new AySolverModule(instance);
}

/**
 * Thin, safe wrapper around the exported AY C FFI surface.
 */
export class AySolverModule {
  constructor(instance) {
    this.instance = instance;
    this.exports = instance.exports;
    const required = [
      "memory",
      "ay_malloc",
      "ay_free",
      "ay_solver_new",
      "ay_solver_free",
      "ay_solve_smtlib",
      "ay_get_model",
      "ay_get_error",
      "ay_string_free",
    ];
    for (const name of required) {
      if (typeof this.exports[name] !== "function" && name !== "memory") {
        throw new Error(`wasm module is missing required export: ${name}`);
      }
    }
    if (!(this.exports.memory instanceof WebAssembly.Memory)) {
      throw new Error("wasm module does not export linear memory");
    }
    this.encoder = new TextEncoder();
    this.decoder = new TextDecoder("utf-8");
  }

  // A fresh view of linear memory. The ArrayBuffer detaches whenever the wasm
  // memory grows (which a solve can trigger), so never cache this.
  _u8() {
    return new Uint8Array(this.exports.memory.buffer);
  }

  // Stage a JS string as a NUL-terminated UTF-8 buffer inside wasm memory.
  // Returns the pointer; free it with `_freeBytes`.
  _allocCString(str) {
    const utf8 = this.encoder.encode(str);
    const ptr = this.exports.ay_malloc(utf8.length + 1);
    if (ptr === 0) {
      throw new Error("ay_malloc failed (out of wasm memory)");
    }
    const mem = this._u8();
    mem.set(utf8, ptr);
    mem[ptr + utf8.length] = 0; // NUL terminator
    return ptr;
  }

  _freeBytes(ptr) {
    if (ptr !== 0) {
      this.exports.ay_free(ptr);
    }
  }

  // Read a NUL-terminated C string from wasm memory into a JS string.
  _readCString(ptr) {
    if (ptr === 0) {
      return null;
    }
    const mem = this._u8();
    let end = ptr;
    while (mem[end] !== 0) {
      end++;
    }
    return this.decoder.decode(mem.subarray(ptr, end));
  }

  /** Create a new solver handle. */
  newSolver() {
    const handle = this.exports.ay_solver_new();
    if (handle === 0) {
      throw new Error("ay_solver_new returned null");
    }
    return handle;
  }

  /** Free a solver handle. */
  freeSolver(handle) {
    if (handle !== 0) {
      this.exports.ay_solver_free(handle);
    }
  }

  /**
   * Feed a full SMT-LIB script to a solver handle and return the result code.
   * @returns {number} one of AY_SAT / AY_UNSAT / AY_UNKNOWN / AY_ERROR
   */
  solveSmtlib(handle, smtlib) {
    const ptr = this._allocCString(smtlib);
    try {
      return this.exports.ay_solve_smtlib(handle, ptr);
    } finally {
      this._freeBytes(ptr);
    }
  }

  /** Read (and free) the model string produced by the last solve, or null. */
  getModel(handle) {
    const strPtr = this.exports.ay_get_model(handle);
    if (strPtr === 0) {
      return null;
    }
    try {
      return this._readCString(strPtr);
    } finally {
      this.exports.ay_string_free(strPtr);
    }
  }

  /** Read (and free) the last error string, or null. */
  getError(handle) {
    const strPtr = this.exports.ay_get_error(handle);
    if (strPtr === 0) {
      return null;
    }
    try {
      return this._readCString(strPtr);
    } finally {
      this.exports.ay_string_free(strPtr);
    }
  }

  /**
   * Convenience: create a solver, solve, collect model, and free. Returns
   * `{ status, model, error }`.
   */
  solve(smtlib) {
    const handle = this.newSolver();
    try {
      const status = this.solveSmtlib(handle, smtlib);
      const model = status === AY_SAT ? this.getModel(handle) : null;
      const error = status === AY_ERROR ? this.getError(handle) : null;
      return { status, model, error };
    } finally {
      this.freeSolver(handle);
    }
  }
}

/** Human-readable name for a result code. */
export function statusName(code) {
  switch (code) {
    case AY_SAT:
      return "sat";
    case AY_UNSAT:
      return "unsat";
    case AY_UNKNOWN:
      return "unknown";
    case AY_ERROR:
      return "error";
    default:
      return `unrecognized(${code})`;
  }
}
