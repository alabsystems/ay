// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//
// End-to-end proof that `ay_ffi.wasm` runs REAL solves under Node.
//
// This loads the wasm module (NOT a native dylib) and drives genuine solves
// through it, then checks the verdicts and models the solver returns. Run:
//
//   cargo build --release --target wasm32-unknown-unknown \
//       -p ay-ffi --lib --no-default-features
//   node bindings/js/test-wasm.mjs
//

import {
  loadAySolver,
  statusName,
  AY_SAT,
  AY_UNSAT,
  DEFAULT_WASM_PATH,
} from "./wasm.mjs";

let failures = 0;
function check(cond, msg) {
  if (cond) {
    console.log(`  PASS  ${msg}`);
  } else {
    console.log(`  FAIL  ${msg}`);
    failures++;
  }
}

const mod = await loadAySolver();
console.log(`Loaded wasm module: ${DEFAULT_WASM_PATH}`);
console.log(`AY version: ${readVersion(mod)}\n`);

function readVersion(m) {
  if (typeof m.exports.ay_version !== "function") return "(no ay_version export)";
  const p = m.exports.ay_version();
  const s = m._readCString(p);
  m.exports.ay_string_free(p);
  return s;
}

// ---------------------------------------------------------------------------
// Case 1: SAT with a model.  x > 3 AND x < 6  =>  sat, x in {4, 5}
// ---------------------------------------------------------------------------
console.log("Case 1: (> x 3) AND (< x 6)  [expect SAT, x in {4,5}]");
{
  const smt =
    "(set-logic QF_LIA)" +
    "(declare-const x Int)" +
    "(assert (> x 3))" +
    "(assert (< x 6))" +
    "(check-sat)";
  const { status, model } = mod.solve(smt);
  console.log(`  status = ${statusName(status)}`);
  console.log(`  model  = ${JSON.stringify(model)}`);
  check(status === AY_SAT, "verdict is SAT");

  // Extract x's value from the model text and confirm it satisfies 3 < x < 6.
  const m = model && model.match(/x[^-\d]*(-?\d+)/);
  const xVal = m ? Number(m[1]) : NaN;
  check(
    Number.isFinite(xVal) && xVal > 3 && xVal < 6,
    `model assigns x = ${xVal} with 3 < x < 6 (x in {4,5})`,
  );
}

// ---------------------------------------------------------------------------
// Case 2: UNSAT.  x > 5 AND x < 3  =>  unsat
// ---------------------------------------------------------------------------
console.log("\nCase 2: (> x 5) AND (< x 3)  [expect UNSAT]");
{
  const smt =
    "(set-logic QF_LIA)" +
    "(declare-const x Int)" +
    "(assert (> x 5))" +
    "(assert (< x 3))" +
    "(check-sat)";
  const { status } = mod.solve(smt);
  console.log(`  status = ${statusName(status)}`);
  check(status === AY_UNSAT, "verdict is UNSAT");
}

// ---------------------------------------------------------------------------
// Case 3: Boolean UNSAT.  p AND (not p)  =>  unsat
// ---------------------------------------------------------------------------
console.log("\nCase 3: p AND (not p)  [expect UNSAT]");
{
  const smt =
    "(set-logic QF_UF)" +
    "(declare-const p Bool)" +
    "(assert p)" +
    "(assert (not p))" +
    "(check-sat)";
  const { status } = mod.solve(smt);
  console.log(`  status = ${statusName(status)}`);
  check(status === AY_UNSAT, "verdict is UNSAT");
}

// ---------------------------------------------------------------------------
// Case 4: SAT equality.  y + 2 = 10  =>  sat, y = 8
// ---------------------------------------------------------------------------
console.log("\nCase 4: (= (+ y 2) 10)  [expect SAT, y = 8]");
{
  const smt =
    "(set-logic QF_LIA)" +
    "(declare-const y Int)" +
    "(assert (= (+ y 2) 10))" +
    "(check-sat)";
  const { status, model } = mod.solve(smt);
  console.log(`  status = ${statusName(status)}`);
  console.log(`  model  = ${JSON.stringify(model)}`);
  check(status === AY_SAT, "verdict is SAT");
  const m = model && model.match(/y[^-\d]*(-?\d+)/);
  const yVal = m ? Number(m[1]) : NaN;
  check(yVal === 8, `model assigns y = ${yVal} (expected 8)`);
}

console.log(
  `\n${failures === 0 ? "ALL PASS" : `${failures} FAILURE(S)`} — real solves executed by ay_ffi.wasm`,
);
process.exit(failures === 0 ? 0 : 1);
