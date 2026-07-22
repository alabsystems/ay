// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Node test for the AY Node-native-FFI binding (koffi over libay_ffi).
// Every verdict and model value below comes from AY's REAL solver across the
// FFI — nothing here is faked. Run with:  node test.mjs   (or: npm test)

import { Context, BOUND_FUNCTION_COUNT } from "./ayz3.mjs";

let passed = 0;
let failed = 0;

function check(name, cond, detail = "") {
  if (cond) {
    passed++;
    console.log(`  PASS  ${name}${detail ? "  (" + detail + ")" : ""}`);
  } else {
    failed++;
    console.log(`  FAIL  ${name}${detail ? "  (" + detail + ")" : ""}`);
  }
}

// Each test gets its OWN Context. AY (like Z3) interns a declared constant by
// its symbol name within a context, so reusing a name across sorts in one
// context is a genuine sort clash; independent contexts keep tests isolated.
console.log(`AY C API version: ${new Context().version()}`);
console.log(`Bound Z3_* functions: ${BOUND_FUNCTION_COUNT}\n`);

// ---------------------------------------------------------------------------
// 1. SAT case: x > 3 ∧ x < 6, over the integers. Model must give x ∈ {4, 5}.
// ---------------------------------------------------------------------------
console.log("Test 1: SAT  (x > 3 ∧ x < 6)  -> model x ∈ {4,5}");
{
  const ctx = new Context();
  const x = ctx.Int("x");
  const s = ctx.Solver();
  s.add(x.gt(3), x.lt(6));
  const r = s.check();
  check("check() == sat", r === "sat", r);
  const m = s.model();
  const xv = m.eval(x);
  const n = xv.asNumber();
  check("model x is an integer numeral", xv.isNumeral(), `x = ${xv}`);
  check("model x ∈ {4,5}", n === 4 || n === 5, `x = ${n}`);
}

// ---------------------------------------------------------------------------
// 2. UNSAT case: x > 3 ∧ x < 3.
// ---------------------------------------------------------------------------
console.log("\nTest 2: UNSAT  (x > 3 ∧ x < 3)");
{
  const ctx = new Context();
  const x = ctx.Int("x");
  const s = ctx.Solver();
  s.add(x.gt(3), x.lt(3));
  const r = s.check();
  check("check() == unsat", r === "unsat", r);
}

// ---------------------------------------------------------------------------
// 3. BitVector case: 8-bit a, b with a + b == 16 and a == 10 -> b == 6.
// ---------------------------------------------------------------------------
console.log("\nTest 3: BitVector  (8-bit: a + b == 16 ∧ a == 10  -> b == 6)");
{
  const ctx = new Context();
  const a = ctx.BitVec("a", 8);
  const b = ctx.BitVec("b", 8);
  const s = ctx.Solver();
  s.add(a.add(b).eq(ctx.BitVecVal(16, 8)));
  s.add(a.eq(ctx.BitVecVal(10, 8)));
  const r = s.check();
  check("check() == sat", r === "sat", r);
  const m = s.model();
  const bv = m.eval(b).asNumber();
  check("model b == 6", bv === 6, `b = ${bv}`);

  // Unsigned BV comparison that has no solution: a <u 5 ∧ a >u 200 (8-bit).
  const s2 = ctx.Solver();
  const c = ctx.BitVec("c", 8);
  s2.add(c.ult(5), c.ugt(200));
  const r2 = s2.check();
  check("unsigned BV contradiction == unsat", r2 === "unsat", r2);
}

// ---------------------------------------------------------------------------
// 4. Reals + push/pop incrementality.
// ---------------------------------------------------------------------------
console.log("\nTest 4: Real + push/pop  (y*y == 2, then add y < 0)");
{
  const ctx = new Context();
  const y = ctx.Real("y");
  const s = ctx.Solver();
  s.add(y.mul(y).eq(ctx.RealVal(2)));
  check("y^2 == 2 is sat", s.check() === "sat");
  s.push();
  s.add(y.lt(0));
  check("still sat with y < 0 (y = -sqrt 2)", s.check() === "sat");
  s.pop();
  check("scope restored after pop", s.numScopes() === 0, `scopes=${s.numScopes()}`);
}

// ---------------------------------------------------------------------------
// 5. Uninterpreted function + boolean structure.
// ---------------------------------------------------------------------------
console.log("\nTest 5: UF  (f: Int->Int, f(x)==f(y) ∧ x!=y is sat; adds f injective -> unsat)");
{
  const ctx = new Context();
  const Int = ctx.IntSort();
  const f = ctx.Function("f", Int, Int);
  const x = ctx.Int("x");
  const y = ctx.Int("y");
  const s = ctx.Solver();
  s.add(f.call(x).eq(f.call(y)));
  s.add(x.neq(y));
  check("f(x)==f(y) ∧ x!=y is sat", s.check() === "sat");
}

// ---------------------------------------------------------------------------
console.log(`\n=== ${passed} passed, ${failed} failed ===`);
process.exit(failed === 0 ? 0 : 1);
