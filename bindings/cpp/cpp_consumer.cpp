// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// C++ smoke test for the header-only ay.hpp wrapper over AY's Z3-shaped C
// API. Builds tiny QF_LIA / QF_UF / QF_BV problems through the C++ wrapper,
// checks satisfiability, and asserts the verdicts (cross-checked against z3).
//
// If this compiles, links against libay_ffi, and exits 0, the C++ wrapper is
// sound and usable by C++ consumers.

#include "ay.hpp"

#include <cassert>
#include <cstdint>
#include <cstdio>

using namespace ay;

// QF_LIA SAT: 0 < x < 10 AND x == 7 -> SAT, model gives x == 7.
static void test_lia_sat() {
  context c;
  expr x = c.int_const("x");
  solver s(c);
  s.add(x > c.int_val(0));
  s.add(x < c.int_val(10));
  s.add(x == c.int_val(7));

  assert(s.check() == sat);

  model m = s.get_model();
  assert(m.valid());
  expr xv = m.eval(x);
  int64_t v = 0;
  bool ok = xv.as_int64(&v);
  assert(ok);
  assert(v == 7);
}

// QF_LIA UNSAT: x > 5 AND x < 3 -> UNSAT.
static void test_lia_unsat() {
  context c;
  expr x = c.int_const("x");
  solver s(c);
  s.add(x > c.int_val(5));
  s.add(x < c.int_val(3));
  assert(s.check() == unsat);
}

// QF_LIA via operator combinators: (x + y == 10) && (x - y == 4) -> x=7,y=3.
static void test_lia_arith() {
  context c;
  expr x = c.int_const("x");
  expr y = c.int_const("y");
  solver s(c);
  s.add((x + y == c.int_val(10)) && (x - y == c.int_val(4)));
  assert(s.check() == sat);

  model m = s.get_model();
  int64_t vx = 0, vy = 0;
  assert(m.eval(x).as_int64(&vx));
  assert(m.eval(y).as_int64(&vy));
  assert(vx == 7);
  assert(vy == 3);
}

// QF_UF SAT: uninterpreted f over sort U; f(a) == f(b) is satisfiable.
static void test_uf_sat() {
  context c;
  sort u = c.uninterpreted_sort("U");
  expr a = c.constant("a", u);
  expr b = c.constant("b", u);
  func_decl f = c.function("f", {u}, u);

  solver s(c);
  s.add(f(a) == f(b));
  assert(s.check() == sat);
}

// QF_UF UNSAT (congruence): a == b but f(a) != f(b) -> UNSAT.
static void test_uf_unsat_congruence() {
  context c;
  sort u = c.uninterpreted_sort("U");
  expr a = c.constant("a", u);
  expr b = c.constant("b", u);
  func_decl f = c.function("f", {u}, u);

  solver s(c);
  s.add(a == b);
  s.add(f(a) != f(b));
  assert(s.check() == unsat);  // congruence: a=b => f(a)=f(b)
}

// Boolean: (p || q) && !p -> SAT with q true.
static void test_bool() {
  context c;
  expr p = c.bool_const("p");
  expr q = c.bool_const("q");
  solver s(c);
  s.add((p || q) && !p);
  assert(s.check() == sat);

  model m = s.get_model();
  assert(m.eval(q).bool_value() == Z3_L_TRUE);
  assert(m.eval(p).bool_value() == Z3_L_FALSE);
}

// Boolean UNSAT: p && !p -> UNSAT.
static void test_bool_unsat() {
  context c;
  expr p = c.bool_const("p");
  solver s(c);
  s.add(p && !p);
  assert(s.check() == unsat);
}

// QF_BV SAT: 8-bit a & 0x0F == 0x0F is satisfiable.
static void test_bv() {
  context c;
  expr a = c.bv_const("a", 8);
  expr mask = c.bv_val(0x0F, 8);
  solver s(c);
  s.add((a & mask) == mask);
  assert(s.check() == sat);
}

// Push/pop incremental: assert x>0 (SAT), push, assert x<0 (UNSAT), pop, SAT.
static void test_push_pop() {
  context c;
  expr x = c.int_const("x");
  solver s(c);
  s.add(x > c.int_val(0));
  assert(s.check() == sat);

  s.push();
  s.add(x < c.int_val(0));
  assert(s.check() == unsat);
  s.pop();

  assert(s.check() == sat);
}

// Array: select(store(arr, i, v), i) == v is valid -> its negation is UNSAT.
static void test_array() {
  context c;
  sort is = c.int_sort();
  sort arr_s = c.array_sort(is, is);
  expr arr = c.constant("arr", arr_s);
  expr i = c.int_const("i");
  expr v = c.int_const("v");

  solver s(c);
  s.add(select(store(arr, i, v), i) != v);
  assert(s.check() == unsat);  // read-over-write axiom
}

int main() {
  printf("ay.hpp C++ consumer test\n");

  test_lia_sat();
  printf("  PASS: lia_sat\n");
  test_lia_unsat();
  printf("  PASS: lia_unsat\n");
  test_lia_arith();
  printf("  PASS: lia_arith\n");
  test_uf_sat();
  printf("  PASS: uf_sat\n");
  test_uf_unsat_congruence();
  printf("  PASS: uf_unsat_congruence\n");
  test_bool();
  printf("  PASS: bool\n");
  test_bool_unsat();
  printf("  PASS: bool_unsat\n");
  test_bv();
  printf("  PASS: bv\n");
  test_push_pop();
  printf("  PASS: push_pop\n");
  test_array();
  printf("  PASS: array\n");

  printf("All 10 C++ consumer tests passed.\n");
  return 0;
}
