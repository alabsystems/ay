// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Idiomatic, z3-JS-shaped wrapper over AY's Z3-shaped C API.
//
// This is a THIN, SOUND wrapper: verdicts and models come from AY's real
// solver across the FFI (see _lib.mjs); this module only builds AST handles and
// marshals them. It mirrors the shape of z3's own JS/Python API — Context,
// Sort, Expr, FuncDecl, Model, Solver — so existing z3 muscle memory transfers.
//
// ABI note: AY's `Z3_ast` is a u64 handle (not a pointer), already accounted
// for in _lib.mjs. Everything here is handle-passing over that binding.

import {
  lib,
  Z3_L_FALSE,
  Z3_L_TRUE,
  Z3_OK,
  Z3_BOOL_SORT,
  Z3_INT_SORT,
  Z3_REAL_SORT,
  Z3_BV_SORT,
  Z3_ARRAY_SORT,
  BOUND_FUNCTION_COUNT,
} from "./_lib.mjs";

export { BOUND_FUNCTION_COUNT };

/** Error raised when AY's C ABI reports a non-OK error code. */
export class Ayz3Error extends Error {}

// ---------------------------------------------------------------------------
// Context: owns a Z3_config + Z3_context and is the factory for everything.
// ---------------------------------------------------------------------------

export class Context {
  /**
   * @param {Object<string,string>} [params] config key/value pairs, e.g.
   *   `{ timeout: "5000" }` (forwarded to Z3_set_param_value on the config).
   */
  constructor(params = {}) {
    this.cfg = lib.Z3_mk_config();
    for (const [k, v] of Object.entries(params)) {
      lib.Z3_set_param_value(this.cfg, String(k), String(v));
    }
    this.ptr = lib.Z3_mk_context(this.cfg);
  }

  /** Throw an Ayz3Error if the context's last operation set an error code. */
  _check(op) {
    const code = lib.Z3_get_error_code(this.ptr);
    if (code !== Z3_OK) {
      const msg = lib.Z3_get_error_msg(this.ptr, code);
      throw new Ayz3Error(`${op}: AY error ${code}: ${msg}`);
    }
  }

  /** Wrap a raw ast handle into an Expr, after an error-code check. */
  _expr(ast, op) {
    this._check(op);
    return new Expr(this, ast);
  }

  // ---- Sorts ----
  BoolSort() {
    return new Sort(this, lib.Z3_mk_bool_sort(this.ptr));
  }
  IntSort() {
    return new Sort(this, lib.Z3_mk_int_sort(this.ptr));
  }
  RealSort() {
    return new Sort(this, lib.Z3_mk_real_sort(this.ptr));
  }
  BitVecSort(bits) {
    return new Sort(this, lib.Z3_mk_bv_sort(this.ptr, bits >>> 0));
  }
  ArraySort(domain, range) {
    return new Sort(
      this,
      lib.Z3_mk_array_sort(this.ptr, domain.ptr, range.ptr),
    );
  }

  _symbol(name) {
    return lib.Z3_mk_string_symbol(this.ptr, String(name));
  }

  // ---- Constants ----
  Const(name, sort) {
    return this._expr(
      lib.Z3_mk_const(this.ptr, this._symbol(name), sort.ptr),
      "Const",
    );
  }
  FreshConst(sort, prefix = "fresh") {
    return this._expr(
      lib.Z3_mk_fresh_const(this.ptr, String(prefix), sort.ptr),
      "FreshConst",
    );
  }
  Bool(name) {
    return this.Const(name, this.BoolSort());
  }
  Int(name) {
    return this.Const(name, this.IntSort());
  }
  Real(name) {
    return this.Const(name, this.RealSort());
  }
  BitVec(name, bits) {
    return this.Const(name, this.BitVecSort(bits));
  }

  // ---- Values / numerals ----
  BoolVal(b) {
    const ast = b ? lib.Z3_mk_true(this.ptr) : lib.Z3_mk_false(this.ptr);
    return this._expr(ast, "BoolVal");
  }
  IntVal(n) {
    return this._expr(
      lib.Z3_mk_numeral(this.ptr, String(n), lib.Z3_mk_int_sort(this.ptr)),
      "IntVal",
    );
  }
  RealVal(n) {
    return this._expr(
      lib.Z3_mk_numeral(this.ptr, String(n), lib.Z3_mk_real_sort(this.ptr)),
      "RealVal",
    );
  }
  BitVecVal(n, bits) {
    return this._expr(
      lib.Z3_mk_numeral(this.ptr, String(n), lib.Z3_mk_bv_sort(this.ptr, bits >>> 0)),
      "BitVecVal",
    );
  }
  StringVal(s) {
    return this._expr(lib.Z3_mk_string(this.ptr, String(s)), "StringVal");
  }

  // ---- Uninterpreted functions ----
  /**
   * Function('f', dom0, dom1, ..., range) -> FuncDecl (last arg is the range).
   */
  Function(name, ...sorts) {
    const range = sorts.pop();
    const domainPtrs = sorts.map((s) => s.ptr);
    const decl = lib.Z3_mk_func_decl(
      this.ptr,
      this._symbol(name),
      domainPtrs.length,
      domainPtrs,
      range.ptr,
    );
    this._check("Function");
    return new FuncDecl(this, decl);
  }

  // ---- Boolean / control builders (functional style) ----
  And(...args) {
    const asts = flattenExprs(args).map((e) => e.ast);
    return this._expr(lib.Z3_mk_and(this.ptr, asts.length, asts), "And");
  }
  Or(...args) {
    const asts = flattenExprs(args).map((e) => e.ast);
    return this._expr(lib.Z3_mk_or(this.ptr, asts.length, asts), "Or");
  }
  Not(a) {
    return this._expr(lib.Z3_mk_not(this.ptr, a.ast), "Not");
  }
  Implies(a, b) {
    return this._expr(lib.Z3_mk_implies(this.ptr, a.ast, this._coerce(b, a)), "Implies");
  }
  Xor(a, b) {
    return this._expr(lib.Z3_mk_xor(this.ptr, a.ast, this._coerce(b, a)), "Xor");
  }
  Distinct(...args) {
    const asts = flattenExprs(args).map((e) => e.ast);
    return this._expr(
      lib.Z3_mk_distinct(this.ptr, asts.length, asts),
      "Distinct",
    );
  }
  If(cond, t, e) {
    return this._expr(
      lib.Z3_mk_ite(this.ptr, cond.ast, t.ast, this._coerce(e, t)),
      "If",
    );
  }
  Eq(a, b) {
    return a.eq(b);
  }

  Solver() {
    return new Solver(this);
  }
  Optimize() {
    return new Optimize(this);
  }

  /**
   * Coerce `value` to a Z3_ast handle sort-matched to `ref` (an Expr). If it is
   * already an Expr, its handle is returned unchanged; a JS number/bigint/
   * boolean/string becomes a numeral of `ref`'s sort.
   */
  _coerce(value, ref) {
    if (value instanceof Expr) return value.ast;
    const kind = ref._sortKind();
    if (kind === Z3_BOOL_SORT) {
      return value ? lib.Z3_mk_true(this.ptr) : lib.Z3_mk_false(this.ptr);
    }
    // INT / REAL / BV: a same-sort numeral from the decimal string form.
    const sortPtr = lib.Z3_get_sort(this.ptr, ref.ast);
    return lib.Z3_mk_numeral(this.ptr, String(value), sortPtr);
  }

  version() {
    const M = [0], m = [0], b = [0], r = [0];
    lib.Z3_get_version(M, m, b, r);
    return `${M[0]}.${m[0]}.${b[0]}.${r[0]}`;
  }

  dispose() {
    lib.Z3_del_context(this.ptr);
    lib.Z3_del_config(this.cfg);
  }
}

function flattenExprs(args) {
  // Accept And(a, b) as well as And([a, b]).
  if (args.length === 1 && Array.isArray(args[0])) return args[0];
  return args;
}

// ---------------------------------------------------------------------------
// Sort
// ---------------------------------------------------------------------------

export class Sort {
  constructor(ctx, ptr) {
    this.ctx = ctx;
    this.ptr = ptr;
  }
  kind() {
    return lib.Z3_get_sort_kind(this.ctx.ptr, this.ptr);
  }
  /** For a bit-vector sort, its width in bits. */
  size() {
    return lib.Z3_get_bv_sort_size(this.ctx.ptr, this.ptr);
  }
  toString() {
    const name = lib.Z3_get_sort_name(this.ctx.ptr, this.ptr);
    return lib.Z3_get_symbol_string(this.ctx.ptr, name);
  }
}

// ---------------------------------------------------------------------------
// FuncDecl (an uninterpreted function). Callable via .call(...args).
// ---------------------------------------------------------------------------

export class FuncDecl {
  constructor(ctx, ptr) {
    this.ctx = ctx;
    this.ptr = ptr;
  }
  call(...args) {
    const asts = args.map((a) => (a instanceof Expr ? a.ast : a));
    const ast = lib.Z3_mk_app(this.ctx.ptr, this.ptr, asts.length, asts);
    return this.ctx._expr(ast, "FuncDecl.call");
  }
}

// ---------------------------------------------------------------------------
// Expr: a wrapped Z3_ast handle with idiomatic operator methods.
// ---------------------------------------------------------------------------

export class Expr {
  constructor(ctx, ast) {
    this.ctx = ctx;
    this.ast = ast;
    this._kind = undefined;
  }

  _sortKind() {
    if (this._kind === undefined) {
      const sortPtr = lib.Z3_get_sort(this.ctx.ptr, this.ast);
      this._kind = lib.Z3_get_sort_kind(this.ctx.ptr, sortPtr);
    }
    return this._kind;
  }

  sort() {
    return new Sort(this.ctx, lib.Z3_get_sort(this.ctx.ptr, this.ast));
  }

  isBV() {
    return this._sortKind() === Z3_BV_SORT;
  }
  isBool() {
    return this._sortKind() === Z3_BOOL_SORT;
  }

  _c(v) {
    return this.ctx._coerce(v, this);
  }
  _e(ast, op) {
    return this.ctx._expr(ast, op);
  }

  // ---- equality ----
  eq(other) {
    return this._e(lib.Z3_mk_eq(this.ctx.ptr, this.ast, this._c(other)), "eq");
  }
  neq(other) {
    return this.ctx.Not(this.eq(other));
  }

  // ---- arithmetic / bitvector (routed by sort) ----
  add(...others) {
    if (this.isBV()) return this._foldBV(others, lib.Z3_mk_bvadd);
    return this._nary(others, lib.Z3_mk_add);
  }
  sub(...others) {
    if (this.isBV()) return this._foldBV(others, lib.Z3_mk_bvsub);
    return this._nary(others, lib.Z3_mk_sub);
  }
  mul(...others) {
    if (this.isBV()) return this._foldBV(others, lib.Z3_mk_bvmul);
    return this._nary(others, lib.Z3_mk_mul);
  }
  div(other) {
    if (this.isBV())
      return this._e(lib.Z3_mk_bvudiv(this.ctx.ptr, this.ast, this._c(other)), "div");
    return this._e(lib.Z3_mk_div(this.ctx.ptr, this.ast, this._c(other)), "div");
  }
  mod(other) {
    return this._e(lib.Z3_mk_mod(this.ctx.ptr, this.ast, this._c(other)), "mod");
  }
  neg() {
    if (this.isBV()) return this._e(lib.Z3_mk_bvneg(this.ctx.ptr, this.ast), "neg");
    return this._e(lib.Z3_mk_unary_minus(this.ctx.ptr, this.ast), "neg");
  }

  _nary(others, mk) {
    const asts = [this.ast, ...others.map((o) => this._c(o))];
    return this._e(mk(this.ctx.ptr, asts.length, asts), "nary");
  }
  _foldBV(others, mk) {
    let acc = this.ast;
    for (const o of others) acc = mk(this.ctx.ptr, acc, this._c(o));
    return this._e(acc, "bv-fold");
  }

  // ---- arithmetic comparisons (Int/Real) ----
  lt(o) {
    return this._e(lib.Z3_mk_lt(this.ctx.ptr, this.ast, this._c(o)), "lt");
  }
  le(o) {
    return this._e(lib.Z3_mk_le(this.ctx.ptr, this.ast, this._c(o)), "le");
  }
  gt(o) {
    return this._e(lib.Z3_mk_gt(this.ctx.ptr, this.ast, this._c(o)), "gt");
  }
  ge(o) {
    return this._e(lib.Z3_mk_ge(this.ctx.ptr, this.ast, this._c(o)), "ge");
  }

  // ---- boolean / bitwise (routed by sort) ----
  and(...others) {
    if (this.isBV()) return this._foldBV(others, lib.Z3_mk_bvand);
    const asts = [this.ast, ...others.map((o) => this._c(o))];
    return this._e(lib.Z3_mk_and(this.ctx.ptr, asts.length, asts), "and");
  }
  or(...others) {
    if (this.isBV()) return this._foldBV(others, lib.Z3_mk_bvor);
    const asts = [this.ast, ...others.map((o) => this._c(o))];
    return this._e(lib.Z3_mk_or(this.ctx.ptr, asts.length, asts), "or");
  }
  xor(o) {
    if (this.isBV())
      return this._e(lib.Z3_mk_bvxor(this.ctx.ptr, this.ast, this._c(o)), "xor");
    return this._e(lib.Z3_mk_xor(this.ctx.ptr, this.ast, this._c(o)), "xor");
  }
  not() {
    if (this.isBV()) return this._e(lib.Z3_mk_bvnot(this.ctx.ptr, this.ast), "not");
    return this._e(lib.Z3_mk_not(this.ctx.ptr, this.ast), "not");
  }

  // ---- unsigned / signed BV comparisons ----
  ult(o) { return this._bvCmp(o, lib.Z3_mk_bvult, "ult"); }
  ule(o) { return this._bvCmp(o, lib.Z3_mk_bvule, "ule"); }
  ugt(o) { return this._bvCmp(o, lib.Z3_mk_bvugt, "ugt"); }
  uge(o) { return this._bvCmp(o, lib.Z3_mk_bvuge, "uge"); }
  slt(o) { return this._bvCmp(o, lib.Z3_mk_bvslt, "slt"); }
  sle(o) { return this._bvCmp(o, lib.Z3_mk_bvsle, "sle"); }
  sgt(o) { return this._bvCmp(o, lib.Z3_mk_bvsgt, "sgt"); }
  sge(o) { return this._bvCmp(o, lib.Z3_mk_bvsge, "sge"); }
  _bvCmp(o, mk, op) {
    return this._e(mk(this.ctx.ptr, this.ast, this._c(o)), op);
  }
  shl(o) { return this._e(lib.Z3_mk_bvshl(this.ctx.ptr, this.ast, this._c(o)), "shl"); }
  lshr(o) { return this._e(lib.Z3_mk_bvlshr(this.ctx.ptr, this.ast, this._c(o)), "lshr"); }
  ashr(o) { return this._e(lib.Z3_mk_bvashr(this.ctx.ptr, this.ast, this._c(o)), "ashr"); }
  extract(hi, lo) {
    return this._e(lib.Z3_mk_extract(this.ctx.ptr, hi >>> 0, lo >>> 0, this.ast), "extract");
  }
  concat(o) {
    return this._e(lib.Z3_mk_concat(this.ctx.ptr, this.ast, this._c(o)), "concat");
  }

  // ---- array select ----
  select(index) {
    return this._e(lib.Z3_mk_select(this.ctx.ptr, this.ast, this._c(index)), "select");
  }

  // ---- inspection ----
  isNumeral() {
    return lib.Z3_is_numeral_ast(this.ctx.ptr, this.ast);
  }
  /** Decimal string of a numeral (int/real/bv). Throws for non-numerals. */
  asString() {
    return lib.Z3_get_numeral_string(this.ctx.ptr, this.ast);
  }
  /** Numeric value of an integer/bv numeral as a JS number (may lose precision above 2^53). */
  asNumber() {
    return Number(this.asString());
  }
  /** Boolean value of a boolean numeral: true/false/null(unknown). */
  asBool() {
    const v = lib.Z3_get_bool_value(this.ctx.ptr, this.ast);
    if (v === Z3_L_TRUE) return true;
    if (v === Z3_L_FALSE) return false;
    return null;
  }
  toString() {
    return lib.Z3_ast_to_string(this.ctx.ptr, this.ast);
  }
}

// ---------------------------------------------------------------------------
// Model
// ---------------------------------------------------------------------------

export class Model {
  constructor(ctx, ptr) {
    this.ctx = ctx;
    this.ptr = ptr;
  }
  /**
   * Evaluate `expr` under this model. With modelCompletion (default true), a
   * variable with no explicit assignment gets a canonical value of its sort.
   * Returns an Expr (typically a numeral) or null if evaluation failed.
   */
  eval(expr, modelCompletion = true) {
    const out = [0n];
    const ok = lib.Z3_model_eval(
      this.ctx.ptr,
      this.ptr,
      expr.ast,
      modelCompletion,
      out,
    );
    this.ctx._check("Model.eval");
    if (!ok) return null;
    return new Expr(this.ctx, out[0]);
  }
  /** Number of constant (0-ary) interpretations in the model. */
  numConsts() {
    return lib.Z3_model_get_num_consts(this.ctx.ptr, this.ptr);
  }
  toString() {
    return lib.Z3_model_to_string(this.ctx.ptr, this.ptr);
  }
}

// ---------------------------------------------------------------------------
// Solver
// ---------------------------------------------------------------------------

function verdict(lbool) {
  if (lbool === Z3_L_TRUE) return "sat";
  if (lbool === Z3_L_FALSE) return "unsat";
  return "unknown";
}

export class Solver {
  constructor(ctx) {
    this.ctx = ctx;
    this.ptr = lib.Z3_mk_solver(ctx.ptr);
  }
  /** Assert one or more boolean constraints (accepts Exprs or arrays). */
  add(...constraints) {
    for (const c of flattenExprs(constraints)) {
      lib.Z3_solver_assert(this.ctx.ptr, this.ptr, c.ast);
    }
    this.ctx._check("Solver.add");
    return this;
  }
  assert(...constraints) {
    return this.add(...constraints);
  }
  push() {
    lib.Z3_solver_push(this.ctx.ptr, this.ptr);
    return this;
  }
  pop(n = 1) {
    lib.Z3_solver_pop(this.ctx.ptr, this.ptr, n >>> 0);
    return this;
  }
  reset() {
    lib.Z3_solver_reset(this.ctx.ptr, this.ptr);
    return this;
  }
  numScopes() {
    return lib.Z3_solver_get_num_scopes(this.ctx.ptr, this.ptr);
  }
  /** Run the solver. Returns 'sat' | 'unsat' | 'unknown'. */
  check() {
    const r = lib.Z3_solver_check(this.ctx.ptr, this.ptr);
    this.ctx._check("Solver.check");
    return verdict(r);
  }
  model() {
    return new Model(this.ctx, lib.Z3_solver_get_model(this.ctx.ptr, this.ptr));
  }
  reasonUnknown() {
    return lib.Z3_solver_get_reason_unknown(this.ctx.ptr, this.ptr);
  }
  toString() {
    return lib.Z3_solver_to_string(this.ctx.ptr, this.ptr);
  }
}

// ---------------------------------------------------------------------------
// Optimize (core subset)
// ---------------------------------------------------------------------------

export class Optimize {
  constructor(ctx) {
    this.ctx = ctx;
    this.ptr = lib.Z3_mk_optimize(ctx.ptr);
  }
  add(...constraints) {
    for (const c of flattenExprs(constraints)) {
      lib.Z3_optimize_assert(this.ctx.ptr, this.ptr, c.ast);
    }
    return this;
  }
  maximize(expr) {
    return lib.Z3_optimize_maximize(this.ctx.ptr, this.ptr, expr.ast);
  }
  minimize(expr) {
    return lib.Z3_optimize_minimize(this.ctx.ptr, this.ptr, expr.ast);
  }
  check() {
    const r = lib.Z3_optimize_check(this.ctx.ptr, this.ptr, 0, []);
    this.ctx._check("Optimize.check");
    return verdict(r);
  }
  model() {
    return new Model(this.ctx, lib.Z3_optimize_get_model(this.ctx.ptr, this.ptr));
  }
}

export { lib };
