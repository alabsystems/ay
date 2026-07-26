// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Low-level koffi (N-API FFI) binding to AY's Z3-shaped C API (libay_ffi).
//
// This module loads the cdylib and declares koffi signatures for the subset of
// Z3_* functions used by the high-level, z3-JS-shaped wrapper in ayz3.mjs. The
// signature list is a direct port of bindings/python/ayz3/_lib.py's `_SIGS`,
// which is the authoritative signature source for every AY binding.
//
// IMPORTANT ABI NOTE: AY's C ABI is NOT libz3-ABI-compatible. In particular,
// `Z3_ast` is a `uint64_t` *handle* (not a `void*` pointer), so libz3's own JS
// bindings cannot be loaded against it. This binding declares Z3_ast as koffi
// 'uint64' accordingly (koffi marshals it to/from a JS Number, which is exact
// for AY's small interned handle ids). All other opaque handles (context,
// solver, sort, ...) are real pointers and are declared as 'void *'.

import { createRequire } from "node:module";
import { existsSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import process from "node:process";

const require = createRequire(import.meta.url);
const koffi = require("koffi");

// ---------------------------------------------------------------------------
// Locating the shared library
// ---------------------------------------------------------------------------
// Resolution order mirrors ayz3 (Python):
//   1. AYSEARCH_LIB, then AYZ3_LIB, if set (highest priority).
//   2. A library bundled next to this module (installed-package layout).
//   3. The in-tree Cargo build output: walk up to the workspace root (a dir
//      with `target/`) and probe target/{debug,release}/.

const __dirname = dirname(fileURLToPath(import.meta.url));

const LIB_BASENAMES = {
  darwin: "libay_ffi.dylib",
  linux: "libay_ffi.so",
  win32: "ay_ffi.dll",
};

function platformBasename() {
  return LIB_BASENAMES[process.platform] ?? "libay_ffi.so";
}

function* candidatePaths() {
  for (const variable of ["AYSEARCH_LIB", "AYZ3_LIB"]) {
    const configured = process.env[variable];
    if (configured) yield configured;
  }

  const basename = platformBasename();
  // Bundled next to this module (installed layout).
  for (const name of new Set([basename, ...Object.values(LIB_BASENAMES)])) {
    yield join(__dirname, name);
  }
  // Walk up looking for a Cargo workspace root (has a `target/` dir).
  let dir = __dirname;
  for (let i = 0; i < 12; i++) {
    for (const profile of ["debug", "release"]) {
      yield join(dir, "target", profile, basename);
    }
    const parent = dirname(dir);
    if (parent === dir) break;
    dir = parent;
  }
}

function loadLibrary() {
  const tried = [];
  for (const p of candidatePaths()) {
    tried.push(p);
    if (existsSync(p)) return koffi.load(p);
  }
  throw new Error(
    "Could not locate libay_ffi shared library. Build it with " +
      "`cargo build -p ay-ffi`, or set AYSEARCH_LIB/AYZ3_LIB to its full path.\nTried:\n  " +
      tried.join("\n  "),
  );
}

const dylib = loadLibrary();

// ---------------------------------------------------------------------------
// koffi type aliases (mirror the ctypes aliases in ayz3/_lib.py)
// ---------------------------------------------------------------------------

const AST = "uint64"; // AY: a 64-bit handle, NOT a pointer.
const PTR = "void *"; // context/config/sort/solver/model/symbol/func_decl/...
const STR = "str"; // const char* (in and out)
const INT = "int";
const UINT = "uint";
const I64 = "int64";
const U64 = "uint64";
const BOOL = "bool";
const DBL = "double";
const VOID = "void";
const AST_IN = "uint64 *"; // [in] array of Z3_ast handles
const PTR_IN = "void **"; // [in] array of opaque pointers (sorts/symbols/...)
const INT_IN = "int *"; // [in] array of C ints (pble/pbge/pbeq coefficients)

// Z3_lbool (return of Z3_solver_check / Z3_optimize_check / ...)
export const Z3_L_FALSE = -1; // unsat
export const Z3_L_UNDEF = 0; // unknown
export const Z3_L_TRUE = 1; // sat

// Z3_error_code
export const Z3_OK = 0;

// Z3_sort_kind (upstream Z3_sort_kind enum, verified vs z3py 4.15.4).
export const Z3_UNINTERPRETED_SORT = 0;
export const Z3_BOOL_SORT = 1;
export const Z3_INT_SORT = 2;
export const Z3_REAL_SORT = 3;
export const Z3_BV_SORT = 4;
export const Z3_ARRAY_SORT = 5;
export const Z3_DATATYPE_SORT = 6;
export const Z3_FLOATING_POINT_SORT = 9;
export const Z3_ROUNDING_MODE_SORT = 10;
export const Z3_SEQ_SORT = 11;
export const Z3_RE_SORT = 12;

// Z3_ast_kind
export const Z3_NUMERAL_AST = 0;
export const Z3_APP_AST = 1;
export const Z3_VAR_AST = 2;
export const Z3_QUANTIFIER_AST = 3;
export const Z3_UNKNOWN_AST = 1000;

// ---------------------------------------------------------------------------
// Signature declarations. Ported from ayz3/_lib.py `_SIGS`.
// Each entry: [name, restype, [argtypes...]]. Functions with pointer OUTPUT
// parameters (model_eval, get_version) are bound separately below with
// koffi.out(...).
// ---------------------------------------------------------------------------

const SIGS = [
  // Config & context
  ["Z3_mk_config", PTR, []],
  ["Z3_del_config", VOID, [PTR]],
  ["Z3_set_param_value", VOID, [PTR, STR, STR]],
  ["Z3_mk_context", PTR, [PTR]],
  ["Z3_del_context", VOID, [PTR]],
  ["Z3_get_error_code", UINT, [PTR]],
  ["Z3_get_error_msg", STR, [PTR, UINT]],

  // Symbols
  ["Z3_mk_string_symbol", PTR, [PTR, STR]],
  ["Z3_get_symbol_kind", UINT, [PTR, PTR]],
  ["Z3_get_symbol_string", STR, [PTR, PTR]],
  ["Z3_get_symbol_int", INT, [PTR, PTR]],

  // Sorts
  ["Z3_mk_bool_sort", PTR, [PTR]],
  ["Z3_mk_int_sort", PTR, [PTR]],
  ["Z3_mk_real_sort", PTR, [PTR]],
  ["Z3_mk_bv_sort", PTR, [PTR, UINT]],
  ["Z3_mk_array_sort", PTR, [PTR, PTR, PTR]],
  ["Z3_mk_string_sort", PTR, [PTR]],
  ["Z3_get_sort_kind", UINT, [PTR, PTR]],
  ["Z3_get_bv_sort_size", UINT, [PTR, PTR]],
  ["Z3_get_array_sort_domain", PTR, [PTR, PTR]],
  ["Z3_get_array_sort_range", PTR, [PTR, PTR]],
  ["Z3_get_sort_name", PTR, [PTR, PTR]],

  // Constants & numerals
  ["Z3_mk_const", AST, [PTR, PTR, PTR]],
  ["Z3_mk_numeral", AST, [PTR, STR, PTR]],
  ["Z3_mk_int64", AST, [PTR, I64, PTR]],
  ["Z3_mk_true", AST, [PTR]],
  ["Z3_mk_false", AST, [PTR]],
  ["Z3_mk_fresh_const", AST, [PTR, STR, PTR]],
  ["Z3_mk_string", AST, [PTR, STR]],

  // Boolean ops
  ["Z3_mk_eq", AST, [PTR, AST, AST]],
  ["Z3_mk_distinct", AST, [PTR, UINT, AST_IN]],
  ["Z3_mk_not", AST, [PTR, AST]],
  ["Z3_mk_ite", AST, [PTR, AST, AST, AST]],
  ["Z3_mk_implies", AST, [PTR, AST, AST]],
  ["Z3_mk_iff", AST, [PTR, AST, AST]],
  ["Z3_mk_xor", AST, [PTR, AST, AST]],
  ["Z3_mk_and", AST, [PTR, UINT, AST_IN]],
  ["Z3_mk_or", AST, [PTR, UINT, AST_IN]],

  // Pseudo-boolean / cardinality
  ["Z3_mk_atmost", AST, [PTR, UINT, AST_IN, UINT]],
  ["Z3_mk_atleast", AST, [PTR, UINT, AST_IN, UINT]],
  ["Z3_mk_pble", AST, [PTR, UINT, AST_IN, INT_IN, INT]],
  ["Z3_mk_pbge", AST, [PTR, UINT, AST_IN, INT_IN, INT]],
  ["Z3_mk_pbeq", AST, [PTR, UINT, AST_IN, INT_IN, INT]],

  // Arithmetic
  ["Z3_mk_add", AST, [PTR, UINT, AST_IN]],
  ["Z3_mk_mul", AST, [PTR, UINT, AST_IN]],
  ["Z3_mk_sub", AST, [PTR, UINT, AST_IN]],
  ["Z3_mk_unary_minus", AST, [PTR, AST]],
  ["Z3_mk_div", AST, [PTR, AST, AST]],
  ["Z3_mk_mod", AST, [PTR, AST, AST]],
  ["Z3_mk_lt", AST, [PTR, AST, AST]],
  ["Z3_mk_le", AST, [PTR, AST, AST]],
  ["Z3_mk_gt", AST, [PTR, AST, AST]],
  ["Z3_mk_ge", AST, [PTR, AST, AST]],
  ["Z3_mk_int2real", AST, [PTR, AST]],
  ["Z3_mk_real2int", AST, [PTR, AST]],
  ["Z3_mk_is_int", AST, [PTR, AST]],
  ["Z3_mk_power", AST, [PTR, AST, AST]],

  // Bitvector core
  ["Z3_mk_bvadd", AST, [PTR, AST, AST]],
  ["Z3_mk_bvsub", AST, [PTR, AST, AST]],
  ["Z3_mk_bvmul", AST, [PTR, AST, AST]],
  ["Z3_mk_bvand", AST, [PTR, AST, AST]],
  ["Z3_mk_bvor", AST, [PTR, AST, AST]],
  ["Z3_mk_bvxor", AST, [PTR, AST, AST]],
  ["Z3_mk_bvnot", AST, [PTR, AST]],
  ["Z3_mk_bvneg", AST, [PTR, AST]],
  ["Z3_mk_bvult", AST, [PTR, AST, AST]],
  ["Z3_mk_bvule", AST, [PTR, AST, AST]],
  ["Z3_mk_bvugt", AST, [PTR, AST, AST]],
  ["Z3_mk_bvuge", AST, [PTR, AST, AST]],
  ["Z3_mk_bvslt", AST, [PTR, AST, AST]],
  ["Z3_mk_bvsle", AST, [PTR, AST, AST]],
  ["Z3_mk_bvsgt", AST, [PTR, AST, AST]],
  ["Z3_mk_bvsge", AST, [PTR, AST, AST]],
  // Bitvector extended
  ["Z3_mk_bvudiv", AST, [PTR, AST, AST]],
  ["Z3_mk_bvsdiv", AST, [PTR, AST, AST]],
  ["Z3_mk_bvurem", AST, [PTR, AST, AST]],
  ["Z3_mk_bvsrem", AST, [PTR, AST, AST]],
  ["Z3_mk_bvsmod", AST, [PTR, AST, AST]],
  ["Z3_mk_bvshl", AST, [PTR, AST, AST]],
  ["Z3_mk_bvlshr", AST, [PTR, AST, AST]],
  ["Z3_mk_bvashr", AST, [PTR, AST, AST]],
  ["Z3_mk_concat", AST, [PTR, AST, AST]],
  ["Z3_mk_extract", AST, [PTR, UINT, UINT, AST]],
  ["Z3_mk_sign_ext", AST, [PTR, UINT, AST]],
  ["Z3_mk_zero_ext", AST, [PTR, UINT, AST]],
  ["Z3_mk_repeat", AST, [PTR, UINT, AST]],
  ["Z3_mk_rotate_left", AST, [PTR, UINT, AST]],
  ["Z3_mk_rotate_right", AST, [PTR, UINT, AST]],
  ["Z3_mk_bv2int", AST, [PTR, AST, BOOL]],
  ["Z3_mk_int2bv", AST, [PTR, UINT, AST]],
  ["Z3_mk_bvredand", AST, [PTR, AST]],
  ["Z3_mk_bvredor", AST, [PTR, AST]],
  ["Z3_mk_bvadd_no_overflow", AST, [PTR, AST, AST, BOOL]],
  ["Z3_mk_bvadd_no_underflow", AST, [PTR, AST, AST]],
  ["Z3_mk_bvsub_no_overflow", AST, [PTR, AST, AST]],
  ["Z3_mk_bvsub_no_underflow", AST, [PTR, AST, AST, BOOL]],
  ["Z3_mk_bvmul_no_overflow", AST, [PTR, AST, AST, BOOL]],
  ["Z3_mk_bvmul_no_underflow", AST, [PTR, AST, AST]],
  ["Z3_mk_bvsdiv_no_overflow", AST, [PTR, AST, AST]],

  // AST / numeral inspection
  ["Z3_get_sort", PTR, [PTR, AST]],
  ["Z3_get_numeral_string", STR, [PTR, AST]],
  ["Z3_get_bool_value", INT, [PTR, AST]],
  ["Z3_ast_to_string", STR, [PTR, AST]],
  ["Z3_get_ast_kind", UINT, [PTR, AST]],
  ["Z3_is_numeral_ast", BOOL, [PTR, AST]],
  ["Z3_is_app", BOOL, [PTR, AST]],
  ["Z3_get_app_decl", PTR, [PTR, AST]],
  ["Z3_get_app_num_args", UINT, [PTR, AST]],
  ["Z3_get_app_arg", AST, [PTR, AST, UINT]],
  ["Z3_get_decl_kind", UINT, [PTR, PTR]],
  ["Z3_get_decl_name", PTR, [PTR, PTR]],
  ["Z3_get_decl_num_parameters", UINT, [PTR, PTR]],
  ["Z3_get_decl_int_parameter", INT, [PTR, PTR, UINT]],

  // Arrays
  ["Z3_mk_select", AST, [PTR, AST, AST]],
  ["Z3_mk_store", AST, [PTR, AST, AST, AST]],
  ["Z3_mk_const_array", AST, [PTR, PTR, AST]],

  // Uninterpreted functions
  ["Z3_mk_func_decl", PTR, [PTR, PTR, UINT, PTR_IN, PTR]],
  ["Z3_mk_app", AST, [PTR, PTR, UINT, AST_IN]],
  ["Z3_get_range", PTR, [PTR, PTR]],
  ["Z3_get_domain", PTR, [PTR, PTR, UINT]],

  // Quantifiers (constant style)
  ["Z3_mk_forall_const", AST, [PTR, UINT, UINT, AST_IN, UINT, PTR_IN, AST]],
  ["Z3_mk_exists_const", AST, [PTR, UINT, UINT, AST_IN, UINT, PTR_IN, AST]],
  ["Z3_mk_pattern", PTR, [PTR, UINT, AST_IN]],
  ["Z3_get_quantifier_num_bound", UINT, [PTR, AST]],
  ["Z3_get_quantifier_body", AST, [PTR, AST]],
  ["Z3_is_quantifier_forall", BOOL, [PTR, AST]],
  ["Z3_is_quantifier_exists", BOOL, [PTR, AST]],

  // Solver
  ["Z3_mk_solver", PTR, [PTR]],
  ["Z3_solver_push", VOID, [PTR, PTR]],
  ["Z3_solver_pop", VOID, [PTR, PTR, UINT]],
  ["Z3_solver_reset", VOID, [PTR, PTR]],
  ["Z3_solver_assert", VOID, [PTR, PTR, AST]],
  ["Z3_solver_check", INT, [PTR, PTR]],
  ["Z3_solver_check_assumptions", INT, [PTR, PTR, UINT, AST_IN]],
  ["Z3_solver_get_unsat_core", PTR, [PTR, PTR]],
  ["Z3_solver_get_assertions", PTR, [PTR, PTR]],
  ["Z3_solver_get_reason_unknown", STR, [PTR, PTR]],
  ["Z3_solver_get_model", PTR, [PTR, PTR]],
  ["Z3_solver_to_string", STR, [PTR, PTR]],
  ["Z3_solver_get_num_scopes", UINT, [PTR, PTR]],
  ["Z3_solver_set_params", VOID, [PTR, PTR, PTR]],

  // Model
  ["Z3_model_to_string", STR, [PTR, PTR]],
  ["Z3_model_get_num_consts", UINT, [PTR, PTR]],
  ["Z3_model_get_const_decl", PTR, [PTR, PTR, UINT]],
  ["Z3_model_get_const_interp", AST, [PTR, PTR, PTR]],

  // AST vectors
  ["Z3_mk_ast_vector", PTR, [PTR]],
  ["Z3_ast_vector_inc_ref", VOID, [PTR, PTR]],
  ["Z3_ast_vector_dec_ref", VOID, [PTR, PTR]],
  ["Z3_ast_vector_push", VOID, [PTR, PTR, AST]],
  ["Z3_ast_vector_size", UINT, [PTR, PTR]],
  ["Z3_ast_vector_get", AST, [PTR, PTR, UINT]],

  // Params
  ["Z3_mk_params", PTR, [PTR]],
  ["Z3_params_inc_ref", VOID, [PTR, PTR]],
  ["Z3_params_dec_ref", VOID, [PTR, PTR]],
  ["Z3_params_set_uint", VOID, [PTR, PTR, PTR, UINT]],
  ["Z3_params_set_bool", VOID, [PTR, PTR, PTR, BOOL]],
  ["Z3_params_set_double", VOID, [PTR, PTR, PTR, DBL]],
  ["Z3_params_set_symbol", VOID, [PTR, PTR, PTR, PTR]],

  // Simplify / substitute
  ["Z3_simplify", AST, [PTR, AST]],
  ["Z3_substitute", AST, [PTR, AST, UINT, AST_IN, AST_IN]],

  // Optimize (core subset)
  ["Z3_mk_optimize", PTR, [PTR]],
  ["Z3_optimize_assert", VOID, [PTR, PTR, AST]],
  ["Z3_optimize_maximize", UINT, [PTR, PTR, AST]],
  ["Z3_optimize_minimize", UINT, [PTR, PTR, AST]],
  ["Z3_optimize_check", INT, [PTR, PTR, UINT, AST_IN]],
  ["Z3_optimize_get_model", PTR, [PTR, PTR]],
];

/**
 * Bound Z3_* functions, keyed by name. Each is a directly-callable JS function.
 * @type {Record<string, Function>}
 */
export const lib = {};

for (const [name, ret, args] of SIGS) {
  lib[name] = dylib.func(name, ret, args);
}

// Functions with pointer OUTPUT parameters need koffi.out(...): the caller
// passes a length-1 JS array and reads element 0 back after the call.

// Z3_model_eval(ctx, model, ast, model_completion, Z3_ast* out) -> bool
lib.Z3_model_eval = dylib.func("Z3_model_eval", BOOL, [
  PTR,
  PTR,
  AST,
  BOOL,
  koffi.out("uint64 *"),
]);

// Z3_get_version(uint* major, uint* minor, uint* build, uint* revision) -> void
lib.Z3_get_version = dylib.func("Z3_get_version", VOID, [
  koffi.out("uint *"),
  koffi.out("uint *"),
  koffi.out("uint *"),
  koffi.out("uint *"),
]);

// ay-search is deliberately a tiny one-shot JSON ABI. Return values stay as
// pointers so the high-level wrapper can decode and then release the Rust-owned
// allocation with ay_string_free.
lib.ay_search_solve_json = dylib.func("ay_search_solve_json", PTR, [STR]);
lib.ay_search_compile_json = dylib.func("ay_search_compile_json", PTR, [STR]);
lib.ay_string_free = dylib.func("ay_string_free", VOID, [PTR]);

/** Number of Z3_* functions bound by this module. */
export const BOUND_FUNCTION_COUNT = SIGS.length + 2;

export { koffi };
