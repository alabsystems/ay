# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# Low-level ctypes binding to AY's Z3-shaped C API (libay_ffi).
#
# This module loads the cdylib and declares the exact ctypes signatures for the
# subset of Z3_* functions used by the high-level z3py-shaped wrapper.
#
# IMPORTANT ABI NOTE: AY's C ABI is NOT libz3-ABI-compatible. In particular,
# `Z3_ast` is a `uint64_t` *handle* (not a `void*` pointer), so libz3's own z3py
# cannot be loaded against it. This binding declares Z3_ast as ctypes.c_uint64
# accordingly. All other opaque handles (context, solver, sort, ...) are real
# pointers and are declared as c_void_p.

import ctypes
import os
import sys
from pathlib import Path

# ---------------------------------------------------------------------------
# Locating the shared library
# ---------------------------------------------------------------------------
#
# Resolution order:
#   1. The AYZ3_LIB environment variable, if set, is treated as the full path to
#      the dylib/so (highest priority; lets callers point at a release build).
#   2. The cdylib bundled INSIDE this package directory (next to this file).
#      An installed wheel ships the library here, so an installed package is
#      self-contained and does not need the AY source tree.
#   3. Otherwise we walk up from this file looking for a Cargo workspace root
#      (a directory containing `target/`) and probe target/{debug,release}/.
#      This is the in-tree dev workflow (run `cargo build -p ay-ffi` first;
#      add --release for the release build).

_LIB_BASENAMES = {
    "darwin": "libay_ffi.dylib",
    "linux": "libay_ffi.so",
    "win32": "ay_ffi.dll",
}


def _platform_basename() -> str:
    for key, name in _LIB_BASENAMES.items():
        if sys.platform.startswith(key):
            return name
    # Fallback: assume an ELF .so name.
    return "libay_ffi.so"


def _candidate_paths():
    # 1. Explicit override.
    env = os.environ.get("AYZ3_LIB")
    if env:
        yield Path(env)

    basename = _platform_basename()
    here = Path(__file__).resolve()

    # 2. Bundled inside this package (installed-wheel layout): the build step
    #    copies the cdylib next to this module. Probe every known basename so a
    #    wheel built on one platform still names its own library correctly.
    pkg_dir = here.parent
    for name in dict.fromkeys([basename, *_LIB_BASENAMES.values()]):
        yield pkg_dir / name

    # 3. Walk up looking for a Cargo workspace root (has a `target/` dir).
    for parent in here.parents:
        target = parent / "target"
        if target.is_dir():
            for profile in ("debug", "release"):
                yield target / profile / basename
        # Stop once we hit the repo root marker to avoid walking the whole FS.
        if (parent / "Cargo.toml").is_file() and (parent / "crates").is_dir():
            break


def _load_library() -> ctypes.CDLL:
    tried = []
    for path in _candidate_paths():
        tried.append(str(path))
        if path.is_file():
            return ctypes.CDLL(str(path))
    raise OSError(
        "Could not locate libay_ffi shared library. Build it with "
        "`cargo build -p ay-ffi`, or set AYZ3_LIB to its full path.\n"
        "Tried:\n  " + "\n  ".join(tried)
    )


lib = _load_library()

# ---------------------------------------------------------------------------
# ctypes type aliases
# ---------------------------------------------------------------------------

Z3_ast = ctypes.c_uint64        # AY: a 64-bit handle, NOT a pointer.
Z3_context = ctypes.c_void_p
Z3_config = ctypes.c_void_p
Z3_sort = ctypes.c_void_p
Z3_func_decl = ctypes.c_void_p
Z3_solver = ctypes.c_void_p
Z3_optimize = ctypes.c_void_p
# Fixedpoint (CHC/Datalog) handle — arena-owned real pointer, like Z3_optimize.
Z3_fixedpoint = ctypes.c_void_p
Z3_tactic = ctypes.c_void_p
Z3_model = ctypes.c_void_p
Z3_symbol = ctypes.c_void_p
Z3_pattern = ctypes.c_void_p
Z3_params = ctypes.c_void_p
# Parameter-descriptor set handle (real pointer; arena-owned by the context).
Z3_param_descrs = ctypes.c_void_p
Z3_ast_vector = ctypes.c_void_p
Z3_string = ctypes.c_char_p
# Statistics snapshot handle (real pointer; freed with its context).
Z3_stats = ctypes.c_void_p
# Goal (set of assertion formulas) and apply-result (tactic subgoals) handles
# (real pointers; arena-owned by the context, freed with it).
Z3_goal = ctypes.c_void_p
Z3_apply_result = ctypes.c_void_p
# Datatype constructor / constructor-list descriptor handles (real pointers).
Z3_constructor = ctypes.c_void_p
Z3_constructor_list = ctypes.c_void_p

# Z3_lbool
Z3_L_FALSE = -1
Z3_L_UNDEF = 0
Z3_L_TRUE = 1

# Z3_symbol_kind (return of Z3_get_symbol_kind).
Z3_INT_SYMBOL = 0
Z3_STRING_SYMBOL = 1

# Z3_param_kind (return of Z3_param_descrs_get_kind). Byte-for-byte the upstream
# Z3_param_kind enum (verified vs z3py 4.15.4).
Z3_PK_UINT = 0
Z3_PK_BOOL = 1
Z3_PK_DOUBLE = 2
Z3_PK_SYMBOL = 3
Z3_PK_STRING = 4
Z3_PK_OTHER = 5
Z3_PK_INVALID = 6

# Z3_ast_kind (return of Z3_get_ast_kind). NOTE: AY reports a *declared
# constant* (e.g. Int('x')) as VAR, and a literal/numeral as NUMERAL.
Z3_NUMERAL_AST = 0
Z3_APP_AST = 1
Z3_VAR_AST = 2
Z3_QUANTIFIER_AST = 3
Z3_UNKNOWN_AST = 1000

# Z3_decl_kind subset (return of Z3_get_decl_kind). AY exposes the same numeric
# values as upstream Z3; we only need the ones the cross-context rebuild routes
# on. Anything not listed routes through the operator-NAME path instead.
# Byte-for-byte the upstream Z3_decl_kind enum (verified vs z3py 4.15.4).
Z3_OP_UNINTERPRETED = 45102  # 0xB02E

# Z3_sort_kind (upstream Z3_sort_kind enum, verified vs z3py 4.15.4).
Z3_UNINTERPRETED_SORT = 0
Z3_BOOL_SORT = 1
Z3_INT_SORT = 2
Z3_REAL_SORT = 3
Z3_BV_SORT = 4
Z3_ARRAY_SORT = 5
# An algebraic datatype (Datatype/EnumSort/TupleSort) reports DATATYPE.
Z3_DATATYPE_SORT = 6
# A String is a sequence in AY's model, so Z3_get_sort_kind reports SEQ for it.
Z3_SEQ_SORT = 11
# A regular-expression sort (RegLan) reports RE (matches upstream Z3_sort_kind).
Z3_RE_SORT = 12

# ---------------------------------------------------------------------------
# Signature declarations
# ---------------------------------------------------------------------------
#
# Each entry: (name, restype, [argtypes...]). Declaring argtypes/restype is
# essential on 64-bit platforms so ctypes marshals Z3_ast (u64) and pointers
# correctly rather than truncating to c_int.

_SIGS = [
    # Config & context
    ("Z3_mk_config", Z3_config, []),
    ("Z3_del_config", None, [Z3_config]),
    ("Z3_set_param_value", None, [Z3_config, Z3_string, Z3_string]),
    ("Z3_mk_context", Z3_context, [Z3_config]),
    ("Z3_del_context", None, [Z3_context]),
    ("Z3_get_error_code", ctypes.c_uint, [Z3_context]),
    ("Z3_get_error_msg", Z3_string, [Z3_context, ctypes.c_uint]),

    # Symbols
    ("Z3_mk_string_symbol", Z3_symbol, [Z3_context, Z3_string]),

    # Sorts
    ("Z3_mk_bool_sort", Z3_sort, [Z3_context]),
    ("Z3_mk_int_sort", Z3_sort, [Z3_context]),
    ("Z3_mk_real_sort", Z3_sort, [Z3_context]),
    ("Z3_mk_bv_sort", Z3_sort, [Z3_context, ctypes.c_uint]),
    ("Z3_get_sort_kind", ctypes.c_uint, [Z3_context, Z3_sort]),
    ("Z3_get_bv_sort_size", ctypes.c_uint, [Z3_context, Z3_sort]),

    # Constants & numerals
    ("Z3_mk_const", Z3_ast, [Z3_context, Z3_symbol, Z3_sort]),
    ("Z3_mk_numeral", Z3_ast, [Z3_context, Z3_string, Z3_sort]),
    ("Z3_mk_int64", Z3_ast, [Z3_context, ctypes.c_int64, Z3_sort]),
    ("Z3_mk_true", Z3_ast, [Z3_context]),
    ("Z3_mk_false", Z3_ast, [Z3_context]),
    # Fresh (uniquely named) constant of a given sort (z3py Fresh*/FreshConst).
    ("Z3_mk_fresh_const", Z3_ast, [Z3_context, Z3_string, Z3_sort]),

    # Boolean ops
    ("Z3_mk_eq", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_distinct", Z3_ast, [Z3_context, ctypes.c_uint, ctypes.POINTER(Z3_ast)]),
    ("Z3_mk_not", Z3_ast, [Z3_context, Z3_ast]),
    ("Z3_mk_ite", Z3_ast, [Z3_context, Z3_ast, Z3_ast, Z3_ast]),
    ("Z3_mk_implies", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_iff", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_xor", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_and", Z3_ast, [Z3_context, ctypes.c_uint, ctypes.POINTER(Z3_ast)]),
    ("Z3_mk_or", Z3_ast, [Z3_context, ctypes.c_uint, ctypes.POINTER(Z3_ast)]),

    # Pseudo-boolean / cardinality constraints over Bool literals.
    #   atmost/atleast: k is `unsigned`.
    #   pble/pbge/pbeq: signed `int` coefficients (one per arg) then signed `int` k.
    ("Z3_mk_atmost", Z3_ast,
     [Z3_context, ctypes.c_uint, ctypes.POINTER(Z3_ast), ctypes.c_uint]),
    ("Z3_mk_atleast", Z3_ast,
     [Z3_context, ctypes.c_uint, ctypes.POINTER(Z3_ast), ctypes.c_uint]),
    ("Z3_mk_pble", Z3_ast,
     [Z3_context, ctypes.c_uint, ctypes.POINTER(Z3_ast),
      ctypes.POINTER(ctypes.c_int), ctypes.c_int]),
    ("Z3_mk_pbge", Z3_ast,
     [Z3_context, ctypes.c_uint, ctypes.POINTER(Z3_ast),
      ctypes.POINTER(ctypes.c_int), ctypes.c_int]),
    ("Z3_mk_pbeq", Z3_ast,
     [Z3_context, ctypes.c_uint, ctypes.POINTER(Z3_ast),
      ctypes.POINTER(ctypes.c_int), ctypes.c_int]),

    # Arithmetic
    ("Z3_mk_add", Z3_ast, [Z3_context, ctypes.c_uint, ctypes.POINTER(Z3_ast)]),
    ("Z3_mk_mul", Z3_ast, [Z3_context, ctypes.c_uint, ctypes.POINTER(Z3_ast)]),
    ("Z3_mk_sub", Z3_ast, [Z3_context, ctypes.c_uint, ctypes.POINTER(Z3_ast)]),
    ("Z3_mk_unary_minus", Z3_ast, [Z3_context, Z3_ast]),
    ("Z3_mk_div", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_mod", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_lt", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_le", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_gt", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_ge", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    # Int<->Real coercions (z3py inserts ToReal on the Int side of a mixed
    # Int/Real arithmetic, comparison or ite term).
    ("Z3_mk_int2real", Z3_ast, [Z3_context, Z3_ast]),
    ("Z3_mk_real2int", Z3_ast, [Z3_context, Z3_ast]),
    # Real "is an integer" predicate (z3py IsInt) and real exponentiation
    # (z3py Sqrt/Cbrt build `base ^ (1/2)` / `base ^ (1/3)` over this).
    ("Z3_mk_is_int", Z3_ast, [Z3_context, Z3_ast]),
    ("Z3_mk_power", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),

    # Bitvector ops (subset for the core slice)
    ("Z3_mk_bvadd", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_bvsub", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_bvmul", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_bvand", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_bvor", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_bvxor", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_bvnot", Z3_ast, [Z3_context, Z3_ast]),
    ("Z3_mk_bvneg", Z3_ast, [Z3_context, Z3_ast]),
    ("Z3_mk_bvult", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_bvule", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_bvugt", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_bvuge", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_bvslt", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_bvsle", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_bvsgt", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_bvsge", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),

    # Bitvector ops added in B-10: division/remainder/mod, shifts, width-changing
    # (extract/concat/extend/repeat/rotate), Int<->BV conversion, reductions, and
    # overflow/underflow predicates. libay_ffi already exports all of these; these
    # ctypes prototypes wire them through to the high-level BV wrappers.
    ("Z3_mk_bvudiv", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_bvsdiv", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_bvurem", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_bvsrem", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_bvsmod", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_bvshl", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_bvlshr", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_bvashr", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_concat", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_extract", Z3_ast, [Z3_context, ctypes.c_uint, ctypes.c_uint, Z3_ast]),
    ("Z3_mk_sign_ext", Z3_ast, [Z3_context, ctypes.c_uint, Z3_ast]),
    ("Z3_mk_zero_ext", Z3_ast, [Z3_context, ctypes.c_uint, Z3_ast]),
    ("Z3_mk_repeat", Z3_ast, [Z3_context, ctypes.c_uint, Z3_ast]),
    ("Z3_mk_rotate_left", Z3_ast, [Z3_context, ctypes.c_uint, Z3_ast]),
    ("Z3_mk_rotate_right", Z3_ast, [Z3_context, ctypes.c_uint, Z3_ast]),
    ("Z3_mk_bv2int", Z3_ast, [Z3_context, Z3_ast, ctypes.c_bool]),
    ("Z3_mk_int2bv", Z3_ast, [Z3_context, ctypes.c_uint, Z3_ast]),
    ("Z3_mk_bvredand", Z3_ast, [Z3_context, Z3_ast]),
    ("Z3_mk_bvredor", Z3_ast, [Z3_context, Z3_ast]),
    ("Z3_mk_bvadd_no_overflow", Z3_ast, [Z3_context, Z3_ast, Z3_ast, ctypes.c_bool]),
    ("Z3_mk_bvadd_no_underflow", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_bvsub_no_overflow", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_bvsub_no_underflow", Z3_ast, [Z3_context, Z3_ast, Z3_ast, ctypes.c_bool]),
    ("Z3_mk_bvmul_no_overflow", Z3_ast, [Z3_context, Z3_ast, Z3_ast, ctypes.c_bool]),
    ("Z3_mk_bvmul_no_underflow", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_bvsdiv_no_overflow", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),

    # AST / numeral inspection
    ("Z3_get_sort", Z3_sort, [Z3_context, Z3_ast]),
    ("Z3_get_numeral_string", Z3_string, [Z3_context, Z3_ast]),
    ("Z3_get_bool_value", ctypes.c_int, [Z3_context, Z3_ast]),
    ("Z3_ast_to_string", Z3_string, [Z3_context, Z3_ast]),
    ("Z3_sort_to_string", Z3_string, [Z3_context, Z3_sort]),

    # AST introspection (used to rebuild an expr in a different context).
    # Z3_ast is a u64 handle, so these MUST be declared or ctypes truncates
    # the handle to c_int and the call segfaults.
    ("Z3_get_ast_kind", ctypes.c_uint, [Z3_context, Z3_ast]),
    ("Z3_is_numeral_ast", ctypes.c_bool, [Z3_context, Z3_ast]),
    ("Z3_is_app", ctypes.c_bool, [Z3_context, Z3_ast]),
    ("Z3_get_app_decl", Z3_func_decl, [Z3_context, Z3_ast]),
    ("Z3_get_app_num_args", ctypes.c_uint, [Z3_context, Z3_ast]),
    ("Z3_get_app_arg", Z3_ast, [Z3_context, Z3_ast, ctypes.c_uint]),
    ("Z3_get_decl_kind", ctypes.c_uint, [Z3_context, Z3_func_decl]),
    ("Z3_get_decl_num_parameters", ctypes.c_uint, [Z3_context, Z3_func_decl]),
    ("Z3_get_decl_int_parameter", ctypes.c_int, [Z3_context, Z3_func_decl, ctypes.c_uint]),

    # Arrays
    ("Z3_mk_array_sort", Z3_sort, [Z3_context, Z3_sort, Z3_sort]),
    ("Z3_get_array_sort_domain", Z3_sort, [Z3_context, Z3_sort]),
    ("Z3_get_array_sort_range", Z3_sort, [Z3_context, Z3_sort]),
    ("Z3_mk_select", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_store", Z3_ast, [Z3_context, Z3_ast, Z3_ast, Z3_ast]),
    ("Z3_mk_const_array", Z3_ast, [Z3_context, Z3_sort, Z3_ast]),
    ("Z3_mk_map", Z3_ast,
     [Z3_context, Z3_func_decl, ctypes.c_uint, ctypes.POINTER(Z3_ast)]),
    ("Z3_mk_array_ext", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),

    # Uninterpreted functions
    ("Z3_mk_func_decl", Z3_func_decl,
     [Z3_context, Z3_symbol, ctypes.c_uint, ctypes.POINTER(Z3_sort), Z3_sort]),
    ("Z3_mk_app", Z3_ast,
     [Z3_context, Z3_func_decl, ctypes.c_uint, ctypes.POINTER(Z3_ast)]),
    ("Z3_get_range", Z3_sort, [Z3_context, Z3_func_decl]),
    ("Z3_get_domain", Z3_sort, [Z3_context, Z3_func_decl, ctypes.c_uint]),

    # Recursive function definitions (RecFunction / RecAddDefinition). The decl
    # is declared with Z3_mk_rec_func_decl; Z3_add_rec_def attaches the body
    # (AY registers it for check-time bounded expansion — fail-closed: a goal
    # whose rec applications cannot be fully expanded never certifies `sat`).
    ("Z3_mk_rec_func_decl", Z3_func_decl,
     [Z3_context, Z3_symbol, ctypes.c_uint, ctypes.POINTER(Z3_sort), Z3_sort]),
    ("Z3_add_rec_def", None,
     [Z3_context, Z3_func_decl, ctypes.c_uint, ctypes.POINTER(Z3_ast), Z3_ast]),

    # Algebraic datatypes (Datatype / EnumSort / TupleSort). The multi-step Z3
    # workflow: build constructor descriptors, create the datatype sort, then
    # query the constructor/recognizer/accessor func_decls back out. `Z3_sort`
    # entries in `sorts` may be null to denote a (recursive) self-reference.
    ("Z3_get_sort_name", Z3_symbol, [Z3_context, Z3_sort]),
    ("Z3_mk_constructor", Z3_constructor,
     [Z3_context, Z3_symbol, Z3_symbol, ctypes.c_uint, ctypes.POINTER(Z3_symbol),
      ctypes.POINTER(Z3_sort), ctypes.POINTER(ctypes.c_uint)]),
    ("Z3_mk_constructor_list", Z3_constructor_list,
     [Z3_context, ctypes.c_uint, ctypes.POINTER(Z3_constructor)]),
    ("Z3_mk_datatype", Z3_sort,
     [Z3_context, Z3_symbol, ctypes.c_uint, ctypes.POINTER(Z3_constructor)]),
    ("Z3_mk_datatypes", None,
     [Z3_context, ctypes.c_uint, ctypes.POINTER(Z3_symbol), ctypes.POINTER(Z3_sort),
      ctypes.POINTER(Z3_constructor_list)]),
    ("Z3_query_constructor", None,
     [Z3_context, Z3_constructor, ctypes.c_uint, ctypes.POINTER(Z3_func_decl),
      ctypes.POINTER(Z3_func_decl), ctypes.POINTER(Z3_func_decl)]),
    ("Z3_del_constructor", None, [Z3_context, Z3_constructor]),
    ("Z3_del_constructor_list", None, [Z3_context, Z3_constructor_list]),

    # Quantifiers (constant style — bound vars are app-consts, not de Bruijn)
    ("Z3_mk_forall_const", Z3_ast,
     [Z3_context, ctypes.c_uint, ctypes.c_uint, ctypes.POINTER(Z3_ast),
      ctypes.c_uint, ctypes.POINTER(Z3_pattern), Z3_ast]),
    ("Z3_mk_exists_const", Z3_ast,
     [Z3_context, ctypes.c_uint, ctypes.c_uint, ctypes.POINTER(Z3_ast),
      ctypes.c_uint, ctypes.POINTER(Z3_pattern), Z3_ast]),

    # Quantifier introspection (used by the cross-context rebuild).
    ("Z3_get_quantifier_num_bound", ctypes.c_uint, [Z3_context, Z3_ast]),
    ("Z3_get_quantifier_bound_name", Z3_symbol, [Z3_context, Z3_ast, ctypes.c_uint]),
    ("Z3_get_quantifier_bound_sort", Z3_sort, [Z3_context, Z3_ast, ctypes.c_uint]),
    ("Z3_get_quantifier_body", Z3_ast, [Z3_context, Z3_ast]),
    ("Z3_is_quantifier_forall", ctypes.c_bool, [Z3_context, Z3_ast]),
    ("Z3_is_quantifier_exists", ctypes.c_bool, [Z3_context, Z3_ast]),
    # Trigger patterns (B-10): build a pattern from term(s), and read back a
    # quantifier's pattern count.
    ("Z3_mk_pattern", Z3_pattern, [Z3_context, ctypes.c_uint, ctypes.POINTER(Z3_ast)]),
    ("Z3_get_quantifier_num_patterns", ctypes.c_uint, [Z3_context, Z3_ast]),

    # Sequences & strings
    ("Z3_mk_string_sort", Z3_sort, [Z3_context]),
    ("Z3_mk_string", Z3_ast, [Z3_context, Z3_string]),
    ("Z3_mk_seq_concat", Z3_ast, [Z3_context, ctypes.c_uint, ctypes.POINTER(Z3_ast)]),
    ("Z3_mk_seq_length", Z3_ast, [Z3_context, Z3_ast]),
    ("Z3_mk_seq_contains", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_seq_prefix", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_seq_suffix", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_seq_index", Z3_ast, [Z3_context, Z3_ast, Z3_ast, Z3_ast]),
    ("Z3_mk_seq_extract", Z3_ast, [Z3_context, Z3_ast, Z3_ast, Z3_ast]),
    ("Z3_mk_seq_replace", Z3_ast, [Z3_context, Z3_ast, Z3_ast, Z3_ast]),
    ("Z3_mk_seq_at", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_seq_nth", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_seq_unit", Z3_ast, [Z3_context, Z3_ast]),
    # String <-> Int conversions (z3py IntToStr / StrToInt; SMT-LIB
    # str.from_int / str.to_int).
    ("Z3_mk_int_to_str", Z3_ast, [Z3_context, Z3_ast]),
    ("Z3_mk_str_to_int", Z3_ast, [Z3_context, Z3_ast]),
    # Sequence sort constructor (z3py SeqSort; `(Seq elem)`).
    ("Z3_mk_seq_sort", Z3_sort, [Z3_context, Z3_sort]),
    # String <-> code-point conversions (z3py StrToCode / StrFromCode; SMT-LIB
    # str.to_code / str.from_code).
    ("Z3_mk_string_to_code", Z3_ast, [Z3_context, Z3_ast]),
    ("Z3_mk_string_from_code", Z3_ast, [Z3_context, Z3_ast]),
    # (z3py `LastIndexOf` / SMT `seq.last_indexof` is intentionally NOT bound:
    # AY's decision procedure leaves the result unconstrained on ground inputs,
    # yielding wrong models, so the binding omits it — see __init__.py.)
    # Character theory (z3py CharVal / CharToInt / CharToBv / CharIsDigit). AY
    # models a Char as a bounded-Int code point; the builders below carry that
    # model faithfully. Z3_mk_char takes an unsigned code point.
    ("Z3_mk_char_sort", Z3_sort, [Z3_context]),
    ("Z3_mk_char", Z3_ast, [Z3_context, ctypes.c_uint]),
    ("Z3_mk_char_to_int", Z3_ast, [Z3_context, Z3_ast]),
    ("Z3_mk_char_to_bv", Z3_ast, [Z3_context, Z3_ast]),
    ("Z3_mk_char_is_digit", Z3_ast, [Z3_context, Z3_ast]),

    # Regular expressions (RegLan). Z3_mk_re_sort builds the regex sort (AY's
    # RegLan is monomorphic over strings). str.to_re / str.in_re bridge
    # sequences and regexes; the re.* builders return RegLan. Full/Empty/AllChar
    # take a regex sort (from Z3_mk_re_sort). Z3_ast is a u64 handle, so these
    # MUST be declared or ctypes truncates the handle and the call segfaults.
    ("Z3_mk_re_sort", Z3_sort, [Z3_context, Z3_sort]),
    ("Z3_mk_seq_to_re", Z3_ast, [Z3_context, Z3_ast]),
    ("Z3_mk_seq_in_re", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_re_star", Z3_ast, [Z3_context, Z3_ast]),
    ("Z3_mk_re_plus", Z3_ast, [Z3_context, Z3_ast]),
    ("Z3_mk_re_option", Z3_ast, [Z3_context, Z3_ast]),
    ("Z3_mk_re_complement", Z3_ast, [Z3_context, Z3_ast]),
    ("Z3_mk_re_union", Z3_ast, [Z3_context, ctypes.c_uint, ctypes.POINTER(Z3_ast)]),
    ("Z3_mk_re_concat", Z3_ast, [Z3_context, ctypes.c_uint, ctypes.POINTER(Z3_ast)]),
    ("Z3_mk_re_intersect", Z3_ast, [Z3_context, ctypes.c_uint, ctypes.POINTER(Z3_ast)]),
    ("Z3_mk_re_range", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_re_loop", Z3_ast, [Z3_context, Z3_ast, ctypes.c_uint, ctypes.c_uint]),
    ("Z3_mk_re_full", Z3_ast, [Z3_context, Z3_sort]),
    ("Z3_mk_re_empty", Z3_ast, [Z3_context, Z3_sort]),
    ("Z3_mk_re_allchar", Z3_ast, [Z3_context, Z3_sort]),

    # Solver
    ("Z3_mk_solver", Z3_solver, [Z3_context]),
    ("Z3_solver_push", None, [Z3_context, Z3_solver]),
    ("Z3_solver_pop", None, [Z3_context, Z3_solver, ctypes.c_uint]),
    ("Z3_solver_reset", None, [Z3_context, Z3_solver]),
    ("Z3_solver_assert", None, [Z3_context, Z3_solver, Z3_ast]),
    ("Z3_solver_check", ctypes.c_int, [Z3_context, Z3_solver]),
    ("Z3_solver_check_assumptions", ctypes.c_int,
     [Z3_context, Z3_solver, ctypes.c_uint, ctypes.POINTER(Z3_ast)]),
    ("Z3_solver_get_unsat_core", Z3_ast_vector, [Z3_context, Z3_solver]),
    ("Z3_solver_get_assertions", Z3_ast_vector, [Z3_context, Z3_solver]),
    ("Z3_solver_set_params", None, [Z3_context, Z3_solver, Z3_params]),
    ("Z3_solver_get_reason_unknown", Z3_string, [Z3_context, Z3_solver]),
    ("Z3_solver_get_model", Z3_model, [Z3_context, Z3_solver]),
    ("Z3_solver_to_string", Z3_string, [Z3_context, Z3_solver]),

    # Solver introspection landed in the C ABI: implied unit literals, the
    # non-unit clause set, the current propagation trail, the assertion-stack
    # scope depth, and forward-implication (consequences) enumeration. The
    # ast_vector-returning getters hand back an arena-owned vector; num_scopes
    # returns the number of `push`es not yet `pop`ped. get_consequences takes
    # (assumptions_vec, variables_vec) as INPUT vectors and fills a caller-owned
    # `consequences` OUTPUT vector, returning a Z3_lbool.
    ("Z3_solver_get_units", Z3_ast_vector, [Z3_context, Z3_solver]),
    ("Z3_solver_get_non_units", Z3_ast_vector, [Z3_context, Z3_solver]),
    ("Z3_solver_get_trail", Z3_ast_vector, [Z3_context, Z3_solver]),
    ("Z3_solver_get_num_scopes", ctypes.c_uint, [Z3_context, Z3_solver]),
    ("Z3_solver_get_consequences", ctypes.c_int,
     [Z3_context, Z3_solver, Z3_ast_vector, Z3_ast_vector, Z3_ast_vector]),

    # Solver statistics (Z3_solver_get_statistics + Z3_stats_*). The values are
    # AY's REAL solve counters; keys are AY's honest counters (its set differs
    # from z3's). Z3_stats_get_uint_value returns `unsigned`, get_double_value a
    # C `double`; is_uint/is_double classify each entry.
    ("Z3_solver_get_statistics", Z3_stats, [Z3_context, Z3_solver]),
    ("Z3_stats_inc_ref", None, [Z3_context, Z3_stats]),
    ("Z3_stats_dec_ref", None, [Z3_context, Z3_stats]),
    ("Z3_stats_size", ctypes.c_uint, [Z3_context, Z3_stats]),
    ("Z3_stats_get_key", Z3_string, [Z3_context, Z3_stats, ctypes.c_uint]),
    ("Z3_stats_is_uint", ctypes.c_bool, [Z3_context, Z3_stats, ctypes.c_uint]),
    ("Z3_stats_is_double", ctypes.c_bool, [Z3_context, Z3_stats, ctypes.c_uint]),
    ("Z3_stats_get_uint_value", ctypes.c_uint, [Z3_context, Z3_stats, ctypes.c_uint]),
    ("Z3_stats_get_double_value", ctypes.c_double, [Z3_context, Z3_stats, ctypes.c_uint]),
    ("Z3_stats_to_string", Z3_string, [Z3_context, Z3_stats]),

    # Proof production/retrieval. AY emits Alethe proofs (NOT z3 proof-term
    # ASTs): get_proof_string returns the real Alethe text after an UNSAT check
    # with production enabled, else null. set_proof_production toggles it.
    ("Z3_solver_set_proof_production", None, [Z3_context, Z3_solver, ctypes.c_bool]),
    ("Z3_solver_get_proof_production", ctypes.c_bool, [Z3_context, Z3_solver]),
    ("Z3_solver_get_proof_string", Z3_string, [Z3_context, Z3_solver]),

    # Params (timeout etc.; AY currently honors `timeout` in ms). ref-counting
    # + the full value-setter family (uint/bool/double/symbol) so a Params
    # object mirrors z3py's set() type dispatch exactly.
    ("Z3_mk_params", Z3_params, [Z3_context]),
    ("Z3_params_inc_ref", None, [Z3_context, Z3_params]),
    ("Z3_params_dec_ref", None, [Z3_context, Z3_params]),
    ("Z3_params_set_uint", None, [Z3_context, Z3_params, Z3_symbol, ctypes.c_uint]),
    ("Z3_params_set_bool", None, [Z3_context, Z3_params, Z3_symbol, ctypes.c_bool]),
    ("Z3_params_set_double", None, [Z3_context, Z3_params, Z3_symbol, ctypes.c_double]),
    ("Z3_params_set_symbol", None, [Z3_context, Z3_params, Z3_symbol, Z3_symbol]),

    # Parameter-descriptor sets (Z3_param_descrs). Produced by a tactic's /
    # optimizer's get_param_descrs; queried for names, per-name kinds and docs,
    # and a whole-set string form. AY's descr sets are HONEST-EMPTY (size 0) —
    # its transforms/optimizer expose no per-object tunable that changes the
    # decided model set — but the handle is REAL and fully queryable.
    ("Z3_param_descrs_inc_ref", None, [Z3_context, Z3_param_descrs]),
    ("Z3_param_descrs_dec_ref", None, [Z3_context, Z3_param_descrs]),
    ("Z3_param_descrs_size", ctypes.c_uint, [Z3_context, Z3_param_descrs]),
    ("Z3_param_descrs_get_name", Z3_symbol,
     [Z3_context, Z3_param_descrs, ctypes.c_uint]),
    ("Z3_param_descrs_get_kind", ctypes.c_uint,
     [Z3_context, Z3_param_descrs, Z3_symbol]),
    ("Z3_param_descrs_get_documentation", Z3_string,
     [Z3_context, Z3_param_descrs, Z3_symbol]),
    ("Z3_param_descrs_to_string", Z3_string, [Z3_context, Z3_param_descrs]),
    ("Z3_tactic_get_param_descrs", Z3_param_descrs, [Z3_context, Z3_tactic]),
    ("Z3_optimize_get_param_descrs", Z3_param_descrs, [Z3_context, Z3_optimize]),

    # Global (process-wide) parameters. Z3_global_param_set forwards a
    # stringified key/value to the engine's global config; reset_all clears
    # them. (AY has no Z3_global_param_get, so ayz3 mirrors set values Python-
    # side for read-back — see set_param/get_param.)
    ("Z3_global_param_set", None, [Z3_string, Z3_string]),
    ("Z3_global_param_reset_all", None, []),

    # Symbol introspection (used to read back a param-descr name symbol / a
    # params key). Z3_get_symbol_kind classifies int- vs string-named symbols.
    ("Z3_get_symbol_kind", ctypes.c_uint, [Z3_context, Z3_symbol]),
    ("Z3_get_symbol_int", ctypes.c_int, [Z3_context, Z3_symbol]),

    # AST vectors (unsat cores, parsed assertions, units/trail introspection).
    # Z3_mk_ast_vector + push build the INPUT vectors for get_consequences;
    # inc_ref/dec_ref manage the caller-owned output vector's lifetime.
    ("Z3_mk_ast_vector", Z3_ast_vector, [Z3_context]),
    ("Z3_ast_vector_inc_ref", None, [Z3_context, Z3_ast_vector]),
    ("Z3_ast_vector_dec_ref", None, [Z3_context, Z3_ast_vector]),
    ("Z3_ast_vector_push", None, [Z3_context, Z3_ast_vector, Z3_ast]),
    ("Z3_ast_vector_size", ctypes.c_uint, [Z3_context, Z3_ast_vector]),
    ("Z3_ast_vector_get", Z3_ast, [Z3_context, Z3_ast_vector, ctypes.c_uint]),

    # Simplification (identity in AY — simplifies eagerly during construction)
    ("Z3_simplify", Z3_ast, [Z3_context, Z3_ast]),

    # Simultaneous substitution: replace each `from[i]` with `to[i]` in a term
    # (z3py substitute). All `from`/`to` pairs must be sort-matched.
    ("Z3_substitute", Z3_ast,
     [Z3_context, Z3_ast, ctypes.c_uint, ctypes.POINTER(Z3_ast),
      ctypes.POINTER(Z3_ast)]),

    # SMT-LIB2 parsing
    ("Z3_parse_smtlib2_string", Z3_ast_vector,
     [Z3_context, Z3_string, ctypes.c_uint, ctypes.POINTER(Z3_symbol),
      ctypes.POINTER(Z3_sort), ctypes.c_uint, ctypes.POINTER(Z3_symbol),
      ctypes.POINTER(Z3_func_decl)]),

    # Model
    ("Z3_model_to_string", Z3_string, [Z3_context, Z3_model]),
    ("Z3_model_get_num_consts", ctypes.c_uint, [Z3_context, Z3_model]),
    ("Z3_model_get_const_decl", Z3_func_decl, [Z3_context, Z3_model, ctypes.c_uint]),
    ("Z3_model_get_const_interp", Z3_ast, [Z3_context, Z3_model, Z3_func_decl]),
    ("Z3_model_eval", ctypes.c_bool,
     [Z3_context, Z3_model, Z3_ast, ctypes.c_bool, ctypes.POINTER(Z3_ast)]),
    ("Z3_get_decl_name", Z3_symbol, [Z3_context, Z3_func_decl]),
    ("Z3_get_symbol_string", Z3_string, [Z3_context, Z3_symbol]),

    # Fixedpoint (CHC / Datalog) — backed by ay-chc via the z3_compat FFI.
    # Exactly the 8 Z3_fixedpoint_* entry points the dylib exports (verified
    # via nm): mk / inc_ref / dec_ref / register_relation / add_rule / query /
    # get_answer / to_string. Z3's other fixedpoint C fns (set_params, assert,
    # update_rule, get_cover_delta, ...) are NOT exported.
    ("Z3_mk_fixedpoint", Z3_fixedpoint, [Z3_context]),
    ("Z3_fixedpoint_inc_ref", None, [Z3_context, Z3_fixedpoint]),
    ("Z3_fixedpoint_dec_ref", None, [Z3_context, Z3_fixedpoint]),
    ("Z3_fixedpoint_register_relation",
     None, [Z3_context, Z3_fixedpoint, Z3_func_decl]),
    ("Z3_fixedpoint_add_rule", None, [Z3_context, Z3_fixedpoint, Z3_ast, Z3_symbol]),
    ("Z3_fixedpoint_query", ctypes.c_int, [Z3_context, Z3_fixedpoint, Z3_ast]),
    ("Z3_fixedpoint_get_answer", Z3_string, [Z3_context, Z3_fixedpoint]),
    ("Z3_fixedpoint_to_string", Z3_string, [Z3_context, Z3_fixedpoint]),

    # Optimize
    ("Z3_mk_optimize", Z3_optimize, [Z3_context]),
    ("Z3_optimize_assert", None, [Z3_context, Z3_optimize, Z3_ast]),
    ("Z3_optimize_assert_soft", ctypes.c_uint,
     [Z3_context, Z3_optimize, Z3_ast, Z3_string, Z3_symbol]),
    ("Z3_optimize_maximize", ctypes.c_uint, [Z3_context, Z3_optimize, Z3_ast]),
    ("Z3_optimize_minimize", ctypes.c_uint, [Z3_context, Z3_optimize, Z3_ast]),
    ("Z3_optimize_check", ctypes.c_int,
     [Z3_context, Z3_optimize, ctypes.c_uint, ctypes.POINTER(Z3_ast)]),
    ("Z3_optimize_get_model", Z3_model, [Z3_context, Z3_optimize]),
    ("Z3_optimize_get_lower", Z3_ast, [Z3_context, Z3_optimize, ctypes.c_uint]),
    ("Z3_optimize_get_upper", Z3_ast, [Z3_context, Z3_optimize, ctypes.c_uint]),
    ("Z3_optimize_get_lower_as_vector", Z3_ast_vector,
     [Z3_context, Z3_optimize, ctypes.c_uint]),
    ("Z3_optimize_get_upper_as_vector", Z3_ast_vector,
     [Z3_context, Z3_optimize, ctypes.c_uint]),
    ("Z3_optimize_push", None, [Z3_context, Z3_optimize]),
    ("Z3_optimize_pop", None, [Z3_context, Z3_optimize]),
    ("Z3_optimize_assert_and_track",
     None, [Z3_context, Z3_optimize, Z3_ast, Z3_ast]),
    ("Z3_optimize_get_assertions", Z3_ast_vector, [Z3_context, Z3_optimize]),
    ("Z3_optimize_get_objectives", Z3_ast_vector, [Z3_context, Z3_optimize]),
    ("Z3_optimize_get_unsat_core", Z3_ast_vector, [Z3_context, Z3_optimize]),
    ("Z3_optimize_get_statistics", Z3_stats, [Z3_context, Z3_optimize]),
    ("Z3_optimize_get_reason_unknown", Z3_string, [Z3_context, Z3_optimize]),
    ("Z3_optimize_set_params", None, [Z3_context, Z3_optimize, Z3_params]),
    ("Z3_optimize_from_string", None, [Z3_context, Z3_optimize, Z3_string]),
    ("Z3_optimize_from_file", None, [Z3_context, Z3_optimize, Z3_string]),
    ("Z3_optimize_to_string", Z3_string, [Z3_context, Z3_optimize]),
    ("Z3_optimize_get_help", Z3_string, [Z3_context, Z3_optimize]),

    # Tactics (goal-to-goal transformations). Z3_mk_tactic returns NULL for an
    # unknown tactic name (and sets Z3_INVALID_ARG) — the high-level wrapper
    # raises rather than pretending the tactic exists. Z3_mk_solver_from_tactic
    # builds a solver that applies the (equivalence-preserving) tactic to its
    # goal before solving, so the verdict/model equal a plain solver's.
    ("Z3_mk_tactic", Z3_tactic, [Z3_context, Z3_string]),
    # Tactic enumeration/introspection (z3py `tactics()` / `describe_tactics()`).
    ("Z3_get_num_tactics", ctypes.c_uint, [Z3_context]),
    ("Z3_get_tactic_name", Z3_string, [Z3_context, ctypes.c_uint]),
    ("Z3_tactic_get_descr", Z3_string, [Z3_context, Z3_string]),
    ("Z3_tactic_inc_ref", None, [Z3_context, Z3_tactic]),
    ("Z3_tactic_dec_ref", None, [Z3_context, Z3_tactic]),
    ("Z3_tactic_and_then", Z3_tactic, [Z3_context, Z3_tactic, Z3_tactic]),
    ("Z3_tactic_or_else", Z3_tactic, [Z3_context, Z3_tactic, Z3_tactic]),
    ("Z3_tactic_repeat", Z3_tactic, [Z3_context, Z3_tactic, ctypes.c_uint]),
    ("Z3_tactic_using_params", Z3_tactic, [Z3_context, Z3_tactic, Z3_params]),
    ("Z3_tactic_with", Z3_tactic, [Z3_context, Z3_tactic, Z3_params]),
    ("Z3_mk_solver_from_tactic", Z3_solver, [Z3_context, Z3_tactic]),
    ("Z3_tactic_get_help", Z3_string, [Z3_context]),

    # Goals + apply-results (z3py Goal / callable-Tactic surface). A Goal is a set
    # of assertion formulas; Z3_tactic_apply runs a tactic on it and returns the
    # subgoals it produced (each itself a Z3_goal). Ref-counting is a no-op (the
    # handles are arena-owned by the context). Z3_tactic_apply returns NULL and
    # sets Z3_INVALID_ARG on an honest tactic failure — never a fabricated subgoal.
    ("Z3_mk_goal", Z3_goal,
     [Z3_context, ctypes.c_bool, ctypes.c_bool, ctypes.c_bool]),
    ("Z3_goal_inc_ref", None, [Z3_context, Z3_goal]),
    ("Z3_goal_dec_ref", None, [Z3_context, Z3_goal]),
    ("Z3_goal_assert", None, [Z3_context, Z3_goal, Z3_ast]),
    ("Z3_goal_size", ctypes.c_uint, [Z3_context, Z3_goal]),
    ("Z3_goal_formula", Z3_ast, [Z3_context, Z3_goal, ctypes.c_uint]),
    ("Z3_tactic_apply", Z3_apply_result, [Z3_context, Z3_tactic, Z3_goal]),
    ("Z3_apply_result_inc_ref", None, [Z3_context, Z3_apply_result]),
    ("Z3_apply_result_dec_ref", None, [Z3_context, Z3_apply_result]),
    ("Z3_apply_result_get_num_subgoals", ctypes.c_uint,
     [Z3_context, Z3_apply_result]),
    ("Z3_apply_result_get_subgoal", Z3_goal,
     [Z3_context, Z3_apply_result, ctypes.c_uint]),

    # Version (z3py get_version_string / get_version).
    ("Z3_get_version", None, [ctypes.POINTER(ctypes.c_uint),
                              ctypes.POINTER(ctypes.c_uint),
                              ctypes.POINTER(ctypes.c_uint),
                              ctypes.POINTER(ctypes.c_uint)]),

    # ------------------------------------------------------------------
    # Floating-point (IEEE-754) theory — the Z3_mk_fpa_* surface exported by
    # libay_ffi (verified via `nm`). All FP terms are ordinary Z3_ast handles;
    # FP sorts are ordinary Z3_sort handles.
    # ------------------------------------------------------------------
    # Sorts
    ("Z3_mk_fpa_sort", Z3_sort, [Z3_context, ctypes.c_uint, ctypes.c_uint]),
    ("Z3_mk_fpa_sort_half", Z3_sort, [Z3_context]),
    ("Z3_mk_fpa_sort_single", Z3_sort, [Z3_context]),
    ("Z3_mk_fpa_sort_double", Z3_sort, [Z3_context]),
    ("Z3_mk_fpa_sort_quadruple", Z3_sort, [Z3_context]),
    ("Z3_mk_fpa_rounding_mode_sort", Z3_sort, [Z3_context]),
    # Rounding-mode values (short + long constructor names build the same term)
    ("Z3_mk_fpa_rne", Z3_ast, [Z3_context]),
    ("Z3_mk_fpa_rna", Z3_ast, [Z3_context]),
    ("Z3_mk_fpa_rtp", Z3_ast, [Z3_context]),
    ("Z3_mk_fpa_rtn", Z3_ast, [Z3_context]),
    ("Z3_mk_fpa_rtz", Z3_ast, [Z3_context]),
    ("Z3_mk_fpa_round_nearest_ties_to_even", Z3_ast, [Z3_context]),
    ("Z3_mk_fpa_round_nearest_ties_to_away", Z3_ast, [Z3_context]),
    ("Z3_mk_fpa_round_toward_positive", Z3_ast, [Z3_context]),
    ("Z3_mk_fpa_round_toward_negative", Z3_ast, [Z3_context]),
    ("Z3_mk_fpa_round_toward_zero", Z3_ast, [Z3_context]),
    # Values
    ("Z3_mk_fpa_nan", Z3_ast, [Z3_context, Z3_sort]),
    ("Z3_mk_fpa_inf", Z3_ast, [Z3_context, Z3_sort, ctypes.c_bool]),
    ("Z3_mk_fpa_zero", Z3_ast, [Z3_context, Z3_sort, ctypes.c_bool]),
    ("Z3_mk_fpa_numeral_double", Z3_ast, [Z3_context, ctypes.c_double, Z3_sort]),
    ("Z3_mk_fpa_numeral_int", Z3_ast, [Z3_context, ctypes.c_int, Z3_sort]),
    # Arithmetic
    ("Z3_mk_fpa_abs", Z3_ast, [Z3_context, Z3_ast]),
    ("Z3_mk_fpa_neg", Z3_ast, [Z3_context, Z3_ast]),
    ("Z3_mk_fpa_add", Z3_ast, [Z3_context, Z3_ast, Z3_ast, Z3_ast]),
    ("Z3_mk_fpa_sub", Z3_ast, [Z3_context, Z3_ast, Z3_ast, Z3_ast]),
    ("Z3_mk_fpa_mul", Z3_ast, [Z3_context, Z3_ast, Z3_ast, Z3_ast]),
    ("Z3_mk_fpa_div", Z3_ast, [Z3_context, Z3_ast, Z3_ast, Z3_ast]),
    ("Z3_mk_fpa_fma", Z3_ast, [Z3_context, Z3_ast, Z3_ast, Z3_ast, Z3_ast]),
    ("Z3_mk_fpa_sqrt", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_fpa_round_to_integral", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_fpa_rem", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_fpa_min", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_fpa_max", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    # Comparisons
    ("Z3_mk_fpa_eq", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_fpa_lt", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_fpa_leq", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_fpa_gt", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    ("Z3_mk_fpa_geq", Z3_ast, [Z3_context, Z3_ast, Z3_ast]),
    # Classification predicates
    ("Z3_mk_fpa_is_nan", Z3_ast, [Z3_context, Z3_ast]),
    ("Z3_mk_fpa_is_infinite", Z3_ast, [Z3_context, Z3_ast]),
    ("Z3_mk_fpa_is_zero", Z3_ast, [Z3_context, Z3_ast]),
    ("Z3_mk_fpa_is_normal", Z3_ast, [Z3_context, Z3_ast]),
    ("Z3_mk_fpa_is_subnormal", Z3_ast, [Z3_context, Z3_ast]),
    ("Z3_mk_fpa_is_negative", Z3_ast, [Z3_context, Z3_ast]),
    ("Z3_mk_fpa_is_positive", Z3_ast, [Z3_context, Z3_ast]),
    # Conversions
    ("Z3_mk_fpa_to_fp_float", Z3_ast, [Z3_context, Z3_ast, Z3_ast, Z3_sort]),
    ("Z3_mk_fpa_to_fp_signed", Z3_ast, [Z3_context, Z3_ast, Z3_ast, Z3_sort]),
    ("Z3_mk_fpa_to_fp_bv", Z3_ast, [Z3_context, Z3_ast, Z3_sort]),
    ("Z3_mk_fpa_to_fp_real", Z3_ast, [Z3_context, Z3_ast, Z3_ast, Z3_sort]),
    ("Z3_mk_fpa_to_fp_unsigned", Z3_ast, [Z3_context, Z3_ast, Z3_ast, Z3_sort]),
    ("Z3_mk_fpa_to_sbv", Z3_ast, [Z3_context, Z3_ast, Z3_ast, ctypes.c_uint]),
    ("Z3_mk_fpa_to_ubv", Z3_ast, [Z3_context, Z3_ast, Z3_ast, ctypes.c_uint]),
    ("Z3_mk_fpa_to_real", Z3_ast, [Z3_context, Z3_ast]),
    ("Z3_mk_fpa_to_ieee_bv", Z3_ast, [Z3_context, Z3_ast]),
    # Per-field FP construction
    ("Z3_mk_fpa_fp", Z3_ast, [Z3_context, Z3_ast, Z3_ast, Z3_ast]),
    # FP numeral field accessors + classification predicates
    ("Z3_fpa_get_numeral_sign", ctypes.c_bool,
     [Z3_context, Z3_ast, ctypes.POINTER(ctypes.c_int)]),
    ("Z3_fpa_get_numeral_exponent_int64", ctypes.c_bool,
     [Z3_context, Z3_ast, ctypes.POINTER(ctypes.c_int64), ctypes.c_bool]),
    ("Z3_fpa_get_numeral_significand_uint64", ctypes.c_bool,
     [Z3_context, Z3_ast, ctypes.POINTER(ctypes.c_uint64)]),
    ("Z3_fpa_is_numeral_nan", ctypes.c_bool, [Z3_context, Z3_ast]),
    ("Z3_fpa_is_numeral_inf", ctypes.c_bool, [Z3_context, Z3_ast]),
    ("Z3_fpa_is_numeral_zero", ctypes.c_bool, [Z3_context, Z3_ast]),
    ("Z3_fpa_is_numeral_negative", ctypes.c_bool, [Z3_context, Z3_ast]),
]


def _install_signatures():
    for name, restype, argtypes in _SIGS:
        fn = getattr(lib, name)
        fn.restype = restype
        fn.argtypes = argtypes


_install_signatures()
