/* Copyright 2026 Andrew Yates
 * Author: Andrew Yates
 * Licensed under the Apache License, Version 2.0
 *
 * OCaml -> AY C API stubs.
 *
 * These stubs are a thin bridge between OCaml and the AY C API declared in
 * crates/ay-ffi/include/ay.h. They contain no independent solving logic: AY
 * computes verdicts and models after the stubs marshal a request. Correctness
 * still depends on the argument encoding, result mapping, ABI, and handle
 * lifetime behavior in this file.
 *
 * The AYSolver* handle is boxed inside an OCaml custom block so the GC can
 * finalize it (calling ay_solver_free) and so it is never confused with an
 * OCaml-managed pointer. The handle is NULLed on free to make double-free and
 * use-after-free fail closed (every accessor checks for NULL).
 */

#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/fail.h>
#include <caml/custom.h>

#include <string.h>

#include "ay.h"

/* ---- custom block wrapping AYSolver* -------------------------------------- */

#define AYSolver_val(v) (*((AYSolver **) Data_custom_val(v)))

static void ay_solver_finalize(value v) {
    AYSolver *s = AYSolver_val(v);
    if (s != NULL) {
        ay_solver_free(s);
        AYSolver_val(v) = NULL;
    }
}

static struct custom_operations ay_solver_ops = {
    "io.proof-lang.ay.solver",
    ay_solver_finalize,
    custom_compare_default,
    custom_hash_default,
    custom_serialize_default,
    custom_deserialize_default,
    custom_compare_ext_default,
    custom_fixed_length_default
};

/* ---- lifecycle ------------------------------------------------------------ */

CAMLprim value ocaml_ay_solver_new(value unit) {
    CAMLparam1(unit);
    CAMLlocal1(block);
    AYSolver *s = ay_solver_new();
    if (s == NULL) {
        caml_failwith("ay_solver_new: out of memory");
    }
    block = caml_alloc_custom(&ay_solver_ops, sizeof(AYSolver *), 0, 1);
    AYSolver_val(block) = s;
    CAMLreturn(block);
}

/* Explicit free; idempotent. After this the finalizer becomes a no-op. */
CAMLprim value ocaml_ay_solver_free(value v) {
    CAMLparam1(v);
    AYSolver *s = AYSolver_val(v);
    if (s != NULL) {
        ay_solver_free(s);
        AYSolver_val(v) = NULL;
    }
    CAMLreturn(Val_unit);
}

CAMLprim value ocaml_ay_reset(value v) {
    CAMLparam1(v);
    AYSolver *s = AYSolver_val(v);
    if (s != NULL) {
        ay_reset(s);
    }
    CAMLreturn(Val_unit);
}

/* ---- batch / setup -------------------------------------------------------- */

/* Run a block of SMT-LIB commands (set-logic, declarations, ...).
 * Returns the C result code of the last check-sat (or UNKNOWN if none). */
CAMLprim value ocaml_ay_solve_smtlib(value v, value smt) {
    CAMLparam2(v, smt);
    AYSolver *s = AYSolver_val(v);
    if (s == NULL) {
        CAMLreturn(Val_int(AY_ERROR));
    }
    int r = ay_solve_smtlib(s, String_val(smt));
    CAMLreturn(Val_int(r));
}

/* ---- incremental ---------------------------------------------------------- */

CAMLprim value ocaml_ay_assert(value v, value term) {
    CAMLparam2(v, term);
    AYSolver *s = AYSolver_val(v);
    if (s == NULL) {
        CAMLreturn(Val_int(AY_ERROR));
    }
    int r = ay_assert(s, String_val(term));
    CAMLreturn(Val_int(r));
}

CAMLprim value ocaml_ay_check_sat(value v) {
    CAMLparam1(v);
    AYSolver *s = AYSolver_val(v);
    if (s == NULL) {
        CAMLreturn(Val_int(AY_ERROR));
    }
    int r = ay_check_sat(s);
    CAMLreturn(Val_int(r));
}

CAMLprim value ocaml_ay_push(value v) {
    CAMLparam1(v);
    AYSolver *s = AYSolver_val(v);
    if (s != NULL) {
        ay_push(s);
    }
    CAMLreturn(Val_unit);
}

CAMLprim value ocaml_ay_pop(value v, value levels) {
    CAMLparam2(v, levels);
    AYSolver *s = AYSolver_val(v);
    if (s == NULL) {
        CAMLreturn(Val_int(AY_ERROR));
    }
    int r = ay_pop(s, Int_val(levels));
    CAMLreturn(Val_int(r));
}

/* ---- introspection -------------------------------------------------------- */

/* Returns "" when no model / no error is available (OCaml side maps to None). */
CAMLprim value ocaml_ay_get_model(value v) {
    CAMLparam1(v);
    CAMLlocal1(out);
    AYSolver *s = AYSolver_val(v);
    char *m = (s == NULL) ? NULL : ay_get_model(s);
    if (m == NULL) {
        out = caml_copy_string("");
    } else {
        out = caml_copy_string(m);
        ay_string_free(m);
    }
    CAMLreturn(out);
}

CAMLprim value ocaml_ay_get_error(value v) {
    CAMLparam1(v);
    CAMLlocal1(out);
    AYSolver *s = AYSolver_val(v);
    char *e = (s == NULL) ? NULL : ay_get_error(s);
    if (e == NULL) {
        out = caml_copy_string("");
    } else {
        out = caml_copy_string(e);
        ay_string_free(e);
    }
    CAMLreturn(out);
}

CAMLprim value ocaml_ay_version(value unit) {
    CAMLparam1(unit);
    CAMLlocal1(out);
    char *vstr = ay_version();
    if (vstr == NULL) {
        out = caml_copy_string("");
    } else {
        out = caml_copy_string(vstr);
        ay_string_free(vstr);
    }
    CAMLreturn(out);
}
