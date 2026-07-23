// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible `Probe` sub-API — numeric/boolean queries over a goal.
//!
//! A *probe* inspects a goal and returns a `double` (a "Boolean" probe returns
//! `1.0`/`0.0`). Probes drive tactic selection (`when` / `fail-if`) and let a
//! caller classify a goal — its size, its constant counts, its logic fragment.
//!
//! This exposes the subset of the Z3 `Z3_probe_*` C API that z3py's `Probe`
//! surface uses, backed by AY's [`ay_frontend::Probe`] — the SAME probe
//! representation and the SAME evaluator the SMT-LIB `(apply (when <probe> …))`
//! path uses (via [`ay_dpll::api::Solver::apply_probe`]). So `Z3_probe_apply`
//! returns the REAL value AY's engine computes over the goal's formulas — never
//! a fabricated number — and matches libz3's built-in probes exactly on the
//! supported set (cross-checked against libz3 on LIA/LRA/LIRA/NIA/BV/UF/
//! quantified goals).
//!
//! # Supported probe names (honest handling of the rest)
//!
//! `Z3_mk_probe` recognizes the names in [`SUPPORTED_PROBES`] via the shared
//! front-end parser ([`ay_frontend::Probe::parse`]), so this C-API surface and
//! the SMT-LIB `when`/`fail-if` surface recognize an identical set — EVERY
//! probe name z3 4.15.4 exposes (42, `z3 -probes`). The structural and
//! logic-fragment probes are computed exactly; probes AY cannot compute
//! exactly evaluate CONSERVATIVELY, and each such entry's description text
//! says so (a probe value only selects between two sound tactics, so a
//! conservative value can never flip a verdict — and it is never a fabricated
//! reading dressed up as z3's). A name z3 itself does not have returns NULL
//! and sets `Z3_INVALID_ARG`.
//!
//! Ref-counting (`Z3_probe_inc_ref`/`_dec_ref`) is bookkeeping-only: probe
//! handles are arena-owned by the context and freed by `Z3_del_context`,
//! mirroring the goal/tactic/apply-result handle discipline.

use std::ptr;

use ay_frontend::{Probe, ProbeCmp, SExpr};

use super::{
    cache_probe, cache_string, ffi_guard_const_ptr, ffi_guard_double, ffi_guard_ptr,
    ffi_guard_uint, ffi_read_bounded_text, require_term_asts_or_return, Z3_context, Z3_goal,
    Z3_probe, Z3_string, Z3_INVALID_ARG, Z3_OK,
};
use std::os::raw::{c_double, c_uint};

/// The probe names AY implements, each with Z3's own description text.
///
/// `Z3_get_num_probes`/`Z3_get_probe_name`/`Z3_probe_get_descr` report exactly
/// this set. Every name here is accepted by `Z3_mk_probe` (the parser and this
/// list are kept in lock-step), so the introspection surface never advertises a
/// probe the constructor would reject.
pub(crate) const SUPPORTED_PROBES: &[(&str, &str)] = &[
    ("size", "number of assertions in the given goal."),
    (
        "num-exprs",
        "number of expressions/terms in the given goal.",
    ),
    (
        "num-consts",
        "number of non Boolean constants in the given goal.",
    ),
    (
        "num-bool-consts",
        "number of Boolean constants in the given goal.",
    ),
    (
        "num-arith-consts",
        "number of arithmetic constants in the given goal.",
    ),
    (
        "num-bv-consts",
        "number of bit-vector constants in the given goal.",
    ),
    ("depth", "depth of the input goal."),
    ("has-quantifiers", "true if the goal contains quantifiers."),
    (
        "is-propositional",
        "true if the goal is in propositional logic.",
    ),
    ("is-qfbv", "true if the goal is in QF_BV."),
    ("is-qflia", "true if the goal is in QF_LIA."),
    ("is-qflra", "true if the goal is in QF_LRA."),
    ("is-qflira", "true if the goal is in QF_LIRA."),
    (
        "is-lia",
        "true if the goal is in LIA (linear integer arithmetic, formula may have quantifiers).",
    ),
    (
        "is-lra",
        "true if the goal is in LRA (linear real arithmetic, formula may have quantifiers).",
    ),
    (
        "is-lira",
        "true if the goal is in LIRA (linear integer and real arithmetic, formula may have quantifiers).",
    ),
    (
        "is-qfnia",
        "true if the goal is in QF_NIA (quantifier-free nonlinear integer arithmetic).",
    ),
    (
        "is-qfnra",
        "true if the goal is in QF_NRA (quantifier-free nonlinear real arithmetic).",
    ),
    (
        "is-nia",
        "true if the goal is in NIA (nonlinear integer arithmetic, formula may have quantifiers).",
    ),
    (
        "is-nra",
        "true if the goal is in NRA (nonlinear real arithmetic, formula may have quantifiers).",
    ),
    // ------------------------------------------------------------------
    // Full z3-4.15.4 probe-name coverage (z3 -probes lists 42 names). Each
    // entry carries z3's own description; where AY's evaluation is a
    // documented conservative approximation rather than an exact computation,
    // the description says so (honesty over byte-parity). A probe value only
    // selects between two SOUND tactics, so an approximation can never flip a
    // verdict. See `ay_frontend::Probe` for the per-probe evaluation contract.
    // ------------------------------------------------------------------
    (
        "has-patterns",
        "true if the goal contains quantifiers with patterns.",
    ),
    ("is-ilp", "true if the goal is ILP."),
    (
        "is-nira",
        "true if the goal is in NIRA (nonlinear integer and real arithmetic).",
    ),
    (
        "is-pb",
        "true if the goal is a pseudo-boolean problem. (AY: evaluates the propositional core; a documented conservative under-approximation.)",
    ),
    (
        "is-quasi-pb",
        "true if the goal is quasi-pb. (AY: evaluates the propositional core; a documented conservative under-approximation.)",
    ),
    (
        "is-qfaufbv",
        "true if the goal is in QF_AUFBV. (AY: evaluates the bool/BV core; arrays/UF read 0 — a documented conservative under-approximation.)",
    ),
    (
        "is-qfauflia",
        "true if the goal is in QF_AUFLIA. (AY: evaluates the bool/LIA core; arrays/UF read 0 — a documented conservative under-approximation.)",
    ),
    (
        "is-qfbv-eq",
        "true if the goal is in a fragment of QF_BV which uses only =, extract, concat. (AY: reads 0 on any bit-vector-term goal — a documented conservative under-approximation.)",
    ),
    (
        "is-qffp",
        "true if the goal is in QF_FP (floats). (AY: evaluates the measured bool/BV core; genuine FP terms read 0 — a documented conservative under-approximation.)",
    ),
    (
        "is-qffpbv",
        "true if the goal is in QF_FPBV (floats+bit-vectors). (AY: evaluates the measured bool/BV core; genuine FP terms read 0 — a documented conservative under-approximation.)",
    ),
    (
        "is-qffplra",
        "true if the goal is in QF_FPLRA. (AY: conservative constant 0 — AY cannot classify FP terms and never claims membership; measured z3 reads 0 on FP-free goals too.)",
    ),
    (
        "is-qfufnra",
        "true if the goal is QF_UFNRA (quantifier-free nonlinear arithmetic with other theories). (AY: evaluates the nonlinear-real core; UF goals read 0 — a documented conservative under-approximation.)",
    ),
    (
        "is-unbounded",
        "true if the goal contains integer/real constants that do not have lower/upper bounds. (AY: a light var-vs-numeral bound scan over the top-level atoms — a documented approximation of z3's bound manager.)",
    ),
    (
        "ackr-bound-probe",
        "A probe to give an upper bound of Ackermann congruence lemmas that a formula might generate.",
    ),
    (
        "arith-avg-bw",
        "avg coefficient bit width. (AY: computed over every arithmetic numeral in the goal — a documented approximation of z3's per-atom coefficient harvesting.)",
    ),
    (
        "arith-max-bw",
        "max coefficient bit width. (AY: computed over every arithmetic numeral in the goal — a documented approximation of z3's per-atom coefficient harvesting.)",
    ),
    (
        "arith-avg-deg",
        "avg polynomial total degree of an arithmetic atom.",
    ),
    (
        "arith-max-deg",
        "max polynomial total degree of an arithmetic atom.",
    ),
    (
        "memory",
        "amount of used memory in megabytes. (AY: conservative constant 0 — AY does not meter allocator usage and never fabricates a reading.)",
    ),
    (
        "produce-model",
        "true if model generation is enabled for the given goal. (AY goals always support model extraction, matching z3's default goal.)",
    ),
    (
        "produce-proofs",
        "true if proof generation is enabled for the given goal. (AY apply-goals never carry proof mode, matching z3's default goal.)",
    ),
    (
        "produce-unsat-cores",
        "true if unsat-core generation is enabled for the given goal. (AY apply-goals never carry core mode, matching z3's default goal.)",
    ),
];

/// Create a probe by name.
///
/// Recognizes [`SUPPORTED_PROBES`] via the shared front-end parser
/// ([`ay_frontend::Probe::parse`]) — the same parser the SMT-LIB
/// `(apply (when <probe> …))` path uses. Any unknown or unsupported name
/// (including real Z3 probes AY does not implement) returns NULL and sets
/// `Z3_INVALID_ARG`; it never fabricates a probe.
///
/// # Safety
/// `c` must be a valid context pointer; `name`, when non-null, a null-terminated
/// C string.
#[no_mangle]
pub unsafe extern "C" fn Z3_mk_probe(c: Z3_context, name: Z3_string) -> Z3_probe {
    // Pre-extract the name string outside the guard (raw-pointer deref).
    let name_str: Option<String> = if name.is_null() {
        None
    } else {
        // SAFETY: caller contract guarantees `name`, when non-null, is a valid
        // null-terminated C string owned for the duration of this call.
        match unsafe { ffi_read_bounded_text(name) } {
            Ok(s) => Some(s),
            Err(_) => Some(String::new()), // non-UTF-8 -> unsupported below
        }
    };

    // SAFETY: `c` is the caller-supplied context pointer; `ffi_guard_ptr` handles
    // the null case and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let Some(ref n) = name_str else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_mk_probe: null probe name".to_string());
                return ptr::null_mut();
            };
            match Probe::parse(&SExpr::Symbol(n.clone())) {
                Ok(probe) => {
                    ctx.last_error = Z3_OK;
                    cache_probe(ctx, probe)
                }
                Err(e) => {
                    // HONEST: unknown/unsupported probe name -> NULL + error. The
                    // diagnostic comes straight from the shared registry parser.
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some(format!("Z3_mk_probe: {e}"));
                    ptr::null_mut()
                }
            }
        })
    }
}

/// Increment a probe's reference count (bookkeeping no-op — arena-owned).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_probe_inc_ref(_c: Z3_context, _p: Z3_probe) {}

/// Decrement a probe's reference count (bookkeeping no-op — arena-owned).
///
/// # Safety
/// Pointers must be valid.
#[no_mangle]
pub unsafe extern "C" fn Z3_probe_dec_ref(_c: Z3_context, _p: Z3_probe) {}

/// Return a probe that always evaluates to `val` (Z3's `Z3_probe_const`).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_probe_const(c: Z3_context, val: c_double) -> Z3_probe {
    // SAFETY: `ffi_guard_ptr` handles a null context and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            ctx.last_error = Z3_OK;
            // Store the value as its round-trippable text (the `Probe::Const`
            // representation), parsed back to `f64` at evaluation time.
            cache_probe(ctx, Probe::Const(val.to_string()))
        })
    }
}

/// Which comparison a probe combinator builds.
#[derive(Clone, Copy)]
enum Cmp {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    And,
    Or,
}

/// Shared builder for the binary probe combinators.
///
/// # Safety
/// `c` must be a valid context pointer; `p1`/`p2`, when non-null, valid probe
/// handles.
unsafe fn combine_probes(c: Z3_context, p1: Z3_probe, p2: Z3_probe, op: Cmp) -> Z3_probe {
    // Pre-extract the operand probes outside the guard (raw-pointer deref).
    // SAFETY: each handle, when non-null, is a live `ProbeHandle` kept in the
    // context's `probe_cache` (single-threaded per context). `as_ref` null-checks.
    let a = unsafe { p1.as_ref() }.map(|h| h.probe.clone());
    let b = unsafe { p2.as_ref() }.map(|h| h.probe.clone());

    // SAFETY: `ffi_guard_ptr` handles a null context and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let (Some(a), Some(b)) = (a, b) else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_probe combinator: null probe operand".to_string());
                return ptr::null_mut();
            };
            let (ba, bb) = (Box::new(a), Box::new(b));
            let probe = match op {
                Cmp::Lt => Probe::Cmp(ProbeCmp::Lt, ba, bb),
                Cmp::Le => Probe::Cmp(ProbeCmp::Le, ba, bb),
                Cmp::Gt => Probe::Cmp(ProbeCmp::Gt, ba, bb),
                Cmp::Ge => Probe::Cmp(ProbeCmp::Ge, ba, bb),
                Cmp::Eq => Probe::Cmp(ProbeCmp::Eq, ba, bb),
                Cmp::And => Probe::And(ba, bb),
                Cmp::Or => Probe::Or(ba, bb),
            };
            ctx.last_error = Z3_OK;
            cache_probe(ctx, probe)
        })
    }
}

/// Probe: `p1 < p2` (Boolean; `1.0`/`0.0`). Null operand → NULL + `Z3_INVALID_ARG`.
///
/// # Safety
/// `c` must be a valid context pointer; `p1`/`p2`, when non-null, valid handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_probe_lt(c: Z3_context, p1: Z3_probe, p2: Z3_probe) -> Z3_probe {
    // SAFETY: forwarded under the caller's contract.
    unsafe { combine_probes(c, p1, p2, Cmp::Lt) }
}

/// Probe: `p1 <= p2`. Null operand → NULL + `Z3_INVALID_ARG`.
///
/// # Safety
/// `c` must be a valid context pointer; `p1`/`p2`, when non-null, valid handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_probe_le(c: Z3_context, p1: Z3_probe, p2: Z3_probe) -> Z3_probe {
    // SAFETY: forwarded under the caller's contract.
    unsafe { combine_probes(c, p1, p2, Cmp::Le) }
}

/// Probe: `p1 > p2`. Null operand → NULL + `Z3_INVALID_ARG`.
///
/// # Safety
/// `c` must be a valid context pointer; `p1`/`p2`, when non-null, valid handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_probe_gt(c: Z3_context, p1: Z3_probe, p2: Z3_probe) -> Z3_probe {
    // SAFETY: forwarded under the caller's contract.
    unsafe { combine_probes(c, p1, p2, Cmp::Gt) }
}

/// Probe: `p1 >= p2`. Null operand → NULL + `Z3_INVALID_ARG`.
///
/// # Safety
/// `c` must be a valid context pointer; `p1`/`p2`, when non-null, valid handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_probe_ge(c: Z3_context, p1: Z3_probe, p2: Z3_probe) -> Z3_probe {
    // SAFETY: forwarded under the caller's contract.
    unsafe { combine_probes(c, p1, p2, Cmp::Ge) }
}

/// Probe: `p1 == p2`. Null operand → NULL + `Z3_INVALID_ARG`.
///
/// # Safety
/// `c` must be a valid context pointer; `p1`/`p2`, when non-null, valid handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_probe_eq(c: Z3_context, p1: Z3_probe, p2: Z3_probe) -> Z3_probe {
    // SAFETY: forwarded under the caller's contract.
    unsafe { combine_probes(c, p1, p2, Cmp::Eq) }
}

/// Probe: `p1` and `p2` (both nonzero). Null operand → NULL + `Z3_INVALID_ARG`.
///
/// # Safety
/// `c` must be a valid context pointer; `p1`/`p2`, when non-null, valid handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_probe_and(c: Z3_context, p1: Z3_probe, p2: Z3_probe) -> Z3_probe {
    // SAFETY: forwarded under the caller's contract.
    unsafe { combine_probes(c, p1, p2, Cmp::And) }
}

/// Probe: `p1` or `p2` (either nonzero). Null operand → NULL + `Z3_INVALID_ARG`.
///
/// # Safety
/// `c` must be a valid context pointer; `p1`/`p2`, when non-null, valid handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_probe_or(c: Z3_context, p1: Z3_probe, p2: Z3_probe) -> Z3_probe {
    // SAFETY: forwarded under the caller's contract.
    unsafe { combine_probes(c, p1, p2, Cmp::Or) }
}

/// Probe: logical negation of `p` (Z3's `Z3_probe_not`). Null → NULL +
/// `Z3_INVALID_ARG`.
///
/// # Safety
/// `c` must be a valid context pointer; `p`, when non-null, a valid handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_probe_not(c: Z3_context, p: Z3_probe) -> Z3_probe {
    // Pre-extract the operand probe outside the guard (raw-pointer deref).
    // SAFETY: `p`, when non-null, is a live `ProbeHandle`; `as_ref` null-checks.
    let inner = unsafe { p.as_ref() }.map(|h| h.probe.clone());
    // SAFETY: `ffi_guard_ptr` handles a null context and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let Some(inner) = inner else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_probe_not: null probe handle".to_string());
                return ptr::null_mut();
            };
            ctx.last_error = Z3_OK;
            cache_probe(ctx, Probe::Not(Box::new(inner)))
        })
    }
}

/// Execute probe `p` over goal `g`, returning the REAL `double` the probe
/// computes (Z3's `Z3_probe_apply`). Boolean probes return `1.0`/`0.0`.
///
/// Routes through the SAME engine evaluator the SMT-LIB `when`/`fail-if` path
/// uses ([`ay_dpll::api::Solver::apply_probe`]), over the goal's real formulas
/// and its transformation depth — never a fabricated value. A null probe or goal
/// yields `0.0` and sets `Z3_INVALID_ARG`.
///
/// # Safety
/// `c` must be a valid context pointer; `p`/`g`, when non-null, valid handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_probe_apply(c: Z3_context, p: Z3_probe, g: Z3_goal) -> c_double {
    // Pre-extract the probe and the goal's formulas + depth (raw-pointer derefs).
    // SAFETY: both handles, when non-null, are arena-owned by the context and
    // single-threaded per context; `as_ref` null-checks.
    let probe = unsafe { p.as_ref() }.map(|h| h.probe.clone());
    let goal_data = unsafe { g.as_ref() }.map(|h| (h.formulas.clone(), h.depth));

    // SAFETY: `ffi_guard_double` handles a null context and catches panics.
    unsafe {
        ffi_guard_double(c, 0.0, |ctx| {
            let (Some(probe), Some((formulas, depth))) = (probe, goal_data) else {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_probe_apply: null probe or goal handle".to_string());
                return 0.0;
            };
            let terms = require_term_asts_or_return!(ctx, &formulas, "Z3_probe_apply", 0.0);
            ctx.last_error = Z3_OK;
            ctx.solver.apply_probe(&probe, &terms, depth)
        })
    }
}

/// Return the number of built-in probes AY implements (Z3's `Z3_get_num_probes`).
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_num_probes(c: Z3_context) -> c_uint {
    // SAFETY: `ffi_guard_uint` handles a null context and catches panics.
    unsafe {
        ffi_guard_uint(c, 0, |ctx| {
            ctx.last_error = Z3_OK;
            SUPPORTED_PROBES.len() as c_uint
        })
    }
}

/// Return the name of the `i`-th probe (Z3's `Z3_get_probe_name`). Out-of-range
/// `i` yields NULL and sets `Z3_INVALID_ARG`.
///
/// # Safety
/// `c` must be a valid context pointer.
#[no_mangle]
pub unsafe extern "C" fn Z3_get_probe_name(c: Z3_context, i: c_uint) -> Z3_string {
    // SAFETY: `ffi_guard_const_ptr` handles a null context and catches panics.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| match SUPPORTED_PROBES.get(i as usize) {
            Some((name, _)) => {
                ctx.last_error = Z3_OK;
                cache_string(ctx, (*name).to_string())
            }
            None => {
                ctx.last_error = Z3_INVALID_ARG;
                ctx.error_msg = Some("Z3_get_probe_name: index out of range".to_string());
                ptr::null()
            }
        })
    }
}

/// Return a description of the probe with the given name (Z3's
/// `Z3_probe_get_descr`). An unsupported name yields NULL and sets
/// `Z3_INVALID_ARG`.
///
/// # Safety
/// `c` must be a valid context pointer; `name`, when non-null, a null-terminated
/// C string.
#[no_mangle]
pub unsafe extern "C" fn Z3_probe_get_descr(c: Z3_context, name: Z3_string) -> Z3_string {
    // Pre-extract the name string outside the guard (raw-pointer deref).
    let name_str: Option<String> = if name.is_null() {
        None
    } else {
        // SAFETY: caller contract guarantees a valid null-terminated C string.
        unsafe { ffi_read_bounded_text(name) }.ok()
    };
    // SAFETY: `ffi_guard_const_ptr` handles a null context and catches panics.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            let descr = name_str
                .as_deref()
                .and_then(|n| SUPPORTED_PROBES.iter().find(|(pn, _)| *pn == n))
                .map(|(_, d)| *d);
            match descr {
                Some(d) => {
                    ctx.last_error = Z3_OK;
                    cache_string(ctx, d.to_string())
                }
                None => {
                    ctx.last_error = Z3_INVALID_ARG;
                    ctx.error_msg = Some("Z3_probe_get_descr: unknown probe name".to_string());
                    ptr::null()
                }
            }
        })
    }
}
