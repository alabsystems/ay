// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `behavior` subcommand — differential BEHAVIOR-PARITY probes for the
//! honest-divergence surface.
//!
//! For each probed C-API function, the SAME minimal valid input sequence is
//! driven through BOTH libraries (dlopen'd side by side, like `diff`), and the
//! observable OUTCOME is classified: `ok-value` / `error` / `null-no-error` /
//! `inert` / a solve verdict. The pair of classes is then judged:
//!
//! * **PARITY** — identical class (and, where a value is compared, identical
//!   value). AY behaves the same as libz3 on that input: errors where it
//!   errors, inert where it is inert.
//! * **GAP(ay-weaker)** — libz3 produces a value/verdict where AY honestly
//!   errors or reports unknown. A REAL remaining capability gap, reported —
//!   never hidden — but not a soundness disagreement.
//! * **LENIENT(ay-stronger)** — AY produces a value where libz3 errors on its
//!   default configuration. Sound but different; reported.
//! * **DISAGREE** — both produce values/verdicts and they CONFLICT (e.g.
//!   sat vs unsat, different widths). This is the failure class: exit != 0.
//!
//! Nothing here trusts either library: every outcome is read back live
//! through the same C ABI an outside consumer would use.

use std::ffi::{c_char, c_int, c_uint, c_void, CStr, CString};
use std::path::Path;

use crate::loader::open_local;
use crate::loader::Library;

/// Handle/AST word: every probed signature passes handles and ASTs in one
/// pointer-sized register on both implementations (libz3: pointers; AY:
/// pointer-or-u64-id), so `usize` is ABI-exact for both.
type W = usize;

/// The on_clause callback shape (`Z3_on_clause_eh`).
type OnClauseEh = unsafe extern "C" fn(*mut c_void, W, c_uint, *const c_uint, W);

/// The raw C entry points the probes drive, resolved per library.
#[allow(non_snake_case)]
struct Api {
    Z3_mk_config: unsafe extern "C" fn() -> W,
    Z3_mk_context: unsafe extern "C" fn(W) -> W,
    Z3_del_config: unsafe extern "C" fn(W),
    Z3_del_context: unsafe extern "C" fn(W),
    Z3_set_error_handler: unsafe extern "C" fn(W, W),
    Z3_get_error_code: unsafe extern "C" fn(W) -> c_uint,
    Z3_get_error_msg: unsafe extern "C" fn(W, c_uint) -> *const c_char,
    Z3_eval_smtlib2_string: unsafe extern "C" fn(W, *const c_char) -> *const c_char,
    Z3_mk_string_symbol: unsafe extern "C" fn(W, *const c_char) -> W,
    Z3_mk_int_sort: unsafe extern "C" fn(W) -> W,
    Z3_mk_bool_sort: unsafe extern "C" fn(W) -> W,
    Z3_mk_bv_sort: unsafe extern "C" fn(W, c_uint) -> W,
    Z3_mk_func_decl: unsafe extern "C" fn(W, W, c_uint, *const W, W) -> W,
    Z3_mk_app: unsafe extern "C" fn(W, W, c_uint, *const W) -> W,
    Z3_mk_int: unsafe extern "C" fn(W, c_int, W) -> W,
    Z3_mk_unsigned_int64: unsafe extern "C" fn(W, u64, W) -> W,
    Z3_mk_true: unsafe extern "C" fn(W) -> W,
    Z3_get_sort: unsafe extern "C" fn(W, W) -> W,
    Z3_get_sort_kind: unsafe extern "C" fn(W, W) -> c_uint,
    Z3_get_bv_sort_size: unsafe extern "C" fn(W, W) -> c_uint,
    Z3_mk_char: unsafe extern "C" fn(W, c_uint) -> W,
    Z3_mk_char_to_bv: unsafe extern "C" fn(W, W) -> W,
    Z3_mk_char_from_bv: unsafe extern "C" fn(W, W) -> W,
    Z3_mk_transitive_closure: unsafe extern "C" fn(W, W) -> W,
    Z3_mk_type_variable: unsafe extern "C" fn(W, W) -> W,
    Z3_get_relation_arity: unsafe extern "C" fn(W, W) -> c_uint,
    Z3_get_relation_column: unsafe extern "C" fn(W, W, c_uint) -> W,
    Z3_mk_solver: unsafe extern "C" fn(W) -> W,
    Z3_solver_register_on_clause: unsafe extern "C" fn(W, W, *mut c_void, OnClauseEh),
    Z3_mk_fixedpoint: unsafe extern "C" fn(W) -> W,
    Z3_fixedpoint_inc_ref: unsafe extern "C" fn(W, W),
    Z3_fixedpoint_register_relation: unsafe extern "C" fn(W, W, W),
    Z3_fixedpoint_init: unsafe extern "C" fn(W, W, *mut c_void),
    Z3_fixedpoint_get_reachable: unsafe extern "C" fn(W, W, W) -> W,
    Z3_fixedpoint_get_cover_delta: unsafe extern "C" fn(W, W, c_int, W) -> W,
    Z3_fixedpoint_add_cover: unsafe extern "C" fn(W, W, c_int, W, W),
    Z3_fixedpoint_add_constraint: unsafe extern "C" fn(W, W, W, c_uint),
    Z3_fixedpoint_set_predicate_representation: unsafe extern "C" fn(W, W, W, c_uint, *const W),
    Z3_fixedpoint_set_reduce_app_callback: unsafe extern "C" fn(W, W, W),
    Z3_fixedpoint_set_reduce_assign_callback: unsafe extern "C" fn(W, W, W),
    Z3_fixedpoint_add_callback: unsafe extern "C" fn(W, W, *mut c_void, W, W, W),
    Z3_mk_params: unsafe extern "C" fn(W) -> W,
    Z3_params_inc_ref: unsafe extern "C" fn(W, W),
    Z3_params_set_symbol: unsafe extern "C" fn(W, W, W, W),
    Z3_fixedpoint_set_params: unsafe extern "C" fn(W, W, W),
}

macro_rules! resolve {
    ($lib:expr, $($name:ident),+ $(,)?) => {{
        Ok::<Api, String>(Api {
            $($name: {
                let mut sym = stringify!($name).as_bytes().to_vec();
                sym.push(0);
                // SAFETY: looked up by its documented Z3 C name and used only
                // at the matching signature declared in `Api`.
                let f = unsafe { $lib.get::<*const c_void>(&sym) }
                    .map_err(|e| format!("missing symbol {}: {e}", stringify!($name)))?;
                // SAFETY: transmute of a dlsym address to its C signature.
                // The target type is the `Api` field's declared signature, one
                // hop away; spelling out all 40+ signatures again here would
                // only invite drift between the annotation and the field.
                #[allow(clippy::missing_transmute_annotations)]
                let f = unsafe { std::mem::transmute::<*const c_void, _>(*f) };
                f
            }),+
        })
    }};
}

fn load(lib: &Library) -> Result<Api, String> {
    resolve!(
        lib,
        Z3_mk_config,
        Z3_mk_context,
        Z3_del_config,
        Z3_del_context,
        Z3_set_error_handler,
        Z3_get_error_code,
        Z3_get_error_msg,
        Z3_eval_smtlib2_string,
        Z3_mk_string_symbol,
        Z3_mk_int_sort,
        Z3_mk_bool_sort,
        Z3_mk_bv_sort,
        Z3_mk_func_decl,
        Z3_mk_app,
        Z3_mk_int,
        Z3_mk_unsigned_int64,
        Z3_mk_true,
        Z3_get_sort,
        Z3_get_sort_kind,
        Z3_get_bv_sort_size,
        Z3_mk_char,
        Z3_mk_char_to_bv,
        Z3_mk_char_from_bv,
        Z3_mk_transitive_closure,
        Z3_mk_type_variable,
        Z3_get_relation_arity,
        Z3_get_relation_column,
        Z3_mk_solver,
        Z3_solver_register_on_clause,
        Z3_mk_fixedpoint,
        Z3_fixedpoint_inc_ref,
        Z3_fixedpoint_register_relation,
        Z3_fixedpoint_init,
        Z3_fixedpoint_get_reachable,
        Z3_fixedpoint_get_cover_delta,
        Z3_fixedpoint_add_cover,
        Z3_fixedpoint_add_constraint,
        Z3_fixedpoint_set_predicate_representation,
        Z3_fixedpoint_set_reduce_app_callback,
        Z3_fixedpoint_set_reduce_assign_callback,
        Z3_fixedpoint_add_callback,
        Z3_mk_params,
        Z3_params_inc_ref,
        Z3_params_set_symbol,
        Z3_fixedpoint_set_params,
    )
}

/// Observable outcome class of one probe against one library.
#[derive(Clone, PartialEq, Eq)]
enum Class {
    /// Produced a value; the string is a canonical value summary (compared).
    OkValue(String),
    /// Set a nonzero error code (message summarized, NOT compared).
    Error,
    /// A void call that completed with the error code still OK.
    Inert,
    /// Solve verdicts from `check-sat` style probes.
    Verdict(&'static str),
}

impl Class {
    fn label(&self) -> String {
        match self {
            Class::OkValue(v) => format!("ok[{v}]"),
            Class::Error => "error".to_string(),
            Class::Inert => "inert".to_string(),
            Class::Verdict(v) => format!("verdict[{v}]"),
        }
    }
}

struct Outcome {
    class: Class,
    detail: String,
}

/// One library's context, wrapped so every probe runs on a FRESH context (an
/// error on a shared context could poison later probes).
struct Session<'a> {
    api: &'a Api,
    ctx: W,
}

impl<'a> Session<'a> {
    fn new(api: &'a Api) -> Self {
        // SAFETY: standard config/context construction on a live library; the
        // NULL error handler makes libz3 record error codes instead of
        // invoking a handler (AY has no handler dispatch either).
        let ctx = unsafe {
            let cfg = (api.Z3_mk_config)();
            let ctx = (api.Z3_mk_context)(cfg);
            (api.Z3_del_config)(cfg);
            (api.Z3_set_error_handler)(ctx, 0);
            ctx
        };
        Session { api, ctx }
    }

    fn err(&self) -> c_uint {
        // SAFETY: live context.
        unsafe { (self.api.Z3_get_error_code)(self.ctx) }
    }

    fn err_msg(&self) -> String {
        // SAFETY: live context; the returned string is context-owned — copied
        // out immediately.
        unsafe {
            let code = (self.api.Z3_get_error_code)(self.ctx);
            let p = (self.api.Z3_get_error_msg)(self.ctx, code);
            if p.is_null() {
                String::new()
            } else {
                CStr::from_ptr(p).to_string_lossy().into_owned()
            }
        }
    }

    fn sym(&self, name: &str) -> W {
        let cname = CString::new(name).expect("no NUL in symbol names");
        // SAFETY: live context; the library copies the name.
        unsafe { (self.api.Z3_mk_string_symbol)(self.ctx, cname.as_ptr()) }
    }
}

impl Drop for Session<'_> {
    fn drop(&mut self) {
        // SAFETY: contexts are only dropped after all probe values built on
        // them are dead (each probe is self-contained).
        unsafe { (self.api.Z3_del_context)(self.ctx) };
    }
}

/// Classify an AST-producing call: `error` if the error code moved, else the
/// canonical value from `summarize`.
fn class_of_ast(s: &Session<'_>, ast: W, summarize: impl FnOnce() -> String) -> Outcome {
    if s.err() != 0 || ast == 0 {
        Outcome {
            class: Class::Error,
            detail: s.err_msg(),
        }
    } else {
        Outcome {
            class: Class::OkValue(summarize()),
            detail: String::new(),
        }
    }
}

/// Classify a void call.
fn class_of_void(s: &Session<'_>) -> Outcome {
    if s.err() != 0 {
        Outcome {
            class: Class::Error,
            detail: s.err_msg(),
        }
    } else {
        Outcome {
            class: Class::Inert,
            detail: String::new(),
        }
    }
}

// ---------------------------------------------------------------------------
// The probes. Each takes a fresh Session and returns the observable Outcome.
// ---------------------------------------------------------------------------

/// `Z3_mk_char_to_bv` on the char literal 65: value class = BV sort width.
fn probe_char_to_bv(s: &Session<'_>) -> Outcome {
    // SAFETY: live context/handles throughout (single-threaded session).
    unsafe {
        let ch = (s.api.Z3_mk_char)(s.ctx, 65);
        let bv = (s.api.Z3_mk_char_to_bv)(s.ctx, ch);
        class_of_ast(s, bv, || {
            let sort = (s.api.Z3_get_sort)(s.ctx, bv);
            let kind = (s.api.Z3_get_sort_kind)(s.ctx, sort);
            let width = (s.api.Z3_get_bv_sort_size)(s.ctx, sort);
            format!("sort-kind={kind},bv-width={width}")
        })
    }
}

/// `Z3_mk_char_from_bv` on a width-8 bit-vector: both libs must REJECT.
fn probe_char_from_bv_wrong_width(s: &Session<'_>) -> Outcome {
    // SAFETY: live context/handles.
    unsafe {
        let bv8 = (s.api.Z3_mk_bv_sort)(s.ctx, 8);
        let v = (s.api.Z3_mk_unsigned_int64)(s.ctx, 65, bv8);
        let ch = (s.api.Z3_mk_char_from_bv)(s.ctx, v);
        class_of_ast(s, ch, || "char".to_string())
    }
}

/// `Z3_mk_char_from_bv` on a width-18 bit-vector: both libs must ACCEPT.
fn probe_char_from_bv_ok(s: &Session<'_>) -> Outcome {
    // SAFETY: live context/handles.
    unsafe {
        let bv18 = (s.api.Z3_mk_bv_sort)(s.ctx, 18);
        let v = (s.api.Z3_mk_unsigned_int64)(s.ctx, 65, bv18);
        let ch = (s.api.Z3_mk_char_from_bv)(s.ctx, v);
        class_of_ast(s, ch, || {
            let sort = (s.api.Z3_get_sort)(s.ctx, ch);
            format!("sort-kind={}", (s.api.Z3_get_sort_kind)(s.ctx, sort))
        })
    }
}

/// Declare `R : Int × Int → Bool` on the session and return the decl.
fn binary_int_pred(s: &Session<'_>, name: &str) -> W {
    // SAFETY: live context/handles.
    unsafe {
        let int = (s.api.Z3_mk_int_sort)(s.ctx);
        let boolean = (s.api.Z3_mk_bool_sort)(s.ctx);
        let dom = [int, int];
        (s.api.Z3_mk_func_decl)(s.ctx, s.sym(name), 2, dom.as_ptr(), boolean)
    }
}

/// `Z3_mk_transitive_closure` on a valid binary predicate: both must ACCEPT.
fn probe_transitive_closure_ok(s: &Session<'_>) -> Outcome {
    // SAFETY: live context/handles.
    unsafe {
        let f = binary_int_pred(s, "R");
        let tc = (s.api.Z3_mk_transitive_closure)(s.ctx, f);
        class_of_ast(s, tc, || "func-decl".to_string())
    }
}

/// `Z3_mk_transitive_closure` on `Int × Int → Int`: both must REJECT.
fn probe_transitive_closure_bad_range(s: &Session<'_>) -> Outcome {
    // SAFETY: live context/handles.
    unsafe {
        let int = (s.api.Z3_mk_int_sort)(s.ctx);
        let dom = [int, int];
        let f = (s.api.Z3_mk_func_decl)(s.ctx, s.sym("F3"), 2, dom.as_ptr(), int);
        let tc = (s.api.Z3_mk_transitive_closure)(s.ctx, f);
        class_of_ast(s, tc, || "func-decl".to_string())
    }
}

/// `Z3_mk_transitive_closure` on a unary predicate: both must REJECT.
fn probe_transitive_closure_unary(s: &Session<'_>) -> Outcome {
    // SAFETY: live context/handles.
    unsafe {
        let int = (s.api.Z3_mk_int_sort)(s.ctx);
        let boolean = (s.api.Z3_mk_bool_sort)(s.ctx);
        let f = (s.api.Z3_mk_func_decl)(s.ctx, s.sym("F1"), 1, &raw const int, boolean);
        let tc = (s.api.Z3_mk_transitive_closure)(s.ctx, f);
        class_of_ast(s, tc, || "func-decl".to_string())
    }
}

unsafe extern "C" fn on_clause_cb(
    _u: *mut c_void,
    _hint: W,
    _n: c_uint,
    _deps: *const c_uint,
    _cl: W,
) {
}

/// `Z3_solver_register_on_clause`: the REGISTRATION contract (accepted, no
/// error) — the exact point at issue for AY's accept-never-fire
/// implementation.
///
/// Deliberately NOT followed by a `Z3_solver_check` here: libz3 4.16.0 itself
/// SEGFAULTS inside `Z3_solver_check` when an on_clause callback was
/// registered through the raw C ABI (reproduced standalone via ctypes on both
/// RC and non-RC contexts; z3py survives only through its own wrapper layer).
/// Callback GRANULARITY is undocumented/experimental with zero invocations
/// observed on some inputs (probed via z3py 2026-07-09), so the comparable
/// observable contract is registration itself.
fn probe_register_on_clause(s: &Session<'_>) -> Outcome {
    // SAFETY: live context/handles; the callback address matches the C shape.
    unsafe {
        let solver = (s.api.Z3_mk_solver)(s.ctx);
        (s.api.Z3_solver_register_on_clause)(s.ctx, solver, std::ptr::null_mut(), on_clause_cb);
        if s.err() != 0 {
            return Outcome {
                class: Class::Error,
                detail: s.err_msg(),
            };
        }
        Outcome {
            class: Class::OkValue("registration accepted".to_string()),
            detail: "callback firing not compared: libz3 4.16 segfaults in check after \
                     raw-C registration; granularity is undocumented (0 fires allowed)"
                .to_string(),
        }
    }
}

/// Fresh fixedpoint with `p : Int → Bool` registered; optionally spacer-mode.
fn fixedpoint_with_pred(s: &Session<'_>, spacer: bool) -> (W, W) {
    // SAFETY: live context/handles.
    unsafe {
        let fp = (s.api.Z3_mk_fixedpoint)(s.ctx);
        // Fixedpoint objects require refcounting in libz3 EVEN on non-RC
        // contexts (z3py always inc_refs; skipping it segfaults).
        (s.api.Z3_fixedpoint_inc_ref)(s.ctx, fp);
        if spacer {
            let params = (s.api.Z3_mk_params)(s.ctx);
            // Params objects require refcounting in libz3 EVEN on non-RC
            // contexts (documented; skipping inc_ref segfaults).
            (s.api.Z3_params_inc_ref)(s.ctx, params);
            (s.api.Z3_params_set_symbol)(s.ctx, params, s.sym("engine"), s.sym("spacer"));
            (s.api.Z3_fixedpoint_set_params)(s.ctx, fp, params);
        }
        let int = (s.api.Z3_mk_int_sort)(s.ctx);
        let boolean = (s.api.Z3_mk_bool_sort)(s.ctx);
        let p = (s.api.Z3_mk_func_decl)(s.ctx, s.sym("p"), 1, &raw const int, boolean);
        (s.api.Z3_fixedpoint_register_relation)(s.ctx, fp, p);
        (fp, p)
    }
}

/// `Z3_fixedpoint_init(NULL state)`: deprecated hook — inert in both?
fn probe_fixedpoint_init(s: &Session<'_>) -> Outcome {
    // SAFETY: live context/handles.
    unsafe {
        let (fp, _p) = fixedpoint_with_pred(s, false);
        (s.api.Z3_fixedpoint_init)(s.ctx, fp, std::ptr::null_mut());
        class_of_void(s)
    }
}

/// `Z3_fixedpoint_get_reachable` with no query run (default engine).
fn probe_fixedpoint_get_reachable(s: &Session<'_>) -> Outcome {
    // SAFETY: live context/handles.
    unsafe {
        let (fp, p) = fixedpoint_with_pred(s, false);
        let r = (s.api.Z3_fixedpoint_get_reachable)(s.ctx, fp, p);
        class_of_ast(s, r, || "ast".to_string())
    }
}

/// `Z3_fixedpoint_get_cover_delta(level = 0)` on a spacer-mode fixedpoint.
fn probe_fixedpoint_cover_delta_finite(s: &Session<'_>) -> Outcome {
    // SAFETY: live context/handles.
    unsafe {
        let (fp, p) = fixedpoint_with_pred(s, true);
        let r = (s.api.Z3_fixedpoint_get_cover_delta)(s.ctx, fp, 0, p);
        class_of_ast(s, r, || "bool-ast".to_string())
    }
}

/// `Z3_fixedpoint_add_cover(level = 2, p, true)` on a spacer-mode fixedpoint
/// with DEFAULT parameters (slicing on).
fn probe_fixedpoint_add_cover_finite(s: &Session<'_>) -> Outcome {
    // SAFETY: live context/handles.
    unsafe {
        let (fp, p) = fixedpoint_with_pred(s, true);
        let t = (s.api.Z3_mk_true)(s.ctx);
        (s.api.Z3_fixedpoint_add_cover)(s.ctx, fp, 2, p, t);
        class_of_void(s)
    }
}

/// `Z3_fixedpoint_add_constraint(true, lvl = 3)` (a FINITE level).
fn probe_fixedpoint_add_constraint_finite(s: &Session<'_>) -> Outcome {
    // SAFETY: live context/handles.
    unsafe {
        let (fp, _p) = fixedpoint_with_pred(s, true);
        let t = (s.api.Z3_mk_true)(s.ctx);
        (s.api.Z3_fixedpoint_add_constraint)(s.ctx, fp, t, 3);
        class_of_void(s)
    }
}

/// `Z3_fixedpoint_set_predicate_representation(p, ["interval_relation"])`.
fn probe_fixedpoint_set_pred_repr(s: &Session<'_>) -> Outcome {
    // SAFETY: live context/handles.
    unsafe {
        let (fp, p) = fixedpoint_with_pred(s, false);
        let kind = s.sym("interval_relation");
        (s.api.Z3_fixedpoint_set_predicate_representation)(s.ctx, fp, p, 1, &raw const kind);
        class_of_void(s)
    }
}

/// The datalog reduce-callback pair, registered as NULL (the minimal input).
fn probe_fixedpoint_reduce_callbacks(s: &Session<'_>) -> Outcome {
    // SAFETY: live context/handles.
    unsafe {
        let (fp, _p) = fixedpoint_with_pred(s, false);
        (s.api.Z3_fixedpoint_set_reduce_app_callback)(s.ctx, fp, 0);
        if s.err() != 0 {
            return Outcome {
                class: Class::Error,
                detail: s.err_msg(),
            };
        }
        (s.api.Z3_fixedpoint_set_reduce_assign_callback)(s.ctx, fp, 0);
        class_of_void(s)
    }
}

/// `Z3_fixedpoint_add_callback` with NULL handlers (the minimal input).
fn probe_fixedpoint_add_callback(s: &Session<'_>) -> Outcome {
    // SAFETY: live context/handles.
    unsafe {
        let (fp, _p) = fixedpoint_with_pred(s, true);
        (s.api.Z3_fixedpoint_add_callback)(s.ctx, fp, std::ptr::null_mut(), 0, 0, 0);
        class_of_void(s)
    }
}

/// `Z3_get_relation_arity` on the Int sort (NOT a relation sort — the only
/// input class AY can ever receive, since it has no relation sorts).
fn probe_relation_arity(s: &Session<'_>) -> Outcome {
    // SAFETY: live context/handles.
    unsafe {
        let int = (s.api.Z3_mk_int_sort)(s.ctx);
        let arity = (s.api.Z3_get_relation_arity)(s.ctx, int);
        if s.err() != 0 {
            Outcome {
                class: Class::Error,
                detail: s.err_msg(),
            }
        } else {
            Outcome {
                class: Class::OkValue(format!("arity={arity}")),
                detail: String::new(),
            }
        }
    }
}

/// `Z3_get_relation_column` on the Int sort.
fn probe_relation_column(s: &Session<'_>) -> Outcome {
    // SAFETY: live context/handles.
    unsafe {
        let int = (s.api.Z3_mk_int_sort)(s.ctx);
        let col = (s.api.Z3_get_relation_column)(s.ctx, int, 0);
        class_of_ast(s, col, || "sort".to_string())
    }
}

/// Polymorphic INSTANTIATION: declare `f : α → α`, apply to an Int numeral.
fn probe_polymorphic_instantiation(s: &Session<'_>) -> Outcome {
    // SAFETY: live context/handles.
    unsafe {
        let alpha = (s.api.Z3_mk_type_variable)(s.ctx, s.sym("alpha"));
        if alpha == 0 || s.err() != 0 {
            return Outcome {
                class: Class::Error,
                detail: s.err_msg(),
            };
        }
        let f = (s.api.Z3_mk_func_decl)(s.ctx, s.sym("f"), 1, &raw const alpha, alpha);
        if f == 0 || s.err() != 0 {
            return Outcome {
                class: Class::Error,
                detail: s.err_msg(),
            };
        }
        let int = (s.api.Z3_mk_int_sort)(s.ctx);
        let five = (s.api.Z3_mk_int)(s.ctx, 5, int);
        let app = (s.api.Z3_mk_app)(s.ctx, f, 1, &raw const five);
        class_of_ast(s, app, || {
            let sort = (s.api.Z3_get_sort)(s.ctx, app);
            format!("app-sort-kind={}", (s.api.Z3_get_sort_kind)(s.ctx, sort))
        })
    }
}

/// Higher-order sequence SOLVING through the SMT-LIB2 front door.
fn probe_hoseq_solving(s: &Session<'_>) -> Outcome {
    const SCRIPT: &str = "(declare-const s (Seq Int))\n\
                          (declare-const f (Array Int Int))\n\
                          (assert (= (seq.map f s) (as seq.empty (Seq Int))))\n\
                          (assert (> (seq.len s) 0))\n\
                          (check-sat)\n";
    let cscript = CString::new(SCRIPT).expect("static script");
    // SAFETY: live context; the returned string is context-owned — copied out
    // before the session drops.
    let out = unsafe {
        let p = (s.api.Z3_eval_smtlib2_string)(s.ctx, cscript.as_ptr());
        if p.is_null() {
            String::new()
        } else {
            CStr::from_ptr(p).to_string_lossy().into_owned()
        }
    };
    let verdict = if out.contains("unsat") {
        "unsat"
    } else if out.contains("unknown") {
        "unknown"
    } else if out.contains("sat") {
        "sat"
    } else {
        "no-verdict"
    };
    Outcome {
        class: Class::Verdict(verdict),
        detail: String::new(),
    }
}

// ---------------------------------------------------------------------------
// Judgement + runner
// ---------------------------------------------------------------------------

/// The pairwise judgement of one probe.
enum Judgement {
    Parity,
    GapAyWeaker,
    LenientAyStronger,
    Disagree,
}

impl Judgement {
    fn tag(&self) -> &'static str {
        match self {
            Judgement::Parity => "PARITY",
            Judgement::GapAyWeaker => "GAP(ay-weaker)",
            Judgement::LenientAyStronger => "LENIENT(ay-stronger)",
            Judgement::Disagree => "DISAGREE",
        }
    }
}

fn judge(ay: &Class, z3: &Class) -> Judgement {
    use Class::{Error, Verdict};
    match (ay, z3) {
        (a, b) if a == b => Judgement::Parity,
        // Verdicts: unknown against a decided verdict is a capability gap;
        // sat against unsat is the soundness failure.
        (Verdict("unknown"), Verdict(_)) => Judgement::GapAyWeaker,
        (Verdict(_), Verdict("unknown")) => Judgement::LenientAyStronger,
        (Verdict(_), Verdict(_)) => Judgement::Disagree,
        // AY errors where libz3 produces something: honest capability gap.
        (Error, _) => Judgement::GapAyWeaker,
        // AY produces something where libz3 errors: sound leniency.
        (_, Error) => Judgement::LenientAyStronger,
        // Both produced values but they differ (e.g. widths): conflict.
        _ => Judgement::Disagree,
    }
}

pub(crate) fn run(ay_path: &Path, z3_path: &Path, json: bool) -> i32 {
    let ay_lib = match open_local(ay_path) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("error: {e}");
            return 2;
        }
    };
    let z3_lib = match open_local(z3_path) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("error: {e}");
            return 2;
        }
    };
    let (ay, z3) = match (load(&ay_lib), load(&z3_lib)) {
        (Ok(a), Ok(z)) => (a, z),
        (Err(e), _) | (_, Err(e)) => {
            eprintln!("error: {e}");
            return 2;
        }
    };

    type Probe = (&'static str, fn(&Session<'_>) -> Outcome);
    let probes: &[Probe] = &[
        ("Z3_mk_char_to_bv(char 65)", probe_char_to_bv),
        ("Z3_mk_char_from_bv(bv8)", probe_char_from_bv_wrong_width),
        ("Z3_mk_char_from_bv(bv18)", probe_char_from_bv_ok),
        (
            "Z3_mk_transitive_closure(Int²→Bool)",
            probe_transitive_closure_ok,
        ),
        (
            "Z3_mk_transitive_closure(Int²→Int)",
            probe_transitive_closure_bad_range,
        ),
        (
            "Z3_mk_transitive_closure(unary)",
            probe_transitive_closure_unary,
        ),
        ("Z3_solver_register_on_clause", probe_register_on_clause),
        ("Z3_fixedpoint_init(NULL)", probe_fixedpoint_init),
        (
            "Z3_fixedpoint_get_reachable(no query)",
            probe_fixedpoint_get_reachable,
        ),
        (
            "Z3_fixedpoint_get_cover_delta(level 0, spacer)",
            probe_fixedpoint_cover_delta_finite,
        ),
        (
            "Z3_fixedpoint_add_cover(level 2, spacer)",
            probe_fixedpoint_add_cover_finite,
        ),
        (
            "Z3_fixedpoint_add_constraint(lvl 3)",
            probe_fixedpoint_add_constraint_finite,
        ),
        (
            "Z3_fixedpoint_set_predicate_representation",
            probe_fixedpoint_set_pred_repr,
        ),
        (
            "Z3_fixedpoint_set_reduce_{app,assign}_callback(NULL)",
            probe_fixedpoint_reduce_callbacks,
        ),
        (
            "Z3_fixedpoint_add_callback(NULL handlers)",
            probe_fixedpoint_add_callback,
        ),
        ("Z3_get_relation_arity(Int sort)", probe_relation_arity),
        ("Z3_get_relation_column(Int sort)", probe_relation_column),
        (
            "polymorphic instantiation (f:α→α at Int)",
            probe_polymorphic_instantiation,
        ),
        ("HO-seq solving (seq.map goal)", probe_hoseq_solving),
    ];

    let mut disagreements = 0usize;
    let mut gaps: Vec<String> = Vec::new();
    let mut rows: Vec<String> = Vec::new();

    println!(
        "behavior parity: {} vs {}",
        ay_path.display(),
        z3_path.display()
    );
    println!("{:<52} {:<28} {:<28} judgement", "probe", "AY", "libz3");
    for (name, probe) in probes {
        let ay_out = probe(&Session::new(&ay));
        let z3_out = probe(&Session::new(&z3));
        let j = judge(&ay_out.class, &z3_out.class);
        match j {
            Judgement::Disagree => disagreements += 1,
            Judgement::GapAyWeaker | Judgement::LenientAyStronger => {
                gaps.push(format!(
                    "{} — AY {}, libz3 {}",
                    name,
                    ay_out.class.label(),
                    z3_out.class.label()
                ));
            }
            Judgement::Parity => {}
        }
        let mut detail = String::new();
        if !ay_out.detail.is_empty() {
            detail.push_str(&format!("  [AY: {}]", ay_out.detail));
        }
        if !z3_out.detail.is_empty() {
            detail.push_str(&format!("  [z3: {}]", z3_out.detail));
        }
        println!(
            "{:<52} {:<28} {:<28} {}{}",
            name,
            ay_out.class.label(),
            z3_out.class.label(),
            j.tag(),
            detail
        );
        rows.push(format!(
            "{{\"probe\":{:?},\"ay\":{:?},\"z3\":{:?},\"judgement\":{:?}}}",
            name,
            ay_out.class.label(),
            z3_out.class.label(),
            j.tag()
        ));
    }

    println!();
    if gaps.is_empty() {
        println!("honest residue: none — every probed fn matches libz3's class");
    } else {
        println!(
            "honest residue ({} probes where the classes differ, reported, sound):",
            gaps.len()
        );
        for g in &gaps {
            println!("  * {g}");
        }
    }
    println!(
        "result: {} disagreements, {} parity, {} residue",
        disagreements,
        probes.len() - disagreements - gaps.len(),
        gaps.len()
    );
    if json {
        println!("[{}]", rows.join(","));
    }
    i32::from(disagreements > 0)
}
