// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible C API for AY
//!
//! Implements a documented subset of the Z3 C API (`z3_api.h`) so external
//! consumers can evaluate AY behind familiar ABI shapes. It is not a universal
//! drop-in replacement; unsupported entry points and semantic gaps remain part
//! of the public compatibility boundary.
//!
//! # Architecture
//!
//! - `Z3_context` wraps a `ay_dpll::api::Solver` (the term arena + solve engine)
//! - `Z3_ast` is an opaque context-salted encoding of an
//!   `ay_dpll::api::Term` index
//! - `Z3_sort` is a heap-allocated sort descriptor
//! - `Z3_func_decl` is a heap-allocated function declaration
//! - `Z3_model` is a heap-allocated model from a SAT result
//! - `Z3_solver` owns its own assertion stack (independent per handle, like
//!   Z3); each check loads exactly the handle's assertions into the context's
//!   shared engine before solving (see [`Z3SolverHandle`])
//!
//! # Reference counting (`inc_ref`/`dec_ref`)
//!
//! `Z3_ast` wraps a hash-consed, arena-interned `Term` (`ay_core::TermId`).
//! Terms are SHARED and are NEVER individually freed — the whole `TermStore`
//! drops with the context. Z3-style reclamation (freeing an AST when its count
//! hits zero) is therefore structurally impossible here and would be a
//! use-after-free/double-free bug against the arena.
//!
//! Consequently `Z3_inc_ref`/`Z3_dec_ref` are BOOKKEEPING ONLY: on a
//! reference-counted context (`Z3_mk_context_rc`) they maintain per-`Term`
//! counts so that `dec_ref` below zero is detected and reported as
//! `Z3_DEC_REF_ERROR`. They NEVER free a term. On a non-RC context
//! (`Z3_mk_context`) they are no-ops, matching Z3's own behavior where ref
//! counting is only active on RC contexts. In all cases, every object (AST,
//! sort, model, ...) lives until its parent context is destroyed via
//! `Z3_del_context`. This is discipline tracking, not memory reclamation.

mod accessors;
mod algebraic;
mod arithmetic;
mod ast_containers;
mod ast_identity;
#[allow(unreachable_pub)] // FFI functions are pub for linker visibility
mod ast_inspect;
mod bitvectors;
mod bitvectors_overflow;
mod context;
mod datatypes;
mod engine_ext;
mod engine_local;
mod ffi_guards;
pub(crate) use ffi_guards::*;
mod finite_sets;
mod fixedpoint;
mod fixedpoint_ext;
mod fixedpoint_ext2;
mod fpa;
mod fpa_ext;
mod fpa_introspect;
mod getters_ext;
mod global_params;
mod goals;
mod misc_ext;
mod mk_ext;
mod model_build;
mod model_params;
mod numerals;
mod optimize;
mod parser_context;
mod probes;
mod proofs;
mod propagate;
mod quantifier_inspect;
mod quantifiers;
mod rcf;
mod rcf_series;
mod sequences;
mod sets_regex;
mod simplifiers;
mod solver;
mod sorts;
mod statistics;
mod tactics;
mod terms;

#[cfg(test)]
mod bv_numeral_radix_tests;
#[cfg(test)]
mod finite_sets_tests;
#[cfg(test)]
mod rec_def_ffi_tests;
#[cfg(test)]
mod tests;

// Re-export all public items from submodules
pub use accessors::*;
pub use algebraic::*;
pub use arithmetic::*;
pub use ast_containers::*;
pub use ast_identity::*;
pub use ast_inspect::*;
pub use bitvectors::*;
pub use bitvectors_overflow::*;
pub use context::*;
pub use datatypes::*;
pub use engine_ext::*;
pub use engine_local::*;
pub use finite_sets::*;
pub use fixedpoint::*;
pub use fixedpoint_ext::*;
pub use fixedpoint_ext2::*;
pub use fpa::*;
pub use fpa_ext::*;
pub use fpa_introspect::*;
pub use getters_ext::*;
pub use global_params::*;
pub use goals::*;
pub use misc_ext::*;
pub use mk_ext::*;
pub use model_build::*;
pub use model_params::*;
pub use numerals::*;
pub use optimize::*;
pub use parser_context::*;
pub use probes::*;
pub use proofs::*;
pub use propagate::*;
pub use quantifier_inspect::*;
pub use quantifiers::*;
pub use rcf::*;
pub use sequences::*;
pub use sets_regex::*;
pub use simplifiers::*;
pub use solver::*;
pub use sorts::*;
pub use statistics::*;
pub use tactics::*;
pub use terms::*;

/// Prevent compact C precision arguments from expanding into unbounded
/// `BigInt`s, refinement loops, and output strings.  This shared ceiling is
/// enforced by every decimal/algebraic FFI entry point before doing work.
pub(crate) const MAX_FFI_DECIMAL_PRECISION: c_uint = 1_000_000;

/// Exact algebraic/transcendental rendering grows large rational endpoints on
/// every refinement step, so it needs a substantially tighter work cap than
/// direct rational decimal formatting.
pub(crate) const MAX_FFI_REFINEMENT_PRECISION: c_uint = 4_096;

/// Maximum number of elements accepted by compact FFI container-resize calls.
/// This prevents a single `c_uint` from requesting multi-gigabyte allocations.
pub(crate) const MAX_FFI_CONTAINER_ELEMENTS: c_uint = 1 << 20;

/// Maximum byte length accepted for general caller-provided C strings.
///
/// String literals legitimately need a larger envelope than numerals, but they
/// must not trigger an unbounded scan and clone from one foreign pointer.
pub(crate) const MAX_FFI_TEXT_BYTES: usize = 16 * 1024 * 1024;

/// Maximum source size accepted by SMT-LIB parser entry points.
///
/// AY's ordinary CLI is constrained by its process-memory envelope rather than
/// a source-size switch. The compatibility layer still needs an explicit
/// foreign-pointer/file ceiling, but it must accommodate large benchmark
/// corpora. One GiB is intentionally much larger than scalar FFI text while
/// remaining finite and below the harness's 8 GiB decompression ceiling.
pub(crate) const MAX_FFI_PARSER_SOURCE_BYTES: usize = 1024 * 1024 * 1024;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum FfiTextError {
    Null,
    TooLong(usize),
    InvalidUtf8,
}

impl std::fmt::Display for FfiTextError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Null => formatter.write_str("null text pointer"),
            Self::TooLong(max_bytes) => write!(
                formatter,
                "text exceeds the supported maximum {max_bytes} bytes"
            ),
            Self::InvalidUtf8 => formatter.write_str("text is not valid UTF-8"),
        }
    }
}

unsafe fn ffi_read_utf8_with_limit(
    text: *const c_char,
    max_bytes: usize,
) -> Result<String, FfiTextError> {
    if text.is_null() {
        return Err(FfiTextError::Null);
    }
    for text_bytes in 0..=max_bytes {
        // SAFETY: the caller guarantees a live NUL-terminated string, so every
        // byte through its terminator is readable. The loop stops no later
        // than the explicit `max_bytes + 1` inspection window.
        if unsafe { *text.add(text_bytes) } == 0 {
            // SAFETY: the bounded scan established the readable extent before
            // the terminator; `u8` has alignment one.
            let bytes = unsafe { std::slice::from_raw_parts(text.cast::<u8>(), text_bytes) };
            return std::str::from_utf8(bytes)
                .map(str::to_owned)
                .map_err(|_| FfiTextError::InvalidUtf8);
        }
    }
    Err(FfiTextError::TooLong(max_bytes))
}

/// Decode a caller-owned UTF-8 C string with an explicit scan/allocation cap.
///
/// # Safety
/// `text` must be null or point to a valid NUL-terminated C string that remains
/// live for this call. The NUL-termination contract guarantees readable storage
/// through the terminator even when it lies beyond the bounded window.
pub(crate) unsafe fn ffi_read_bounded_text(text: *const c_char) -> Result<String, FfiTextError> {
    // SAFETY: forwarded from this function's contract.
    unsafe { ffi_read_utf8_with_limit(text, MAX_FFI_TEXT_BYTES) }
}

/// Decode an SMT-LIB source C string with the larger parser-source envelope.
///
/// # Safety
/// Same as [`ffi_read_bounded_text`].
pub(crate) unsafe fn ffi_read_bounded_parser_text(
    text: *const c_char,
) -> Result<String, FfiTextError> {
    // SAFETY: forwarded from this function's contract.
    unsafe { ffi_read_utf8_with_limit(text, MAX_FFI_PARSER_SOURCE_BYTES) }
}

/// Read a UTF-8 regular file through the same bounded envelope as C parser
/// input. The `take(max + 1)` reader keeps a file that grows after metadata
/// lookup from bypassing the cap. FIFOs and devices are rejected before a
/// potentially blocking read; Unix opens are additionally nonblocking so a
/// path-type race cannot hang between the portable precheck and descriptor
/// validation. Symlinks to regular files remain supported.
fn ffi_read_text_file_with_limit(path: &str, max_bytes: usize) -> Result<String, String> {
    use std::io::Read as _;

    let metadata = std::fs::metadata(path).map_err(|error| error.to_string())?;
    if !metadata.is_file() {
        return Err("input source is not a regular file".to_string());
    }

    let mut options = std::fs::OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        options.custom_flags(libc::O_NONBLOCK);
    }
    let file = options.open(path).map_err(|error| error.to_string())?;
    if !file
        .metadata()
        .map_err(|error| error.to_string())?
        .is_file()
    {
        return Err("opened input source is not a regular file".to_string());
    }

    let mut bytes = Vec::new();
    file.take((max_bytes as u64).saturating_add(1))
        .read_to_end(&mut bytes)
        .map_err(|error| error.to_string())?;
    if bytes.len() > max_bytes {
        return Err(format!(
            "input exceeds the supported maximum {max_bytes} bytes"
        ));
    }
    String::from_utf8(bytes).map_err(|_| "input is not valid UTF-8".to_string())
}

pub(crate) fn ffi_read_bounded_parser_file(path: &str) -> Result<String, String> {
    ffi_read_text_file_with_limit(path, MAX_FFI_PARSER_SOURCE_BYTES)
}

/// Maximum byte length accepted for caller-provided exact numeral text.
/// Decimal-to-`BigInt` conversion can use substantially more CPU and memory
/// than the source string itself, so reject oversized values before cloning or
/// parsing them. 64 KiB still permits numerals far beyond ordinary solver use.
pub(crate) const MAX_FFI_NUMERAL_TEXT_BYTES: usize = 64 * 1024;

/// Read exact numeral text without first performing an unbounded C-string scan.
/// At most `MAX_FFI_NUMERAL_TEXT_BYTES + 1` bytes are inspected; a NUL at the
/// last position admits exactly the maximum text length.
///
/// # Safety
/// `text` must be non-null and point to a valid NUL-terminated C string. That
/// contract guarantees readable storage through the terminator even when it
/// lies beyond this bounded window.
pub(crate) unsafe fn ffi_read_bounded_numeral_text(
    ctx: &mut Z3Context,
    operation: &str,
    text: *const c_char,
) -> Option<String> {
    // SAFETY: forwarded from this function's contract.
    match unsafe { ffi_read_utf8_with_limit(text, MAX_FFI_NUMERAL_TEXT_BYTES) } {
        Ok(value) => Some(value),
        Err(FfiTextError::InvalidUtf8) => {
            ctx.last_error = Z3_INVALID_ARG;
            ctx.error_msg = Some(format!("{operation}: numeral text is not valid UTF-8"));
            None
        }
        Err(FfiTextError::Null) => {
            ctx.last_error = Z3_INVALID_ARG;
            ctx.error_msg = Some(format!("{operation}: null numeral text"));
            None
        }
        Err(FfiTextError::TooLong(_)) => {
            ctx.last_error = Z3_INVALID_ARG;
            ctx.error_msg = Some(format!(
                "{operation}: numeral text exceeds the supported maximum \
                 {MAX_FFI_NUMERAL_TEXT_BYTES} bytes"
            ));
            None
        }
    }
}

/// Reject an untrusted C array/count pair before any `Vec::with_capacity`,
/// iterator collection, or raw-pointer walk can amplify the compact count into
/// unbounded work. Call this before dereferencing the accompanying array.
///
/// # Safety
/// `c` must be null or a live, exclusively borrowed context pointer for the
/// duration of this call, matching every public Z3 entry point's contract.
pub(crate) unsafe fn ffi_count_within_limit(c: Z3_context, operation: &str, count: c_uint) -> bool {
    if count <= MAX_FFI_CONTAINER_ELEMENTS {
        return true;
    }
    // SAFETY: guaranteed by this helper's contract; `as_mut` handles null.
    if let Some(ctx) = unsafe { c.as_mut() } {
        ctx.last_error = Z3_INVALID_ARG;
        ctx.error_msg = Some(format!(
            "{operation}: element count {count} exceeds the supported maximum {MAX_FFI_CONTAINER_ELEMENTS}"
        ));
    }
    false
}

/// Apply the same ceiling to the aggregate number of elements traversed across
/// multiple caller arrays in one FFI call. Each individual array can fit while
/// their sum still requests product/duplicate-scale work.
///
/// # Safety
/// Same context-pointer contract as [`ffi_count_within_limit`].
pub(crate) unsafe fn ffi_counts_within_limit(
    c: Z3_context,
    operation: &str,
    counts: &[c_uint],
) -> bool {
    let total = counts
        .iter()
        .try_fold(0u64, |sum, &count| sum.checked_add(u64::from(count)));
    if total.is_some_and(|total| total <= u64::from(MAX_FFI_CONTAINER_ELEMENTS)) {
        return true;
    }
    // SAFETY: guaranteed by this helper's contract; `as_mut` handles null.
    if let Some(ctx) = unsafe { c.as_mut() } {
        ctx.last_error = Z3_INVALID_ARG;
        ctx.error_msg = Some(format!(
            "{operation}: aggregate element count exceeds the supported maximum \
             {MAX_FFI_CONTAINER_ELEMENTS}"
        ));
    }
    false
}

/// Maximum exponent/root degree accepted by exact algebraic FFI operations.
/// These arguments otherwise amplify into linear iteration counts and large
/// exact-polynomial allocations.
pub(crate) const MAX_FFI_ALGEBRAIC_EXPONENT: c_uint = 4_096;

use std::collections::HashMap;
use std::ffi::{c_char, c_int, c_uint, CString};
use std::ptr;
use std::time::Duration;

use ay_dpll::api::{FuncDecl, Model, Solver, Sort, Tactic, Term, TermKind};
use ay_dpll::Statistics;
// PatternHandle is available via `pub use quantifiers::*` above.

// ============================================================================
// Z3 Type Aliases (Opaque Pointers)
// ============================================================================

/// Opaque context handle (wraps AY Solver)
pub type Z3_context = *mut Z3Context;
/// Opaque config handle
pub type Z3_config = *mut Z3Config;
/// AST handle (an opaque context-salted encoding of AY's Copy 32-bit term index)
pub type Z3_ast = u64;
/// Sort handle (heap-allocated)
pub type Z3_sort = *mut SortHandle;
/// Function declaration handle (heap-allocated)
pub type Z3_func_decl = *mut FuncDeclHandle;
/// Solver handle (aliases context in AY)
pub type Z3_solver = *mut Z3SolverHandle;
/// Optimize (MaxSMT) handle (aliases the context's single Solver in AY)
pub type Z3_optimize = *mut OptimizeHandle;
/// Fixedpoint (CHC/Datalog) handle (drives the `ay-chc` engine)
pub type Z3_fixedpoint = *mut FixedpointHandle;
/// Tactic (goal-to-goal transformation) handle (heap-allocated).
pub type Z3_tactic = *mut TacticHandle;
/// Simplifier (preprocessing goal-to-goal transformer) handle (heap-allocated).
pub type Z3_simplifier = *mut SimplifierHandle;
/// Model handle (heap-allocated)
pub type Z3_model = *mut ModelHandle;
/// Model function-interpretation handle (arity > 0) (heap-allocated)
pub type Z3_func_interp = *mut FuncInterpHandle;
/// Model function-interpretation entry (one point of the finite map)
pub type Z3_func_entry = *mut FuncEntryHandle;
/// Symbol handle (heap-allocated)
pub type Z3_symbol = *mut SymbolHandle;
/// Params handle (heap-allocated)
pub type Z3_params = *mut ParamsHandle;
/// AST vector handle
pub type Z3_ast_vector = *mut AstVectorHandle;
/// AST map handle (a map from `Z3_ast` key to `Z3_ast` value)
pub type Z3_ast_map = *mut AstMapHandle;
/// Datatype constructor descriptor handle (heap-allocated) (#phase3-dt)
pub type Z3_constructor = *mut ConstructorHandle;
/// Datatype constructor-list descriptor handle (heap-allocated) (#phase3-dt)
pub type Z3_constructor_list = *mut ConstructorListHandle;
/// Incremental SMT-LIB parser-context handle (heap-allocated).
///
/// Wraps AY's real SMT-LIB2 front-end (`Solver::parse_smtlib2`) with a
/// persistent symbol table: sorts/decls added via `Z3_parser_context_add_sort`/
/// `_add_decl` and declarations parsed by an earlier `Z3_parser_context_from_string`
/// stay visible to later parses. See [`ParserContextHandle`] and `parser_context.rs`.
pub type Z3_parser_context = *mut ParserContextHandle;
/// Z3 string type (context-owned C string), matching `typedef const char* Z3_string`.
pub type Z3_string = *const c_char;
/// Statistics handle (heap-allocated snapshot of a solver check's counters).
pub type Z3_stats = *mut StatsHandle;
/// Parameter-descriptor set handle (heap-allocated, arena-owned).
pub type Z3_param_descrs = *mut ParamDescrsHandle;
/// Goal handle (a set of assertion formulas; heap-allocated, arena-owned).
pub type Z3_goal = *mut GoalHandle;
/// Apply-result handle (the subgoals a tactic produced; arena-owned).
pub type Z3_apply_result = *mut ApplyResultHandle;
/// Probe handle (a numeric/boolean query over a goal; heap-allocated, arena-owned).
pub type Z3_probe = *mut ProbeHandle;

/// High-bit tag distinguishing a proof-AST handle from an ordinary term handle.
///
/// Ordinary `Z3_ast` values keep `TermId + 1` in the low 33-bit payload and a
/// context salt below the reserved top nibble. A proof handle returned by
/// `Z3_solver_get_proof` sets bit 63, carries the same context salt in bits
/// 32–58, and stores its proof-text index in the low 32 bits, so it can never
/// alias a real term or a proof from another context and `Z3_ast_to_string` can
/// route it to the stored Alethe text. See `proofs.rs` (#phase3-proof).
pub(crate) const PROOF_AST_TAG: u64 = 1u64 << 63;

/// High-bit tag distinguishing an irrational-algebraic-number AST handle from an
/// ordinary term handle.
///
/// Ordinary term ASTs never set the reserved top nibble. AY's `Real` AST only
/// encodes `BigRational`, so an irrational result of `Z3_algebraic_root` /
/// `Z3_algebraic_add` (e.g. √2) has no term representation. Such a result sets
/// bit 62, carries the context salt in bits 32–58, and stores its `RealScalar`
/// index in the low 32 bits (in `Z3Context::algebraic_values`), so it can never
/// alias a real term, a proof handle (bit 63), or an algebraic value from
/// another context. The `Z3_algebraic_*` / `Z3_get_algebraic_number_*` entry
/// points route it to the stored exact value. Rational results keep using the
/// ordinary numeral-AST path.
pub(crate) const ALGEBRAIC_AST_TAG: u64 = 1u64 << 62;

/// High-bit tag distinguishing a SORT-AST handle (`Z3_sort_to_ast`) from an
/// ordinary term handle.
///
/// A sort is not a term in AY (`Z3_sort` is a `*mut SortHandle`, a disjoint
/// representation), so `Z3_sort_to_ast` mints a value-canonical tagged handle:
/// bit 61 set, low bits = the context's stable semantic `sort_id` (same `Sort`
/// value → same id → same handle, which is what makes `Z3_is_eq_ast` correct
/// for equal sorts with plain `u64` equality — z3 parity, z3 hash-conses its
/// sorts). The context table [`Z3Context::sort_ast_handles`] maps the id back
/// to a live `SortHandle` for decode (`Z3_ast_to_string`, parser-context
/// injection).
pub(crate) const SORT_AST_TAG: u64 = 1u64 << 61;

/// High-bit tag distinguishing a FUNC-DECL-AST handle (`Z3_func_decl_to_ast`)
/// from an ordinary term handle.
///
/// Like [`SORT_AST_TAG`] but for func_decls: bit 60 set, low bits = a
/// value-canonical index into [`Z3Context::decl_ast_handles`], interned by
/// [`DeclAstKey`] (name/domain/range + indexed params + datatype-op kind) so
/// two handles for the same declaration yield the SAME tagged ast — z3py
/// hashes and `==`-compares `as_ast()` results.
pub(crate) const FUNC_DECL_AST_TAG: u64 = 1u64 << 60;

/// Mask covering every non-term `Z3_ast` tag: proof (63), algebraic (62),
/// sort (61), func_decl (60) — the reserved top nibble.
///
/// SOUNDNESS: [`checked_ast_to_term`] rejects this mask before decoding. A tagged
/// handle leaking into a term-consuming entry point must NEVER be silently
/// `u32`-truncated into a real `Term` id (that would alias an arbitrary
/// unrelated term — a direct wrong-verdict channel).
pub(crate) const HANDLE_TAG_MASK: u64 = 0xF << 60;

/// Per-context discriminator carried by every indexed tagged AST handle
/// (proof/algebraic/sort/func-decl) in bits 32–58 (27 bits), so a handle minted
/// in one context can NEVER silently decode in another context (whose tables
/// could map the same low index to an unrelated object — a wrong-OBJECT decode
/// real z3 does not have, since z3 hash-conses per context / interns builtins
/// globally).
/// Decode verifies the salt and fails CLOSED (null handle → the caller's
/// honest error path) on a foreign or forged salt. Salts are never 0, so a
/// bare-forged `TAG | idx` value also fails closed. The 27-bit space wraps
/// after ~1.3e8 contexts in one process; a post-wrap collision only matters
/// for a caller already deep in cross-context UB, and is documented here.
pub(crate) const HANDLE_SALT_MASK: u64 = 0x07FF_FFFF;
/// Bit position of the [`HANDLE_SALT_MASK`] field inside a tagged handle.
pub(crate) const HANDLE_SALT_SHIFT: u32 = 32;
/// Index payload shared by context-owned tagged ASTs (proof, algebraic, sort,
/// and func-decl). Bits 32–58 are reserved for the context salt.
pub(crate) const TAGGED_AST_INDEX_MASK: u64 = u32::MAX as u64;

/// Ordinary term AST payload (`TermId + 1`) occupies bits 0–32. The 33rd bit
/// is needed for the theoretical `u32::MAX` term id; keeping it avoids a
/// wrapping alias even though a store of that size is not practical.
pub(crate) const TERM_AST_PAYLOAD_MASK: u64 = (1u64 << 33) - 1;
/// Ordinary term ASTs carry the same nonzero context salt in bits 33–59.
pub(crate) const TERM_AST_SALT_SHIFT: u32 = 33;
const _: () = {
    let term_salt_mask = HANDLE_SALT_MASK << TERM_AST_SALT_SHIFT;
    assert!(TERM_AST_PAYLOAD_MASK & term_salt_mask == 0);
    assert!((TERM_AST_PAYLOAD_MASK | term_salt_mask) & HANDLE_TAG_MASK == 0);
};

/// Process-global source of per-context handle salts (see
/// [`HANDLE_SALT_MASK`]). Starts at 1: salt 0 is reserved as "never valid".
static NEXT_HANDLE_SALT: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(1);

/// Mint the handle salt for a new context: nonzero, 27-bit.
pub(crate) fn next_handle_salt() -> u32 {
    loop {
        let raw = NEXT_HANDLE_SALT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let salt = raw & (HANDLE_SALT_MASK as u32);
        if salt != 0 {
            return salt;
        }
    }
}

// ============================================================================
// Z3 Constants
// ============================================================================

/// Z3_lbool values
pub const Z3_L_FALSE: c_int = -1;
pub const Z3_L_UNDEF: c_int = 0;
pub const Z3_L_TRUE: c_int = 1;

/// Z3_sort_kind values — byte-for-byte the upstream `Z3_sort_kind` enum from
/// z3_api.h (verified against z3py 4.15.4). Note `Z3_UNINTERPRETED_SORT` is `0`
/// (NOT `6` — that is `Z3_DATATYPE_SORT`) and `Z3_SEQ_SORT` is `11` (NOT `7`).
pub const Z3_UNINTERPRETED_SORT: c_uint = 0;
pub const Z3_BOOL_SORT: c_uint = 1;
pub const Z3_INT_SORT: c_uint = 2;
pub const Z3_REAL_SORT: c_uint = 3;
pub const Z3_BV_SORT: c_uint = 4;
pub const Z3_ARRAY_SORT: c_uint = 5;
pub const Z3_DATATYPE_SORT: c_uint = 6;
pub const Z3_RELATION_SORT: c_uint = 7;
pub const Z3_FINITE_DOMAIN_SORT: c_uint = 8;
pub const Z3_FLOATING_POINT_SORT: c_uint = 9;
pub const Z3_ROUNDING_MODE_SORT: c_uint = 10;
/// Sequence sort kind. AY reports this for both `Sort::Seq` and `Sort::String`,
/// matching Z3's model where a String is a sequence of characters (#phase3-seq).
pub const Z3_SEQ_SORT: c_uint = 11;
pub const Z3_RE_SORT: c_uint = 12;
pub const Z3_CHAR_SORT: c_uint = 13;
/// Type-variable sort kind (verified against z3_api.h 4.16: `Z3_TYPE_VAR` is
/// the enum entry immediately after `Z3_CHAR_SORT`).
pub const Z3_TYPE_VAR: c_uint = 14;
pub const Z3_UNKNOWN_SORT: c_uint = 1000;

/// AY's dense bit-vector/FP-significand construction envelope. Public FFI
/// builders reject larger compact widths before allocating.
pub(crate) const MAX_FFI_BITVECTOR_WIDTH: c_uint = 1 << 20;
/// `FpPrecision` represents exponent bias in `u32`, so 32-bit exponent fields
/// are not representable by the current core API.
pub(crate) const MAX_FFI_FP_EXPONENT_BITS: c_uint = 31;

/// Validate the rounding-mode operand shared by every FPA constructor.
///
/// The public `ay-dpll` FP builders validate their numeric operands but accept
/// an already-internalized rounding-mode term. The C API is a typed
/// construction boundary, so it must reject (for example) a Bool passed where
/// Z3 requires `RoundingMode` instead of interning an ill-sorted application.
pub(crate) fn require_fpa_rounding_mode(
    ctx: &mut Z3Context,
    operation: &str,
    ast: Z3_ast,
) -> Option<Term> {
    let term = require_term_ast(ctx, ast, operation, "rounding-mode operand")?;
    if matches!(
        ctx.solver.sort_of(term),
        Sort::Uninterpreted(name) if name == "RoundingMode"
    ) {
        return Some(term);
    }
    ctx.last_error = Z3_SORT_ERROR;
    ctx.error_msg = Some(format!(
        "{operation}: rounding-mode operand must have RoundingMode sort"
    ));
    None
}

/// Z3_goal_prec values (upstream `Z3_goal_prec` enum from z3_api.h). AY's
/// tactics are all equivalence-preserving (no over/under approximation), so a
/// goal is always `Z3_GOAL_PRECISE`.
pub const Z3_GOAL_PRECISE: c_uint = 0;
pub const Z3_GOAL_UNDER: c_uint = 1;
pub const Z3_GOAL_OVER: c_uint = 2;
pub const Z3_GOAL_UNDER_OVER: c_uint = 3;

/// Z3_ast_kind values (upstream `Z3_ast_kind` enum from z3_api.h).
pub const Z3_NUMERAL_AST: c_uint = 0;
pub const Z3_APP_AST: c_uint = 1;
pub const Z3_VAR_AST: c_uint = 2;
pub const Z3_QUANTIFIER_AST: c_uint = 3;
pub const Z3_SORT_AST: c_uint = 4;
pub const Z3_FUNC_DECL_AST: c_uint = 5;
pub const Z3_UNKNOWN_AST: c_uint = 1000;

/// Z3_decl_kind values (operator kinds for function declarations).
/// These match the Z3 C API enum values from z3_api.h.
// Basic
pub const Z3_OP_TRUE: c_uint = 0x100;
pub const Z3_OP_FALSE: c_uint = 0x101;
pub const Z3_OP_EQ: c_uint = 0x102;
pub const Z3_OP_DISTINCT: c_uint = 0x103;
pub const Z3_OP_ITE: c_uint = 0x104;
pub const Z3_OP_AND: c_uint = 0x105;
pub const Z3_OP_OR: c_uint = 0x106;
pub const Z3_OP_IFF: c_uint = 0x107;
pub const Z3_OP_XOR: c_uint = 0x108;
pub const Z3_OP_NOT: c_uint = 0x109;
pub const Z3_OP_IMPLIES: c_uint = 0x10a;
// Arithmetic
pub const Z3_OP_ANUM: c_uint = 0x200;
pub const Z3_OP_AGNUM: c_uint = 0x201;
pub const Z3_OP_LE: c_uint = 0x202;
pub const Z3_OP_GE: c_uint = 0x203;
pub const Z3_OP_LT: c_uint = 0x204;
pub const Z3_OP_GT: c_uint = 0x205;
pub const Z3_OP_ADD: c_uint = 0x206;
pub const Z3_OP_SUB: c_uint = 0x207;
pub const Z3_OP_UMINUS: c_uint = 0x208;
pub const Z3_OP_MUL: c_uint = 0x209;
pub const Z3_OP_DIV: c_uint = 0x20a;
pub const Z3_OP_IDIV: c_uint = 0x20b;
pub const Z3_OP_REM: c_uint = 0x20c;
pub const Z3_OP_MOD: c_uint = 0x20d;
pub const Z3_OP_TO_REAL: c_uint = 0x20e;
pub const Z3_OP_TO_INT: c_uint = 0x20f;
pub const Z3_OP_IS_INT: c_uint = 0x210;
pub const Z3_OP_POWER: c_uint = 0x211;
pub const Z3_OP_ABS: c_uint = 0x212;
// Arrays
pub const Z3_OP_STORE: c_uint = 0x300;
pub const Z3_OP_SELECT: c_uint = 0x301;
pub const Z3_OP_CONST_ARRAY: c_uint = 0x302;
// Bitvectors
pub const Z3_OP_BNUM: c_uint = 0x400;
pub const Z3_OP_BIT1: c_uint = 0x401;
pub const Z3_OP_BIT0: c_uint = 0x402;
pub const Z3_OP_BNEG: c_uint = 0x403;
pub const Z3_OP_BADD: c_uint = 0x404;
pub const Z3_OP_BSUB: c_uint = 0x405;
pub const Z3_OP_BMUL: c_uint = 0x406;
pub const Z3_OP_BSDIV: c_uint = 0x407;
pub const Z3_OP_BUDIV: c_uint = 0x408;
pub const Z3_OP_BSREM: c_uint = 0x409;
pub const Z3_OP_BUREM: c_uint = 0x40a;
pub const Z3_OP_BSMOD: c_uint = 0x40b;
// BV (un)signed comparisons come *before* the bitwise ops in the upstream
// enum (0x411..0x418), then the bitwise/structural ops (0x419..).
pub const Z3_OP_ULEQ: c_uint = 0x411;
pub const Z3_OP_SLEQ: c_uint = 0x412;
pub const Z3_OP_UGEQ: c_uint = 0x413;
pub const Z3_OP_SGEQ: c_uint = 0x414;
pub const Z3_OP_ULT: c_uint = 0x415;
pub const Z3_OP_SLT: c_uint = 0x416;
pub const Z3_OP_UGT: c_uint = 0x417;
pub const Z3_OP_SGT: c_uint = 0x418;
pub const Z3_OP_BAND: c_uint = 0x419;
pub const Z3_OP_BOR: c_uint = 0x41a;
pub const Z3_OP_BNOT: c_uint = 0x41b;
pub const Z3_OP_BXOR: c_uint = 0x41c;
pub const Z3_OP_BNAND: c_uint = 0x41d;
pub const Z3_OP_BNOR: c_uint = 0x41e;
pub const Z3_OP_BXNOR: c_uint = 0x41f;
pub const Z3_OP_CONCAT: c_uint = 0x420;
pub const Z3_OP_SIGN_EXT: c_uint = 0x421;
pub const Z3_OP_ZERO_EXT: c_uint = 0x422;
pub const Z3_OP_EXTRACT: c_uint = 0x423;
pub const Z3_OP_REPEAT: c_uint = 0x424;
pub const Z3_OP_BSHL: c_uint = 0x428;
pub const Z3_OP_BLSHR: c_uint = 0x429;
pub const Z3_OP_BASHR: c_uint = 0x42a;
pub const Z3_OP_ROTATE_LEFT: c_uint = 0x42b;
pub const Z3_OP_ROTATE_RIGHT: c_uint = 0x42c;
// Finite sets (Z3 5.0.0 plugin theory).
pub const Z3_OP_FINITE_SET_EMPTY: c_uint = 0xc000;
pub const Z3_OP_FINITE_SET_SINGLETON: c_uint = 0xc001;
pub const Z3_OP_FINITE_SET_UNION: c_uint = 0xc002;
pub const Z3_OP_FINITE_SET_INTERSECT: c_uint = 0xc003;
pub const Z3_OP_FINITE_SET_DIFFERENCE: c_uint = 0xc004;
pub const Z3_OP_FINITE_SET_IN: c_uint = 0xc005;
pub const Z3_OP_FINITE_SET_SIZE: c_uint = 0xc006;
pub const Z3_OP_FINITE_SET_SUBSET: c_uint = 0xc007;
pub const Z3_OP_FINITE_SET_MAP: c_uint = 0xc008;
pub const Z3_OP_FINITE_SET_FILTER: c_uint = 0xc009;
pub const Z3_OP_FINITE_SET_RANGE: c_uint = 0xc00a;
pub const Z3_OP_FINITE_SET_EXT: c_uint = 0xc00b;
pub const Z3_OP_FINITE_SET_MAP_INVERSE: c_uint = 0xc00c;
// Z3 5.0.0 tail values. Keep these exact: bindings use the numeric ABI.
pub const Z3_OP_INTERNAL: c_uint = 0xc00d;
pub const Z3_OP_RECURSIVE: c_uint = 0xc00e;
pub const Z3_OP_UNINTERPRETED: c_uint = 0xc00f;

/// Z3_error_code values
pub const Z3_OK: c_uint = 0;
pub const Z3_SORT_ERROR: c_uint = 1;
pub const Z3_IOB: c_uint = 2;
pub const Z3_INVALID_ARG: c_uint = 3;
pub const Z3_PARSER_ERROR: c_uint = 4;
pub const Z3_NO_PARSER: c_uint = 5;
pub const Z3_INVALID_PATTERN: c_uint = 6;
pub const Z3_MEMOUT_FAIL: c_uint = 7;
pub const Z3_FILE_ACCESS_ERROR: c_uint = 8;
pub const Z3_INTERNAL_FATAL: c_uint = 9;
pub const Z3_INVALID_USAGE: c_uint = 10;
pub const Z3_DEC_REF_ERROR: c_uint = 11;
pub const Z3_EXCEPTION: c_uint = 12;

// ============================================================================
// Internal Handle Types
// ============================================================================

/// Family currently authorized to mutate/check the context's shared SMT engine.
///
/// Ordinary solver handles replay independent goals and may coexist with each
/// other. Optimize is eager and cannot be replayed yet, so it is an exclusive
/// family: mixing it with solver/global-parser semantic state would silently
/// union or wipe constraints.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum DecisionOwnerFamily {
    Solver,
    Optimize,
}

/// Complete C-API-visible quantifier hint identity for one hash-consed term.
/// AY's core term identity intentionally excludes these heuristic attributes,
/// so a second constructor may reuse the term only when this signature is
/// exactly equal. Conflicting metadata is rejected instead of overwriting the
/// first public AST's introspection state.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct QuantifierFfiMetadata {
    pub(crate) weight: c_uint,
    pub(crate) quantifier_id: Option<SymbolKey>,
    pub(crate) skolem_id: Option<SymbolKey>,
    pub(crate) no_patterns: Vec<Term>,
}

impl QuantifierFfiMetadata {
    fn is_default(&self) -> bool {
        self.weight == 1
            && self.quantifier_id.is_none()
            && self.skolem_id.is_none()
            && self.no_patterns.is_empty()
    }
}

impl Default for QuantifierFfiMetadata {
    fn default() -> Self {
        Self {
            weight: 1,
            quantifier_id: None,
            skolem_id: None,
            no_patterns: Vec::new(),
        }
    }
}

/// Internal context state
pub struct Z3Context {
    pub(crate) solver: Solver,
    pub(crate) last_error: c_uint,
    pub(crate) error_msg: Option<String>,
    /// Exclusive family owning semantic mutation/check access to `solver`.
    /// Term/sort/declaration construction and fixedpoint's independent CHC
    /// engine do not claim this field.
    pub(crate) decision_owner: Option<DecisionOwnerFamily>,
    /// Permanent fail-closed latch for a partially mutated shared SMT engine
    /// that could not be rolled back (currently cross-context Optimize
    /// translation failure). No later decision owner may claim the context.
    pub(crate) decision_engine_poisoned: Option<String>,
    /// Interned strings for Z3_ast_to_string etc. (Z3 returns context-owned ptrs)
    pub(crate) string_cache: Vec<CString>,
    /// Cached symbol handles — freed on context deletion (#5528).
    pub(crate) symbol_cache: Vec<*mut SymbolHandle>,
    /// Canonical C-API constants keyed by the exact Z3 symbol kind/value and
    /// requested sort.  AY's core variable interner is name-only, so routing
    /// `Z3_mk_const` through this cache plus a fresh internal identity is what
    /// keeps overloaded same-spelled constants distinct.
    pub(crate) ffi_const_cache: HashMap<(SymbolKey, Sort), Term>,
    /// Reverse constant metadata: term → (private model/replay name, original
    /// Z3 symbol).  This preserves symbol kind through `Z3_get_app_decl`.
    pub(crate) ffi_const_metadata: HashMap<Term, (String, SymbolKey)>,
    /// Private model/replay name → term, used to translate model entries back
    /// to the API-visible symbol without collapsing overloaded display names.
    pub(crate) ffi_const_terms_by_identity: HashMap<String, Term>,
    /// Canonical collision-proof solver name for each C-API function
    /// declaration identity.  Z3 overloads a displayed symbol by signature;
    /// AY's core names applications with a string, so every distinct
    /// `(symbol kind/value, domain, range)` receives its own private name.
    pub(crate) ffi_func_names: HashMap<(SymbolKey, Vec<Sort>, Sort), String>,
    /// Successfully registered native declaration for each exact C-API
    /// function identity. Repeated `Z3_mk_func_decl` calls must allocate
    /// distinct handles for one declaration, not attempt a second frontend
    /// declaration of the same private name.
    pub(crate) ffi_func_decls: HashMap<(SymbolKey, Vec<Sort>, Sort), FuncDecl>,
    /// Original Z3 symbol identity for solver-internal declaration names.
    /// Used to preserve `Z3_get_decl_name` kind/display after integer-symbol
    /// and fresh declarations are assigned collision-proof internal names.
    pub(crate) ffi_decl_symbols: HashMap<String, SymbolKey>,
    /// Caller-supplied recognizer symbol keyed by datatype sort and semantic
    /// constructor name. `DatatypeSort` stores constructor names but not
    /// recognizer symbols, so this preserves exact C-API round-trips while the
    /// core declaration retains its canonical `is-<constructor>` identity.
    pub(crate) ffi_dt_recognizers: HashMap<(Sort, String), SymbolKey>,
    /// Original Z3 symbol identity for uninterpreted sorts whose solver name
    /// differs from the API-visible symbol.
    pub(crate) ffi_sort_symbols: HashMap<Sort, SymbolKey>,
    /// Display names already used by C-API constants/functions.  Fresh-name
    /// generation skips these even though internal identities are disjoint.
    pub(crate) ffi_used_decl_names: std::collections::HashSet<String>,
    /// Monotonic identity/name source shared by fresh constants and functions.
    pub(crate) next_ffi_fresh_id: u64,
    /// Track sorts associated with AST handles for sort queries
    pub(crate) ast_sorts: Vec<Option<Sort>>,
    /// Public Z3 5.0.0 finite-set sort identity -> public element sort.
    pub(crate) finite_set_sorts: HashMap<Sort, Sort>,
    /// Canonical public element sort -> finite-set sort identity.
    pub(crate) finite_set_sorts_by_basis: HashMap<Sort, Sort>,
    /// Per-term finite-set decision provenance. Decision gates are derived
    /// from the current handle's reachable goal, never from unrelated ASTs
    /// constructed elsewhere in this context.
    pub(crate) finite_set_term_provenance: HashMap<Term, FiniteSetTermProvenance>,
    /// Finite-set witness axioms keyed by the public term whose semantics they
    /// define. Only axioms reachable from the current goal are installed.
    pub(crate) finite_set_reachable_axioms: HashMap<Term, Vec<Term>>,
    /// Publicly typed bound-variable terms for quantifiers built through the C
    /// API. Their AST sort side-table entries preserve FiniteSet identity even
    /// though the quantifier's engine binder sorts are lowered arrays.
    pub(crate) quantifier_public_bound_terms: HashMap<Term, Vec<Term>>,
    /// Parsed quantifiers do not expose their elaborator-private bound term
    /// identities. Preserve their public binder sorts directly.
    pub(crate) parsed_quantifier_public_bound_sorts: HashMap<Term, Vec<Sort>>,
    /// Z3 C-API quantifier priority weights keyed by the retained quantifier
    /// term. The weight is an instantiation hint, not logical semantics, but
    /// stock consumers expect it to round-trip through
    /// `Z3_get_quantifier_weight`.
    pub(crate) quantifier_weights: HashMap<Term, c_uint>,
    /// Explicit `:no-pattern` expressions supplied through the extended C
    /// quantifier constructors. They affect instantiation strategy only, but
    /// stock API introspection requires exact round-trip metadata.
    pub(crate) quantifier_no_patterns: HashMap<Term, Vec<Term>>,
    /// Atomic signature guarding the two side maps above plus the core qid and
    /// skolemid maps against hash-consed metadata aliasing.
    pub(crate) quantifier_ffi_metadata: HashMap<Term, QuantifierFfiMetadata>,
    /// Public finite-set applications retained over their engine witnesses.
    pub(crate) finite_set_apps: HashMap<Term, FiniteSetApp>,
    /// Exact characteristic-array meaning of each retained application.
    pub(crate) finite_set_app_backings: HashMap<Term, Term>,
    /// Z3-style hash-consing for retained finite-set applications.
    pub(crate) finite_set_app_cache: HashMap<FiniteSetAppKey, Term>,
    /// Public signatures for declarations whose engine signature lowers a
    /// finite-set sort to its characteristic-array representation.
    pub(crate) finite_set_decl_signatures: HashMap<String, (Vec<Sort>, Sort)>,
    /// Arena for heap-allocated handles — freed on context deletion (#5498).
    pub(crate) sort_cache: Vec<*mut SortHandle>,
    pub(crate) func_decl_cache: Vec<*mut FuncDeclHandle>,
    pub(crate) solver_handle_cache: Vec<*mut Z3SolverHandle>,
    pub(crate) optimize_handle_cache: Vec<*mut OptimizeHandle>,
    pub(crate) fixedpoint_handle_cache: Vec<*mut FixedpointHandle>,
    pub(crate) tactic_handle_cache: Vec<*mut TacticHandle>,
    /// Simplifier handles created via `Z3_mk_simplifier` and the simplifier
    /// combinators. Arena-owned; freed at `Z3_del_context` (so
    /// `Z3_simplifier_inc_ref`/`_dec_ref` are bookkeeping-only no-ops).
    pub(crate) simplifier_handle_cache: Vec<*mut SimplifierHandle>,
    pub(crate) stats_handle_cache: Vec<*mut StatsHandle>,
    pub(crate) model_cache: Vec<*mut ModelHandle>,
    /// Function-interpretation handles produced by `Z3_model_get_func_interp`
    /// (arity > 0 model function tables). Non-RC arena, freed at
    /// `Z3_del_context`; each references (but does not own) entries in
    /// `func_entry_cache`.
    pub(crate) func_interp_cache: Vec<*mut FuncInterpHandle>,
    /// Function-interpretation entry handles (one point of a finite map).
    /// The sole owner of these boxes; drained at `Z3_del_context`.
    pub(crate) func_entry_cache: Vec<*mut FuncEntryHandle>,
    pub(crate) params_cache: Vec<*mut ParamsHandle>,
    /// Parameter-descriptor handles produced by `Z3_optimize_get_param_descrs`
    /// (and any future `*_get_param_descrs`). Arena-owned; freed at
    /// `Z3_del_context`.
    pub(crate) param_descrs_cache: Vec<*mut ParamDescrsHandle>,
    pub(crate) ast_vector_cache: Vec<*mut AstVectorHandle>,
    /// AST-map handles created via `Z3_mk_ast_map`. Arena-owned; freed at
    /// `Z3_del_context`.
    pub(crate) ast_map_cache: Vec<*mut AstMapHandle>,
    pub(crate) pattern_cache: Vec<*mut PatternHandle>,
    /// Goal handles created via `Z3_mk_goal` or produced as tactic subgoals.
    pub(crate) goal_cache: Vec<*mut GoalHandle>,
    /// Apply-result handles produced by `Z3_tactic_apply`.
    pub(crate) apply_result_cache: Vec<*mut ApplyResultHandle>,
    /// Probe handles created via `Z3_mk_probe` / the probe combinators.
    pub(crate) probe_cache: Vec<*mut ProbeHandle>,
    /// Incremental parser-context handles created via `Z3_mk_parser_context`.
    /// Arena-owned; freed at `Z3_del_context`.
    pub(crate) parser_context_cache: Vec<*mut ParserContextHandle>,
    /// This context's nonzero 27-bit handle salt (see [`HANDLE_SALT_MASK`]):
    /// embedded in every term/SORT/FUNC-DECL AST handle this context mints and
    /// verified at checked decode boundaries, so foreign-context handles fail
    /// CLOSED instead of decoding to an unrelated object.
    pub(crate) handle_salt: u32,
    /// Stable semantic sort IDs: same Sort → same ID within a context (#6580).
    pub(crate) sort_ids: HashMap<Sort, c_uint>,
    /// Next available sort ID (monotonically increasing, starting at 1).
    pub(crate) next_sort_id: c_uint,
    /// Decode table for SORT-AST handles: `sort_id` → a live `SortHandle` of
    /// that semantic sort (the FIRST handle allocated for the id). Filled by
    /// [`alloc_sort`] (the single sort-allocation path — every `Z3_sort` flows
    /// through it), so it can never desync from `sort_ids`. Slot 0 is unused
    /// (ids start at 1); unfilled slots are null. Non-owning aliases into
    /// `sort_cache`.
    pub(crate) sort_ast_handles: Vec<*mut SortHandle>,
    /// Value-canonical interning of FUNC-DECL-AST handles: a [`DeclAstKey`]
    /// (the declaration's semantic identity) → index into
    /// [`Self::decl_ast_handles`]. Populated lazily by `Z3_func_decl_to_ast`
    /// (zero cost on the hot decl-creation path). Two `Z3_func_decl` handles
    /// with the same name/domain/range/params/dt-op therefore mint the SAME
    /// tagged ast — required for z3py's `as_ast()` equality/hash contract.
    pub(crate) decl_ast_ids: HashMap<DeclAstKey, u32>,
    /// Decode table for FUNC-DECL-AST handles: interned index → the canonical
    /// `FuncDeclHandle` (the first handle presented for that key). Non-owning
    /// aliases into `func_decl_cache`.
    pub(crate) decl_ast_handles: Vec<*mut FuncDeclHandle>,
    /// Signature registry for `Z3_mk_map`: function NAME → the exact
    /// `FuncDecl` first mapped under that name.
    ///
    /// SOUNDNESS: AY's array-map term is `App("map[f]", args)` — it captures
    /// the mapped function by NAME only, and the eager select rewrite
    /// (`select(map[f](a..), i) → f(select(a, i)..)`) also emits `f` by name.
    /// Two distinct decls both named `f` with different signatures would alias
    /// onto ONE symbol, silently conflating two different functions (a
    /// wrong-verdict channel). `Z3_mk_map` therefore refuses (Z3_INVALID_ARG,
    /// fail-close) a map over a name already mapped at a different signature.
    pub(crate) map_fn_sigs: HashMap<String, FuncDecl>,
    /// Next available func_decl ID (monotonically increasing, starting at 1).
    /// Backs `Z3_get_func_decl_id`: each cached `FuncDeclHandle` is stamped with
    /// a distinct id, stable for the life of the context (AY has no global decl
    /// numbering, so this is an honest per-context identity, like `sort_id`).
    pub(crate) next_decl_id: c_uint,
    /// True iff this context was created via `Z3_mk_context_rc` (z3py-style RC
    /// discipline). When false, `inc_ref`/`dec_ref` are no-ops.
    pub(crate) ref_counted: bool,
    /// Per-`Term` reference counts for RC contexts (BOOKKEEPING ONLY).
    ///
    /// Tracks how many `inc_ref` calls are outstanding for each interned term
    /// so that an unbalanced `dec_ref` is detected (`Z3_DEC_REF_ERROR`). A
    /// `Term` is NEVER freed when its count reaches zero — the entry is simply
    /// removed. Terms are arena-interned and live until `Z3_del_context`.
    pub(crate) ast_refcounts: HashMap<Term, u64>,
    /// Rendered Alethe proof texts backing proof-AST handles (#phase3-proof).
    ///
    /// `Z3_solver_get_proof` returns an opaque `Z3_ast` handle tagged with
    /// [`PROOF_AST_TAG`] and authenticated by this context's handle salt; its
    /// low bits index into this vector. The text is the solver's real exporter
    /// output (`Solver::export_last_proof_alethe`); it is never fabricated.
    /// `Z3_ast_to_string` recognizes the tag and returns the indexed text. These
    /// handles live until `Z3_del_context`.
    pub(crate) proof_texts: Vec<String>,
    /// Arena of Real-Closed-Field numerals (`Z3_rcf_num` handles). Each is a
    /// `Box::into_raw` of an exact [`rcf::RcfNum`] (an `ay_nra::RealScalar`);
    /// `Z3_rcf_*` producers push here and hand back the raw pointer, and the
    /// arena frees every box exactly once at `Z3_del_context` (so `Z3_rcf_del`
    /// is bookkeeping-only, matching AY's non-RC handle discipline).
    pub(crate) rcf_num_cache: Vec<*mut RcfNum>,
    /// Backing store for irrational algebraic-number ASTs (`Z3_algebraic_*`
    /// results). A `Z3_ast` tagged with [`ALGEBRAIC_AST_TAG`] and authenticated
    /// by this context's handle salt indexes this vector; the stored
    /// [`ay_nra::RealScalar`] is the exact value, read back by the
    /// algebraic-number entry points (sign / compare / get_poly / interval).
    /// Rational results keep flowing through the ordinary numeral-AST path.
    pub(crate) algebraic_values: Vec<ay_nra::RealScalar>,
    /// Context-global, theory-internal background axioms asserted into the shared
    /// engine at every solve site (see [`assert_background_axioms`]). Holds:
    ///   * special-relation ORDER axioms (reflexive/antisym/transitive + total/
    ///     tree/piecewise) over the fresh predicates minted by
    ///     `Z3_mk_{linear,partial,tree,piecewise_linear}_order`, and
    ///   * the `Char`-sort range invariant `0 <= x <= 196607` for every
    ///     `Char`-sorted term (emitted from [`record_ast_sort`]),
    ///   * the finite-domain range invariant `0 <= x <= size-1` for every
    ///     `Sort::FiniteDomain`-sorted term (same mechanism as `Char`), and
    ///   * the array-extensionality witness axiom
    ///     `a != b => select(a, k) != select(b, k)` for every witness `k`
    ///     minted by `Z3_mk_array_ext`.
    /// SOUNDNESS: every entry is a pure constraint over a FRESH predicate /
    /// witness / a bounded code point, so it can only SHRINK the model set — it
    /// can never flip a Z3-unsat into an AY-sat. Each is satisfiable in
    /// isolation, so unconditional injection introduces no spurious unsat. NOT
    /// added to any handle's `assertions`, so `Z3_solver_get_assertions` /
    /// unsat-core stay faithful (theory-internal, exactly like Z3's
    /// special-relations theory).
    pub(crate) background_axioms: Vec<Term>,
    /// Durable defining equations installed by `Z3_add_rec_def`.
    ///
    /// These are context-global declaration semantics, not handle assertions:
    /// every Solver and Optimize decision reloads them after replacing its
    /// handle-local goal. Keeping them separate from theory-internal background
    /// axioms preserves the latter's stronger "fresh and independently
    /// satisfiable" invariant (a recursive equation itself may be inconsistent).
    pub(crate) global_definition_axioms: Vec<Term>,
    /// Recursive definitions registered by `Z3_add_rec_def`, keyed by the
    /// defined function's name (P1.1).
    ///
    /// Twin of the SMT-LIB path's `fun_defs`: every solve site attempts a
    /// bounded check-time expansion of the goal through
    /// [`ay_dpll::api::Solver::try_expand_rec_defs`]. A fully-expanded goal is
    /// solved WITHOUT the quantified defining axioms (the goal itself carries
    /// the definition, which is what lets genuinely recursive definitions
    /// decide `sat`); any expansion failure keeps today's axiom-injected goal
    /// and DEMOTES an engine `sat` to `unknown` — a recursively defined
    /// function must never reach a released `sat` as a plain uninterpreted
    /// function. Context-global and never popped (z3 parity).
    pub(crate) rec_fun_defs: HashMap<String, ay_dpll::api::RecFunDef>,
    /// Names declared through `Z3_mk_rec_func_decl` (rec-DECLARED). A name
    /// here that is absent from [`Self::rec_fun_defs`] is an UNDEFINED
    /// recursive declaration: any check whose expansion would unfold a
    /// defined body that reaches such a name fails closed (real z3 4.15.4
    /// answers `unsat` in that window while the plain-UF reading answers
    /// `sat` — AY releases neither; see
    /// `solver::rec_defs_tainted_by_undefined`). Builtin-conflating names
    /// (`+`, `and`, …) are deliberately NOT recorded: they can never receive
    /// a definition (`Z3_add_rec_def` rejects them) and their applications
    /// ARE the builtin operator, identical in both solvers.
    pub(crate) rec_declared_names: std::collections::HashSet<String>,
    /// Index of each recursive definition's defining axiom inside
    /// [`Self::global_definition_axioms`], keyed by function name, so a
    /// RE-definition REPLACES its old axiom instead of leaving both equations
    /// live (stale old-body axioms could manufacture a spurious residual-mode
    /// UNSAT that z3, which keeps one definition, would not produce).
    pub(crate) rec_def_axiom_index: HashMap<String, usize>,
    /// Dedup set: `(term, inclusive upper bound)` pairs whose `0 <= t <= hi`
    /// range invariant has already been pushed to `background_axioms`
    /// (`hi = 196607` for `Char`, `hi = size-1` for a finite-domain sort), so a
    /// re-`record_ast_sort` of the same interned term does not duplicate the
    /// bound — while the SAME term recorded at a DIFFERENT bound still gets its
    /// own (sound, conjoined) invariant.
    pub(crate) range_bounded: std::collections::HashSet<(Term, i64)>,
    /// Cache of array-extensionality witness indices minted by
    /// `Z3_mk_array_ext`, keyed by the (ordered) argument pair, so repeated
    /// calls on the same `(a, b)` return the IDENTICAL witness AST and inject
    /// its axiom exactly once (matching Z3, where `ext(a,b)` is a hash-consed
    /// application).
    pub(crate) array_ext_cache: HashMap<(Term, Term), Z3_ast>,
    /// Cache of char→BV witness constants minted by `Z3_mk_char_to_bv`, keyed
    /// by the underlying char code-point term, so repeated calls return the
    /// IDENTICAL BV18 AST and inject the `bv2int(v) = code` pin exactly once
    /// (matching Z3, where `char.to_bv ch` is a hash-consed application).
    pub(crate) char_to_bv_cache: HashMap<Term, Z3_ast>,
    /// Cache of special-relation predicates keyed by `(kind_tag, domain sort,
    /// id)`, so repeated `Z3_mk_*_order(c, a, id)` with the same triple return
    /// the IDENTICAL func_decl and inject the order axioms exactly once (Z3
    /// parity). `kind_tag`: 0=partial, 1=linear, 2=tree, 3=piecewise-linear.
    pub(crate) special_relation_cache: HashMap<(u8, Sort, c_uint), Z3_func_decl>,
    /// Monomorphic instances of polymorphic declarations (#poly-inst).
    ///
    /// `Z3_mk_app` on a decl whose signature mentions a [`Sort::TypeVar`]
    /// unifies the type variables against the actual argument sorts and
    /// applies a monomorphic INSTANCE decl (same name, concrete signature) —
    /// matching libz3, which instantiates `f : α → α` at the call sort.
    /// Keyed by `(decl name, concrete argument sorts)` so the same
    /// instantiation always reuses the IDENTICAL instance decl.
    pub(crate) poly_decl_instances: HashMap<(String, Vec<Sort>), FuncDecl>,
    /// Transitive-closure predicates minted by `Z3_mk_transitive_closure`,
    /// keyed by the underlying relation's `(name, domain sort)` so a repeated
    /// call on the same relation returns the IDENTICAL decl (libz3 parity,
    /// probed 2026-07-09). Each registration also drives the SAT model-check
    /// gate in `check_solver_handle`: a SAT verdict on a context with TC
    /// registrations is only released after the model's TC interpretation is
    /// verified to BE the reflexive-transitive closure of the model's R
    /// interpretation (else the check reports unknown). The partial axioms
    /// asserted as background (`R ⊆ TC`, reflexivity, transitivity) make UNSAT
    /// sound on their own; the gate is what makes SAT sound, because a least
    /// fixed point is not finitely FO-axiomatizable.
    pub(crate) transitive_closure_regs: Vec<TcRegistration>,
}

impl Z3Context {
    /// Report whether the shared decision engine can still be used.
    ///
    /// Unlike `claim_decision_owner`, this does not alter ownership. Existing
    /// handles call it after a transaction has poisoned the context so they
    /// cannot bypass the fail-closed latch merely because they claimed their
    /// family before the failure.
    pub(crate) fn decision_engine_is_usable(&mut self, operation: &str) -> bool {
        let Some(reason) = self.decision_engine_poisoned.clone() else {
            return true;
        };
        self.last_error = Z3_INVALID_USAGE;
        self.error_msg = Some(format!(
            "{operation}: context SMT decision engine is permanently unavailable after an \
             incomplete mutation: {reason}"
        ));
        false
    }

    /// Retire every copied decision result owned by handles on this context.
    ///
    /// Parser transactions and durable global-definition mutations affect the
    /// context rather than one handle. Clearing only the initiating handle
    /// would leave models/cores/statistics copied by sibling handles falsely
    /// authoritative under the changed (or partially changed) semantics.
    pub(crate) fn clear_decision_check_artifacts(&mut self) {
        for &handle in &self.solver_handle_cache {
            if !handle.is_null() {
                // SAFETY: cache entries are live arena-owned allocations and
                // decision operations are single-threaded per context.
                unsafe { (*handle).clear_check_artifacts() };
            }
        }
        for &handle in &self.optimize_handle_cache {
            if !handle.is_null() {
                // SAFETY: same arena/single-threaded invariant as above.
                unsafe { (*handle).clear_check_artifacts() };
            }
        }
    }

    /// Claim the shared SMT decision engine for one API family, or fail closed
    /// when the other family already owns it.
    pub(crate) fn claim_decision_owner(
        &mut self,
        requested: DecisionOwnerFamily,
        operation: &str,
    ) -> bool {
        if let Some(reason) = &self.decision_engine_poisoned {
            self.last_error = Z3_INVALID_USAGE;
            self.error_msg = Some(format!(
                "{operation}: context SMT decision engine is permanently unavailable after an \
                 incomplete mutation: {reason}"
            ));
            return false;
        }
        match self.decision_owner {
            None => {
                self.decision_owner = Some(requested);
                true
            }
            Some(owner) if owner == requested => true,
            Some(owner) => {
                self.last_error = Z3_INVALID_USAGE;
                self.error_msg = Some(format!(
                    "{operation}: context SMT decision engine is already owned by the {owner:?} \
                     family; use a separate Z3_context for {requested:?}"
                ));
                false
            }
        }
    }

    /// Permanently prevent the shared SMT engine from admitting later work.
    pub(crate) fn poison_decision_engine(&mut self, reason: String) {
        self.clear_decision_check_artifacts();
        self.decision_engine_poisoned = Some(reason.clone());
        self.last_error = Z3_EXCEPTION;
        self.error_msg = Some(reason);
    }
}

/// Admit a cross-context translation only when every source semantic
/// obligation is carried by the translated term DAG itself.
///
/// Several Z3-compat features deliberately live in context metadata rather
/// than in a term: range/order background axioms, recursive-definition axioms,
/// and transitive-closure registrations plus their SAT verifier. The current
/// deep-copy primitive only re-interns terms. Silently copying a handle/AST
/// without this metadata can weaken its meaning and turn an UNSAT source query
/// into SAT, so all translation surfaces share this conservative gate until an
/// atomic metadata-transfer protocol exists.
pub(crate) fn ensure_cross_context_translation_semantics(
    source: &Z3Context,
    target: &mut Z3Context,
    operation: &str,
) -> bool {
    let mut missing = Vec::new();
    if !source.background_axioms.is_empty() {
        missing.push("background range/order axioms");
    }
    if !source.global_definition_axioms.is_empty() || !source.rec_fun_defs.is_empty() {
        missing.push("recursive-definition axioms");
    }
    if !source.transitive_closure_regs.is_empty() {
        missing.push("transitive-closure registrations/verifier state");
    }
    // Quantifier attributes are AST-local. The metadata-transfer walk below
    // rejects them only when their quantifier is reachable from a requested
    // root; inspecting the whole source context here would poison unrelated
    // translations. The public-bound maps are likewise populated for every C
    // quantifier and are not, by themselves, evidence of FiniteSet use.
    if !source.finite_set_sorts.is_empty()
        || !source.finite_set_apps.is_empty()
        || !source.finite_set_term_provenance.is_empty()
        || !source.finite_set_reachable_axioms.is_empty()
    {
        missing.push("FiniteSet public sorts/applications and decision gates");
    }
    if missing.is_empty() {
        return true;
    }
    target.last_error = Z3_INVALID_USAGE;
    target.error_msg = Some(format!(
        "{operation}: cross-context translation cannot yet transfer source semantic metadata ({}); refusing to weaken semantics",
        missing.join(", ")
    ));
    false
}

fn translation_metadata_error(target: &mut Z3Context, operation: &str, detail: &str) -> bool {
    target.last_error = Z3_INVALID_USAGE;
    target.error_msg = Some(format!(
        "{operation}: cross-context translation metadata conflict: {detail}"
    ));
    false
}

fn sort_contains(root: &Sort, needle: &Sort) -> bool {
    if root == needle {
        return true;
    }
    match root {
        Sort::Array(array) => {
            sort_contains(&array.index_sort, needle) || sort_contains(&array.element_sort, needle)
        }
        Sort::Seq(element) => sort_contains(element, needle),
        Sort::Datatype(datatype) => datatype.constructors.iter().any(|constructor| {
            constructor
                .fields
                .iter()
                .any(|field| sort_contains(&field.sort, needle))
        }),
        _ => false,
    }
}

fn sort_mentions_datatype(sort: &Sort) -> bool {
    match sort {
        Sort::Datatype(_) => true,
        Sort::Array(array) => {
            sort_mentions_datatype(&array.index_sort) || sort_mentions_datatype(&array.element_sort)
        }
        Sort::Seq(element) => sort_mentions_datatype(element),
        _ => false,
    }
}

/// Canonical observable `(name, sort)` pairs for C-constructed quantifier
/// binders. Bound terms are metadata-only and need not occur in the logical
/// DAG, so both their public symbol identity and AST sort side table must take
/// part in translation collision checks.
fn public_bound_term_descriptors(
    context: &Z3Context,
    quantifier: Term,
    bounds: &[Term],
) -> Option<Vec<(SymbolKey, Sort)>> {
    let engine_bounds = context.solver.quantifier_bound_vars(quantifier)?;
    if engine_bounds.len() != bounds.len() {
        return None;
    }
    Some(
        bounds
            .iter()
            .zip(engine_bounds)
            .map(|(&bound, (engine_name, engine_sort))| {
                let symbol = context
                    .ffi_const_metadata
                    .get(&bound)
                    .map(|(_, symbol)| symbol.clone())
                    .unwrap_or(SymbolKey::String(engine_name));
                let sort = lookup_ast_sort(context, term_to_ast(context, bound))
                    .cloned()
                    .unwrap_or(engine_sort);
                (symbol, sort)
            })
            .collect(),
    )
}

/// Canonical observable `(name, sort)` pairs for parsed quantifier binders.
/// Parsed SMT-LIB names are string symbols in the core binder vector; only
/// their public sorts require a separate side table.
fn parsed_public_bound_descriptors(
    context: &Z3Context,
    quantifier: Term,
    public_sorts: &[Sort],
) -> Option<Vec<(SymbolKey, Sort)>> {
    let engine_bounds = context.solver.quantifier_bound_vars(quantifier)?;
    if engine_bounds.len() != public_sorts.len() {
        return None;
    }
    Some(
        engine_bounds
            .into_iter()
            .zip(public_sorts)
            .map(|((name, _), sort)| (SymbolKey::String(name), sort.clone()))
            .collect(),
    )
}

/// Carry C-API declaration/display identity alongside a translated term DAG.
///
/// `Solver::translate_terms_from` faithfully rebuilds core nodes, whose private
/// names remain semantically authoritative, but the exact caller-visible Z3
/// symbols live in [`Z3Context`] metadata. Walk the source/destination DAGs in
/// lockstep, preflight all target collisions, and then copy only metadata
/// reachable from the translated roots. A conflict fails closed instead of
/// letting two context-local private identities alias.
pub(crate) fn transfer_cross_context_ffi_metadata(
    source: &Z3Context,
    target: &mut Z3Context,
    source_roots: &[Term],
    target_roots: &[Term],
    operation: &str,
) -> bool {
    if source_roots.len() != target_roots.len() {
        return translation_metadata_error(target, operation, "root count changed during copy");
    }

    let mut pairs: HashMap<Term, Term> = HashMap::new();
    let mut stack: Vec<(Term, Term)> = source_roots
        .iter()
        .copied()
        .zip(target_roots.iter().copied())
        .collect();
    let mut relevant_names = std::collections::HashSet::new();
    let mut relevant_sorts = std::collections::HashSet::new();
    let mut relevant_map_functions = std::collections::HashSet::new();
    let mut quantifier_public_bound_copies: HashMap<Term, (Vec<Term>, Vec<Sort>)> = HashMap::new();
    let mut parsed_quantifier_public_bound_sort_copies: HashMap<Term, Vec<Sort>> = HashMap::new();
    let mut source_public_bound_descriptors: HashMap<Term, Vec<(SymbolKey, Sort)>> = HashMap::new();
    while let Some((source_term, target_term)) = stack.pop() {
        if let Some(existing) = pairs.insert(source_term, target_term) {
            if existing != target_term {
                return translation_metadata_error(
                    target,
                    operation,
                    "shared source node was translated to multiple target nodes",
                );
            }
            continue;
        }

        relevant_sorts.insert(source.solver.term_sort(source_term));
        match source.solver.term_kind(source_term) {
            TermKind::App { name, .. } => {
                if let Some(function) = name
                    .strip_prefix("map[")
                    .and_then(|name| name.strip_suffix(']'))
                {
                    relevant_map_functions.insert(function.to_string());
                    // `map[f]` captures the mapped declaration by its private
                    // core name even though `f` is not a child term. Include
                    // that hidden dependency in the ordinary declaration
                    // identity/signature preflight, or two contexts can reuse
                    // the same private name for different public functions.
                    relevant_names.insert(function.to_string());
                }
                relevant_names.insert(name);
            }
            TermKind::Var { name } => {
                relevant_names.insert(name);
            }
            _ => {}
        }
        if let Some(vars) = source.solver.quantifier_bound_vars(source_term) {
            relevant_sorts.extend(vars.iter().map(|(_, sort)| sort.clone()));
            if !source
                .quantifier_public_bound_terms
                .contains_key(&source_term)
                && !source
                    .parsed_quantifier_public_bound_sorts
                    .contains_key(&source_term)
            {
                // A tactic/native-produced quantifier can legitimately have no
                // FFI side-table entry. Its observable fallback is still exact:
                // string binder names plus core sorts. Record it so translation
                // cannot silently borrow different target-side metadata from a
                // hash-consed quantifier.
                source_public_bound_descriptors.insert(
                    target_term,
                    vars.into_iter()
                        .map(|(name, sort)| (SymbolKey::String(name), sort))
                        .collect(),
                );
            }
        }

        // C-API binder terms are public-AST metadata rather than children of
        // the core quantifier node. Graft even unused binders explicitly, then
        // feed them through this same lockstep walk so their exact SymbolKey,
        // declaration identity, and sort metadata receive the ordinary
        // transactional collision checks below.
        if let Some(source_bounds) = source.quantifier_public_bound_terms.get(&source_term) {
            let target_bounds = target
                .solver
                .translate_terms_from(&source.solver, source_bounds);
            if source_bounds.len() != target_bounds.len() {
                return translation_metadata_error(
                    target,
                    operation,
                    "quantifier public-bound count changed during copy",
                );
            }
            let public_sorts: Vec<Sort> = source_bounds
                .iter()
                .map(|&bound| {
                    lookup_ast_sort(source, term_to_ast(source, bound))
                        .cloned()
                        .unwrap_or_else(|| source.solver.term_sort(bound))
                })
                .collect();
            let Some(descriptors) =
                public_bound_term_descriptors(source, source_term, source_bounds)
            else {
                return translation_metadata_error(
                    target,
                    operation,
                    "quantifier public-bound metadata does not match its core binders",
                );
            };
            if source_public_bound_descriptors
                .get(&target_term)
                .is_some_and(|existing| existing != &descriptors)
            {
                return translation_metadata_error(
                    target,
                    operation,
                    "source quantifier has conflicting public-bound representations",
                );
            }
            source_public_bound_descriptors
                .entry(target_term)
                .or_insert(descriptors);
            if quantifier_public_bound_copies
                .get(&target_term)
                .is_some_and(|(existing_bounds, existing_sorts)| {
                    existing_bounds != &target_bounds || existing_sorts != &public_sorts
                })
            {
                return translation_metadata_error(
                    target,
                    operation,
                    "shared translated quantifier has different public-bound metadata",
                );
            }
            stack.extend(
                source_bounds
                    .iter()
                    .copied()
                    .zip(target_bounds.iter().copied()),
            );
            relevant_sorts.extend(public_sorts.iter().cloned());
            quantifier_public_bound_copies
                .entry(target_term)
                .or_insert((target_bounds, public_sorts));
        }
        if let Some(public_sorts) = source
            .parsed_quantifier_public_bound_sorts
            .get(&source_term)
        {
            let Some(descriptors) =
                parsed_public_bound_descriptors(source, source_term, public_sorts)
            else {
                return translation_metadata_error(
                    target,
                    operation,
                    "parsed quantifier public-bound metadata does not match its core binders",
                );
            };
            if source_public_bound_descriptors
                .get(&target_term)
                .is_some_and(|existing| existing != &descriptors)
            {
                return translation_metadata_error(
                    target,
                    operation,
                    "source quantifier has conflicting public-bound representations",
                );
            }
            source_public_bound_descriptors
                .entry(target_term)
                .or_insert(descriptors);
            if parsed_quantifier_public_bound_sort_copies
                .get(&target_term)
                .is_some_and(|existing| existing != public_sorts)
            {
                return translation_metadata_error(
                    target,
                    operation,
                    "shared translated quantifier has different parsed public-bound sorts",
                );
            }
            relevant_sorts.extend(public_sorts.iter().cloned());
            parsed_quantifier_public_bound_sort_copies
                .entry(target_term)
                .or_insert_with(|| public_sorts.clone());
        }

        let source_children = source.solver.term_children(source_term);
        let target_children = target.solver.term_children(target_term);
        if source_children.len() != target_children.len() {
            return translation_metadata_error(
                target,
                operation,
                "term child count changed during copy",
            );
        }
        stack.extend(source_children.into_iter().zip(target_children));

        let source_triggers = source.solver.quantifier_triggers(source_term);
        let target_triggers = target.solver.quantifier_triggers(target_term);
        match (source_triggers, target_triggers) {
            (None, None) => {}
            (Some(source_sets), Some(target_sets)) if source_sets.len() == target_sets.len() => {
                for (source_set, target_set) in source_sets.into_iter().zip(target_sets) {
                    if source_set.len() != target_set.len() {
                        return translation_metadata_error(
                            target,
                            operation,
                            "quantifier trigger width changed during copy",
                        );
                    }
                    stack.extend(source_set.into_iter().zip(target_set));
                }
            }
            _ => {
                return translation_metadata_error(
                    target,
                    operation,
                    "quantifier triggers changed during copy",
                );
            }
        }
    }

    // The term-store graft preserves datatype-shaped sorts but does not replay
    // the declaration into the target executor's datatype registry. Publishing
    // such a term would let logic detection and datatype axioms treat it as an
    // ordinary uninterpreted sort. Reject the translation until declarations
    // can be replayed transactionally together with their exact C identities.
    if relevant_sorts.iter().any(sort_mentions_datatype) {
        return translation_metadata_error(
            target,
            operation,
            "reachable datatype declarations cannot yet be translated transactionally",
        );
    }

    // Quantifier hints are keyed by core Term today. Non-default attributes
    // still cannot be remapped because no-pattern terms are metadata-only, but
    // a DEFAULT quantifier must nevertheless install an exact default latch in
    // the destination. Otherwise a target `_ex` constructor could attach qid,
    // skolemid, or a different weight to the same hash-consed term and
    // retroactively change the translated AST's public introspection.
    let mut quantifier_metadata_copies = Vec::new();
    for (source_term, target_term) in &pairs {
        if !matches!(
            source.solver.term_kind(*source_term),
            TermKind::Forall | TermKind::Exists
        ) {
            continue;
        }
        let metadata = source
            .quantifier_ffi_metadata
            .get(source_term)
            .cloned()
            .unwrap_or_default();
        if !metadata.is_default()
            || source.solver.quantifier_id(*source_term).is_some()
            || source.solver.skolem_id(*source_term).is_some()
        {
            return translation_metadata_error(
                target,
                operation,
                "quantifier weight/qid/skolemid/no-pattern attributes cannot be translated without changing public AST identity",
            );
        }
        if target
            .quantifier_ffi_metadata
            .get(target_term)
            .is_some_and(|existing| existing != &metadata)
            || target
                .quantifier_weights
                .get(target_term)
                .is_some_and(|weight| *weight != metadata.weight)
            || target
                .quantifier_no_patterns
                .get(target_term)
                .is_some_and(|patterns| !patterns.is_empty())
            || target.solver.quantifier_id(*target_term).is_some()
            || target.solver.skolem_id(*target_term).is_some()
        {
            return translation_metadata_error(
                target,
                operation,
                "translated quantifier has different target metadata",
            );
        }
        quantifier_metadata_copies.push((*target_term, metadata));
    }

    // Public binder identity is part of a quantifier AST's observable C-API
    // contract. Preflight both the quantifier-to-binder association and every
    // binder's public sort side-table before committing any metadata.
    for (quantifier, source_descriptors) in &source_public_bound_descriptors {
        if let Some(target_bounds) = target.quantifier_public_bound_terms.get(quantifier) {
            let Some(target_descriptors) =
                public_bound_term_descriptors(target, *quantifier, target_bounds)
            else {
                return translation_metadata_error(
                    target,
                    operation,
                    "target quantifier public-bound metadata does not match its core binders",
                );
            };
            if &target_descriptors != source_descriptors {
                return translation_metadata_error(
                    target,
                    operation,
                    "translated quantifier has different public-bound name/sort metadata",
                );
            }
        }
        if let Some(target_sorts) = target.parsed_quantifier_public_bound_sorts.get(quantifier) {
            let Some(target_descriptors) =
                parsed_public_bound_descriptors(target, *quantifier, target_sorts)
            else {
                return translation_metadata_error(
                    target,
                    operation,
                    "target parsed quantifier metadata does not match its core binders",
                );
            };
            if &target_descriptors != source_descriptors {
                return translation_metadata_error(
                    target,
                    operation,
                    "translated quantifier has different parsed public-bound name/sort metadata",
                );
            }
        }
    }
    for (quantifier, (bounds, public_sorts)) in &quantifier_public_bound_copies {
        if target
            .quantifier_public_bound_terms
            .get(quantifier)
            .is_some_and(|existing| existing != bounds)
        {
            return translation_metadata_error(
                target,
                operation,
                "translated quantifier has different public-bound terms",
            );
        }
        for (&bound, public_sort) in bounds.iter().zip(public_sorts) {
            if lookup_ast_sort(target, term_to_ast(target, bound))
                .is_some_and(|existing| existing != public_sort)
            {
                return translation_metadata_error(
                    target,
                    operation,
                    "translated quantifier bound has a different public sort",
                );
            }
        }
    }
    for (quantifier, public_sorts) in &parsed_quantifier_public_bound_sort_copies {
        if target
            .parsed_quantifier_public_bound_sorts
            .get(quantifier)
            .is_some_and(|existing| existing != public_sorts)
        {
            return translation_metadata_error(
                target,
                operation,
                "translated parsed quantifier has different public-bound sorts",
            );
        }
    }

    let const_copies: Vec<(Term, String, SymbolKey, Sort)> = pairs
        .iter()
        .filter_map(|(source_term, target_term)| {
            source
                .ffi_const_metadata
                .get(source_term)
                .map(|(identity, symbol)| {
                    (
                        *target_term,
                        identity.clone(),
                        symbol.clone(),
                        source.solver.term_sort(*source_term),
                    )
                })
        })
        .collect();
    for (term, identity, symbol, sort) in &const_copies {
        if target.ffi_const_metadata.get(term).is_some_and(
            |(existing_identity, existing_symbol)| {
                existing_identity != identity || existing_symbol != symbol
            },
        ) {
            return translation_metadata_error(
                target,
                operation,
                "translated constant node already has different public identity",
            );
        }
        if target
            .ffi_const_terms_by_identity
            .get(identity)
            .is_some_and(|existing| existing != term)
        {
            return translation_metadata_error(
                target,
                operation,
                "translated constant private identity is already in use",
            );
        }
        if target
            .ffi_const_cache
            .get(&(symbol.clone(), sort.clone()))
            .is_some_and(|existing| existing != term)
        {
            return translation_metadata_error(
                target,
                operation,
                "translated constant public symbol/signature is already bound differently",
            );
        }
    }

    let decl_symbol_copies: Vec<(String, SymbolKey)> = relevant_names
        .iter()
        .filter_map(|name| {
            source
                .ffi_decl_symbols
                .get(name)
                .map(|symbol| (name.clone(), symbol.clone()))
        })
        .collect();
    for (name, symbol) in &decl_symbol_copies {
        if target
            .ffi_decl_symbols
            .get(name)
            .is_some_and(|existing| existing != symbol)
        {
            return translation_metadata_error(
                target,
                operation,
                "translated function private identity has a different public symbol",
            );
        }
    }

    let function_copies: Vec<((SymbolKey, Vec<Sort>, Sort), String, Option<FuncDecl>)> = source
        .ffi_func_names
        .iter()
        .filter(|(_, name)| relevant_names.contains(*name))
        .map(|(key, name)| {
            (
                key.clone(),
                name.clone(),
                source.ffi_func_decls.get(key).cloned(),
            )
        })
        .collect();
    for (key, name, decl) in &function_copies {
        if target
            .ffi_func_names
            .get(key)
            .is_some_and(|existing| existing != name)
            || target
                .ffi_func_names
                .iter()
                .any(|(existing_key, existing_name)| existing_key != key && existing_name == name)
        {
            return translation_metadata_error(
                target,
                operation,
                "translated function identity collides with a target declaration",
            );
        }
        if let Some(decl) = decl {
            if target
                .ffi_func_decls
                .get(key)
                .is_some_and(|existing| existing != decl)
            {
                return translation_metadata_error(
                    target,
                    operation,
                    "translated function signature is already bound differently",
                );
            }
        }
    }

    let sort_copies: Vec<(Sort, SymbolKey)> = source
        .ffi_sort_symbols
        .iter()
        .filter(|(sort, _)| {
            relevant_sorts
                .iter()
                .any(|relevant| sort_contains(relevant, sort))
        })
        .map(|(sort, symbol)| (sort.clone(), symbol.clone()))
        .collect();
    for (sort, symbol) in &sort_copies {
        if target
            .ffi_sort_symbols
            .get(sort)
            .is_some_and(|existing| existing != symbol)
        {
            return translation_metadata_error(
                target,
                operation,
                "translated sort identity has a different public symbol",
            );
        }
    }

    // Array-map terms capture the mapped declaration by name. Translation
    // rebuilds the core `map[f]` node without re-running `Z3_mk_map`, so copy
    // the exact signature latch transactionally. A missing source signature or
    // a different target signature must fail closed; otherwise a later map
    // under the same name could alias a different function and fabricate
    // select-map semantics.
    let mut map_signature_copies = Vec::with_capacity(relevant_map_functions.len());
    for name in relevant_map_functions {
        let Some(decl) = source.map_fn_sigs.get(&name).cloned() else {
            return translation_metadata_error(
                target,
                operation,
                "reachable array-map term has no authenticated function signature",
            );
        };
        if target
            .map_fn_sigs
            .get(&name)
            .is_some_and(|existing| existing != &decl)
        {
            return translation_metadata_error(
                target,
                operation,
                "translated array-map function name has a different target signature",
            );
        }
        map_signature_copies.push((name, decl));
    }

    for (term, identity, symbol, sort) in const_copies {
        target
            .ffi_const_metadata
            .insert(term, (identity.clone(), symbol.clone()));
        target.ffi_const_terms_by_identity.insert(identity, term);
        target.ffi_const_cache.insert((symbol.clone(), sort), term);
        target.ffi_used_decl_names.insert(symbol.display_name());
    }
    for (name, symbol) in decl_symbol_copies {
        target.ffi_decl_symbols.insert(name, symbol.clone());
        target.ffi_used_decl_names.insert(symbol.display_name());
    }
    for (key, name, decl) in function_copies {
        target.ffi_func_names.insert(key.clone(), name);
        if let Some(decl) = decl {
            target.ffi_func_decls.insert(key, decl);
        }
    }
    for (sort, symbol) in sort_copies {
        target.ffi_sort_symbols.insert(sort, symbol);
    }
    for (quantifier, (bounds, public_sorts)) in quantifier_public_bound_copies {
        for (&bound, public_sort) in bounds.iter().zip(public_sorts) {
            let ast = term_to_ast(target, bound);
            record_ast_sort(target, ast, public_sort);
        }
        target
            .quantifier_public_bound_terms
            .insert(quantifier, bounds);
    }
    for (quantifier, public_sorts) in parsed_quantifier_public_bound_sort_copies {
        target
            .parsed_quantifier_public_bound_sorts
            .insert(quantifier, public_sorts);
    }
    for (name, decl) in map_signature_copies {
        target.map_fn_sigs.insert(name, decl);
    }
    for (term, metadata) in quantifier_metadata_copies {
        target.quantifier_weights.insert(term, metadata.weight);
        target.quantifier_ffi_metadata.insert(term, metadata);
    }
    target.next_ffi_fresh_id = target.next_ffi_fresh_id.max(source.next_ffi_fresh_id);
    true
}

/// One `Z3_mk_transitive_closure` registration (see
/// [`Z3Context::transitive_closure_regs`]).
pub(crate) struct TcRegistration {
    /// The fresh TC predicate's declaration name.
    pub(crate) tc_name: String,
    /// The underlying relation's declaration name.
    pub(crate) rel_name: String,
    /// The shared domain sort of both binary predicates.
    pub(crate) domain: Sort,
    /// The cached decl handle returned for repeated calls.
    pub(crate) handle: Z3_func_decl,
}

/// Free all non-null raw pointers in a Vec arena.
///
/// # Safety
/// Every pointer in `arena` must have been created via `Box::into_raw` and must
/// not have been freed elsewhere. Each pointer is consumed exactly once by
/// `Box::from_raw`, so double-free is impossible as long as the arena is the
/// sole owner.
unsafe fn drain_arena<T>(arena: &mut Vec<*mut T>) {
    for ptr in arena.drain(..) {
        if !ptr.is_null() {
            // SAFETY: The pointer was produced by a matching `Box::into_raw` in the
            // corresponding `Z3_mk_*`/cache-add path and stored in the context's handle cache.
            // We own it exclusively here because the Z3 C API is single-threaded per context.
            unsafe {
                let _ = Box::from_raw(ptr);
            }
        }
    }
}

impl Drop for Z3Context {
    fn drop(&mut self) {
        // Free all handle arenas (#5498, #5528).
        // SAFETY: Each cache was only ever populated by `Box::into_raw` calls
        // in the matching `cache_*`/`Z3_mk_*` paths. The `Z3Context` that owns
        // these caches is being dropped, so no other reference can observe
        // the freed pointers. `drain_arena` consumes each pointer exactly
        // once via `Box::from_raw`, so double-free is impossible.
        unsafe {
            drain_arena(&mut self.symbol_cache);
            drain_arena(&mut self.sort_cache);
            drain_arena(&mut self.func_decl_cache);
            drain_arena(&mut self.solver_handle_cache);
            drain_arena(&mut self.optimize_handle_cache);
            drain_arena(&mut self.fixedpoint_handle_cache);
            drain_arena(&mut self.tactic_handle_cache);
            drain_arena(&mut self.simplifier_handle_cache);
            drain_arena(&mut self.stats_handle_cache);
            drain_arena(&mut self.model_cache);
            // `func_interp_cache` boxes reference (but do not own) the entry
            // boxes in `func_entry_cache`; draining both frees each box exactly
            // once (the interp handles never call `Box::from_raw` on entries).
            drain_arena(&mut self.func_interp_cache);
            drain_arena(&mut self.func_entry_cache);
            drain_arena(&mut self.params_cache);
            drain_arena(&mut self.param_descrs_cache);
            drain_arena(&mut self.ast_vector_cache);
            drain_arena(&mut self.ast_map_cache);
            drain_arena(&mut self.pattern_cache);
            // `apply_result_cache` holds only the ApplyResultHandle boxes; the
            // subgoal GoalHandles they reference are owned by `goal_cache` and
            // freed there, so draining these two never double-frees a goal.
            drain_arena(&mut self.apply_result_cache);
            drain_arena(&mut self.goal_cache);
            drain_arena(&mut self.probe_cache);
            drain_arena(&mut self.parser_context_cache);
            // RCF numerals: each is a `Box::into_raw(RcfNum)`; free each once.
            drain_arena(&mut self.rcf_num_cache);
        }
    }
}

/// Configuration parameters recognized when creating a context.
pub struct Z3Config {
    pub(crate) params: Vec<(String, String)>,
}

pub struct SortHandle {
    pub(crate) sort: Sort,
    /// Stable semantic sort ID assigned per-context (#6580).
    pub(crate) sort_id: c_uint,
}

pub struct FuncDeclHandle {
    pub(crate) decl: FuncDecl,
    /// API-visible name/kind when it differs from `decl.name()` (the latter is
    /// AY's collision-proof internal solver key).
    pub(crate) symbol: Option<SymbolKey>,
    /// Indexed operator parameters (e.g., [7, 4] for extract[7:4]) (#6580 F2).
    pub(crate) params: Vec<c_int>,
    /// Stable per-context decl identity, assigned at cache time. Backs
    /// `Z3_get_func_decl_id` (distinct decls → distinct ids within a context).
    pub(crate) decl_id: c_uint,
    /// Datatype operator kind, if this func_decl is a datatype
    /// constructor/recognizer/accessor produced by `Z3_mk_datatype`.
    ///
    /// When set, `Z3_mk_app` dispatches the application through the verified
    /// `Solver::datatype_constructor`/`datatype_tester`/`datatype_selector`
    /// builders (so nullary constructors resolve to the registered constant and
    /// testers/selectors carry the right DT semantics), instead of building a
    /// generic uninterpreted application. `None` for ordinary func_decls.
    pub(crate) dt_op: Option<DatatypeOp>,
    /// Finite-set builtin provenance. A user UF may legally have the same
    /// display name and must remain `Z3_OP_UNINTERPRETED`.
    pub(crate) finite_set_op: Option<FiniteSetOp>,
}

/// Identifies a datatype operator backing a [`FuncDeclHandle`] (#phase3-dt).
///
/// Produced by `Z3_mk_datatype` and consumed by `Z3_mk_app` so a constructed
/// datatype term is built through the same path AY's SMT-LIB elaborator uses.
#[derive(Clone)]
pub(crate) enum DatatypeOp {
    /// Constructor application. Carries the full datatype definition so
    /// `Solver::datatype_constructor` can validate args and resolve nullary
    /// constructors to their registered constant.
    Constructor {
        dt: ay_dpll::api::DatatypeSort,
        ctor: String,
    },
    /// Recognizer (`is-Ctor`) test on a datatype value.
    Recognizer { ctor: String },
    /// Field accessor (selector) on a datatype value.
    Accessor { field: String, result_sort: Sort },
}

/// Small hashable discriminant of a [`DatatypeOp`], for [`DeclAstKey`].
///
/// Keeps a user decl from aliasing a datatype-op decl of the same
/// name/signature in the func-decl-ast interning (they dispatch differently in
/// `Z3_mk_app`, so they must not share a canonical decl-ast).
#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) enum DtOpKind {
    None,
    Constructor(String),
    Recognizer(String),
    Accessor(String),
}

impl DtOpKind {
    fn of(op: Option<&DatatypeOp>) -> Self {
        match op {
            None => Self::None,
            Some(DatatypeOp::Constructor { ctor, .. }) => Self::Constructor(ctor.clone()),
            Some(DatatypeOp::Recognizer { ctor }) => Self::Recognizer(ctor.clone()),
            Some(DatatypeOp::Accessor { field, .. }) => Self::Accessor(field.clone()),
        }
    }
}

/// Value-canonical identity of a func_decl for FUNC-DECL-AST interning:
/// the declaration itself (`FuncDecl` is value-`Eq`/`Hash` on
/// name/domain/range), its indexed operator parameters (so `(_ extract 7 4)`
/// and `(_ extract 3 0)` stay distinct), and the datatype-op discriminant.
#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) struct DeclAstKey {
    pub(crate) decl: FuncDecl,
    pub(crate) params: Vec<c_int>,
    pub(crate) dt_op: DtOpKind,
    pub(crate) finite_set_op: Option<FiniteSetOp>,
}

/// Internal state for a `Z3_solver` handle.
///
/// Every handle owns its own LOGICAL solver state — its assertion stack (with
/// push/pop scope markers) and the artefacts of its last check (model, unsat
/// assumptions, unknown reason, proof text). Handles created on the same
/// context share that context's term arena and its single underlying solve
/// ENGINE, but never each other's assertions: `Z3_solver_check` REPLACES the
/// engine's assertion stack with exactly this handle's assertions (via
/// `reset-assertions` + re-assert, which preserves the term arena and all
/// declarations) and materializes every queryable artefact back into the
/// handle right after the check. Two `Z3_mk_solver` handles on one context
/// are therefore fully independent, matching Z3 semantics.
pub struct Z3SolverHandle {
    /// A tactic to apply to the goal before each `check`, when this solver was
    /// produced by `Z3_mk_solver_from_tactic`. `None` for a plain `Z3_mk_solver`.
    ///
    /// Because every supported tactic is equivalence-preserving, applying it
    /// before solving yields exactly the same SAT/UNSAT verdict and a valid
    /// model — it can never change the answer. See [`TacticHandle`].
    pub(crate) tactic: Option<Tactic>,
    /// This handle's own asserted formulas (its logical assertion stack).
    pub(crate) assertions: Vec<Term>,
    /// `assertions.len()` snapshot at each `Z3_solver_push`; `Z3_solver_pop`
    /// truncates back to the popped marker.
    pub(crate) scope_markers: Vec<usize>,
    /// Assertions added via `Z3_solver_assert_and_track`, each paired with its
    /// Boolean tracking literal `p`. The IMPLICATION `(=> p a)` is what actually
    /// enters `assertions`; this parallel list records the `(p, a)` pairs so
    /// `Z3_solver_check`/`Z3_solver_check_assumptions` can pass every `p` as an
    /// assumption. That makes each tracked assertion's contribution to an UNSAT
    /// observable through `Z3_solver_get_unsat_core` (the core is a subset of the
    /// tracking literals, mirroring Z3's assert-and-track core mechanism).
    pub(crate) tracked: Vec<(Term, Term)>,
    /// `tracked.len()` snapshot at each `Z3_solver_push`, parallel to
    /// `scope_markers`, so `Z3_solver_pop` drops the tracked pairs added in the
    /// popped scope (keeping the tracking literals scope-correct).
    pub(crate) tracked_scope_markers: Vec<usize>,
    /// Model from this handle's last SAT check, materialized right after the
    /// check (a later check by any handle replaces the engine-side state).
    pub(crate) last_model: Option<Model>,
    /// The engine's raw SMT-LIB model text from the same check, captured so a
    /// `Z3_model` handle can carry the FUNCTION interpretations (arity > 0
    /// `define-fun` tables) that the parsed [`Model`] — a constants-only
    /// structure — drops. `None` when no model text was available.
    pub(crate) last_model_text: Option<String>,
    /// The last publicly admitted check outcome. The backend can retain a
    /// candidate model/core even when a later FFI trust gate rejects that
    /// candidate, so accessors must use this authority instead of inferring an
    /// outcome from whichever backend artifact happens to be present.
    pub(crate) last_check_outcome: Option<SolverCheckOutcome>,
    /// Unsat assumptions from this handle's last UNSAT
    /// `Z3_solver_check_assumptions`.
    pub(crate) last_unsat_core: Option<Vec<Term>>,
    /// SMT-LIB `:reason-unknown` from this handle's last check, if any.
    pub(crate) last_reason_unknown: Option<String>,
    /// Alethe proof text from this handle's last UNSAT check (present only
    /// when proof production was enabled at check time; never fabricated).
    pub(crate) last_proof_alethe: Option<String>,
    /// Solver statistics snapshot from this handle's last check, materialized
    /// right after the check (a later check by any handle overwrites the
    /// engine-side counters). These are the executor's REAL counters —
    /// `Z3_solver_get_statistics` reads this snapshot; nothing is fabricated.
    pub(crate) last_statistics: Option<Statistics>,
    /// User propagator registered via `Z3_solver_propagate_init` (callbacks,
    /// registered terms, user context). When present, `Z3_solver_check` runs the
    /// SOUND FINAL-CHECK LOOP (see `propagate::user_propagator_check`): SAT is
    /// only returned once the user's `final` callback raises no objection, and
    /// every user consequence is asserted as a guarded lemma before re-solving.
    pub(crate) propagator: Option<UserPropagator>,
    /// Remaining cube-and-conquer cubes for `Z3_solver_cube`, generated lazily
    /// on the first call by the REAL lookahead cube generator
    /// (`ay_sat::Solver::generate_cubes`) over this handle's Tseitin-encoded
    /// Boolean skeleton. Each cube is a list of `(atom term, polarity)` pairs;
    /// `Some(empty)` means the generator is exhausted (`Z3_solver_cube` then
    /// returns Z3's empty "rest of the space" cube). Invalidated (reset to
    /// `None`) on every assertion-stack mutation.
    pub(crate) pending_cubes: Option<std::collections::VecDeque<Vec<(Term, bool)>>>,
}

impl Z3SolverHandle {
    /// A fresh, empty solver handle (optionally carrying a tactic).
    pub(crate) fn new(tactic: Option<Tactic>) -> Self {
        Self {
            tactic,
            assertions: Vec::new(),
            scope_markers: Vec::new(),
            tracked: Vec::new(),
            tracked_scope_markers: Vec::new(),
            last_model: None,
            last_model_text: None,
            last_check_outcome: None,
            last_unsat_core: None,
            last_reason_unknown: None,
            last_proof_alethe: None,
            last_statistics: None,
            propagator: None,
            pending_cubes: None,
        }
    }

    /// Drop the artefacts of the last check. Called on every assertion-stack
    /// mutation (assert/push/pop/reset), mirroring SMT-LIB semantics where
    /// stack mutations invalidate `get-model`/`get-proof`/core queries.
    pub(crate) fn clear_check_artifacts(&mut self) {
        self.last_model = None;
        self.last_model_text = None;
        self.last_check_outcome = None;
        self.last_unsat_core = None;
        self.last_reason_unknown = None;
        self.last_proof_alethe = None;
        self.last_statistics = None;
        // The cube cursor is derived from the assertion stack; any mutation
        // invalidates it (a fresh Z3_solver_cube call re-generates).
        self.pending_cubes = None;
    }

    /// Admit one completed solver outcome and retire artifacts that are not
    /// meaningful for it. Statistics remain a valid snapshot for any backend
    /// query that actually ran.
    pub(crate) fn record_check_outcome(&mut self, outcome: SolverCheckOutcome) {
        self.last_check_outcome = Some(outcome);
        if outcome != SolverCheckOutcome::Sat {
            self.last_model = None;
            self.last_model_text = None;
        }
        if outcome != SolverCheckOutcome::Unsat {
            self.last_unsat_core = None;
            self.last_proof_alethe = None;
        }
        if outcome != SolverCheckOutcome::Unknown {
            self.last_reason_unknown = None;
        }
    }
}

/// Internal state for a `Z3_tactic` (goal-to-goal transformation) handle.
///
/// Wraps an [`ay_dpll::api::Tactic`]. The handle is arena-owned by the context
/// (see [`Z3Context::tactic_handle_cache`]) and lives until `Z3_del_context`.
/// `Z3_tactic_inc_ref`/`Z3_tactic_dec_ref` are bookkeeping-only no-ops, matching
/// `Z3_solver_inc_ref`/`Z3_solver_dec_ref` (the handle is never freed early).
///
/// Only equivalence-preserving tactics can be constructed here: `Z3_mk_tactic`
/// recognizes the shared real-z3 name set (`skip`, `simplify`, `solve-eqs`,
/// `propagate-values`, `elim-and`, `qe-light`) and returns NULL with
/// `Z3_INVALID_ARG` for any unknown name — it NEVER maps an unknown name to a
/// silent identity that would pretend to be the requested transform. The
/// `and-then`/`or-else` combinators
/// only ever compose tactics built this way, so the whole tree is
/// equivalence-preserving.
pub struct TacticHandle {
    pub(crate) tactic: Tactic,
}

/// Internal state for a `Z3_simplifier` (preprocessing goal-to-goal transformer)
/// handle.
///
/// A Z3 *simplifier* is a preprocessing transformer — like a tactic, but attached
/// to a solver so it runs incrementally before each `check-sat`. AY realizes each
/// simplifier over a verdict-preserving [`ay_dpll::api::Tactic`]. The exact Z3
/// 5.0.0 name-to-pass matrix lives in `simplifiers.rs`: names with an aligned AY
/// pass use it, and names whose rewrite is not implemented yet use the
/// equivalence-preserving identity tactic.
///
/// Only VERDICT-PRESERVING simplifiers can be constructed here: `Z3_mk_simplifier`
/// recognizes exactly Z3 5.0.0's 37-name registry and returns NULL with
/// `Z3_INVALID_ARG` for any other name. The
/// `and-then` combinator only ever composes simplifiers built this way, so the
/// whole tree stays verdict-preserving; attaching it via
/// `Z3_solver_add_simplifier` therefore never changes a solver's SAT/UNSAT answer.
/// The handle is arena-owned by the context (see
/// [`Z3Context::simplifier_handle_cache`]) and lives until `Z3_del_context`;
/// `Z3_simplifier_inc_ref`/`_dec_ref` are bookkeeping-only no-ops.
pub struct SimplifierHandle {
    pub(crate) tactic: Tactic,
}

/// A soft constraint recorded on an optimize handle.
///
/// Mirrors exactly what was handed to `Solver::assert_soft` so rendering and
/// cross-context translation cannot silently drop grouping semantics.
pub struct SoftRecord {
    pub(crate) term: Term,
    pub(crate) weight: u64,
    pub(crate) group: Option<String>,
}

/// A user push/pop backtracking marker for an optimize handle.
///
/// Records the handle-side list lengths at `Z3_optimize_push` time so
/// `Z3_optimize_pop` can restore them. The engine's `(push)`/`(pop)` already
/// scopes the hard assertions and objectives (and parsed soft constraints); this
/// marker restores the API-level mirrors the engine scope does not cover: the
/// soft record list (and the aliased `Solver` soft list) and the tracked-assert
/// list.
#[derive(Clone, Copy)]
pub struct OptimizeScopeMarker {
    /// `hard.len()` at push.
    pub(crate) hard_len: usize,
    /// `softs.len()` (== the aliased `Solver`'s soft-constraint count) at push.
    pub(crate) soft_len: usize,
    /// `tracked.len()` at push.
    pub(crate) tracked_len: usize,
    /// `public_objectives.len()` at push.
    pub(crate) public_objective_len: usize,
    /// `parsed_soft_public_terms.len()` at push.
    pub(crate) parsed_soft_public_len: usize,
}

/// Publicly admitted outcome of the last optimize decision query.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum OptimizeCheckOutcome {
    Sat,
    Unsat,
    Unknown,
}

/// Publicly admitted outcome of the last solver decision query.
///
/// This is deliberately separate from the backend's raw result. A candidate
/// SAT result may still be rejected at the consumer/model-validation boundary,
/// by the transitive-closure verifier, or by a user-propagator final check. No
/// outcome-dependent artifact is authoritative until this field admits it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum SolverCheckOutcome {
    Sat,
    Unsat,
    Unknown,
}

/// Internal state for a `Z3_optimize` (MaxSMT) handle.
///
/// The handle ALIASES the context's single `Solver` (AY has one solver per
/// context); it does not own a separate solver. It is arena-owned by the
/// context (see `optimize_handle_cache`) and lives until `Z3_del_context`.
pub struct OptimizeHandle {
    /// Back-pointer to the parent context (the solver lives there).
    pub(crate) _ctx: Z3_context,
    /// The hard assertions added to this handle, in insertion order — the CLEAN
    /// user/parsed constraint set backing `Z3_optimize_get_assertions`. Mirrors
    /// exactly what was asserted on the engine (via `Z3_optimize_assert`,
    /// `Z3_optimize_assert_and_track`, and `Z3_optimize_from_string`/`_from_file`)
    /// so the reported set never includes the engine's internal MaxSMT
    /// relaxation clauses. Scoped by `Z3_optimize_push`/`_pop`.
    pub(crate) hard: Vec<Term>,
    /// Soft constraints asserted through this handle (index-aligned with the
    /// solver-side soft list, which this handle is the sole owner of).
    pub(crate) softs: Vec<SoftRecord>,
    /// Public roots of parsed soft constraints, aligned with the frontend's
    /// parsed-soft list and used for FiniteSet reachability gates.
    pub(crate) parsed_soft_public_terms: Vec<Term>,
    /// Public objective roots, aligned with every registered objective
    /// (programmatic and parsed) in the aliased solver.
    pub(crate) public_objectives: Vec<Term>,
    /// Model realizing the optimum found by the last `Z3_optimize_check`.
    pub(crate) last_model: Option<Model>,
    /// The last publicly admitted check outcome. This is the authority for
    /// every outcome-dependent accessor: the aliased solver can retain a
    /// backend model or objective value even when the FFI subsequently rejects
    /// that result (for example at the transitive-closure gate).
    pub(crate) last_check_outcome: Option<OptimizeCheckOutcome>,
    /// Tracked hard assertions from `Z3_optimize_assert_and_track`: `(p, a)`
    /// pairs where `p` is the tracking literal and `a` the asserted formula.
    /// `a` is asserted UNCONDITIONALLY on the engine (a real hard assertion);
    /// the pair is retained for faithful assertion introspection and a future
    /// engine with participating-core extraction. The current Optimize core
    /// accessor honestly returns empty rather than invent an over-approximation.
    pub(crate) tracked: Vec<(Term, Term)>,
    /// User backtracking markers (one per outstanding `Z3_optimize_push`).
    pub(crate) scope_markers: Vec<OptimizeScopeMarker>,
    /// Unsat core (tracking literals) captured at the last UNSAT
    /// `Z3_optimize_check`; `None` if the last check was not UNSAT.
    pub(crate) last_unsat_core: Option<Vec<Term>>,
    /// Reason-unknown string captured at the last `Z3_optimize_check`.
    pub(crate) last_reason_unknown: Option<String>,
    /// Executor statistics snapshot captured at the last `Z3_optimize_check`.
    pub(crate) last_statistics: Option<Statistics>,
    /// Permanent fail-closed latch after an Optimize parse transaction could
    /// not be proven fully rolled back. A poisoned handle never checks again.
    pub(crate) terminal_error: Option<String>,
}

impl OptimizeHandle {
    /// Drop every externally observable artefact of the preceding check.
    ///
    /// Called before a new decision query and after every successful formula,
    /// objective, or scope mutation. The solver has its own invalidation, but
    /// optimize models and diagnostics are copied into this handle and must be
    /// retired independently.
    pub(crate) fn clear_check_artifacts(&mut self) {
        self.last_model = None;
        self.last_check_outcome = None;
        self.last_unsat_core = None;
        self.last_reason_unknown = None;
        self.last_statistics = None;
    }

    /// Admit one completed decision-query outcome and retire artefacts that are
    /// not meaningful for it. Statistics, when captured, remain valid for all
    /// completed backend queries.
    pub(crate) fn record_check_outcome(&mut self, outcome: OptimizeCheckOutcome) {
        self.last_check_outcome = Some(outcome);
        if outcome != OptimizeCheckOutcome::Sat {
            self.last_model = None;
        }
        if outcome != OptimizeCheckOutcome::Unsat {
            self.last_unsat_core = None;
        }
        if outcome != OptimizeCheckOutcome::Unknown {
            self.last_reason_unknown = None;
        }
    }
}

pub struct ModelHandle {
    pub(crate) model: Model,
    /// FUNCTION interpretations (arity > 0) from the same check, parsed out of
    /// the engine's raw model text (the constants-only [`Model`] drops them).
    /// Part of the snapshot: `Z3_model_eval` resolves ground uninterpreted
    /// function applications against these tables — never against live solver
    /// state. Empty when the model text carried no function tables (or none
    /// could be faithfully parsed; unparseable tables are skipped, leaving the
    /// application symbolic — honest partial evaluation, never fabrication).
    pub(crate) func_interps: Vec<FuncInterp>,
    /// User-provided CONSTANT interpretations set via `Z3_add_const_interp` on a
    /// model built by `Z3_mk_model`. Each entry maps a (nullary) `FuncDecl` to
    /// the value AST the caller assigned. `Z3_model_get_const_interp` consults
    /// this map FIRST (by decl name), so a hand-built model reads back exactly
    /// what was stored. Empty for solver/optimize-produced models.
    pub(crate) user_const_interps: Vec<(FuncDecl, Z3_ast)>,
    /// User-provided FUNCTION interpretations set via `Z3_add_func_interp` on a
    /// model built by `Z3_mk_model`. Each entry maps a `FuncDecl` to the
    /// arena-owned `Z3_func_interp` handle created for it (populated further via
    /// `Z3_func_interp_add_entry` / `Z3_func_interp_set_else`).
    /// `Z3_model_get_func_interp` consults this map FIRST (by decl name+arity).
    pub(crate) user_func_interps: Vec<(FuncDecl, Z3_func_interp)>,
    /// Size of `ctx.rec_fun_defs` when this model was created. The registry is
    /// ADD-ONLY (redefinition is rejected at `Z3_add_rec_def`), so a mismatch
    /// with the live registry means definitions arrived AFTER this model;
    /// `eval_term_under_model` then refuses to evaluate any term mentioning a
    /// rec-defined name — evaluating through the LIVE registry could
    /// contradict the model's own certifying constraints (a model that pinned
    /// `f` as a plain UF before `f` was defined must never re-answer through
    /// the definition).
    pub(crate) rec_def_count: usize,
    /// Context for evaluating model values (kept for future model_eval)
    pub(crate) _ctx: Z3_context,
}

/// A model function interpretation exposed to the C API (`Z3_func_interp`).
///
/// A finite map (`entries`) plus an `else` value, materialized ONCE — in the
/// querying context's term arena — from a snapshot [`FuncInterp`] table (itself
/// parsed from the engine's real `get-model` text). The AST handles are real
/// value terms of the model; nothing is fabricated (an unrepresentable row or
/// else value yields a skipped row / `0` else, never a guessed value).
///
/// Arena-owned by the context (see [`Z3Context::func_interp_cache`]) and freed
/// at `Z3_del_context`, so `Z3_func_interp_inc_ref`/`_dec_ref` are
/// bookkeeping-only no-ops — matching AY's non-RC handle convention for
/// goals/tactics/models/params.
pub struct FuncInterpHandle {
    /// Number of arguments (domain size) of the interpreted function.
    pub(crate) arity: c_uint,
    /// Non-owning references to the finite-map points; the boxes are owned by
    /// [`Z3Context::func_entry_cache`].
    pub(crate) entries: Vec<*mut FuncEntryHandle>,
    /// The `else` (default) value AST; `0` when it could not be faithfully
    /// represented as a term (honest not-found, never a fabricated value).
    pub(crate) else_ast: Z3_ast,
}

/// One point of a [`FuncInterpHandle`]'s finite map (`Z3_func_entry`): an
/// argument tuple and the value the function takes there. Arena-owned by the
/// context (see [`Z3Context::func_entry_cache`]).
pub struct FuncEntryHandle {
    /// Argument value ASTs (length == the interpretation's arity).
    pub(crate) args: Vec<Z3_ast>,
    /// The function's value at `args`.
    pub(crate) value: Z3_ast,
}

/// A relation (predicate) registered with a [`FixedpointHandle`].
///
/// Mirrors the Bool-range `Z3_func_decl` handed to
/// `Z3_fixedpoint_register_relation`: its name and argument (domain) sorts,
/// already lowered to `ay-chc`'s [`ay_chc::ChcSort`].
pub struct RegisteredRelation {
    pub(crate) name: String,
    pub(crate) arg_sorts: Vec<ay_chc::ChcSort>,
}

/// A caller-supplied, TRUSTED predicate lemma registered via
/// `Z3_fixedpoint_add_invariant` / `Z3_fixedpoint_add_cover(level = -1, ...)`
/// / `Z3_fixedpoint_add_constraint(lvl = ∞, P(vars) => φ)`.
///
/// SEMANTICS (matching Z3's Spacer trust-the-hint contract, documented in
/// `fixedpoint_ext.rs`): the property is ASSUMED to hold of every reachable
/// `pred`-state; at problem-construction time it is instantiated and conjoined
/// onto every BODY occurrence of `pred` (exactly how a Spacer lemma prunes the
/// search). Z3 does not validate these hints and neither does AY — a WRONG
/// hint can flip a verdict in both solvers identically; that is the API's
/// contract, not a fabrication.
pub struct FixedpointLemmaHint {
    /// The predicate the lemma is about.
    pub(crate) pred: String,
    /// The property over the predicate's argument positions, translated to
    /// `ay-chc`'s expression form at registration time.
    pub(crate) expr: ay_chc::ChcExpr,
    /// `(argument position, the exact `ChcVar` the property uses for it)` —
    /// substitution keys for instantiating [`Self::expr`] at a body atom.
    pub(crate) vars: Vec<(usize, ay_chc::ChcVar)>,
}

/// Internal state for a `Z3_fixedpoint` (CHC/Datalog) handle.
///
/// The handle is arena-owned by the context (see `fixedpoint_handle_cache`) and
/// lives until `Z3_del_context`. It records the registered relations and the
/// added rule ASTs; on `Z3_fixedpoint_query` these are translated into an
/// [`ay_chc::ChcProblem`] and solved by AY's CHC portfolio. See the
/// `fixedpoint` module docs for the (fixedpoint-inverted) query polarity.
pub struct FixedpointHandle {
    /// Back-pointer to the parent context (the solver/term store lives there).
    pub(crate) _ctx: Z3_context,
    /// Relations registered via `Z3_fixedpoint_register_relation`.
    pub(crate) relations: Vec<RegisteredRelation>,
    /// Rule ASTs added via `Z3_fixedpoint_add_rule` (interned `Term` handles).
    pub(crate) rules: Vec<Term>,
    /// Rule NAMES parallel to `rules` (`None` for unnamed rules/facts). Plumbed
    /// by `Z3_fixedpoint_add_rule` and `Z3_fixedpoint_update_rule`; every push to
    /// `rules` MUST push here too so the two stay index-aligned.
    pub(crate) rule_names: Vec<Option<String>>,
    /// Background axioms added via `Z3_fixedpoint_assert`. Folded into every
    /// clause body as a global constraint during problem construction, and
    /// returned verbatim by `Z3_fixedpoint_get_assertions`.
    pub(crate) assertions: Vec<Term>,
    /// The `Z3_lbool` returned by the most recent `Z3_fixedpoint_query`.
    pub(crate) last_status: c_int,
    /// Honest reason recorded whenever the most recent query returned
    /// `Z3_L_UNDEF` (untranslatable, portfolio-inconclusive, or Safe-but-demoted).
    /// Read back by `Z3_fixedpoint_get_reason_unknown`.
    pub(crate) last_reason_unknown: Option<String>,
    /// The counterexample retained from the most recent `Unsafe` (`Z3_L_TRUE`)
    /// query. Backs the Spacer trace family (`get_ground_sat_answer`,
    /// `get_rules_along_trace`, `get_rule_names_along_trace`). `None` unless the
    /// last query was `Unsafe`.
    pub(crate) last_cex: Option<ay_chc::Counterexample>,
    /// Snapshot of `rules` taken at the query that produced `last_cex`, so the
    /// counterexample's clause indices map back to rule ASTs even if rules are
    /// mutated afterwards.
    pub(crate) last_query_rules: Vec<Term>,
    /// Snapshot of `rule_names` taken alongside `last_query_rules`.
    pub(crate) last_query_rule_names: Vec<Option<String>>,
    /// REAL `ay-chc` solve counters accumulated by the most recent query's
    /// `AdaptivePortfolio` run (`AdaptivePortfolio::statistics`). Backs
    /// `Z3_fixedpoint_get_statistics` and `Z3_fixedpoint_get_num_levels`
    /// (`max_frame` = the deepest PDR frame reached). `None` before any query.
    pub(crate) last_statistics: Option<ay_chc::ChcStatistics>,
    /// The VALIDATED whole-system inductive invariant retained from the most
    /// recent `Safe` (`Z3_L_FALSE`) query — the exact model the strict-proof
    /// discharge gate verified — together with the `(name, PredicateId)`
    /// resolution table of that query. Backs `Z3_fixedpoint_get_cover_delta`
    /// (`level == -1`). `None` unless the last query was validated-Safe.
    pub(crate) last_invariant: Option<(Vec<(String, ay_chc::PredicateId)>, ay_chc::InvariantModel)>,
    /// Trusted predicate lemmas (see [`FixedpointLemmaHint`]), conjoined onto
    /// every body occurrence of their predicate at problem-construction time.
    pub(crate) lemma_hints: Vec<FixedpointLemmaHint>,
}

/// Value identity of a Z3 symbol.
///
/// Integer symbols and string symbols are distinct even when their printed
/// spellings coincide (for example integer symbol `7` and string symbol
/// `"s!7"`).  Keeping the discriminator here prevents C-API declarations
/// from being accidentally interned by display text alone.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) enum SymbolKey {
    Integer(c_int),
    String(String),
}

impl SymbolKey {
    pub(crate) fn display_name(&self) -> String {
        match self {
            Self::Integer(value) => format!("s!{value}"),
            Self::String(name) => name.clone(),
        }
    }

    /// Collision-proof name used only inside AY's string-named solver IR.
    ///
    /// Most string symbols retain their original name.  Integer symbols live
    /// in a private namespace; string symbols that themselves begin with that
    /// namespace are injectively escaped, so no C string symbol can alias an
    /// integer symbol's internal declaration.
    pub(crate) fn semantic_name(&self) -> String {
        const SYMBOL_NAMESPACE: &str = "!ay.z3-symbol.";
        match self {
            Self::Integer(value) => format!("{SYMBOL_NAMESPACE}int!{value}"),
            Self::String(name) if name.starts_with(SYMBOL_NAMESPACE) => {
                let mut encoded = String::with_capacity(name.len() * 2);
                for byte in name.as_bytes() {
                    use std::fmt::Write as _;
                    let _ = write!(encoded, "{byte:02x}");
                }
                format!("{SYMBOL_NAMESPACE}string!{encoded}")
            }
            Self::String(name) => name.clone(),
        }
    }
}

pub struct SymbolHandle {
    pub(crate) key: SymbolKey,
}

impl SymbolHandle {
    pub(crate) fn display_name(&self) -> String {
        self.key.display_name()
    }

    pub(crate) fn semantic_name(&self) -> String {
        self.key.semantic_name()
    }
}

pub struct ParamsHandle {
    /// Stored until solver params are applied; only supported keys take effect.
    pub(crate) params: Vec<(String, String)>,
}

/// One parameter descriptor: name, its `Z3_param_kind`, and a documentation
/// string. Backs a [`ParamDescrsHandle`] entry.
pub struct ParamDescr {
    pub(crate) name: String,
    /// A `Z3_param_kind` value (`Z3_PK_UINT`, `Z3_PK_BOOL`, ...).
    pub(crate) kind: c_uint,
    pub(crate) doc: String,
}

/// A parameter-descriptor set (`Z3_param_descrs`).
///
/// Produced by `Z3_optimize_get_param_descrs`; a REAL, queryable list of the
/// parameters the optimize engine recognizes (name + `Z3_param_kind` + doc).
/// Arena-owned by the context (see [`Z3Context::param_descrs_cache`]) and freed
/// at `Z3_del_context`, so `Z3_param_descrs_inc_ref`/`_dec_ref` are
/// bookkeeping-only no-ops.
pub struct ParamDescrsHandle {
    pub(crate) entries: Vec<ParamDescr>,
}

// Z3_param_kind values (mirrors z3_api.h's Z3_param_kind enum).
pub const Z3_PK_UINT: c_uint = 0;
pub const Z3_PK_BOOL: c_uint = 1;
pub const Z3_PK_DOUBLE: c_uint = 2;
#[allow(dead_code)]
pub const Z3_PK_SYMBOL: c_uint = 3;
pub const Z3_PK_STRING: c_uint = 4;
#[allow(dead_code)]
pub const Z3_PK_OTHER: c_uint = 5;
pub const Z3_PK_INVALID: c_uint = 6;

// Z3_parameter_kind values (mirrors Z3 5.0.0's `Z3_parameter_kind` enum).
// These classify a function declaration's parameters
// (`Z3_get_decl_parameter_kind`). Indexed operators such as
// `(_ extract h l)` use INTEGER parameters; finite-set `set.empty` carries one
// SORT parameter. The remaining kinds are declared for source compatibility
// and completeness of the enum.
pub const Z3_PARAMETER_INT: c_uint = 0;
#[allow(dead_code)]
pub const Z3_PARAMETER_DOUBLE: c_uint = 1;
#[allow(dead_code)]
pub const Z3_PARAMETER_RATIONAL: c_uint = 2;
#[allow(dead_code)]
pub const Z3_PARAMETER_SYMBOL: c_uint = 3;
#[allow(dead_code)]
pub const Z3_PARAMETER_SORT: c_uint = 4;
#[allow(dead_code)]
pub const Z3_PARAMETER_AST: c_uint = 5;
#[allow(dead_code)]
pub const Z3_PARAMETER_FUNC_DECL: c_uint = 6;

pub struct AstVectorHandle {
    pub(crate) asts: Vec<Z3_ast>,
}

/// A Z3 *AST map*: a mapping from `Z3_ast` key to `Z3_ast` value.
///
/// Backs the C-API `Z3_ast_map_*` surface. Keys and values are ordinary
/// `Z3_ast` term handles interned in the context's shared term store; the map
/// owns no terms, only their handles. Lookup/containment go through a real
/// `HashMap<Z3_ast, Z3_ast>`; a parallel `order` vector records key *insertion
/// order* so `Z3_ast_map_keys` / `Z3_ast_map_to_string` render deterministically
/// (Z3's own map iteration order is hash-table-dependent and unspecified). The
/// two are kept in lockstep by the `insert`/`erase`/`reset` methods below.
///
/// The handle is arena-owned by the context (see [`Z3Context::ast_map_cache`])
/// and lives until `Z3_del_context`, so `Z3_ast_map_inc_ref`/`_dec_ref` are
/// bookkeeping-only no-ops (matching AY's arena/no-op RC convention).
#[derive(Default)]
pub struct AstMapHandle {
    /// Real key→value store for O(1) `contains`/`find`/`insert`/`erase`.
    pub(crate) map: HashMap<Z3_ast, Z3_ast>,
    /// Keys in first-insertion order (a key re-inserted with a new value keeps
    /// its position). Every entry here is present in `map` and vice-versa.
    pub(crate) order: Vec<Z3_ast>,
}

impl AstMapHandle {
    /// Store or replace `k -> v`. A new key is appended to the insertion order;
    /// an existing key keeps its position and only updates its value.
    pub(crate) fn insert(&mut self, k: Z3_ast, v: Z3_ast) {
        if self.map.insert(k, v).is_none() {
            self.order.push(k);
        }
    }

    /// Remove `k` from both the store and the order vector (no-op if absent).
    pub(crate) fn erase(&mut self, k: Z3_ast) {
        if self.map.remove(&k).is_some() {
            self.order.retain(|&key| key != k);
        }
    }

    /// Drop every entry.
    pub(crate) fn reset(&mut self) {
        self.map.clear();
        self.order.clear();
    }
}

/// A Z3 *goal*: an (implicit-conjunction) list of assertion formulas.
///
/// Backs the C-API `Z3_mk_goal`/`Z3_goal_assert` surface and is what
/// `Z3_tactic_apply` transforms. The formulas are ordinary `Z3_ast` term handles
/// interned in the context's shared term store; a goal owns no terms, only their
/// handles. The handle is arena-owned by the context (see
/// [`Z3Context::goal_cache`]) and lives until `Z3_del_context`, so
/// `Z3_goal_inc_ref`/`Z3_goal_dec_ref` are bookkeeping-only no-ops.
pub struct GoalHandle {
    pub(crate) formulas: Vec<Z3_ast>,
    /// The Z3 goal *depth* — the number of primitive tactic applications that
    /// produced this goal. A goal built by `Z3_mk_goal` has depth `0`; a subgoal
    /// produced by `Z3_tactic_apply` carries the engine's real transformation
    /// depth. Read by `Z3_goal_depth` and the `depth` probe.
    pub(crate) depth: usize,
}

/// The result of applying a tactic to a goal: the produced subgoals.
///
/// Each subgoal is a [`GoalHandle`] that is ALSO registered in the context's
/// `goal_cache` (so it is freed exactly once, there), which is why this handle
/// stores raw `Z3_goal` references it does not own. Arena-owned by the context
/// (see [`Z3Context::apply_result_cache`]); `Z3_apply_result_inc_ref`/`_dec_ref`
/// are no-ops.
pub struct ApplyResultHandle {
    pub(crate) subgoals: Vec<Z3_goal>,
}

/// A Z3 *probe*: a numeric (or boolean, `1.0`/`0.0`) query over a goal.
///
/// Wraps an [`ay_frontend::Probe`] — the SAME probe representation the SMT-LIB
/// `(apply (when <probe> …))` / `(fail-if <probe>)` surface evaluates — so
/// `Z3_probe_apply` runs the identical, real engine computation over the goal's
/// formulas (never a fabricated value). Named probes (`num-consts`, `is-qflia`,
/// …) come from `Z3_mk_probe`; `Z3_probe_const`/`_lt`/`_and`/`_not`/… build the
/// comparison/boolean combinators. Arena-owned by the context (see
/// [`Z3Context::probe_cache`]); `Z3_probe_inc_ref`/`_dec_ref` are no-ops.
pub struct ProbeHandle {
    pub(crate) probe: ay_frontend::Probe,
}

/// A datatype constructor descriptor created by `Z3_mk_constructor` (#phase3-dt).
///
/// Unlike most AY FFI handles, constructor handles follow Z3's *explicit*
/// ownership contract: the caller frees them with `Z3_del_constructor` and they
/// are NOT registered in a context arena (so there is no double-free between an
/// explicit `Z3_del_constructor` and `Z3_del_context`).
///
/// Field sorts are stored as `Option<Sort>`: `None` marks a self/sibling sort
/// reference (the `sort_refs[i]` entry) whose concrete sort is only known once
/// `Z3_mk_datatype` creates the datatype sort. AY currently supports
/// self-references (recursive datatypes referencing the datatype under
/// construction); cross-datatype references via `Z3_mk_datatypes` are rejected.
pub struct ConstructorHandle {
    /// Collision-proof name used by AY's string-keyed datatype registry.
    pub(crate) name: String,
    /// Exact caller-visible constructor symbol, including integer-vs-string
    /// kind, retained for `Z3_get_decl_name`.
    pub(crate) name_symbol: SymbolKey,
    /// Exact caller-visible recognizer symbol.
    pub(crate) recognizer_symbol: SymbolKey,
    pub(crate) field_names: Vec<String>,
    /// Exact caller-visible accessor symbols, index-aligned with
    /// `field_names`.
    pub(crate) field_symbols: Vec<SymbolKey>,
    /// Concrete field sort, or `None` for a sort-reference field.
    pub(crate) field_sorts: Vec<Option<Sort>>,
    /// Z3 sort-reference index per field (only meaningful where `field_sorts` is
    /// `None`). `0` denotes the single datatype under construction (self-ref).
    pub(crate) sort_refs: Vec<c_uint>,
    /// Constructor func_decl, filled in by `Z3_mk_datatype`.
    pub(crate) constructor_decl: Z3_func_decl,
    /// Recognizer (`is-Ctor`) func_decl, filled in by `Z3_mk_datatype`.
    pub(crate) tester_decl: Z3_func_decl,
    /// Accessor (selector) func_decls, index-aligned with `field_names`.
    pub(crate) accessor_decls: Vec<Z3_func_decl>,
}

/// A list of datatype constructors created by `Z3_mk_constructor_list`.
///
/// Borrows (does not own) the constructor handles it lists; freeing the list
/// with `Z3_del_constructor_list` does NOT free the constructors (matching Z3,
/// where each constructor must still be freed with `Z3_del_constructor`).
pub struct ConstructorListHandle {
    pub(crate) constructors: Vec<Z3_constructor>,
}

/// Internal state for a `Z3_parser_context` (incremental SMT-LIB parser).
///
/// AY has a single `Solver` per context, and that solver's SMT-LIB front-end
/// (`Solver::parse_smtlib2`) already keeps a PERSISTENT symbol table across
/// calls: declarations from one parse are visible to the next. The parser
/// context is a token over that shared table plus a record of the sorts/decls
/// injected through `Z3_parser_context_add_sort`/`_add_decl` (registered in the
/// context solver's symbol table at add time so subsequent
/// `Z3_parser_context_from_string` calls resolve them by name). Every term the
/// context yields is interned in — and therefore valid against — the parent
/// `Z3_context`, exactly like [`Z3_parse_smtlib2_string`].
///
/// Arena-owned by the context (see [`Z3Context::parser_context_cache`]) and
/// freed at `Z3_del_context`, so `Z3_parser_context_inc_ref`/`_dec_ref` are
/// bookkeeping-only (they maintain [`refcount`](ParserContextHandle::refcount)
/// but never free the handle early), matching AY's non-RC handle convention.
pub struct ParserContextHandle {
    /// Sorts injected via `Z3_parser_context_add_sort`, retained for membership
    /// and introspection. Each was declared in the solver exactly once at add
    /// time.
    pub(crate) added_sorts: Vec<Sort>,
    /// Function declarations injected via `Z3_parser_context_add_decl` (same
    /// role as `added_sorts`).
    pub(crate) added_decls: Vec<FuncDecl>,
    /// `inc_ref`/`dec_ref` bookkeeping count. The handle is arena-owned and is
    /// NEVER freed by reference counting; this only records outstanding
    /// references for discipline tracking.
    pub(crate) refcount: u64,
}

// ============================================================================
// Helpers
// ============================================================================

/// Convert AY Term to Z3_ast (u64).
/// Adds 1 so that TermId 0 has payload 1, reserving 0 as null, and embeds the
/// owning context's salt. `Z3_ast` is opaque at the C ABI, so the salt changes
/// no public layout while making same-number cross-context aliases
/// distinguishable.
#[inline]
pub(crate) fn term_to_ast(ctx: &Z3Context, term: Term) -> Z3_ast {
    (u64::from(ctx.handle_salt) << TERM_AST_SALT_SHIFT) | (u64::from(term.to_raw()) + 1)
}

/// True exactly when an untagged, non-null term AST carries `ctx`'s salt and a
/// representable nonzero 1-based payload.
#[inline]
pub(crate) fn term_ast_belongs_to(ctx: &Z3Context, ast: Z3_ast) -> bool {
    ast != 0
        && ast & HANDLE_TAG_MASK == 0
        && ((ast >> TERM_AST_SALT_SHIFT) & HANDLE_SALT_MASK) as u32 == ctx.handle_salt
        && ast & TERM_AST_PAYLOAD_MASK != 0
}

/// Decode a term AST only when it is structurally valid, salted for `ctx`, and
/// names a live entry in that context's term store.
///
/// This is the sole term-handle decoder. Keeping the payload conversion behind
/// the context check makes it impossible for a consumer to accidentally accept
/// a same-number handle minted by another context.
#[inline]
pub(crate) fn checked_ast_to_term(ctx: &Z3Context, ast: Z3_ast) -> Option<Term> {
    if !term_ast_belongs_to(ctx, ast) {
        return None;
    }
    let payload = ast & TERM_AST_PAYLOAD_MASK;
    if payload > u64::from(u32::MAX) + 1 {
        return None;
    }
    let term = Term::from_raw((payload - 1) as u32);
    ctx.solver.is_valid_term(term).then_some(term)
}

/// Return whether an opaque AST handle names a live object owned by `ctx`.
///
/// AST containers may hold ordinary terms as well as the tagged proof,
/// algebraic, sort, and function-declaration ASTs exposed by the Z3 API.  A
/// term-only check would incorrectly reject those values; skipping the check
/// would instead permit a foreign context's indexed handle to alias a local
/// object.  Dispatch through each kind's authenticated decoder so both cases
/// fail or succeed for the right reason.
#[inline]
pub(crate) fn ast_handle_belongs_to(ctx: &Z3Context, ast: Z3_ast) -> bool {
    match ast & HANDLE_TAG_MASK {
        0 => checked_ast_to_term(ctx, ast).is_some(),
        PROOF_AST_TAG => proof_text_for_ast(ctx, ast).is_some(),
        ALGEBRAIC_AST_TAG => ast_as_scalar(ctx, ast).is_some(),
        SORT_AST_TAG => !sort_ast_to_handle(ctx, ast).is_null(),
        FUNC_DECL_AST_TAG => !func_decl_ast_to_handle(ctx, ast).is_null(),
        _ => false,
    }
}

/// Authenticate any AST kind and record a stable container diagnostic.
#[inline]
pub(crate) fn require_ast_handle(
    ctx: &mut Z3Context,
    ast: Z3_ast,
    operation: &str,
    role: &str,
) -> bool {
    let valid = ast_handle_belongs_to(ctx, ast);
    if !valid {
        ctx.last_error = Z3_INVALID_ARG;
        ctx.error_msg = Some(format!(
            "{operation}: {role} is null, malformed, stale, or belongs to a different context"
        ));
    }
    valid
}

/// Authenticate a term AST and record a stable FFI diagnostic on failure.
#[inline]
pub(crate) fn require_term_ast(
    ctx: &mut Z3Context,
    ast: Z3_ast,
    operation: &str,
    role: &str,
) -> Option<Term> {
    let term = checked_ast_to_term(ctx, ast);
    if term.is_none() {
        ctx.last_error = Z3_INVALID_ARG;
        ctx.error_msg = Some(format!(
            "{operation}: {role} is null, malformed, stale, or belongs to a different context"
        ));
    }
    term
}

/// Authenticate a caller-owned sequence of term ASTs under one context.
pub(crate) fn require_term_asts(
    ctx: &mut Z3Context,
    asts: &[Z3_ast],
    operation: &str,
) -> Option<Vec<Term>> {
    asts.iter()
        .enumerate()
        .map(|(index, &ast)| require_term_ast(ctx, ast, operation, &format!("argument {index}")))
        .collect()
}

/// Decode one AST or return the caller-selected FFI sentinel immediately.
/// Keeping the fallback at the call site makes each API's failure contract
/// explicit while sharing the ownership/liveness check.
macro_rules! require_term_ast_or_return {
    ($ctx:expr, $ast:expr, $operation:expr, $role:expr $(,)?) => {{
        let Some(term) = $crate::z3_compat::require_term_ast($ctx, $ast, $operation, $role) else {
            return;
        };
        term
    }};
    ($ctx:expr, $ast:expr, $operation:expr, $role:expr, $fallback:expr) => {{
        let Some(term) = $crate::z3_compat::require_term_ast($ctx, $ast, $operation, $role) else {
            return $fallback;
        };
        term
    }};
}
pub(crate) use require_term_ast_or_return;

/// Decode an AST slice or return the caller-selected FFI sentinel before any
/// consumer-side mutation occurs.
macro_rules! require_term_asts_or_return {
    ($ctx:expr, $asts:expr, $operation:expr $(,)?) => {{
        let Some(terms) = $crate::z3_compat::require_term_asts($ctx, $asts, $operation) else {
            return;
        };
        terms
    }};
    ($ctx:expr, $asts:expr, $operation:expr, $fallback:expr) => {{
        let Some(terms) = $crate::z3_compat::require_term_asts($ctx, $asts, $operation) else {
            return $fallback;
        };
        terms
    }};
}
pub(crate) use require_term_asts_or_return;

/// Apply the subset of configuration/solver params that AY actually honors.
///
/// Supported keys:
/// - `timeout` — solver timeout in milliseconds.
/// - `proof` / `produce_proofs` / `produce-proofs` — enable proof production
///   (matches Z3's global `proof` config param). Truthy values (`true`/`1`)
///   turn it on; everything else turns it off. See `proofs.rs` (#phase3-proof).
pub(crate) fn apply_supported_params(solver: &mut Solver, params: &[(String, String)]) {
    for (key, value) in params {
        match key.as_str() {
            "timeout" => {
                if let Ok(ms) = value.parse::<u64>() {
                    // Z3 defines zero as "no limit". Mapping it to a zero
                    // duration would instead make every solve time out
                    // immediately.
                    solver.set_timeout((ms != 0).then(|| Duration::from_millis(ms)));
                }
            }
            "proof" | "produce_proofs" | "produce-proofs" => {
                solver.set_produce_proofs(matches!(value.as_str(), "true" | "1"));
            }
            _ => {}
        }
    }
}

// `ctx_ref` was removed in #8568 (unsound caller-chosen lifetime).
//
// The old signature `unsafe fn ctx_ref<'a>(c: Z3_context) -> Option<&'a mut Z3Context>`
// let callers choose any lifetime (including `'static`) for the returned
// mutable reference. This violated Rust's aliasing rules because:
// 1. Raw pointers carry no lifetime, so there is no input lifetime to constrain the output.
// 2. Two sequential calls could create overlapping `&mut` references.
//
// All call sites now use `c.as_mut()` directly within a minimal scope, which
// is the same pattern the `ffi_guard_*` functions use. The compiler ties the
// returned reference's lifetime to the enclosing block, preventing escape.

/// Store a string in context cache and return a pointer valid for context lifetime.
/// Z3 convention: returned strings are owned by the context.
pub(crate) fn cache_string(ctx: &mut Z3Context, s: String) -> *const c_char {
    match CString::new(s) {
        Ok(cs) => {
            let ptr = cs.as_ptr();
            ctx.string_cache.push(cs);
            ptr
        }
        Err(_) => ptr::null(),
    }
}

/// Store a symbol handle in context cache and return a pointer valid for context lifetime.
/// Prevents symbol handle leaks (#5528).
pub(crate) fn cache_symbol(ctx: &mut Z3Context, name: String) -> Z3_symbol {
    cache_symbol_key(ctx, SymbolKey::String(name))
}

/// Store an integer-symbol handle without conflating it with a same-spelled
/// string symbol.
pub(crate) fn cache_int_symbol(ctx: &mut Z3Context, value: c_int) -> Z3_symbol {
    cache_symbol_key(ctx, SymbolKey::Integer(value))
}

/// Store a symbol handle with its exact Z3 kind/value identity.
pub(crate) fn cache_symbol_key(ctx: &mut Z3Context, key: SymbolKey) -> Z3_symbol {
    let handle = Box::into_raw(Box::new(SymbolHandle { key }));
    ctx.symbol_cache.push(handle);
    handle
}

/// Return the canonical private solver name for a Z3 function declaration.
/// Repeating the exact symbol/signature reuses the same declaration identity;
/// overloads and integer-vs-string symbols are always disjoint.
pub(crate) fn ffi_function_semantic_name(
    ctx: &mut Z3Context,
    symbol: &SymbolKey,
    domain: &[Sort],
    range: &Sort,
) -> String {
    let key = (symbol.clone(), domain.to_vec(), range.clone());
    if let Some(name) = ctx.ffi_func_names.get(&key) {
        return name.clone();
    }
    let id = ctx.next_ffi_fresh_id;
    ctx.next_ffi_fresh_id += 1;
    let name = format!("!ay.z3-func!{id}");
    ctx.ffi_func_names.insert(key, name.clone());
    name
}

/// Return the native declaration for an exact C-API function identity,
/// declaring it on first use.
///
/// Z3 hash-conses declarations by symbol and signature. AY deliberately gives
/// each C call a distinct pointer handle, but every such handle must refer to
/// the same underlying declaration. Keeping that idempotence here also lets
/// the frontend reject textual/native redeclarations without breaking the C
/// compatibility boundary.
pub(crate) fn ffi_try_declare_function(
    ctx: &mut Z3Context,
    symbol: &SymbolKey,
    domain: &[Sort],
    range: &Sort,
) -> Result<FuncDecl, ay_dpll::api::SolverError> {
    if domain
        .iter()
        .any(|sort| has_unsupported_finite_set_datatype_embedding(ctx, sort))
        || has_unsupported_finite_set_datatype_embedding(ctx, range)
    {
        return Err(ay_dpll::api::SolverError::InvalidArgument {
            operation: "declare_fun",
            message: "a datatype containing FiniteSet fields cannot be lowered without changing \
                      the datatype identity"
                .to_string(),
        });
    }
    let key = (symbol.clone(), domain.to_vec(), range.clone());
    if let Some(decl) = ctx.ffi_func_decls.get(&key) {
        return Ok(decl.clone());
    }

    let semantic_name = ffi_function_semantic_name(ctx, symbol, domain, range);
    let engine_domain: Vec<Sort> = domain
        .iter()
        .map(|sort| finite_set_engine_public_sort(ctx, sort))
        .collect();
    let engine_range = finite_set_engine_public_sort(ctx, range);
    match ctx
        .solver
        .try_declare_fun(&semantic_name, &engine_domain, engine_range)
    {
        Ok(decl) => {
            ctx.finite_set_decl_signatures
                .insert(semantic_name, (domain.to_vec(), range.clone()));
            ctx.ffi_func_decls.insert(key, decl.clone());
            Ok(decl)
        }
        Err(error) => {
            // Do not retain a private identity for a declaration that never
            // became live; a later retry must take the normal first-use path.
            ctx.ffi_func_names.remove(&key);
            Err(error)
        }
    }
}

/// Translate private declaration/sort identities in formatted solver text back
/// to the caller-visible Z3 symbols.
///
/// Internal names stay authoritative in the solver. Ordinary C-facing
/// diagnostic text APIs apply this final token-level projection so
/// overload-safe identities do not leak through `Z3_ast_to_string`,
/// solver/goal dumps, model sorts, or fixedpoint output. Proof certificates are
/// deliberately excluded: rewriting an overloaded declaration there could
/// invalidate the certificate. String literals are copied verbatim;
/// replacements happen only on complete SMT-LIB symbol tokens.
pub(crate) fn apply_surface_replacements(
    rendered: &str,
    replacements: &HashMap<String, String>,
) -> String {
    if replacements.is_empty() {
        return rendered.to_string();
    }
    let bytes = rendered.as_bytes();
    let mut out = String::with_capacity(rendered.len());
    let mut i = 0;
    let is_delimiter = |byte: u8| byte.is_ascii_whitespace() || matches!(byte, b'(' | b')' | b',');
    while i < bytes.len() {
        if bytes[i] == b'"' {
            // SMT-LIB escapes an embedded quote by doubling it.
            let start = i;
            i += 1;
            while i < bytes.len() {
                if bytes[i] == b'"' {
                    if i + 1 < bytes.len() && bytes[i + 1] == b'"' {
                        i += 2;
                        continue;
                    }
                    i += 1;
                    break;
                }
                i += 1;
            }
            out.push_str(&rendered[start..i]);
            continue;
        }

        let start = i;
        if bytes[i] == b'|' {
            i += 1;
            while i < bytes.len() && bytes[i] != b'|' {
                i += 1;
            }
            i = (i + 1).min(bytes.len());
        } else if is_delimiter(bytes[i]) {
            i += 1;
        } else {
            while i < bytes.len() && !is_delimiter(bytes[i]) {
                i += 1;
            }
        }
        let token = &rendered[start..i];
        out.push_str(replacements.get(token).map_or(token, String::as_str));
    }
    out
}

/// Project ordinary private C-API declaration/sort identities, excluding the
/// retained FiniteSet application layer.
pub(crate) fn ffi_surface_text_base(ctx: &Z3Context, rendered: &str) -> String {
    let mut replacements: HashMap<String, String> = HashMap::new();
    for (internal, symbol) in &ctx.ffi_decl_symbols {
        replacements.insert(
            ay_core::quote_symbol(internal),
            ay_core::quote_symbol(&symbol.display_name()),
        );
    }
    for (sort, symbol) in &ctx.ffi_sort_symbols {
        let internal = match sort {
            Sort::Uninterpreted(name) | Sort::FiniteDomain(name, _) | Sort::TypeVar(name) => {
                Some(name)
            }
            Sort::Datatype(dt) => Some(&dt.name),
            _ => None,
        };
        if let Some(internal) = internal {
            replacements.insert(
                ay_core::quote_symbol(internal),
                ay_core::quote_symbol(&symbol.display_name()),
            );
        }
    }
    for (internal, symbol) in ctx.ffi_const_metadata.values() {
        replacements.insert(
            ay_core::quote_symbol(internal),
            ay_core::quote_symbol(&symbol.display_name()),
        );
    }
    apply_surface_replacements(rendered, &replacements)
}

pub(crate) fn ffi_surface_text(ctx: &Z3Context, rendered: &str) -> String {
    let base = ffi_surface_text_base(ctx, rendered);
    let replacements = finite_set_surface_replacements(ctx);
    apply_surface_replacements(&base, &replacements)
}

/// Z3's `max_char` (`zstring::max_char` = `0x2FFFF`): the largest SMT-LIB
/// Unicode code point. A `Char`-sorted term denotes a code point in
/// `[0, AY_MAX_CHAR]`.
pub(crate) const AY_MAX_CHAR: i64 = 196607;

/// Record the sort for an AST handle.
///
/// If `sort` is [`Sort::Char`] or a [`Sort::FiniteDomain`], this also wires the
/// standing invariant `0 <= t <= hi` for the term (once per bound), so a free
/// `Char` / finite-domain value is never an unbounded `Int`. See
/// [`emit_range_axiom`].
pub(crate) fn record_ast_sort(ctx: &mut Z3Context, ast: Z3_ast, sort: Sort) {
    let belongs_to_context = term_ast_belongs_to(ctx, ast);
    debug_assert!(
        belongs_to_context,
        "attempted to record a foreign or malformed term AST"
    );
    if !belongs_to_context {
        return;
    }
    if ast != 0 {
        if sort.is_char() {
            emit_range_axiom(ctx, ast, AY_MAX_CHAR);
        } else if let Some(size) = sort.finite_domain_size() {
            // `size >= 1` is enforced at `Z3_mk_finite_domain_sort`; saturate
            // defensively (a `>= i64::MAX` domain is unbounded in practice).
            let hi = i64::try_from(size.saturating_sub(1)).unwrap_or(i64::MAX);
            emit_range_axiom(ctx, ast, hi);
        }
    }
    let idx = (ast & TERM_AST_PAYLOAD_MASK) as usize;
    if idx >= ctx.ast_sorts.len() {
        ctx.ast_sorts.resize(idx + 1, None);
    }
    ctx.ast_sorts[idx] = Some(sort);
}

/// Push the range invariant `0 <= t <= hi` for the term behind `ast` into
/// `ctx.background_axioms` (deduped, once per interned term per bound).
///
/// SOUNDNESS: a `Char` (`hi = 196607`, the exact range Z3 enforces via
/// `max_char`) or finite-domain value (`hi = size-1`, the exact cardinality
/// bound Z3 enforces on `Z3_mk_finite_domain_sort`) lowers to an `Int` in the
/// engine ([`Sort::as_term_sort`]), which is otherwise unbounded. Attaching the
/// bound makes a Z3-unsat range query (e.g. a `size+1`-element pigeonhole over
/// a finite domain) stay unsat in AY. The bound only ADDS a constraint, so it
/// can never flip unsat→sat; and it is trivially satisfiable, so it introduces
/// no spurious unsat. For an in-range *literal* it is redundant and folds away.
fn emit_range_axiom(ctx: &mut Z3Context, ast: Z3_ast, hi_inclusive: i64) {
    let Some(t) = checked_ast_to_term(ctx, ast) else {
        debug_assert!(false, "internal range axiom received an invalid term AST");
        return;
    };
    if !ctx.range_bounded.insert((t, hi_inclusive)) {
        return; // this exact range invariant was already emitted for this term
    }
    let zero = ctx.solver.int_const(0);
    let max = ctx.solver.int_const(hi_inclusive);
    let lo = ctx.solver.le(zero, t);
    let hi = ctx.solver.le(t, max);
    let bound = ctx.solver.and_many(&[lo, hi]);
    ctx.background_axioms.push(bound);
    ctx.clear_decision_check_artifacts();
}

/// Build the range guard `0 <= t <= hi` as a TERM (not asserted) — used to
/// guard quantified `Char` / finite-domain bound variables in
/// `Z3_mk_forall*`/`Z3_mk_exists*` (see `quantifiers.rs`).
pub(crate) fn range_guard_term(ctx: &mut Z3Context, t: Term, hi_inclusive: i64) -> Term {
    let zero = ctx.solver.int_const(0);
    let max = ctx.solver.int_const(hi_inclusive);
    let lo = ctx.solver.le(zero, t);
    let hi = ctx.solver.le(t, max);
    ctx.solver.and_many(&[lo, hi])
}

/// The inclusive upper range bound a sort carries, if it is one of AY's
/// bounded-Int-lowered sorts (`Char` → 196607, `FiniteDomain(_, n)` → `n-1`).
pub(crate) fn bounded_sort_hi(sort: &Sort) -> Option<i64> {
    if sort.is_char() {
        Some(AY_MAX_CHAR)
    } else {
        sort.finite_domain_size()
            .map(|size| i64::try_from(size.saturating_sub(1)).unwrap_or(i64::MAX))
    }
}

/// Look up sort for an AST handle
pub(crate) fn lookup_ast_sort(ctx: &Z3Context, ast: Z3_ast) -> Option<&Sort> {
    if !term_ast_belongs_to(ctx, ast) {
        return None;
    }
    let idx = (ast & TERM_AST_PAYLOAD_MASK) as usize;
    ctx.ast_sorts.get(idx).and_then(|s| s.as_ref())
}

/// Allocate a sort handle and register it in the context arena (#5498).
/// Assigns a stable semantic sort ID: same `Sort` value → same ID within
/// this context (#6580).
///
/// Handles are HASH-CONSED per context: asking twice for the same `Sort`
/// returns the same `Z3_sort` pointer. Z3 sorts are AST nodes in a
/// hash-consing manager, so `Z3_mk_real_sort(c) == Z3_mk_real_sort(c)` and
/// `Z3_get_sort(c, real_numeral) == Z3_mk_real_sort(c)` hold there, and C
/// consumers written against Z3 compare sorts with `==`. Minting a fresh box
/// per call made every such comparison false.
///
/// `Sort` derives structural `Eq`/`Hash`, so two handles that this pass
/// collapses carry byte-identical payloads and every `(*s).sort` reader is
/// unaffected. `sort_ast_handles[sort_id]` was already the canonical handle;
/// this only makes it the ONLY one, so `sort_cache` now holds exactly one
/// owning pointer per sort id and `Drop`'s `drain_arena` still frees each box
/// exactly once.
pub(crate) fn alloc_sort(ctx: &mut Z3Context, sort: Sort) -> Z3_sort {
    let sort_id = if let Some(&id) = ctx.sort_ids.get(&sort) {
        id
    } else {
        let id = ctx.next_sort_id;
        ctx.next_sort_id += 1;
        ctx.sort_ids.insert(sort.clone(), id);
        id
    };
    // This is the single sort-allocation path, so `sort_ast_handles` cannot
    // desync from `sort_ids`.
    let idx = sort_id as usize;
    if idx >= ctx.sort_ast_handles.len() {
        ctx.sort_ast_handles.resize(idx + 1, ptr::null_mut());
    }
    debug_assert!(
        ctx.sort_ast_handles.len() <= ctx.next_sort_id as usize + 1,
        "sort_ast_handles must track sort_id assignment"
    );
    if !ctx.sort_ast_handles[idx].is_null() {
        return ctx.sort_ast_handles[idx];
    }
    let handle = Box::into_raw(Box::new(SortHandle { sort, sort_id }));
    ctx.sort_cache.push(handle);
    ctx.sort_ast_handles[idx] = handle;
    handle
}

/// Encode a live sort handle as its value-canonical SORT-AST (`Z3_sort_to_ast`).
///
/// # Safety
/// `s` must be a valid, non-null `SortHandle` owned by `ctx`'s arena.
pub(crate) unsafe fn sort_handle_to_ast(ctx: &mut Z3Context, s: Z3_sort) -> Z3_ast {
    // SAFETY: caller guarantees `s` is a live handle from this context's arena.
    let sort_id = unsafe { (*s).sort_id };
    let idx = sort_id as usize;
    // Defensive: every handle flows through `alloc_sort`, which registered the
    // slot; re-register here anyway so a decode can never miss.
    if idx >= ctx.sort_ast_handles.len() {
        ctx.sort_ast_handles.resize(idx + 1, ptr::null_mut());
    }
    if ctx.sort_ast_handles[idx].is_null() {
        ctx.sort_ast_handles[idx] = s;
    }
    encode_indexed_ast(ctx, SORT_AST_TAG, sort_id as usize).unwrap_or(0)
}

/// Extract and verify the per-context salt of a tagged handle (see
/// [`HANDLE_SALT_MASK`]). `false` means the handle was minted by a DIFFERENT
/// context (or forged) and must fail closed — decoding it against this
/// context's tables would resolve to an unrelated object.
fn handle_salt_matches(ctx: &Z3Context, a: Z3_ast) -> bool {
    ((a >> HANDLE_SALT_SHIFT) & HANDLE_SALT_MASK) as u32 == ctx.handle_salt
}

/// Encode an index into one of the context-owned tagged AST arenas.
///
/// The top nibble identifies the arena, bits 32–58 authenticate the owning
/// context, and the low 32 bits hold the arena index. `None` means the arena
/// has exceeded the representable index space; callers must fail closed before
/// inserting the value so no two objects can acquire the same handle.
pub(crate) fn encode_indexed_ast(ctx: &Z3Context, tag: u64, index: usize) -> Option<Z3_ast> {
    debug_assert_eq!(tag & HANDLE_TAG_MASK, tag);
    debug_assert_eq!(tag.count_ones(), 1);
    let index = u32::try_from(index).ok()?;
    Some(tag | (u64::from(ctx.handle_salt) << HANDLE_SALT_SHIFT) | u64::from(index))
}

/// Authenticate and decode an index from a context-owned tagged AST arena.
///
/// A wrong tag, a foreign/forged context salt, or any bits outside the defined
/// tag/salt/index fields fails closed. Arena liveness (index in range) remains
/// the caller's responsibility because each tagged kind has a different store.
pub(crate) fn decode_indexed_ast(ctx: &Z3Context, a: Z3_ast, tag: u64) -> Option<usize> {
    debug_assert_eq!(tag & HANDLE_TAG_MASK, tag);
    debug_assert_eq!(tag.count_ones(), 1);
    if a & HANDLE_TAG_MASK != tag || !handle_salt_matches(ctx, a) {
        return None;
    }
    let defined_bits =
        HANDLE_TAG_MASK | (HANDLE_SALT_MASK << HANDLE_SALT_SHIFT) | TAGGED_AST_INDEX_MASK;
    if a & !defined_bits != 0 {
        return None;
    }
    Some((a & TAGGED_AST_INDEX_MASK) as usize)
}

/// Decode a SORT-AST handle back to the canonical `SortHandle`, or null if the
/// value is not a live sort-ast of THIS context (wrong tag, foreign/forged
/// salt, or dangling index all fail closed to null).
pub(crate) fn sort_ast_to_handle(ctx: &Z3Context, a: Z3_ast) -> Z3_sort {
    let Some(idx) = decode_indexed_ast(ctx, a, SORT_AST_TAG) else {
        return ptr::null_mut();
    };
    ctx.sort_ast_handles
        .get(idx)
        .copied()
        .unwrap_or(ptr::null_mut())
}

/// Encode a live func_decl handle as its value-canonical FUNC-DECL-AST
/// (`Z3_func_decl_to_ast`): get-or-insert the declaration's semantic identity
/// ([`DeclAstKey`]) into the interning table, so equal declarations (same
/// name/domain/range/params/dt-op) always yield the SAME tagged handle even
/// when presented through distinct `Z3_func_decl` pointers.
///
/// # Safety
/// `d` must be a valid, non-null `FuncDeclHandle` owned by `ctx`'s arena.
pub(crate) unsafe fn func_decl_handle_to_ast(ctx: &mut Z3Context, d: Z3_func_decl) -> Z3_ast {
    // SAFETY: caller guarantees `d` is a live handle from this context's arena.
    let key = unsafe {
        DeclAstKey {
            decl: (*d).decl.clone(),
            params: (*d).params.clone(),
            dt_op: DtOpKind::of((*d).dt_op.as_ref()),
            finite_set_op: (*d).finite_set_op,
        }
    };
    let idx = if let Some(&i) = ctx.decl_ast_ids.get(&key) {
        i
    } else {
        let i = u32::try_from(ctx.decl_ast_handles.len()).unwrap_or(u32::MAX);
        ctx.decl_ast_ids.insert(key, i);
        ctx.decl_ast_handles.push(d);
        i
    };
    encode_indexed_ast(ctx, FUNC_DECL_AST_TAG, idx as usize).unwrap_or(0)
}

/// Decode a FUNC-DECL-AST handle back to the canonical `FuncDeclHandle`, or
/// null if the value is not a live func-decl-ast of this context. The returned
/// pointer is the CANONICAL handle for the declaration and may differ from the
/// pointer the ast was minted from; equality is by value
/// (`Z3_is_eq_func_decl` value-compares) — documented divergence from z3's
/// hash-consed pointer identity.
pub(crate) fn func_decl_ast_to_handle(ctx: &Z3Context, a: Z3_ast) -> Z3_func_decl {
    let Some(idx) = decode_indexed_ast(ctx, a, FUNC_DECL_AST_TAG) else {
        return ptr::null_mut();
    };
    ctx.decl_ast_handles
        .get(idx)
        .copied()
        .unwrap_or(ptr::null_mut())
}

/// Resolve a `Z3_sort`-typed argument that may actually be a TAGGED SORT-AST
/// handle smuggled through the pointer parameter.
///
/// Stock z3py passes `sort.as_ast()` into `Z3_parser_context_add_sort`
/// (z3.py:9531) — with real sort-asts that is a tagged `u64` reinterpreted as
/// a pointer, and a raw deref would be a garbage-pointer SEGV (not a catchable
/// panic). Heap pointers never have bits 60–63 set on supported platforms
/// (macOS arm64 / Linux x86-64 ≤ 2^56), so the tag discriminator is total:
/// tagged values decode through [`sort_ast_to_handle`], plain pointers pass
/// through. Returns `None` for null and for a dangling/foreign tagged value.
pub(crate) fn sort_arg_handle(ctx: &Z3Context, s: Z3_sort) -> Option<Z3_sort> {
    let raw = s as u64;
    if raw & HANDLE_TAG_MASK != 0 {
        let h = sort_ast_to_handle(ctx, raw);
        (!h.is_null()).then_some(h)
    } else {
        (!s.is_null()).then_some(s)
    }
}

/// Twin of [`sort_arg_handle`] for `Z3_func_decl`-typed arguments (stock z3py
/// passes `decl.as_ast()` into `Z3_parser_context_add_decl`, z3.py:9534).
pub(crate) fn func_decl_arg_handle(ctx: &Z3Context, d: Z3_func_decl) -> Option<Z3_func_decl> {
    let raw = d as u64;
    if raw & HANDLE_TAG_MASK != 0 {
        let h = func_decl_ast_to_handle(ctx, raw);
        (!h.is_null()).then_some(h)
    } else {
        (!d.is_null()).then_some(d)
    }
}

/// Allocate a func_decl handle and register it in the context arena (#5498).
pub(crate) fn cache_func_decl(ctx: &mut Z3Context, decl: FuncDecl) -> Z3_func_decl {
    cache_func_decl_with_params(ctx, decl, Vec::new())
}

/// Allocate a declaration handle while preserving the caller-visible Z3
/// symbol independently from the collision-proof name stored in `decl`.
pub(crate) fn cache_func_decl_with_symbol(
    ctx: &mut Z3Context,
    decl: FuncDecl,
    symbol: SymbolKey,
) -> Z3_func_decl {
    ctx.ffi_decl_symbols.insert(decl.name().to_string(), symbol);
    cache_func_decl(ctx, decl)
}

/// Allocate a func_decl handle with indexed operator parameters (#6580 F2).
pub(crate) fn cache_func_decl_with_params(
    ctx: &mut Z3Context,
    decl: FuncDecl,
    params: Vec<c_int>,
) -> Z3_func_decl {
    let symbol = ctx.ffi_decl_symbols.get(decl.name()).cloned();
    let decl_id = ctx.next_decl_id;
    ctx.next_decl_id += 1;
    let handle = Box::into_raw(Box::new(FuncDeclHandle {
        decl,
        symbol,
        params,
        dt_op: None,
        finite_set_op: None,
        decl_id,
    }));
    ctx.func_decl_cache.push(handle);
    handle
}

/// Allocate a function-interpretation entry and register it in the context's
/// owning arena (`func_entry_cache`). Returned raw pointer is referenced (not
/// owned) by the enclosing [`FuncInterpHandle`].
pub(crate) fn cache_func_entry(
    ctx: &mut Z3Context,
    args: Vec<Z3_ast>,
    value: Z3_ast,
) -> *mut FuncEntryHandle {
    let handle = Box::into_raw(Box::new(FuncEntryHandle { args, value }));
    ctx.func_entry_cache.push(handle);
    handle
}

/// Allocate a function-interpretation handle and register it in the context
/// arena (`func_interp_cache`). `entries` are non-owning references to boxes
/// already registered in `func_entry_cache`.
pub(crate) fn cache_func_interp(
    ctx: &mut Z3Context,
    arity: c_uint,
    entries: Vec<*mut FuncEntryHandle>,
    else_ast: Z3_ast,
) -> Z3_func_interp {
    let handle = Box::into_raw(Box::new(FuncInterpHandle {
        arity,
        entries,
        else_ast,
    }));
    ctx.func_interp_cache.push(handle);
    handle
}

/// Substitute the self-reference encoding of a (possibly recursive) datatype —
/// `Sort::Uninterpreted(<dt name>)`, the representation `build_datatype_sort`
/// and the core term store use for a recursive field — with the canonical
/// `Sort::Datatype` value, recursing through the parametric Array/Seq
/// constructors. `Sort::Datatype` itself is atomic here: its INTERNAL fields
/// keep the Uninterpreted self-reference (that nesting is the canonical core
/// value; rewriting it would mint a DIFFERENT `Sort` and break identity with
/// the sort handle `alloc_sort` registered for the datatype).
fn resolve_dt_self_sort(sort: &Sort, dt_name: &str, dt_sort: &Sort) -> Sort {
    match sort {
        Sort::Uninterpreted(n) if n == dt_name => dt_sort.clone(),
        Sort::Array(arr) => Sort::array(
            resolve_dt_self_sort(&arr.index_sort, dt_name, dt_sort),
            resolve_dt_self_sort(&arr.element_sort, dt_name, dt_sort),
        ),
        Sort::Seq(elem) => Sort::seq(resolve_dt_self_sort(elem, dt_name, dt_sort)),
        _ => sort.clone(),
    }
}

/// Allocate a datatype-operator func_decl handle and register it in the arena.
///
/// The returned handle carries a [`DatatypeOp`] so that `Z3_mk_app` routes the
/// application through AY's verified datatype builders (#phase3-dt).
///
/// SORT-IDENTITY (#wavec-p3-capi-stubs repair, skeptic F1): a self-recursive
/// datatype's constructor/accessor signatures arrive here with the recursive
/// position encoded as `Sort::Uninterpreted(<dt name>)` (the core term-store
/// representation). Left as-is, `Z3_get_domain`/`Z3_get_range` would alloc
/// that Uninterpreted sort — a DIFFERENT semantic sort id than the datatype
/// sort itself, so `IL.constructor(0).domain(1).as_ast() != IL.as_ast()`
/// (wrong kind 0 decode, and z3py's `cast` → `SortRef.eq` raises on
/// `cons(5, nil)`; real z3 hash-conses them equal). This is the single choke
/// point every datatype decl flows through, so the self-reference is resolved
/// to the canonical `Sort::Datatype` HERE — in the exposed `FuncDecl`
/// signature and the accessor's `result_sort` — while the `DatatypeOp`'s
/// embedded `DatatypeSort` keeps the core representation the verified
/// builders expect.
pub(crate) fn cache_dt_func_decl(
    ctx: &mut Z3Context,
    decl: FuncDecl,
    dt_op: DatatypeOp,
) -> Z3_func_decl {
    // Identify the datatype this decl belongs to: a Constructor op carries it;
    // recognizers/accessors are unary with the datatype as their sole domain.
    let self_dt_sort: Option<(String, Sort)> = match &dt_op {
        DatatypeOp::Constructor { dt, .. } => Some((dt.name.clone(), Sort::Datatype(dt.clone()))),
        DatatypeOp::Recognizer { .. } | DatatypeOp::Accessor { .. } => decl
            .domain()
            .iter()
            .chain(std::iter::once(decl.range()))
            .find_map(|s| match s {
                Sort::Datatype(dt) => Some((dt.name.clone(), s.clone())),
                _ => None,
            }),
    };
    let (decl, dt_op) = if let Some((dt_name, dt_sort)) = self_dt_sort {
        let resolved_decl = FuncDecl::new(
            decl.name().to_string(),
            decl.domain()
                .iter()
                .map(|s| resolve_dt_self_sort(s, &dt_name, &dt_sort))
                .collect(),
            resolve_dt_self_sort(decl.range(), &dt_name, &dt_sort),
        );
        let resolved_op = match dt_op {
            DatatypeOp::Accessor { field, result_sort } => DatatypeOp::Accessor {
                field,
                result_sort: resolve_dt_self_sort(&result_sort, &dt_name, &dt_sort),
            },
            other => other,
        };
        (resolved_decl, resolved_op)
    } else {
        (decl, dt_op)
    };
    let symbol = ctx.ffi_decl_symbols.get(decl.name()).cloned();
    let decl_id = ctx.next_decl_id;
    ctx.next_decl_id += 1;
    let handle = Box::into_raw(Box::new(FuncDeclHandle {
        decl,
        symbol,
        params: Vec::new(),
        dt_op: Some(dt_op),
        finite_set_op: None,
        decl_id,
    }));
    ctx.func_decl_cache.push(handle);
    handle
}

/// Datatype-declaration variant that records the exact caller-visible symbol
/// while retaining a collision-proof internal declaration name.
pub(crate) fn cache_dt_func_decl_with_symbol(
    ctx: &mut Z3Context,
    decl: FuncDecl,
    dt_op: DatatypeOp,
    symbol: SymbolKey,
) -> Z3_func_decl {
    if let DatatypeOp::Recognizer { ctor } = &dt_op {
        if let Some(dt_sort) = decl.domain().first() {
            ctx.ffi_dt_recognizers
                .insert((dt_sort.clone(), ctor.clone()), symbol.clone());
        }
    }
    ctx.ffi_decl_symbols.insert(decl.name().to_string(), symbol);
    cache_dt_func_decl(ctx, decl, dt_op)
}

/// Reject user declarations whose NAME would be captured by an internal
/// AY reserved namespace (#wavec-p3-capi-stubs repair, skeptic finding 2).
///
/// SOUNDNESS: AY's core array theory matches array-map terms purely by name —
/// `TermStore::get_array_map` treats ANY `App` named `map[<f>]` as the array
/// map of `<f>` and rewrites `select(map[f](a..), i) → f(select(a, i)..)`.
/// An ordinary user function that HAPPENS to be named `map[f]` therefore
/// silently acquires map semantics: measured wrong verdict (z3 `sat`, AY
/// `unsat`) for `(declare-fun |map[f]| ((Array Int Int)) (Array Int Int))`
/// applied to an array. `!ay.`-prefixed names are AY-internal witnesses
/// (e.g. the `!ay.array-ext!<n>` extensionality witnesses `Z3_mk_ext` mints)
/// and could likewise collide with engine-generated constants.
///
/// Real z3 accepts such names; AY refuses them with `Z3_INVALID_ARG` — an
/// honest, fail-closed divergence (an error is always sound; the silent
/// wrong verdict is not). Returns the detailed error message to install, or
/// `None` when the name is safe.
pub(crate) fn reserved_name_error(name: &str) -> Option<String> {
    let captured_by_array_map = name.starts_with("map[") && name.ends_with(']');
    let internal_namespace = name.starts_with("!ay.");
    (captured_by_array_map || internal_namespace).then(|| {
        format!(
            "invalid declaration: symbol name '{name}' is reserved by AY \
             (names of the form 'map[...]' denote the internal array-map \
             operator and would silently change the formula's meaning; \
             '!ay.*' names are internal engine witnesses). Rename the symbol."
        )
    })
}

/// Fail-close scan for the reserved `map[...]` namespace inside SMT-LIB 2
/// text handed to the FFI parse/eval entry points.
///
/// Those entry points hand the text to AY's core parser+elaborator, where the
/// same name-capture channel [`reserved_name_error`] closes for the C API is
/// still open (a quoted symbol `|map[f]|` declares an ordinary function whose
/// applications the array theory then rewrites — measured wrong verdict). A
/// `map[`-prefixed symbol can ONLY be written as a quoted symbol (`[` is not
/// in the SMT-LIB simple-symbol alphabet), so scanning for the byte sequence
/// `|map[` covers every declaration spelling. The scan is deliberately
/// over-approximate (the sequence inside a string literal also trips it):
/// refusing with an error is sound; the wrong verdict it prevents is not.
pub(crate) fn smtlib2_reserved_error(input: &str) -> Option<String> {
    input.contains("|map[").then(|| {
        "input contains a quoted symbol in AY's reserved 'map[...]' namespace \
         (these names denote the internal array-map operator and would \
         silently change the formula's meaning); rename the symbol"
            .to_string()
    })
}

/// Parse an indexed symbol like `"(_ extract 7 4)"` into base name and indices.
/// Returns `(base_name, indices)`. Non-indexed names return `(name, [])`.
pub(crate) fn parse_indexed_name(name: &str) -> (String, Vec<c_int>) {
    if let Some(inner) = name.strip_prefix("(_ ").and_then(|s| s.strip_suffix(')')) {
        let parts: Vec<&str> = inner.split_whitespace().collect();
        if parts.len() >= 2 {
            let base = parts[0].to_string();
            let indices: Vec<c_int> = parts[1..].iter().filter_map(|s| s.parse().ok()).collect();
            return (base, indices);
        }
    }
    (name.to_string(), Vec::new())
}

/// Allocate an AST vector handle and register it in the context arena (#5498).
pub(crate) fn cache_ast_vector(ctx: &mut Z3Context, asts: Vec<Z3_ast>) -> Z3_ast_vector {
    let handle = Box::into_raw(Box::new(AstVectorHandle { asts }));
    ctx.ast_vector_cache.push(handle);
    handle
}

/// Allocate an (empty) AST map handle and register it in the context arena.
pub(crate) fn cache_ast_map(ctx: &mut Z3Context) -> Z3_ast_map {
    let handle = Box::into_raw(Box::new(AstMapHandle::default()));
    ctx.ast_map_cache.push(handle);
    handle
}

/// Allocate a goal handle (depth 0) and register it in the context arena.
pub(crate) fn cache_goal(ctx: &mut Z3Context, formulas: Vec<Z3_ast>) -> Z3_goal {
    cache_goal_with_depth(ctx, formulas, 0)
}

/// Allocate a goal handle at an explicit transformation `depth` and register it
/// in the context arena. Used for subgoals produced by `Z3_tactic_apply`, which
/// carry the engine's real depth.
pub(crate) fn cache_goal_with_depth(
    ctx: &mut Z3Context,
    formulas: Vec<Z3_ast>,
    depth: usize,
) -> Z3_goal {
    let handle = Box::into_raw(Box::new(GoalHandle { formulas, depth }));
    ctx.goal_cache.push(handle);
    handle
}

/// Allocate an apply-result handle and register it in the context arena. The
/// `subgoals` are `GoalHandle` pointers that MUST already be registered in
/// `goal_cache` (so ownership/free is single-sourced there).
pub(crate) fn cache_apply_result(ctx: &mut Z3Context, subgoals: Vec<Z3_goal>) -> Z3_apply_result {
    let handle = Box::into_raw(Box::new(ApplyResultHandle { subgoals }));
    ctx.apply_result_cache.push(handle);
    handle
}

/// Allocate a probe handle and register it in the context arena.
pub(crate) fn cache_probe(ctx: &mut Z3Context, probe: ay_frontend::Probe) -> Z3_probe {
    let handle = Box::into_raw(Box::new(ProbeHandle { probe }));
    ctx.probe_cache.push(handle);
    handle
}

/// Allocate a parser-context handle and register it in the context arena.
pub(crate) fn cache_parser_context(ctx: &mut Z3Context) -> Z3_parser_context {
    let handle = Box::into_raw(Box::new(ParserContextHandle {
        added_sorts: Vec::new(),
        added_decls: Vec::new(),
        refcount: 0,
    }));
    ctx.parser_context_cache.push(handle);
    handle
}
