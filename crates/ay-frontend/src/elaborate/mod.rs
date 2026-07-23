// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Elaboration: convert parsed terms to internal representation
//!
//! This module bridges the parser's AST to the core term representation.
//! It handles:
//! - Sort conversion
//! - Term internalization into the hash-consed store
//! - Symbol table management
//! - Let-binding expansion

use crate::command::Term as ParsedTerm;
// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{Sort, TermId, TermStore};

/// The reserved prefix for internal AY symbols.
/// User declarations with this prefix are rejected.
pub(crate) const INTERNAL_SYMBOL_PREFIX: &str = "__ay_";

/// Builtin theory-operator names that AY's term layer and theory solvers
/// recognize STRUCTURALLY, by name, on `App(Symbol::Named(name), ..)` — i.e.
/// independently of any `declare-fun`. Because `TermData` has no dedicated
/// per-op variant (every operator is an `App(Named(name), args)`), a
/// `declare-fun`/`define-fun`/`declare-const` of one of these names does NOT
/// create a fresh uninterpreted function: the user-symbol elaboration path
/// (`elaborate_app`) builds the very same `App(Named(name), ..)` shape the
/// theory then matches, so the forged symbol is silently conflated with the
/// builtin operator. For array's `const-array`/`select`/`store` that conflation
/// is a *wrong-UNSAT* (a false claim is "proved") — the cardinal soundness
/// failure. Reserving these names makes such a declaration a clean elaboration
/// error instead.
///
/// This gates DECLARATIONS only. The builtin USE path (`(select a i)`,
/// `((as const T) v)`, `(bvadd x y)`, …) never declares these names — it is
/// parsed directly by the app elaborator — so it is entirely unaffected. These
/// are theory/extension operator names that no conforming SMT-LIB script
/// declares (redeclaring a theory function symbol is malformed), so rejecting a
/// declaration of one is both sound (fail-closed) and standards-consistent.
///
/// The names are AY's own structural-match vocabulary, gathered from the app
/// elaborators (`elaborate/app/*.rs`), the qualified-identifier elaborator
/// (`elaborate/qualified.rs`, which matches `(as <name> <sort>)` names BEFORE
/// falling back to declared symbols), the term elaborator (`elaborate/term.rs`,
/// rounding-mode constants), and the term/theory matchers in `ay-core`
/// (`term/array.rs`, `term/bitvector/*`, …) and `ay-dpll`.
///
/// Deliberately EXCLUDED (each would reject legitimate input): see the
/// companion table [`EXCLUDED_DECLARABLE_OP_NAMES`], which lists every
/// elaborator-recognized name that REMAINS user-declarable together with its
/// documented reason. The two tables are kept mutually exhaustive over the
/// elaborator match-arm vocabulary by the drift-proof test
/// `test_reserved_op_table_covers_all_elaborator_match_arms`, which
/// mechanically re-extracts the matched names from the elaborator sources
/// (`app/*.rs`, `indexed.rs`, `qualified.rs`, `term.rs`) at test time and fails
/// on any name in neither table — so a future match-arm addition cannot
/// silently widen the forgery surface.
///
/// Intentionally not listed in either STATIC table (they are gated
/// DYNAMICALLY, per context state, because the vulnerable vocabulary is
/// user-defined): datatype constructor/selector/tester names. The DT theory
/// matches these by name too, so they get two dedicated dynamic gates:
/// declaring a fn/const/define-fun whose name is a registered datatype member
/// is rejected ([`ElaborateError::DatatypeMemberCollision`], see
/// `declarations.rs`), and re-declaring an existing sort name as a datatype —
/// the only way a pre-existing user symbol can mention the datatype's carrier
/// sort and be captured by the new members — is rejected
/// ([`ElaborateError::SortRedeclaration`], see `datatypes.rs`). (An earlier
/// revision of this comment claimed `datatypes.rs` already gated post-hoc
/// member forgery; that was FALSE — its `validate_datatype_names` only checks
/// the static reserved table at datatype-declaration time. Both post-hoc
/// `declare-fun is-Cons`/`hd` forgeries were confirmed wrong-UNSATs before the
/// dynamic gates above were added.) Also not listed: bare collection words
/// (`union`, `member`, `subset`, …) that AY matches ONLY in dotted form
/// (`set.union`), which are legitimate user-symbol names.
#[rustfmt::skip]
pub(crate) const RESERVED_OP_NAMES: &[&str] = &[
    // ---- Arrays (term/array.rs, app/core.rs, indexed.rs as-array) ----
    "select", "store", "const-array", "lambda-array", "default", "as-array",
    // ---- Bit-vectors (term/bitvector/*, app/bitvectors.rs, indexed.rs) ----
    "bvadd", "bvsub", "bvmul", "bvudiv", "bvurem", "bvsdiv", "bvsrem", "bvsmod",
    "bvneg", "bvnot", "bvand", "bvor", "bvxor", "bvnand", "bvnor", "bvxnor",
    "bvshl", "bvlshr", "bvashr", "bvcomp",
    "bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge",
    "concat", "bv2nat", "bv2int", "int2bv", "ubv_to_int", "sbv_to_int",
    "extract", "zero_extend", "sign_extend", "repeat", "rotate_left", "rotate_right",
    // BV overflow predicates (app/bitvectors.rs)
    "bvnego", "bvsaddo", "bvuaddo", "bvsdivo", "bvsmulo", "bvumulo", "bvssubo", "bvusubo",
    // BV reduction ops (app/bitvectors.rs) — 1-bit AND/OR fold of all bits
    "bvredand", "bvredor",
    // ---- Floating point (term/floating_point*, app/floating_point.rs, indexed.rs) ----
    "fp", "fp.abs", "fp.neg", "fp.add", "fp.sub", "fp.mul", "fp.div", "fp.fma",
    "fp.sqrt", "fp.rem", "fp.roundToIntegral", "fp.min", "fp.max", "fp.leq",
    "fp.lt", "fp.geq", "fp.gt", "fp.eq",
    // FP classification predicates — ALL seven from the single arm at
    // floating_point.rs:64 (forging fp.isZero/fp.isNaN/fp.isInfinite was a
    // confirmed wrong-UNSAT: `(not (fp.isZero (_ +zero 8 24)))` returned unsat).
    "fp.isNaN", "fp.isInfinite", "fp.isZero", "fp.isNormal", "fp.isSubnormal",
    "fp.isNegative", "fp.isPositive",
    "fp.to_real", "fp.to_ieee_bv", "to_fp", "to_fp_unsigned", "fp.to_ubv", "fp.to_sbv",
    // FP rounding-mode constants
    "RNE", "RNA", "RTP", "RTN", "RTZ",
    "roundNearestTiesToEven", "roundNearestTiesToAway",
    "roundTowardPositive", "roundTowardNegative", "roundTowardZero",
    // ---- Sets (elaborate/app/set.rs, ay-dpll set theory) ----
    // (`set.subset` is declaration-activated — see EXCLUDED_DECLARABLE_OP_NAMES.)
    "set.union", "set.inter", "set.minus", "set.member", "set.card",
    "set.singleton", "set.insert", "set.remove", "set.complement",
    // ---- Multisets (elaborate/app/multiset.rs) ----
    // ALL fourteen ops from multiset.rs, including the pointwise/higher-order
    // arm at multiset.rs:110-118 (forging those conflates with the builtin —
    // fail-closed `unknown` today, but the surface must be sealed uniformly).
    // (`multiset.subset` is declaration-activated — see
    // EXCLUDED_DECLARABLE_OP_NAMES.)
    "multiset.count", "multiset.insert", "multiset.remove", "multiset.singleton",
    "multiset.choose",
    "multiset.union", "multiset.inter", "multiset.diff", "multiset.map",
    "multiset.filter", "multiset.fold", "multiset.comprehension", "multiset.sum",
    // ---- Maps (elaborate/app/map.rs) ----
    // (`map.dom`/`map.subset` are declaration-activated — see
    // EXCLUDED_DECLARABLE_OP_NAMES.)
    "map.get", "map.insert", "map.remove", "map.contains_key",
    // ---- Sequences (elaborate/app/sequences.rs, ay-dpll seq theory) ----
    "seq.++", "seq.at", "seq.contains", "seq.empty", "seq.extract", "seq.foldl",
    "seq.fold_left", "seq.foldli", "seq.fold_lefti",
    "seq.in_re", "seq.in.re", "seq.indexof", "seq.last_indexof",
    "seq.len", "seq.map", "seq.mapi", "seq.nth", "seq.prefixof", "seq.replace",
    "seq.replace_all", "seq.suffixof", "seq.to_re", "seq.to.re", "seq.unit",
    // ---- Strings (elaborate/app/strings.rs, ay-dpll str theory) ----
    "str.++", "str.<", "str.<=", "str.at", "str.contains", "str.from_code",
    "str.from_int", "str.in_re", "str.in.re", "str.indexof", "str.is_digit",
    "str.len", "str.prefixof", "str.replace", "str.replace_all", "str.replace_re",
    "str.replace_re_all", "str.substr", "str.suffixof", "str.to_code", "str.to_int",
    "str.to.int", "str.to_lower", "str.to_upper", "str.to_re", "str.to.re", "int.to.str",
    // ---- Regular expressions (elaborate/app/strings.rs) ----
    "re.*", "re.+", "re.++", "re.all", "re.allchar", "re.comp", "re.diff",
    "re.inter", "re.none", "re.opt", "re.range", "re.union", "re.loop", "re.to_re",
    // ---- Char theory (elaborate/app/strings.rs) — desugars to Int on the code point ----
    // (z3 has char.<= but not char.<, so char.< is intentionally absent.)
    "char.to_int", "char.<=", "char.is_digit",
    // ---- Qualified-(as)-path names (elaborate/qualified.rs) ----
    // `elaborate_qualified_app` matches these names BEFORE its declared-symbol
    // fallback, so a user `declare-fun` of one was silently conflated with the
    // builtin at every `(as <name> <sort>)` use — each was a confirmed
    // wrong-UNSAT (e.g. declared `set.empty` + `(select (as set.empty (Array
    // Int Bool)) 0)` treated the forged symbol as the constant-false array).
    // `seq.empty` (also a qualified-path arm) is already reserved in the
    // sequences section above. The fifth qualified-path name, `const`, is NOT
    // reserved: real-world QF_UF benchmarks legitimately declare it (the
    // B-method CLEARSY fixtures declare `|const|`), so its arm is instead
    // guarded to defer to a declared user symbol — see
    // EXCLUDED_DECLARABLE_OP_NAMES ("declared-shadowed") and `qualified.rs`.
    "set.empty", "multiset.empty", "map.empty",
];

/// Check whether `name` is a builtin theory-operator name AY matches
/// structurally (see [`RESERVED_OP_NAMES`]).
pub fn is_reserved_op_name(name: &str) -> bool {
    RESERVED_OP_NAMES.contains(&name)
}

/// Elaborator-recognized operator names that REMAIN user-declarable, each with
/// its documented reason. This is the explicit complement of
/// [`RESERVED_OP_NAMES`]: the drift-proof test
/// `test_reserved_op_table_covers_all_elaborator_match_arms` mechanically
/// extracts every name the app elaborators (`elaborate/app/*.rs`,
/// `elaborate/indexed.rs`) match structurally and asserts each one appears in
/// exactly one of the two tables — adding a new match arm without classifying
/// its name fails the test, so the forgery surface cannot silently widen.
///
/// Reason tags:
///
/// * `"map-target"` — SMT-LIB Core connectives and Ints/Reals operators. AY's
///   higher-order `(_ map f)` feature REQUIRES its target `f` to be a declared
///   symbol (it is looked up in the symbol table), and pointwise boolean/
///   arithmetic array maps legitimately `declare-fun` these very names — e.g.
///   `((_ map not) s)` implements set complement over `(Array _ Bool)` (see the
///   `array_map` suites). Reserving them would break that supported
///   capability. Their forge-as-UF conflation is a separate, pre-existing
///   entanglement with the map design, not the theory-extension cardinal bug
///   the reserved table closes. (Verified: `legit_map_not.smt2` — declare-fun
///   `not` + `((_ map not) s)` — still elaborates and answers `sat`.)
///
/// * `"indexed-only"` — identifiers recognized solely inside `(_ …)` indexed
///   forms (`(_ map f)`, `(_ is C)`, `(_ divisible n)`, `(_ at-most k)`, …,
///   and the structured Char/FP special literals `(_ Char n)`/
///   `(_ +zero eb sb)`/`(_ NaN eb sb)`/… matched in `indexed.rs`. A plain
///   `App(Named(name), ..)` of the bare name is never theory-matched, so a
///   user declaration cannot conflate with the builtin (adversarially
///   verified for `map`/`at-most`/`at-least`/`pble`/`pbge`/`pbeq`/`divisible`/
///   `re.^`, and for quoted-symbol FP-literal forgeries: sat/correct).
///
/// * `"pattern-binder"` — `_`, matched in `term.rs` only as the wildcard
///   binder of a `(match …)` default case. It is not an operator and is never
///   elaborated as an application head, so it cannot conflate.
///
/// * `"declared-shadowed"` — `const`, the constant-array qualified identifier
///   `((as const (Array ..)) v)`. It stays declarable because real-world
///   QF_UF benchmarks legitimately declare it (the B-method CLEARSY
///   regression fixtures declare `(declare-fun |const| (U U) U)` — reserving
///   it broke `test_clearsy_00307/00310_full_instance_matches_z3`). Instead
///   its `qualified.rs` arm is GUARDED on `const` not being a declared
///   symbol: once declared, both bare applications and `(as const <sort>)`
///   resolve to the user symbol (a plain uninterpreted application — nothing
///   in the term layer matches bare `const` structurally), so the forged-
///   builtin conflation (rc_const_as wrong-UNSAT) is closed by shadowing
///   rather than by reservation.
///
/// * `"declaration-activated"` — AY-extension collection predicates whose
///   `declare-fun` IS the documented activation route for the native
///   collection solvers: deductive-checks's encoder declares exactly these names via
///   the ay-dpll programmatic API (`try_declare_fun("set.subset", …)`, …) to
///   route the formula to the native QF_SETLIA/map/multiset procedures, and
///   the declared symbol is *intended* to denote the builtin predicate.
///   Reserving them outright breaks the default `Set::subset_of`/`Map::dom`/
///   `Map::subset_of`/`Multiset::subset` encodings downstream (hard-fail on
///   `try_declare_fun`). Instead they are gated by SIGNATURE
///   ([`declaration_activated_signature_ok`]): only a `declare-fun` at the
///   native collection shape (`(Array …) (Array …) -> Bool` for the subset
///   predicates, `(Array …) -> (Array …)` for `map.dom`) is accepted — that
///   declaration *requests the native predicate semantics*, which is the
///   activation contract. Every other declaration form is rejected
///   fail-closed: `declare-const`, `define-fun`(-rec), datatype
///   constructor/selector/tester names, and any mismatched signature.
///   Probed on this build:
///   `(declare-fun set.subset (Int Int) Bool)` + `(not (set.subset 0 0))`,
///   `(declare-fun multiset.subset (Int Int) Bool)`,
///   `(declare-fun map.subset (Int Int) Bool)`, and
///   `(declare-fun map.dom (Int) Int)` are all rejected at elaboration
///   (before the guard, the first answered `unsat` via native ground-identity
///   reflexivity — a definitive verdict on a forged symbol); at the native
///   signature, `(not (set.subset A A))` / `(not (multiset.subset M M))`
///   answer `unsat`, which is CORRECT for the native predicate the
///   declaration requests (subset reflexivity holds in every model).
#[rustfmt::skip]
pub(crate) const EXCLUDED_DECLARABLE_OP_NAMES: &[(&str, &str)] = &[
    // SMT-LIB Core connectives (elaborate/app/core.rs)
    ("and", "map-target"), ("or", "map-target"), ("not", "map-target"),
    ("xor", "map-target"), ("=>", "map-target"), ("implies", "map-target"),
    ("=", "map-target"), ("distinct", "map-target"), ("ite", "map-target"),
    // Ints/Reals operators (elaborate/app/arithmetic.rs, app/core.rs)
    ("+", "map-target"), ("-", "map-target"), ("*", "map-target"),
    ("/", "map-target"), ("^", "map-target"), ("div", "map-target"),
    ("mod", "map-target"), ("rem", "map-target"), ("abs", "map-target"),
    ("min", "map-target"), ("max", "map-target"),
    ("<", "map-target"), ("<=", "map-target"), (">", "map-target"),
    (">=", "map-target"),
    ("to_int", "map-target"), ("to_real", "map-target"), ("is_int", "map-target"),
    // Indexed-form-only identifiers (elaborate/indexed.rs)
    ("map", "indexed-only"), ("is", "indexed-only"), ("divisible", "indexed-only"),
    ("at-most", "indexed-only"), ("at-least", "indexed-only"),
    ("pble", "indexed-only"), ("pbge", "indexed-only"), ("pbeq", "indexed-only"),
    ("re.^", "indexed-only"),
    // Datatype field update `((_ update-field <sel>) record value)`
    // (elaborate/indexed.rs): matched ONLY inside the `(_ …)` indexed form, so a
    // bare `App(Named("update-field"), ..)` is never theory-matched and a user
    // declaration of `update-field` cannot conflate with the builtin.
    ("update-field", "indexed-only"),
    // Special-relations family (elaborate/indexed.rs): special ONLY as the
    // indexed identifier `(_ partial-order N)` &c. The bare name is a legal user
    // function — Verus's own cvc5 prelude declares `(declare-fun partial-order
    // (Height Height) Bool)` — so these must stay declarable, not reserved.
    ("partial-order", "indexed-only"), ("linear-order", "indexed-only"),
    ("tree-order", "indexed-only"), ("piecewise-linear-order", "indexed-only"),
    // Char and FP special literals, matched only inside a structured `(_ …)` form
    ("Char", "indexed-only"), ("char", "indexed-only"),
    ("+zero", "indexed-only"), ("-zero", "indexed-only"),
    ("+oo", "indexed-only"), ("-oo", "indexed-only"), ("NaN", "indexed-only"),
    // Match-case wildcard binder (term.rs), not an operator
    ("_", "pattern-binder"),
    // Constant-array qualified identifier: declarable (CLEARSY benchmarks do);
    // its qualified.rs arm defers to the declared symbol (see doc above).
    ("const", "declared-shadowed"),
    // Declaration-activated collection theory ops (see doc comment above):
    // deductive-checks declares these to trigger the native solver; misuse fails
    // closed (probed).
    ("set.subset", "declaration-activated"),
    ("map.dom", "declaration-activated"),
    ("map.subset", "declaration-activated"),
    ("multiset.subset", "declaration-activated"),
];

/// Check whether `name` is an elaborator-recognized operator name that is
/// deliberately kept user-declarable (see [`EXCLUDED_DECLARABLE_OP_NAMES`]).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn is_excluded_declarable_op_name(name: &str) -> bool {
    EXCLUDED_DECLARABLE_OP_NAMES
        .iter()
        .any(|&(op, _)| op == name)
}

/// Check whether `name` is a declaration-activated collection predicate (the
/// `"declaration-activated"` rows of [`EXCLUDED_DECLARABLE_OP_NAMES`]): a name
/// whose `declare-fun` at the native collection signature is the documented
/// activation route for AY's native set/map/multiset solvers, and which is
/// rejected in every other declaration context (wrong signature,
/// `declare-const`, `define-fun`, datatype ctor/selector/tester).
pub(crate) fn is_declaration_activated_op_name(name: &str) -> bool {
    EXCLUDED_DECLARABLE_OP_NAMES
        .iter()
        .any(|&(op, reason)| reason == "declaration-activated" && op == name)
}

/// Signature gate for the declaration-activated collection predicates: a
/// `declare-fun` of one of these names is accepted ONLY at the native
/// collection shape it activates —
///   * `set.subset` / `map.subset` / `multiset.subset`:
///     `((Array …) (Array …)) -> Bool` (two collection carriers to Bool);
///   * `map.dom`: `((Array …)) -> (Array …)` (map carrier to domain-set
///     carrier).
///
/// This is exactly the shape deductive-checks's encoder declares
/// (`Set<T>`/`Multiset<T>`/`Map<K,V>` carriers are all `Sort::Array`). Any
/// other signature — e.g. the probed `(declare-fun set.subset (Int Int)
/// Bool)`, which previously reached the native subset rule and answered a
/// definitive `unsat` via ground-identity reflexivity — is rejected
/// fail-closed at elaboration.
///
/// The carriers must also share their INDEX sort (the collection element/key
/// sort): the native subset rule instantiates one shared element variable
/// across both carriers, so a mixed-index declaration like `(declare-fun
/// set.subset ((Array Int Bool) (Array Bool Bool)) Bool)` previously reached
/// ay-core's `mk_select` with a mismatched index sort and PANICKED
/// (user-triggerable crash, `array.rs` "mk_select index sort mismatch");
/// likewise `map.dom`'s domain-set result must be indexed by the map's key
/// sort. Rejected fail-closed here instead.
pub(crate) fn declaration_activated_signature_ok(
    name: &str,
    arg_sorts: &[Sort],
    ret_sort: &Sort,
) -> bool {
    let index_of = |s: &Sort| match s {
        Sort::Array(arr) => Some(arr.index_sort.clone()),
        _ => None,
    };
    match name {
        "set.subset" | "map.subset" | "multiset.subset" => {
            arg_sorts.len() == 2
                && matches!(ret_sort, Sort::Bool)
                && match (index_of(&arg_sorts[0]), index_of(&arg_sorts[1])) {
                    (Some(i0), Some(i1)) => i0 == i1,
                    _ => false,
                }
        }
        "map.dom" => {
            arg_sorts.len() == 1
                && match (index_of(&arg_sorts[0]), index_of(ret_sort)) {
                    (Some(key), Some(dom_key)) => key == dom_key,
                    _ => false,
                }
        }
        _ => false,
    }
}

/// Check if a symbol name is reserved: it uses the internal `__ay_` prefix, it
/// is a builtin theory-operator name AY matches structurally (see
/// [`RESERVED_OP_NAMES`]), or it is a declaration-activated collection
/// predicate (see [`is_declaration_activated_op_name`]). Reserved names cannot
/// be `declare`d/`define`d by user input; doing so is rejected with
/// [`ElaborateError::ReservedSymbol`]. Sole exception: `declare_fun` admits a
/// declaration-activated name at its native collection signature — the
/// documented activation route for the native collection solvers (it
/// special-cases BEFORE this check; see `Context::declare_fun`).
pub fn is_reserved_symbol(name: &str) -> bool {
    name.starts_with(INTERNAL_SYMBOL_PREFIX)
        || is_reserved_op_name(name)
        || is_declaration_activated_op_name(name)
}

/// Error during elaboration
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum ElaborateError {
    /// Undefined symbol
    #[error("undefined symbol: {0}")]
    UndefinedSymbol(String),
    /// Sort mismatch
    #[error("sort mismatch: expected {expected}, got {actual}")]
    SortMismatch {
        /// The expected sort
        expected: String,
        /// The actual sort found
        actual: String,
    },
    /// Invalid constant
    #[error("invalid constant: {0}")]
    InvalidConstant(String),
    /// A declaration or definition collides with an existing symbol under
    /// SMT-LIB/z3's signature and namespace rules.
    #[error("{0}")]
    Redefinition(String),
    /// z3 accepts this name as an overload, but AY's definition expansion is
    /// keyed only by surface name and cannot preserve both meanings soundly.
    #[error(
        "symbol '{0}' uses a definition overload that this frontend cannot represent without conflating signatures"
    )]
    UnrepresentableOverload(String),
    /// Unsupported feature
    #[error("unsupported: {0}")]
    Unsupported(String),
    /// Reserved symbol: either the internal `__ay_` prefix or a builtin
    /// theory-operator name that AY matches structurally (see
    /// [`RESERVED_OP_NAMES`]). Declaring such a name would silently conflate the
    /// forged symbol with the builtin operator, so it is rejected.
    #[error(
        "symbol '{0}' is reserved (internal '{INTERNAL_SYMBOL_PREFIX}' prefix or builtin \
         theory-operator name) and cannot be declared"
    )]
    ReservedSymbol(String),
    /// Declaration of a symbol whose name is a registered datatype
    /// constructor/selector/tester. The DT theory matches these operations
    /// structurally by name, so a same-named user declaration would be
    /// silently conflated with the builtin datatype operation (a confirmed
    /// wrong-UNSAT class: post-hoc `declare-fun is-Cons`/`hd` forgeries);
    /// it is rejected instead. (The programmatic ay-dpll API separately
    /// ADOPTS an identical-signature redeclaration as a handle to the
    /// registered member — the documented embedder contract — without going
    /// through this error; see `Solver::try_declare_fun`.)
    #[error(
        "symbol '{0}' is already a datatype constructor/selector/tester; \
         declaring it would conflate the user symbol with the builtin datatype \
         operation"
    )]
    DatatypeMemberCollision(String),
    /// A `declare-datatype`/`declare-datatypes` re-uses an already-declared
    /// sort name. Re-declaring an existing sort as a datatype is malformed
    /// SMT-LIB and is the only way a pre-existing user symbol can mention the
    /// datatype's carrier sort — after which the DT theory captures that
    /// symbol's applications as constructor/selector/tester operations (a
    /// confirmed wrong-UNSAT class: `declare-sort Lst` + `declare-fun hd (Lst)
    /// Int` + use + `declare-datatype Lst ((Cons (hd Int)) …)`).
    #[error(
        "sort '{0}' is already declared; re-declaring it as a datatype would \
         conflate existing symbols over the old sort with the new datatype's \
         members"
    )]
    SortRedeclaration(String),
    /// Scope underflow (pop with no matching push)
    #[error("scope underflow: pop called with no matching push")]
    ScopeUnderflow,
    /// Recursion depth exceeded during define-fun-rec expansion
    #[error("recursion depth limit ({0}) exceeded during function expansion")]
    RecursionDepthExceeded(usize),
    /// A pre-rendered ill-sorted-application error whose payload is the exact
    /// z3 4.15.4 message text (e.g. the `ite` argument-#1 sort mismatch:
    /// `Sort mismatch at argument #1 for function (declare-fun ite (Bool T T)
    /// T) supplied sort is C`). Carried verbatim so the CLI reproduces z3's
    /// wording via the generic elaboration-error rendering path.
    #[error("{0}")]
    IllSorted(String),
}

/// Result type for elaboration
pub(crate) type Result<T> = std::result::Result<T, ElaborateError>;

/// Symbol information
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct SymbolInfo {
    /// The term ID if it's a constant
    pub term: Option<TermId>,
    /// The sort of the symbol
    pub sort: Sort,
    /// Argument sorts (empty for constants)
    pub arg_sorts: Vec<Sort>,
    /// Instance-specific INTERNAL symbol name to use when building the term,
    /// when it differs from the user-facing surface name. This is set for
    /// monomorphized parametric-datatype members and for every ordinary
    /// declaration after the first overload of a surface name. The term then
    /// carries a name-disjoint symbol, preventing distinct SMT-LIB signatures
    /// from collapsing onto one core UF identity. The first ordinary
    /// declaration keeps `None`, preserving its historical surface identity.
    pub internal_name: Option<String>,
}

/// Optimization direction for an objective term
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ObjectiveDirection {
    /// Maximize the objective
    Maximize,
    /// Minimize the objective
    Minimize,
}

/// An optimization objective
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Objective {
    /// Whether to maximize or minimize
    pub direction: ObjectiveDirection,
    /// The objective term
    pub term: TermId,
}

/// A soft (weighted) constraint from `(assert-soft ...)`.
///
/// A soft assertion is *not* a hard assertion: the solver may leave it
/// violated. At `check-sat` the solver minimizes the total `weight` of
/// violated soft assertions subject to the hard assertions (Weighted Partial
/// MaxSMT).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SoftAssertion {
    /// The elaborated Boolean term that should ideally be satisfied.
    pub term: TermId,
    /// Penalty incurred when the term is violated (default 1).
    pub weight: u64,
    /// Optional group label (`:id`).
    pub id: Option<String>,
}

/// Maximum recursion depth for define-fun-rec expansion (#8622).
/// Prevents unbounded stack/heap growth from mutually recursive definitions.
const MAX_FUN_EXPANSION_DEPTH: usize = 1000;

const OPTION_GLOBAL_DECLARATIONS: &str = "global-declarations";
const OPTION_GLOBAL_DECLS: &str = "global-decls";

type FunctionDefinition = (Vec<(String, Sort)>, Sort, ParsedTerm);

/// Elaboration context
// Trust: `Clone` lets an independent UNSAT re-discharge rebuild a fresh `Executor`
// over a COPY of the full solving context (terms, assertions, logic, options) — the
// same setup the main solve used — so the complete solve path re-decides deep
// nested-ite obligations that a thin re-translate leaves Unknown.
#[derive(Clone)]
pub struct Context {
    /// The term store
    pub terms: TermStore,
    /// Symbol table: name -> info
    symbols: HashMap<String, SymbolInfo>,
    /// Names in `symbols` that are SOLVER-INTERNAL, not user-declared: the
    /// fresh field constants introduced by the eager single-constructor
    /// datatype elimination (`v!field`, see `build_const_term`). They must be
    /// solvable and `get-value`-resolvable, but `(get-model)` must NOT print
    /// them: model validators treat definitions of undeclared names as
    /// errors/garbage (observed: the pinned SMT-COMP 2025 Dolmen silently stops
    /// reading the model at the first one, orphaning every later user symbol).
    /// A user (re)declaration of the same name always removes it from this set
    /// — suppression may never hit a user-DECLARED symbol
    /// (#mv-internal-symbol-suppression).
    internal_symbols: ay_core::kani_compat::DetHashSet<String>,
    /// Overloaded declared symbols keyed by surface name.
    ///
    /// Datatype selectors may legally reuse the same surface name across
    /// different datatypes, so elaboration must resolve them by argument sort.
    overloaded_symbols: HashMap<String, Vec<SymbolInfo>>,
    /// Monotonic source of collision-proof identities for ordinary overloads.
    /// Never rewound by `pop`: an internal name cannot be reused while an old
    /// term bearing it may still exist in the term store.
    next_overload_identity: u64,
    /// Sort definitions: name -> sort
    sort_defs: HashMap<String, Sort>,
    /// Parameterized sort synonyms (`(define-sort Name (T..) body)`, arity > 0):
    /// name -> (type-parameter names, un-elaborated body template). Kept as a
    /// template (not eagerly elaborated) so each ground use `(Name A1 .. An)`
    /// can substitute the parameters and elaborate the body — see
    /// `elaborate/sorts.rs`. The 0-arity case stays in `sort_defs`.
    parametric_sort_defs: HashMap<String, (Vec<String>, crate::command::Sort)>,
    /// Names of parameterized sort synonyms currently mid-expansion. Guards
    /// against a self- or mutually-recursive `define-sort` (malformed per
    /// SMT-LIB; z3 rejects it as an unknown sort) infinite-looping the lazy
    /// template expansion — re-entry errors instead of overflowing the stack.
    expanding_sort_synonyms: Vec<String>,
    /// Function definitions: name -> (params, body)
    /// Macro/recursive definitions keyed by surface name. The declared result
    /// sort travels with the body so expansion never consults a later
    /// overloaded symbol-table entry for its type.
    fun_defs: HashMap<String, FunctionDefinition>,
    /// #quantprod-g3: DECLARED functions adopted as macros from a
    /// definitional forall `(assert (forall X. (= (f X) body)))` with `f`
    /// not (transitively) in `body` and not used by any earlier assertion:
    /// name -> (elaborated binder list, elaborated definition body), kept for
    /// `(get-model)` emission (`(define-fun f (X) S body)` — the z3-parity
    /// model entry; the constraint itself becomes a reflexive tautology once
    /// the macro expands every application). Adoption is restricted to the
    /// OUTERMOST scope so `pop` can never remove the justifying assertion
    /// while the macro lives on; `reset-assertions` un-adopts explicitly.
    adopted_macro_interps: HashMap<String, (Vec<(String, Sort)>, TermId)>,
    /// Test-only fault injection for the transaction boundary between macro
    /// adoption and assertion re-elaboration.
    #[cfg(test)]
    fail_next_assert_after_macro_adoption: bool,
    /// Names bound by `define-fun-rec` / `define-funs-rec` (a strict subset of
    /// `fun_defs`, which also holds plain `define-fun` macros). z3 treats a
    /// recursive-function declaration and a plain macro differently for
    /// redefinition/overload collision (the `recfun` plugin lives in a distinct
    /// namespace): a `declare-*` never collides with a prior recursive function,
    /// and a `define-fun-rec` never collides with a prior `declare-*`. Tracking
    /// recfun-ness separately lets [`Context::redefinition_error`] reproduce
    /// z3 4.15.4's exact accept/reject matrix (#P0.3).
    recursive_fun_names: ay_core::kani_compat::DetHashSet<String>,
    /// Datatype definitions: dt_name -> constructor_names
    datatypes: HashMap<String, Vec<String>>,
    /// The full monomorphic declaration behind each `datatypes` entry, retained
    /// so an EXACTLY-identical re-declaration can be adopted as a no-op
    /// (`declare_datatype`), mirroring `try_declare_fun`'s adopt-identical
    /// embedder contract. Only an exact `DatatypeDec` match is adopted; a
    /// plain-sort redeclaration (the wrong-UNSAT class) or a DIFFERENT datatype
    /// of the same name still hits `check_datatype_sort_redeclaration`.
    monomorphic_datatype_decs: HashMap<String, crate::command::DatatypeDec>,
    /// Constructor to datatype map: ctor_name -> (dt_name, ctor_name)
    constructors: HashMap<String, (String, String)>,
    /// Constructor to selectors map: ctor_name -> selector_names (positional)
    ctor_selectors: HashMap<String, Vec<String>>,
    /// Constructor to selector metadata (name + return sort) in declaration order.
    ctor_selector_info: HashMap<String, Vec<(String, Sort)>>,
    /// Nullary constructor internal name -> its bound constant term.
    ///
    /// A nullary datatype constructor (`nil`) elaborates to a named VARIABLE
    /// term (`mk_fresh_named_var`, see `datatypes.rs`), not a 0-ary `App`, so
    /// constructor-shape checks that match on `TermData::App` miss it. This map
    /// records the exact `TermId` bound to each nullary constructor so folds
    /// (tester-over-constructor, `ctor_of_term`) can recognize it TermId-EXACTLY
    /// — a binder that shadows the constructor name binds a different term and
    /// can never fold unsoundly. (#rec-dt-expansion)
    nullary_ctor_terms: HashMap<String, TermId>,
    /// Parametric (polymorphic) datatype templates: dt_name -> declaration.
    ///
    /// A `(declare-datatypes ((Name n)) ((par (T..) ..)))` with arity `n > 0`
    /// is stored here instead of being eagerly registered. Each ground use
    /// `(Name A1 .. An)` is lazily monomorphized into a fresh instance sort and
    /// its constructors/selectors/testers (see `elaborate/datatypes.rs`).
    parametric_datatypes: HashMap<String, crate::command::DatatypeDec>,
    /// Reverse map for a registered parametric instance: mangled instance sort
    /// name -> (template name, type arguments). Lets constructor-application
    /// instance inference recover the type arguments of a nested instance sort
    /// (e.g. unify the template field `(Lst T)` against an argument of sort
    /// `Lst!{Int}` to learn `T = Int`).
    parametric_instance_args: HashMap<String, (String, Vec<Sort>)>,
    /// Internal term symbol name -> user-facing surface name. Covers both
    /// instance-mangled datatype members and ordinary declaration overloads,
    /// so serialization/model output never leaks private identities.
    dt_internal_surface: HashMap<String, String>,
    /// Current logic
    logic: Option<String>,
    /// Assertions (internal normalized form)
    pub assertions: Vec<TermId>,
    /// Assertions in their original parsed form (before internal normalization)
    ///
    /// This is used to align exported proofs with the surface syntax of the input file.
    /// For example, AY internally canonicalizes `(>= a b)` into `(<= b a)` for hashing
    /// and solver simplicity, but proof checkers match `assume` steps against the
    /// original problem premises.
    assertions_parsed: Vec<ParsedTerm>,
    /// Whether `assert` retains the original parsed AST in `assertions_parsed`.
    ///
    /// Defaults to `true` (library behavior unchanged). The CLI turns this OFF
    /// when proof emission is impossible for the session (`--no-proof`,
    /// `--z3-mode`, competition mode): the parsed AST exists ONLY to align
    /// exported proofs with surface syntax, and retaining a deep clone of every
    /// assertion dominated peak RSS on large parse-heavy inputs (~190 MB of a
    /// 318 MB peak on a 6 MB QF_UF instance — #rss-vs-z3 campaign). A later
    /// `(set-option :produce-proofs true)` flips retention back ON.
    ///
    /// INVARIANT (prefix alignment): `assertions_parsed` is always an exact
    /// parallel copy of `assertions[..assertions_parsed.len()]`. Pushes are
    /// guarded on the stacks being fully aligned, so once one parsed term is
    /// skipped, no later one is retained — a shorter-than-`assertions` parsed
    /// stack is always a correct PREFIX, which is exactly what the proof
    /// surface-alignment consumers assume (they fall back to canonical terms
    /// for anything past the prefix, or skip alignment when it is empty).
    retain_parsed_assertions: bool,
    /// Optimization objectives (from maximize/minimize)
    objectives: Vec<Objective>,
    /// Soft (weighted) constraints from `(assert-soft ...)`
    soft_constraints: Vec<SoftAssertion>,
    /// Scope stack for push/pop
    scopes: Vec<ScopeFrame>,
    /// Internal one-command override for native solver declarations whose
    /// handles outlive SMT-LIB assertion scopes. Kept separate from the public
    /// global-declarations option so native calls never mutate session options.
    native_global_declaration: bool,
    /// Solver options (keyword -> value)
    options: HashMap<String, OptionValue>,
    /// Named formulas: name -> term_id (for get-assignment and get-unsat-core)
    named_terms: HashMap<String, TermId>,
    /// Current depth of define-fun-rec expansion (#8622)
    fun_expansion_depth: usize,
    /// Set (only) while elaborating the direct function argument of a
    /// higher-order sequence combinator (`seq.foldl`/`seq.foldli`/`seq.map`/
    /// `seq.mapi` and their `fold_left*` aliases). A MULTI-variable lambda is
    /// elaborated as a curried nest of single-variable lambda-arrays, which is
    /// the shape `ho_unfold` consumes — but that curried encoding diverges from
    /// z3 in any OTHER position (z3 treats an n-ary lambda as an n-ary function,
    /// not a curried array). Left visible elsewhere it wrong-decides: a false
    /// `sat` on an equality between two 2-var lambda-arrays, and a spurious
    /// `unsat` on a direct 2-arg `(select (select f i) j)` chain that z3 rejects
    /// as ill-sorted. So multi-var currying is permitted ONLY when this flag is
    /// set; every other multi-var lambda fails closed to `unknown` (as the
    /// pre-P1.5 code did). (#p1.5-curried-lambda-gate)
    multivar_lambda_curry_allowed: bool,
    /// Set when a `multiset.*` operator is elaborated. The `(Multiset T)` carrier
    /// is erased to `Array(T -> Int)`, so logic detection cannot otherwise tell a
    /// multiset-count formula from a plain int-array one and would route it to
    /// the generic array/LIA solver, which misses the `count >= 0` invariant
    /// (a wrong SAT for e.g. `multiset.count = -1`). This flag forces the
    /// dedicated QF_MSLIA route under `(set-logic ALL)` (#multiset-routing).
    uses_multiset: bool,
    /// Set when a `set.*` operator is elaborated. The `(Set T)` carrier is erased
    /// to `Array(T -> Bool)`, so — exactly like `uses_multiset` — logic detection
    /// cannot otherwise tell a set formula from a plain bool-array one and would
    /// route it to the generic array solver, which misses the set cardinality /
    /// membership / subset invariants (a wrong SAT for e.g. `set.card(singleton)=0`
    /// or `subset(A, empty) ∧ member(x, A)`). Forces the dedicated QF_SETLIA route
    /// even under a mismatched declared logic (#set-routing).
    uses_set: bool,
    /// Memoized predicates realizing Z3's special-relations family
    /// (`(_ partial-order N)`, `(_ linear-order N)`, `(_ tree-order N)`,
    /// `(_ piecewise-linear-order N)`), keyed by `(kind, sort, index)`. Every use
    /// of the same indexed relation over the same sort must resolve to the SAME
    /// uninterpreted predicate so its injected order axioms are shared — this is
    /// what Verus relies on when its `height_lt` definition and every decreases
    /// check both name `(_ partial-order 0)`. Not scope-truncated directly; a
    /// `pop` that removes the predicate symbol (and truncates its axioms) is
    /// detected by the `symbols.contains_key` guard at reuse, which forces a
    /// sound re-declaration in the surviving scope.
    special_relations: HashMap<(String, String, String), String>,
    /// When set, `=`/`distinct`/`ite` operand sort-checking is RELAXED to the
    /// legacy lenient behavior: mismatched BitVec widths in `=`/`distinct` are
    /// zero-extended (#5115, the MCMPC family) and other non-coercible sort
    /// mismatches fall through instead of erroring. Default `false` — AY then
    /// matches z3 4.15.4, which rejects every such ill-sorted term as a sort
    /// error (the coercible set is exactly {Bool, Int, Real}). Opt-in only
    /// (`set_lenient_sort_coercions`), e.g. for the #5115 zero-extension tests.
    lenient_sort_coercions: bool,
}

/// Value for a solver option
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum OptionValue {
    /// Boolean option
    Bool(bool),
    /// String option
    String(String),
    /// Numeric option
    Numeral(String),
}

/// A scope frame for push/pop
#[derive(Debug, Clone, Default)]
struct ScopeFrame {
    /// Lazily captured pre-scope state for every symbol name changed here.
    /// Restoring snapshots (rather than deleting by surface name) preserves an
    /// outer declaration when an overload of the same name is scoped.
    symbols: HashMap<String, ScopedSymbolState>,
    /// Number of assertions before this scope
    assertion_count: usize,
    /// Number of objectives before this scope
    objective_count: usize,
    /// Number of soft constraints before this scope
    soft_constraint_count: usize,
    /// Named terms defined in this scope
    named_terms: Vec<String>,
    /// Datatypes defined in this scope
    datatypes: Vec<String>,
    /// Constructors defined in this scope
    constructors: Vec<String>,
    /// Sort definitions in this scope
    sort_defs: Vec<String>,
    /// Function definitions in this scope (#8621)
    fun_defs: Vec<String>,
    /// Parametric datatype templates declared in this scope
    parametric_datatypes: Vec<String>,
}

#[derive(Debug, Clone)]
struct ScopedSymbolState {
    name: String,
    primary: Option<SymbolInfo>,
    overloads: Option<Vec<SymbolInfo>>,
    was_internal: bool,
}

impl Default for Context {
    fn default() -> Self {
        Self::new()
    }
}

impl Context {
    /// Iterate declared symbols (name -> info). Used by problem-dump
    /// debugging facilities (e.g. the LIA eager-probe benchmark extractor).
    pub fn symbols_iter(&self) -> impl Iterator<Item = (&String, &SymbolInfo)> {
        self.symbol_iter()
    }

    /// Whether a declared symbol named `name` exists with EXACTLY this
    /// signature (argument sorts and result sort), considering overloads.
    ///
    /// Used by the programmatic ay-dpll API to ADOPT an identical-signature
    /// redeclaration of a datatype constructor/selector/tester as a handle to
    /// the registered member (the documented embedder contract, relied on by
    /// deductive-checks's encoder) instead of tripping the
    /// [`ElaborateError::DatatypeMemberCollision`] gate that protects the
    /// SMT-LIB text path.
    pub fn has_symbol_with_signature(
        &self,
        name: &str,
        arg_sorts: &[Sort],
        ret_sort: &Sort,
    ) -> bool {
        let sig_matches = |info: &SymbolInfo| info.arg_sorts == arg_sorts && &info.sort == ret_sort;
        if self.symbols.get(name).is_some_and(sig_matches) {
            return true;
        }
        self.overloaded_symbols
            .get(name)
            .is_some_and(|overloads| overloads.iter().any(sig_matches))
    }

    /// Whether a declared symbol named `name` exists with EXACTLY this argument
    /// domain, IGNORING its result sort. z3 keys a `define-fun` macro (a "named
    /// expression") by name + domain only — two macros of the same name and
    /// domain but different result sorts still collide (`named expression
    /// already defined`), unlike `declare-*` which overloads on the full
    /// signature. Used by [`Context::redefinition_error`] for the
    /// macro-on-the-existing-side collision rule (#P0.3).
    pub fn has_symbol_with_domain(&self, name: &str, arg_sorts: &[Sort]) -> bool {
        let dom_matches = |info: &SymbolInfo| info.arg_sorts == arg_sorts;
        if self.symbols.get(name).is_some_and(dom_matches) {
            return true;
        }
        self.overloaded_symbols
            .get(name)
            .is_some_and(|overloads| overloads.iter().any(dom_matches))
    }

    /// Create a new elaboration context
    pub fn new() -> Self {
        let mut options = HashMap::default();
        // Default options per SMT-LIB 2.6 standard
        options.insert("print-success".to_string(), OptionValue::Bool(false));
        options.insert("produce-models".to_string(), OptionValue::Bool(true));
        options.insert("produce-unsat-cores".to_string(), OptionValue::Bool(false));
        options.insert("produce-proofs".to_string(), OptionValue::Bool(false));
        options.insert("produce-assignments".to_string(), OptionValue::Bool(false));
        options.insert(
            OPTION_GLOBAL_DECLARATIONS.to_string(),
            OptionValue::Bool(false),
        );
        options.insert(OPTION_GLOBAL_DECLS.to_string(), OptionValue::Bool(false));
        options.insert(
            "random-seed".to_string(),
            OptionValue::Numeral("0".to_string()),
        );

        Self {
            terms: TermStore::new(),
            symbols: HashMap::default(),
            internal_symbols: ay_core::kani_compat::DetHashSet::default(),
            overloaded_symbols: HashMap::default(),
            next_overload_identity: 0,
            sort_defs: HashMap::default(),
            parametric_sort_defs: HashMap::default(),
            expanding_sort_synonyms: Vec::new(),
            fun_defs: HashMap::default(),
            adopted_macro_interps: HashMap::default(),
            #[cfg(test)]
            fail_next_assert_after_macro_adoption: false,
            recursive_fun_names: ay_core::kani_compat::DetHashSet::default(),
            datatypes: HashMap::default(),
            monomorphic_datatype_decs: HashMap::default(),
            constructors: HashMap::default(),
            ctor_selectors: HashMap::default(),
            ctor_selector_info: HashMap::default(),
            nullary_ctor_terms: HashMap::default(),
            parametric_datatypes: HashMap::default(),
            parametric_instance_args: HashMap::default(),
            dt_internal_surface: HashMap::default(),
            logic: None,
            assertions: Vec::new(),
            assertions_parsed: Vec::new(),
            retain_parsed_assertions: true,
            objectives: Vec::new(),
            soft_constraints: Vec::new(),
            scopes: Vec::new(),
            native_global_declaration: false,
            options,
            named_terms: HashMap::default(),
            fun_expansion_depth: 0,
            multivar_lambda_curry_allowed: false,
            uses_multiset: false,
            uses_set: false,
            special_relations: HashMap::default(),
            lenient_sort_coercions: false,
        }
    }

    /// Enable/disable the legacy lenient `=`/`distinct`/`ite` sort coercions
    /// (default off — z3 4.15.4 parity, which rejects ill-sorted operands).
    /// Enabling restores the #5115 BitVec-width zero-extension leniency.
    pub fn set_lenient_sort_coercions(&mut self, lenient: bool) {
        self.lenient_sort_coercions = lenient;
    }

    /// Whether legacy lenient sort coercions are enabled (see
    /// [`set_lenient_sort_coercions`](Self::set_lenient_sort_coercions)).
    pub fn lenient_sort_coercions(&self) -> bool {
        self.lenient_sort_coercions
    }

    /// Whether the elaborated problem uses any `multiset.*` operator.
    pub fn uses_multiset(&self) -> bool {
        self.uses_multiset
    }

    /// Record that a `multiset.*` operator was elaborated.
    pub(crate) fn mark_uses_multiset(&mut self) {
        self.uses_multiset = true;
    }

    /// Whether the elaborated problem uses any `set.*` operator.
    pub fn uses_set(&self) -> bool {
        self.uses_set
    }

    /// Record that a `set.*` operator was elaborated.
    pub(crate) fn mark_uses_set(&mut self) {
        self.uses_set = true;
    }

    /// Get the current logic setting.
    pub fn logic(&self) -> Option<&str> {
        self.logic.as_deref()
    }

    /// Return the current push/pop scope depth.
    #[must_use]
    pub fn scope_depth(&self) -> usize {
        self.scopes.len()
    }

    /// Set the logic for this context.
    pub fn set_logic(&mut self, logic: String) {
        self.logic = Some(logic);
    }

    /// Get the parsed assertions (original surface syntax).
    pub fn assertions_parsed(&self) -> &[ParsedTerm] {
        &self.assertions_parsed
    }

    /// Nullary (`()`-parameter) `define-fun` macro bodies as `(name, body)`
    /// pairs, in arbitrary order. `assertions_parsed()` retains the ORIGINAL
    /// surface syntax with such macros UNEXPANDED (e.g. `(select fwd i0)` where
    /// `fwd` is a `define-fun`), so a proof/lean-export consumer that needs the
    /// expanded structure can substitute these definitionally-equal bodies. Only
    /// parameter-less macros are returned — a macro with parameters would require
    /// beta-reduction at each application, which the surface-syntax consumers do
    /// not perform. This is a diagnostic export surface; it does not affect the
    /// solver's own (already fully-elaborated) reasoning.
    pub fn nullary_defined_terms(&self) -> Vec<(String, ParsedTerm)> {
        self.fun_defs
            .iter()
            .filter(|(_, (params, _, _))| params.is_empty())
            .map(|(name, (_, _, body))| (name.clone(), body.clone()))
            .collect()
    }

    /// Re-elaborate a parsed (surface-syntax) subterm into the term store.
    ///
    /// Used by proof export to map a surface subterm of an assertion back to
    /// its hash-consed canonical `TermId` (elaboration is deterministic, so a
    /// closed subterm re-elaborates to the exact term it produced when the
    /// assertion was first asserted). The caller must only pass subterms that
    /// are closed (no binder-bound variables) — anything else returns the
    /// wrong term or an error. Errors are reported as `None`: this is a
    /// best-effort provenance query, never a solving path.
    pub fn elaborate_surface_subterm(&mut self, term: &ParsedTerm) -> Option<TermId> {
        let env = HashMap::default();
        self.elaborate_term(term, &env).ok()
    }

    /// Re-elaborate a parsed proof-surface subterm under an existing binder.
    ///
    /// Proof export normally re-elaborates only closed subterms.  A certified
    /// quantifier step also needs the authored spelling of the quantified body
    /// and its immediate subterms, whose surface variable names are scoped by
    /// the quantifier.  The caller supplies the exact surface-name to canonical
    /// `TermId` environment recovered from that already-elaborated binder; this
    /// method creates no fresh variables and remains a best-effort provenance
    /// query.  Errors are reported as `None`, exactly like the closed helper.
    pub fn elaborate_surface_subterm_with_bindings(
        &mut self,
        term: &ParsedTerm,
        bindings: &[(String, TermId)],
    ) -> Option<TermId> {
        let env: HashMap<String, TermId> = bindings.iter().cloned().collect();
        self.elaborate_term(term, &env).ok()
    }

    /// Return the minimum active SMT scope depth for each asserted term.
    ///
    /// Depth `0` is the global scope. If the same assertion term is present in
    /// multiple active scopes, the shallowest active depth wins because that is
    /// the scope where its activation must survive after pop().
    pub fn active_assertion_min_scope_depths(&self) -> HashMap<TermId, usize> {
        let mut depths = HashMap::default();
        let mut scope_boundaries: Vec<usize> = self
            .scopes
            .iter()
            .map(|frame| frame.assertion_count)
            .collect();
        scope_boundaries.push(self.assertions.len());

        let mut depth = 0usize;
        let mut next_boundary_idx = 0usize;
        let mut next_boundary = scope_boundaries
            .get(next_boundary_idx)
            .copied()
            .unwrap_or(self.assertions.len());

        for (idx, &assertion) in self.assertions.iter().enumerate() {
            while idx >= next_boundary && next_boundary_idx + 1 < scope_boundaries.len() {
                depth += 1;
                next_boundary_idx += 1;
                next_boundary = scope_boundaries[next_boundary_idx];
            }
            depths
                .entry(assertion)
                .and_modify(|existing: &mut usize| *existing = (*existing).min(depth))
                .or_insert(depth);
        }

        depths
    }

    /// Push an assertion and its parsed form together, keeping them aligned.
    ///
    /// The parsed form is retained only under the retention policy — see
    /// [`Self::set_retain_parsed_assertions`] and the `retain_parsed_assertions`
    /// field docs (prefix-alignment invariant).
    pub fn add_assertion_with_parsed(&mut self, term: TermId, parsed: ParsedTerm) {
        if self.retain_parsed_assertions && self.assertions_parsed.len() == self.assertions.len() {
            self.assertions_parsed.push(parsed);
        }
        self.assertions.push(term);
    }

    /// Configure whether `assert` retains original parsed ASTs for proof
    /// surface-syntax alignment (see the `retain_parsed_assertions` field docs).
    ///
    /// Turning retention OFF is a pure memory optimization: every consumer of
    /// `assertions_parsed` is a proof/lean export path that degrades gracefully
    /// on a short or empty parsed stack. `(set-option :produce-proofs true)`
    /// forces retention back ON from that point.
    pub fn set_retain_parsed_assertions(&mut self, retain: bool) {
        self.retain_parsed_assertions = retain;
    }

    /// Get the optimization objectives.
    pub fn objectives(&self) -> &[Objective] {
        &self.objectives
    }

    /// Add an optimization objective.
    pub fn add_objective(&mut self, objective: Objective) {
        self.objectives.push(objective);
    }

    /// Get the soft (weighted) constraints from `(assert-soft ...)`.
    pub fn soft_constraints(&self) -> &[SoftAssertion] {
        &self.soft_constraints
    }

    /// Add a soft (weighted) constraint.
    pub(crate) fn add_soft_constraint(&mut self, soft: SoftAssertion) {
        self.soft_constraints.push(soft);
    }

    /// Atomically replace the active soft-constraint set, returning the prior
    /// set to the caller.
    ///
    /// This is the transaction primitive used when a native API owns soft
    /// constraints outside the parsed SMT-LIB context: install the native set,
    /// run one MaxSMT query, then restore the parsed set on every exit. Hard
    /// assertions, parsed-assertion alignment, scopes, and symbols are untouched.
    pub fn replace_soft_constraints(
        &mut self,
        soft_constraints: Vec<SoftAssertion>,
    ) -> Vec<SoftAssertion> {
        std::mem::replace(&mut self.soft_constraints, soft_constraints)
    }

    pub(crate) fn global_declarations_enabled(&self) -> bool {
        self.native_global_declaration
            || matches!(
                self.get_option(OPTION_GLOBAL_DECLARATIONS)
                    .or_else(|| self.get_option(OPTION_GLOBAL_DECLS)),
                Some(OptionValue::Bool(true))
            )
    }

    /// Capture a symbol name's state before its first mutation in the current
    /// scope. Callers must invoke this before changing `symbols`,
    /// `overloaded_symbols`, or `internal_symbols` for `name`.
    pub(crate) fn track_scoped_symbol(&mut self, name: &str) {
        if self.global_declarations_enabled() {
            return;
        }
        let Some(frame) = self.scopes.last() else {
            return;
        };
        if frame.symbols.contains_key(name) {
            return;
        }
        let state = ScopedSymbolState {
            name: name.to_string(),
            primary: self.symbols.get(name).cloned(),
            overloads: self.overloaded_symbols.get(name).cloned(),
            was_internal: self.internal_symbols.contains(name),
        };
        if let Some(frame) = self.scopes.last_mut() {
            frame.symbols.insert(name.to_string(), state);
        }
    }

    pub(crate) fn track_scoped_datatype(&mut self, name: String) {
        if self.global_declarations_enabled() {
            return;
        }
        if let Some(frame) = self.scopes.last_mut() {
            frame.datatypes.push(name);
        }
    }

    pub(crate) fn track_scoped_constructor(&mut self, name: String) {
        if self.global_declarations_enabled() {
            return;
        }
        if let Some(frame) = self.scopes.last_mut() {
            frame.constructors.push(name);
        }
    }

    pub(crate) fn track_scoped_sort_def(&mut self, name: String) {
        if self.global_declarations_enabled() {
            return;
        }
        if let Some(frame) = self.scopes.last_mut() {
            frame.sort_defs.push(name);
        }
    }

    pub(crate) fn track_scoped_fun_def(&mut self, name: String) {
        if self.global_declarations_enabled() {
            return;
        }
        if let Some(frame) = self.scopes.last_mut() {
            frame.fun_defs.push(name);
        }
    }

    pub(crate) fn track_scoped_parametric(&mut self, name: String) {
        if self.global_declarations_enabled() {
            return;
        }
        if let Some(frame) = self.scopes.last_mut() {
            frame.parametric_datatypes.push(name);
        }
    }

    /// Record an internal term name and its user-facing surface name for
    /// serialization/model output.
    pub(crate) fn track_internal_surface(&mut self, internal: String, surface: String) {
        self.dt_internal_surface.insert(internal, surface);
    }

    /// Map an internal datatype-member or ordinary-overload name back to its
    /// user-facing surface name.
    pub fn dt_surface_name(&self, internal: &str) -> Option<&str> {
        self.dt_internal_surface.get(internal).map(String::as_str)
    }
}

/// Result of processing a command that requires action
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum CommandResult {
    /// Need to run check-sat
    CheckSat,
    /// Need to run check-sat with assumptions
    CheckSatAssuming(Vec<TermId>),
    /// Need to produce a model
    GetModel,
    /// Need to produce objective values (for maximize/minimize)
    GetObjectives,
    /// Need to produce dual (Farkas) optimality certificates
    /// (`get-objective-certificates`, AY extension #lra-opt-cert)
    GetObjectiveCertificates,
    /// Need to produce values for specific terms. Each entry pairs the term's
    /// ORIGINAL SMT-LIB text (echoed verbatim as the `(get-value ...)` key) with
    /// its elaborated `TermId` (evaluated against the model).
    GetValue(Vec<(String, TermId)>),
    /// Need to evaluate a single term and print its bare value (`eval`)
    Eval(TermId),
    /// Need to compute implied consequences (`get-consequences`).
    ///
    /// First field is the elaborated background assumptions, second is the list
    /// of candidate literals to test for entailment.
    GetConsequences(Vec<TermId>, Vec<TermId>),
    /// `(get-abduct <name> <goal>)`: synthesize an abduct C such that A∧C is
    /// SAT and A∧C ⇒ goal. First field is the abduct name, second the elaborated
    /// goal term; the executor performs validated synthesis (fail-closed to `none`).
    GetAbduct(String, TermId),
    /// Need to get solver info
    GetInfo(String),
    /// Need to get an option value
    GetOption(String),
    /// Need to get current assertions
    GetAssertions,
    /// Need to print a string (echo command)
    Echo(String),
    /// Need to get assignment of named formulas
    GetAssignment,
    /// Need to get unsatisfiable core
    GetUnsatCore,
    /// Need to get unsatisfiable core with Farkas coefficients (#8769)
    GetUnsatCoreWithFarkas,
    /// Need to get unsatisfiable assumptions (from check-sat-assuming)
    GetUnsatAssumptions,
    /// Need to get proof
    GetProof,
    /// Exit the solver
    Exit,
    /// Need to simplify a term
    Simplify(TermId),
    /// Need to apply a Z3-style tactic to the current goal and print the
    /// resulting goal(s). Carries the parsed tactic; the executor runs it over a
    /// snapshot of the assertions (never mutating the real stack) and formats the
    /// result. See [`Command::Apply`](crate::Command::Apply).
    Apply(crate::command::ApplyTactic),
}

mod app;
mod commands;
mod datatypes;
mod declarations;
pub use declarations::IntroKind;
mod indexed;
mod qualified;
mod sorts;
mod term;

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;
