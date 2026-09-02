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
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermStoreSnapshotStamp;
use ay_core::{Sort, TermId, TermStore};

mod provenance;

use provenance::ContextIdentity;
pub use provenance::{
    CheckedProjectionBinding, CheckedProjectionBindings, DeclarationId, DeclarationKind,
    ProjectionBindingRejection, ProjectionBindingRequest, SourceContextStamp,
};

/// The reserved prefix for internal AY symbols.
/// User declarations with this prefix are rejected.
pub(crate) const INTERNAL_SYMBOL_PREFIX: &str = "__ay_";

/// Which layer MINTS names in an AY-internal namespace (see
/// [`INTERNAL_NAMESPACES`]). Recorded per row so the table says WHY a shape is
/// dangerous, rather than leaving that to a comment somewhere else.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum InternalNamespaceMinter {
    /// Minted by the core elaborator as a PRIVATE core identity
    /// (`fresh_private_declaration_core_identity`,
    /// `allocate_nominal_sort_identity`). Never a declared surface name.
    CoreElaborator,
    /// Minted AND structurally matched by the core term layer itself
    /// (`TermStore::mk_array_map` / `TermStore::get_array_map`). It is built by
    /// interning a `TermData::App` directly, never by declaring a symbol.
    CoreTermLayer,
    /// Minted by the in-process embedder/adapter API — AY's Z3 C surface
    /// (`ay-ffi`) allocates `!ay.*` engine witnesses (`!ay.array-ext!<n>`,
    /// `!ay.z3-func!<n>`, …) and DECLARES them through the native
    /// `Solver::declare_const`/`try_declare_fun` API.
    EmbedderApi,
}

/// Which declaration routes refuse a namespace.
///
/// This is a SEPARATE axis from [`InternalNamespaceMinter`], deliberately. Who
/// mints a shape says how dangerous it is; which routes refuse it is also a
/// statement about which callers AY trusts, and the two do not always coincide
/// (see `map[...]`, whose row documents the difference and the residual hole it
/// leaves).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum InternalNamespaceScope {
    /// Refused on EVERY declaration route, including the in-process native
    /// `Solver` API and the C surface.
    EveryRoute,
    /// Refused to untrusted SMT-LIB SOURCE TEXT and to the C API, but NOT to
    /// the in-process native `Solver` API. Reserved for shapes whose native
    /// registration is an existing, exercised embedder contract.
    SourceTextAndCApi,
}

/// One AY-internal name namespace: a `prefix`/`suffix` shape that some AY layer
/// mints or structurally matches, and which therefore must not be capturable by
/// a user declaration.
#[derive(Clone, Copy, Debug)]
pub struct InternalNamespace {
    /// Required leading text of a name in this namespace.
    pub prefix: &'static str,
    /// Required trailing text (empty when the namespace is prefix-only).
    pub suffix: &'static str,
    /// The layer that mints names here.
    pub minter: InternalNamespaceMinter,
    /// Which declaration routes refuse this namespace.
    pub scope: InternalNamespaceScope,
    /// Human-readable reason, quoted verbatim in the rejection message.
    pub rationale: &'static str,
}

/// Every AY-internal name namespace, in ONE place.
///
/// SOUNDNESS: each of these shapes is minted or structurally matched by an AY
/// layer, so an ordinary user symbol that happens to have the shape is silently
/// conflated with the internal object.
///
/// * `map[<f>]` — `TermStore::get_array_map` treats ANY `App` named `map[<f>]`
///   as the array map of `<f>` and licenses the rewrite
///   `select(map[f](a..), i) → f(select(a, i)..)`. A user function declared
///   `|map[f]|` therefore acquires map semantics: MEASURED wrong verdict
///   (pinned z3 5.0.0 `sat`, AY `unsat`) for
///   `(declare-fun |map[f]| ((Array Int Int)) (Array Int Int))` asserted
///   against `(distinct (select b 0) (f (select a 0)))` — a false PROVE, the
///   cardinal soundness failure. The shape is RE-DERIVED from the matcher
///   (`starts_with("map[") && ends_with(']')`), not guessed, so a name like
///   `map[f` that the matcher does NOT capture stays declarable.
/// * `__ay_` — the elaborator's private core identities. A user declaration of
///   one aliases whichever internal binding already owns that spelling.
/// * `!ay.` — engine witnesses minted by the Z3 C surface. `Z3_mk_ext` mints
///   `!ay.array-ext!<n>` and axiomatizes it with
///   `a != b => select(a,k) != select(b,k)`; because
///   `Solver::try_declare_const` is idempotent at an identical sort, SMT-LIB
///   text that declared `|!ay.array-ext!0|` first would have that axiom
///   attached to ITS constant — an over-constraint, i.e. a sat→unsat channel.
///
/// SCOPE — `map[...]` is refused to SOURCE TEXT and to the C API, not to the
/// in-process native `Solver` API. That is where the measured false PROVE
/// lived, and the native route already has an exercised contract for
/// registering internal-looking names as ordinary uninterpreted functions
/// (`ay-dpll` `native_replay_prefers_registered_internal_looking_function_names`
/// declares `map[replay_user]` through `Solver::try_declare_fun` and requires
/// the replay path to honor the registration). The residual native-route hole
/// is REAL and deliberately left open here: a native caller that declares
/// `map[g]` at an ARRAY rank still hands `get_array_map` a term to claim.
/// Closing it needs the native declaration gate to become rank-aware (the
/// existing contract is only sound because that fixture's rank is
/// `(Int) -> Bool`, which can never be a `select` argument), which is a
/// separate change to `Solver::try_declare_fun`.
///
/// This table is the SINGLE SOURCE OF TRUTH shared by the core elaborator's
/// declaration gates and `ay-ffi`'s `reserved_name_error`; the FFI predicate
/// delegates here rather than re-spelling the shapes, so the two paths cannot
/// drift apart (regression-tested by
/// `test_ffi_and_core_internal_namespace_gates_agree` in `ay-ffi` and by
/// `test_internal_namespace_table_covers_every_ffi_minted_identity` here).
pub const INTERNAL_NAMESPACES: &[InternalNamespace] = &[
    InternalNamespace {
        prefix: INTERNAL_SYMBOL_PREFIX,
        suffix: "",
        minter: InternalNamespaceMinter::CoreElaborator,
        scope: InternalNamespaceScope::EveryRoute,
        rationale: "'__ay_*' names are the elaborator's private core identities",
    },
    InternalNamespace {
        prefix: "map[",
        suffix: "]",
        minter: InternalNamespaceMinter::CoreTermLayer,
        scope: InternalNamespaceScope::SourceTextAndCApi,
        rationale: "names of the form 'map[...]' denote the internal array-map \
                    operator and would silently change the formula's meaning",
    },
    InternalNamespace {
        prefix: "!ay.",
        suffix: "",
        minter: InternalNamespaceMinter::EmbedderApi,
        scope: InternalNamespaceScope::SourceTextAndCApi,
        rationale: "'!ay.*' names are internal engine witnesses",
    },
];

/// The internal namespace `name` falls into, if any (see
/// [`INTERNAL_NAMESPACES`]).
///
/// A name is in a namespace when it carries BOTH the prefix and the suffix and
/// is long enough to carry them disjointly — the same test the matcher that
/// owns the namespace performs.
#[must_use]
pub fn internal_namespace_of(name: &str) -> Option<&'static InternalNamespace> {
    INTERNAL_NAMESPACES.iter().find(|namespace| {
        name.len() >= namespace.prefix.len() + namespace.suffix.len()
            && name.starts_with(namespace.prefix)
            && name.ends_with(namespace.suffix)
    })
}

/// Whether `name` lies in ANY AY-internal namespace. This is the predicate the
/// untrusted SMT-LIB source-text route and `ay-ffi`'s C-API name gate share.
#[must_use]
pub fn is_internal_namespace_name(name: &str) -> bool {
    internal_namespace_of(name).is_some()
}

/// Whether `name` lies in an internal namespace that NO declaration route may
/// mint (`InternalNamespaceScope::EveryRoute`). This is the part of the
/// internal-namespace gate that also binds the native/programmatic API.
fn is_undeclarable_internal_namespace_name(name: &str) -> bool {
    internal_namespace_of(name)
        .is_some_and(|namespace| namespace.scope == InternalNamespaceScope::EveryRoute)
}

/// Why `name` was refused, for [`ElaborateError::ReservedSymbol`]'s message.
/// Names the ACTUAL namespace rather than always blaming the `__ay_` prefix, so
/// a user hitting the `map[...]` or `!ay.*` gate is told what they collided
/// with.
fn reserved_symbol_reason(name: &str) -> &'static str {
    internal_namespace_of(name).map_or(
        "builtin theory-operator name AY matches structurally",
        |namespace| namespace.rationale,
    )
}

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
/// dynamic gates above were added.) Bare Z3 array-plugin set aliases (`union`,
/// `intersection`, `setminus`, `complement`, `subset`) are structurally matched
/// only after declared-symbol resolution. They therefore remain legitimate
/// user-symbol names and are classified as `declared-shadowed` below.
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
    // Z3 5.0.0 FiniteSet spellings. `set.union`, `set.singleton`,
    // `set.subset`, and qualified `set.empty` are shared with the vocabulary
    // above; the remaining names are Z3-5-specific aliases/operators.
    "set.in", "set.size", "set.intersect", "set.difference",
    "set.map", "set.filter", "set.range",
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
    // ---- Char theory (elaborate/app/strings.rs) — character terms lower to Int code points ----
    // (z3 has char.<= but not char.<, so char.< is intentionally absent.)
    "char.to_int", "char.<=", "char.is_digit", "char.to_bv", "char.from_bv",
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

/// Why an elaborator-recognized operator spelling remains user-declarable.
///
/// Keeping this classification closed prevents a misspelled reason tag from
/// silently changing the declaration-identity or theory-identity gates.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ExcludedDeclarableOpClass {
    /// A Core/Ints/Reals operator that must remain a legal array-map target.
    MapTarget,
    /// A spelling recognized only as part of an indexed identifier.
    IndexedOnly,
    /// The match-expression wildcard binder, rather than an operator head.
    PatternBinder,
    /// An operator for which a live declaration takes precedence.
    DeclaredShadowed,
    /// A collection operator activated by a declaration at its native rank.
    DeclarationActivated,
}

use ExcludedDeclarableOpClass::{
    DeclarationActivated, DeclaredShadowed, IndexedOnly, MapTarget, PatternBinder,
};

impl ExcludedDeclarableOpClass {
    const fn is_canonical_theory_identity(self) -> bool {
        matches!(self, Self::MapTarget | Self::DeclarationActivated)
    }
}

fn excluded_declarable_op_class(name: &str) -> Option<ExcludedDeclarableOpClass> {
    EXCLUDED_DECLARABLE_OP_NAMES
        .iter()
        .find_map(|&(operator, class)| (operator == name).then_some(class))
}

/// Whether `name` is an exact core identity whose semantics are selected by a
/// theory operator rather than by an ordinary uninterpreted declaration.
///
/// This is wider than [`is_reserved_op_name`]: Core/Ints/Reals operators remain
/// legal array-map targets, so source declarations using those spellings are
/// assigned private core identities instead of being rejected.  Their raw
/// spellings nevertheless remain canonical theory identities.  Collection
/// predicates in the declaration-activated class likewise request native
/// theory semantics rather than an arbitrary UF interpretation.
///
/// `declared-shadowed` names are intentionally absent: once a live declaration
/// owns one of those names, elaboration gives that declaration precedence over
/// the builtin syntax. `indexed-only` names are classified by the `Symbol`
/// shape at their consumer because their bare named forms remain ordinary
/// declaration identities.
#[doc(hidden)]
pub fn is_canonical_theory_operator_identity(name: &str) -> bool {
    is_reserved_op_name(name)
        || excluded_declarable_op_class(name)
            .is_some_and(ExcludedDeclarableOpClass::is_canonical_theory_identity)
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
/// Exclusion classes:
///
/// * `MapTarget` — SMT-LIB Core connectives and Ints/Reals operators. AY's
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
/// * `IndexedOnly` — identifiers recognized solely inside `(_ …)` indexed
///   forms (`(_ map f)`, `(_ is C)`, `(_ divisible n)`, `(_ at-most k)`, …,
///   and the structured Char/FP special literals `(_ Char n)`/
///   `(_ +zero eb sb)`/`(_ NaN eb sb)`/… matched in `indexed.rs`. A plain
///   `App(Named(name), ..)` of the bare name is never theory-matched, so a
///   user declaration cannot conflate with the builtin (adversarially
///   verified for `map`/`at-most`/`at-least`/`pble`/`pbge`/`pbeq`/`divisible`/
///   `re.^`, and for quoted-symbol FP-literal forgeries: sat/correct).
///
/// * `PatternBinder` — `_`, matched in `term.rs` only as the wildcard
///   binder of a `(match …)` default case. It is not an operator and is never
///   elaborated as an application head, so it cannot conflate.
///
/// * `DeclaredShadowed` — structurally recognized operators whose dispatcher
///   is reached only after declared-symbol resolution. This includes `const`,
///   the constant-array qualified identifier `((as const (Array ..)) v)`, and
///   Z3's legacy array-plugin set aliases (`union`, `intersection`, `setminus`,
///   `complement`, `subset`). They stay declarable because Z3 gives a user
///   declaration precedence over these builtin spellings. Real-world QF_UF
///   benchmarks also legitimately declare `const` (the B-method CLEARSY
///   regression fixtures declare `(declare-fun |const| (U U) U)` — reserving
///   it broke `test_clearsy_00307/00310_full_instance_matches_z3`). The
///   dispatcher guards ensure that once declared, these names resolve to the
///   user symbol, closing builtin conflation by shadowing rather than by
///   reservation.
///
/// * `DeclarationActivated` — AY-extension collection predicates whose
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
pub(crate) const EXCLUDED_DECLARABLE_OP_NAMES: &[(&str, ExcludedDeclarableOpClass)] = &[
    // SMT-LIB Core connectives (elaborate/app/core.rs)
    ("and", MapTarget), ("or", MapTarget), ("not", MapTarget),
    ("xor", MapTarget), ("=>", MapTarget), ("implies", MapTarget),
    ("&&", MapTarget), ("||", MapTarget),
    ("=", MapTarget), ("equals", MapTarget), ("equiv", MapTarget),
    ("iff", MapTarget), ("distinct", MapTarget),
    ("ite", MapTarget), ("if", MapTarget), ("if_then_else", MapTarget),
    // Ints/Reals operators (elaborate/app/arithmetic.rs, app/core.rs)
    ("+", MapTarget), ("-", MapTarget), ("*", MapTarget),
    ("/", MapTarget), ("^", MapTarget), ("~", MapTarget),
    ("**", MapTarget), ("div", MapTarget),
    ("mod", MapTarget), ("rem", MapTarget), ("abs", MapTarget),
    ("min", MapTarget), ("max", MapTarget),
    ("<", MapTarget), ("<=", MapTarget), (">", MapTarget),
    (">=", MapTarget),
    ("to_int", MapTarget), ("to_real", MapTarget), ("is_int", MapTarget),
    // Indexed-form-only identifiers (elaborate/indexed.rs)
    ("map", IndexedOnly), ("is", IndexedOnly), ("divisible", IndexedOnly),
    ("at-most", IndexedOnly), ("at-least", IndexedOnly),
    ("pble", IndexedOnly), ("pbge", IndexedOnly), ("pbeq", IndexedOnly),
    ("re.^", IndexedOnly),
    // Datatype field update `((_ update-field <sel>) record value)`
    // (elaborate/indexed.rs): matched ONLY inside the `(_ …)` indexed form, so a
    // bare `App(Named("update-field"), ..)` is never theory-matched and a user
    // declaration of `update-field` cannot conflate with the builtin.
    ("update-field", IndexedOnly),
    // Special-relations family (elaborate/indexed.rs): special ONLY as the
    // indexed identifier `(_ partial-order N)` &c. The bare name is a legal user
    // function — Verus's own cvc5 prelude declares `(declare-fun partial-order
    // (Height Height) Bool)` — so these must stay declarable, not reserved.
    ("partial-order", IndexedOnly), ("linear-order", IndexedOnly),
    ("tree-order", IndexedOnly), ("piecewise-linear-order", IndexedOnly),
    // Char and FP special literals, matched only inside a structured `(_ …)` form
    ("Char", IndexedOnly), ("char", IndexedOnly),
    ("+zero", IndexedOnly), ("-zero", IndexedOnly),
    ("+oo", IndexedOnly), ("-oo", IndexedOnly), ("NaN", IndexedOnly),
    // Match-case wildcard binder (term.rs), not an operator
    ("_", PatternBinder),
    // Constant-array qualified identifier: declarable (CLEARSY benchmarks do);
    // its qualified.rs arm defers to the declared symbol (see doc above).
    ("const", DeclaredShadowed),
    // Z3 array-plugin set aliases: a declaration shadows the builtin before
    // app/set.rs dispatch, exactly as in Z3 5.0.0 (see doc above).
    ("union", DeclaredShadowed),
    ("intersection", DeclaredShadowed),
    ("setminus", DeclaredShadowed),
    ("complement", DeclaredShadowed),
    ("subset", DeclaredShadowed),
    // Declaration-activated collection theory ops (see doc comment above):
    // deductive-checks declares these to trigger the native solver; misuse fails
    // closed (probed).
    ("set.subset", DeclarationActivated),
    ("map.dom", DeclarationActivated),
    ("map.subset", DeclarationActivated),
    ("multiset.subset", DeclarationActivated),
];

/// Check whether `name` is an elaborator-recognized operator name that is
/// deliberately kept user-declarable (see [`EXCLUDED_DECLARABLE_OP_NAMES`]).
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn is_excluded_declarable_op_name(name: &str) -> bool {
    excluded_declarable_op_class(name).is_some()
}

/// Whether a legal user declaration must receive a private core symbol even
/// when it is the first declaration with that surface spelling.
///
/// Map-target names are also builtin operator spellings.  Keeping a user's
/// first `(declare-fun rem ...)` as `Symbol::Named("rem")`, for example, makes
/// the core DAG indistinguishable from builtin integer remainder.  That is
/// unsafe for every independently checked rewrite or proof rule that assigns
/// fixed semantics by core symbol.  Array-map still resolves the declaration
/// through `SymbolInfo::internal_name`, while ordinary builtin syntax (with no
/// declaration in scope) retains the canonical builtin spelling.
pub(crate) fn declaration_requires_private_core_identity(name: &str) -> bool {
    excluded_declarable_op_class(name) == Some(MapTarget)
}

/// Check whether `name` is a declaration-activated collection predicate (the
/// `DeclarationActivated` rows of [`EXCLUDED_DECLARABLE_OP_NAMES`]): a name
/// whose `declare-fun` at the native collection signature is the documented
/// activation route for AY's native set/map/multiset solvers, and which is
/// rejected in every other declaration context (wrong signature,
/// `declare-const`, `define-fun`, datatype ctor/selector/tester).
pub(crate) fn is_declaration_activated_op_name(name: &str) -> bool {
    excluded_declarable_op_class(name) == Some(DeclarationActivated)
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

/// Check if a symbol name is reserved on EVERY declaration route, including the
/// programmatic/native `Solver` API: it lies in an AY-internal namespace that no
/// declaration may mint (`__ay_*`, `map[...]` — see
/// [`is_undeclarable_internal_namespace_name`]), it is a builtin
/// theory-operator name AY matches structurally (see [`RESERVED_OP_NAMES`]), or
/// it is a declaration-activated collection predicate (see
/// [`is_declaration_activated_op_name`]). Reserved names cannot be
/// `declare`d/`define`d; doing so is rejected with
/// [`ElaborateError::ReservedSymbol`]. Sole exception: `declare_fun` admits a
/// declaration-activated name at its native collection signature — the
/// documented activation route for the native collection solvers (it
/// special-cases BEFORE this check; see `Context::declare_fun`).
///
/// The `InternalNamespaceScope::SourceTextAndCApi` namespaces (`!ay.*`,
/// `map[...]`) are deliberately NOT here: the in-process native API declares
/// `!ay.*` witnesses through this very entry point, and registering
/// internal-looking function names natively is an existing exercised contract.
/// Both are refused on the untrusted SMT-LIB source-text route and by the C
/// surface — see [`is_source_reserved_symbol`] and `ay-ffi`'s
/// `reserved_name_error`.
pub fn is_reserved_symbol(name: &str) -> bool {
    is_undeclarable_internal_namespace_name(name)
        || is_reserved_op_name(name)
        || is_declaration_activated_op_name(name)
}

/// Check if a symbol name is reserved against UNTRUSTED SMT-LIB SOURCE TEXT.
///
/// This is [`is_reserved_symbol`] widened with every remaining AY-internal
/// namespace, including the embedder-minted `!ay.*` witnesses. Source text has
/// no minting authority over any internal namespace, so the union applies;
/// only the in-process native API (`Solver::declare_const`,
/// `Solver::try_declare_fun`, used by AY's own Z3 C surface) keeps the narrower
/// [`is_reserved_symbol`] gate.
#[must_use]
pub fn is_source_reserved_symbol(name: &str) -> bool {
    is_reserved_symbol(name) || is_internal_namespace_name(name)
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
    /// Reserved symbol: either a name in an AY-internal namespace (see
    /// [`INTERNAL_NAMESPACES`]) or a builtin theory-operator name that AY
    /// matches structurally (see [`RESERVED_OP_NAMES`]). Declaring such a name
    /// would silently conflate the forged symbol with the internal object or
    /// builtin operator, so it is rejected.
    #[error(
        "symbol '{}' is reserved ({}) and cannot be declared",
        .0,
        reserved_symbol_reason(.0)
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
    /// A sort symbol that is not in the signature: neither a builtin, nor a
    /// `declare-sort`/`define-sort`/`declare-datatype(s)` name that is still in
    /// scope. Previously such a name was silently accepted as a fresh
    /// uninterpreted sort, which accepted every mistyped sort name and let a
    /// sort declared inside a `push` outlive its `pop` (with the datatype's
    /// interpretation, and its finite domain, silently lost).
    #[error("unknown sort '{0}'")]
    UnknownSort(String),
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
    /// Public SMT-LIB result sort before implementation lowering.
    ///
    /// Z3 5.0.0's `(FiniteSet T)` remains distinct here even though the engine
    /// carries it as `(Array T Bool)`.
    pub public_sort: PublicSort,
    /// Public SMT-LIB argument sorts before implementation lowering.
    pub public_arg_sorts: Vec<PublicSort>,
    /// Instance-specific INTERNAL symbol name to use when building the term,
    /// when it differs from the user-facing surface name. This is set for
    /// datatype members whose preferred identity was already used,
    /// monomorphized parametric-datatype members, builtin-colliding map-target
    /// declarations/definitions, and every ordinary source binding after the
    /// first overload or scoped incarnation of a surface name. The term then
    /// carries a name-disjoint symbol, preventing interpreted/user and distinct
    /// SMT-LIB bindings from collapsing onto one core identity. A non-colliding
    /// first ordinary binding keeps `None`, preserving its historical surface
    /// identity.
    pub internal_name: Option<String>,
    /// Stable identity of the declaration behind this surface binding.
    declaration_id: DeclarationId,
    /// Positive origin classification. Adopted definitions are overlaid by
    /// [`Context::effective_declaration_kind`] while their justifying assertion
    /// remains live.
    declaration_kind: DeclarationKind,
    /// How this surface binding entered the frontend symbol table.
    ///
    /// This is deliberately distinct from `declaration_kind`: a trusted native
    /// alias may point at an ordinary uninterpreted declaration and share its
    /// stable `DeclarationId`/semantic kind, but the alias is not itself a direct
    /// authored declaration and must never become quantified-model projection
    /// authority. Only `declare-const`/`declare-fun` set the direct-source origin.
    binding_origin: SymbolBindingOrigin,
}

/// Private provenance for one symbol-table binding.
///
/// The enum is intentionally not exported. Downstream candidate producers get
/// only the narrow observational predicate on [`SymbolInfo`]; the positive
/// source checker still combines this bit with exact core identity, declaration
/// identity/kind, signature, overload, and source/scope-epoch checks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SymbolBindingOrigin {
    Other,
    DirectSourceDeclaration,
    /// Installed by a native-API declaration that ALLOCATES its own term and
    /// registers it atomically (`register_native_global_constant`), so the
    /// spelling/identity coherence a parsed `declare-const` guarantees holds
    /// by construction. Distinct from [`Self::DirectSourceDeclaration`] so
    /// the two lanes stay separately auditable, and NEVER given to
    /// `register_symbol`/`register_native_global_symbol`: those accept a
    /// caller-supplied term, which is exactly the freedom the forged-owner
    /// rejection tests exercise, and are also used for solver-internal
    /// bookkeeping symbols that must not leak into user models.
    NativeApiDeclaration,
}

impl SymbolInfo {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn fresh(
        term: Option<TermId>,
        sort: Sort,
        arg_sorts: Vec<Sort>,
        public_sort: PublicSort,
        public_arg_sorts: Vec<PublicSort>,
        internal_name: Option<String>,
        declaration_kind: DeclarationKind,
    ) -> Self {
        Self::fresh_with_binding_origin(
            term,
            sort,
            arg_sorts,
            public_sort,
            public_arg_sorts,
            internal_name,
            declaration_kind,
            SymbolBindingOrigin::Other,
        )
    }

    /// Construct the binding installed by a direct source `declare-const` or
    /// `declare-fun`. This is the sole constructor for projection-eligible
    /// binding origin; semantic eligibility is still checked independently.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn fresh_direct_source_declaration(
        term: Option<TermId>,
        sort: Sort,
        arg_sorts: Vec<Sort>,
        public_sort: PublicSort,
        public_arg_sorts: Vec<PublicSort>,
        internal_name: Option<String>,
        declaration_kind: DeclarationKind,
    ) -> Self {
        Self::fresh_with_binding_origin(
            term,
            sort,
            arg_sorts,
            public_sort,
            public_arg_sorts,
            internal_name,
            declaration_kind,
            SymbolBindingOrigin::DirectSourceDeclaration,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn fresh_with_binding_origin(
        term: Option<TermId>,
        sort: Sort,
        arg_sorts: Vec<Sort>,
        public_sort: PublicSort,
        public_arg_sorts: Vec<PublicSort>,
        internal_name: Option<String>,
        declaration_kind: DeclarationKind,
        binding_origin: SymbolBindingOrigin,
    ) -> Self {
        Self {
            term,
            sort,
            arg_sorts,
            public_sort,
            public_arg_sorts,
            internal_name,
            declaration_id: DeclarationId::fresh(),
            declaration_kind,
            binding_origin,
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn alias_of(
        term: Option<TermId>,
        sort: Sort,
        arg_sorts: Vec<Sort>,
        public_sort: PublicSort,
        public_arg_sorts: Vec<PublicSort>,
        internal_name: Option<String>,
        target: &Self,
    ) -> Self {
        Self {
            term,
            sort,
            arg_sorts,
            public_sort,
            public_arg_sorts,
            internal_name,
            declaration_id: target.declaration_id.clone(),
            declaration_kind: target.declaration_kind,
            binding_origin: SymbolBindingOrigin::Other,
        }
    }
}

include!("symbol_info.rs");

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

/// Public typing policy for historically shared `set.*` spellings.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum FiniteSetTypingMode {
    /// Preserve AY's pre-Z3-5 legacy `Set` extensions.
    #[default]
    LegacyCompatible,
    /// Match Z3 5.0.0: shared constructors are `FiniteSet`-only.
    Z3_5Strict,
}

/// Maximum recursion depth for define-fun-rec expansion (#8622).
/// Prevents unbounded stack/heap growth from mutually recursive definitions.
const MAX_FUN_EXPANSION_DEPTH: usize = 1000;

const OPTION_GLOBAL_DECLARATIONS: &str = "global-declarations";
const OPTION_GLOBAL_DECLS: &str = "global-decls";

type FunctionDefinition = (Vec<(String, Sort)>, Sort, ParsedTerm);

/// How to render one solver-invented single-constructor FIELD constant as
/// SMT-LIB text an external proof checker can read: a selector application over
/// the DECLARED parent constant (`s_!left` -> `(left s_)`).
///
/// WHY. Eager single-constructor datatype elimination (`build_const_term`,
/// `declarations.rs`) replaces a declared constant `s_` of a product sort with
/// `(Record_left_center_right s_!left s_!center s_!right)` over per-field
/// constants it invents. Those names exist ONLY inside AY — the problem file
/// declares `s_`, not `s_!left` — so an exported Alethe certificate that names
/// them is unreadable to a checker, which builds its symbol table from the
/// ORIGINAL `.smt2`. Measured on
/// `QF_DT/20230720-blocksworld/blocksworld_from_0_0_8_to_1_3_4_negated_goal_bmc_2`:
/// 14 distinct invented names in 26,366 occurrences, and a declaration preamble
/// with ZERO `(declare-fun ...)` lines (the auxiliary-declaration pass computes
/// the problem scope from AY's own ELABORATED assertions, which already contain
/// the invented names, so every one looks problem-declared). carcara 1.1.0 then
/// died in the PARSER, before checking a single rule:
///   `[ERROR] parser error: identifier 's_tmp___!left' is not defined`
///
/// Declaring the invented names in the preamble instead would be WRONG: the
/// document would become a proof about fresh constants rather than about the
/// problem's `s_`. Rendering them as what they ARE needs no declaration at all
/// — `left` is a real selector, in scope from `declare-datatypes`, and `s_` is
/// declared by the problem at the right sort (verified against carcara 1.1.0:
/// a selector application is accepted even when that application appears
/// NOWHERE in the problem text).
///
/// The record is keyed by `TermId` and built ONLY where the constants are
/// minted, never by inspecting a spelling: this problem file also declares the
/// USER symbols `c!0`, `c!1`, `c!2`, which a split-on-`!` rule would rewrite
/// into the nonsense `(0 c)`.
#[derive(Clone, Debug)]
struct DtFieldSurface {
    /// The composed rendering, e.g. `(top (right s_))` at nesting depth 2.
    /// Built by passing the parent's rendering DOWN the recursion (the child is
    /// minted before any of the parent's bookkeeping runs, so it cannot be
    /// looked up afterwards).
    rendering: String,
    /// Surface name of the DECLARED constant at the root of the chain.
    root_surface: String,
    /// Private core identity of an overloaded root. `None` is the first
    /// declaration, whose core identity is its surface name.
    root_internal_name: Option<String>,
    /// Exact elaborated result sort selected by a qualified root.
    root_sort: Sort,
    /// Whether `rendering` starts with an `(as root sort)` qualification.
    /// Unqualified overloaded roots remain unsafe and are withheld.
    qualified_root: bool,
    /// Positional constructor-argument indices from the root's bound term down
    /// to this field. Used at export time to re-derive — not merely assume —
    /// that `rendering` still denotes this exact term.
    path: Vec<usize>,
    /// Surface selector names occurring in `rendering`. Re-checked at export
    /// time for shadowing, which is a property of LATER commands.
    selectors: Vec<String>,
}

/// A user declaration whose rank mentions global SMT-LIB 2.7 sort parameters.
/// It denotes a family of ordinary monomorphic declarations.
#[derive(Debug, Clone)]
struct PolymorphicDeclaration {
    name: String,
    argument_sorts: Vec<crate::command::Sort>,
    result_sort: crate::command::Sort,
    parameters: Vec<String>,
    global: bool,
}

/// An authored assertion containing global schematic sort parameters.
#[derive(Debug, Clone)]
struct PolymorphicAssertion {
    term: ParsedTerm,
    parameters: Vec<String>,
    /// Definition axioms survive `reset-assertions`; authored `assert`
    /// commands do not.
    persistent_definition: bool,
}

#[derive(Debug, Clone)]
enum AuthoredAssertion {
    Concrete {
        term: TermId,
        parsed_index: Option<usize>,
        /// Compact provenance retained when the optional parsed AST is not.
        /// A canonical `false` TermId alone cannot distinguish literal source
        /// `false` from an arbitrary formula that elaborated to false.
        source_is_literal_false: bool,
    },
    Schematic(ParsedTerm),
}

/// Whether the authored source is literally `false` (modulo annotations), or
/// the reserved native-API placeholder whose exact TermId is the entire source
/// obligation. Proof consumers additionally require that TermId to be false.
fn authored_source_is_literal_false(term: &ParsedTerm) -> bool {
    let mut term = term;
    while let ParsedTerm::Annotated(inner, _) = term {
        term = inner;
    }
    matches!(term, ParsedTerm::Const(crate::command::Constant::False))
        || matches!(term, ParsedTerm::Symbol(name) if name == "__ay_api_assertion__")
}

/// One authored assertion in source order, ready for `get-assertions` display.
///
/// Ordinary assertions normally retain their parsed surface tree.  When that
/// optional high-memory proof aid is disabled, callers still receive the exact
/// elaborated term as a sound fallback.  Schematic SMT-LIB 2.7 assertions have
/// no single elaborated term, so their authored surface tree is authoritative.
#[derive(Debug, Clone, Copy)]
pub enum AuthoredAssertionRef<'a> {
    /// Original parsed surface syntax.
    Parsed(&'a ParsedTerm),
    /// Elaborated fallback for a non-schematic assertion.
    Elaborated(TermId),
}

/// Sticky source-level description of one nominal engine carrier.
///
/// This metadata follows the term-store lifetime, not source scope: a retained
/// term may still need to print its old sort after the declaration was popped.
#[derive(Debug, Clone, PartialEq, Eq)]
enum NominalSortSurface {
    /// A zero-arity sort declaration or monomorphic datatype.
    Simple(String),
    /// One structurally keyed application of a parametric datatype template.
    ParametricDatatype {
        /// Legacy readable spelling retained for diagnostics only.
        display: String,
        /// Source template name.
        template: String,
        /// Exact engine arguments, recursively surfaced when printed.
        arguments: Vec<Sort>,
    },
}

/// The put-it-back token from [`Context::begin_internal_logic_borrow`].
///
/// Opaque and field-private on purpose: only the paired begin/end methods may
/// construct or read one, so no caller can fabricate a revision to roll back
/// to. It is deliberately NOT `Drop`-based — an internal sub-solve wants the
/// restore to be an explicit, greppable line in the lane that borrowed.
#[derive(Debug)]
#[must_use = "the borrowed logic slot must be put back"]
pub struct InternalLogicBorrow {
    /// The logic in effect before the borrow, restored verbatim.
    saved_logic: Option<String>,
    /// The source revision before the borrow's own outbound write.
    saved_revision: u64,
    /// The source revision immediately after that outbound write. If the live
    /// revision has moved past this, something other than the borrow changed
    /// the source context and `saved_revision` must NOT be restored.
    entry_revision: u64,
}

/// Elaboration context
// Trust: `Clone` lets an independent UNSAT re-discharge rebuild a fresh `Executor`
// over a COPY of the full solving context (terms, assertions, logic, options) — the
// same setup the main solve used — so the complete solve path re-decides deep
// nested-ite obligations that a thin re-translate leaves Unknown.
#[derive(Clone)]
pub struct Context {
    /// Identity of this independently mutable frontend context. Cloning a
    /// context deliberately mints a fresh identity.
    context_identity: ContextIdentity,
    /// Revision of source declaration/scope semantics in this context.
    source_revision: u64,
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
    /// Core spellings already assigned to declarations in this term store.
    /// Scope pop deliberately does not rewind this set: old native [`TermId`]
    /// handles may survive the pop, so a later ordinary function or datatype
    /// member must not hash-cons onto an old application's core identity. A
    /// full context reset replaces both this set and the term store.
    declaration_core_identities_used: HashSet<String>,
    /// Monotonic source of private nominal sort identities. It shares the
    /// context lifetime with `terms` and is never rewound by scope pop.
    next_sort_identity: u64,
    /// Nominal sort cores already assigned in this context's term-store
    /// lifetime. Retained terms can outlive a scoped sort declaration, so a
    /// later declaration must not reuse the old carrier spelling.
    sort_core_identities_used: HashSet<String>,
    /// Exact nominal carrier -> typed source-level rendering metadata.
    /// Retained across `pop`; cleared only with the context/term store.
    nominal_sort_surfaces: HashMap<String, NominalSortSurface>,
    /// Sort definitions: name -> sort
    sort_defs: HashMap<String, Sort>,
    /// Public identities for zero-arity sort synonyms.
    ///
    /// `sort_defs` stores engine lowerings and therefore cannot distinguish
    /// `(FiniteSet T)` from `(Array T Bool)`.
    public_sort_defs: HashMap<String, PublicSort>,
    /// Parameterized sort synonyms (`(define-sort Name (T..) body)`, arity > 0):
    /// name -> (type-parameter names, un-elaborated body template). Kept as a
    /// template (not eagerly elaborated) so each ground use `(Name A1 .. An)`
    /// can substitute the parameters and elaborate the body — see
    /// `elaborate/sorts.rs`. The 0-arity case stays in `sort_defs`.
    parametric_sort_defs: HashMap<String, (Vec<String>, crate::command::Sort)>,
    /// Global schematic sort parameters declared by SMT-LIB 2.7 scripts.
    sort_parameters: ay_core::kani_compat::DetHashSet<String>,
    /// Schematic `declare-fun` / `declare-const` families.
    polymorphic_declarations: Vec<PolymorphicDeclaration>,
    /// Internal guard while registering one concrete family member.
    instantiating_polymorphic_declaration: bool,
    /// Authored assertions instantiated at each satisfiability check.
    polymorphic_assertions: Vec<PolymorphicAssertion>,
    /// User `assert` commands in source order, excluding definition axioms and
    /// query-local schematic instances.
    authored_assertions: Vec<AuthoredAssertion>,
    /// Concrete assertion instances appended for the current query.
    materialized_polymorphic_assertions: usize,
    /// Whether the current query contains every required schematic instance.
    polymorphic_instantiation_complete: bool,
    /// Suppress name-keyed macro adoption for a concrete family member.
    elaborating_polymorphic_instance: bool,
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
    /// Exact declaration identity behind each adopted macro interpretation.
    adopted_macro_declaration_ids: HashMap<String, DeclarationId>,
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
    ///
    /// This is a sticky semantic registry for the lifetime of `terms`.
    /// `pop` removes a carrier from `live_datatype_carriers` but retains this
    /// exact metadata so an authenticated old term can still be solved with
    /// its datatype semantics if a native caller re-asserts it later.
    datatypes: HashMap<String, Vec<String>>,
    /// Datatype carriers currently reachable through live source declarations
    /// or live parametric-instance caches.
    live_datatype_carriers: HashSet<String>,
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
    /// Exact signature/identity record for every datatype member registered in
    /// this term store. Live symbol tables remain scoped; proof, model, and
    /// cached-instance consumers use this sticky registry only when they have
    /// already authenticated an exact datatype-member identity.
    datatype_member_symbols: HashMap<String, SymbolInfo>,
    /// Parametric (polymorphic) datatype templates: dt_name -> declaration.
    ///
    /// A `(declare-datatypes ((Name n)) ((par (T..) ..)))` with arity `n > 0`
    /// is stored here instead of being eagerly registered. Each ground use
    /// `(Name A1 .. An)` is lazily monomorphized into a fresh instance sort and
    /// its constructors/selectors/testers (see `elaborate/datatypes.rs`).
    parametric_datatypes: HashMap<String, crate::command::DatatypeDec>,
    /// Stable identity of each live parametric datatype declaration.
    ///
    /// The surface name is scoped and may be reused after `pop`, while retained
    /// terms can still contain instances of the old template. Structural
    /// instance caches therefore key on this identity, never on the spelling.
    parametric_datatype_ids: HashMap<String, DeclarationId>,
    /// Reverse map for a registered parametric instance: mangled instance sort
    /// name -> (template identity, template name, type arguments). Lets
    /// constructor-application instance inference recover the type arguments
    /// of a nested instance sort (e.g. unify the template field `(Lst T)`
    /// against an argument of sort `Lst!{Int}` to learn `T = Int`). The exact
    /// template identity also makes scope cleanup immune to name reuse.
    parametric_instance_args: HashMap<String, (DeclarationId, String, Vec<Sort>)>,
    /// Structural parametric instance key -> exact nominal carrier core.
    /// Unlike the legacy display-style mangle, this key cannot conflate a user
    /// sort spelling with an Array/Seq/datatype argument of similar text, or a
    /// popped template with a later declaration using the same surface name.
    parametric_instance_sorts: HashMap<(DeclarationId, Vec<Sort>), String>,
    /// Internal term symbol name -> user-facing surface name. Covers both
    /// instance-mangled datatype members and ordinary declaration overloads,
    /// so serialization/model output never leaks private identities.
    dt_internal_surface: HashMap<String, String>,
    /// Surface rendering of each solver-invented single-constructor FIELD
    /// constant, keyed by the exact `TermId` `build_const_term` minted for it
    /// (see [`DtFieldSurface`] for why this exists and what it is read for).
    dt_field_surface: HashMap<TermId, DtFieldSurface>,
    /// Current logic
    logic: Option<String>,
    /// Enforce the language declared by the 25 official SMT-LIB 2.7 logics.
    ///
    /// The library keeps its historical permissive default because embedders
    /// use `set-logic` as a solver-selection upper bound.  The ordinary AY
    /// SMT-LIB CLI enables this policy; the explicit Z3 compatibility surface
    /// leaves it disabled because Z3 accepts a wider overlay language.
    strict_logic_compliance: bool,
    /// Whether the logic was set by a `(set-logic ...)` in the COMMAND STREAM,
    /// as opposed to being installed by an API constructor.
    ///
    /// z3 draws exactly this line: "the logic has already been set" is PARSER
    /// state, so `Z3_mk_solver_for_logic` / `SolverFor(...)` does not count as a
    /// `set-logic` and a subsequently parsed script may still carry one — even
    /// one naming a DIFFERENT logic. Keying the guard on `logic.is_some()`
    /// conflated the two and rejected the first `(set-logic ...)` of every
    /// script handed to an API-constructed solver.
    logic_set_by_command: bool,
    /// Assertions (internal normalized form)
    pub assertions: Vec<TermId>,
    /// Finite-set provenance aligned one-for-one with `assertions`.
    assertion_finite_set_metadata: Vec<PublicAssertionMetadata>,
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
    /// Public-sort metadata aligned with `objectives`.
    objective_finite_set_metadata: Vec<PublicAssertionMetadata>,
    /// Soft (weighted) constraints from `(assert-soft ...)`
    soft_constraints: Vec<SoftAssertion>,
    /// Public-sort metadata aligned with `soft_constraints`.
    soft_finite_set_metadata: Vec<PublicAssertionMetadata>,
    /// Scope stack for push/pop
    scopes: Vec<ScopeFrame>,
    /// Whether this session ever processed a `push`, `pop`, or
    /// `check-sat-assuming` command. Distinct from `scopes.is_empty()`, which a
    /// matched `push`/`pop` pair restores to `true`. See
    /// [`Self::is_single_shot_query`].
    scope_commands_used: bool,
    /// Number of `check-sat` / `check-sat-assuming` commands processed. See
    /// [`Self::is_single_shot_query`].
    check_sat_commands: u32,
    /// Internal one-command override for native solver declarations whose
    /// handles outlive SMT-LIB assertion scopes. Kept separate from the public
    /// global-declarations option so native calls never mutate session options.
    native_global_declaration: bool,
    /// Solver options (keyword -> value)
    options: HashMap<String, OptionValue>,
    /// Z3's `:numeral-as-real` parser mode. When enabled, an otherwise
    /// unconstrained numeral token is elaborated as a Real constant instead of
    /// an Int constant.
    numeral_as_real: bool,
    /// Whether Z3-style implicit Bool/Int/Real coercions are enabled.
    /// Controlled by the `:int-real-coercions` SMT-LIB option.
    int_real_coercions: bool,
    /// Named formulas: name -> term_id (for get-assignment and get-unsat-core)
    named_terms: HashMap<String, TermId>,
    /// Z3 debug-command global AST slots (`dbg-set` / `dbg-pp-var`).
    ///
    /// The authored spelling is retained because these commands inspect the
    /// parser AST before AY's eager solver rewrites. Storing a lowered
    /// `TermId` would turn e.g. `(and true false)` into `false` on replay.
    z3_debug_exprs: HashMap<String, String>,
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
    /// Public typing policy for Z3 5 finite-set spellings.
    finite_set_typing_mode: FiniteSetTypingMode,
}

/// Opaque saved query view for one internal solver probe.
///
/// A probe sometimes has to solve an exact derived root vector in the original
/// [`Context`] so a resulting model's `TermId`s remain in the same arena. Merely
/// replacing [`Context::assertions`] is not enough: parsed assertion metadata,
/// named terms, objectives, soft constraints, and schematic-query bookkeeping
/// would still describe the enclosing public query. This affine value owns that
/// complete query-local view while the derived roots are active.
///
/// Construction and restoration intentionally do not advance the source
/// revision. Declarations and scopes are not changed, and the enclosing query
/// must retain the same [`SourceContextStamp`] after restoration. The solver may
/// append terms while the window is active; rollback, compaction, a cloned
/// context, or a source mutation makes restoration report that the surrounding
/// authority is no longer exact.
#[doc(hidden)]
#[must_use = "an internal query window must be restored on every exit path"]
pub struct InternalQueryWindow {
    source_context_stamp: SourceContextStamp,
    term_prefix: TermStoreSnapshotStamp,
    assertions: Vec<TermId>,
    assertion_finite_set_metadata: Vec<PublicAssertionMetadata>,
    assertions_parsed: Vec<ParsedTerm>,
    retain_parsed_assertions: bool,
    objectives: Vec<Objective>,
    objective_finite_set_metadata: Vec<PublicAssertionMetadata>,
    soft_constraints: Vec<SoftAssertion>,
    soft_finite_set_metadata: Vec<PublicAssertionMetadata>,
    named_terms: HashMap<String, TermId>,
    polymorphic_assertions: Vec<PolymorphicAssertion>,
    authored_assertions: Vec<AuthoredAssertion>,
    materialized_polymorphic_assertions: usize,
    polymorphic_instantiation_complete: bool,
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
    /// Datatypes defined in this scope: (internal carrier, surface declaration).
    datatypes: Vec<(String, String)>,
    /// Constructors defined in this scope
    constructors: Vec<String>,
    /// Sort definitions in this scope
    sort_defs: Vec<String>,
    /// Function definitions in this scope (#8621)
    fun_defs: Vec<String>,
    /// Parametric datatype templates declared in this scope
    parametric_datatypes: Vec<String>,
    /// Number of authored polymorphic assertions before this scope.
    polymorphic_assertion_count: usize,
    /// Number of user `assert` commands before this scope.
    authored_assertion_count: usize,
    /// Schematic declarations introduced in this scope.
    polymorphic_declarations: Vec<String>,
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
    /// Invalidate every previously captured source/scope stamp.
    ///
    /// On the practically unreachable counter exhaustion boundary, rotate the
    /// context identity instead of wrapping into a revision that could equal a
    /// stale snapshot.
    pub(super) fn advance_source_revision(&mut self) {
        if let Some(next) = self.source_revision.checked_add(1) {
            self.source_revision = next;
        } else {
            self.context_identity = ContextIdentity::fresh();
            self.source_revision = 0;
        }
    }

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
        self.symbol_info_with_signature(name, arg_sorts, ret_sort)
            .is_some()
    }

    /// Return the unique live declaration with this exact surface name and
    /// signature. The associated core identity is available through
    /// [`Self::symbol_identity_name`].
    pub fn symbol_info_with_signature(
        &self,
        name: &str,
        arg_sorts: &[Sort],
        ret_sort: &Sort,
    ) -> Option<&SymbolInfo> {
        let candidates = self
            .overloaded_symbols
            .get(name)
            .map(Vec::as_slice)
            .or_else(|| self.symbols.get(name).map(std::slice::from_ref))?;
        let mut matches = candidates
            .iter()
            .filter(|info| info.arg_sorts == arg_sorts && &info.sort == ret_sort);
        let first = matches.next()?;
        if matches.next().is_some() {
            return None;
        }
        Some(first)
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
            context_identity: ContextIdentity::fresh(),
            source_revision: 0,
            terms: TermStore::new(),
            symbols: HashMap::default(),
            internal_symbols: ay_core::kani_compat::DetHashSet::default(),
            overloaded_symbols: HashMap::default(),
            next_overload_identity: 0,
            declaration_core_identities_used: HashSet::default(),
            next_sort_identity: 0,
            sort_core_identities_used: HashSet::default(),
            nominal_sort_surfaces: HashMap::default(),
            sort_defs: HashMap::default(),
            public_sort_defs: HashMap::default(),
            parametric_sort_defs: HashMap::default(),
            sort_parameters: ay_core::kani_compat::DetHashSet::default(),
            polymorphic_declarations: Vec::new(),
            instantiating_polymorphic_declaration: false,
            polymorphic_assertions: Vec::new(),
            authored_assertions: Vec::new(),
            materialized_polymorphic_assertions: 0,
            polymorphic_instantiation_complete: true,
            elaborating_polymorphic_instance: false,
            expanding_sort_synonyms: Vec::new(),
            fun_defs: HashMap::default(),
            adopted_macro_interps: HashMap::default(),
            adopted_macro_declaration_ids: HashMap::default(),
            #[cfg(test)]
            fail_next_assert_after_macro_adoption: false,
            recursive_fun_names: ay_core::kani_compat::DetHashSet::default(),
            datatypes: HashMap::default(),
            live_datatype_carriers: HashSet::default(),
            monomorphic_datatype_decs: HashMap::default(),
            constructors: HashMap::default(),
            ctor_selectors: HashMap::default(),
            ctor_selector_info: HashMap::default(),
            nullary_ctor_terms: HashMap::default(),
            datatype_member_symbols: HashMap::default(),
            parametric_datatypes: HashMap::default(),
            parametric_datatype_ids: HashMap::default(),
            parametric_instance_args: HashMap::default(),
            parametric_instance_sorts: HashMap::default(),
            dt_internal_surface: HashMap::default(),
            dt_field_surface: HashMap::default(),
            logic: None,
            strict_logic_compliance: false,
            logic_set_by_command: false,
            assertions: Vec::new(),
            assertion_finite_set_metadata: Vec::new(),
            assertions_parsed: Vec::new(),
            retain_parsed_assertions: true,
            objectives: Vec::new(),
            objective_finite_set_metadata: Vec::new(),
            soft_constraints: Vec::new(),
            soft_finite_set_metadata: Vec::new(),
            scopes: Vec::new(),
            scope_commands_used: false,
            check_sat_commands: 0,
            native_global_declaration: false,
            options,
            numeral_as_real: false,
            int_real_coercions: true,
            named_terms: HashMap::default(),
            z3_debug_exprs: HashMap::default(),
            fun_expansion_depth: 0,
            multivar_lambda_curry_allowed: false,
            uses_multiset: false,
            uses_set: false,
            special_relations: HashMap::default(),
            lenient_sort_coercions: false,
            finite_set_typing_mode: FiniteSetTypingMode::default(),
        }
    }

    /// Enable/disable the legacy lenient `=`/`distinct`/`ite` sort coercions
    /// (default off — z3 4.15.4 parity, which rejects ill-sorted operands).
    /// Enabling restores the #5115 BitVec-width zero-extension leniency.
    pub fn set_lenient_sort_coercions(&mut self, lenient: bool) {
        if self.lenient_sort_coercions != lenient {
            self.lenient_sort_coercions = lenient;
            self.advance_source_revision();
        }
    }

    /// Whether legacy lenient sort coercions are enabled (see
    /// [`set_lenient_sort_coercions`](Self::set_lenient_sort_coercions)).
    pub fn lenient_sort_coercions(&self) -> bool {
        self.lenient_sort_coercions
    }

    /// Select public typing for Z3 5.0.0 finite-set spellings.
    ///
    /// API adapters implementing Z3's parser select
    /// [`FiniteSetTypingMode::Z3_5Strict`]. The default retains AY's older
    /// textual `Set` extension for compatibility.
    pub fn set_finite_set_typing_mode(&mut self, mode: FiniteSetTypingMode) {
        if self.finite_set_typing_mode != mode {
            self.finite_set_typing_mode = mode;
            self.advance_source_revision();
        }
    }

    /// Current finite-set public typing policy.
    #[must_use]
    pub fn finite_set_typing_mode(&self) -> FiniteSetTypingMode {
        self.finite_set_typing_mode
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

    /// Whether this session is a SINGLE-SHOT query: no `push`/`pop` command was
    /// ever processed and at most one `check-sat` has run.
    ///
    /// This is the precondition a diagnostic consumer needs before treating
    /// [`Self::assertions_parsed`] as "the assertion set of the check-sat whose
    /// verdict I am accompanying". With scopes or repeated check-sats, that
    /// identification needs per-check-sat bookkeeping the surface-syntax export
    /// does not carry, and getting it wrong means certifying a set that is not
    /// the query — e.g. an assertion made inside a `push` that was popped before
    /// the check-sat being reported. Consumers must DECLINE when this is false.
    ///
    /// Deliberately conservative: it counts the check-sat currently being
    /// answered, so it is `true` for the ordinary
    /// `assert*; check-sat` file and `false` from the second check-sat onwards.
    #[must_use]
    pub const fn is_single_shot_query(&self) -> bool {
        !self.scope_commands_used && self.check_sat_commands <= 1
    }

    /// Set the logic for this context.
    pub fn set_logic(&mut self, logic: String) {
        if self.logic.as_ref() != Some(&logic) {
            self.logic = Some(logic);
            self.advance_source_revision();
        }
    }

    /// Retarget the logic slot for an INTERNAL sub-solve, returning the token
    /// that puts it back.
    ///
    /// WHY THIS EXISTS. `source_revision` is the second half of
    /// [`SourceContextStamp`], and the mandatory UNSAT gate
    /// (`Executor::authenticate_unsat_query_scope`) rejects a refutation whose
    /// stamp no longer equals the one captured when the public query was bound
    /// — "the public UNSAT source context is no longer current". That test is
    /// meant to catch the source/declaration scope CHANGING under a bound
    /// query.
    ///
    /// An internal lane that borrows the logic slot and puts it back changes
    /// nothing observable, yet `set_logic` A -> B -> A advances the revision
    /// TWICE, so the stamp never returns to its captured value. Measured on
    /// `group_fp::fp_congruence::uf_over_float32_is_congruent_under_fp_to_real`:
    /// the `fp.to_real` two-phase lane
    /// (`Executor::solve_rewritten_mixed_subproblem`) infers a logic for its
    /// FP-free subproblem and restores the caller's on exit; revisions 6 and 7
    /// are those two writes and nothing else, and the correct `unsat` was
    /// discarded as stale. The context that decided the query is byte-for-byte
    /// the context that was bound.
    ///
    /// FAIL-CLOSED BY CONSTRUCTION. The revision is rolled back ONLY when this
    /// borrow's own two writes are the only ones that happened: the token
    /// records the revision immediately after the outbound write, and
    /// [`Self::end_internal_logic_borrow`] restores the saved revision only if
    /// the live revision still equals it. Any declaration, assertion-scope
    /// change, push/pop, or option write inside the borrow advances it past
    /// that mark, and then the revision is left advanced and the query
    /// correctly reads as stale. So this can never hide a real source change —
    /// it can only stop counting a no-op.
    #[must_use = "the borrow must be ended with `end_internal_logic_borrow`"]
    pub fn begin_internal_logic_borrow(&mut self, logic: String) -> InternalLogicBorrow {
        let saved_logic = self.logic.clone();
        let saved_revision = self.source_revision;
        self.set_logic(logic);
        InternalLogicBorrow {
            saved_logic,
            saved_revision,
            entry_revision: self.source_revision,
        }
    }

    /// Put back the logic (and, when nothing else moved, the source revision)
    /// captured by [`Self::begin_internal_logic_borrow`].
    pub fn end_internal_logic_borrow(&mut self, borrow: InternalLogicBorrow) {
        let InternalLogicBorrow {
            saved_logic,
            saved_revision,
            entry_revision,
        } = borrow;
        // Only this borrow's outbound write may have moved the revision. If
        // anything else did, the source context genuinely changed and the
        // rollback below is withheld.
        let untouched = self.source_revision == entry_revision;
        match saved_logic {
            Some(logic) => self.set_logic(logic),
            // The caller had no logic at all. `set_logic` cannot express that,
            // and clearing it is not this borrow's business — leave the
            // inferred logic in place and, because the context DID observably
            // change, keep the advanced revision.
            None => return,
        }
        if untouched {
            self.source_revision = saved_revision;
        }
    }

    /// Install the logic the way an API CONSTRUCTOR does: the logic takes
    /// effect, but no `(set-logic ...)` is recorded as having been seen in the
    /// COMMAND STREAM, so a script parsed afterwards may still carry its own —
    /// including one naming a different logic.
    ///
    /// This mirrors z3, where "the logic has already been set" is parser state:
    /// `Z3_mk_solver_for_logic` / `SolverFor(L)` does not touch it, and a
    /// subsequently parsed `(set-logic M)` is accepted even when `M != L`.
    /// Going through `Command::SetLogic` here instead would mark the origin and
    /// reject the first `(set-logic ...)` of every script the caller parses.
    ///
    /// # Errors
    /// Propagates the same validation `Command::SetLogic` performs.
    pub fn set_initial_logic(&mut self, logic: &str) -> Result<()> {
        self.validate_logic_sort_parameter_conflicts(logic)?;
        self.set_logic(logic.to_string());
        self.refresh_polymorphic_declarations()?;
        Ok(())
    }

    /// Select whether official SMT-LIB logic declarations are enforced as
    /// language boundaries instead of being treated only as routing hints.
    pub fn set_strict_logic_compliance(&mut self, strict: bool) {
        self.strict_logic_compliance = strict;
    }

    /// Get the parsed assertions (original surface syntax).
    pub fn assertions_parsed(&self) -> &[ParsedTerm] {
        &self.assertions_parsed
    }

    /// Return user-authored assertions in source order for `get-assertions`.
    ///
    /// Query-local monomorphic instances of schematic assertions are
    /// intentionally absent: SMT-LIB asks for the authored assertion stack,
    /// before elaboration and independently of whether `check-sat` has run.
    pub fn authored_assertions_for_display(&self) -> Vec<AuthoredAssertionRef<'_>> {
        if self.authored_assertions.is_empty() {
            // Native API clients can append TermIds without a surface command.
            // Preserve the historical useful fallback for that path.
            return self
                .assertions
                .iter()
                .copied()
                .map(AuthoredAssertionRef::Elaborated)
                .collect();
        }
        self.authored_assertions
            .iter()
            .map(|assertion| match assertion {
                AuthoredAssertion::Concrete {
                    term, parsed_index, ..
                } => parsed_index
                    .and_then(|index| self.assertions_parsed.get(index))
                    .map_or(AuthoredAssertionRef::Elaborated(*term), |parsed| {
                        AuthoredAssertionRef::Parsed(parsed)
                    }),
                AuthoredAssertion::Schematic(parsed) => AuthoredAssertionRef::Parsed(parsed),
            })
            .collect()
    }

    /// Exact elaborated terms introduced by authored, concrete `assert`
    /// commands, in source order.
    ///
    /// This deliberately has no fallback to the mutable solver assertion
    /// stack: that stack may also contain transient axioms and preprocessing
    /// artifacts.  Schematic assertions likewise have no single concrete term
    /// until query-local instantiation and are omitted.
    #[doc(hidden)]
    pub fn concrete_authored_assertion_terms(&self) -> Vec<TermId> {
        self.authored_assertions
            .iter()
            .filter_map(|assertion| match assertion {
                AuthoredAssertion::Concrete { term, .. } => Some(*term),
                AuthoredAssertion::Schematic(_) => None,
            })
            .collect()
    }

    /// Exact concrete-authored terms only when every retained parsed row is
    /// still paired with its original authored assertion at the same index.
    ///
    /// The row counts and indices are checked before allocating. This is the
    /// fail-closed proof-export accessor: query-local/transient parsed rows,
    /// retention gaps, and rows removed by scope or stack truncation cannot be
    /// mistaken for immutable authored source.
    #[doc(hidden)]
    pub fn concrete_authored_assertion_terms_aligned_bounded(
        &self,
        max_rows: usize,
    ) -> Option<Vec<TermId>> {
        if self.assertions_parsed.len() > max_rows || self.authored_assertions.len() > max_rows {
            return None;
        }

        let mut concrete_count = 0usize;
        for assertion in &self.authored_assertions {
            let AuthoredAssertion::Concrete { parsed_index, .. } = assertion else {
                continue;
            };
            if *parsed_index != Some(concrete_count) {
                return None;
            }
            concrete_count += 1;
        }
        if concrete_count != self.assertions_parsed.len() {
            return None;
        }

        Some(
            self.authored_assertions
                .iter()
                .filter_map(|assertion| match assertion {
                    AuthoredAssertion::Concrete { term, .. } => Some(*term),
                    AuthoredAssertion::Schematic(_) => None,
                })
                .collect(),
        )
    }

    /// Exact terms whose authored source was literally `false`.
    ///
    /// This compact provenance survives parsed-AST retention being disabled,
    /// where keeping only the canonical TermId would conflate literal false
    /// with every source formula that constant-folded to false.
    #[doc(hidden)]
    pub fn concrete_authored_literal_false_terms(&self) -> Vec<TermId> {
        self.authored_assertions
            .iter()
            .filter_map(|assertion| match assertion {
                AuthoredAssertion::Concrete {
                    term,
                    source_is_literal_false: true,
                    ..
                } => Some(*term),
                _ => None,
            })
            .collect()
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

    /// The floating-point format of every NULLARY symbol — both
    /// `declare-const`/`declare-fun` constants and parameter-less `define-fun`
    /// macros. `Some((eb, sb))` for a floating-point sort, `None` for any
    /// other sort.
    ///
    /// [`Context::assertions_parsed`] hands consumers the ORIGINAL surface
    /// syntax, in which [`ParsedTerm::Symbol`] carries no sort at all. A
    /// proof/lean-export consumer whose soundness depends on the format (e.g.
    /// a binary64-only forward-error certificate: the SAME parsed assertion
    /// terms are UNSAT at `Float64` and SATISFIABLE at `Float32`) cannot
    /// recover it from the terms and must consult this table.
    ///
    /// The format is read off the ELABORATED [`ay_core::Sort::FloatingPoint`],
    /// never off a sort NAME: `Float64`, `(_ FloatingPoint 11 53)` and a
    /// `define-sort` synonym of either all resolve to the same `(11, 53)`
    /// pair, while a user-declared sort cannot masquerade as one (the
    /// theory-sort names are reserved by `ensure_sort_name_available`).
    ///
    /// A name is OMITTED ENTIRELY whenever its format is not unambiguous — an
    /// overloaded surface name, or a name whose constant and macro entries
    /// disagree. "Absent" and "present with `None`" are therefore different
    /// answers: absent means UNKNOWN, and a consumer that requires a specific
    /// format must decline on it, exactly as it declines on a wrong format.
    ///
    /// This is a diagnostic export surface; it does not affect the solver's own
    /// (already fully-elaborated) reasoning.
    pub fn nullary_fp_formats(&self) -> Vec<(String, Option<(u32, u32)>)> {
        let fp_of = |sort: &Sort| match *sort {
            Sort::FloatingPoint(eb, sb) => Some((eb, sb)),
            _ => None,
        };
        let mut out: Vec<(String, Option<(u32, u32)>)> = Vec::new();
        for (name, info) in self.symbol_iter() {
            if !info.arg_sorts.is_empty() || self.overloaded_symbols.contains_key(name) {
                continue;
            }
            out.push((name.clone(), fp_of(&info.sort)));
        }
        for (name, (params, ret, _)) in &self.fun_defs {
            if params.is_empty() {
                out.push((name.clone(), fp_of(ret)));
            }
        }
        out.sort();
        out.dedup();
        // Drop every name that survived with two DIFFERENT answers: the surface
        // name does not determine one, so no consumer may pick.
        let ambiguous: Vec<String> = out
            .windows(2)
            .filter(|w| w[0].0 == w[1].0)
            .map(|w| w[0].0.clone())
            .collect();
        out.retain(|(name, _)| !ambiguous.contains(name));
        out
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
        let source_is_literal_false = authored_source_is_literal_false(&parsed);
        let parsed_index = self.push_assertion_stacks(term, parsed);
        self.authored_assertions.push(AuthoredAssertion::Concrete {
            term,
            parsed_index,
            source_is_literal_false,
        });
    }

    /// Push a solver-generated query-local assertion without changing the
    /// authored `(get-assertions)` history.
    ///
    /// This is public only for the solver crate. The caller must restore the
    /// assertion stacks with [`Self::truncate_assertions`] on every exit path.
    #[doc(hidden)]
    pub fn add_transient_assertion_with_parsed(&mut self, term: TermId, parsed: ParsedTerm) {
        self.push_assertion_stacks(term, parsed);
    }

    fn push_assertion_stacks(&mut self, term: TermId, parsed: ParsedTerm) -> Option<usize> {
        let parsed_index = (self.retain_parsed_assertions
            && self.assertions_parsed.len() == self.assertions.len())
        .then_some(self.assertions_parsed.len());
        if parsed_index.is_some() {
            self.assertions_parsed.push(parsed);
        }
        self.assertions.push(term);
        self.assertion_finite_set_metadata
            .push(PublicAssertionMetadata::default());
        parsed_index
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

    /// Whether new assertions retain their parsed source trees for proof
    /// surface alignment.
    #[must_use]
    pub const fn retains_parsed_assertions(&self) -> bool {
        self.retain_parsed_assertions
    }

    /// Replace the complete active query view with exact internal probe roots.
    ///
    /// This is a narrow cross-crate transaction primitive for solver probes
    /// that must keep the original term arena. It hides every query-local input
    /// that could strengthen, redirect, or misattribute the derived solve while
    /// preserving declarations, options, and scope identities. `roots` must be
    /// live Boolean terms in this context; validation happens before any state
    /// is changed.
    ///
    /// The returned affine window must be passed to
    /// [`Self::restore_internal_query_window`] on every exit path. In
    /// particular, callers moving this context into another owner should put
    /// the pair behind an RAII guard so unwinding cannot strand the enclosing
    /// query in the temporary view.
    ///
    /// # Errors
    ///
    /// Returns an error without mutation when a root is not live in this term
    /// arena or is not Boolean-sorted.
    #[doc(hidden)]
    pub fn begin_internal_query_window(
        &mut self,
        roots: Vec<TermId>,
    ) -> std::result::Result<InternalQueryWindow, ElaborateError> {
        for &root in &roots {
            if self.terms.entry_stamp(root).is_none() {
                return Err(ElaborateError::Unsupported(format!(
                    "internal query root {root} is not live in this term arena"
                )));
            }
            let sort = self.terms.sort(root);
            if sort != &Sort::Bool {
                return Err(ElaborateError::SortMismatch {
                    expected: "Bool".to_string(),
                    actual: format!("{sort:?}"),
                });
            }
        }

        // Allocate the replacement metadata before taking any outer state so
        // an allocation panic cannot leave a half-installed query window.
        let probe_metadata = vec![PublicAssertionMetadata::default(); roots.len()];
        let source_context_stamp = self.source_context_stamp();
        let term_prefix = self.terms.snapshot_stamp();
        let window = InternalQueryWindow {
            source_context_stamp,
            term_prefix,
            assertions: std::mem::replace(&mut self.assertions, roots),
            assertion_finite_set_metadata: std::mem::replace(
                &mut self.assertion_finite_set_metadata,
                probe_metadata,
            ),
            assertions_parsed: std::mem::take(&mut self.assertions_parsed),
            retain_parsed_assertions: std::mem::replace(&mut self.retain_parsed_assertions, false),
            objectives: std::mem::take(&mut self.objectives),
            objective_finite_set_metadata: std::mem::take(&mut self.objective_finite_set_metadata),
            soft_constraints: std::mem::take(&mut self.soft_constraints),
            soft_finite_set_metadata: std::mem::take(&mut self.soft_finite_set_metadata),
            named_terms: std::mem::take(&mut self.named_terms),
            polymorphic_assertions: std::mem::take(&mut self.polymorphic_assertions),
            authored_assertions: std::mem::take(&mut self.authored_assertions),
            materialized_polymorphic_assertions: std::mem::replace(
                &mut self.materialized_polymorphic_assertions,
                0,
            ),
            polymorphic_instantiation_complete: std::mem::replace(
                &mut self.polymorphic_instantiation_complete,
                true,
            ),
        };
        Ok(window)
    }

    /// Restore a query view saved by [`Self::begin_internal_query_window`].
    ///
    /// Restoration itself is allocation-free and always puts the saved vectors,
    /// maps, and policy bits back. The Boolean result additionally authenticates
    /// that the same source context and an append-only extension of the same
    /// term arena survived the probe. Callers must discard every derived
    /// verdict/model capability when it is `false`.
    #[doc(hidden)]
    pub fn restore_internal_query_window(&mut self, window: InternalQueryWindow) -> bool {
        let source_is_current = window.source_context_stamp == self.source_context_stamp();
        let term_prefix_is_current = window.term_prefix.is_append_only_prefix_of(&self.terms);
        let InternalQueryWindow {
            source_context_stamp: _,
            term_prefix: _,
            assertions,
            assertion_finite_set_metadata,
            assertions_parsed,
            retain_parsed_assertions,
            objectives,
            objective_finite_set_metadata,
            soft_constraints,
            soft_finite_set_metadata,
            named_terms,
            polymorphic_assertions,
            authored_assertions,
            materialized_polymorphic_assertions,
            polymorphic_instantiation_complete,
        } = window;
        self.assertions = assertions;
        self.assertion_finite_set_metadata = assertion_finite_set_metadata;
        self.assertions_parsed = assertions_parsed;
        self.retain_parsed_assertions = retain_parsed_assertions;
        self.objectives = objectives;
        self.objective_finite_set_metadata = objective_finite_set_metadata;
        self.soft_constraints = soft_constraints;
        self.soft_finite_set_metadata = soft_finite_set_metadata;
        self.named_terms = named_terms;
        self.polymorphic_assertions = polymorphic_assertions;
        self.authored_assertions = authored_assertions;
        self.materialized_polymorphic_assertions = materialized_polymorphic_assertions;
        self.polymorphic_instantiation_complete = polymorphic_instantiation_complete;
        source_is_current && term_prefix_is_current
    }

    /// Get the optimization objectives.
    pub fn objectives(&self) -> &[Objective] {
        &self.objectives
    }

    /// Add an optimization objective.
    pub fn add_objective(&mut self, objective: Objective) {
        self.objectives.push(objective);
        self.objective_finite_set_metadata
            .push(PublicAssertionMetadata::default());
    }

    /// Get the soft (weighted) constraints from `(assert-soft ...)`.
    pub fn soft_constraints(&self) -> &[SoftAssertion] {
        &self.soft_constraints
    }

    /// Add a soft (weighted) constraint.
    pub(crate) fn add_soft_constraint(&mut self, soft: SoftAssertion) {
        self.soft_constraints.push(soft);
        self.soft_finite_set_metadata
            .push(PublicAssertionMetadata::default());
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

    /// The reserved-name gate for a declaration arriving on THIS route.
    ///
    /// `native_global_declaration` is set exactly while a declaration comes
    /// from the in-process native API (`Context::execute_native_global_
    /// declaration`, i.e. `Solver::try_declare_fun`/`try_declare_datatype` and
    /// the `register_native_global_*` helpers) — the route AY's own Z3 C
    /// surface uses to mint its `!ay.*` engine witnesses. That route therefore
    /// keeps the narrower [`is_reserved_symbol`] gate. Every other caller is
    /// untrusted SMT-LIB source text, which has minting authority over no
    /// internal namespace at all and gets the full
    /// [`is_source_reserved_symbol`] union.
    ///
    /// Both predicates are derived from the single [`INTERNAL_NAMESPACES`]
    /// table, so widening or narrowing a namespace updates both routes and the
    /// FFI's own gate together.
    ///
    /// This gate is UNCONDITIONAL on the active logic: `set-logic` selects which
    /// theories are available, never which names AY itself mints, and every
    /// reserved theory-operator spelling is matched structurally by name+arity
    /// with no sort check. Narrowing it per-logic would need every surface-name
    /// interception path to first defer to a declared symbol; only `const` does
    /// (see `EXCLUDED_DECLARABLE_OP_NAMES`), so the rest stay refused.
    pub(crate) fn is_reserved_symbol_on_this_route(&self, name: &str) -> bool {
        if self.native_global_declaration {
            is_reserved_symbol(name)
        } else {
            is_source_reserved_symbol(name)
        }
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

    pub(crate) fn track_scoped_datatype(&mut self, internal: String, surface: String) {
        if self.global_declarations_enabled() {
            return;
        }
        if let Some(frame) = self.scopes.last_mut() {
            frame.datatypes.push((internal, surface));
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

    /// Record how a freshly minted single-constructor field constant should be
    /// rendered for external proof checkers (see [`DtFieldSurface`]).
    fn record_dt_field_surface(&mut self, term: TermId, surface: DtFieldSurface) {
        self.dt_field_surface.insert(term, surface);
    }

    /// `TermId` -> selector-application rendering for the solver-invented
    /// single-constructor field constants, for use as Alethe printer term
    /// overrides (see [`DtFieldSurface`] for the defect this repairs).
    ///
    /// Every entry is RE-VALIDATED here rather than trusted from mint time,
    /// because both ways a rendering can go stale are created by LATER
    /// commands, and printing a term as something it is not would mean the
    /// checker verifies a different statement than the one AY proved:
    ///
    /// * **Rebinding.** `(push) (declare-const s Rec) (pop) (declare-const s
    ///   Other)` leaves the OLD field terms alive in the store while `s` now
    ///   names a different constant. The guard walks `path` from whatever `s`
    ///   is bound to RIGHT NOW and keeps the entry only if the walk lands back
    ///   on this exact `TermId` — so the rendering is re-derived, not assumed.
    /// * **Shadowing.** An external checker's symbol table is FLAT and
    ///   LAST-DECLARATION-WINS (measured on carcara 1.1.0). A selector name
    ///   bound more than once may resolve to the other binding: loudly when the
    ///   signatures differ, but SILENTLY when they match — the checker would
    ///   then verify an application of an unrelated uninterpreted function and
    ///   report `valid` for something that is not a proof about the datatype.
    ///
    /// Withholding costs nothing beyond the status quo: the term simply prints
    /// as its bare invented name, which is exactly today's (already
    /// unreadable) output — never a wrong answer.
    #[must_use]
    pub fn dt_field_surface_overrides(&self) -> HashMap<TermId, String> {
        let mut overrides: HashMap<TermId, String> = HashMap::default();
        if self.dt_field_surface.is_empty() {
            return overrides;
        }
        let ambiguous = self.ambiguous_selector_names();
        for (term, field) in &self.dt_field_surface {
            if field
                .selectors
                .iter()
                .any(|selector| ambiguous.contains(selector))
            {
                continue;
            }
            if self.field_term_at(field) != Some(*term) {
                continue;
            }
            overrides.insert(*term, field.rendering.clone());
        }
        overrides
    }

    /// The term reached by following `field.path` (positional constructor-
    /// argument indices) from the exact root declaration, or `None` if that
    /// declaration is no longer present or the walk does not fit.
    ///
    /// An unqualified overloaded root is rejected outright. A qualified root
    /// is safe only when result sort plus private identity select exactly one
    /// current nullary declaration — the same resolution the checker applies
    /// to `(as root sort)`.
    fn field_term_at(&self, field: &DtFieldSurface) -> Option<TermId> {
        let mut current = if field.qualified_root {
            let candidates: &[SymbolInfo] = self
                .overloaded_symbols
                .get(&field.root_surface)
                .map(Vec::as_slice)
                .or_else(|| {
                    self.symbols
                        .get(&field.root_surface)
                        .map(std::slice::from_ref)
                })?;
            let mut matches = candidates.iter().filter(|info| {
                info.arg_sorts.is_empty()
                    && info.sort == field.root_sort
                    && info.internal_name.as_deref() == field.root_internal_name.as_deref()
            });
            let root = matches.next()?.term?;
            if matches.next().is_some() {
                return None;
            }
            root
        } else {
            if self.overloaded_symbols.contains_key(&field.root_surface) {
                return None;
            }
            self.symbols.get(&field.root_surface)?.term?
        };
        for &index in &field.path {
            let ay_core::TermData::App(_, args) = self.terms.get(current) else {
                return None;
            };
            current = *args.get(index)?;
        }
        Some(current)
    }

    /// Surface selector names an external checker may not resolve to the
    /// intended selector: reused by another registered constructor (including
    /// a second instance of a parametric datatype), or also bound by a
    /// `define-fun`. The reverse collision — a `declare-fun`/`declare-const`/
    /// `define-fun` that takes over a name already registered as a datatype
    /// member — cannot arise here: those paths reject it up front with
    /// [`ElaborateError::DatatypeMemberCollision`] (#reserved-ops).
    fn ambiguous_selector_names(&self) -> ay_core::kani_compat::DetHashSet<String> {
        let mut counts: HashMap<String, usize> = HashMap::default();
        for (constructor, selectors) in &self.ctor_selector_info {
            if !self.is_live_datatype_member_identity(constructor) {
                continue;
            }
            for (selector, _) in selectors {
                let surface = self.dt_surface_name(selector).unwrap_or(selector);
                *counts.entry(surface.to_string()).or_insert(0) += 1;
            }
        }
        counts
            .into_iter()
            .filter(|(name, count)| *count > 1 || self.fun_defs.contains_key(name))
            .map(|(name, _)| name)
            .collect()
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
    /// Need to retrieve labels from the last solver result.
    Labels,
    /// Need to get current assertions
    GetAssertions,
    /// Need to print a string (echo command)
    Echo(String),
    /// Need to print a validated authored term without rewriting it.
    Display(String),
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
mod derived_query;
pub use declarations::IntroKind;
mod indexed;
mod public_sorts;
pub use public_sorts::{
    FiniteSetOp, FiniteSetTermMetadata, PublicAssertionMetadata, PublicSort, PublicSymbolSignature,
    PublicTermMetadata,
};
mod logic_policy;
mod qualified;
mod sort_parameters;
mod sorts;
mod term;

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;
