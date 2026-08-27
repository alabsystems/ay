// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Catamorphism abstraction for recursive-ADT CHC problems (CHC-COMP agenda #7,
//! "CATA v1").
//!
//! Reimplements — from the competitor-brief description only — the abstraction
//! of ChocoCatalia / "CHC Satisfiability via Catamorphic Abstractions"
//! (De Angelis–Fioravanti–Pettorossi–Proietti, TPLP 2024; foundations:
//! Suter–Dotta–Kuncak, POPL'10). No competitor code was consulted.
//!
//! # Transformation
//!
//! Every ADT-sorted predicate argument `x` is replaced by a tuple of integer
//! *catamorphism values* `c(x) = (cata_1(x), …, cata_k(x))`, producing a pure
//! LIA CHC system. The v1 catamorphism pool is fixed:
//!
//! - `Size`      — total node count: `size(C(f̄)) = 1 + Σ_{ADT fields} size(f)`
//! - `Height`    — tree height: `height(C(f̄)) = 1 + max_{ADT fields} height(f)`
//! - `IntSum`    — recursive sum of integer fields:
//!   `intsum(C(f̄)) = Σ_{Int fields} f + Σ_{ADT fields} intsum(f)`
//! - `CtorCount(C)` — occurrences of constructor `C` in the whole tree
//! - `RootDisc`  — index of the root constructor (non-recursive)
//!
//! Clause constraints are abstracted conjunct-by-conjunct:
//!
//! - ADT equality `t1 = t2`      → tuple equality `c(t1) = c(t2)`
//! - ADT disequality             → dropped (information loss = the abstraction);
//!   except `t ≠ NullaryCtor` on a two-constructor sort, which yields the other
//!   constructor's tester consequences plus an exact `RootDisc` disequality
//! - tester `(_ is C)(t)`        → catamorphism consequences (e.g.
//!   `size(t) = 1` for a leaf constructor, `size(t) ≥ 1 + n` otherwise,
//!   `rootdisc(t) = index(C)` exactly)
//! - constructor terms `C(t̄)`    → their defining recurrences over sub-tuples
//! - conjuncts with no ADT subterm → kept verbatim
//! - anything else               → dropped (weakened to `true`, which
//!   over-approximates and is therefore sound for the SAT direction)
//!
//! Additionally every catamorphism tuple gets its universally-true "min facts"
//! (`size ≥ 1`, `height ≥ 1`, `count ≥ 0`, `0 ≤ rootdisc < #ctors`).
//!
//! # Soundness (the load-bearing part)
//!
//! Direction of the abstraction: for every clause with constraint `θ` and
//! abstract constraint `θ#`,
//!
//! ```text
//!     θ  ⇒  θ#[ cata(t) / c_t ]           (per-clause implication obligation)
//! ```
//!
//! If this holds for every clause and `M#` is a model of the abstract system,
//! then `P(x̄, ȳ) := M#[P#](cata(x̄), ȳ)` is a model of the ORIGINAL system —
//! i.e. **abstract SAT ⇒ original SAT**. Abstract UNSAT proves NOTHING about
//! the original (the abstraction only over-approximates derivations); callers
//! must concretize any abstract counterexample on the original clauses and
//! replay it through the standard verified-unsafe pipeline, refining (adding
//! the next catamorphism) when concretization fails.
//!
//! The per-clause implication obligations are NOT trusted by construction:
//! [`CataAbstraction::discharge_obligations`] checks each one with a fresh
//! ADT+LIA+UF SMT query (fail-closed — any `sat`/`unknown`/error kills the
//! lane). The encoding declares one uninterpreted function per (catamorphism,
//! sort), asserts only facts that are TRUE of the real catamorphism (its
//! defining recurrences instantiated at the clause's constructor terms, a
//! one-level unfolding case-split per abstracted term, and the min facts), and
//! checks `θ ∧ facts ∧ ¬θ#` UNSAT. Because the real catamorphisms are one
//! admissible interpretation of the UFs, UNSAT here certifies the implication
//! for the real catamorphisms. `define-fun-rec` was evaluated and rejected:
//! ay-frontend expands recursive definitions by bounded macro expansion, which
//! diverges on symbolic ADT arguments, so it cannot discharge these
//! obligations (per the agenda: "certify by per-clause induction obligations
//! or WITHHOLD").
//!
//! Composed SAT models materialize `cata_k(x)` as [`ChcExpr::FuncApp`] terms
//! with reserved names (`__ay_cata_<kind>@<sort>`). Downstream re-checks that
//! treat those symbols as uninterpreted are strictly conservative: an
//! unconstrained UF admits more behaviours than the real catamorphism, so a
//! query-clause discharge that succeeds under the UF reading also holds for
//! the real semantics; one that fails merely demotes to unknown.

use std::cell::Cell;
use std::sync::Arc;
use std::time::Duration;
// The workspace-wide monotonic clock shim (#wasm port): byte-identical to
// `std::time::Instant` on native targets, host-clock-backed on wasm32 (raw
// `std::time::Instant` panics there and breaks the wasm build).
use ay_core::time::Instant;

use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::collections::{BTreeMap, BTreeSet};

use crate::smt::executor_adapter::{quote_symbol, sort_to_smtlib};
use crate::{
    ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause, InvariantModel,
    PredicateId, PredicateInterpretation,
};

use super::{
    BackTranslator, InvalidityWitness, TransformMemoryReport, TransformObligation,
    TransformationResult, Transformer, ValidityWitness,
};

/// CATA v2: multi-predicate affine Houdini solver for the abstract LIA problem.
pub(crate) mod affine_houdini;
pub(crate) mod disj_abstract;
/// CATA v3: Horn-ICE decision-tree learner (generalizing disjunctive learner).
pub(crate) mod ice_dt;

/// Per-clause cap on distinct abstracted ADT terms (tuple explosion guard).
const MAX_TUPLES_PER_CLAUSE: usize = 64;
/// Cap on total constructors before the `CtorCount` ladder level is skipped.
const MAX_CTOR_COUNT_COLUMNS: usize = 8;

/// Sentinel value of `Min` on an element-free subtree (the `+∞` identity of
/// integer `min`). CATA v3, element catamorphisms. The value is a free choice:
/// soundness comes from the obligation certifying the recurrence we *actually*
/// assert of the `Min` UF — the sentinel is never claimed to be a real element,
/// only the neutral element of the fold. Kept above every constant the affine
/// layer mines (`harvest_constants` caps at `1_000_000`) so it never becomes a
/// spurious affine candidate.
const CATA_MIN_SENTINEL: i64 = 1_000_000_000;
/// Sentinel value of `Max` on an element-free subtree (the `-∞` identity of
/// integer `max`). Symmetric to [`CATA_MIN_SENTINEL`].
const CATA_MAX_SENTINEL: i64 = -1_000_000_000;

// ============================================================================
// Catamorphism pool
// ============================================================================

/// One catamorphism from the fixed v1 pool.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CataKind {
    /// Total node count across all (mutually) recursive ADT fields.
    Size,
    /// Tree height (`1 + max` over ADT fields; `1` for leaves).
    Height,
    /// Recursive sum of integer fields.
    IntSum,
    /// Number of occurrences of the named constructor in the whole tree.
    CtorCount(String),
    /// Index of the root constructor (non-recursive discriminant).
    RootDisc,
    /// Minimum integer element across the whole tree (element catamorphism,
    /// CATA v3). `min(C(f̄)) = min({Int fields} ∪ {min(ADT fields)})`; on an
    /// element-free subtree it is [`CATA_MIN_SENTINEL`] (`+∞`).
    Min,
    /// Maximum integer element across the whole tree (element catamorphism).
    /// Symmetric to [`CataKind::Min`]; empty subtree is [`CATA_MAX_SENTINEL`].
    Max,
    /// Ascending-sortedness as a `0/1` integer fold (ordering catamorphism,
    /// CATA v3). `sorted(nil)=1`; `sorted(C(x, rest…)) = 1` iff every recursive
    /// field is sorted and the head element `x ≤ min(rest)`. It references the
    /// [`CataKind::Min`] column of its recursive fields, so `Min` MUST also be
    /// in the pool (the ladder guarantees this) — otherwise the head-vs-rest
    /// comparison cannot be expressed and the recurrence is withheld.
    Sorted,
}

impl CataKind {
    fn tag(&self) -> String {
        match self {
            Self::Size => "size".to_string(),
            Self::Height => "height".to_string(),
            Self::IntSum => "intsum".to_string(),
            Self::CtorCount(ctor) => format!("cc_{ctor}"),
            Self::RootDisc => "rootdisc".to_string(),
            Self::Min => "min".to_string(),
            Self::Max => "max".to_string(),
            Self::Sorted => "sorted".to_string(),
        }
    }

    /// Parse a reserved catamorphism UF symbol (`cata_<tag>@<sort>`) back
    /// into its kind and sort name. Inverse of [`CataKind::uf_name`].
    pub(crate) fn parse_symbol(name: &str) -> Option<(Self, &str)> {
        let rest = name.strip_prefix("cata_")?;
        let (tag, sort_name) = rest.split_once('@')?;
        let kind = match tag {
            "size" => Self::Size,
            "height" => Self::Height,
            "intsum" => Self::IntSum,
            "rootdisc" => Self::RootDisc,
            "min" => Self::Min,
            "max" => Self::Max,
            "sorted" => Self::Sorted,
            other => Self::CtorCount(other.strip_prefix("cc_")?.to_string()),
        };
        Some((kind, sort_name))
    }

    /// Reserved uninterpreted-function name for this catamorphism at a sort.
    ///
    /// NOTE: must NOT start with `__ay_` — the ay-frontend elaborator rejects
    /// declarations of that internal prefix, and the obligation scripts
    /// declare these symbols. The `@` separator keeps accidental collision
    /// with user symbols implausible (it forces SMT-LIB quoting).
    pub(crate) fn uf_name(&self, sort_name: &str) -> String {
        format!("cata_{}@{}", self.tag(), sort_name)
    }
}

// ============================================================================
// Datatype registry
// ============================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
enum FieldKind {
    /// Field of a (possibly mutually) recursive ADT sort, by name.
    Adt(String),
    /// Integer field (feeds `IntSum`).
    Int,
    /// Any other field sort (ignored by every catamorphism).
    Opaque,
}

#[derive(Debug, Clone)]
struct CtorField {
    selector: String,
    sort: ChcSort,
    kind: FieldKind,
}

#[derive(Debug, Clone)]
struct CtorInfo {
    name: String,
    index: usize,
    fields: Vec<CtorField>,
}

impl CtorInfo {
    fn adt_field_count(&self) -> usize {
        self.fields
            .iter()
            .filter(|f| matches!(f.kind, FieldKind::Adt(_)))
            .count()
    }
}

/// Name-keyed registry of every datatype sort reachable from the problem
/// signature. Field sorts that the parser left as `Uninterpreted(name)`
/// self-references are resolved by name against the registry.
#[derive(Debug, Clone)]
struct DtRegistry {
    /// Deterministically ordered: sort name → constructor metadata.
    sorts: BTreeMap<String, Vec<CtorInfo>>,
}

impl DtRegistry {
    fn build(problem: &ChcProblem) -> Self {
        // Pass 1: collect every datatype definition reachable from predicate
        // argument sorts (full metadata travels inside `ChcSort::Datatype`).
        let mut raw: BTreeMap<String, Vec<(String, Vec<(String, ChcSort)>)>> = BTreeMap::new();
        fn collect(
            sort: &ChcSort,
            out: &mut BTreeMap<String, Vec<(String, Vec<(String, ChcSort)>)>>,
        ) {
            match sort {
                ChcSort::Datatype { name, constructors } => {
                    if out.contains_key(name) {
                        return;
                    }
                    let ctors: Vec<(String, Vec<(String, ChcSort)>)> = constructors
                        .iter()
                        .map(|c| {
                            (
                                c.name.clone(),
                                c.selectors
                                    .iter()
                                    .map(|s| (s.name.clone(), s.sort.clone()))
                                    .collect(),
                            )
                        })
                        .collect();
                    out.insert(name.clone(), ctors);
                    for ctor in constructors.iter() {
                        for sel in &ctor.selectors {
                            collect(&sel.sort, out);
                        }
                    }
                }
                ChcSort::Array(k, v) => {
                    collect(k, out);
                    collect(v, out);
                }
                _ => {}
            }
        }
        for pred in problem.predicates() {
            for sort in &pred.arg_sorts {
                collect(sort, &mut raw);
            }
        }
        // Also pull in the problem-level datatype registry (covers clause-local
        // sorts that never appear in a predicate signature).
        for (name, ctors) in problem.datatype_defs() {
            raw.entry(name.clone()).or_insert_with(|| ctors.clone());
        }

        // Pass 2: classify fields against the full name set.
        let mut sorts = BTreeMap::new();
        let names: Vec<String> = raw.keys().cloned().collect();
        for (name, ctors) in &raw {
            let infos = ctors
                .iter()
                .enumerate()
                .map(|(index, (ctor_name, fields))| CtorInfo {
                    name: ctor_name.clone(),
                    index,
                    fields: fields
                        .iter()
                        .map(|(sel, sort)| CtorField {
                            selector: sel.clone(),
                            sort: sort.clone(),
                            kind: match sort {
                                ChcSort::Datatype { name, .. } => FieldKind::Adt(name.clone()),
                                ChcSort::Uninterpreted(n) if names.contains(n) => {
                                    FieldKind::Adt(n.clone())
                                }
                                ChcSort::Int => FieldKind::Int,
                                _ => FieldKind::Opaque,
                            },
                        })
                        .collect(),
                })
                .collect();
            sorts.insert(name.clone(), infos);
        }
        Self { sorts }
    }

    fn is_empty(&self) -> bool {
        self.sorts.is_empty()
    }

    /// Resolve an expression sort to a registered ADT sort name.
    fn adt_sort_name<'a>(&'a self, sort: &'a ChcSort) -> Option<&'a str> {
        match sort {
            ChcSort::Datatype { name, .. } => Some(name.as_str()),
            ChcSort::Uninterpreted(name) if self.sorts.contains_key(name) => Some(name.as_str()),
            _ => None,
        }
    }

    fn ctors(&self, sort_name: &str) -> Option<&[CtorInfo]> {
        self.sorts.get(sort_name).map(Vec::as_slice)
    }

    fn ctor(&self, sort_name: &str, ctor_name: &str) -> Option<&CtorInfo> {
        self.ctors(sort_name)?.iter().find(|c| c.name == ctor_name)
    }

    /// Constructor lookup by name across all sorts (constructor names are
    /// globally unique in SMT-LIB).
    fn ctor_sort(&self, ctor_name: &str) -> Option<(&str, &CtorInfo)> {
        for (sort_name, ctors) in &self.sorts {
            if let Some(info) = ctors.iter().find(|c| c.name == ctor_name) {
                return Some((sort_name.as_str(), info));
            }
        }
        None
    }

    fn is_dt_member_symbol(&self, name: &str) -> bool {
        if let Some(ctor) = name.strip_prefix("is-") {
            if self.ctor_sort(ctor).is_some() {
                return true;
            }
        }
        if self.ctor_sort(name).is_some() {
            return true;
        }
        self.sorts.values().any(|ctors| {
            ctors
                .iter()
                .any(|c| c.fields.iter().any(|f| f.selector == name))
        })
    }

    fn has_int_fields(&self) -> bool {
        self.sorts.values().any(|ctors| {
            ctors
                .iter()
                .any(|c| c.fields.iter().any(|f| matches!(f.kind, FieldKind::Int)))
        })
    }

    fn total_ctors(&self) -> usize {
        self.sorts.values().map(Vec::len).sum()
    }

    fn any_multi_recursive_ctor(&self) -> bool {
        self.sorts
            .values()
            .any(|ctors| ctors.iter().any(|c| c.adt_field_count() >= 2))
    }

    /// Is there an int-carrying *list-like* sort — a sort with a recursive
    /// constructor that has exactly one `Int` field and exactly one recursive
    /// `Adt` field of the same sort (cons of an int list)? Gates the ordering
    /// (`Sorted`) catamorphism, whose ascending-sortedness recurrence is only
    /// meaningful for such shapes.
    fn has_int_list_sort(&self) -> bool {
        self.sorts.iter().any(|(name, ctors)| {
            ctors.iter().any(|c| {
                let int_fields = c
                    .fields
                    .iter()
                    .filter(|f| matches!(f.kind, FieldKind::Int))
                    .count();
                let self_rec = c
                    .fields
                    .iter()
                    .filter(|f| matches!(&f.kind, FieldKind::Adt(s) if s == name))
                    .count();
                int_fields == 1 && self_rec == 1 && c.adt_field_count() == 1
            })
        })
    }

    /// Emit one combined `(declare-datatypes …)` block covering every
    /// registered sort — combined so mutual recursion and forward references
    /// need no dependency ordering.
    fn emit_declare_datatypes(&self) -> String {
        self.emit_declare_datatypes_filtered(None)
    }

    /// Like [`Self::emit_declare_datatypes`] but, when `keep` is `Some`,
    /// restricted to those sort names (in registry order). Declaring datatypes
    /// a per-clause obligation never mentions sends ay's DT solver into
    /// (irrelevant) constructor case-splitting that can PREVENT an otherwise
    /// trivial EUF+LIA+ite discharge — so each obligation declares only the
    /// datatypes reachable from its own terms. SOUND: an omitted sort has no
    /// term in the script, so the formula's models are unchanged (the discharge
    /// is a pure UNSAT search whose result is invariant under dropping inert
    /// declarations; a wrongly-omitted-yet-referenced sort merely fails to
    /// parse ⇒ fail-closed).
    fn emit_declare_datatypes_filtered(&self, keep: Option<&BTreeSet<String>>) -> String {
        let mut heads = String::new();
        let mut bodies = String::new();
        for (name, ctors) in &self.sorts {
            if let Some(keep) = keep {
                if !keep.contains(name) {
                    continue;
                }
            }
            heads.push_str(&format!("({} 0) ", quote_symbol(name)));
            bodies.push('(');
            for ctor in ctors {
                bodies.push('(');
                bodies.push_str(&quote_symbol(&ctor.name));
                for field in &ctor.fields {
                    bodies.push_str(&format!(
                        " ({} {})",
                        quote_symbol(&field.selector),
                        sort_to_smtlib(&field.sort)
                    ));
                }
                bodies.push(')');
            }
            bodies.push_str(") ");
        }
        if heads.is_empty() {
            return String::new();
        }
        format!("(declare-datatypes ({heads}) ({bodies}))\n")
    }
}

// ============================================================================
// Ladder (CEGAR v1: add the next catamorphism from the fixed pool)
// ============================================================================

/// Build the v1 CEGAR ladder of catamorphism pools for `problem`, weakest
/// (cheapest) first. Each refinement level adds catamorphisms.
///
/// When `include_element_catas` is set, the CATA v3 element/ordering levels
/// (`Min`/`Max` projections, the ascending-sortedness fold) are appended after
/// the exact v2 size-family ladder (default on at the route; opt-out via
/// `--chc-no-cata-elements`). They are fully certified by the same
/// fail-closed gate (per-clause obligations + abstract re-verification + query
/// gate), so they are 0-wrong by construction. NOTE: on the sampled
/// element/ordering ADT-LIA family the affine-Houdini/PDR abstract-solve
/// backend does not yet synthesize the inductive invariants these columns
/// target (sortedness insert-preservation, element ordering), so measured net
/// conversions from them are ~0 — the sound machinery lands ready for a
/// stronger (ICE / decision-tree) abstract solver.
pub(crate) fn build_cata_ladder(
    problem: &ChcProblem,
    include_element_catas: bool,
) -> Vec<Vec<CataKind>> {
    let registry = DtRegistry::build(problem);
    if registry.is_empty() {
        return Vec::new();
    }
    let mut ladder = Vec::new();
    // L0: {Size} only — the leanest abstraction. Size subsumes the root
    // discriminant for two-constructor list sorts (size = 1 ⟺ nil), and the
    // fewer columns keep the affine-Houdini candidate pool (CATA v2) small and
    // its equality invariants un-truncated. RootDisc is a refinement level.
    let mut pool = vec![CataKind::Size];
    ladder.push(pool.clone());
    pool.push(CataKind::RootDisc);
    ladder.push(pool.clone());
    if registry.has_int_fields() {
        pool.push(CataKind::IntSum);
        ladder.push(pool.clone());
    }
    if registry.total_ctors() <= MAX_CTOR_COUNT_COLUMNS {
        for ctors in registry.sorts.values() {
            for ctor in ctors {
                pool.push(CataKind::CtorCount(ctor.name.clone()));
            }
        }
        ladder.push(pool.clone());
    }
    if registry.any_multi_recursive_ctor() {
        pool.push(CataKind::Height);
        ladder.push(pool.clone());
    }

    // ── Element / ordering refinement levels (CATA v3) ──────────────────────
    // These target the element-level / ordering unknowns the size-family pool
    // cannot express (min/max projections, ascending sortedness). They are
    // appended as SEPARATE lean pools rather than piled onto the accumulated
    // one: keeping the column count low bounds the affine-Houdini candidate
    // pool (cubic in columns) and the abstract predicate arity. Reached only
    // after the cheaper size-family levels fail, so solved instances are never
    // slowed (the route returns on the first certified verdict).
    //
    if registry.has_int_fields() && include_element_catas {
        // Min/max element projections, alongside size/rootdisc/sum for the
        // affine ties the element props need (e.g. min preserved by a map).
        let mut elem = vec![CataKind::Size, CataKind::RootDisc, CataKind::IntSum];
        elem.push(CataKind::Min);
        elem.push(CataKind::Max);
        ladder.push(elem);

        // Ascending-sortedness fold. Requires `Min` in the same pool (its
        // recurrence compares the head to `min(rest)`). RootDisc lets the
        // affine layer relate a sortedness-flag datatype column (e.g. the
        // `ordered(b, l)` benchmarks' `Bool` flag) to the `sorted` column.
        if registry.has_int_list_sort() {
            ladder.push(vec![
                CataKind::Size,
                CataKind::RootDisc,
                CataKind::Min,
                CataKind::Sorted,
            ]);
        }
    }
    ladder
}

// ============================================================================
// Abstraction result
// ============================================================================

/// Why the abstraction declined to apply (all fail-closed: caller falls back).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CataSkip {
    NoDatatypes,
    UnsupportedArgumentSort(String),
    ClauseTooLarge(usize),
}

/// One per-original-clause implication obligation `θ ⇒ θ#`, encoded as a
/// standalone SMT-LIB script whose expected answer is `unsat`.
#[derive(Debug, Clone)]
pub(crate) struct ClauseObligation {
    pub(crate) clause_index: usize,
    /// Monolithic `θ ∧ ¬(⋀ θ#) ⊨ ⊥` script. Tried FIRST by the discharge gate
    /// on NARROW clauses (see `CATA_MONOLITHIC_MAX_SUB_SCRIPTS`) — one SMT
    /// query for the whole clause instead of one per conjunct — and used by
    /// the diagnostics dump and the pinned script-shape assertions in
    /// `cata_abstract/tests.rs`. Anything but `unsat` falls back to
    /// `sub_scripts`, so the verdict is exactly the per-conjunct one.
    pub(crate) script: String,
    /// Per-conjunct decomposition used by the discharge gate: each entry is
    /// `θ ∧ ¬θ#ᵢ ⊨ ⊥`. Discharged iff EVERY entry is `unsat` (fail-closed).
    /// Avoids the wide-disjunction case-split blowup of the monolithic form —
    /// see [`ClauseCtx::obligation_sub_scripts`].
    pub(crate) sub_scripts: Vec<String>,
}

/// Layout of one abstract predicate argument list.
#[derive(Debug, Clone)]
enum ArgMap {
    /// Non-ADT argument copied through at the given abstract position.
    Scalar { abs_index: usize },
    /// ADT argument expanded to `pool.len()` Int columns starting here.
    Adt {
        sort_name: String,
        first_abs_index: usize,
    },
}

/// Semantic tag for ONE abstract predicate column, derived purely from the
/// stored layout + catamorphism pool (no new persisted state). It lets the
/// CATA v2 affine Houdini enumerate the depth-1 GUARDED candidate families
/// (flag-guarded ordering facts, non-convex min recurrences) that a
/// conjunction of affine (in)equalities provably cannot express.
///
/// The `Vec<ColumnTag>` returned by [`CataAbstraction::column_tags`] is
/// index-aligned with the abstract predicate's `arg_sorts`: column `i`'s tag
/// is at position `i`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ColumnTag {
    /// The catamorphism this column carries, or `None` for a pass-through
    /// (non-ADT) scalar column.
    pub(crate) kind: Option<CataKind>,
    /// Original argument index this column expands from. Every column of the
    /// same ADT argument shares one `group`; each scalar is its own group.
    pub(crate) group: usize,
    /// True iff this is a pass-through `Int` scalar column — a valid operand
    /// for the guarded-min comparison (the inserted/compared element).
    pub(crate) scalar_int: bool,
}

/// A built catamorphism abstraction: the abstract LIA problem plus everything
/// needed to certify and back-translate it.
pub(crate) struct CataAbstraction {
    pub(crate) abstract_problem: ChcProblem,
    pub(crate) obligations: Vec<ClauseObligation>,
    /// Conjuncts weakened to `true` during abstraction (precision loss only).
    pub(crate) dropped_conjuncts: usize,
    pool: Vec<CataKind>,
    registry: DtRegistry,
    layout: FxHashMap<PredicateId, Vec<ArgMap>>,
    /// Original predicate signatures (for model composition).
    original_preds: Vec<(PredicateId, Vec<ChcSort>)>,
    /// RESUMABLE progress through the obligation gate: the first
    /// `(obligation index, sub-script index)` not yet discharged `unsat`.
    ///
    /// The gate is a property of the ABSTRACTION (`θ ⇒ θ#`), not of any
    /// candidate model, so every candidate generator at one ladder level faces
    /// the identical obligations. Before this memo the gate was re-run from
    /// scratch per candidate and a clock-exhausted attempt threw away every
    /// sub-query it had already discharged — measured on the equal-shape list
    /// problem under a loaded 18-way test suite: one attempt discharged 15 of
    /// 25 sub-queries in 5.28 s, the next re-started at 0 and got 4 more in
    /// 873 ms, and the level failed having proved 19 of 25 twice over.
    obligation_cursor: Cell<(usize, usize)>,
    /// Obligation indices whose monolithic whole-clause attempt already ran and
    /// did not come back `unsat`: the resumed gate goes straight to the
    /// per-conjunct split for those instead of re-paying the failed attempt.
    obligation_mono_tried_upto: Cell<usize>,
    /// A sub-query came back anything but `unsat` (sat / unknown / parse
    /// failure / panic / per-query timeout). Fail-closed and FINAL for this
    /// abstraction: no candidate model at this ladder level can certify past a
    /// gate that already rejected the abstraction it shares.
    obligation_refuted: Cell<bool>,
}

/// Outcome of one (resumable) run of the implication-obligation gate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ObligationGate {
    /// EVERY obligation came back `unsat`. The only outcome that certifies.
    Discharged,
    /// A sub-query did not come back `unsat`. Fail-closed and final: this
    /// abstraction can never certify a Safe.
    Refuted,
    /// The deadline arrived with obligations left. Neither certified nor
    /// refuted — the progress made is kept for a later resumed attempt.
    Exhausted,
}

/// Clause width (θ# conjunct count) at or below which the gate tries the
/// MONOLITHIC whole-clause obligation `θ ∧ ¬(⋀ᵢ θ#ᵢ) ⊨ ⊥` before the
/// per-conjunct split.
///
/// The split exists because `¬(⋀ᵢ θ#ᵢ)` is a WIDE disjunction and ay's eager
/// DPLL(T) enumerates it: a sortedness clause carries 100+ conjuncts and stalls
/// (>90 s) where each `θ ∧ ¬θ#ᵢ` sub-query is milliseconds. That reasoning is
/// about WIDE clauses. On the narrow size-family clauses the split instead
/// multiplies a ~20 ms fixed per-`check-sat` cost by the conjunct count, which
/// is how the equal-shape list problem's 3 clauses became 25 SMT queries
/// (measured: 512 ms monolithic-free vs 226 ms monolithic, idle; the ratio
/// carries straight through the ~15x wall-clock inflation of a loaded parallel
/// test suite).
///
/// Sound either way: the monolithic script IS the clause obligation, so an
/// `unsat` discharges it exactly; anything else falls back to the per-conjunct
/// split and the gate's verdict is unchanged.
const CATA_MONOLITHIC_MAX_SUB_SCRIPTS: usize = 16;

impl CataAbstraction {
    /// Build the abstraction of `problem` under the catamorphism `pool`.
    pub(crate) fn build(problem: &ChcProblem, pool: &[CataKind]) -> Result<Self, CataSkip> {
        let registry = DtRegistry::build(problem);
        if registry.is_empty() || !problem.has_datatype_sorts() {
            return Err(CataSkip::NoDatatypes);
        }

        // Reject signatures the v1 lane cannot represent faithfully.
        for pred in problem.predicates() {
            for sort in &pred.arg_sorts {
                match sort {
                    ChcSort::Bool | ChcSort::Int | ChcSort::Real | ChcSort::BitVec(_) => {}
                    ChcSort::Datatype { .. } => {}
                    other => {
                        return Err(CataSkip::UnsupportedArgumentSort(other.to_string()));
                    }
                }
            }
        }

        // Phase 1: abstract predicate signatures (same declaration order, so
        // PredicateIds are positionally identical to the original problem).
        let mut abstract_problem = ChcProblem::new();
        let mut layout: FxHashMap<PredicateId, Vec<ArgMap>> = FxHashMap::default();
        let mut original_preds = Vec::new();
        for pred in problem.predicates() {
            original_preds.push((pred.id, pred.arg_sorts.clone()));
            let mut abs_sorts = Vec::new();
            let mut arg_maps = Vec::new();
            for sort in &pred.arg_sorts {
                if let Some(sort_name) = registry.adt_sort_name(sort) {
                    arg_maps.push(ArgMap::Adt {
                        sort_name: sort_name.to_string(),
                        first_abs_index: abs_sorts.len(),
                    });
                    for _ in pool {
                        abs_sorts.push(ChcSort::Int);
                    }
                } else {
                    arg_maps.push(ArgMap::Scalar {
                        abs_index: abs_sorts.len(),
                    });
                    abs_sorts.push(sort.clone());
                }
            }
            let new_id = abstract_problem.declare_predicate(&pred.name, abs_sorts);
            debug_assert_eq!(new_id, pred.id, "cata: predicate ids must stay positional");
            layout.insert(pred.id, arg_maps);
        }

        // Phase 2: clauses + obligations.
        let mut obligations = Vec::new();
        let mut dropped_conjuncts = 0usize;
        for (clause_index, clause) in problem.clauses().iter().enumerate() {
            let mut ctx = ClauseCtx::new(&registry, pool, clause);
            let abstract_clause = ctx.translate_clause(clause, &layout)?;
            dropped_conjuncts += ctx.dropped;
            obligations.push(ClauseObligation {
                clause_index,
                script: ctx.obligation_script(clause),
                sub_scripts: ctx.obligation_sub_scripts(clause),
            });
            abstract_problem.add_clause(abstract_clause);
        }

        debug_assert!(
            !abstract_problem.has_datatype_sorts(),
            "cata: abstract problem must be datatype-free"
        );

        Ok(Self {
            abstract_problem,
            obligations,
            dropped_conjuncts,
            pool: pool.to_vec(),
            registry,
            layout,
            original_preds,
            obligation_cursor: Cell::new((0, 0)),
            obligation_mono_tried_upto: Cell::new(0),
            obligation_refuted: Cell::new(false),
        })
    }

    /// Per-column semantic tags for abstract predicate `pid`, in abstract
    /// column order (index-aligned with the predicate's `arg_sorts`). Derived
    /// PURELY from the stored `layout` + `pool`: an [`ArgMap::Adt`] expands to
    /// `self.pool.len()` catamorphism columns in pool order; an
    /// [`ArgMap::Scalar`] is a single column. Returns an empty vector for a
    /// predicate with no recorded layout (the CATA v2 guarded families then
    /// contribute nothing, so the conjunctive path is unchanged).
    pub(crate) fn column_tags(&self, pid: PredicateId) -> Vec<ColumnTag> {
        let Some(arg_maps) = self.layout.get(&pid) else {
            return Vec::new();
        };
        // Abstract predicate sorts (positionally identical to `pid.index()`),
        // used only to distinguish an `Int` scalar from a Bool/Real/BV scalar.
        let abs_sorts: &[ChcSort] = self
            .abstract_problem
            .predicates()
            .get(pid.index())
            .map(|p| p.arg_sorts.as_slice())
            .unwrap_or(&[]);
        let mut tags = Vec::new();
        for (group, arg_map) in arg_maps.iter().enumerate() {
            match arg_map {
                ArgMap::Scalar { abs_index } => {
                    let scalar_int = matches!(abs_sorts.get(*abs_index), Some(ChcSort::Int));
                    tags.push(ColumnTag {
                        kind: None,
                        group,
                        scalar_int,
                    });
                }
                ArgMap::Adt { .. } => {
                    for kind in &self.pool {
                        tags.push(ColumnTag {
                            kind: Some(kind.clone()),
                            group,
                            scalar_int: false,
                        });
                    }
                }
            }
        }
        tags
    }

    /// Discharge every per-clause implication obligation with a fresh SMT
    /// query (fail-closed): returns `true` only when EVERY obligation comes
    /// back `unsat` within its budget. Any `sat`, `unknown`, parse failure,
    /// panic, or deadline overrun rejects the whole abstraction.
    pub(crate) fn discharge_obligations(
        &self,
        per_obligation_budget: Duration,
        deadline: Option<Instant>,
    ) -> bool {
        self.run_obligation_gate(per_obligation_budget, deadline) == ObligationGate::Discharged
    }

    /// The implication-obligation gate, resumable and memoized (see
    /// `obligation_cursor`).
    ///
    /// Runs the obligations still outstanding, in order, and returns as soon as
    /// one is refuted or the deadline arrives. Progress is recorded on `self`,
    /// so a later call at the SAME ladder level continues where this one
    /// stopped rather than re-proving what is already proved, and a refutation
    /// short-circuits every later call.
    ///
    /// Fail-closed polarity is unchanged from the pre-memo gate: `Discharged`
    /// requires a real, fresh `unsat` for every obligation of the abstraction;
    /// every other outcome withholds.
    pub(crate) fn run_obligation_gate(
        &self,
        per_obligation_budget: Duration,
        deadline: Option<Instant>,
    ) -> ObligationGate {
        if self.obligation_refuted.get() {
            return ObligationGate::Refuted;
        }
        let expired = || deadline.is_some_and(|d| Instant::now() >= d);
        let (mut clause_index, mut sub_index) = self.obligation_cursor.get();
        while clause_index < self.obligations.len() {
            let obligation = &self.obligations[clause_index];
            // WHOLE-CLAUSE attempt first on narrow clauses: `θ ∧ ¬(⋀ᵢ θ#ᵢ) ⊨ ⊥`
            // is the clause obligation itself, so one `unsat` discharges every
            // conjunct at once and skips the fixed per-`check-sat` cost the
            // split otherwise pays once per conjunct. Anything else falls
            // through to the per-conjunct split below, so the VERDICT is
            // exactly the split's. Tried at most once per clause (a failed
            // attempt is remembered, so a resumed gate does not re-pay it).
            if sub_index == 0
                && obligation.sub_scripts.len() <= CATA_MONOLITHIC_MAX_SUB_SCRIPTS
                && clause_index >= self.obligation_mono_tried_upto.get()
            {
                if expired() {
                    tracing::debug!(
                        clause = obligation.clause_index,
                        "cata: obligation budget exhausted; failing closed"
                    );
                    return ObligationGate::Exhausted;
                }
                self.obligation_mono_tried_upto.set(clause_index + 1);
                // `_impl`, not the dumping wrapper: this is a PROBE, not the
                // gate's rejection. A failed probe is followed by the split,
                // and it is the split's failure that `--chc-cata-dump-obligations`
                // should record.
                if run_obligation_expect_unsat_impl(&obligation.script, per_obligation_budget) {
                    clause_index += 1;
                    self.obligation_cursor.set((clause_index, 0));
                    continue;
                }
            }
            // Per-conjunct split: `θ ⊨ ⋀ᵢ θ#ᵢ ⟺ ∀i. θ ⊨ θ#ᵢ`, so the level is
            // certified iff every sub-script is `unsat` — identical verdict to
            // the monolithic form, but each sub-query negates a SINGLE conjunct
            // instead of the whole conjunction, so ay never builds the wide
            // `¬(⋀ᵢ θ#ᵢ)` disjunction whose case-split blowup stalls the
            // sorted/min recurrence obligations (>90 s vs z3's <0.1 s).
            // Fail-closed unchanged: any non-`unsat` sub-query, a deadline
            // overrun, or an empty sub-script list rejects the level.
            while sub_index < obligation.sub_scripts.len() {
                if expired() {
                    self.obligation_cursor.set((clause_index, sub_index));
                    tracing::debug!(
                        clause = obligation.clause_index,
                        "cata: obligation budget exhausted; failing closed"
                    );
                    return ObligationGate::Exhausted;
                }
                if !run_obligation_expect_unsat(
                    &obligation.sub_scripts[sub_index],
                    per_obligation_budget,
                ) {
                    self.obligation_refuted.set(true);
                    tracing::debug!(
                        clause = obligation.clause_index,
                        "cata: implication obligation NOT discharged; failing closed"
                    );
                    return ObligationGate::Refuted;
                }
                sub_index += 1;
                self.obligation_cursor.set((clause_index, sub_index));
            }
            clause_index += 1;
            sub_index = 0;
            self.obligation_cursor.set((clause_index, 0));
        }
        ObligationGate::Discharged
    }

    /// Compose an abstract LIA model into an original-vocabulary invariant
    /// model: every abstract catamorphism column becomes a `FuncApp` of the
    /// reserved catamorphism symbol applied to the original argument, and the
    /// universally-true min facts are conjoined (they hold for the real
    /// catamorphisms, so this does not change the model's meaning — it only
    /// helps conservative downstream UF-based re-checks discharge).
    ///
    /// Returns `None` (caller must withhold the verdict) when any original
    /// predicate lacks a usable abstract interpretation.
    pub(crate) fn compose_model(&self, abstract_model: &InvariantModel) -> Option<InvariantModel> {
        let mut model = InvariantModel::new();
        for (pred_id, arg_sorts) in &self.original_preds {
            let arg_maps = self.layout.get(pred_id)?;
            let interp = abstract_model.get(pred_id)?;
            let abs_arity: usize = arg_maps
                .iter()
                .map(|m| match m {
                    ArgMap::Scalar { .. } => 1,
                    ArgMap::Adt { .. } => self.pool.len(),
                })
                .sum();
            if interp.vars.len() != abs_arity {
                return None;
            }

            // Canonical original argument variables (PDR convention).
            let orig_vars: Vec<ChcVar> = arg_sorts
                .iter()
                .enumerate()
                .map(|(j, sort)| ChcVar::new(format!("__p{}_a{j}", pred_id.index()), sort.clone()))
                .collect();

            let mut subst: Vec<(ChcVar, ChcExpr)> = Vec::new();
            let mut min_facts: Vec<ChcExpr> = Vec::new();
            for (j, arg_map) in arg_maps.iter().enumerate() {
                match arg_map {
                    ArgMap::Scalar { abs_index } => {
                        subst.push((
                            interp.vars[*abs_index].clone(),
                            ChcExpr::var(orig_vars[j].clone()),
                        ));
                    }
                    ArgMap::Adt {
                        sort_name,
                        first_abs_index,
                    } => {
                        for (k, kind) in self.pool.iter().enumerate() {
                            let cata_term = func_app(
                                kind.uf_name(sort_name),
                                ChcSort::Int,
                                vec![ChcExpr::var(orig_vars[j].clone())],
                            );
                            min_facts.extend(cata_min_facts(
                                kind,
                                &cata_term,
                                self.registry.ctors(sort_name).map_or(0, <[CtorInfo]>::len),
                            ));
                            subst.push((interp.vars[*first_abs_index + k].clone(), cata_term));
                        }
                    }
                }
            }

            let mut formula = interp.formula.substitute(&subst);
            if !min_facts.is_empty() {
                min_facts.insert(0, formula);
                formula = ChcExpr::and_all(min_facts);
            }
            model.set(*pred_id, PredicateInterpretation::new(orig_vars, formula));
        }
        Some(model)
    }

    #[cfg(test)]
    pub(crate) fn obligation_scripts(&self) -> Vec<&str> {
        self.obligations.iter().map(|o| o.script.as_str()).collect()
    }

    /// Transform-memory report per gating rule G1: sat-side verdicts require
    /// original validation via the per-clause implication obligations; unsafe
    /// witnesses can NOT be back-translated from the abstract side at all.
    #[allow(dead_code)] // G1 framework surface; exercised via CataBackTranslator + tests.
    pub(crate) fn transform_memory(&self) -> TransformMemoryReport {
        TransformMemoryReport::with_original_validation_obligations(
            "cata_abstract",
            self.obligations.iter().map(|o| {
                TransformObligation::named(format!("cata_clause_implication_{}", o.clause_index))
            }),
        )
        .with_incomplete_unsafe_backtranslation()
        .with_fact("cata_pool", format!("{}", self.pool.len()))
        .with_fact(
            "cata_dropped_conjuncts",
            format!("{}", self.dropped_conjuncts),
        )
    }
}

// ============================================================================
// Transformer / BackTranslator (G1 framework conformance)
// ============================================================================

/// `Transformer` wrapper around [`CataAbstraction`] for pipeline use.
///
/// The adaptive route drives [`CataAbstraction`] directly (it needs the
/// obligation scripts and the composition hooks); this wrapper keeps the lane
/// conformant with the G1 `Transformer`/`BackTranslator` framework and is
/// exercised by the unit tests.
#[allow(dead_code)]
pub(crate) struct CataAbstractor {
    pool: Vec<CataKind>,
}

impl CataAbstractor {
    #[cfg(test)]
    pub(crate) fn new(pool: Vec<CataKind>) -> Self {
        Self { pool }
    }
}

impl Transformer for CataAbstractor {
    fn transform(self: Box<Self>, problem: ChcProblem) -> TransformationResult {
        match CataAbstraction::build(&problem, &self.pool) {
            Ok(abstraction) => {
                let abstract_problem = abstraction.abstract_problem.clone();
                TransformationResult {
                    problem: abstract_problem,
                    back_translator: Box::new(CataBackTranslator { abstraction }),
                }
            }
            Err(_) => TransformationResult {
                problem,
                back_translator: Box::new(super::IdentityBackTranslator),
            },
        }
    }
}

/// Back-translator for the catamorphism abstraction.
///
/// - `translate_validity` composes the abstract LIA model with the reserved
///   catamorphism symbols (see [`CataAbstraction::compose_model`]); on failure
///   it returns an EMPTY model, which every downstream gate rejects
///   (fail-closed).
/// - `translate_invalidity` is intentionally an identity that the memory
///   report marks incomplete: an abstract counterexample is NEVER a witness
///   for the original problem and must be concretized by the caller instead.
#[allow(dead_code)]
pub(crate) struct CataBackTranslator {
    abstraction: CataAbstraction,
}

impl BackTranslator for CataBackTranslator {
    fn translate_validity(&self, witness: ValidityWitness) -> ValidityWitness {
        self.abstraction.compose_model(&witness).unwrap_or_default()
    }

    fn translate_invalidity(&self, witness: InvalidityWitness) -> InvalidityWitness {
        witness
    }

    fn transform_memory(&self) -> TransformMemoryReport {
        self.abstraction.transform_memory()
    }
}

// ============================================================================
// Clause translation
// ============================================================================

/// One abstracted ADT term: its catamorphism-value tuple.
struct TupleInfo {
    term: ChcExpr,
    sort_name: String,
    vars: Vec<ChcVar>,
    /// θ# uses tester/disequality consequences for this term, so the
    /// obligation needs the one-level unfolding case split to justify them.
    /// Equality-only tuples skip it — the selector terms it introduces make
    /// the DT search an order of magnitude slower.
    needs_unfolding: bool,
}

struct ClauseCtx<'a> {
    registry: &'a DtRegistry,
    pool: &'a [CataKind],
    /// Deterministic insertion order (obligations + naming).
    tuples: Vec<TupleInfo>,
    /// Abstract conjuncts (θ#): recurrences, min facts, tuple equalities,
    /// tester consequences, and kept scalar conjuncts.
    abs_conjuncts: Vec<ChcExpr>,
    /// Conjuncts weakened to `true`.
    dropped: usize,
    /// All variable names already used in the clause (collision avoidance).
    used_names: Vec<String>,
    fresh_counter: usize,
}

impl<'a> ClauseCtx<'a> {
    fn new(registry: &'a DtRegistry, pool: &'a [CataKind], clause: &HornClause) -> Self {
        let mut used_names: Vec<String> = clause.body.vars().into_iter().map(|v| v.name).collect();
        for v in clause.head.vars() {
            if !used_names.contains(&v.name) {
                used_names.push(v.name);
            }
        }
        Self {
            registry,
            pool,
            tuples: Vec::new(),
            abs_conjuncts: Vec::new(),
            dropped: 0,
            used_names,
            fresh_counter: 0,
        }
    }

    fn fresh_name(&mut self, base: &str) -> String {
        loop {
            let candidate = format!("{base}{}", self.fresh_counter);
            self.fresh_counter += 1;
            if !self.used_names.contains(&candidate) {
                self.used_names.push(candidate.clone());
                return candidate;
            }
        }
    }

    /// Get or create the catamorphism tuple for an ADT-sorted term. Creating a
    /// tuple records the universally-true min facts, and for constructor terms
    /// the defining recurrences (recursing into ADT-sorted constructor args).
    fn tuple_for(&mut self, term: &ChcExpr, sort_name: &str) -> Result<Vec<ChcVar>, CataSkip> {
        if let Some(info) = self.tuples.iter().find(|t| &t.term == term) {
            return Ok(info.vars.clone());
        }
        if self.tuples.len() >= MAX_TUPLES_PER_CLAUSE {
            return Err(CataSkip::ClauseTooLarge(self.tuples.len()));
        }

        let base = self.fresh_name("__cata");
        let vars: Vec<ChcVar> = self
            .pool
            .iter()
            .map(|kind| ChcVar::new(format!("{base}_{}", kind.tag()), ChcSort::Int))
            .collect();
        let n_ctors = self.registry.ctors(sort_name).map_or(0, <[CtorInfo]>::len);
        for (kind, var) in self.pool.iter().zip(&vars) {
            self.abs_conjuncts
                .extend(cata_min_facts(kind, &ChcExpr::var(var.clone()), n_ctors));
        }
        self.tuples.push(TupleInfo {
            term: term.clone(),
            sort_name: sort_name.to_string(),
            vars: vars.clone(),
            needs_unfolding: false,
        });

        // Constructor term: pin the tuple with the defining recurrences.
        if let ChcExpr::FuncApp(name, _, args) = term {
            if let Some(ctor) = self.registry.ctor(sort_name, name).cloned() {
                if ctor.fields.len() == args.len() {
                    // Recurse into ADT-sorted constructor arguments first.
                    let mut sub_tuples: Vec<Option<Vec<ChcVar>>> = Vec::new();
                    for (field, arg) in ctor.fields.iter().zip(args) {
                        if let FieldKind::Adt(field_sort) = &field.kind {
                            let field_sort = field_sort.clone();
                            sub_tuples.push(Some(self.tuple_for(arg, &field_sort)?));
                        } else {
                            sub_tuples.push(None);
                        }
                    }
                    for (k, kind) in self.pool.iter().enumerate() {
                        if let Some(eq) = ctor_recurrence(
                            kind,
                            &ctor,
                            args,
                            &sub_tuples,
                            k,
                            &ChcExpr::var(vars[k].clone()),
                            self.registry,
                            self.pool,
                        ) {
                            self.abs_conjuncts.push(eq);
                        }
                    }
                }
            }
        }

        Ok(vars)
    }

    /// Mark a term's tuple as requiring the one-level unfolding case split in
    /// its obligation (θ# used tester/disequality consequences for it).
    fn mark_needs_unfolding(&mut self, term: &ChcExpr) {
        if let Some(info) = self.tuples.iter_mut().find(|t| &t.term == term) {
            info.needs_unfolding = true;
        }
    }

    /// Does `expr` mention any ADT-sorted subterm or datatype member symbol?
    fn mentions_adt(&self, expr: &ChcExpr) -> bool {
        if self.registry.adt_sort_name(&expr.sort()).is_some() {
            return true;
        }
        match expr {
            ChcExpr::Var(v) => self.registry.adt_sort_name(&v.sort).is_some(),
            ChcExpr::FuncApp(name, _, args) => {
                self.registry.is_dt_member_symbol(name) || args.iter().any(|a| self.mentions_adt(a))
            }
            ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) => {
                args.iter().any(|a| self.mentions_adt(a))
            }
            ChcExpr::ConstArray(_, v) => self.mentions_adt(v),
            _ => false,
        }
    }

    /// Abstract one conjunct of the clause constraint into θ# conjuncts.
    fn translate_conjunct(&mut self, conjunct: &ChcExpr) -> Result<(), CataSkip> {
        use crate::ChcOp;
        match conjunct {
            // ADT equality → tuple equality.
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                let sort = args[0].sort();
                if let Some(sort_name) = self.registry.adt_sort_name(&sort).map(str::to_string) {
                    let ta = self.tuple_for(&args[0], &sort_name)?;
                    let tb = self.tuple_for(&args[1], &sort_name)?;
                    for (a, b) in ta.into_iter().zip(tb) {
                        self.abs_conjuncts
                            .push(ChcExpr::eq(ChcExpr::var(a), ChcExpr::var(b)));
                    }
                    return Ok(());
                }
                if self.mentions_adt(conjunct) {
                    self.dropped += 1;
                } else {
                    self.abs_conjuncts.push(conjunct.clone());
                }
                Ok(())
            }
            // ADT disequality: `t ≠ NullaryCtor` on a 2-ctor sort keeps the
            // other constructor's consequences; everything else is dropped.
            ChcExpr::Op(ChcOp::Ne, args) if args.len() == 2 => {
                self.translate_adt_disequality(&args[0], &args[1], conjunct)
            }
            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => match args[0].as_ref() {
                ChcExpr::Op(ChcOp::Eq, eq_args) if eq_args.len() == 2 => {
                    self.translate_adt_disequality(&eq_args[0], &eq_args[1], conjunct)
                }
                ChcExpr::FuncApp(name, _, t_args)
                    if name.starts_with("is-") && t_args.len() == 1 =>
                {
                    self.translate_negated_tester(name, &t_args[0], conjunct)
                }
                _ => {
                    if self.mentions_adt(conjunct) {
                        self.dropped += 1;
                    } else {
                        self.abs_conjuncts.push(conjunct.clone());
                    }
                    Ok(())
                }
            },
            // Tester → catamorphism consequences.
            ChcExpr::FuncApp(name, _, args) if name.starts_with("is-") && args.len() == 1 => {
                let ctor_name = name.trim_start_matches("is-").to_string();
                let sort = args[0].sort();
                if let Some(sort_name) = self.registry.adt_sort_name(&sort).map(str::to_string) {
                    if let Some(ctor) = self.registry.ctor(&sort_name, &ctor_name).cloned() {
                        let tuple = self.tuple_for(&args[0], &sort_name)?;
                        self.mark_needs_unfolding(&args[0]);
                        let n_ctors = self.registry.ctors(&sort_name).map_or(0, <[CtorInfo]>::len);
                        self.abs_conjuncts
                            .extend(tester_consequences(self.pool, &ctor, &tuple, n_ctors));
                        return Ok(());
                    }
                }
                self.dropped += 1;
                Ok(())
            }
            other => {
                if self.mentions_adt(other) {
                    self.dropped += 1;
                } else {
                    self.abs_conjuncts.push(other.clone());
                }
                Ok(())
            }
        }
    }

    fn translate_adt_disequality(
        &mut self,
        lhs: &ChcExpr,
        rhs: &ChcExpr,
        original: &ChcExpr,
    ) -> Result<(), CataSkip> {
        let sort = lhs.sort();
        let Some(sort_name) = self.registry.adt_sort_name(&sort).map(str::to_string) else {
            if self.mentions_adt(original) {
                self.dropped += 1;
            } else {
                self.abs_conjuncts.push(original.clone());
            }
            return Ok(());
        };
        // Recognize `t ≠ NullaryCtor` in either orientation.
        let nullary = |e: &ChcExpr| -> Option<String> {
            if let ChcExpr::FuncApp(name, _, args) = e {
                if args.is_empty() && self.registry.ctor(&sort_name, name).is_some() {
                    return Some(name.clone());
                }
            }
            None
        };
        let (subject, excluded_ctor) = if let Some(c) = nullary(rhs) {
            (lhs, Some(c))
        } else if let Some(c) = nullary(lhs) {
            (rhs, Some(c))
        } else {
            (lhs, None)
        };
        if let Some(excluded) = excluded_ctor {
            let ctors: Vec<CtorInfo> = self
                .registry
                .ctors(&sort_name)
                .map(<[CtorInfo]>::to_vec)
                .unwrap_or_default();
            let subject = subject.clone();
            let tuple = self.tuple_for(&subject, &sort_name)?;
            self.mark_needs_unfolding(&subject);
            // RootDisc is exact for any constructor count.
            if let Some(excluded_info) = ctors.iter().find(|c| c.name == excluded) {
                for (k, kind) in self.pool.iter().enumerate() {
                    if matches!(kind, CataKind::RootDisc) {
                        self.abs_conjuncts.push(ChcExpr::ne(
                            ChcExpr::var(tuple[k].clone()),
                            ChcExpr::int(excluded_info.index as i64),
                        ));
                    }
                }
            }
            // Two-constructor sorts: the subject must be the OTHER constructor.
            if ctors.len() == 2 {
                if let Some(other) = ctors.iter().find(|c| c.name != excluded) {
                    let n_ctors = ctors.len();
                    self.abs_conjuncts
                        .extend(tester_consequences(self.pool, other, &tuple, n_ctors));
                }
            }
            return Ok(());
        }
        // General ADT disequality: information loss by design.
        self.dropped += 1;
        Ok(())
    }

    fn translate_negated_tester(
        &mut self,
        tester_name: &str,
        subject: &ChcExpr,
        original: &ChcExpr,
    ) -> Result<(), CataSkip> {
        let ctor_name = tester_name.trim_start_matches("is-").to_string();
        let sort = subject.sort();
        if let Some(sort_name) = self.registry.adt_sort_name(&sort).map(str::to_string) {
            let ctors: Vec<CtorInfo> = self
                .registry
                .ctors(&sort_name)
                .map(<[CtorInfo]>::to_vec)
                .unwrap_or_default();
            if ctors.iter().any(|c| c.name == ctor_name) {
                let tuple = self.tuple_for(subject, &sort_name)?;
                self.mark_needs_unfolding(subject);
                if let Some(excluded_info) = ctors.iter().find(|c| c.name == ctor_name) {
                    for (k, kind) in self.pool.iter().enumerate() {
                        if matches!(kind, CataKind::RootDisc) {
                            self.abs_conjuncts.push(ChcExpr::ne(
                                ChcExpr::var(tuple[k].clone()),
                                ChcExpr::int(excluded_info.index as i64),
                            ));
                        }
                    }
                }
                if ctors.len() == 2 {
                    if let Some(other) = ctors.iter().find(|c| c.name != ctor_name) {
                        self.abs_conjuncts.extend(tester_consequences(
                            self.pool,
                            other,
                            &tuple,
                            ctors.len(),
                        ));
                    }
                }
                return Ok(());
            }
        }
        if self.mentions_adt(original) {
            self.dropped += 1;
        } else {
            self.abs_conjuncts.push(original.clone());
        }
        Ok(())
    }

    /// Translate one predicate argument list per the abstract layout.
    fn translate_pred_args(
        &mut self,
        pred_id: PredicateId,
        args: &[ChcExpr],
        layout: &FxHashMap<PredicateId, Vec<ArgMap>>,
    ) -> Result<Vec<ChcExpr>, CataSkip> {
        let arg_maps = layout
            .get(&pred_id)
            .expect("cata: every predicate has a layout");
        let mut out = Vec::new();
        for (arg, arg_map) in args.iter().zip(arg_maps) {
            match arg_map {
                ArgMap::Adt { sort_name, .. } => {
                    let tuple = self.tuple_for(arg, sort_name)?;
                    out.extend(tuple.into_iter().map(ChcExpr::var));
                }
                ArgMap::Scalar { .. } => {
                    if self.mentions_adt(arg) {
                        // Sound over-approximation: an unconstrained fresh
                        // variable admits every value the ADT-dependent term
                        // could take.
                        let name = self.fresh_name("__cata_opq");
                        out.push(ChcExpr::var(ChcVar::new(name, arg.sort())));
                    } else {
                        out.push(arg.clone());
                    }
                }
            }
        }
        Ok(out)
    }

    fn translate_clause(
        &mut self,
        clause: &HornClause,
        layout: &FxHashMap<PredicateId, Vec<ArgMap>>,
    ) -> Result<HornClause, CataSkip> {
        let mut abs_body_preds = Vec::new();
        for (pred_id, args) in &clause.body.predicates {
            abs_body_preds.push((*pred_id, self.translate_pred_args(*pred_id, args, layout)?));
        }
        let abs_head = match &clause.head {
            ClauseHead::False => ClauseHead::False,
            ClauseHead::Predicate(pred_id, args) => {
                ClauseHead::Predicate(*pred_id, self.translate_pred_args(*pred_id, args, layout)?)
            }
        };
        if let Some(constraint) = &clause.body.constraint {
            for conjunct in constraint.conjuncts() {
                self.translate_conjunct(conjunct)?;
            }
        }
        let abs_constraint = if self.abs_conjuncts.is_empty() {
            None
        } else {
            Some(ChcExpr::and_all(self.abs_conjuncts.iter().cloned()))
        };
        Ok(HornClause::new(
            ClauseBody::new(abs_body_preds, abs_constraint),
            abs_head,
        ))
    }

    // ── Obligation emission ────────────────────────────────────────────────

    /// Emit the standalone SMT-LIB implication-obligation script for this
    /// clause: `θ ∧ true-catamorphism-facts ∧ ¬θ#`, expected `unsat`.
    /// Datatype sort names reachable from this clause's obligation script:
    /// every tuple's sort, every datatype variable in the tuple terms and the
    /// clause constraint, closed over constructor-field datatype references
    /// (so a mutually-recursive or nested datatype a kept sort mentions is
    /// still declared). Deliberately a SUPERSET of what actually appears —
    /// erring toward inclusion keeps a needed declaration from ever being
    /// dropped (which would fail-close and lose a discharge).
    fn obligation_used_sorts(&self, clause: &HornClause) -> BTreeSet<String> {
        let mut used: BTreeSet<String> = BTreeSet::new();
        let add = |used: &mut BTreeSet<String>, sort: &ChcSort| {
            if let Some(name) = self.registry.adt_sort_name(sort) {
                used.insert(name.to_string());
            }
        };
        for tuple in &self.tuples {
            used.insert(tuple.sort_name.clone());
            for var in tuple.term.vars() {
                add(&mut used, &var.sort);
            }
        }
        if let Some(constraint) = &clause.body.constraint {
            for var in constraint.vars() {
                add(&mut used, &var.sort);
            }
        }
        // Transitive closure over constructor-field datatype references.
        let mut frontier: Vec<String> = used.iter().cloned().collect();
        while let Some(name) = frontier.pop() {
            if let Some(ctors) = self.registry.ctors(&name) {
                for ctor in ctors {
                    for field in &ctor.fields {
                        if let FieldKind::Adt(dep) = &field.kind {
                            if used.insert(dep.clone()) {
                                frontier.push(dep.clone());
                            }
                        }
                    }
                }
            }
        }
        used
    }

    /// The SHARED environment prefix of a clause's obligation script: the
    /// logic declaration, reachable datatypes, catamorphism UFs, clause/tuple
    /// variable declarations, `θ` (the original clause constraint), and the
    /// universally-true catamorphism facts (ties, min facts, defining
    /// recurrences). It stops BEFORE the `¬θ#` goal assertion and `check-sat`,
    /// so the monolithic [`Self::obligation_script`] and the per-conjunct
    /// [`Self::obligation_sub_scripts`] share one construction.
    fn obligation_env_prefix(&self, clause: &HornClause) -> String {
        // Datatypes REACHABLE from this clause's own terms (tuple sorts + any
        // datatype variable in θ), closed over constructor-field datatype
        // references. Declaring the rest sends ay's DT solver into irrelevant
        // constructor case-splitting that can block an otherwise-trivial
        // discharge (e.g. an unused `Bool` enum stalling a `list` min/sorted
        // obligation). Pruning is sound: omitted sorts have no term here.
        let used_sorts = self.obligation_used_sorts(clause);

        let mut smt = String::with_capacity(4096);
        smt.push_str("(set-logic ALL)\n");
        smt.push_str(
            &self
                .registry
                .emit_declare_datatypes_filtered(Some(&used_sorts)),
        );

        // Catamorphism UFs: every pool member at every REACHABLE sort.
        for kind in self.pool {
            for sort_name in self.registry.sorts.keys() {
                if !used_sorts.contains(sort_name) {
                    continue;
                }
                smt.push_str(&format!(
                    "(declare-fun {} ({}) Int)\n",
                    quote_symbol(&kind.uf_name(sort_name)),
                    quote_symbol(sort_name)
                ));
            }
        }

        // Clause variables (θ vars plus vars inside abstracted terms).
        let mut declared: Vec<String> = Vec::new();
        let mut declare_var = |smt: &mut String, var: &ChcVar| {
            if !declared.contains(&var.name) {
                declared.push(var.name.clone());
                smt.push_str(&format!(
                    "(declare-const {} {})\n",
                    quote_symbol(&var.name),
                    sort_to_smtlib(&var.sort)
                ));
            }
        };
        if let Some(constraint) = &clause.body.constraint {
            for var in constraint.vars() {
                declare_var(&mut smt, &var);
            }
        }
        for tuple in &self.tuples {
            for var in tuple.term.vars() {
                declare_var(&mut smt, &var);
            }
        }
        // Tuple variables.
        for tuple in &self.tuples {
            for var in &tuple.vars {
                declare_var(&mut smt, var);
            }
        }
        // Fresh opaque scalar vars can occur in θ# via predicate args; they
        // are unconstrained, and θ# only APPEARS negated, so they need no
        // declarations here (θ# below is the abstract CONSTRAINT only, which
        // never mentions them).

        // θ (the original clause constraint, over real ADT semantics).
        if let Some(constraint) = &clause.body.constraint {
            smt.push_str("(assert ");
            smt.push_str(&InvariantModel::expr_to_smtlib(constraint));
            smt.push_str(")\n");
        }

        // True facts of the real catamorphisms, instantiated per tuple:
        // ties, min facts, defining recurrences.
        for tuple in &self.tuples {
            let n_ctors = self
                .registry
                .ctors(&tuple.sort_name)
                .map_or(0, <[CtorInfo]>::len);
            for (k, kind) in self.pool.iter().enumerate() {
                // Tie the abstraction variable to the UF value.
                let uf_term = func_app(
                    kind.uf_name(&tuple.sort_name),
                    ChcSort::Int,
                    vec![tuple.term.clone()],
                );
                smt.push_str("(assert ");
                smt.push_str(&InvariantModel::expr_to_smtlib(&ChcExpr::eq(
                    ChcExpr::var(tuple.vars[k].clone()),
                    uf_term.clone(),
                )));
                smt.push_str(")\n");
                // Min facts are universally true of the real catamorphisms;
                // asserting them directly keeps equality-only obligations
                // selector-free (fast).
                for fact in cata_min_facts(kind, &uf_term, n_ctors) {
                    smt.push_str("(assert ");
                    smt.push_str(&InvariantModel::expr_to_smtlib(&fact));
                    smt.push_str(")\n");
                }
            }
            // CONSTRUCTOR terms get their defining recurrences instantiated
            // DIRECTLY over the argument terms — never through selectors.
            // (Selector applications on explicit constructor terms, e.g.
            // `tl(nil)` inside an unfolding case split, are underspecified
            // values that send the DT solver into non-terminating search.)
            // Everything else (variables, opaque terms) gets the one-level
            // unfolding case split.
            let mut is_ctor_term = false;
            if let ChcExpr::FuncApp(name, _, args) = &tuple.term {
                if let Some(ctor) = self.registry.ctor(&tuple.sort_name, name) {
                    if ctor.fields.len() == args.len() {
                        is_ctor_term = true;
                        let field_terms: Vec<ChcExpr> =
                            args.iter().map(|a| a.as_ref().clone()).collect();
                        for kind in self.pool {
                            if let Some(rhs) =
                                recurrence_rhs(kind, ctor, &field_terms, self.registry, self.pool)
                            {
                                let lhs = func_app(
                                    kind.uf_name(&tuple.sort_name),
                                    ChcSort::Int,
                                    vec![tuple.term.clone()],
                                );
                                smt.push_str("(assert ");
                                smt.push_str(&InvariantModel::expr_to_smtlib(&ChcExpr::eq(
                                    lhs, rhs,
                                )));
                                smt.push_str(")\n");
                            }
                        }
                    }
                }
            }
            // The unfolding case split is only needed to justify
            // tester/disequality consequences; it introduces selector terms
            // that slow the DT search considerably, so it stays opt-in.
            if !is_ctor_term && tuple.needs_unfolding {
                if let Some(axiom) = self.unfolding_axiom(tuple) {
                    smt.push_str("(assert ");
                    smt.push_str(&InvariantModel::expr_to_smtlib(&axiom));
                    smt.push_str(")\n");
                }
            }
        }
        smt
    }

    /// The MONOLITHIC obligation script `θ ∧ ¬(⋀ᵢ θ#ᵢ) ⊨ ⊥`, retained for
    /// diagnostics ([`Self::obligation_scripts`], the dump env var) and the
    /// symbol-declaration tests. The discharge path uses the per-conjunct
    /// decomposition instead (see [`Self::obligation_sub_scripts`]).
    fn obligation_script(&self, clause: &HornClause) -> String {
        let mut smt = self.obligation_env_prefix(clause);
        // ¬θ#.
        let theta_sharp = if self.abs_conjuncts.is_empty() {
            ChcExpr::Bool(true)
        } else {
            ChcExpr::and_all(self.abs_conjuncts.iter().cloned())
        };
        smt.push_str("(assert ");
        smt.push_str(&InvariantModel::expr_to_smtlib(&ChcExpr::not(theta_sharp)));
        smt.push_str(")\n(check-sat)\n");
        smt
    }

    /// Decompose the single conjunctive obligation `θ ⊨ ⋀ᵢ θ#ᵢ` into one
    /// independent sub-obligation `θ ∧ ¬θ#ᵢ ⊨ ⊥` per conjunct.
    ///
    /// SOUND and EQUIVALENT: `θ ⊨ ⋀ᵢ θ#ᵢ  ⟺  ∀i. θ ⊨ θ#ᵢ`, so the abstraction
    /// discharges iff EVERY sub-script is `unsat` — identical verdict to the
    /// monolithic form, and fail-closed is unchanged (any non-`unsat` sub-query
    /// rejects the whole abstraction).
    ///
    /// WHY: the monolithic `¬(⋀ᵢ θ#ᵢ)` is a WIDE disjunction (θ# routinely has
    /// 100+ conjuncts — trivial congruence ties plus a few recurrence facts).
    /// ay's eager DPLL(T) enumerates that disjunction against the full premise
    /// set, blowing up to thousands of theory-conflict case-splits (the sorted /
    /// min ordering-recurrence obligations stall >90 s where z3 — which
    /// decomposes internally — discharges in <0.1 s). Each sub-script negates a
    /// SINGLE conjunct, so no wide disjunction is ever built and every sub-query
    /// discharges in milliseconds. Pure discharge-side restructuring: the SMT
    /// engine and the obligation SEMANTICS are untouched.
    fn obligation_sub_scripts(&self, clause: &HornClause) -> Vec<String> {
        let prefix = self.obligation_env_prefix(clause);
        if self.abs_conjuncts.is_empty() {
            // θ# ≡ true ⇒ ¬θ# ≡ false; the obligation is trivially discharged.
            let mut smt = prefix;
            smt.push_str("(assert false)\n(check-sat)\n");
            return vec![smt];
        }
        self.abs_conjuncts
            .iter()
            .map(|conjunct| {
                let mut smt = prefix.clone();
                smt.push_str("(assert (not ");
                smt.push_str(&InvariantModel::expr_to_smtlib(conjunct));
                smt.push_str("))\n(check-sat)\n");
                smt
            })
            .collect()
    }

    /// One-level unfolding axiom for an abstracted term `t` of sort `S`:
    /// a case split over the constructors of `S`, asserting each
    /// catamorphism's defining recurrence through the selectors plus the min
    /// facts of the selector values. Every branch is a true fact of the real
    /// catamorphisms, so asserting the disjunction is sound.
    fn unfolding_axiom(&self, tuple: &TupleInfo) -> Option<ChcExpr> {
        let ctors = self.registry.ctors(&tuple.sort_name)?;
        let n_ctors = ctors.len();
        let mut branches = Vec::new();
        for ctor in ctors {
            let mut parts = vec![func_app(
                format!("is-{}", ctor.name),
                ChcSort::Bool,
                vec![tuple.term.clone()],
            )];
            // Selector-applied subterms and their catamorphism UF values.
            let field_terms: Vec<ChcExpr> = ctor
                .fields
                .iter()
                .map(|field| {
                    func_app(
                        field.selector.clone(),
                        field.sort.clone(),
                        vec![tuple.term.clone()],
                    )
                })
                .collect();
            for kind in self.pool {
                let lhs = func_app(
                    kind.uf_name(&tuple.sort_name),
                    ChcSort::Int,
                    vec![tuple.term.clone()],
                );
                if let Some(rhs) =
                    recurrence_rhs(kind, ctor, &field_terms, self.registry, self.pool)
                {
                    parts.push(ChcExpr::eq(lhs, rhs));
                }
                // Min facts of the recursive fields' catamorphism values.
                for (field, term) in ctor.fields.iter().zip(&field_terms) {
                    if let FieldKind::Adt(field_sort) = &field.kind {
                        let sub =
                            func_app(kind.uf_name(field_sort), ChcSort::Int, vec![term.clone()]);
                        let n_sub = self.registry.ctors(field_sort).map_or(0, <[CtorInfo]>::len);
                        parts.extend(cata_min_facts(kind, &sub, n_sub));
                    }
                }
            }
            branches.push(ChcExpr::and_all(parts));
        }
        if n_ctors == 0 {
            return None;
        }
        Some(ChcExpr::or_all(branches))
    }
}

// ============================================================================
// Catamorphism semantics (recurrences / consequences / min facts)
// ============================================================================

include!("semantics_helpers.rs");

/// Right-hand side of the defining recurrence of `kind` at constructor `ctor`,
/// with `field_terms[i]` standing for the i-th field value. ADT fields are
/// referenced through their catamorphism UF; Int fields directly. Returns
/// `None` when the recurrence would mention a field this encoding cannot
/// represent (never happens for the v1 pool).
fn recurrence_rhs(
    kind: &CataKind,
    ctor: &CtorInfo,
    field_terms: &[ChcExpr],
    registry: &DtRegistry,
    pool: &[CataKind],
) -> Option<ChcExpr> {
    let adt_field_values: Vec<ChcExpr> = ctor
        .fields
        .iter()
        .zip(field_terms)
        .filter_map(|(field, term)| match &field.kind {
            FieldKind::Adt(field_sort) => Some(func_app(
                kind.uf_name(field_sort),
                ChcSort::Int,
                vec![term.clone()],
            )),
            _ => None,
        })
        .collect();
    // Integer-field terms (direct element values feeding min/max/sorted).
    let int_field_values: Vec<ChcExpr> = ctor
        .fields
        .iter()
        .zip(field_terms)
        .filter_map(|(field, term)| match &field.kind {
            FieldKind::Int => Some(term.clone()),
            _ => None,
        })
        .collect();
    // Recursive-field values EXCLUDING element-free leaves (`nil`) — the ±∞
    // identity of min/max (and vacuously sorted). Only Min/Max/Sorted use this;
    // Size/Height/IntSum/CtorCount must still count every field, so they keep
    // `adt_field_values`. See [`is_empty_leaf_term`].
    let adt_elem_values: Vec<ChcExpr> =
        ctor.fields
            .iter()
            .zip(field_terms)
            .filter_map(|(field, term)| match &field.kind {
                FieldKind::Adt(field_sort) if !is_empty_leaf_term(registry, term) => Some(
                    func_app(kind.uf_name(field_sort), ChcSort::Int, vec![term.clone()]),
                ),
                _ => None,
            })
            .collect();
    match kind {
        CataKind::Size => Some(sum_exprs(
            std::iter::once(ChcExpr::int(1))
                .chain(adt_field_values)
                .collect(),
        )),
        CataKind::Height => {
            if adt_field_values.is_empty() {
                Some(ChcExpr::int(1))
            } else {
                let mut max = adt_field_values[0].clone();
                for value in &adt_field_values[1..] {
                    max = ChcExpr::ite(ChcExpr::ge(max.clone(), value.clone()), max, value.clone());
                }
                Some(ChcExpr::add(ChcExpr::int(1), max))
            }
        }
        CataKind::IntSum => {
            let mut terms: Vec<ChcExpr> = ctor
                .fields
                .iter()
                .zip(field_terms)
                .filter_map(|(field, term)| match &field.kind {
                    FieldKind::Int => Some(term.clone()),
                    _ => None,
                })
                .collect();
            terms.extend(adt_field_values);
            Some(sum_exprs(terms))
        }
        CataKind::CtorCount(counted) => {
            let own = i64::from(&ctor.name == counted);
            Some(sum_exprs(
                std::iter::once(ChcExpr::int(own))
                    .chain(adt_field_values)
                    .collect(),
            ))
        }
        CataKind::RootDisc => Some(ChcExpr::int(ctor.index as i64)),
        CataKind::Min => {
            // min over {int elements} ∪ {min(non-empty recursive fields)};
            // element-free leaves contribute +∞ (excluded), so an empty subtree
            // never clamps a real element via the finite sentinel. All-empty ⇒ +∞.
            let mut terms = int_field_values;
            terms.extend(adt_elem_values);
            if terms.is_empty() {
                Some(ChcExpr::int(CATA_MIN_SENTINEL))
            } else {
                Some(min_expr(terms))
            }
        }
        CataKind::Max => {
            let mut terms = int_field_values;
            terms.extend(adt_elem_values);
            if terms.is_empty() {
                Some(ChcExpr::int(CATA_MAX_SENTINEL))
            } else {
                Some(max_expr(terms))
            }
        }
        CataKind::Sorted => {
            // Recursive fields' `min` and `sorted` values via their UFs.
            let has_min = pool.iter().any(|k| matches!(k, CataKind::Min));
            // Element-free leaves (`nil`) are vacuously sorted and carry `+∞`
            // as their `min`; excluding them makes `head ≤ min(rest)` vacuous
            // for a singleton rather than the spurious `head ≤ sentinel`.
            let rest_mins: Vec<ChcExpr> =
                ctor.fields
                    .iter()
                    .zip(field_terms)
                    .filter_map(|(field, term)| match &field.kind {
                        FieldKind::Adt(fs) if !is_empty_leaf_term(registry, term) => Some(
                            func_app(CataKind::Min.uf_name(fs), ChcSort::Int, vec![term.clone()]),
                        ),
                        _ => None,
                    })
                    .collect();
            let rest_sorteds: Vec<ChcExpr> = ctor
                .fields
                .iter()
                .zip(field_terms)
                .filter_map(|(field, term)| match &field.kind {
                    FieldKind::Adt(fs) if !is_empty_leaf_term(registry, term) => Some(func_app(
                        CataKind::Sorted.uf_name(fs),
                        ChcSort::Int,
                        vec![term.clone()],
                    )),
                    _ => None,
                })
                .collect();
            sorted_recurrence_rhs(
                int_field_values.into_iter().next(),
                has_min.then_some(rest_mins),
                rest_sorteds,
            )
        }
    }
}

/// Defining recurrence for a CONSTRUCTOR TERM in a clause: equate the term's
/// tuple variable with the recurrence over the constructor-argument tuples.
/// Int fields use the actual argument expression when it is ADT-free (skipped
/// otherwise — soundly leaving the value under-constrained).
fn ctor_recurrence(
    kind: &CataKind,
    ctor: &CtorInfo,
    args: &[Arc<ChcExpr>],
    sub_tuples: &[Option<Vec<ChcVar>>],
    pool_index: usize,
    tuple_value: &ChcExpr,
    registry: &DtRegistry,
    pool: &[CataKind],
) -> Option<ChcExpr> {
    let adt_values: Vec<ChcExpr> = sub_tuples
        .iter()
        .filter_map(|t| {
            t.as_ref()
                .map(|vars| ChcExpr::var(vars[pool_index].clone()))
        })
        .collect();
    // As `adt_values`, but EXCLUDING element-free leaves (`nil`): their column
    // is the finite `±1e9` sentinel, the ±∞ identity of min/max, which would
    // clamp a real element above it. Used only by Min/Max/Sorted (Size/Height/
    // IntSum/CtorCount count every field). See [`is_empty_leaf_term`].
    let adt_elem_values: Vec<ChcExpr> = sub_tuples
        .iter()
        .zip(args)
        .filter_map(|(t, arg)| {
            t.as_ref().and_then(|vars| {
                (!is_empty_leaf_term(registry, arg)).then(|| ChcExpr::var(vars[pool_index].clone()))
            })
        })
        .collect();
    // ADT-free integer-field arguments (verbatim element values). `None` when
    // any int field is ADT-dependent — that would make min/max/head over a
    // proper subset, which is NOT a sound equality, so the recurrence is
    // withheld (leaving the value under-constrained, i.e. over-approximated).
    let int_args = |kind_needs_all: bool| -> Option<Vec<ChcExpr>> {
        let mut terms = Vec::new();
        for (field, arg) in ctor.fields.iter().zip(args) {
            if matches!(field.kind, FieldKind::Int) {
                let arg_expr: &ChcExpr = arg;
                if expr_mentions_registered_adt(arg_expr, registry) {
                    return None;
                }
                terms.push(arg_expr.clone());
                if !kind_needs_all {
                    break;
                }
            }
        }
        Some(terms)
    };
    let rhs = match kind {
        CataKind::Size => sum_exprs(std::iter::once(ChcExpr::int(1)).chain(adt_values).collect()),
        CataKind::Height => {
            if adt_values.is_empty() {
                ChcExpr::int(1)
            } else {
                let mut max = adt_values[0].clone();
                for value in &adt_values[1..] {
                    max = ChcExpr::ite(ChcExpr::ge(max.clone(), value.clone()), max, value.clone());
                }
                ChcExpr::add(ChcExpr::int(1), max)
            }
        }
        CataKind::IntSum => {
            let mut terms = Vec::new();
            for ((field, arg), _) in ctor.fields.iter().zip(args).zip(sub_tuples) {
                if matches!(field.kind, FieldKind::Int) {
                    // Only ADT-free Int arguments can be used verbatim.
                    let arg_expr: &ChcExpr = arg;
                    if expr_mentions_registered_adt(arg_expr, registry) {
                        return None;
                    }
                    terms.push(arg_expr.clone());
                }
            }
            terms.extend(adt_values);
            sum_exprs(terms)
        }
        CataKind::CtorCount(counted) => {
            let own = i64::from(&ctor.name == counted);
            sum_exprs(
                std::iter::once(ChcExpr::int(own))
                    .chain(adt_values)
                    .collect(),
            )
        }
        CataKind::RootDisc => ChcExpr::int(ctor.index as i64),
        CataKind::Min => {
            let mut terms = int_args(true)?; // all int elements
            terms.extend(adt_elem_values); // min columns of non-empty recursive fields
            if terms.is_empty() {
                ChcExpr::int(CATA_MIN_SENTINEL)
            } else {
                min_expr(terms)
            }
        }
        CataKind::Max => {
            let mut terms = int_args(true)?;
            terms.extend(adt_elem_values);
            if terms.is_empty() {
                ChcExpr::int(CATA_MAX_SENTINEL)
            } else {
                max_expr(terms)
            }
        }
        CataKind::Sorted => {
            // `adt_elem_values` are the sorted-columns of the NON-EMPTY recursive
            // fields; pull the matching min-columns from the same (non-empty)
            // sub-tuples for `head ≤ min(rest)`. Element-free leaves (`nil`) are
            // excluded: they are vacuously sorted and carry the sentinel as their
            // `min`, so a singleton's head must not be gated by `head ≤ sentinel`.
            let min_idx = pool.iter().position(|k| matches!(k, CataKind::Min));
            let rest_mins = min_idx.map(|mi| {
                sub_tuples
                    .iter()
                    .zip(args)
                    .filter_map(|(t, arg)| {
                        t.as_ref().and_then(|vars| {
                            (!is_empty_leaf_term(registry, arg))
                                .then(|| ChcExpr::var(vars[mi].clone()))
                        })
                    })
                    .collect::<Vec<_>>()
            });
            let int_head = int_args(false)?.into_iter().next();
            sorted_recurrence_rhs(int_head, rest_mins, adt_elem_values)?
        }
    };
    Some(ChcExpr::eq(tuple_value.clone(), rhs))
}

fn expr_mentions_registered_adt(expr: &ChcExpr, registry: &DtRegistry) -> bool {
    if registry.adt_sort_name(&expr.sort()).is_some() {
        return true;
    }
    match expr {
        ChcExpr::Var(v) => registry.adt_sort_name(&v.sort).is_some(),
        ChcExpr::FuncApp(name, _, args) => {
            registry.is_dt_member_symbol(name)
                || args
                    .iter()
                    .any(|a| expr_mentions_registered_adt(a, registry))
        }
        ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) => args
            .iter()
            .any(|a| expr_mentions_registered_adt(a, registry)),
        ChcExpr::ConstArray(_, v) => expr_mentions_registered_adt(v, registry),
        _ => false,
    }
}

/// Catamorphism consequences of `(_ is C)(t)` on `t`'s tuple. Each returned
/// conjunct is implied by the tester under the real catamorphism semantics.
fn tester_consequences(
    pool: &[CataKind],
    ctor: &CtorInfo,
    tuple: &[ChcVar],
    n_ctors: usize,
) -> Vec<ChcExpr> {
    let _ = n_ctors;
    let adt_fields = ctor.adt_field_count();
    let int_fields = ctor
        .fields
        .iter()
        .filter(|f| matches!(f.kind, FieldKind::Int))
        .count();
    let mut out = Vec::new();
    for (k, kind) in pool.iter().enumerate() {
        let value = ChcExpr::var(tuple[k].clone());
        match kind {
            CataKind::Size => {
                if adt_fields == 0 {
                    out.push(ChcExpr::eq(value, ChcExpr::int(1)));
                } else {
                    out.push(ChcExpr::ge(value, ChcExpr::int(1 + adt_fields as i64)));
                }
            }
            CataKind::Height => {
                if adt_fields == 0 {
                    out.push(ChcExpr::eq(value, ChcExpr::int(1)));
                } else {
                    out.push(ChcExpr::ge(value, ChcExpr::int(2)));
                }
            }
            CataKind::IntSum => {}
            CataKind::CtorCount(counted) => {
                if counted == &ctor.name {
                    out.push(ChcExpr::ge(value, ChcExpr::int(1)));
                } else if adt_fields == 0 {
                    // A leaf of a different constructor contains zero
                    // occurrences of `counted` (within this subtree).
                    out.push(ChcExpr::eq(value, ChcExpr::int(0)));
                }
            }
            CataKind::RootDisc => {
                out.push(ChcExpr::eq(value, ChcExpr::int(ctor.index as i64)));
            }
            // An element-free leaf (e.g. `nil`) pins `min`/`max` to the fold
            // sentinels exactly; any constructor carrying an element leaves
            // them unknown from the tester alone.
            CataKind::Min => {
                if adt_fields == 0 && int_fields == 0 {
                    out.push(ChcExpr::eq(value, ChcExpr::int(CATA_MIN_SENTINEL)));
                }
            }
            CataKind::Max => {
                if adt_fields == 0 && int_fields == 0 {
                    out.push(ChcExpr::eq(value, ChcExpr::int(CATA_MAX_SENTINEL)));
                }
            }
            // Any leaf (no recursive field: `nil`, singletons) is sorted.
            CataKind::Sorted => {
                if adt_fields == 0 {
                    out.push(ChcExpr::eq(value, ChcExpr::int(1)));
                }
            }
        }
    }
    out
}

// ============================================================================
// Debug: dump a datatype-free abstract LIA problem as a solvable HORN script
// ============================================================================

/// Serialize a datatype-free LIA CHC problem to a standalone `(set-logic HORN)`
/// SMT-LIB script (diagnostic only; see `--chc-cata-dump-abstract`).
pub(crate) fn dump_abstract_lia_problem(problem: &ChcProblem) -> String {
    let preds = problem.predicates();
    let pred_name = |id: PredicateId| -> String { quote_symbol(&preds[id.index()].name) };
    let emit_app = |id: PredicateId, args: &[ChcExpr]| -> String {
        if args.is_empty() {
            pred_name(id)
        } else {
            let a: Vec<String> = args.iter().map(InvariantModel::expr_to_smtlib).collect();
            format!("({} {})", pred_name(id), a.join(" "))
        }
    };

    let mut s = String::from("(set-logic HORN)\n");
    for pred in preds {
        let sorts: Vec<String> = pred.arg_sorts.iter().map(sort_to_smtlib).collect();
        s.push_str(&format!(
            "(declare-fun {} ({}) Bool)\n",
            quote_symbol(&pred.name),
            sorts.join(" ")
        ));
    }
    for clause in problem.clauses() {
        let mut vars = clause.body.vars();
        if let ClauseHead::Predicate(_, args) = &clause.head {
            for a in args {
                for v in a.vars() {
                    if !vars.contains(&v) {
                        vars.push(v);
                    }
                }
            }
        }
        let binders: Vec<String> = vars
            .iter()
            .map(|v| format!("({} {})", quote_symbol(&v.name), sort_to_smtlib(&v.sort)))
            .collect();
        let mut body_parts: Vec<String> = Vec::new();
        if let Some(c) = &clause.body.constraint {
            body_parts.push(InvariantModel::expr_to_smtlib(c));
        }
        for (pid, args) in &clause.body.predicates {
            body_parts.push(emit_app(*pid, args));
        }
        let body = match body_parts.len() {
            0 => "true".to_string(),
            1 => body_parts.remove(0),
            _ => format!("(and {})", body_parts.join(" ")),
        };
        let head = match &clause.head {
            ClauseHead::False => "false".to_string(),
            ClauseHead::Predicate(pid, args) => emit_app(*pid, args),
        };
        let imp = format!("(=> {body} {head})");
        if binders.is_empty() {
            s.push_str(&format!("(assert {imp})\n"));
        } else {
            s.push_str(&format!(
                "(assert (forall ({}) {imp}))\n",
                binders.join(" ")
            ));
        }
    }
    s.push_str("(check-sat)\n");
    s
}

// ============================================================================
// Obligation discharge (fresh raw executor, fail-closed)
// ============================================================================

/// Run one obligation script on a fresh `ay_dpll` executor. Returns `true`
/// ONLY for a definitive `unsat`; every other outcome (sat, unknown, parse
/// error, executor error, ay-internal panic) fails closed.
///
/// Diagnostics: set `--chc-cata-dump-obligations <dir>` to write every
/// non-discharging script to `<dir>` for offline replay.
pub(crate) fn run_obligation_expect_unsat(script: &str, budget: Duration) -> bool {
    let discharged = run_obligation_expect_unsat_impl(script, budget);
    if !discharged {
        if let Some(dir) = ay_core::misc_cli_flags()
            .chc_cata_dump_obligations
            .as_deref()
        {
            let dir = std::path::PathBuf::from(dir);
            let _ = std::fs::create_dir_all(&dir);
            let stamp = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map_or(0, |d| d.as_nanos());
            let _ = std::fs::write(dir.join(format!("cata_obligation_{stamp}.smt2")), script);
        }
    }
    discharged
}

fn run_obligation_expect_unsat_impl(script: &str, budget: Duration) -> bool {
    use std::panic::AssertUnwindSafe;

    let timeout_ms = budget.as_millis();
    let script_with_timeout = if timeout_ms > 0 && timeout_ms < u128::from(u64::MAX) {
        // The :timeout option must precede assertions; splice after set-logic.
        match script.find('\n') {
            Some(pos) => {
                let (head, tail) = script.split_at(pos + 1);
                format!("{head}(set-option :timeout {timeout_ms})\n{tail}")
            }
            None => script.to_string(),
        }
    } else {
        script.to_string()
    };

    let Ok(commands) = ay_frontend::parse(&script_with_timeout) else {
        return false;
    };
    let outputs = match ay_core::catch_ay_panics(
        AssertUnwindSafe(|| {
            let mut exec = ay_dpll::Executor::new();
            exec.execute_all(&commands).map_err(|_| ())
        }),
        |_| Err(()),
    ) {
        Ok(outputs) => outputs,
        Err(()) => return false,
    };
    outputs.first().map(String::as_str) == Some("unsat")
}

// ============================================================================
// Cata-aware query discharge for COMPOSED models (final CLI gate support)
// ============================================================================

/// Check that a COMPOSED catamorphism model excludes the error states of
/// `problem`: for every query clause, `interpretations ∧ θ` must be UNSAT
/// under facts that are true of the real catamorphisms (ties are implicit —
/// the interpretations already apply the reserved UFs to the clause's own
/// terms; we add each applied term's min facts, defining recurrences for
/// constructor terms, and one-level unfolding case splits for the rest).
///
/// This is the query-only safety gate for models the generic
/// `verify_model_query_only` cannot evaluate (it has no interpretation for
/// the reserved catamorphism symbols, so it conservatively fails). The
/// polarity is identical: `true` ONLY when EVERY query clause discharges
/// `unsat`; any parse failure, unknown, sat, missing interpretation, or
/// non-cata model returns `false` (fail-closed for the caller's demotion
/// logic).
pub(crate) fn cata_model_excludes_error(
    problem: &ChcProblem,
    model: &InvariantModel,
    per_query_budget: Duration,
    deadline: Option<Instant>,
) -> bool {
    // Only applicable to models that actually mention reserved cata symbols.
    let mut mentions_cata = false;
    for pred in problem.predicates() {
        if let Some(interp) = model.get(&pred.id) {
            if formula_mentions_cata(&interp.formula) {
                mentions_cata = true;
                break;
            }
        }
    }
    if !mentions_cata {
        return false;
    }

    let registry = DtRegistry::build(problem);
    if registry.is_empty() {
        return false;
    }

    for clause in problem.clauses() {
        if !clause.is_query() {
            continue;
        }
        if let Some(deadline) = deadline {
            if Instant::now() >= deadline {
                return false;
            }
        }
        let Some(script) = query_discharge_script(problem, model, clause, &registry) else {
            return false;
        };
        if !run_obligation_expect_unsat(&script, per_query_budget) {
            return false;
        }
    }
    true
}

fn formula_mentions_cata(expr: &ChcExpr) -> bool {
    match expr {
        ChcExpr::FuncApp(name, _, args) => {
            CataKind::parse_symbol(name).is_some() || args.iter().any(|a| formula_mentions_cata(a))
        }
        ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) => {
            args.iter().any(|a| formula_mentions_cata(a))
        }
        ChcExpr::ConstArray(_, v) => formula_mentions_cata(v),
        _ => false,
    }
}

/// Collect every `(term, sort_name)` a reserved cata UF is applied to.
fn collect_cata_applications(
    expr: &ChcExpr,
    out: &mut Vec<(ChcExpr, String)>,
    kinds_by_sort: &mut BTreeMap<String, Vec<CataKind>>,
) {
    if let ChcExpr::FuncApp(name, _, args) = expr {
        if let Some((kind, sort_name)) = CataKind::parse_symbol(name) {
            if args.len() == 1 {
                let term = args[0].as_ref().clone();
                if !out.iter().any(|(t, _)| t == &term) {
                    out.push((term, sort_name.to_string()));
                }
                let kinds = kinds_by_sort.entry(sort_name.to_string()).or_default();
                if !kinds.contains(&kind) {
                    kinds.push(kind);
                }
            }
        }
    }
    match expr {
        ChcExpr::FuncApp(_, _, args) | ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) => {
            for arg in args {
                collect_cata_applications(arg, out, kinds_by_sort);
            }
        }
        ChcExpr::ConstArray(_, v) => collect_cata_applications(v, out, kinds_by_sort),
        _ => {}
    }
}

/// Build the discharge script for one query clause of the ORIGINAL problem
/// under the composed model: `⋀ interps(args) ∧ θ ∧ cata-facts` must be UNSAT.
fn query_discharge_script(
    _problem: &ChcProblem,
    model: &InvariantModel,
    clause: &HornClause,
    registry: &DtRegistry,
) -> Option<String> {
    // Instantiate every body predicate's interpretation at its argument terms.
    let mut instantiated: Vec<ChcExpr> = Vec::new();
    for (pred_id, args) in &clause.body.predicates {
        let interp = model.get(pred_id)?;
        if interp.vars.len() != args.len() {
            return None;
        }
        let subst: Vec<(ChcVar, ChcExpr)> = interp
            .vars
            .iter()
            .cloned()
            .zip(args.iter().cloned())
            .collect();
        instantiated.push(interp.formula.substitute(&subst));
    }

    // Collect the ADT terms the cata UFs are applied to (plus which kinds).
    let mut applications: Vec<(ChcExpr, String)> = Vec::new();
    let mut kinds_by_sort: BTreeMap<String, Vec<CataKind>> = BTreeMap::new();
    for formula in &instantiated {
        collect_cata_applications(formula, &mut applications, &mut kinds_by_sort);
    }
    // The `Sorted` recurrence references the `Min` UF of its recursive fields;
    // ensure `Min` is declared (and available as a "pool" member) for every
    // sort that carries `Sorted`, even if the model formula never mentions the
    // min column directly. `compose_model` materializes it in practice, but
    // guarding here keeps the query gate from tripping on an undeclared symbol
    // (which would fail-closed and needlessly demote a valid Safe to unknown).
    for kinds in kinds_by_sort.values_mut() {
        if kinds.iter().any(|k| matches!(k, CataKind::Sorted))
            && !kinds.iter().any(|k| matches!(k, CataKind::Min))
        {
            kinds.push(CataKind::Min);
        }
    }

    let mut smt = String::with_capacity(4096);
    smt.push_str("(set-logic ALL)\n");
    smt.push_str(&registry.emit_declare_datatypes());
    for (sort_name, kinds) in &kinds_by_sort {
        if registry.ctors(sort_name).is_none() {
            return None;
        }
        for kind in kinds {
            smt.push_str(&format!(
                "(declare-fun {} ({}) Int)\n",
                quote_symbol(&kind.uf_name(sort_name)),
                quote_symbol(sort_name)
            ));
        }
    }

    // Clause variables (constraint + predicate arguments + applied terms).
    let mut declared: Vec<String> = Vec::new();
    let mut declare_var = |smt: &mut String, var: &ChcVar| {
        if !declared.contains(&var.name) {
            declared.push(var.name.clone());
            smt.push_str(&format!(
                "(declare-const {} {})\n",
                quote_symbol(&var.name),
                sort_to_smtlib(&var.sort)
            ));
        }
    };
    for var in clause.body.vars() {
        declare_var(&mut smt, &var);
    }
    for formula in &instantiated {
        for var in formula.vars() {
            declare_var(&mut smt, &var);
        }
    }

    // θ and the instantiated interpretations.
    if let Some(constraint) = &clause.body.constraint {
        smt.push_str("(assert ");
        smt.push_str(&InvariantModel::expr_to_smtlib(constraint));
        smt.push_str(")\n");
    }
    for formula in &instantiated {
        smt.push_str("(assert ");
        smt.push_str(&InvariantModel::expr_to_smtlib(formula));
        smt.push_str(")\n");
    }

    // True catamorphism facts at every applied term: min facts, plus direct
    // recurrences for constructor terms or a one-level unfolding case split
    // for everything else.
    for (term, sort_name) in &applications {
        let kinds = kinds_by_sort.get(sort_name)?;
        let n_ctors = registry.ctors(sort_name).map_or(0, <[CtorInfo]>::len);
        for kind in kinds {
            let uf_term = func_app(kind.uf_name(sort_name), ChcSort::Int, vec![term.clone()]);
            for fact in cata_min_facts(kind, &uf_term, n_ctors) {
                smt.push_str("(assert ");
                smt.push_str(&InvariantModel::expr_to_smtlib(&fact));
                smt.push_str(")\n");
            }
        }
        let mut is_ctor_term = false;
        if let ChcExpr::FuncApp(name, _, args) = term {
            if let Some(ctor) = registry.ctor(sort_name, name) {
                if ctor.fields.len() == args.len() {
                    is_ctor_term = true;
                    let field_terms: Vec<ChcExpr> =
                        args.iter().map(|a| a.as_ref().clone()).collect();
                    for kind in kinds {
                        if let Some(rhs) = recurrence_rhs(kind, ctor, &field_terms, registry, kinds)
                        {
                            let lhs =
                                func_app(kind.uf_name(sort_name), ChcSort::Int, vec![term.clone()]);
                            smt.push_str("(assert ");
                            smt.push_str(&InvariantModel::expr_to_smtlib(&ChcExpr::eq(lhs, rhs)));
                            smt.push_str(")\n");
                        }
                    }
                }
            }
        }
        if !is_ctor_term {
            if let Some(axiom) = standalone_unfolding_axiom(registry, kinds, term, sort_name) {
                smt.push_str("(assert ");
                smt.push_str(&InvariantModel::expr_to_smtlib(&axiom));
                smt.push_str(")\n");
            }
        }
    }

    smt.push_str("(check-sat)\n");
    Some(smt)
}

/// One-level unfolding case split for `term` of sort `sort_name` over the
/// given catamorphism kinds (each branch is a true fact of the real
/// catamorphisms). Free-function twin of `ClauseCtx::unfolding_axiom`.
fn standalone_unfolding_axiom(
    registry: &DtRegistry,
    kinds: &[CataKind],
    term: &ChcExpr,
    sort_name: &str,
) -> Option<ChcExpr> {
    let ctors = registry.ctors(sort_name)?;
    if ctors.is_empty() {
        return None;
    }
    let mut branches = Vec::new();
    for ctor in ctors {
        let mut parts = vec![func_app(
            format!("is-{}", ctor.name),
            ChcSort::Bool,
            vec![term.clone()],
        )];
        let field_terms: Vec<ChcExpr> = ctor
            .fields
            .iter()
            .map(|field| {
                func_app(
                    field.selector.clone(),
                    field.sort.clone(),
                    vec![term.clone()],
                )
            })
            .collect();
        for kind in kinds {
            let lhs = func_app(kind.uf_name(sort_name), ChcSort::Int, vec![term.clone()]);
            if let Some(rhs) = recurrence_rhs(kind, ctor, &field_terms, registry, kinds) {
                parts.push(ChcExpr::eq(lhs, rhs));
            }
            for (field, sub_term) in ctor.fields.iter().zip(&field_terms) {
                if let FieldKind::Adt(field_sort) = &field.kind {
                    let sub = func_app(
                        kind.uf_name(field_sort),
                        ChcSort::Int,
                        vec![sub_term.clone()],
                    );
                    let n_sub = registry.ctors(field_sort).map_or(0, <[CtorInfo]>::len);
                    parts.extend(cata_min_facts(kind, &sub, n_sub));
                }
            }
        }
        branches.push(ChcExpr::and_all(parts));
    }
    Some(ChcExpr::or_all(branches))
}

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
#[path = "tests.rs"]
mod tests;

#[allow(clippy::unwrap_used, clippy::panic, clippy::expect_used)]
#[cfg(test)]
#[path = "ice_dt_spike.rs"]
mod ice_dt_spike;

#[allow(clippy::unwrap_used, clippy::panic, clippy::expect_used)]
#[cfg(test)]
#[path = "ice_dt_lra_spike.rs"]
mod ice_dt_lra_spike;
