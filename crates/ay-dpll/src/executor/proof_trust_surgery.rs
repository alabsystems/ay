// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![doc = include_str!("proof_trust_surgery/overview.md")]

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{
    AletheRule, FarkasAnnotation, Proof, ProofId, ProofStep, Sort, Symbol, TermId, TheoryLemmaKind,
    TheoryLit,
};
use ay_frontend::command::Term as FrontendTerm;

use super::proof_euf_lemma::{EufLemmaPlan, EufTarget};
use super::proof_surface_syntax::strip_frontend_annotations;
use super::proof_trust_surgery_ite::ProvenanceItePlan;
use super::proof_trust_surgery_ite_plan::IteLiftPlan;
use super::proof_trust_surgery_provenance::{
    canonical_term_work as quant_canonical_term_work, prepare_rebuilt_premise_append,
    retained_surface_plan_mix_is_safe, surface_or_decomposition_matches, surface_source_is_bounded,
    surgery_sources_are_bounded, OperandCharge, OriginalSourceIndex, SurgeryPlanningBudget,
    MAX_PROVENANCE_REPAIR_TERMS,
};
use super::proof_trust_surgery_provenance_or::{surface_override_policy_allows, ProvenanceOrPlan};
use super::{proof_farkas, Executor, NATIVE_API_ASSERTION_PLACEHOLDER};

#[path = "proof_trust_surgery_quant_plan.rs"]
mod quant_plan;
#[path = "proof_trust_surgery_quant_surface.rs"]
mod quant_surface;
#[path = "proof_trust_surgery_surface_intern.rs"]
mod surface_intern;
#[path = "proof_trust_surgery_surface_plans.rs"]
mod surface_plans;
#[path = "proof_trust_surgery_taut_surface.rs"]
mod taut_surface;
#[path = "proof_trust_surgery_volume.rs"]
mod volume;

#[path = "proof_trust_surgery/and_collapse.rs"]
mod and_collapse;
#[path = "proof_trust_surgery/assume_classification.rs"]
mod assume_classification;
#[path = "proof_trust_surgery/authored_array.rs"]
mod authored_array;
#[path = "proof_trust_surgery/authored_or.rs"]
mod authored_or;
#[path = "proof_trust_surgery/distinct_classification.rs"]
mod distinct_classification;
#[path = "proof_trust_surgery/equality_collapse.rs"]
mod equality_collapse;
#[path = "proof_trust_surgery/false_collapse.rs"]
mod false_collapse;
#[path = "proof_trust_surgery/false_collapse_shape.rs"]
mod false_collapse_shape;
#[path = "proof_trust_surgery/ground_linear_collapse.rs"]
mod ground_linear_collapse;
#[path = "proof_trust_surgery/lemma_bridges.rs"]
mod lemma_bridges;
#[path = "proof_trust_surgery/quant_rebuild.rs"]
mod quant_rebuild;
#[path = "proof_trust_surgery/quant_terms.rs"]
mod quant_terms;
#[path = "proof_trust_surgery/rebuild.rs"]
mod rebuild;
#[path = "proof_trust_surgery/repaired_units.rs"]
mod repaired_units;
#[cfg(test)]
#[path = "proof_trust_surgery/surface_let_tests.rs"]
mod surface_let_tests;
#[path = "proof_trust_surgery/surface_terms.rs"]
pub(in crate::executor) mod surface_terms;
#[path = "proof_trust_surgery/tautology.rs"]
mod tautology;
#[path = "proof_trust_surgery/term_helpers.rs"]
mod term_helpers;
#[path = "proof_trust_surgery/trichotomy.rs"]
mod trichotomy;

use false_collapse_shape::FalseCollapseShape;
use quant_terms::{
    lift_surface_binders_from_ground, raw_instance_matches_substitution, surface_subst_ground,
    value_to_surface,
};
use surface_terms::{eq_flip_equivalent, expand_surface_lets};
use term_helpers::{
    atom_of, complement_of, decode_binary_equality, equality_is_pure_linear_arith,
    term_is_pure_linear_arith,
};

/// How a defective `assume` gets repaired.
enum AssumePlan {
    /// Surface `(distinct x1 .. xn)`, n >= 3, exported as the expanded
    /// pairwise conjunction: assume the raw `distinct`, bridge via
    /// `distinct_elim` + `equiv_pos2` to the conjunction.
    Distinct {
        /// Raw `(distinct x1 .. xn)` application (prints like the file).
        raw: TermId,
        /// The canonical pairwise conjunction (the old assume's term).
        and_term: TermId,
        /// Conjuncts of `and_term`, in order.
        conjs: Vec<TermId>,
    },
    /// Surface `(and c1 .. cn)` whose conjuncts were arithmetic-normalized
    /// (or binary-`distinct` sugar): assume the raw surface conjunction,
    /// bridge each extracted unit where the raw conjunct differs from the
    /// canonical one.
    AndBounds {
        /// Raw `(and raw_1 .. raw_n)` application.
        raw_and: TermId,
        /// Per conjunct: the raw surface literal and, when it differs from
        /// the canonical conjunct, the raw literal's atom (bridge pivot).
        raws: Vec<(TermId, Option<TermId>)>,
        /// Canonical conjuncts (of the old assume's term), in order.
        conjs: Vec<TermId>,
    },
    /// Surface `(and c1 .. cn)` with binary-`distinct` sugar conjuncts
    /// (exported as canonical `(not (= s t))`, whose print no longer matches
    /// the file): assume the raw surface conjunction and RE-DERIVE the
    /// canonical conjunction as a unit — per-conjunct `and_pos` extraction
    /// (bridged via `distinct_elim` + `equiv_pos2` where sugared, or a
    /// certified orientation lemma where arithmetic-normalized) closed by
    /// `and_neg` — onto which EVERY consumer is remapped (unlike the
    /// bounds class, consumers may resolve the assume anywhere).
    AndDistinct {
        /// Raw `(and raw_1 .. raw_n)` application (prints like the file;
        /// folded-away conjuncts like `(= c c)` reappear here raw).
        raw_and: TermId,
        /// The canonical conjunction (the old assume's term).
        and_term: TermId,
        /// The raw conjuncts that supply canonical conjunct units, in
        /// canonical-conjunct order.
        units: Vec<AndDistinctUnit>,
        /// Canonical conjuncts (of the old assume's term), in order.
        conjs: Vec<TermId>,
    },
    /// A single arithmetic-normalized bound literal (e.g. surface `(> a 5)`
    /// exported as the canonical `(< 5 a)`): assume the raw surface literal,
    /// bridge to the canonical literal by a certified `[1, 1]` orientation
    /// lemma, and remap every consumer onto the derived unit.
    Literal {
        /// Raw surface literal (prints like the file).
        raw: TermId,
        /// The raw literal's atom (the bridge resolution pivot).
        atom: TermId,
        /// The canonical literal (the old assume's term).
        canonical: TermId,
    },
    /// A finite-domain quantifier expansion assume (#quant-expansion-proof):
    /// preprocessing replaced a top-level `forall` assertion in place with
    /// the merged ground-instance conjunction, and the exporter assumed the
    /// conjunction — which no external checker can match to the problem's
    /// `forall` premise. Replaced by an assume of the ORIGINAL `forall`;
    /// every consumed conjunct is re-DERIVED from it: `forall_inst`
    /// (positional binder-value args) + `or` + resolution to the raw
    /// substituted body, `implies_pos` + per-atom unit `la_generic` guard
    /// discharge + `and_neg`, and a certified `[1, 1]` strict-Int
    /// orientation bridge onto the canonical conjunct where the tightening
    /// pass rewrote it. All consumers must be recognized unit-extraction
    /// patterns (like [`AssumePlan::AndBounds`]).
    QuantExpansion {
        /// The original `forall` assertion (a genuine problem premise).
        forall_term: TermId,
        /// Index of its parsed authored source in `originals`.
        assertion_index: usize,
        /// Canonical conjuncts of the expansion (the old assume's term).
        conjs: Vec<TermId>,
        /// Folded instance term -> binder values (in binder order).
        instances: HashMap<TermId, Vec<TermId>>,
    },
}

/// A planned per-instance derivation chain from an original `forall`
/// premise to a single unit clause (#quant-expansion-proof). Every
/// ingredient is validated at plan time: the substituted body is built from
/// the premise's own SURFACE syntax (so the printed `forall_inst`
/// conclusion is exactly the instantiation an external checker recomputes),
/// each guard atom is certified as a ground arithmetic tautology by the
/// independent Farkas checker, and the optional strict-Int bridge is a
/// re-verified `[1, 1]` `la_generic` lemma.
struct QuantInstanceChain {
    /// Binder values, in binder order (the `forall_inst` positional args).
    values: Vec<TermId>,
    /// Raw-interned substituted body (the `forall_inst` instance).
    phi: TermId,
    /// `(guard term, guard atoms)` when `phi` is `(=> g b)`; each atom is a
    /// certified ground arithmetic truth, all atoms distinct.
    guard: Option<(TermId, Vec<TermId>)>,
    /// The consequent literal the chain concludes (`phi` when no guard).
    body_lit: TermId,
    /// The final unit term consumers expect. When it differs from
    /// `body_lit`, the plan-time-validated `[1, 1]` pair lemma
    /// `(cl target (not body_lit))` bridges the two.
    target: TermId,
}

/// A recognized trust unit `(cl L)` that is a preprocessing-folded
/// CONSEQUENCE of a quantifier-expansion instance and up to one original
/// premise (#quant-expansion-proof): e.g. the conjunct
/// `(<= (f 24) (+ (f 25) (- 1)))` folded with the asserted `(= (f 25) 26)`
/// into `(<= (f 24) 25)`. Replaced by the instance derivation chain, an
/// assume per consumed original, and one re-verified `la_generic` lemma
/// `(cl (not inst) (not orig).. L)` closed by resolutions.
struct QuantConsequencePlan {
    /// The original `forall` assertion the instance derives from.
    forall_term: TermId,
    /// The plan-time-built derivation of `(cl chain.target)`.
    chain: QuantInstanceChain,
    /// Original premises consumed by the folding (assumed in the rebuild).
    supports: Vec<TermId>,
    /// The validated lemma clause `(not chain.target) (not s)... L`,
    /// ending in the trust unit `L` the consumers expect.
    lemma: Vec<TermId>,
}

/// A folded trust unit `(cl (not Q))` recovered from one authenticated direct
/// E-matching instance of `Q` and up to one original arithmetic premise.
///
/// The producer emits `forall_inst` as `(not Q) \/ instance`, derives
/// `not(instance)` from the original arithmetic premise with a separately
/// checked Farkas lemma, and resolves the two clauses.  Crucially, it does not
/// assume `Q` while deriving `not Q`; the existing proof's authored `Q`
/// assumption closes the final contradiction.
struct QuantNegationPlan {
    /// Canonical source term carried by the pre-surgery proof.  Its Assume is
    /// replaced with `forall_term` so the repaired negative unit remains an
    /// exact complement at both the internal and external checker layers.
    source_quantifier: TermId,
    /// Authored assertion position used to recover the exact surface spelling.
    assertion_index: usize,
    /// Rebuilt original forall term used by the strict `forall_inst` step.
    forall_term: TermId,
    /// Exact positional values and raw ground instance.
    chain: QuantInstanceChain,
    /// Original arithmetic premises consumed by the conflict (currently at
    /// most one; bounded search and independent Farkas validation below).
    supports: Vec<TermId>,
    /// Validated arithmetic conflict clause `(not instance) (not support)..`.
    lemma: Vec<TermId>,
}

/// One raw conjunct of an [`AssumePlan::AndDistinct`] assume that supplies
/// canonical conjunct unit(s).
#[derive(Clone)]
struct AndDistinctUnit {
    /// Operand position in the raw conjunction (the `and_pos` index).
    pos: u32,
    /// The raw conjunct term.
    raw: TermId,
    kind: AndDistinctKind,
}

/// How an extracted raw conjunct bridges to its canonical conjunct(s).
#[derive(Clone)]
enum AndDistinctKind {
    /// The raw conjunct IS the canonical conjunct.
    Plain,
    /// Arithmetic orientation bridge: certified `[1, 1]` `la_generic` lemma
    /// over the raw literal's atom.
    Arith { atom: TermId },
    /// Binary `(distinct s t)` sugar exported as the canonical
    /// `(not (= s t))`: bridge via `distinct_elim` + `equiv_pos2`.
    DistinctBinary,
    /// N-ary `(distinct ..)` sugar exported as `count` pairwise canonical
    /// conjuncts: `distinct_elim` + `equiv_pos2` to the expansion
    /// conjunction `and_term`, then one `and_pos` per pairwise conjunct.
    DistinctNary { and_term: TermId, count: u32 },
    /// An `or`-conjunct whose canonical export REORDERED the disjuncts
    /// and/or FLIPPED individual binary-equality literals (#C2b): the raw
    /// (file-order, file-orientation) disjunction is re-interned for the
    /// assume, and its unit bridges to the canonical or-term via the `or`
    /// rule, one certified `eq_symmetric` + `equiv_pos1/2` orientation
    /// bridge per flipped literal, and the `or_neg` permutation closure
    /// (the C1 or-split reorder machinery).
    OrPerm {
        /// `(raw disjunct, canonical disjunct)` pairs in RAW disjunct
        /// order; each pair is either identical or a top-level
        /// binary-equality orientation flip (possibly under one `not`).
        lits: Vec<(TermId, TermId)>,
    },
}

/// A recognized preprocessor-derived unit trust step `(cl L)` where an
/// original disjunctive assertion (surface `(or ...)` or De Morgan
/// `(not (and ...))`) contains `L` and every OTHER disjunct is refuted by
/// its complementary original assertion. Replaced by an assume of the
/// disjunction, its `or` decomposition (the printer resugars a De Morgan
/// surface to `not_and`), and one resolution per remaining disjunct against
/// the complementary original's assume.
struct OrUnitPlan {
    /// The original disjunctive assertion (canonical or-term; prints via
    /// the surface overrides).
    orig: TermId,
    /// Its disjuncts, in canonical order (the decomposition step's clause).
    disjuncts: Vec<TermId>,
    /// Per non-`L` disjunct, in decomposition order: (resolution pivot
    /// atom, the complementary ORIGINAL assertion discharging it).
    eliminations: Vec<(TermId, TermId)>,
}

/// A singleton trust clause whose term is the canonical packed `or` form of
/// one exact authored, right-associated implication chain. The canonical
/// authored `or` is assumed and decomposed; independently checked linear
/// bridges normalize comparison literals, and `or_neg` packs the resulting
/// exact disjunct set back into the unit the existing proof consumes. The
/// Alethe printer replays that internal `or` decomposition as `implies_pos`
/// steps so the premise still prints exactly like the authored implication.
///
/// This is deliberately a source-authenticated plan, not a general
/// implication simplifier: `source_or` is the canonical half of an exact
/// authenticated `(canonical, parsed)` entry from `originals`, and every source
/// literal must align one-to-one with an exact target disjunct.
struct NormalizedAuthoredOrPlan {
    /// Canonical `(or (not A0) (not A1) ... C)` for the authored implication.
    source_or: TermId,
    /// Exact disjuncts of `source_or`.
    source_disjuncts: Vec<TermId>,
    /// Canonical packed `(or (not A0) (not A1) ... C)` consumed by the old
    /// proof's downstream steps.
    target_or: TermId,
    /// Exact canonical disjuncts of `target_or`.
    target_disjuncts: Vec<TermId>,
    /// Source literals aligned with the target disjuncts.
    literals: Vec<NormalizedAuthoredOrLiteral>,
}

struct NormalizedAuthoredOrLiteral {
    source: TermId,
    canonical: TermId,
    /// The source literal's atom when a checked two-literal LRA bridge is
    /// needed. `None` means `source == canonical`.
    bridge_atom: Option<TermId>,
}

/// A singleton packed disjunction `(or (not E) (ite G T F))` whose then arm
/// follows from two exact authored premises, the array equality `E` and guard
/// `G`, through the strict `ArrayRowChain` schema.  The else arm is irrelevant
/// once `G` is discharged; ordinary `ite_neg2` and `or_neg` steps lift the
/// certified array fact back to the original singleton term.
struct AuthoredArrayItePlan {
    target_or: TermId,
    array_equality: TermId,
    /// Raw-interned exact source spelling of the authored arithmetic guard.
    /// This remains a distinct proof premise when elaboration normalized the
    /// guard's arithmetic expression.
    guard_source: TermId,
    /// Canonical guard consumed by the certified ROW and ITE rules.
    guard: TermId,
    then_branch: TermId,
    ite_term: TermId,
    select_congruence: TermId,
    store_hit: TermId,
    congruence_clause: Vec<TermId>,
    row1_clause: Vec<TermId>,
    transitivity_clause: Vec<TermId>,
}

/// How a recognized preprocessor-derived EUF-transitivity TAUTOLOGY unit
/// `(cl T)` gets re-derived (T is an `or`-term with exactly one implied
/// positive equality disjunct). Two routes:
enum TautRoute {
    /// `T = (or .. E .. ¬e1 .. ¬en)` where the `¬e` disjuncts' equalities
    /// form a transitivity chain proving `E`: one `eq_transitive` step
    /// `(cl ¬e1 .. ¬en E)`, each `¬ei` eliminated against the `or_neg`
    /// tautology `(cl T (not ¬ei))`, closed by the `E`-position `or_neg`.
    Plain {
        /// The `¬e` disjuncts, in disjunct order (ALL of them: the chain
        /// check requires every edge on the path, mirroring the checker).
        negs: Vec<TermId>,
    },
    /// `T = (or .. E .. A ..)` where `A = (and D1 .. Dm)` and each
    /// `Dj = (or ¬f1 .. ¬fp)` is a De Morganized conjunction whose
    /// equalities chain to `E` (the eq_diamond family's shape): per `Dj` an
    /// `eq_transitive` + `or_neg` elimination derives `(cl E Dj)`, an
    /// `and_neg` step recombines them into `(cl A E)`, and the outer
    /// `or_neg` pair closes `(cl T)`.
    And {
        /// The `and`-disjunct `A`.
        and_term: TermId,
        /// `A`'s conjuncts `D1 .. Dm`, in order.
        conjs: Vec<TermId>,
        /// Per conjunct: its `¬f` disjuncts, in order (chain-verified).
        per_conj_negs: Vec<Vec<TermId>>,
    },
}

/// A recognized preprocessor-derived EUF-transitivity tautology unit: a
/// mid-proof `assume` (or premiseless unit trust step) of an `or`-term `T`
/// that is valid on its own by equality transitivity. Such leaves are
/// checker-invalid (an `assume` that matches no problem premise / an
/// unchecked trust step); the plan re-derives `(cl T)` from NOTHING with
/// certified `eq_transitive` / `or_neg` / `and_neg` / `contraction` /
/// resolution steps, and every consumer is remapped onto the derived unit
/// (same clause content, so no consumer rewiring is needed).
struct OrTautologyPlan {
    /// The tautological `or`-term `T`.
    term: TermId,
    /// The implied positive equality disjunct `E`.
    eq: TermId,
    route: TautRoute,
}

/// A recognized preprocessing-COLLAPSE equality unit `(cl (= L R))`: the
/// assertions that define `L` and `R` were substituted away by
/// substitute-and-simplify, so the equality they entail arrives as a
/// premiseless `trust` leaf with no visible premise at all.
///
/// The repair re-introduces the ORIGINAL equality assertions the collapse
/// consumed (faithful: they ARE assertions of the problem file) and closes
/// the unit against them:
///
/// ```text
/// lemma  (cl (= L R) ¬h1 .. ¬hk)     ; eq_transitive / eq_congruent recipe
/// res    (cl (= L R) ¬h2 .. ¬hk)     ; against `assume h1`
/// …
/// res    (cl (= L R))
/// ```
///
/// The lemma itself is planned by the existing EUF planner
/// ([`Executor::plan_euf_lemma`]), so congruence-through-`store`/`select`
/// (needed whenever the substituted constant sits under a function symbol) is
/// covered by the same independently re-validated toolkit, not by a second
/// bespoke prover.
#[derive(Clone)]
struct SubstEqPlan {
    /// The synthesized lemma clause `[(= L R), ¬h1, .., ¬hk]`.
    lemma: Vec<TermId>,
    /// The ORIGINAL equality assertions `h1 .. hk`, aligned with
    /// `lemma[1..]`. Each is hoisted as an `assume` and resolved away.
    hyps: Vec<TermId>,
    /// The certified derivation recipe for `lemma`.
    euf: EufLemmaPlan,
}

/// A recognized Int-trichotomy trust step and its `or`-split consumer.
struct TrichotomyPlan {
    /// Index of the `or`-split step consuming the trust step.
    or_split_idx: usize,
    /// `(= x y)`.
    eq: TermId,
    /// `(<= x y)` / `(<= y x)` (raw-interned, `la_disequality` operand order).
    le_xy: TermId,
    le_yx: TermId,
    /// Their negations (the split literals).
    not_le_xy: TermId,
    not_le_yx: TermId,
    /// `(or eq (not le_xy) (not le_yx))` — the `la_disequality` conclusion.
    or_term: TermId,
    /// The strengthened literal implied by `(not (<= y x))`
    /// (i.e. `(<= x (+ y (- 1)))` up to normalization).
    strong_from_yx: TermId,
    /// The strengthened literal implied by `(not (<= x y))`.
    strong_from_xy: TermId,
}
