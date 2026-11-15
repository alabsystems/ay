// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Provenance plans and authored-conjunct inventory for consequence replay.

use ay_core::TermId;

/// How one non-authored consequence formula is derived from the authored
/// scope. Every variant's steps have strict validators; the plan itself
/// carries no authority.
#[derive(Clone)]
pub(super) enum ConsequencePlan {
    ForallInstance {
        quantifier: TermId,
        binding: Vec<TermId>,
    },
    SkolemInstance {
        source: TermId,
        quantified: TermId,
        witness: TermId,
        instance: TermId,
        positive: bool,
    },
    NegatedExistsDual {
        not_exists_root: TermId,
        exists: TermId,
        /// Units that discharge the co-literals of a clause-shaped root
        /// (`Not(And(E, ψ…))` / `(or (not E) …)`), resolved away before
        /// `qnt_neg_exists` so the dual rests on the derived `(not E)` unit.
        /// Empty for a bare `(not E)` root.
        co_units: Vec<TermId>,
    },
    /// The CONSEQUENT of an authored implication whose antecedent is itself
    /// derivable: `(=> A F)` (or its desugared `(or F (not A))`) plus `A`
    /// yields `F` by `implies_pos` and two resolutions; an authored Boolean
    /// equality `(= A F)` / `(= F A)` yields it by `equiv_pos2` / `equiv_pos1`
    /// (#iff-split-implied-authority).
    ImpliedConsequent {
        implication: TermId,
        antecedent: TermId,
    },
    /// An authored CLAUSE with universal literals instantiated
    /// ([`ClausalInstanceRecord`]).
    ClausalInstance {
        source: TermId,
        literals: Vec<ClausalLiteral>,
    },
    /// A binder split ([`QuantifierJoinRecord`]) of the derivable `source`.
    QuantifierJoin {
        source: TermId,
        joined: TermId,
        nested: TermId,
        positive: bool,
    },
    /// A ground equality `(= L R)` derived by congruence: `cong` steps over
    /// argument equalities that are themselves authored/planned units (or
    /// recursively congruent), `refl` at identical sides. The plan key is
    /// `equality` itself; every premise is re-derived at stitch time.
    CongruenceEquality { equality: TermId },
}

impl ConsequencePlan {
    /// The source formula whose unit this plan's derivation starts from.
    pub(super) fn source(&self) -> TermId {
        match self {
            Self::ForallInstance { quantifier, .. } => *quantifier,
            Self::SkolemInstance { source, .. } => *source,
            Self::NegatedExistsDual {
                not_exists_root, ..
            } => *not_exists_root,
            Self::ImpliedConsequent { implication, .. } => *implication,
            Self::ClausalInstance { source, .. } => *source,
            Self::QuantifierJoin { source, .. } => *source,
            Self::CongruenceEquality { equality } => *equality,
        }
    }
}

/// How one literal of a clause-shaped source is rewritten.
#[derive(Clone, Debug)]
pub(in crate::executor) enum ClausalLiteral {
    /// Kept verbatim.
    Keep,
    /// The literal is `(forall x⃗ B)`; it becomes `B[x⃗ := binding]` by
    /// `forall_inst`.
    Forall { binding: Vec<TermId> },
    /// The literal is `(not E)` with `E = (exists x⃗ B)`; `qnt_neg_exists`
    /// turns it into the dual `forall` (`F = (forall x⃗ (not B))`), which
    /// `forall_inst` instantiates at `binding`.
    NegatedExists {
        forall: TermId,
        binding: Vec<TermId>,
    },
}

/// One authored clause-shaped `and`-conjunct — `(or L₁ … Lₙ)` or
/// `(not (and A₁ … Aₙ))`, read as the clause `(¬A₁ … ¬Aₙ)` — with some of
/// its universal literals instantiated. The consequence is the `or` of the
/// rewritten literals. A HINT: `consequence_unit` derives the source from the
/// authored scope, `or`/`not_and` clausify it, and every `qnt_neg_exists`
/// and `forall_inst` step is re-derived by the strict checker.
#[derive(Clone, Debug)]
pub(in crate::executor) struct ClausalInstanceRecord {
    pub source: TermId,
    pub literals: Vec<ClausalLiteral>,
    pub consequence: TermId,
}

/// One authored implication root `(=> A F)` — or its desugared two-literal
/// `or`, or a Boolean equality `(= A F)` / `(= F A)` — whose consequent is a
/// `forall`, together with the antecedent that makes the consequent a
/// top-level consequence.
///
/// The record is only a hint: `consequence_unit` must independently derive a
/// unit clause for BOTH the implication root and the antecedent from the
/// authored scope, and the emitted `implies_pos` (`equiv_pos1`/`equiv_pos2`)
/// step is re-derived by the strict checker from the root's own structure.
#[derive(Clone, Copy)]
pub(in crate::executor) struct ImpliedForall {
    pub implication: TermId,
    pub antecedent: TermId,
    pub forall: TermId,
}

/// One authored `(not (exists ...))` root and its exact De Morgan dual.
/// The record is only a hint; strict replay re-derives the duality.
///
/// `co_units` generalizes the root to the clause shapes
/// `Not(And(E, ψ…))` and its elaborated `(or (not E) …)`: each listed term
/// is a UNIT the stitcher must derive from the authored scope and resolve
/// against the clausified root to leave the `(not E)` unit the bare shape
/// assumes directly. Empty for a bare root.
#[derive(Clone, Debug)]
pub(in crate::executor) struct NegatedExistsDual {
    pub not_exists_root: TermId,
    pub exists: TermId,
    pub forall: TermId,
    pub co_units: Vec<TermId>,
}

/// Ordered members of the authored `and`-conjunct closure.
#[derive(Default)]
pub(super) struct AndConjunctClosure {
    pub(super) members: ay_core::kani_compat::DetHashSet<TermId>,
    pub(super) ordered: Vec<TermId>,
}

impl AndConjunctClosure {
    pub(super) fn contains(&self, term: &TermId) -> bool {
        self.members.contains(term)
    }
}

/// One step of an instantiation / Skolemization CHAIN, in dependency order:
/// each step's source is an authored `and`-conjunct or the output of an
/// earlier step, and only quantifier-free outputs become consequences for the
/// ground probe. The chain is how a refutation of an ALTERNATING authored
/// formula reaches ground: `∀y` instantiated at a term, the resulting `∃x`
/// Skolemized through a registered witness, the next `∀` instantiated over
/// that witness, and so on. Hints only: every step is re-derived by the
/// strict `forall_inst` / `sko_forall` / `qnt_neg_exists` validators.
#[derive(Clone, Debug)]
pub(in crate::executor) enum ExpansionStep {
    Forall(crate::ematching::ForallInstantiationProvenance),
    Skolem(crate::executor::SkolemInstanceRecord),
    Dual(NegatedExistsDual),
    /// A multi-binder quantifier split one binder off (`qnt_join`), so the
    /// next `Skolem` step Skolemizes a single binder.
    Join(QuantifierJoinRecord),
    /// The consequent of a planned implication/equivalence instance
    /// (`ImpliedConsequent` plan), for chains whose consequent is itself
    /// quantified (an exists-bridge) or feeds a later step.
    Implied {
        implication: TermId,
        antecedent: TermId,
        consequent: TermId,
    },
    /// A ground equality derived by congruence (`CongruenceEquality`
    /// plan); transports planned units across equal subterms.
    Congruence {
        equality: TermId,
    },
}

/// One binder split on a multi-binder Skolemization path: from the unit
/// `source` — `joined` itself when `positive`, `(not joined)` otherwise —
/// derive `nested` (resp. `(not nested)`), where `joined = Q x₁…xₙ φ` and
/// `nested = Q x₁ (Q x₂…xₙ φ)`. A HINT: the strict `qnt_join` validator
/// re-derives the equivalence from the two terms alone (same kind, binder
/// list exactly the concatenation, distinct names, the same body), and
/// `equiv_pos1`/`equiv_pos2` plus two resolutions carry the unit across it.
#[derive(Clone, Debug)]
pub(in crate::executor) struct QuantifierJoinRecord {
    pub(in crate::executor) source: TermId,
    pub(in crate::executor) joined: TermId,
    pub(in crate::executor) nested: TermId,
    pub(in crate::executor) positive: bool,
}

impl QuantifierJoinRecord {
    /// The unit this split derives: `nested`, or `(not nested)`.
    pub(in crate::executor) fn derived(&self, terms: &mut ay_core::TermStore) -> TermId {
        if self.positive {
            self.nested
        } else {
            terms.mk_not_raw(self.nested)
        }
    }
}
