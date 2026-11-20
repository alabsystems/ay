// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fail-closed (`InterpolantMode::Explicit`) proof traversal for Craig
//! interpolation over assertion GROUPS.
//!
//! CHC-COMP 2026 Workstream D, Rung 1 (the development design notes
//! DESIGN_lra_interp_tpa.md` at `9598c4206`, §4.1, §6 INV-4/INV-5). Owner: WP-D1-P.
//!
//! One labelled interpolation system (D'Silva et al., VMCAI 2010) per cut,
//! with ONE literal-label function shared by every rule:
//!
//! - an atom (a literal with all negations stripped; composite Boolean terms
//!   included) that occurs as a subterm of the A groups only is `A`, of the B
//!   groups only is `B`, of both is `AB`; an atom that occurs in no assertion
//!   (a solver-built atom) is labelled by its variables: all shared → `AB`,
//!   all in A → `A`, all in B → `B`, otherwise it is UNCLASSIFIED and the
//!   extraction fails;
//! - the system maps `AB` to `b` (McMillan / `Strongest`), `a` (McMillan′ /
//!   `Weakest`) or `ab` (Pudlák / `Default`).
//!
//! Node contract for a clause `C` with partial interpolant `I`:
//! `A ∧ ¬(C|a,ab) ⊨ I` and `B ∧ ¬(C|b,ab) ∧ I ⊨ ⊥`, `vars(I) ⊆ shared`.
//!
//! Leaf rules: an input clause of side A takes `∨ C|b`, of side B `∧ ¬C|a`;
//! a VALID clause (clausification tautology, recognizer-backed theory
//! lemma, the tautology behind a unary Boolean inference) may take either
//! form, whichever is local; a Farkas-certified arithmetic lemma takes the
//! certificate rule of `interpolant_farkas` with the same labeller.
//! Resolution on an `a` pivot is `I1 ∨ I2`, on `b` `I1 ∧ I2`, on `ab`
//! `(p ∨ I1) ∧ (¬p ∨ I2)` with `p` the literal of the first premise.
//!
//! Fail-closed: a Trust/Hole step, a `Generic` (trust) lemma without a
//! certificate, an uncertified arithmetic lemma, an undecodable or rejected
//! certificate, an unclassified literal or pivot, an `Assume` of a term that
//! is neither a group assertion (a top-level conjunct, or a preprocessed
//! assertion the groups imply) nor a propositional tautology, a missing
//! premise, an unsupported rule and a non-local result are all errors —
//! never a degraded `true`/`false`. Only steps reachable from the root (the
//! empty clause) are interpreted.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{
    AletheRule, FarkasAnnotation, Proof, ProofId, ProofStep, TermId, TermStore, TheoryLemmaKind,
};

use super::super::interpolant_farkas::{
    certificate_lemma_interpolant_why, is_equality_restatement, is_linear_arith_valid_clause,
    AtomClass, CertLeafFailure,
};
use super::{literal_atom_polarity, mk_and_simplified, mk_or_simplified, BoolConstants};
use crate::api::types::{InterpolantFailure, InterpolantStrength};

// ---------------------------------------------------------------------------
// Group occurrence (built once per query, shared by every cut)
// ---------------------------------------------------------------------------

/// Occurrence of every subterm of the assertion groups: bit `g` set = the
/// term occurs (as a subterm) in group `g`.
pub(super) struct GroupOccurrence {
    occ: HashMap<TermId, u128>,
    /// Root-level membership (each assertion and its top-level `and`
    /// conjuncts): the only terms an `Assume` leaf may carry.
    roots: HashMap<TermId, u128>,
    /// Root-level disjunctions keyed by their sorted, deduplicated argument
    /// set: the SAT proof manager re-mints an original clause as
    /// `(or l1 .. ln)` in clause order, which need not be the elaborated
    /// assertion's TermId although it is the same clause.
    or_roots: HashMap<Vec<TermId>, u128>,
    /// Every variable term with its group bits.
    vars: Vec<(TermId, u128)>,
    /// Bits of all groups.
    full: u128,
}

impl GroupOccurrence {
    pub(super) fn build(terms: &TermStore, groups: &[Vec<TermId>]) -> Self {
        let mut occ: HashMap<TermId, u128> = HashMap::default();
        let mut roots: HashMap<TermId, u128> = HashMap::default();
        let mut or_roots: HashMap<Vec<TermId>, u128> = HashMap::default();
        let mut stack: Vec<TermId> = Vec::new();
        for (g, group) in groups.iter().enumerate() {
            let bit = 1u128 << g;
            // Root closure under top-level conjunction (A ⊨ each conjunct).
            let mut conj_stack: Vec<TermId> = group.clone();
            while let Some(t) = conj_stack.pop() {
                let entry = roots.entry(t).or_insert(0);
                if *entry & bit != 0 {
                    continue;
                }
                *entry |= bit;
                if let TermData::App(sym, args) = terms.get(t) {
                    if sym.name() == "and" {
                        conj_stack.extend(args.iter().copied());
                    } else if sym.name() == "or" {
                        *or_roots.entry(or_key(args)).or_insert(0) |= bit;
                    }
                }
            }
            // Subterm occurrence (DAG walk, one visit per term and group).
            stack.extend(group.iter().copied());
            while let Some(t) = stack.pop() {
                let entry = occ.entry(t).or_insert(0);
                if *entry & bit != 0 {
                    continue;
                }
                *entry |= bit;
                match terms.get(t) {
                    TermData::Const(_) | TermData::Var(_, _) => {}
                    _ => stack.extend(terms.children(t)),
                }
            }
        }
        let mut vars: Vec<(TermId, u128)> = occ
            .iter()
            .filter(|(t, _)| matches!(terms.get(**t), TermData::Var(_, _)))
            .map(|(t, m)| (*t, *m))
            .collect();
        vars.sort_unstable_by_key(|(t, _)| *t);
        let full = if groups.len() >= 128 {
            u128::MAX
        } else {
            (1u128 << groups.len()) - 1
        };
        Self {
            occ,
            roots,
            or_roots,
            vars,
            full,
        }
    }

    /// Attribute the solver's PREPROCESSED assertions to groups.
    ///
    /// `sources` maps each assertion the solver's core refuted after
    /// preprocessing to the original assertions whose conjunction implies it
    /// (`Executor::interpolation_leaf_sources`). Such a leaf is a root of
    /// group `g` exactly when every one of its sources is a root of `g` — then
    /// `g` alone implies it, which is all the leaf rule needs — and it is closed
    /// under top-level conjunction and disjunction re-minting like any root.
    /// A leaf with no sources, or with sources in no common group, stays
    /// unattributed and fails closed.
    pub(super) fn attribute_preprocessed_leaves(
        &mut self,
        terms: &TermStore,
        sources: &HashMap<TermId, Vec<TermId>>,
    ) {
        let mut derived: Vec<(TermId, u128)> = Vec::new();
        for (&leaf, leaf_sources) in sources {
            if leaf_sources.is_empty() || self.roots.contains_key(&leaf) {
                continue;
            }
            let bits = leaf_sources.iter().fold(self.full, |bits, source| {
                bits & self.roots.get(source).copied().unwrap_or(0)
            });
            if bits != 0 {
                derived.push((leaf, bits));
            }
        }
        derived.sort_unstable_by_key(|(leaf, _)| *leaf);
        for (leaf, bits) in derived {
            let mut conj_stack = vec![leaf];
            while let Some(t) = conj_stack.pop() {
                let entry = self.roots.entry(t).or_insert(0);
                if *entry & bits == bits {
                    continue;
                }
                *entry |= bits;
                if let TermData::App(sym, args) = terms.get(t) {
                    if sym.name() == "and" {
                        conj_stack.extend(args.iter().copied());
                    } else if sym.name() == "or" {
                        *self.or_roots.entry(or_key(args)).or_insert(0) |= bits;
                    }
                }
            }
        }
    }

    /// Group bits of the assertion an `Assume(t)` leaf restates: `t` itself
    /// (or a top-level conjunct), or a disjunction with the same argument set
    /// as an asserted one. `0` when `t` is not a group assertion.
    fn root_bits(&self, terms: &TermStore, t: TermId) -> u128 {
        if let Some(&m) = self.roots.get(&t) {
            return m;
        }
        match terms.get(t) {
            TermData::App(sym, args) if sym.name() == "or" => {
                self.or_roots.get(&or_key(args)).copied().unwrap_or(0)
            }
            _ => 0,
        }
    }
}

/// The disjuncts of an `or` term, or the term itself.
fn disjuncts_of(terms: &TermStore, t: TermId) -> Vec<TermId> {
    match terms.get(t) {
        TermData::App(sym, args) if sym.name() == "or" => args.clone(),
        _ => vec![t],
    }
}

fn or_key(args: &[TermId]) -> Vec<TermId> {
    let mut key = args.to_vec();
    key.sort_unstable();
    key.dedup();
    key
}

// ---------------------------------------------------------------------------
// Proof view (reachability from the root; built once per proof)
// ---------------------------------------------------------------------------

/// The reachable part of a refutation, in topological (index) order.
pub(super) struct ProofView {
    order: Vec<usize>,
    /// Reachable `Trust`/`Hole` steps.
    pub(super) trust_steps: usize,
}

fn step_premises(step: &ProofStep) -> Vec<ProofId> {
    match step {
        ProofStep::Resolution {
            clause1, clause2, ..
        } => vec![*clause1, *clause2],
        ProofStep::Step { premises, .. } => premises.clone(),
        ProofStep::Anchor { end_step, .. } => vec![*end_step],
        _ => Vec::new(),
    }
}

/// Clause literals of a step (`Assume(t)` is the unit clause `[t]`).
fn step_clause(step: &ProofStep) -> Option<&[TermId]> {
    match step {
        ProofStep::Assume(t) => Some(std::slice::from_ref(t)),
        ProofStep::Resolution { clause, .. }
        | ProofStep::TheoryLemma { clause, .. }
        | ProofStep::Step { clause, .. }
        | ProofStep::FiniteFieldLinear { clause, .. }
        | ProofStep::NraSos { clause, .. } => Some(clause),
        _ => None,
    }
}

impl ProofView {
    /// Reachable steps from the last step, which must derive the empty
    /// clause; every premise must precede its step.
    pub(super) fn build(proof: &Proof) -> Result<Self, InterpolantFailure> {
        let n = proof.steps.len();
        let Some(root) = n.checked_sub(1) else {
            return Err(InterpolantFailure::NoProof);
        };
        match step_clause(&proof.steps[root]) {
            Some([]) => {}
            _ => return Err(InterpolantFailure::NoProof),
        }
        let mut seen = vec![false; n];
        let mut stack = vec![root];
        seen[root] = true;
        while let Some(idx) = stack.pop() {
            for pid in step_premises(&proof.steps[idx]) {
                let p = pid.0 as usize;
                if p >= idx {
                    return Err(InterpolantFailure::MissingPremise { step: idx });
                }
                if !seen[p] {
                    seen[p] = true;
                    stack.push(p);
                }
            }
        }
        let order: Vec<usize> = (0..n).filter(|&i| seen[i]).collect();
        let trust_steps = order
            .iter()
            .filter(|&&i| {
                matches!(
                    proof.steps[i],
                    ProofStep::Step {
                        rule: AletheRule::Trust | AletheRule::Hole,
                        ..
                    }
                )
            })
            .count();
        Ok(Self { order, trust_steps })
    }
}

// ---------------------------------------------------------------------------
// One cut
// ---------------------------------------------------------------------------

/// Label of an atom class under the system in use.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Label {
    A,
    B,
    Ab,
}

fn label_of(class: AtomClass, strength: InterpolantStrength) -> Label {
    match (class, strength) {
        (AtomClass::A, _) | (AtomClass::Ab, InterpolantStrength::Weakest) => Label::A,
        (AtomClass::B, _) | (AtomClass::Ab, InterpolantStrength::Strongest) => Label::B,
        (AtomClass::Ab, _) => Label::Ab,
    }
}

struct Cut<'o> {
    occ: &'o GroupOccurrence,
    a: u128,
    b: u128,
    shared_vars: HashSet<TermId>,
    strength: InterpolantStrength,
    bc: BoolConstants,
}

/// Distinct variables of a term (DAG walk).
fn vars_of(terms: &TermStore, root: TermId) -> Vec<TermId> {
    let mut out = Vec::new();
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut stack = vec![root];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::Var(_, _) => out.push(t),
            TermData::Const(_) => {}
            _ => stack.extend(terms.children(t)),
        }
    }
    out
}

fn var_name(terms: &TermStore, v: TermId) -> String {
    match terms.get(v) {
        TermData::Var(name, _) => name.clone(),
        _ => format!("<term {v}>"),
    }
}

impl<'o> Cut<'o> {
    fn new(
        terms: &TermStore,
        occ: &'o GroupOccurrence,
        a: u128,
        strength: InterpolantStrength,
    ) -> Self {
        let b = occ.full & !a;
        let shared_vars = occ
            .vars
            .iter()
            .filter(|(_, m)| m & a != 0 && m & b != 0)
            .map(|(v, _)| *v)
            .collect();
        Self {
            occ,
            a,
            b,
            shared_vars,
            strength,
            bc: BoolConstants {
                true_tid: terms.true_term(),
                false_tid: terms.false_term(),
            },
        }
    }

    /// THE literal-label function of this cut (see the module docs).
    fn class_of(&self, terms: &TermStore, atom: TermId) -> Option<AtomClass> {
        if let Some(&m) = self.occ.occ.get(&atom) {
            return match (m & self.a != 0, m & self.b != 0) {
                (true, true) => Some(AtomClass::Ab),
                (true, false) => Some(AtomClass::A),
                (false, true) => Some(AtomClass::B),
                (false, false) => None,
            };
        }
        let vars = vars_of(terms, atom);
        let (mut all_shared, mut all_a, mut all_b) = (true, true, true);
        for v in vars {
            let m = self.occ.occ.get(&v).copied().unwrap_or(0);
            let (in_a, in_b) = (m & self.a != 0, m & self.b != 0);
            all_shared &= in_a && in_b;
            all_a &= in_a;
            all_b &= in_b;
        }
        if all_shared {
            Some(AtomClass::Ab)
        } else if all_a {
            Some(AtomClass::A)
        } else if all_b {
            Some(AtomClass::B)
        } else {
            None
        }
    }

    fn label(
        &self,
        terms: &TermStore,
        lit: TermId,
        step: usize,
    ) -> Result<Label, InterpolantFailure> {
        let (atom, _) = literal_atom_polarity(terms, lit);
        self.class_of(terms, atom)
            .map(|c| label_of(c, self.strength))
            .ok_or(InterpolantFailure::UnclassifiedLiteral { step })
    }

    /// First non-shared variable of `t`, if any.
    fn non_local_var(&self, terms: &TermStore, t: TermId) -> Option<TermId> {
        vars_of(terms, t)
            .into_iter()
            .find(|v| !self.shared_vars.contains(v))
    }

    fn require_local(&self, terms: &TermStore, t: TermId) -> Result<(), InterpolantFailure> {
        match self.non_local_var(terms, t) {
            None => Ok(()),
            Some(v) => Err(InterpolantFailure::NonLocal {
                var: var_name(terms, v),
            }),
        }
    }

    /// Input clause of side A: `I = ∨ { l : label(l) = b }`.
    fn a_clause(
        &self,
        terms: &mut TermStore,
        clause: &[TermId],
        step: usize,
    ) -> Result<TermId, InterpolantFailure> {
        let mut result = self.bc.false_tid;
        for &lit in clause {
            if self.label(terms, lit, step)? == Label::B {
                self.require_local(terms, lit)?;
                result = mk_or_simplified(terms, result, lit, self.bc.true_tid, self.bc.false_tid);
            }
        }
        Ok(result)
    }

    /// Input clause of side B: `I = ∧ { ¬l : label(l) = a }`.
    fn b_clause(
        &self,
        terms: &mut TermStore,
        clause: &[TermId],
        step: usize,
    ) -> Result<TermId, InterpolantFailure> {
        let mut result = self.bc.true_tid;
        for &lit in clause {
            if self.label(terms, lit, step)? == Label::A {
                self.require_local(terms, lit)?;
                let neg = terms.mk_not(lit);
                result = mk_and_simplified(terms, result, neg, self.bc.true_tid, self.bc.false_tid);
            }
        }
        Ok(result)
    }

    /// A VALID clause (⊨ C): either leaf form satisfies the node contract
    /// (`¬(C|a,ab) ⊨ C|b` and `¬(C|b,ab) ∧ ¬(C|a) = ¬C ⊨ ⊥`), so take the
    /// one that is local; fail if neither is.
    fn valid_clause(
        &self,
        terms: &mut TermStore,
        clause: &[TermId],
        step: usize,
    ) -> Result<TermId, InterpolantFailure> {
        let mut a_lits = Vec::new();
        let mut b_lits = Vec::new();
        for &lit in clause {
            match self.label(terms, lit, step)? {
                Label::A => a_lits.push(lit),
                Label::B => b_lits.push(lit),
                Label::Ab => {}
            }
        }
        if b_lits.is_empty() {
            return Ok(self.bc.false_tid);
        }
        if a_lits.is_empty() {
            return Ok(self.bc.true_tid);
        }
        let a_side_local = b_lits
            .iter()
            .all(|&l| self.non_local_var(terms, l).is_none());
        let b_side_local = a_lits
            .iter()
            .all(|&l| self.non_local_var(terms, l).is_none());
        let prefer_b = matches!(self.strength, InterpolantStrength::Strongest);
        let use_a = match (a_side_local, b_side_local) {
            (true, true) => !prefer_b,
            (true, false) => true,
            (false, true) => false,
            (false, false) => {
                let v = b_lits
                    .iter()
                    .find_map(|&l| self.non_local_var(terms, l))
                    .unwrap_or(b_lits[0]);
                return Err(InterpolantFailure::NonLocal {
                    var: var_name(terms, v),
                });
            }
        };
        if use_a {
            let mut result = self.bc.false_tid;
            for lit in b_lits {
                result = mk_or_simplified(terms, result, lit, self.bc.true_tid, self.bc.false_tid);
            }
            Ok(result)
        } else {
            let mut result = self.bc.true_tid;
            for lit in a_lits {
                let neg = terms.mk_not(lit);
                result = mk_and_simplified(terms, result, neg, self.bc.true_tid, self.bc.false_tid);
            }
            Ok(result)
        }
    }

    /// Resolution of `C1 ∋ p` (partial `i1`) with `C2 ∋ ¬p` (partial `i2`).
    fn resolve(
        &self,
        terms: &mut TermStore,
        p: TermId,
        i1: TermId,
        i2: TermId,
        step: usize,
    ) -> Result<TermId, InterpolantFailure> {
        let (t, f) = (self.bc.true_tid, self.bc.false_tid);
        Ok(match self.label(terms, p, step)? {
            Label::A => mk_or_simplified(terms, i1, i2, t, f),
            Label::B => mk_and_simplified(terms, i1, i2, t, f),
            Label::Ab => {
                let not_p = terms.mk_not(p);
                let left = mk_or_simplified(terms, i1, p, t, f);
                let right = mk_or_simplified(terms, i2, not_p, t, f);
                mk_and_simplified(terms, left, right, t, f)
            }
        })
    }

    /// Theory lemma leaf.
    #[allow(clippy::too_many_arguments)]
    fn theory_leaf(
        &self,
        terms: &mut TermStore,
        clause: &[TermId],
        farkas: Option<&FarkasAnnotation>,
        kind: &TheoryLemmaKind,
        step: usize,
    ) -> Result<TermId, InterpolantFailure> {
        if let Some(farkas) = farkas {
            let classify = |t: &TermStore, atom: TermId| self.class_of(t, atom);
            return certificate_lemma_interpolant_why(
                terms,
                clause,
                farkas,
                &classify,
                &self.shared_vars,
                self.strength,
                self.bc.true_tid,
                self.bc.false_tid,
            )
            .map_err(|why| match why {
                CertLeafFailure::Unclassified => InterpolantFailure::UnclassifiedLiteral { step },
                CertLeafFailure::Undecodable => InterpolantFailure::UndecodableLeaf { step },
                CertLeafFailure::Rejected => InterpolantFailure::UncertifiedLeaf { step },
                CertLeafFailure::UnsupportedShape => InterpolantFailure::UnsupportedStep { step },
                CertLeafFailure::NonLocal(v) => InterpolantFailure::NonLocal {
                    var: var_name(terms, v),
                },
            });
        }
        if kind.is_trust() {
            // A trust-kind equality restatement is valid on its own
            // (`is_equality_restatement` checks the two linear forms).
            if is_equality_restatement(terms, clause) {
                return self.valid_clause(terms, clause, step);
            }
            return Err(InterpolantFailure::TrustStep { step });
        }
        if matches!(
            kind,
            TheoryLemmaKind::LraFarkas | TheoryLemmaKind::LiaGeneric
        ) {
            return Err(InterpolantFailure::UncertifiedLeaf { step });
        }
        // Kinds that hold only by virtue of a problem assertion (the clause
        // is NOT valid on its own): a valid-clause leaf would silently use a
        // premise that may sit on the other side of the partition. No leaf
        // form is known to be sound without the supporting assertion's
        // label, so they fail closed. A new assertion-dependent kind MUST be
        // added here (`TheoryLemmaKind` is `#[non_exhaustive]`, so the
        // compiler cannot force it).
        if matches!(kind, TheoryLemmaKind::SetCardEmptyByAssertion) {
            return Err(InterpolantFailure::UncertifiedLeaf { step });
        }
        // Recognizer-backed tautology kinds (Bool/ITE/arithmetic-clause
        // tautologies, disequality splits, ...): a valid clause.
        self.valid_clause(terms, clause, step)
    }
}

// ---------------------------------------------------------------------------
// Rule tables
// ---------------------------------------------------------------------------

/// Premiseless rules whose conclusion is a valid clause.
fn is_tautology_rule(rule: &AletheRule) -> bool {
    matches!(
        rule,
        AletheRule::True
            | AletheRule::NotFalse
            | AletheRule::False
            | AletheRule::AndPos(_)
            | AletheRule::AndNeg
            | AletheRule::OrPos(_)
            | AletheRule::OrNeg
            | AletheRule::ImpliesPos
            | AletheRule::ImpliesNeg1
            | AletheRule::ImpliesNeg2
            | AletheRule::EquivPos1
            | AletheRule::EquivPos2
            | AletheRule::EquivNeg1
            | AletheRule::EquivNeg2
            | AletheRule::ItePos1
            | AletheRule::ItePos2
            | AletheRule::IteNeg1
            | AletheRule::IteNeg2
            | AletheRule::XorPos1
            | AletheRule::XorPos2
            | AletheRule::XorNeg1
            | AletheRule::XorNeg2
            | AletheRule::EqReflexive
            | AletheRule::Refl
            | AletheRule::LaTautology
            | AletheRule::LaDisequality
            | AletheRule::LaTotality
    )
}

/// Premiseless arithmetic lemmas that need a Farkas certificate (a `Step`
/// carries none the extractor can decode).
fn is_certified_arith_rule(rule: &AletheRule) -> bool {
    matches!(rule, AletheRule::LaGeneric | AletheRule::LiaGeneric)
}

/// One-premise Boolean inferences `p ⊢ C` whose soundness makes `¬p ∨ C` a
/// valid clause (Alethe "unary" connective rules).
fn is_unary_boolean_rule(rule: &AletheRule) -> bool {
    matches!(
        rule,
        AletheRule::And
            | AletheRule::NotAnd
            | AletheRule::Or
            | AletheRule::NotOr
            | AletheRule::Implies
            | AletheRule::NotImplies1
            | AletheRule::NotImplies2
            | AletheRule::Equiv
            | AletheRule::NotEquiv1
            | AletheRule::NotEquiv2
            | AletheRule::Ite
            | AletheRule::Ite1
            | AletheRule::Ite2
            | AletheRule::NotIte1
            | AletheRule::NotIte2
    )
}

// ---------------------------------------------------------------------------
// Clause-set helpers
// ---------------------------------------------------------------------------

fn lit_key(terms: &TermStore, lit: TermId) -> (TermId, bool) {
    literal_atom_polarity(terms, lit)
}

/// `sub ⊆ sup` as literal sets (atom + polarity).
fn clause_subset(terms: &TermStore, sub: &[TermId], sup: &[TermId]) -> bool {
    let sup_keys: HashSet<(TermId, bool)> = sup.iter().map(|&l| lit_key(terms, l)).collect();
    sub.iter().all(|&l| sup_keys.contains(&lit_key(terms, l)))
}

/// A literal of `c1` whose complement occurs in `c2` (the `c1` occurrence).
fn find_pivot(terms: &TermStore, c1: &[TermId], c2: &[TermId]) -> Option<TermId> {
    let c2_keys: HashSet<(TermId, bool)> = c2.iter().map(|&l| lit_key(terms, l)).collect();
    c1.iter().copied().find(|&l| {
        let (atom, neg) = lit_key(terms, l);
        c2_keys.contains(&(atom, !neg))
    })
}

/// Exact resolvent of `c1 ∋ p` and `c2 ∋ ¬p` (deduplicated): only `p` is
/// removed from `c1` and only `¬p` from `c2`. A literal of the pivot atom
/// with the other polarity (a tautological premise, or a second clash that
/// made an intermediate clause tautological) stays, so the tracked clause is
/// exactly the one the partial interpolant is for; dropping it would let a
/// later subset check accept a conclusion the interpolant does not cover.
fn resolvent(terms: &TermStore, c1: &[TermId], c2: &[TermId], p: TermId) -> Vec<TermId> {
    let (pivot_atom, pivot_neg) = lit_key(terms, p);
    let mut seen: HashSet<(TermId, bool)> = HashSet::default();
    let mut out = Vec::with_capacity(c1.len() + c2.len());
    let from_c1 = c1.iter().map(|&l| (l, (pivot_atom, pivot_neg)));
    let from_c2 = c2.iter().map(|&l| (l, (pivot_atom, !pivot_neg)));
    for (l, removed) in from_c1.chain(from_c2) {
        let key = lit_key(terms, l);
        if key == removed {
            continue;
        }
        if seen.insert(key) {
            out.push(l);
        }
    }
    out
}

// ---------------------------------------------------------------------------
// The traversal
// ---------------------------------------------------------------------------

/// Fail-closed interpolant for the cut whose A side is `a_mask`.
///
/// `groups` are the resolved assertion groups the occurrence map was built
/// from; the caller has validated `a_mask` (non-empty, a strict subset).
pub(super) fn explicit_interpolant(
    terms: &mut TermStore,
    proof: &Proof,
    view: &ProofView,
    occ: &GroupOccurrence,
    a_mask: u128,
    strength: InterpolantStrength,
) -> Result<TermId, InterpolantFailure> {
    let cut = Cut::new(terms, occ, a_mask, strength);
    let n = proof.steps.len();
    let mut partial: Vec<Option<TermId>> = vec![None; n];

    let get = |partial: &[Option<TermId>], pid: ProofId, step: usize| {
        partial
            .get(pid.0 as usize)
            .copied()
            .flatten()
            .ok_or(InterpolantFailure::MissingPremise { step })
    };
    let clause_at = |pid: ProofId, step: usize| {
        proof
            .steps
            .get(pid.0 as usize)
            .and_then(step_clause)
            .ok_or(InterpolantFailure::MissingPremise { step })
    };

    for &idx in &view.order {
        let itp = match &proof.steps[idx] {
            ProofStep::Assume(t) => {
                let m = occ.root_bits(terms, *t);
                if m & cut.a != 0 {
                    cut.a_clause(terms, std::slice::from_ref(t), idx)?
                } else if m & cut.b != 0 {
                    cut.b_clause(terms, std::slice::from_ref(t), idx)?
                } else if tautology::is_propositional_tautology(terms, *t)
                    || is_linear_arith_valid_clause(terms, &disjuncts_of(terms, *t))
                {
                    // Valid on its own: a propositional tautology, or an LRA
                    // theory lemma recorded as an unannotated `assume` of its
                    // disjunction (Fourier–Motzkin-checked).
                    cut.valid_clause(terms, std::slice::from_ref(t), idx)?
                } else {
                    return Err(InterpolantFailure::UnclassifiedLiteral { step: idx });
                }
            }
            ProofStep::Resolution {
                clause: stated,
                pivot,
                clause1,
                clause2,
                ..
            } => {
                let i1 = get(&partial, *clause1, idx)?;
                let i2 = get(&partial, *clause2, idx)?;
                let c1 = clause_at(*clause1, idx)?;
                let c2 = clause_at(*clause2, idx)?;
                // Orient: the resolved literal must occur with opposite
                // polarities in the two premises.
                let (pivot_atom, _) = lit_key(terms, *pivot);
                let in1: Vec<TermId> = c1
                    .iter()
                    .copied()
                    .filter(|&l| lit_key(terms, l).0 == pivot_atom)
                    .collect();
                let in2: Vec<TermId> = c2
                    .iter()
                    .copied()
                    .filter(|&l| lit_key(terms, l).0 == pivot_atom)
                    .collect();
                let (Some(&l1), Some(&l2)) = (in1.first(), in2.first()) else {
                    return Err(InterpolantFailure::UnsupportedStep { step: idx });
                };
                let pol1 = lit_key(terms, l1).1;
                let pol2 = lit_key(terms, l2).1;
                if pol1 == pol2
                    || in1.iter().any(|&l| lit_key(terms, l).1 != pol1)
                    || in2.iter().any(|&l| lit_key(terms, l).1 != pol2)
                {
                    return Err(InterpolantFailure::UnsupportedStep { step: idx });
                }
                // The partial interpolant is for the ACTUAL resolvent; later
                // steps read this node's stated clause, so it must cover the
                // resolvent (weakening is fine, dropped literals are not).
                if !clause_subset(terms, &resolvent(terms, c1, c2, l1), stated) {
                    return Err(InterpolantFailure::UnsupportedStep { step: idx });
                }
                cut.resolve(terms, l1, i1, i2, idx)?
            }
            ProofStep::TheoryLemma {
                clause,
                farkas,
                kind,
                ..
            } => cut.theory_leaf(terms, clause, farkas.as_ref(), kind, idx)?,
            ProofStep::Step {
                rule,
                clause,
                premises,
                ..
            } => match rule {
                AletheRule::Trust | AletheRule::Hole => {
                    return Err(InterpolantFailure::TrustStep { step: idx });
                }
                _ if premises.is_empty() => {
                    if is_tautology_rule(rule) {
                        cut.valid_clause(terms, clause, idx)?
                    } else if is_certified_arith_rule(rule) {
                        return Err(InterpolantFailure::UncertifiedLeaf { step: idx });
                    } else {
                        return Err(InterpolantFailure::UnsupportedStep { step: idx });
                    }
                }
                AletheRule::Resolution | AletheRule::ThResolution if premises.len() >= 2 => {
                    // Pivot-free resolution chain: fold the premises, each
                    // time taking the first remaining premise that clashes
                    // with the running clause, then check the conclusion.
                    let mut cur_lits: Vec<TermId> = clause_at(premises[0], idx)?.to_vec();
                    let mut cur_itp = get(&partial, premises[0], idx)?;
                    let mut rest: Vec<(Vec<TermId>, TermId)> = Vec::with_capacity(premises.len());
                    for pid in &premises[1..] {
                        rest.push((clause_at(*pid, idx)?.to_vec(), get(&partial, *pid, idx)?));
                    }
                    while !rest.is_empty() {
                        let Some((j, p)) = rest.iter().enumerate().find_map(|(j, (lits, _))| {
                            find_pivot(terms, &cur_lits, lits).map(|p| (j, p))
                        }) else {
                            return Err(InterpolantFailure::UnsupportedStep { step: idx });
                        };
                        let (lits, itp) = rest.remove(j);
                        cur_itp = cut.resolve(terms, p, cur_itp, itp, idx)?;
                        cur_lits = resolvent(terms, &cur_lits, &lits, p);
                    }
                    if !clause_subset(terms, &cur_lits, clause) {
                        return Err(InterpolantFailure::UnsupportedStep { step: idx });
                    }
                    cur_itp
                }
                _ if premises.len() == 1 => {
                    let premise_clause = clause_at(premises[0], idx)?;
                    let i_p = get(&partial, premises[0], idx)?;
                    if clause_subset(terms, premise_clause, clause) {
                        // Weakening / contraction / reordering: the node
                        // contract of the premise implies the conclusion's.
                        i_p
                    } else if premise_clause.len() == 1 && is_unary_boolean_rule(rule) {
                        // `p ⊢ C` is resolution of `[p]` with the valid
                        // clause `¬p ∨ C` on `p`.
                        let p = premise_clause[0];
                        // Raw negation: `mk_not` pushes De Morgan / ITE
                        // negation inward, which would give the tautology's
                        // pivot literal a DIFFERENT atom (and label) than `p`.
                        let not_p = terms.mk_not_raw(p);
                        let mut taut = Vec::with_capacity(clause.len() + 1);
                        taut.push(not_p);
                        taut.extend_from_slice(clause);
                        let i_t = cut.valid_clause(terms, &taut, idx)?;
                        cut.resolve(terms, p, i_p, i_t, idx)?
                    } else {
                        return Err(InterpolantFailure::UnsupportedStep { step: idx });
                    }
                }
                _ => return Err(InterpolantFailure::UnsupportedStep { step: idx }),
            },
            _ => return Err(InterpolantFailure::UnsupportedStep { step: idx }),
        };
        partial[idx] = Some(itp);
    }

    let root = partial
        .last()
        .copied()
        .flatten()
        .ok_or(InterpolantFailure::MissingPremise {
            step: n.saturating_sub(1),
        })?;
    // INV-5: locality is a RELEASE check.
    cut.require_local(terms, root)?;
    Ok(root)
}

#[path = "interpolant_explicit_tautology.rs"]
mod tautology;

#[cfg(test)]
#[path = "interpolant_explicit_tests.rs"]
mod tests;
