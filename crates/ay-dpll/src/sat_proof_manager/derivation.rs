// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof derivation methods for [`SatProofManager`].
//!
//! Extracted from `mod.rs` — contains `add_original_clause_step`,
//! `derive_clause_from_hints`, `close_clause_via_originals`,
//! `derive_empty_from_units`, and `derive_empty_from_assumptions`.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{
    AletheRule, ClausificationProof, Proof, ProofId, ProofStep, TermId, TermStore, TheoryLemmaKind,
    TheoryLemmaProof,
};
use ay_sat::{Literal, Variable};

use super::{HintDerivationError, SatProofManager};

/// One processed clause-trace entry: its raw SAT literals and the proof node
/// that proves it. Trace clause ids can be reused across entries (proof-writer
/// ids vs arena-index fallback share one id space), so replay tracks every
/// version rather than a latest-wins map (#rank-4 increment 1).
pub(super) type SatClauseVersion = (Vec<Literal>, ProofId);

/// Cap on the DRUP-widening phase: beyond this many trace entries the widened
/// scan is skipped (the per-derivation cost is O(entries x propagations)) and
/// failed replays fall back to pairwise resolution / Trust as before.
const MAX_RUP_WIDENING_VERSIONS: usize = 100_000;

/// Cap on how many literals a recorded theory lemma may have beyond the
/// traced (level-0-minimized) clause for the superset bridge (#rank-4
/// increment 2) to consider it.
const MAX_BRIDGE_EXTRA_LITERALS: usize = 64;

/// Cap on superset candidates tried per traced clause by the bridge.
const MAX_BRIDGE_CANDIDATES: usize = 4;

/// Node cap for the bounded-DPLL unit-fact re-derivation (#seq-unit-fact).
/// Each node is one propagation-to-fixpoint over the processed clause
/// database; the SEQ finite-model unit facts refute in a few dozen nodes.
const DPLL_MAX_NODES: usize = 4096;

/// Cap on fresh-`LraSolver` theory-oracle calls per bounded-DPLL(T) search
/// (#relu-trust-glue). Each call re-checks the stalled assignment's
/// arithmetic literals; the ReLU case-split family needs one per infeasible
/// branch pattern. Fail-closed on exhaustion (the search falls back to
/// propositional decisions and, ultimately, the honest trust closer).
const DPLL_MAX_THEORY_CHECKS: usize = 128;

/// Variable truth values for the RUP replay assignment vector.
const RUP_UNASSIGNED: u8 = 0;
const RUP_TRUE: u8 = 1;
const RUP_FALSE: u8 = 2;

/// Persistent two-watched-literal unit-propagation engine for RUP replay.
///
/// The legacy `rup_propagate` re-scanned the candidate list to fixpoint with
/// linear passes and a `HashMap<usize, bool>` assignment — superquadratic
/// over a `process_trace` run (~40k trace entries on QF_UF PEQ012, >95% of
/// on-CPU proof-reconstruction time). This engine amortizes the DRUP-widening
/// phase across all replays in one `process_trace` run:
///
/// * clause versions are indexed **incrementally and append-only** (the
///   `clause_versions` vec only grows, so watch indices stay valid);
/// * the assignment is a `Vec<u8>` keyed by variable index, reset via an
///   undo trail between replays (watched pairs need no reset: with an empty
///   assignment any two distinct watched literals satisfy the invariant);
/// * per replay, propagation starts from the trail (assumptions + hint-phase
///   implications) and only traverses watch lists of falsified literals,
///   instead of rescanning every clause version to fixpoint.
///
/// Propagation-to-fixpoint is confluent (the implied-literal set and
/// conflict-existence are order-independent), so this finds a conflict
/// exactly when the legacy widened scan did; only the recorded implication
/// order (and hence the shape of the emitted — still valid — resolution
/// chain) can differ.
#[derive(Default)]
pub(super) struct RupEngine {
    /// Literal code (`2*var + positive`) -> clause versions watching it.
    watches: Vec<Vec<usize>>,
    /// Per indexed version: its two watched literals (multi-literal clauses
    /// only; entries for unit/empty clauses are unused placeholders).
    watched: Vec<[Literal; 2]>,
    /// Versions with exactly one distinct literal, with that literal.
    units: Vec<(usize, Literal)>,
    /// First indexed version with an empty clause, if any (always conflicting).
    empty_version: Option<usize>,
    /// Number of clause versions indexed so far.
    indexed: usize,
    /// Variable index -> RUP_{UNASSIGNED,TRUE,FALSE}.
    assigns: Vec<u8>,
    /// Assigned literals of the current replay, for cheap reset.
    trail: Vec<Literal>,
    /// Literal-code generation marks for the resolution-fold resolvent dedup
    /// (#proof-tax): `mark[code] == mark_gen` means the literal is already in
    /// the resolvent being built. Replaces the `Vec::contains` scan that made
    /// each fold step quadratic in the resolvent length.
    mark: Vec<u32>,
    /// Current generation for `mark`; bumped per resolvent.
    mark_gen: u32,
}

impl RupEngine {
    #[inline]
    fn code(lit: Literal) -> usize {
        lit.variable().index() * 2 + usize::from(lit.is_positive())
    }

    /// Truth value of `lit` under the current assignment.
    #[inline]
    fn value(&self, lit: Literal) -> Option<bool> {
        match self
            .assigns
            .get(lit.variable().index())
            .copied()
            .unwrap_or(RUP_UNASSIGNED)
        {
            RUP_UNASSIGNED => None,
            v => Some((v == RUP_TRUE) == lit.is_positive()),
        }
    }

    /// Assign `lit` true and record it on the trail. Caller must have checked
    /// the variable is unassigned.
    #[inline]
    fn assign(&mut self, lit: Literal) {
        let var = lit.variable().index();
        if self.assigns.len() <= var {
            self.assigns.resize(var + 1, RUP_UNASSIGNED);
        }
        self.assigns[var] = if lit.is_positive() {
            RUP_TRUE
        } else {
            RUP_FALSE
        };
        self.trail.push(lit);
    }

    /// Clear the current replay's assignment (trail-driven, O(|trail|)).
    fn reset(&mut self) {
        for lit in self.trail.drain(..) {
            self.assigns[lit.variable().index()] = RUP_UNASSIGNED;
        }
    }

    /// Start a fresh resolvent-dedup generation and return it. On `mark_gen`
    /// wrap-around the mark array is zeroed so stale generations can never
    /// alias (u32 wrap needs 4B resolvents; belt and suspenders).
    fn next_mark_gen(&mut self) -> u32 {
        self.mark_gen = match self.mark_gen.checked_add(1) {
            Some(generation) => generation,
            None => {
                self.mark.iter_mut().for_each(|m| *m = 0);
                1
            }
        };
        self.mark_gen
    }

    /// Mark `lit`'s code for the current generation; returns `true` iff the
    /// literal was NOT yet marked (i.e. first occurrence).
    #[inline]
    fn mark_first(&mut self, lit: Literal, generation: u32) -> bool {
        let code = Self::code(lit);
        if self.mark.len() <= code {
            self.mark.resize(code + 1, 0);
        }
        if self.mark[code] == generation {
            return false;
        }
        self.mark[code] = generation;
        true
    }

    /// Index any clause versions appended since the last call.
    fn ensure_indexed(&mut self, clause_versions: &[SatClauseVersion]) {
        while self.indexed < clause_versions.len() {
            let version = self.indexed;
            let clause = &clause_versions[version].0;
            self.watched.push([Literal::positive(Variable::new(0)); 2]);
            match clause.split_first() {
                None => {
                    if self.empty_version.is_none() {
                        self.empty_version = Some(version);
                    }
                }
                Some((&first, rest)) => {
                    // Watch the first two DISTINCT literals; a clause whose
                    // literals are all identical is a unit on that literal.
                    match rest.iter().copied().find(|&l| l != first) {
                        None => self.units.push((version, first)),
                        Some(second) => {
                            self.watched[version] = [first, second];
                            for lit in [first, second] {
                                let code = Self::code(lit);
                                if self.watches.len() <= code {
                                    self.watches.resize_with(code + 1, Vec::new);
                                }
                                self.watches[code].push(version);
                            }
                        }
                    }
                }
            }
            self.indexed += 1;
        }
    }

    /// Watched-literal unit propagation over ALL indexed clause versions,
    /// continuing from the current trail (assumptions + any hint-phase
    /// implications). Returns the conflicting version on conflict; records
    /// propagations in `implications`/`used` exactly like the legacy scan.
    ///
    /// Budget semantics match #A2b: one step per clause inspection; on
    /// exhaustion, stall (return no conflict) so `process_trace` abandons
    /// reconstruction.
    fn propagate(
        &mut self,
        clause_versions: &[SatClauseVersion],
        implications: &mut Vec<(usize, Literal)>,
        used: &mut HashSet<usize>,
        step_budget: &mut Option<u64>,
    ) -> Option<usize> {
        self.ensure_indexed(clause_versions);
        if let Some(empty) = self.empty_version {
            return Some(empty);
        }

        // Assert every unit clause (they cannot be watched by two literals).
        // A false unit is an all-falsified clause: the conflict.
        for i in 0..self.units.len() {
            let (version, lit) = self.units[i];
            if let Some(remaining) = step_budget {
                if *remaining == 0 {
                    return None;
                }
                *remaining -= 1;
            }
            match self.value(lit) {
                Some(true) => {}
                Some(false) => return Some(version),
                None => {
                    self.assign(lit);
                    implications.push((version, lit));
                    used.insert(version);
                }
            }
        }

        // Process the whole trail (qhead 0): newly indexed clauses may watch
        // literals falsified earlier in this replay.
        let mut qhead = 0;
        while qhead < self.trail.len() {
            let assigned = self.trail[qhead];
            qhead += 1;
            let false_code = Self::code(assigned.negated());
            if self.watches.len() <= false_code {
                continue;
            }
            let mut ws = std::mem::take(&mut self.watches[false_code]);
            let falsified = assigned.negated();
            let mut keep = 0usize;
            let mut conflict = None;
            let mut i = 0usize;
            while i < ws.len() {
                let version = ws[i];
                i += 1;
                if let Some(remaining) = step_budget {
                    if *remaining == 0 {
                        // Stall: keep the remaining watchers in place.
                        ws.copy_within(i - 1.., keep);
                        ws.truncate(keep + (ws.len() - (i - 1)));
                        self.watches[false_code] = ws;
                        return None;
                    }
                    *remaining -= 1;
                }
                let [w0, w1] = self.watched[version];
                let other = if w0 == falsified { w1 } else { w0 };
                if self.value(other) == Some(true) {
                    ws[keep] = version;
                    keep += 1;
                    continue;
                }
                // Look for a replacement (non-falsified, not the other watch).
                let clause = &clause_versions[version].0;
                let replacement = clause
                    .iter()
                    .copied()
                    .find(|&l| l != falsified && l != other && self.value(l) != Some(false));
                if let Some(new_watch) = replacement {
                    self.watched[version] = [other, new_watch];
                    let code = Self::code(new_watch);
                    if self.watches.len() <= code {
                        self.watches.resize_with(code + 1, Vec::new);
                    }
                    self.watches[code].push(version);
                    continue; // moved out of this list
                }
                // No replacement: clause is unit on `other` or conflicting.
                ws[keep] = version;
                keep += 1;
                match self.value(other) {
                    Some(false) => {
                        conflict = Some(version);
                        break;
                    }
                    _ => {
                        self.assign(other);
                        implications.push((version, other));
                        used.insert(version);
                    }
                }
            }
            // Retain unprocessed watchers (on conflict/early break) plus kept.
            ws.copy_within(i.., keep);
            ws.truncate(keep + (ws.len() - i));
            self.watches[false_code] = ws;
            if conflict.is_some() {
                return conflict;
            }
        }
        None
    }
}

impl SatProofManager<'_> {
    pub(super) fn add_original_clause_step(
        terms: &mut TermStore,
        proof: &mut Proof,
        clause: &[TermId],
        existing_clause_map: &mut HashMap<Vec<TermId>, ProofId>,
        annotation: Option<&ClausificationProof>,
        theory_annotation: Option<&TheoryLemmaProof>,
    ) -> ProofId {
        let key = Self::normalize_clause(clause);
        if let Some(&id) = existing_clause_map.get(&key) {
            return id;
        }

        // Check for clausification proof annotation (#6031 Phase 3). When present,
        // emit a premiseless tautology rule step instead of assume + or.
        // Tautology rules (and_pos, or_neg, etc.) are axiomatic in Alethe.
        if let Some(annot) = annotation {
            // The traced SAT clause may have been literal-permuted by the
            // solver (watched-literal moves), but Alethe tautology rules
            // mandate an exact literal ORDER (e.g. or_pos is
            // `(cl (not (or a b c)) a b c)` — disjuncts in the or's own
            // order). Rebuild the spec-shaped clause from the annotation's
            // source term; fall back to the traced order only when the
            // traced clause isn't dedup-equal to the spec shape.
            let step_clause =
                Self::canonicalize_tautology_clause(terms, &annot.rule, annot.source_term, clause)
                    .unwrap_or_else(|| clause.to_vec());
            let id = proof.add_rule_step(
                annot.rule.clone(),
                step_clause,
                Vec::new(),
                vec![annot.source_term],
            );
            existing_clause_map.insert(key, id);
            return id;
        }

        // Check for theory lemma annotation (#6031 Phase 4). When present,
        // emit a TheoryLemma proof step with the proper Alethe rule.
        if let Some(theory_annot) = theory_annotation {
            let id = if let Some(lia) = theory_annot.lia.clone() {
                proof.add_theory_lemma_with_lia(
                    "theory",
                    clause.to_vec(),
                    theory_annot.farkas.clone(),
                    theory_annot.kind,
                    lia,
                )
            } else {
                proof.add_theory_lemma_with_farkas_and_kind_opt(
                    "theory",
                    clause.to_vec(),
                    theory_annot.farkas.clone(),
                    theory_annot.kind,
                )
            };
            existing_clause_map.insert(key, id);
            return id;
        }

        // Original clauses are input axioms. Emit as Alethe `assume` steps
        // instead of `trust` so carcara accepts them without --allowed-rules
        // trust (#5420 Phase B).
        //
        // Unit clause: (assume hN literal)
        // Multi-literal: (assume hN (or l1 l2 ...))
        //                (step tM (cl l1 l2 ...) :rule or :premises (hN))
        let id = if clause.len() == 1 {
            let assume_id = proof.add_assume(clause[0], None);
            existing_clause_map.insert(key, assume_id);
            return assume_id;
        } else if clause.is_empty() {
            // Empty clause = trivially UNSAT input. Keep as trust since
            // (assume false) + decomposition is non-standard.
            let id =
                proof.add_rule_step(AletheRule::Trust, clause.to_vec(), Vec::new(), Vec::new());
            existing_clause_map.insert(key, id);
            return id;
        } else {
            // Multi-literal: assume the disjunction, then decompose via `or` rule.
            let or_term = terms.mk_or(clause.to_vec());
            let assume_id = proof.add_assume(or_term, None);
            proof.add_rule_step(AletheRule::Or, clause.to_vec(), vec![assume_id], Vec::new())
        };
        existing_clause_map.insert(key, id);
        id
    }

    /// Rebuild the exact Alethe-spec literal order for a clausification
    /// tautology clause from its source term.
    ///
    /// Returns `Some(spec_clause)` when the source term has the shape the
    /// rule expects AND the traced clause is dedup-equal to the spec clause
    /// (same clause up to literal order/duplication — so the swap is purely
    /// a reordering, never a semantic change). Returns `None` otherwise, in
    /// which case the caller keeps the traced order unchanged.
    ///
    /// Spec shapes (Alethe spec, "Tautologous rules"):
    ///   and_pos:  (cl (not (and a1..an)) ak)
    ///   and_neg:  (cl (and a1..an) (not a1) .. (not an))
    ///   or_pos:   (cl (not (or a1..an)) a1 .. an)
    ///   or_neg:   (cl (or a1..an) (not ak))
    ///   xor_pos1: (cl (not (xor a b)) a b)        xor_pos2: (cl (not (xor a b)) (not a) (not b))
    ///   xor_neg1: (cl (xor a b) a (not b))        xor_neg2: (cl (xor a b) (not a) b)
    ///   implies_pos: (cl (not (=> a b)) (not a) b)
    ///   implies_neg1: (cl (=> a b) a)             implies_neg2: (cl (=> a b) (not b))
    ///   equiv_pos1: (cl (not (= a b)) a (not b))  equiv_pos2: (cl (not (= a b)) (not a) b)
    ///   equiv_neg1: (cl (= a b) a b)              equiv_neg2: (cl (= a b) (not a) (not b))
    ///   ite_pos1: (cl (not (ite c t e)) c e)      ite_pos2: (cl (not (ite c t e)) (not c) t)
    ///   ite_neg1: (cl (ite c t e) c (not e))      ite_neg2: (cl (ite c t e) (not c) (not t))
    fn canonicalize_tautology_clause(
        terms: &mut TermStore,
        rule: &AletheRule,
        source: TermId,
        clause: &[TermId],
    ) -> Option<Vec<TermId>> {
        fn neg(terms: &mut TermStore, t: TermId) -> TermId {
            if let TermData::Not(inner) = terms.get(t) {
                return *inner;
            }
            terms.mk_not_raw(t)
        }

        // (op, args) view of the source term for the connective rules.
        let app: Option<(String, Vec<TermId>)> = match terms.get(source) {
            TermData::App(sym, args) => Some((sym.name().to_string(), args.clone())),
            TermData::Ite(c, t, e) => Some(("ite".to_string(), vec![*c, *t, *e])),
            _ => None,
        };
        let not_source = neg(terms, source);

        let expected: Vec<TermId> = match rule {
            AletheRule::OrPos(_) => {
                let (op, args) = app?;
                if op != "or" {
                    return None;
                }
                let mut v = vec![not_source];
                v.extend(args);
                v
            }
            AletheRule::AndNeg => {
                let (op, args) = app?;
                if op != "and" {
                    return None;
                }
                let mut v = vec![source];
                for a in args {
                    v.push(neg(terms, a));
                }
                v
            }
            AletheRule::AndPos(i) => {
                let (op, args) = app?;
                if op != "and" {
                    return None;
                }
                let ak = *args.get(*i as usize)?;
                vec![not_source, ak]
            }
            AletheRule::OrNeg => {
                let (op, args) = app?;
                if op != "or" {
                    return None;
                }
                // The annotation does not record k; recover it from the
                // traced clause (binary: source-literal + (not ak)).
                if clause.len() != 2 {
                    return None;
                }
                let other = *clause.iter().find(|&&l| l != source)?;
                let ok = args.iter().any(|&a| neg(terms, a) == other);
                if !ok {
                    return None;
                }
                vec![source, other]
            }
            AletheRule::XorPos1
            | AletheRule::XorPos2
            | AletheRule::XorNeg1
            | AletheRule::XorNeg2 => {
                let (op, args) = app?;
                if op != "xor" || args.len() != 2 {
                    return None;
                }
                let (a, b) = (args[0], args[1]);
                match rule {
                    AletheRule::XorPos1 => vec![not_source, a, b],
                    AletheRule::XorPos2 => {
                        let (na, nb) = (neg(terms, a), neg(terms, b));
                        vec![not_source, na, nb]
                    }
                    AletheRule::XorNeg1 => {
                        let nb = neg(terms, b);
                        vec![source, a, nb]
                    }
                    _ => {
                        let na = neg(terms, a);
                        vec![source, na, b]
                    }
                }
            }
            AletheRule::ImpliesPos | AletheRule::ImpliesNeg1 | AletheRule::ImpliesNeg2 => {
                let (op, args) = app?;
                if op != "=>" || args.len() != 2 {
                    return None;
                }
                let (a, b) = (args[0], args[1]);
                match rule {
                    AletheRule::ImpliesPos => {
                        let na = neg(terms, a);
                        vec![not_source, na, b]
                    }
                    AletheRule::ImpliesNeg1 => vec![source, a],
                    _ => {
                        let nb = neg(terms, b);
                        vec![source, nb]
                    }
                }
            }
            AletheRule::EquivPos1
            | AletheRule::EquivPos2
            | AletheRule::EquivNeg1
            | AletheRule::EquivNeg2 => {
                let (op, args) = app?;
                if op != "=" || args.len() != 2 {
                    return None;
                }
                let (a, b) = (args[0], args[1]);
                match rule {
                    AletheRule::EquivPos1 => {
                        let nb = neg(terms, b);
                        vec![not_source, a, nb]
                    }
                    AletheRule::EquivPos2 => {
                        let na = neg(terms, a);
                        vec![not_source, na, b]
                    }
                    AletheRule::EquivNeg1 => vec![source, a, b],
                    _ => {
                        let (na, nb) = (neg(terms, a), neg(terms, b));
                        vec![source, na, nb]
                    }
                }
            }
            AletheRule::ItePos1
            | AletheRule::ItePos2
            | AletheRule::IteNeg1
            | AletheRule::IteNeg2 => {
                let (op, args) = app?;
                if op != "ite" || args.len() != 3 {
                    return None;
                }
                let (c, t, e) = (args[0], args[1], args[2]);
                match rule {
                    AletheRule::ItePos1 => vec![not_source, c, e],
                    AletheRule::ItePos2 => {
                        let nc = neg(terms, c);
                        vec![not_source, nc, t]
                    }
                    AletheRule::IteNeg1 => {
                        let ne = neg(terms, e);
                        vec![source, c, ne]
                    }
                    _ => {
                        let (nc, nt) = (neg(terms, c), neg(terms, t));
                        vec![source, nc, nt]
                    }
                }
            }
            _ => return None,
        };

        // Only reorder — the traced clause must be dedup-equal to the spec
        // shape, otherwise leave it alone.
        if Self::normalize_clause(&expected) == Self::normalize_clause(clause) {
            Some(expected)
        } else {
            None
        }
    }

    /// Bridge a level-0-minimized theory conflict clause back to its
    /// recorded full lemma (#rank-4 increment 2).
    ///
    /// The SAT layer strips level-0-false literals from theory conflict
    /// clauses on add, so the traced "original" clause is a strict SUBSET of
    /// the clause the theory solver reported (and that the proof tracker
    /// recorded, with Farkas certificate when available). This finds a
    /// recorded lemma clause that is a superset of the traced clause, emits
    /// it as the (certified) `TheoryLemma` leaf, and derives the traced
    /// clause from it via the increment-1 RUP replay — the stripped literals
    /// resolve away against the level-0 units already in the processed
    /// clause database, as explicit `Resolution` steps.
    ///
    /// Returns `None` (caller falls back to the anonymous-assume path) when
    /// no recorded superset exists, a stripped literal has no SAT encoding,
    /// or the replay cannot reach the traced clause. Purely a proof-shape
    /// improvement: verdicts and traced clauses are never altered.
    pub(super) fn try_bridge_minimized_theory_lemma(
        &mut self,
        target_terms: &[TermId],
        target_sat: &[Literal],
        normalized_key: &[TermId],
        clause_versions: &mut Vec<SatClauseVersion>,
        existing_clause_map: &mut HashMap<Vec<TermId>, ProofId>,
        engine: &mut RupEngine,
        proof: &mut Proof,
    ) -> Option<(ProofId, Vec<TermId>, Vec<Literal>)> {
        let lemma_proofs = self.theory_lemma_proofs?;

        let mut candidates: Vec<&Vec<TermId>> = lemma_proofs
            .keys()
            .filter(|full| {
                full.len() > normalized_key.len()
                    && full.len() - normalized_key.len() <= MAX_BRIDGE_EXTRA_LITERALS
                    && normalized_key.iter().all(|lit| full.contains(lit))
            })
            .collect();
        if candidates.is_empty() {
            return None;
        }
        // Deterministic preference: closest superset first.
        candidates.sort_unstable_by(|a, b| (a.len(), a.as_slice()).cmp(&(b.len(), b.as_slice())));
        candidates.truncate(MAX_BRIDGE_CANDIDATES);

        // Term -> SAT literal for the stripped literals (inverse of
        // `var_to_term`, with explicit `not` handling). Must stay consistent
        // with `lit_to_term`, so each mapping is verified by round-trip.
        let mut atom_to_var: HashMap<TermId, u32> = HashMap::default();
        for (&var, &term) in self.var_to_term.iter() {
            atom_to_var.insert(term, var);
        }

        for full in candidates {
            let annotation = lemma_proofs.get(full)?;

            let mut full_sat: Vec<Literal> = Vec::with_capacity(full.len());
            let mut mapped = true;
            for &lit_term in full {
                let sat_lit = if let Some(&var) = atom_to_var.get(&lit_term) {
                    Literal::positive(Variable::new(var))
                } else if let TermData::Not(inner) = self.terms.get(lit_term) {
                    match atom_to_var.get(inner) {
                        Some(&var) => Literal::negative(Variable::new(var)),
                        None => {
                            mapped = false;
                            break;
                        }
                    }
                } else {
                    mapped = false;
                    break;
                };
                // Round-trip consistency with `lit_to_term`.
                if self.lit_to_term(sat_lit) != Some(lit_term) {
                    mapped = false;
                    break;
                }
                full_sat.push(sat_lit);
            }
            if !mapped {
                continue;
            }

            let lemma_proof = Self::add_original_clause_step(
                self.terms,
                proof,
                full,
                existing_clause_map,
                None,
                Some(annotation),
            );
            let version = clause_versions.len();
            clause_versions.push((full_sat, lemma_proof));

            match self.derive_clause_via_rup_replay(
                target_terms,
                target_sat,
                &[version],
                clause_versions,
                engine,
                proof,
            ) {
                Ok((derived_proof, derived_terms, derived_sat)) => {
                    existing_clause_map
                        .entry(Self::normalize_clause(&derived_terms))
                        .or_insert(derived_proof);
                    return Some((derived_proof, derived_terms, derived_sat));
                }
                Err(error) => {
                    tracing::debug!(
                        ?error,
                        target_len = target_terms.len(),
                        full_len = full.len(),
                        "minimized-lemma bridge replay failed; trying next candidate"
                    );
                }
            }
        }
        None
    }

    /// Certified re-derivation of a derived-fact trace clause by bounded
    /// DPLL with resolution logging (#seq-unit-fact).
    ///
    /// Two clause classes end here (the QF_UF SEQ finite-model families):
    ///
    /// - a fact learned in an EARLIER solver iteration that the incremental
    ///   split loop imported into the final SAT run as an input unit clause
    ///   (e.g. `(not (= c3 c_0))`): the trace marks it "original" with no
    ///   clausification/theory annotation, no recorded superset lemma
    ///   bridges it, and it is not RUP w.r.t. the processed clause database
    ///   (its refutation needs case splits on the totality `or` clauses) —
    ///   so it would fall through to an anonymous `assume` that later
    ///   demotes to a premiseless `trust` step;
    /// - a LEARNED clause whose recorded hint chain fails both hint replay
    ///   and DRUP widening (level-0 restarts drop reason clauses from the
    ///   trace), which would fall to the `trust`-with-premises step.
    ///
    /// This assumes the negation of every target literal and refutes it with
    /// a bounded DPLL search over ALL processed clause versions: each
    /// conflict is folded into explicit `Resolution` steps over existing
    /// proof nodes (the same fold as the RUP replay), and the two branch
    /// refutations of each decision literal are resolved on that literal.
    /// Every leaf is a clause the proof already derives; every emitted step
    /// is an ordinary resolution — no new axioms. Fail-closed: on node/
    /// step-budget exhaustion, an unmapped literal, or a satisfying
    /// assignment, returns `None` and the caller's fallback runs unchanged.
    pub(super) fn derive_clause_via_bounded_dpll(
        &mut self,
        target_sat: &[Literal],
        clause_versions: &mut Vec<SatClauseVersion>,
        existing_clause_map: &mut HashMap<Vec<TermId>, ProofId>,
        proof: &mut Proof,
    ) -> Option<(ProofId, Vec<TermId>, Vec<Literal>)> {
        if target_sat.is_empty() {
            return None;
        }
        // A tautological target is not refutation-derivable.
        for (i, &l) in target_sat.iter().enumerate() {
            if target_sat[i + 1..].contains(&l.negated()) {
                return None;
            }
        }
        let lemma_proofs = self.theory_lemma_proofs?;

        // The imported fact sits EARLY in the trace, before the trace entries
        // that (re-)introduce the theory lemmas its refutation needs — but
        // the recorded lemma annotations are available up front. Materialize
        // every mappable recorded lemma clause as a certified `TheoryLemma`
        // leaf so the search runs over the FULL certified clause set; roll
        // everything back if the search fails (unused leaves that survive a
        // successful search are pruned with the rest of the dead steps).
        let steps_snapshot = proof.steps.len();
        let versions_snapshot = clause_versions.len();
        let mut added_keys: Vec<Vec<TermId>> = Vec::new();

        let mut atom_to_var: HashMap<TermId, u32> = HashMap::default();
        for (&var, &term) in self.var_to_term.iter() {
            atom_to_var.insert(term, var);
        }
        let lemma_clauses: Vec<Vec<TermId>> = {
            let mut keys: Vec<&Vec<TermId>> = lemma_proofs.keys().collect();
            // Deterministic materialization order.
            keys.sort_unstable();
            keys.into_iter().cloned().collect()
        };
        for full in &lemma_clauses {
            let annotation = lemma_proofs.get(full)?;
            let mut full_sat: Vec<Literal> = Vec::with_capacity(full.len());
            let mut mapped = true;
            for &lit_term in full {
                let sat_lit = if let Some(&var) = atom_to_var.get(&lit_term) {
                    Literal::positive(Variable::new(var))
                } else if let TermData::Not(inner) = self.terms.get(lit_term) {
                    match atom_to_var.get(inner) {
                        Some(&var) => Literal::negative(Variable::new(var)),
                        None => {
                            mapped = false;
                            break;
                        }
                    }
                } else {
                    mapped = false;
                    break;
                };
                // Round-trip consistency with `lit_to_term`.
                if self.lit_to_term(sat_lit) != Some(lit_term) {
                    mapped = false;
                    break;
                }
                full_sat.push(sat_lit);
            }
            if !mapped {
                continue;
            }
            let key = Self::normalize_clause(full);
            let track_key = !existing_clause_map.contains_key(&key);
            let lemma_proof = Self::add_original_clause_step(
                self.terms,
                proof,
                full,
                existing_clause_map,
                None,
                Some(annotation),
            );
            if track_key {
                added_keys.push(key);
            }
            clause_versions.push((full_sat, lemma_proof));
        }

        // Fresh local engine: the shared engine's watch index is append-only
        // over `clause_versions` and would be corrupted by the rollback.
        let mut engine = RupEngine::default();
        let mut assumps: Vec<Literal> = target_sat.iter().map(|l| l.negated()).collect();
        let mut nodes = 0usize;
        let mut theory_checks = 0usize;
        let result = self.dpll_refute(
            &mut assumps,
            clause_versions,
            &mut engine,
            proof,
            &mut nodes,
            &mut theory_checks,
        );
        let Some((derived_proof, derived_sat)) = result else {
            // Fail closed: remove the materialized leaves and map entries.
            proof.steps.truncate(steps_snapshot);
            clause_versions.truncate(versions_snapshot);
            for key in added_keys {
                existing_clause_map.remove(&key);
            }
            return None;
        };
        // The derived clause's literals are negations of assumptions, i.e. a
        // subclause of the target (possibly strict — a stronger result,
        // returned as-is like the RUP replay does).
        debug_assert!(derived_sat.iter().all(|l| target_sat.contains(l)));
        let derived_terms = self.clause_to_terms(&derived_sat)?;
        Some((derived_proof, derived_terms, derived_sat))
    }

    /// One bounded-DPLL(T) node: propagate under `assumps`; fold a conflict
    /// into resolution steps; on a propositional stall consult the LRA
    /// theory oracle ([`Self::try_certify_arith_conflict_from_trail`]) —
    /// a certified theory conflict is folded exactly like a propagation
    /// conflict; else split on an unassigned literal of an unsatisfied
    /// clause and resolve the branch refutations. Returns a proof of a
    /// clause whose literals are negations of (a subset of) `assumps`.
    ///
    /// `theory_checks` caps the number of fresh-solver oracle calls per
    /// search (fail-closed on exhaustion). `clause_versions` may GROW
    /// (recorded theory lemmas); it is append-only, so the engine's watch
    /// index stays valid.
    fn dpll_refute(
        &mut self,
        assumps: &mut Vec<Literal>,
        clause_versions: &mut Vec<SatClauseVersion>,
        engine: &mut RupEngine,
        proof: &mut Proof,
        nodes: &mut usize,
        theory_checks: &mut usize,
    ) -> Option<(ProofId, Vec<Literal>)> {
        *nodes += 1;
        if *nodes > DPLL_MAX_NODES {
            return None;
        }
        debug_assert!(engine.trail.is_empty(), "RUP engine not reset");
        for &a in assumps.iter() {
            if engine.value(a).is_none() {
                engine.assign(a);
            }
        }
        let mut implications: Vec<(usize, Literal)> = Vec::new();
        let mut used: HashSet<usize> = Default::default();
        let mut budget = self.step_budget;
        let conflict = engine.propagate(clause_versions, &mut implications, &mut used, &mut budget);
        let budget_exhausted = matches!(budget, Some(0));
        self.step_budget = budget;

        if let Some(conflict_version) = conflict {
            let folded = self.fold_conflict_to_assumption_clause(
                conflict_version,
                &implications,
                assumps,
                clause_versions,
                engine,
                proof,
            );
            engine.reset();
            return folded;
        }

        // Propositional stall: ask the theory oracle whether the assigned
        // arithmetic literals are already jointly infeasible. A certified
        // conflict prunes the whole subtree here (the recorded exclusion
        // lemma is all-false under the current assignment), which is what
        // makes the ReLU case-split family close without exponential
        // model-leaf enumeration. Budgeted + fail-closed: on `None` the
        // node proceeds to an ordinary decision.
        if !budget_exhausted && *theory_checks < DPLL_MAX_THEORY_CHECKS {
            *theory_checks += 1;
            if let Some(conflict_version) =
                self.try_certify_arith_conflict_from_trail(clause_versions, engine, proof)
            {
                let folded = self.fold_conflict_to_assumption_clause(
                    conflict_version,
                    &implications,
                    assumps,
                    clause_versions,
                    engine,
                    proof,
                );
                engine.reset();
                return folded;
            }
        }

        // No conflict: pick a decision literal from an unsatisfied clause
        // while the assignment is still live.
        let mut decision: Option<Literal> = None;
        if !budget_exhausted {
            'clauses: for (clause, _) in clause_versions.iter() {
                let mut unassigned: Option<Literal> = None;
                for &l in clause {
                    match engine.value(l) {
                        Some(true) => continue 'clauses,
                        None => {
                            if unassigned.is_none() {
                                unassigned = Some(l);
                            }
                        }
                        Some(false) => {}
                    }
                }
                // A fully-false clause would have conflicted in propagation;
                // an unassigned literal is the split point.
                if let Some(u) = unassigned {
                    decision = Some(u);
                    break;
                }
            }
        }
        engine.reset();
        // Every clause satisfied (a model of the database extends the
        // assumptions) or budget exhausted: fail closed.
        let decision = decision?;

        // Branch 1: assume the literal.
        assumps.push(decision);
        let left = self.dpll_refute(
            assumps,
            clause_versions,
            engine,
            proof,
            nodes,
            theory_checks,
        );
        assumps.pop();
        let (left_proof, left_clause) = left?;
        let neg_decision = decision.negated();
        if !left_clause.contains(&neg_decision) {
            // The refutation never used the decision: it already refutes the
            // parent assumptions.
            return Some((left_proof, left_clause));
        }

        // Branch 2: assume the negation.
        assumps.push(neg_decision);
        let right = self.dpll_refute(
            assumps,
            clause_versions,
            engine,
            proof,
            nodes,
            theory_checks,
        );
        assumps.pop();
        let (right_proof, right_clause) = right?;
        if !right_clause.contains(&decision) {
            return Some((right_proof, right_clause));
        }

        // Resolve the branches on the decision literal. The resolvent's
        // literals are negations of the parent assumptions.
        let mut resolvent: Vec<Literal> =
            Vec::with_capacity(left_clause.len() + right_clause.len());
        for &l in left_clause.iter().chain(right_clause.iter()) {
            if l != decision && l != neg_decision && !resolvent.contains(&l) {
                resolvent.push(l);
            }
        }
        // Pivot convention matches the RUP replay fold: the pivot literal as
        // it occurs in the LEFT premise.
        let pivot_term = self.lit_to_term(neg_decision)?;
        let resolvent_terms = self.clause_to_terms(&resolvent)?;
        let resolvent_proof =
            proof.add_resolution(resolvent_terms, pivot_term, left_proof, right_proof);
        Some((resolvent_proof, resolvent))
    }

    /// Fold a propagation conflict into a resolution chain over the recorded
    /// implications (the step-3 fold of `derive_clause_via_rup_replay`),
    /// stopping at a clause whose literals are all falsified directly by
    /// `assumps` (their negations). Emits term-level `Resolution` steps.
    fn fold_conflict_to_assumption_clause(
        &mut self,
        conflict_version: usize,
        implications: &[(usize, Literal)],
        assumps: &[Literal],
        clause_versions: &[SatClauseVersion],
        _engine: &RupEngine,
        proof: &mut Proof,
    ) -> Option<(ProofId, Vec<Literal>)> {
        let (conflict_clause, conflict_proof) = clause_versions.get(conflict_version)?;
        let mut current_sat = conflict_clause.clone();
        let mut current_proof = *conflict_proof;

        for &(version, lit) in implications.iter().rev() {
            let neg_lit = lit.negated();
            if !current_sat.contains(&neg_lit) {
                continue;
            }
            let (reason_clause, reason_proof) = clause_versions.get(version)?;

            // SAT-level resolvent (dedup; conflict-analysis sized).
            let mut resolvent: Vec<Literal> =
                Vec::with_capacity(current_sat.len() + reason_clause.len());
            for &l in current_sat.iter().chain(reason_clause.iter()) {
                if l != neg_lit && l != lit && !resolvent.contains(&l) {
                    resolvent.push(l);
                }
            }

            // Pivot convention matches resolve_once: the pivot literal as it
            // occurs in the left premise (`current_sat`).
            let pivot_term = self.lit_to_term(neg_lit)?;
            let resolvent_terms = self.clause_to_terms(&resolvent)?;

            current_proof = proof.add_resolution(
                resolvent_terms.clone(),
                pivot_term,
                current_proof,
                *reason_proof,
            );
            current_sat = resolvent;
        }

        // Every remaining literal must be the negation of an assumption.
        if current_sat.iter().all(|l| assumps.contains(&l.negated())) {
            Some((current_proof, current_sat))
        } else {
            None
        }
    }

    /// Derive the empty clause by RUP replay over the entire processed clause
    /// database (#rank-4 increment 5).
    ///
    /// The SAT solver can exit UNSAT from a propagation conflict at decision
    /// level 0 — the common shape on the executor's incremental
    /// theory-conflict pipeline, where the final theory conflict clause is
    /// added at level 0, propagates, and immediately conflicts. That exit
    /// records no empty-clause trace entry (only the trace-level UNSAT flag,
    /// see `finalize_unsat_proof`), so `process_trace` historically fell
    /// through to the whole-problem trust closer
    /// (`derive_empty_via_trust_lemma`), replacing the entire derivation with
    /// one giant uncertified trust lemma — fatal for proof-backed Craig
    /// interpolation.
    ///
    /// A level-0 propagation conflict is RUP-derivable from the clause
    /// database by definition, and `derive_clause_via_rup_replay` already
    /// folds the propagation trail into explicit, independently checkable
    /// `Resolution` steps. Fail-closed: any replay failure (no conflict
    /// reachable, oversized database, residual literals) returns `None` and
    /// the existing fallbacks run unchanged. Proof-shape only — verdicts are
    /// never affected.
    ///
    /// The replay database is the processed trace clauses PLUS the
    /// SAT-encodings of `TheoryLemma` steps already present in the proof:
    /// the executor's extension propagator can detect a level-0 THEORY
    /// conflict (e.g. an LIA Farkas conflict over trail atoms) and declare
    /// UNSAT directly — the (certified) conflict lemma is recorded in the
    /// proof tracker but its clause never reaches the SAT trace. Including
    /// those lemma steps lets propagation reach the theory conflict, with the
    /// certified lemma as the resolution leaf.
    /// Re-derive a genuine LRA Farkas conflict lemma for a residual set of
    /// theory atoms and record it onto `proof` so `derive_empty_via_level0_rup`
    /// can RUP-close the empty clause (#clause_id=26 / geometry_consumer L0 north-star).
    ///
    /// The SAT/theory pipeline can reach a level-0 UNSAT whose empty-clause
    /// hint chain resolves down to a residual arithmetic clause `[T22,T23]`
    /// (positive atoms) that is only closed by the theory-conflict-exclusion
    /// lemma `[¬T22,¬T23]`. That exclusion lemma is emitted upstream only when
    /// the eager theory `check()` returns Unsat over *exactly* that pair; when
    /// the contradiction only surfaces after resolution it is never recorded,
    /// so `level0_rup` has no lemma to replay and the clause falls to Trust.
    ///
    /// This re-derives the missing certificate the same way
    /// `try_lra_farkas_reconstruction` and the #6242 bound-axiom gate do:
    /// drive a FRESH `LraSolver` over the residual atoms, asserting the
    /// CONFLICT polarity (a positive residual literal `T` becomes the assertion
    /// `T = true`), and take the solver's own `UnsatWithFarkas` certificate.
    ///
    /// Fail-closed (soundness bar): the lemma is recorded ONLY when the fresh
    /// solver returns `UnsatWithFarkas` with a present, shape-valid Farkas
    /// certificate over an all-arithmetic core; the emitted `LraFarkas` step is
    /// then strict-validated end-to-end by `check_proof_strict`
    /// (`validate_lra_farkas` → `verify_farkas_conflict_lits_full`). If the
    /// solver returns anything else (Sat, plain Unsat, missing/overflowed
    /// certificate, non-arith literal), NOTHING is recorded and the caller
    /// falls back to Trust — never a false proof.
    ///
    /// The blocking clause is built with `mk_not_raw` over the solver's OWN
    /// `conflict.literals` (the certified UNSAT core), positionally aligned
    /// with the Farkas coefficients, matching `lit_to_term`'s negation form so
    /// the `derive_empty_via_level0_rup` round-trip guard maps it.
    ///
    /// Returns `true` iff a certified lemma was appended to `proof`.
    /// Level-0 unit-propagation closure over the processed clause database,
    /// mapped to `(theory atom, asserted value)` pairs a fresh `LraSolver`
    /// can replay — the context handed to
    /// [`Self::record_residual_lra_conflict_lemma`].
    ///
    /// The previous context was the unit CLAUSES only. That misses every
    /// level-0 literal that is only derivable by propagation *through* the
    /// Boolean structure — exactly the ReLU/case-split family, where the
    /// bound that makes the residual branch infeasible sits behind an
    /// or_pos/and_pos decomposition (e.g. `(<= x z)` behind the equality's
    /// and-split, or the refuted branch's conjuncts behind the disjunction's
    /// Tseitin definition). Every literal in this closure is a decision-free
    /// consequence of the clause database, so a conflict lemma recorded over
    /// it is guaranteed to conflict under `derive_empty_via_level0_rup`'s
    /// replay — which then folds the propagation trail into genuine,
    /// independently checkable `Resolution` steps (no trust).
    ///
    /// The closure is filtered to literals the fresh LRA solver can actually
    /// assert toward a Farkas certificate:
    /// * binary `<`/`<=`/`>`/`>=` comparisons over Int/Real operands, either
    ///   polarity (a negated bound is the complementary bound);
    /// * binary `=` over Int/Real operands, POSITIVE polarity only — an
    ///   asserted disequality is not a linear bound (it triggers a
    ///   disequality-split request instead of `UnsatWithFarkas`, and a core
    ///   containing it would not print as a valid `la_generic`).
    ///
    /// Boolean gate atoms (the or/and Tseitin heads the old unit-clause
    /// context leaked into the solver, driving `check()` to `Unknown`) are
    /// excluded by the same filter. Fail-closed callers are unaffected: a
    /// too-large database falls back to the (filtered) unit-clause context.
    pub(super) fn level0_arith_context(
        &mut self,
        clause_versions: &[SatClauseVersion],
    ) -> Vec<(TermId, bool)> {
        // Collect the closure as SAT literals first (releases no borrow on
        // `self.terms`, which the filter below needs).
        let closure: Vec<Literal> = if clause_versions.len() <= MAX_RUP_WIDENING_VERSIONS {
            let mut engine = RupEngine::default();
            let mut implications: Vec<(usize, Literal)> = Vec::new();
            let mut used: HashSet<usize> = Default::default();
            let mut budget = self.step_budget;
            // A conflict here means level0_rup will close by itself; the
            // trail collected so far is still a valid (level-0) context.
            let _ = engine.propagate(clause_versions, &mut implications, &mut used, &mut budget);
            self.step_budget = budget;
            engine.trail.clone()
        } else {
            // Oversized database: degrade to the historical unit-clause
            // context (now arith-filtered like the closure).
            clause_versions
                .iter()
                .filter(|(lits, _)| lits.len() == 1)
                .map(|(lits, _)| lits[0])
                .collect()
        };
        self.arith_context_from_lits(&closure)
    }

    /// Whether `t` is a PURE linear-arithmetic term: numerals, arithmetic
    /// variables, and `+`/`-`/`*`/`/` applications thereof. Same discipline
    /// as the executor's la_generic-promotion gates (`proof_trust_surgery`):
    /// an external `la_generic` checker evaluates the linear combination
    /// SYNTACTICALLY, so an impure atom (a `select`, a UF application, a
    /// genuine nonlinear monomial) must never enter a printed Farkas core —
    /// the fresh solver treats such atoms conservatively and can return
    /// padded cores whose unit coefficients do not actually cancel
    /// (observed: a QF_NRA case-split core including `(<= (* x x) 1)` with
    /// coefficient 1, which carcara rejects as non-contradictory).
    fn term_is_pure_linear_arith(&self, t: TermId) -> bool {
        if !matches!(self.terms.sort(t), ay_core::Sort::Int | ay_core::Sort::Real) {
            return false;
        }
        match self.terms.get(t) {
            TermData::Const(_) | TermData::Var(..) => true,
            TermData::App(ay_core::Symbol::Named(op), args) => match op.as_str() {
                "+" | "-" => args.iter().all(|&a| self.term_is_pure_linear_arith(a)),
                // LINEAR multiplication only: at most one non-constant factor
                // (`(* x x)` is a nonlinear monomial — exactly the padded-core
                // trap this filter exists to keep out).
                "*" => {
                    args.iter().all(|&a| self.term_is_pure_linear_arith(a))
                        && args
                            .iter()
                            .filter(|&&a| !self.term_is_constant_arith(a))
                            .count()
                            <= 1
                }
                // Division by CONSTANTS only.
                "/" => args.split_first().is_some_and(|(&num, dens)| {
                    self.term_is_pure_linear_arith(num)
                        && dens.iter().all(|&d| self.term_is_constant_arith(d))
                }),
                _ => false,
            },
            _ => false,
        }
    }

    /// Whether `t` is a constant arithmetic expression (numerals combined
    /// with `+`/`-`/`*`/`/` only).
    fn term_is_constant_arith(&self, t: TermId) -> bool {
        match self.terms.get(t) {
            TermData::Const(_) => true,
            TermData::App(ay_core::Symbol::Named(op), args) => {
                matches!(op.as_str(), "+" | "-" | "*" | "/")
                    && args.iter().all(|&a| self.term_is_constant_arith(a))
            }
            _ => false,
        }
    }

    /// Map assigned SAT literals to `(theory atom, asserted value)` pairs a
    /// fresh `LraSolver` can assert toward a Farkas certificate (see
    /// [`Self::level0_arith_context`] for the filter rationale). Order and
    /// first-seen polarity are preserved; unmapped, non-arithmetic, or
    /// IMPURE literals (see [`Self::term_is_pure_linear_arith`]) are
    /// silently dropped (fail-closed consumers only ever get FEWER context
    /// literals, never a wrong one).
    fn arith_context_from_lits(&self, lits: &[Literal]) -> Vec<(TermId, bool)> {
        let mut seen: HashSet<TermId> = Default::default();
        let mut context: Vec<(TermId, bool)> = Vec::with_capacity(lits.len());
        for &lit in lits {
            let Some(&atom) = self.var_to_term.get(&(lit.variable().index() as u32)) else {
                continue;
            };
            let value = lit.is_positive();
            let assertable = match self.terms.get(atom) {
                TermData::App(ay_core::Symbol::Named(op), args) if args.len() == 2 => {
                    let pure = args.iter().all(|&a| self.term_is_pure_linear_arith(a));
                    pure && match op.as_str() {
                        "<" | "<=" | ">" | ">=" => true,
                        "=" => value,
                        _ => false,
                    }
                }
                _ => false,
            };
            if assertable && seen.insert(atom) {
                context.push((atom, value));
            }
        }
        context
    }

    /// Theory oracle for the bounded-DPLL(T) refutation (#relu-trust-glue):
    /// when propagation stalls without a propositional conflict, ask a FRESH
    /// `LraSolver` whether the currently-assigned arithmetic literals are
    /// jointly infeasible. On `UnsatWithFarkas`, record the certified
    /// exclusion lemma as a `TheoryLemma` proof leaf, append its clause to
    /// the search database, and return the new version index — the caller
    /// folds it exactly like a propagation conflict (the clause is by
    /// construction all-false under the current assignment).
    ///
    /// This is the missing piece of the ReLU-disjunction family: the live
    /// pipeline refutes case-split branches eagerly and (for all but the
    /// branch that ends the search) never records the exclusion lemma, so
    /// the traced clause set is propositionally SATISFIABLE and no
    /// resolution reconstruction can possibly reach `(cl)`. Re-deriving the
    /// lemma at the stalled assignment restores exactly that information —
    /// with a solver-produced Farkas certificate, never a fabricated one.
    ///
    /// SOUNDNESS (fail-closed at every gate):
    /// * only literals passing the [`Self::arith_context_from_lits`] filter
    ///   are asserted; anything else (Boolean gates, UF atoms, negated
    ///   equalities) is invisible to the oracle;
    /// * the certificate must be `UnsatWithFarkas` with a present Farkas
    ///   annotation aligned 1:1 with the core, and every core literal must
    ///   be one of the asserted `(atom, value)` pairs (identical polarity);
    /// * the blocking clause must map back to SAT literals (round-trip via
    ///   `lit_to_term`) and be all-FALSE under the current assignment;
    /// * any failure returns `None` and the search proceeds to an honest
    ///   model/fallback — no step is recorded.
    ///
    /// The recorded lemma is a genuine theory tautology independent of the
    /// search state, so leaving it in the proof is sound even if the
    /// enclosing search later fails (the caller rolls back to a snapshot
    /// anyway).
    fn try_certify_arith_conflict_from_trail(
        &mut self,
        clause_versions: &mut Vec<SatClauseVersion>,
        engine: &RupEngine,
        proof: &mut Proof,
    ) -> Option<usize> {
        let context = self.arith_context_from_lits(&engine.trail);
        if context.is_empty() {
            return None;
        }

        // Fresh solver over the assigned arithmetic literals only.
        let mut lra = ay_lra::LraSolver::new(&*self.terms);
        lra.set_combined_theory_mode(true);
        for &(atom, _) in &context {
            ay_core::TheorySolver::register_atom(&mut lra, atom);
        }
        for &(atom, value) in &context {
            ay_core::TheorySolver::assert_literal(&mut lra, atom, value);
        }
        let ay_core::TheoryResult::UnsatWithFarkas(conflict) =
            ay_core::TheorySolver::check(&mut lra)
        else {
            return None;
        };
        let farkas = conflict.farkas?;
        if conflict.literals.is_empty() || conflict.literals.len() != farkas.coefficients.len() {
            return None;
        }
        // Every core literal must be one of the asserted pairs, with the
        // SAME polarity — the certificate must speak about exactly what the
        // assignment asserted.
        let asserted: HashMap<TermId, bool> = context.iter().copied().collect();
        if !conflict
            .literals
            .iter()
            .all(|lit| asserted.get(&lit.term) == Some(&lit.value))
        {
            return None;
        }

        // Blocking clause = negation of the core, positionally aligned with
        // the Farkas coefficients (`mk_not_raw` matches `lit_to_term`'s
        // negation form).
        let mut clause_terms: Vec<TermId> = Vec::with_capacity(conflict.literals.len());
        for lit in &conflict.literals {
            if lit.value {
                clause_terms.push(self.terms.mk_not_raw(lit.term));
            } else {
                clause_terms.push(lit.term);
            }
        }

        // Map to SAT literals (round-trip verified) and require the clause to
        // be all-false under the current assignment so the caller's conflict
        // fold is guaranteed to apply.
        let mut atom_to_var: HashMap<TermId, u32> = HashMap::default();
        for (&var, &term) in self.var_to_term.iter() {
            atom_to_var.insert(term, var);
        }
        let mut sat_clause: Vec<Literal> = Vec::with_capacity(clause_terms.len());
        for &lit_term in &clause_terms {
            let sat_lit = if let Some(&var) = atom_to_var.get(&lit_term) {
                Literal::positive(Variable::new(var))
            } else if let TermData::Not(inner) = self.terms.get(lit_term) {
                Literal::negative(Variable::new(*atom_to_var.get(inner)?))
            } else {
                return None;
            };
            if self.lit_to_term(sat_lit) != Some(lit_term) {
                return None;
            }
            if engine.value(sat_lit) != Some(false) {
                return None;
            }
            sat_clause.push(sat_lit);
        }

        // Same classification discipline as the residual rescue: the strict
        // checker (`validate_lra_farkas`) is the final arbiter.
        let classified =
            crate::theory_inference::infer_theory_lemma_kind_from_clause_terms_and_farkas(
                &*self.terms,
                &clause_terms,
                Some(&farkas),
            );
        let kind = match classified {
            TheoryLemmaKind::LraFarkas | TheoryLemmaKind::LiaGeneric => classified,
            _ => TheoryLemmaKind::LraFarkas,
        };
        let lemma_id =
            proof.add_theory_lemma_with_farkas_and_kind("lra", clause_terms, farkas, kind);
        let version = clause_versions.len();
        clause_versions.push((sat_clause, lemma_id));
        Some(version)
    }

    pub(super) fn record_residual_lra_conflict_lemma(
        &mut self,
        residual_clause: &[TermId],
        level0_context: &[(TermId, bool)],
        proof: &mut Proof,
    ) -> bool {
        if residual_clause.is_empty() {
            return false;
        }
        // Extract the raw atom behind each residual literal (strip any `Not`
        // wrapper) and de-duplicate; these are the atoms whose joint assertion
        // must be LRA-infeasible for the exclusion lemma to be valid.
        let mut atoms: Vec<TermId> = Vec::with_capacity(residual_clause.len());
        for &lit in residual_clause {
            let atom = match self.terms.get(lit) {
                TermData::Not(inner) => *inner,
                _ => lit,
            };
            if !atoms.contains(&atom) {
                atoms.push(atom);
            }
        }

        // Drive a FRESH LraSolver, asserting the CONFLICT polarity of the
        // residual atoms (each `T` asserted `T = true`). We accept a certificate
        // ONLY when its certified UNSAT core is exactly the residual atoms — so
        // the recorded blocking clause is precisely `[¬T22,¬T23]`, the lemma
        // `derive_empty_via_level0_rup` needs to RUP-close `[]`.
        //
        // Two phases, because the residual pair may or may not be a
        // self-contained LRA conflict:
        //   1. residual atoms ALONE. If they are jointly infeasible the solver
        //      returns a core over exactly those atoms (the common case; T22 and
        //      T23 are asserted as level-0 units, so their joint infeasibility is
        //      a statement about the pair alone).
        //   2. only if phase 1 is SAT, widen with the level-0 context so the
        //      solver can reach the infeasibility — BUT still require the
        //      returned core to be a SUBSET of the residual atoms. If the widened
        //      check instead surfaces an unrelated already-recorded conflict
        //      (e.g. a context-only pair `{T29,T30}` that dual-simplex happens to
        //      detect first), its core is NOT ⊆ residual atoms and we reject it —
        //      recording that lemma would not close the residual and would leave
        //      the clause on Trust anyway. Fail-closed: reject, never record the
        //      wrong lemma.
        let atom_set: HashSet<TermId> = atoms.iter().copied().collect();
        let trace = std::env::var("AY_TSEITIN_TRACE").is_ok_and(|v| v == "1");

        // Phase 1: residual atoms alone.
        let mut conflict = self.residual_farkas_over_atoms(&atoms, &[], &atom_set, trace);
        // Phase 2: only if the residual pair alone is not infeasible, widen with
        // the level-0 context but still demand a residual-scoped core.
        if conflict.is_none() && !level0_context.is_empty() {
            conflict = self.residual_farkas_over_atoms(&atoms, level0_context, &atom_set, trace);
        }
        let Some(conflict) = conflict else {
            return false;
        };
        let Some(farkas) = conflict.farkas else {
            // Coefficient overflowed i64 (all_fit=false): no cert -> Trust.
            return false;
        };
        // The certified core must line up 1:1 with the coefficients.
        if conflict.literals.is_empty() || conflict.literals.len() != farkas.coefficients.len() {
            return false;
        }

        // Build the blocking clause from the solver's OWN core, IN ORDER, using
        // `mk_not_raw` for a `true` conflict literal so it matches the negation
        // form `lit_to_term` reproduces (the round-trip guard in level0_rup).
        // A `false` conflict literal (defensive; the pair is asserted true)
        // appears un-negated. Order is preserved to stay aligned with `farkas`.
        let mut clause_terms: Vec<TermId> = Vec::with_capacity(conflict.literals.len());
        for lit in &conflict.literals {
            if lit.value {
                clause_terms.push(self.terms.mk_not_raw(lit.term));
            } else {
                clause_terms.push(lit.term);
            }
        }

        // The conflict came from a genuine `LraSolver` `UnsatWithFarkas`
        // certificate, so it IS a certified arithmetic conflict. Classify is a
        // SHAPE-only pre-check that can under-report (Generic) even for a valid
        // Farkas core (representation mismatch between the fresh solver's core and
        // the classifier). If it does not confirm LraFarkas/LiaGeneric, still
        // record as LraFarkas and let `check_proof_strict`
        // (`validate_lra_farkas` -> `verify_farkas_conflict_lits_full`) be the
        // FINAL arbiter — it independently re-derives the contradiction from the
        // coefficients. FAIL-CLOSED: if the cert is not actually valid, that
        // strict check rejects the whole proof and the clause stays on Trust; no
        // false proof is possible.
        let classified =
            crate::theory_inference::infer_theory_lemma_kind_from_clause_terms_and_farkas(
                &*self.terms,
                &clause_terms,
                Some(&farkas),
            );
        let kind = match classified {
            TheoryLemmaKind::LraFarkas | TheoryLemmaKind::LiaGeneric => classified,
            _ => TheoryLemmaKind::LraFarkas,
        };
        if trace {
            eprintln!(
                "[residual-lemma] RECORDING clause={clause_terms:?} classified={classified:?} as {kind:?}"
            );
        }

        proof.add_theory_lemma_with_farkas_and_kind("lra", clause_terms, farkas, kind);
        true
    }

    /// Drive a fresh `LraSolver` over `atoms` (asserted `= true`) plus optional
    /// `context`, and return the Farkas conflict ONLY when its certified core
    /// (a) mentions EVERY residual atom and (b) is a subset of the residual
    /// atoms plus the context atoms. Condition (a) rejects the shadowing
    /// conflict — an already-recorded context-only pair (e.g. `{T29,T30}`) that
    /// dual-simplex happens to detect first, whose core does not touch the
    /// residual atoms at all; recording it would not close the residual clause.
    /// Condition (b) keeps the recorded lemma over atoms whose level-0 units are
    /// in the RUP version set, so `derive_empty_via_level0_rup` can chain
    /// `[¬residual..,¬ctx..]` against those units to close `[]`. Fail-closed:
    /// any non-`UnsatWithFarkas`, missing certificate, or out-of-scope core
    /// yields `None` and the caller falls back to Trust.
    fn residual_farkas_over_atoms(
        &self,
        atoms: &[TermId],
        context: &[(TermId, bool)],
        atom_set: &HashSet<TermId>,
        trace: bool,
    ) -> Option<ay_core::TheoryConflict> {
        let mut lra = ay_lra::LraSolver::new(&*self.terms);
        lra.set_combined_theory_mode(true);
        for &atom in atoms {
            ay_core::TheorySolver::register_atom(&mut lra, atom);
        }
        for &(ctx_atom, _) in context {
            ay_core::TheorySolver::register_atom(&mut lra, ctx_atom);
        }
        for &atom in atoms {
            ay_core::TheorySolver::assert_literal(&mut lra, atom, true);
        }
        for &(ctx_atom, ctx_val) in context {
            ay_core::TheorySolver::assert_literal(&mut lra, ctx_atom, ctx_val);
        }
        let result = ay_core::TheorySolver::check(&mut lra);
        if trace {
            let kind = match &result {
                ay_core::TheoryResult::UnsatWithFarkas(c) => format!(
                    "UnsatWithFarkas(core={}, farkas={})",
                    c.literals.len(),
                    c.farkas.is_some()
                ),
                ay_core::TheoryResult::Unsat(_) => "Unsat(no-cert)".to_string(),
                ay_core::TheoryResult::Sat => "Sat".to_string(),
                _ => "other".to_string(),
            };
            eprintln!(
                "[residual-lemma] atoms={} context={} -> check={}",
                atoms.len(),
                context.len(),
                kind
            );
        }
        let ay_core::TheoryResult::UnsatWithFarkas(conflict) = result else {
            return None;
        };
        // Residual-scoped core gate. Raw atom (strip `Not`) of each core literal.
        let core_atoms: Vec<TermId> = conflict
            .literals
            .iter()
            .map(|lit| match self.terms.get(lit.term) {
                TermData::Not(inner) => *inner,
                _ => lit.term,
            })
            .collect();
        // (a) The core must mention EVERY residual atom — otherwise it is the
        //     shadowing context-only conflict (e.g. {T29,T30}), which does not
        //     close the residual clause.
        let covers_residual = atom_set.iter().all(|a| core_atoms.contains(a));
        // (b) The core must stay within residual ∪ context, so every recorded
        //     literal has a level-0 unit in the RUP version set to chain against.
        let ctx_atoms: HashSet<TermId> = context.iter().map(|(t, _)| *t).collect();
        let core_in_scope = core_atoms
            .iter()
            .all(|a| atom_set.contains(a) || ctx_atoms.contains(a));
        if !covers_residual || !core_in_scope {
            if trace {
                eprintln!(
                    "[residual-lemma] rejected: covers_residual={covers_residual} \
                     in_scope={core_in_scope} (shadowing/out-of-scope conflict)"
                );
            }
            return None;
        }
        Some(conflict)
    }

    pub(super) fn derive_empty_via_level0_rup(
        &mut self,
        clause_versions: &[SatClauseVersion],
        proof: &mut Proof,
    ) -> Option<ProofId> {
        if clause_versions.is_empty() || clause_versions.len() > MAX_RUP_WIDENING_VERSIONS {
            return None;
        }

        // Map recorded theory lemma clauses to SAT literals (round-trip
        // verified against `lit_to_term`, same contract as the minimized-lemma
        // bridge). Lemmas with unmapped literals are skipped, not guessed.
        let mut atom_to_var: HashMap<TermId, u32> = HashMap::default();
        for (&var, &term) in self.var_to_term.iter() {
            atom_to_var.insert(term, var);
        }
        let lemma_steps: Vec<(ProofId, Vec<TermId>)> = proof
            .steps
            .iter()
            .enumerate()
            .filter_map(|(idx, step)| match step {
                ProofStep::TheoryLemma { clause, .. } if !clause.is_empty() => {
                    Some((ProofId(idx as u32), clause.clone()))
                }
                _ => None,
            })
            .collect();
        if std::env::var("AY_TSEITIN_TRACE").is_ok_and(|v| v == "1") {
            eprintln!(
                "[empty-rup] gathered {} theory-lemma steps; var_to_term {} keys",
                lemma_steps.len(),
                self.var_to_term.len()
            );
            for (_, c) in &lemma_steps {
                eprintln!("[empty-rup]   lemma clause terms: {c:?}");
            }
        }
        // Exclude per-clause Trust fallback versions: replaying through a Trust
        // step would "close" the empty clause via the very unverified step we are
        // trying to replace. Honest closers only (real trace clauses + recorded
        // theory lemmas). #unit-prop.
        let mut versions: Vec<SatClauseVersion> = clause_versions
            .iter()
            .filter(|(_, pid)| {
                !matches!(
                    proof.get_step(*pid),
                    Some(ProofStep::Step {
                        rule: AletheRule::Trust,
                        ..
                    })
                )
            })
            .cloned()
            .collect();
        for (proof_id, clause) in lemma_steps {
            let mut sat_clause: Vec<Literal> = Vec::with_capacity(clause.len());
            let mut mapped = true;
            for &lit_term in &clause {
                let sat_lit = if let Some(&var) = atom_to_var.get(&lit_term) {
                    Literal::positive(Variable::new(var))
                } else if let TermData::Not(inner) = self.terms.get(lit_term) {
                    match atom_to_var.get(inner) {
                        Some(&var) => Literal::negative(Variable::new(var)),
                        None => {
                            mapped = false;
                            break;
                        }
                    }
                } else {
                    mapped = false;
                    break;
                };
                if self.lit_to_term(sat_lit) != Some(lit_term) {
                    mapped = false;
                    break;
                }
                sat_clause.push(sat_lit);
            }
            if mapped {
                versions.push((sat_clause, proof_id));
            }
        }

        if std::env::var("AY_TSEITIN_TRACE").is_ok_and(|v| v == "1") {
            eprintln!(
                "[empty-rup] {} base versions + mapped lemmas = {} total for RUP",
                clause_versions.len(),
                versions.len()
            );
            for (i, (sc, _)) in versions.iter().enumerate() {
                eprintln!("[empty-rup]   version[{i}] sat-lits: {sc:?}");
            }
        }
        let all_versions: Vec<usize> = (0..versions.len()).collect();
        // Fresh engine: `versions` is a filtered/extended copy of the trace
        // clause list, so the incremental process_trace engine's watch
        // indices do not apply.
        let mut engine = RupEngine::default();
        match self.derive_clause_via_rup_replay(
            &[],
            &[],
            &all_versions,
            &versions,
            &mut engine,
            proof,
        ) {
            Ok((proof_id, _, derived_sat)) => {
                debug_assert!(
                    derived_sat.is_empty(),
                    "BUG: empty-target RUP replay returned a non-empty clause"
                );
                derived_sat.is_empty().then_some(proof_id)
            }
            Err(error) => {
                tracing::debug!(
                    ?error,
                    versions = versions.len(),
                    "level-0 RUP empty-clause replay failed; falling back"
                );
                None
            }
        }
    }

    /// Derive the empty clause by bounded DPLL(T) over the processed clause
    /// database, re-deriving MISSING theory-exclusion lemmas at the leaves
    /// (#relu-trust-glue).
    ///
    /// The ReLU-disjunction family (`(or (and ..) (and ..))` case splits over
    /// linear-arithmetic atoms) reaches UNSAT through eagerly-refuted
    /// branches whose exclusion lemmas are never recorded: for every branch
    /// but the last, the theory conflict only steers the search and leaves no
    /// clause in the trace. The recorded clause set is then propositionally
    /// SATISFIABLE, so `derive_empty_via_level0_rup` stalls and no
    /// resolution reconstruction — however clever — can reach `(cl)`; the
    /// proof previously closed with the whole-problem `trust` lemma.
    ///
    /// This closer runs [`Self::dpll_refute`] with NO assumptions (refuting
    /// the database itself). At every propositional stall the LRA oracle
    /// re-certifies the assigned arithmetic literals with a fresh solver;
    /// each `UnsatWithFarkas` core becomes a recorded `la_generic`-printable
    /// `TheoryLemma` leaf that immediately conflicts and is folded into
    /// ordinary `Resolution` steps. The result — when the search closes —
    /// is a proof of `(cl)` whose leaves are the trace's own clauses plus
    /// solver-certified theory lemmas: every step independently checkable.
    ///
    /// Fail-closed: Trust-proved clause versions and trust-kind theory
    /// lemmas are excluded from the search database (the empty clause must
    /// not ride on an unverified step); node/theory-check budget exhaustion,
    /// an un-foldable conflict, or a genuine theory-consistent model rolls
    /// the proof back to the entry snapshot and returns `None` so the honest
    /// fallbacks run unchanged.
    pub(super) fn derive_empty_via_bounded_dpll_theory(
        &mut self,
        clause_versions: &[SatClauseVersion],
        proof: &mut Proof,
    ) -> Option<ProofId> {
        if clause_versions.is_empty() || clause_versions.len() > MAX_RUP_WIDENING_VERSIONS {
            return None;
        }

        // Honest closers only: exclude versions proved by a Trust step.
        let mut versions: Vec<SatClauseVersion> = clause_versions
            .iter()
            .filter(|(_, pid)| {
                !matches!(
                    proof.get_step(*pid),
                    Some(ProofStep::Step {
                        rule: AletheRule::Trust,
                        ..
                    })
                )
            })
            .cloned()
            .collect();

        // Materialize already-recorded NON-trust theory lemmas as search
        // clauses (their proof steps exist; no new steps are added). Same
        // round-trip-verified mapping as `derive_empty_via_level0_rup`.
        let mut atom_to_var: HashMap<TermId, u32> = HashMap::default();
        for (&var, &term) in self.var_to_term.iter() {
            atom_to_var.insert(term, var);
        }
        let lemma_steps: Vec<(ProofId, Vec<TermId>)> = proof
            .steps
            .iter()
            .enumerate()
            .filter_map(|(idx, step)| match step {
                ProofStep::TheoryLemma { clause, kind, .. }
                    if !clause.is_empty() && !kind.is_trust() =>
                {
                    Some((ProofId(idx as u32), clause.clone()))
                }
                _ => None,
            })
            .collect();
        for (proof_id, clause) in lemma_steps {
            let mut sat_clause: Vec<Literal> = Vec::with_capacity(clause.len());
            let mut mapped = true;
            for &lit_term in &clause {
                let sat_lit = if let Some(&var) = atom_to_var.get(&lit_term) {
                    Literal::positive(Variable::new(var))
                } else if let TermData::Not(inner) = self.terms.get(lit_term) {
                    match atom_to_var.get(inner) {
                        Some(&var) => Literal::negative(Variable::new(var)),
                        None => {
                            mapped = false;
                            break;
                        }
                    }
                } else {
                    mapped = false;
                    break;
                };
                if self.lit_to_term(sat_lit) != Some(lit_term) {
                    mapped = false;
                    break;
                }
                sat_clause.push(sat_lit);
            }
            if mapped {
                versions.push((sat_clause, proof_id));
            }
        }

        let steps_snapshot = proof.steps.len();
        let mut engine = RupEngine::default();
        let mut assumps: Vec<Literal> = Vec::new();
        let mut nodes = 0usize;
        let mut theory_checks = 0usize;
        match self.dpll_refute(
            &mut assumps,
            &mut versions,
            &mut engine,
            proof,
            &mut nodes,
            &mut theory_checks,
        ) {
            Some((proof_id, derived_sat)) if derived_sat.is_empty() => {
                tracing::debug!(
                    nodes,
                    theory_checks,
                    "bounded DPLL(T) closed the empty clause with certified theory leaves"
                );
                Some(proof_id)
            }
            _ => {
                // Fail closed: drop every step the search added.
                proof.steps.truncate(steps_snapshot);
                None
            }
        }
    }

    /// Derive a learned clause from its resolution hints.
    ///
    /// Primary strategy (#rank-4 increment 1): RUP/LRAT-style unit-propagation
    /// replay over the *SAT-level* hint clauses — order-insensitive and
    /// complete for any hint set under which the target clause is RUP (this
    /// is exactly the LRAT-check semantics of `ay-sat::lrat_checker`,
    /// extended with fixpoint iteration because trace hints are not
    /// guaranteed to be in propagation order). Falls back to the legacy
    /// left-to-right pairwise term-level resolution (with original-clause
    /// closure) when replay fails.
    ///
    /// The replay runs over raw SAT literals (not SMT terms): distinct SAT
    /// variables can map to identical or complementary terms, which makes
    /// term-level propagation stall on chains that are perfectly valid at
    /// the SAT level (this was the source of the ~10/87 Trust fallbacks on
    /// the rank-4 captured solve).
    ///
    /// On success returns the proof node id *and* the term/SAT clauses that
    /// node actually proves. RUP replay can derive a strict subclause of the
    /// target (a stronger clause); callers must record that subclause so
    /// downstream replays stay exact.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn derive_clause_from_hints(
        &mut self,
        target_clause: &[TermId],
        target_sat_clause: &[Literal],
        resolution_hints: &[u64],
        clause_terms: &HashMap<u64, Vec<TermId>>,
        clause_versions: &[SatClauseVersion],
        latest_version_by_id: &HashMap<u64, usize>,
        clause_proofs: &HashMap<u64, ProofId>,
        engine: &mut RupEngine,
        proof: &mut Proof,
    ) -> Result<(ProofId, Vec<TermId>, Vec<Literal>), HintDerivationError> {
        let mut hint_ids = Vec::with_capacity(resolution_hints.len());
        let mut hint_versions = Vec::with_capacity(resolution_hints.len());
        let mut seen_hint_ids: HashSet<u64> = Default::default();
        for &hint_id in resolution_hints {
            if !seen_hint_ids.insert(hint_id) {
                continue;
            }
            if clause_terms.contains_key(&hint_id) && clause_proofs.contains_key(&hint_id) {
                hint_ids.push(hint_id);
            }
            if let Some(&version) = latest_version_by_id.get(&hint_id) {
                hint_versions.push(version);
            }
        }
        if hint_ids.is_empty() && hint_versions.is_empty() {
            return Err(HintDerivationError::NoUsableHints);
        }

        match self.derive_clause_via_rup_replay(
            target_clause,
            target_sat_clause,
            &hint_versions,
            clause_versions,
            engine,
            proof,
        ) {
            Ok(derived) => return Ok(derived),
            Err(rup_error) => {
                tracing::debug!(
                    ?rup_error,
                    ?target_clause,
                    "RUP hint replay failed; falling back to pairwise resolution"
                );
            }
        }

        if hint_ids.is_empty() {
            return Err(HintDerivationError::NoUsableHints);
        }
        self.derive_clause_via_pairwise_resolution(
            target_clause,
            &hint_ids,
            clause_terms,
            clause_proofs,
            proof,
        )
        .map(|(id, derived_terms)| (id, derived_terms, target_sat_clause.to_vec()))
    }

    /// Unit-propagate over the clause versions named by `candidates` to
    /// fixpoint, mirroring the LRAT-check hint classification
    /// (`ay-sat::lrat_checker`): a clause with all literals falsified is the
    /// conflict (returned); a clause with exactly one non-falsified,
    /// unassigned literal propagates it (recorded in `implications`);
    /// satisfied or 2+-non-falsified clauses are skipped and revisited on the
    /// next pass. Candidates are scanned in reverse order (trace hint chains
    /// are conflict-analysis order: seed conflict first, reasons after, so
    /// the reverse is closest to propagation order; for the widened phase it
    /// scans newest clauses first).
    fn rup_propagate(
        candidates: &[usize],
        clause_versions: &[SatClauseVersion],
        engine: &mut RupEngine,
        implications: &mut Vec<(usize, Literal)>,
        used: &mut HashSet<usize>,
        step_budget: &mut Option<u64>,
    ) -> Option<usize> {
        loop {
            let mut progressed = false;
            for &version in candidates.iter().rev() {
                // Deterministic best-effort budget (#A2b): one step per
                // candidate clause scan. On exhaustion, stall (return no
                // conflict); `process_trace` then abandons reconstruction.
                if let Some(remaining) = step_budget {
                    if *remaining == 0 {
                        return None;
                    }
                    *remaining -= 1;
                }
                if used.contains(&version) {
                    continue;
                }
                let Some((clause, _)) = clause_versions.get(version) else {
                    continue;
                };

                let mut non_falsified = 0u32;
                let mut candidate: Option<Literal> = None;
                let mut satisfied = false;
                for &lit in clause {
                    match engine.value(lit) {
                        Some(false) => {} // falsified
                        Some(true) => {
                            satisfied = true;
                            break;
                        }
                        None => {
                            non_falsified += 1;
                            if non_falsified >= 2 {
                                break;
                            }
                            candidate = Some(lit);
                        }
                    }
                }
                if satisfied || non_falsified >= 2 {
                    continue;
                }
                if non_falsified == 0 {
                    return Some(version);
                }
                // Exactly one unassigned literal: propagate it true.
                let lit = candidate.expect("invariant: one non-falsified literal");
                engine.assign(lit);
                implications.push((version, lit));
                used.insert(version);
                progressed = true;
            }
            if !progressed {
                return None;
            }
        }
    }

    /// RUP/LRAT-style unit-propagation replay (#rank-4 increment 1).
    ///
    /// Semantics mirror `ay-sat::lrat_checker::LratChecker::verify_chain`
    /// (CaDiCaL `lratchecker.cpp` parity), over the raw SAT literals of the
    /// clause trace, with two extensions:
    ///
    /// 1. Hints are propagated to *fixpoint in any order* (the clause-trace
    ///    hint chains are conflict-analysis order, not strict LRAT order).
    /// 2. The implication sequence is recorded and folded into an explicit
    ///    chain of `ProofStep::Resolution` nodes (reverse-chronological trail
    ///    resolution), so the result is an independently checkable resolution
    ///    derivation rather than a yes/no answer.
    ///
    /// Algorithm: assume the negation of every target literal, then repeatedly
    /// scan the hint clauses. A hint with all literals falsified is the
    /// conflict; a hint with exactly one non-falsified (unassigned) literal
    /// propagates it. On conflict, resolve the conflict clause against the
    /// propagating clauses in reverse propagation order. Every literal of the
    /// final resolvent is falsified by the initial assumptions, so the result
    /// is a subclause of the target (and the chain is tautology-free at the
    /// SAT level because all intermediate resolvents are falsified under a
    /// consistent assignment).
    fn derive_clause_via_rup_replay(
        &mut self,
        target_clause: &[TermId],
        target_sat_clause: &[Literal],
        hint_versions: &[usize],
        clause_versions: &[SatClauseVersion],
        engine: &mut RupEngine,
        proof: &mut Proof,
    ) -> Result<(ProofId, Vec<TermId>, Vec<Literal>), HintDerivationError> {
        debug_assert!(engine.trail.is_empty(), "RUP engine not reset");

        // Step 1: assume the negation of each target literal.
        for &lit in target_sat_clause {
            match engine.value(lit) {
                Some(false) => {} // already falsified
                Some(true) => {
                    // Target contains both `l` and `not l`: a tautology is not
                    // RUP-derivable. Let the caller fall back.
                    engine.reset();
                    return Err(HintDerivationError::RupTautologicalTarget);
                }
                None => engine.assign(lit.negated()),
            }
        }

        // Step 2: propagate hint clauses to fixpoint, recording implications.
        // Skipped when the hints already name every version (the level-0
        // empty-clause closer): the widened watched propagation below covers
        // the same clause set without the quadratic rescans.
        let mut implications: Vec<(usize, Literal)> = Vec::new();
        let mut used: HashSet<usize> = Default::default();
        let mut budget = self.step_budget;
        let mut conflict = if hint_versions.len() < clause_versions.len() {
            Self::rup_propagate(
                hint_versions,
                clause_versions,
                engine,
                &mut implications,
                &mut used,
                &mut budget,
            )
        } else {
            None
        };

        // Step 2b: DRUP-style widening. The trace hint chains are sometimes
        // not self-contained RUP certificates: learned-clause minimization
        // and trail filtering can drop reason clauses from the chain, and
        // trace clause ids can collide across id spaces (proof-writer ids vs
        // arena-index fallback), making "the clause for hint N" ambiguous.
        // When hint-only propagation stalls, widen unit propagation to every
        // clause version processed so far. A 1UIP learned clause is always
        // RUP w.r.t. the live clause database at learning time, and
        // `clause_versions` holds a superset of that database. No new axioms
        // are introduced: every version carries an existing proof node.
        // Runs on the amortized two-watched-literal engine (unit propagation
        // is confluent, so it conflicts exactly when the old full rescans
        // did — only the implication order can differ).
        if conflict.is_none() && clause_versions.len() <= MAX_RUP_WIDENING_VERSIONS {
            conflict = engine.propagate(clause_versions, &mut implications, &mut used, &mut budget);
        }
        self.step_budget = budget;
        engine.reset();

        let Some(conflict_version) = conflict else {
            return Err(HintDerivationError::RupNoConflict {
                usable_hint_count: hint_versions.len(),
                propagations: implications.len(),
            });
        };

        // Step 3: fold the implication sequence into a resolution chain at
        // the SAT level, emitting term-level Resolution steps as we go.
        let (conflict_clause, conflict_proof) = clause_versions
            .get(conflict_version)
            .ok_or(HintDerivationError::NoUsableHints)?;
        let mut current_sat = conflict_clause.clone();
        let mut current_terms = self
            .clause_to_terms(&current_sat)
            .ok_or(HintDerivationError::NoUsableHints)?;
        let mut current_proof = *conflict_proof;

        for &(version, lit) in implications.iter().rev() {
            let neg_lit = lit.negated();
            if !current_sat.contains(&neg_lit) {
                continue;
            }
            let Some((reason_clause, reason_proof)) = clause_versions.get(version) else {
                continue;
            };

            // SAT-level resolvent. Dedup via generation marks keeps the
            // exact first-occurrence push order of the `Vec::contains` scan
            // it replaces, without the quadratic rescan (#proof-tax: long
            // implication chains fold clauses that grow with the chain).
            let generation = engine.next_mark_gen();
            let mut resolvent: Vec<Literal> =
                Vec::with_capacity(current_sat.len() + reason_clause.len());
            for &l in current_sat.iter().chain(reason_clause.iter()) {
                if l != neg_lit && l != lit && engine.mark_first(l, generation) {
                    resolvent.push(l);
                }
            }

            // Pivot convention matches resolve_once: the pivot literal as it
            // occurs in the left premise (`current_sat`).
            let pivot_term = self
                .lit_to_term(neg_lit)
                .ok_or(HintDerivationError::NoUsableHints)?;
            let resolvent_terms = self
                .clause_to_terms(&resolvent)
                .ok_or(HintDerivationError::NoUsableHints)?;

            current_proof = proof.add_resolution(
                resolvent_terms.clone(),
                pivot_term,
                current_proof,
                *reason_proof,
            );
            current_sat = resolvent;
            current_terms = resolvent_terms;
        }

        // Step 4: the derived clause must be a subclause of the target (its
        // literals are exactly the assumption-falsified ones). A strict
        // subclause is a stronger result and is returned as-is.
        if current_sat
            .iter()
            .all(|lit| target_sat_clause.contains(lit))
        {
            Ok((current_proof, current_terms, current_sat))
        } else {
            Err(HintDerivationError::FinalClauseMismatch {
                expected_clause: target_clause.to_vec(),
                derived_clause: current_terms,
            })
        }
    }

    /// Legacy left-to-right pairwise resolution over the hint chain, with
    /// original-clause closure (#6365). Retained as a fallback for hint sets
    /// where RUP replay fails (e.g., targets that need clauses outside the
    /// hint list, which `close_clause_via_originals` can reach).
    fn derive_clause_via_pairwise_resolution(
        &mut self,
        target_clause: &[TermId],
        hint_ids: &[u64],
        clause_terms: &HashMap<u64, Vec<TermId>>,
        clause_proofs: &HashMap<u64, ProofId>,
        proof: &mut Proof,
    ) -> Result<(ProofId, Vec<TermId>), HintDerivationError> {
        let (&first_id, rest) = hint_ids
            .split_first()
            .ok_or(HintDerivationError::NoUsableHints)?;
        let Some(first_clause) = clause_terms.get(&first_id) else {
            return Err(HintDerivationError::NoUsableHints);
        };
        let Some(&first_proof) = clause_proofs.get(&first_id) else {
            return Err(HintDerivationError::NoUsableHints);
        };
        let mut current_clause = first_clause.clone();
        let mut current_proof = first_proof;
        let mut resolved_any = false;

        for &hint_id in rest {
            let rhs_clause = match clause_terms.get(&hint_id) {
                Some(clause) => clause,
                None => continue,
            };
            let rhs_proof = match clause_proofs.get(&hint_id).copied() {
                Some(id) => id,
                None => continue,
            };

            let Some((pivot, resolvent)) = self.resolve_once(&current_clause, rhs_clause) else {
                continue;
            };

            current_proof =
                proof.add_resolution(resolvent.clone(), pivot, current_proof, rhs_proof);
            current_clause = resolvent;
            resolved_any = true;
        }

        if !resolved_any {
            if Self::clauses_equivalent(&current_clause, target_clause) {
                return Ok((current_proof, current_clause));
            }
            // Try second-pass closure over existing original clauses before giving up.
            if let Some(closed) = self.close_clause_via_originals(
                current_clause.clone(),
                current_proof,
                target_clause,
                clause_terms,
                clause_proofs,
                proof,
            ) {
                return Ok(closed);
            }
            return Err(HintDerivationError::NoResolutionPivot {
                usable_hint_count: hint_ids.len(),
            });
        }

        if Self::clauses_equivalent(&current_clause, target_clause) {
            return Ok((current_proof, current_clause));
        }

        // Second-pass closure: try resolving with already-emitted original clauses
        // to close the gap between the derived clause and the target (#6365).
        if let Some(closed) = self.close_clause_via_originals(
            current_clause.clone(),
            current_proof,
            target_clause,
            clause_terms,
            clause_proofs,
            proof,
        ) {
            return Ok(closed);
        }

        Err(HintDerivationError::FinalClauseMismatch {
            expected_clause: target_clause.to_vec(),
            derived_clause: current_clause,
        })
    }

    /// Second-pass closure over already-emitted original clauses (#6365).
    ///
    /// When direct hint replay produces a clause that doesn't match the target,
    /// search existing clause/proof pairs for resolution candidates that bring
    /// the current clause strictly closer to the target. Only uses clauses that
    /// already have proof IDs — no new axioms are synthesized.
    ///
    /// Progress metric: each resolution step must strictly reduce the number of
    /// literals in the current clause that are absent from the target clause.
    /// This guarantees termination and soundness.
    pub(super) fn close_clause_via_originals(
        &mut self,
        mut current_clause: Vec<TermId>,
        mut current_proof: ProofId,
        target_clause: &[TermId],
        clause_terms: &HashMap<u64, Vec<TermId>>,
        clause_proofs: &HashMap<u64, ProofId>,
        proof: &mut Proof,
    ) -> Option<(ProofId, Vec<TermId>)> {
        let target_set: HashSet<TermId> = target_clause.iter().copied().collect();

        // Collect candidate clause IDs to avoid borrowing conflicts.
        let candidate_ids: Vec<u64> = clause_proofs.keys().copied().collect();

        let mismatch_count = |clause: &[TermId], target: &HashSet<TermId>| -> usize {
            clause.iter().filter(|lit| !target.contains(*lit)).count()
        };

        let mut current_mismatch = mismatch_count(&current_clause, &target_set);

        // Bounded iteration: at most one resolution step per round, restart
        // scan after each successful resolution. Progress is strictly monotone
        // (mismatch count must decrease), guaranteeing termination.
        const MAX_CLOSURE_ROUNDS: usize = 32;
        for _ in 0..MAX_CLOSURE_ROUNDS {
            if current_mismatch == 0 {
                break;
            }

            let mut made_progress = false;
            for &cid in &candidate_ids {
                // Deterministic best-effort budget (#A2b construction): one
                // step per candidate resolution attempt. Each attempt costs a
                // `resolve_once` scan (term negation + interning), and the
                // candidate set is the whole clause database — unbudgeted
                // this loop is superquadratic (QF_ALIA pp-dmem2: 93% of a
                // 25s+ default-mode wall after a 2s verdict). On exhaustion,
                // fail closed: `process_trace` aborts and the run degrades to
                // the honest "no proof certificate emitted" warning.
                if let Some(remaining) = &mut self.step_budget {
                    if *remaining == 0 {
                        return None;
                    }
                    *remaining -= 1;
                }
                let Some(rhs_clause) = clause_terms.get(&cid) else {
                    continue;
                };
                let Some(&rhs_proof) = clause_proofs.get(&cid) else {
                    continue;
                };

                let Some((pivot, resolvent)) = self.resolve_once(&current_clause, rhs_clause)
                else {
                    continue;
                };

                let new_mismatch = mismatch_count(&resolvent, &target_set);
                if new_mismatch < current_mismatch {
                    current_proof =
                        proof.add_resolution(resolvent.clone(), pivot, current_proof, rhs_proof);
                    current_clause = resolvent;
                    current_mismatch = new_mismatch;
                    made_progress = true;
                    break; // restart scan with the new clause
                }
            }

            if !made_progress {
                break;
            }
        }

        Self::clauses_equivalent(&current_clause, target_clause)
            .then_some((current_proof, current_clause))
    }

    pub(super) fn derive_empty_from_units(
        &mut self,
        clause_terms: &HashMap<u64, Vec<TermId>>,
        clause_proofs: &HashMap<u64, ProofId>,
        proof: &mut Proof,
    ) -> Option<ProofId> {
        let mut unit_map: HashMap<TermId, ProofId> = HashMap::default();
        for (&clause_id, clause) in clause_terms {
            if clause.len() != 1 {
                continue;
            }
            let lit = clause[0];
            let Some(&lit_proof) = clause_proofs.get(&clause_id) else {
                continue;
            };
            let neg_lit = self.negate_term(lit);
            if let Some(&neg_proof) = unit_map.get(&neg_lit) {
                return Some(proof.add_resolution(Vec::new(), lit, lit_proof, neg_proof));
            }
            unit_map.insert(lit, lit_proof);
        }

        None
    }

    pub(super) fn derive_empty_from_assumptions(&mut self, proof: &mut Proof) -> Option<ProofId> {
        let assumptions: Vec<(ProofId, TermId)> = proof
            .steps
            .iter()
            .enumerate()
            .filter_map(|(idx, step)| match step {
                ProofStep::Assume(term) => Some((ProofId(idx as u32), *term)),
                _ => None,
            })
            .collect();

        let mut seen: HashMap<TermId, ProofId> = HashMap::default();
        for (id, term) in assumptions {
            let neg_term = self.negate_term(term);
            if let Some(&neg_id) = seen.get(&neg_term) {
                return Some(proof.add_resolution(Vec::new(), term, id, neg_id));
            }
            seen.insert(term, id);
        }

        None
    }
}
