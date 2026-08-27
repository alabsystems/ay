// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Certified transitivity-tautology recognition and emission.

use super::*;

type TautologyPlan = Option<OrTautologyPlan>;

impl Executor {
    /// True when a `trust`-kind leaf is NOT this pass's business because a
    /// LATER, idempotent export stage certifies it in place.
    ///
    /// Deliberately restricted to the ARRAY backbone, which is the class this
    /// exists for: an array refutation's ROW / extensionality leaves are still
    /// `Generic` at surface-rewrite time and are certified afterwards, and
    /// before this arm a single such leaf vetoed the repair of every genuinely
    /// defective leaf sharing the proof with it. Two downstream stages:
    ///
    /// * `promote_generic_theory_lemma_kinds_after_rewrite` re-tags a `Generic`
    ///   theory lemma whose clause matches an exact array schema
    ///   (read-over-write, row chain, store permutation) — recognized here by
    ///   the checker's OWN matcher, `ay_proof::recognize_array_theory_lemma`,
    ///   which is what that stage consults;
    /// * `promote_array_extensionality_axioms` promotes a recorded Skolemized
    ///   extensionality claim to `ArrayExtensionality` plus its witness
    ///   provenance step.
    ///
    /// Everything else — the arithmetic, string, regex and datatype funnels —
    /// stays a defect: those stages are conditional on certificate synthesis
    /// or independent re-verification succeeding, and predicting them here
    /// would let this pass pre-empt the later rebuild backbones with an
    /// unproved leaf. A `Step`-form trust leaf is never waved through either;
    /// neither stage touches that shape.
    ///
    /// This is a PREDICTION about a later stage, so it is never the last word:
    /// the acceptance gate re-validates the whole rebuilt proof with those
    /// stages actually applied.
    pub(super) fn trust_leaf_certified_downstream(
        &self,
        step: &ProofStep,
        clause: &[TermId],
    ) -> bool {
        let ProofStep::TheoryLemma { kind, .. } = step else {
            return false;
        };
        if !kind.is_trust() {
            return false;
        }
        if ay_proof::recognize_array_theory_lemma(&self.ctx.terms, clause)
            .is_some_and(|inferred| !inferred.is_trust())
        {
            return true;
        }
        let [unit] = clause else {
            return false;
        };
        self.recorded_array_extensionality_chain(*unit).is_some()
    }

    /// Recognize a preprocessor-derived unit `(cl T)` as an EUF-transitivity
    /// TAUTOLOGY (see [`OrTautologyPlan`]): `T` is an `or`-term with exactly
    /// one positive binary-equality disjunct `E`, implied by the remaining
    /// disjuncts via equality transitivity. Two recognized shapes, both
    /// verified with the same all-edges-used chain check the strict
    /// `eq_transitive` checker enforces (never emit what a checker rejects):
    ///
    /// - **Plain**: every other disjunct is `(not (= s t))` and the
    ///   equalities chain from `E`'s lhs to `E`'s rhs.
    /// - **De Morgan (eq_diamond family)**: some other disjunct is
    ///   `(and D1 .. Dm)` with each `Dj = (or (not (= ..)) ..)` chaining to
    ///   `E` on its own (the unused sibling disjuncts of `T` are simply
    ///   never eliminated — the derivation reaches the `T` literal without
    ///   them).
    pub(super) fn plan_or_transitivity_tautology(&mut self, clause: &[TermId]) -> TautologyPlan {
        if clause.len() != 1 {
            return None;
        }
        let term = clause[0];
        let terms = &self.ctx.terms;
        let TermData::App(Symbol::Named(op), disjuncts) = terms.get(term) else {
            return None;
        };
        if op != "or"
            || disjuncts.len() < 2
            || disjuncts.len() > taut_surface::MAX_EMITTED_CLAUSE_WIDTH
        {
            return None;
        }
        let disjuncts = disjuncts.clone();
        let decode_eq = |terms: &ay_core::TermStore, t: TermId| -> Option<(TermId, TermId)> {
            match terms.get(t) {
                TermData::App(Symbol::Named(n), args) if n == "=" && args.len() == 2 => {
                    Some((args[0], args[1]))
                }
                _ => None,
            }
        };
        // Exactly one POSITIVE disjunct, and it must be a binary equality
        // (any additional positive disjunct could never be eliminated by the
        // derivation, and an ambiguous `E` is rejected outright).
        let mut eq_pos: Option<usize> = None;
        for (i, &d) in disjuncts.iter().enumerate() {
            if !matches!(terms.get(d), TermData::Not(_)) {
                if decode_eq(terms, d).is_none()
                    && !matches!(terms.get(d), TermData::App(s, _) if s.name() == "and")
                {
                    return None;
                }
                if decode_eq(terms, d).is_some() {
                    if eq_pos.is_some() {
                        return None;
                    }
                    eq_pos = Some(i);
                }
            }
        }
        let eq_pos = eq_pos?;
        let eq = disjuncts[eq_pos];
        let (lhs, rhs) = decode_eq(terms, eq)?;
        // Collect a disjunct list as negated-equality edges; `None` when any
        // entry is not `(not (= s t))`.
        let neg_edges =
            |terms: &ay_core::TermStore, lits: &[TermId]| -> Option<Vec<(TermId, TermId)>> {
                let mut edges = Vec::with_capacity(lits.len());
                for &l in lits {
                    let TermData::Not(inner) = terms.get(l) else {
                        return None;
                    };
                    edges.push(decode_eq(terms, *inner)?);
                }
                Some(edges)
            };
        // Route 1: every other disjunct is a negated equality and the whole
        // set chains lhs -> rhs.
        let others: Vec<TermId> = disjuncts
            .iter()
            .enumerate()
            .filter(|&(i, _)| i != eq_pos)
            .map(|(_, &d)| d)
            .collect();
        if let Some(edges) = neg_edges(terms, &others) {
            if Self::transitivity_chain_covers(&edges, lhs, rhs) {
                return Some(OrTautologyPlan {
                    term,
                    eq,
                    route: TautRoute::Plain { negs: others },
                });
            }
            return None;
        }
        // Route 2: an `and`-disjunct whose every conjunct is an or-term of
        // negated equalities chaining lhs -> rhs.
        'cand: for &d in &others {
            let TermData::App(Symbol::Named(n), conjs) = terms.get(d) else {
                continue;
            };
            if n != "and"
                || conjs.is_empty()
                || conjs.len() > taut_surface::MAX_EMITTED_CLAUSE_WIDTH
            {
                continue;
            }
            let conjs = conjs.clone();
            let mut per_conj_negs: Vec<Vec<TermId>> = Vec::with_capacity(conjs.len());
            for &c in &conjs {
                let TermData::App(Symbol::Named(cn), lits) = terms.get(c) else {
                    continue 'cand;
                };
                if cn != "or"
                    || lits.is_empty()
                    || lits.len() > taut_surface::MAX_EMITTED_CLAUSE_WIDTH
                {
                    continue 'cand;
                }
                let lits = lits.clone();
                let Some(edges) = neg_edges(terms, &lits) else {
                    continue 'cand;
                };
                if !Self::transitivity_chain_covers(&edges, lhs, rhs) {
                    continue 'cand;
                }
                per_conj_negs.push(lits);
            }
            return Some(OrTautologyPlan {
                term,
                eq,
                route: TautRoute::And {
                    and_term: d,
                    conjs,
                    per_conj_negs,
                },
            });
        }
        None
    }

    /// Whether `edges` (undirected equalities) form a path from `lhs` to
    /// `rhs` that uses EVERY edge — exactly the strict `eq_transitive`
    /// checker's acceptance condition (BFS shortest path covering all
    /// premises; a redundant premise is rejected there and so must be
    /// rejected here).
    fn transitivity_chain_covers(edges: &[(TermId, TermId)], lhs: TermId, rhs: TermId) -> bool {
        if edges.is_empty() || lhs == rhs {
            return false;
        }
        let mut adj: HashMap<TermId, Vec<TermId>> = HashMap::default();
        for &(a, b) in edges {
            adj.entry(a).or_default().push(b);
            adj.entry(b).or_default().push(a);
        }
        let mut parent: HashMap<TermId, TermId> = HashMap::default();
        parent.insert(lhs, lhs);
        let mut queue = std::collections::VecDeque::new();
        queue.push_back(lhs);
        while let Some(cur) = queue.pop_front() {
            if cur == rhs {
                break;
            }
            if let Some(next) = adj.get(&cur) {
                for &n in next {
                    if !parent.contains_key(&n) {
                        parent.insert(n, cur);
                        queue.push_back(n);
                    }
                }
            }
        }
        if !parent.contains_key(&rhs) {
            return false;
        }
        let mut path_len = 0usize;
        let mut cur = rhs;
        while cur != lhs {
            cur = parent[&cur];
            path_len += 1;
        }
        path_len == edges.len()
    }

    /// Emit the certified derivation of `(cl T)` for a recognized
    /// transitivity tautology (see [`OrTautologyPlan`]; the plan was
    /// chain-verified, so every emitted step passes the strict checker).
    /// Returns the id of the final unit step.
    pub(super) fn emit_or_tautology_derivation(
        &mut self,
        new_proof: &mut Proof,
        plan: &OrTautologyPlan,
    ) -> ProofId {
        let (t, e) = (plan.term, plan.eq);
        // Derive `(cl E <target>)` from `negs` (the ¬e literals whose
        // equalities chain to E) against the or-term `target` that lists
        // them as disjuncts: eq_transitive + one or_neg elimination per ¬e,
        // then contraction of the accumulated duplicate `target` literals.
        let derive_eq_or = |exec: &mut Self,
                            new_proof: &mut Proof,
                            negs: &[TermId],
                            target: TermId|
         -> ProofId {
            let mut clause: Vec<TermId> = negs.to_vec();
            clause.push(e);
            let mut cur = new_proof.add_rule_step(
                AletheRule::EqTransitive,
                clause.clone(),
                Vec::new(),
                Vec::new(),
            );
            for &d in negs {
                let not_d = exec.ctx.terms.mk_not_raw(d);
                let on = new_proof.add_rule_step(
                    AletheRule::OrNeg,
                    vec![target, not_d],
                    Vec::new(),
                    Vec::new(),
                );
                if let Some(pos) = clause.iter().position(|&l| l == d) {
                    // Resolution surgery: the removed literal is the pivot `d`,
                    // already in hand — its id is not needed.
                    let _ = clause.remove(pos);
                }
                clause.push(target);
                cur = new_proof.add_resolution(clause.clone(), d, cur, on);
            }
            if negs.len() > 1 {
                clause = vec![e, target];
                cur =
                    new_proof.add_rule_step(AletheRule::Contraction, clause, vec![cur], Vec::new());
            }
            cur
        };
        // `(cl E X)` where X is the disjunct of T the outer wiring
        // eliminates (T itself on the Plain route, the and-term on the De
        // Morgan route).
        let (eq_x_unit, x) = match &plan.route {
            TautRoute::Plain { negs } => (derive_eq_or(self, new_proof, negs, t), t),
            TautRoute::And {
                and_term,
                conjs,
                per_conj_negs,
            } => {
                let (and_term, conjs) = (*and_term, conjs.clone());
                let units: Vec<ProofId> = conjs
                    .iter()
                    .zip(per_conj_negs.iter())
                    .map(|(&dj, negs)| derive_eq_or(self, new_proof, negs, dj))
                    .collect();
                let mut clause: Vec<TermId> = vec![and_term];
                for &c in &conjs {
                    clause.push(self.ctx.terms.mk_not_raw(c));
                }
                let mut cur = new_proof.add_rule_step(
                    AletheRule::AndNeg,
                    clause.clone(),
                    Vec::new(),
                    Vec::new(),
                );
                for (&dj, &unit) in conjs.iter().zip(units.iter()) {
                    let not_dj = self.ctx.terms.mk_not_raw(dj);
                    if let Some(pos) = clause.iter().position(|&l| l == not_dj) {
                        // Resolution surgery: the removed literal is `not_dj`,
                        // already in hand — its id is not needed.
                        let _ = clause.remove(pos);
                    }
                    clause.push(e);
                    cur = new_proof.add_resolution(clause.clone(), dj, cur, unit);
                }
                if conjs.len() > 1 {
                    clause = vec![and_term, e];
                    cur = new_proof.add_rule_step(
                        AletheRule::Contraction,
                        clause,
                        vec![cur],
                        Vec::new(),
                    );
                }
                (cur, and_term)
            }
        };
        // Outer wiring: `(cl T (not X))` and `(cl T (not E))` or_neg
        // tautologies eliminate X and E, contraction closes `(cl T)`.
        let mut cur = eq_x_unit;
        if x != t {
            let not_x = self.ctx.terms.mk_not_raw(x);
            let on_x =
                new_proof.add_rule_step(AletheRule::OrNeg, vec![t, not_x], Vec::new(), Vec::new());
            cur = new_proof.add_resolution(vec![e, t], x, cur, on_x);
        }
        let not_e = self.ctx.terms.mk_not_raw(e);
        let on_e =
            new_proof.add_rule_step(AletheRule::OrNeg, vec![t, not_e], Vec::new(), Vec::new());
        cur = new_proof.add_resolution(vec![t, t], e, cur, on_e);
        new_proof.add_rule_step(AletheRule::Contraction, vec![t], vec![cur], Vec::new())
    }
}
