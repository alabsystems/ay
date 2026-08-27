// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// The ARRAY half of the rewritten-assertion bridge's hypothesis pool.
//
// `include!`d into `rewritten_assertion_bridge.rs` — one module, two files, so
// each stays inside the repository's per-file line ceiling.
//
// # The class this serves, as measured
//
// the development design notes measured the
// residual the congruence bridge leaves: 97 premiseless, argument-free `trust`
// steps whose clause is a unit `(= a b)`, of which 58 are an authored assertion
// after an ARRAY fold the congruence forest has no node for. Those 58 split
// cleanly: 20 need READ-OVER-WRITE at an equal index and 38 need
// STORE-OVER-STORE; none needs both. This lane closes the first 20, measured
// 20 -> 0, and leaves the other 38 byte-identical.
//
// `mk_select` folds the node away while `VariableSubstitution` is inlining:
//
// ```text
// authored   (assert (= a_260 (store a_258 i0 e_259)))
// authored   (assert (= e_261 (select a_260 i0)))
// asserted   (= e_261 e_259)
// ```
//
// Offering `(= (select (store a_258 i0 e_259) i0) e_259)` as a hypothesis
// re-creates exactly that node, and the closure then reaches the goal with no
// array knowledge of its own.

impl Executor {
    /// Offer the READ-OVER-WRITE axiom instances of the terms already in play.
    ///
    /// # Why this is not an assumption
    ///
    /// Every entry is `(= (select (store a i v) i) v)` with ONE index term used
    /// as both the store index and the read index. That is the ROW1 axiom at a
    /// syntactically identical index: a ground validity of the theory of
    /// arrays with no side condition, and in particular NOT the different-index
    /// instance, which would need a disequality this lane never has.
    /// `ay_proof::plan_row1_axiom_instances` mints only that shape and keeps an
    /// instance only when the checker's OWN `recognize_array_select_store`
    /// answers `Some(true)` for the unit clause, so the leaf is one the
    /// mandatory strict gate re-derives from the clause alone.
    ///
    /// Guard 3 is untouched: an axiom instance is never an `assume`, so it can
    /// never widen the assumption scope. An instance that collides with a term
    /// already in the pool KEEPS that term's stronger leaf.
    fn extend_pool_with_row1_axioms(
        &mut self,
        pool: &mut Vec<TermId>,
        leaf_of: &mut DetHashMap<TermId, HypothesisLeaf>,
        leaves: &[(usize, TermId)],
    ) {
        // The roots are the pool the bridge already has plus the leaves it is
        // trying to derive: the store terms that can possibly matter are the
        // ones those terms mention.
        let mut roots: Vec<TermId> = pool.clone();
        roots.extend(leaves.iter().map(|&(_, atom)| atom));
        let instances = ay_proof::plan_row1_axiom_instances(&mut self.ctx.terms, &roots);
        for equality in instances {
            if pool.len() >= ay_proof::MAX_BRIDGE_CANDIDATES {
                return;
            }
            if leaf_of.contains_key(&equality) {
                continue;
            }
            // Guard 7: the REAL validator, not a recognizer, decides. The
            // instance is closed into a self-contained refutation and replayed
            // by the untouched `check_proof_strict`; only an instance that
            // survives that may ever be cited.
            if !self.row1_axiom_leaf_strict_checks(equality) {
                continue;
            }
            leaf_of.insert(equality, HypothesisLeaf::ArrayRowAxiom);
            pool.push(equality);
        }
    }

    /// Offer the STORE-OVER-STORE axiom instances of the terms already in play.
    ///
    /// # Why this is not an assumption
    ///
    /// Every entry is `(= (store (store B i u) i v) (store B i v))` with ONE
    /// index term written by all three stores. That is a ground validity of the
    /// theory of arrays with extensionality: the two sides agree at `i` (both
    /// `v`) and at every other index (both `select(B, ·)`), with no side
    /// condition of any kind. In particular this lane can never mint the
    /// DIFFERENT-index instance, which is not valid at all, because the index
    /// it writes into the folded store IS the outer store's own index term.
    /// `ay_proof::plan_store_overwrite_instances` mints only that shape and
    /// keeps an instance only when the checker's OWN
    /// `recognize_array_theory_lemma` answers `ArrayRowChain` for the unit
    /// clause, so the leaf is one the mandatory strict gate re-derives from the
    /// clause alone.
    ///
    /// Guard 3 is untouched: an axiom instance is never an `assume`, so it can
    /// never widen the assumption scope. An instance that collides with a term
    /// already in the pool KEEPS that term's stronger leaf.
    fn extend_pool_with_store_overwrite_axioms(
        &mut self,
        pool: &mut Vec<TermId>,
        leaf_of: &mut DetHashMap<TermId, HypothesisLeaf>,
        leaves: &[(usize, TermId)],
    ) {
        // The DEFINITIONS are the pool the bridge already has: only an authored
        // equality naming a `store` can tell the walk which fold to bridge.
        // The ROOTS additionally carry the leaves the lane is trying to derive,
        // because their stores supply the written values.
        let definitions: Vec<TermId> = pool.clone();
        let mut roots: Vec<TermId> = pool.clone();
        roots.extend(leaves.iter().map(|&(_, atom)| atom));
        let instances =
            ay_proof::plan_store_overwrite_instances(&mut self.ctx.terms, &definitions, &roots);
        for equality in instances {
            if pool.len() >= ay_proof::MAX_BRIDGE_CANDIDATES {
                return;
            }
            if leaf_of.contains_key(&equality) {
                continue;
            }
            // Guard 7: the REAL validator, not a recognizer, decides. The
            // instance is closed into a self-contained refutation and replayed
            // by the untouched `check_proof_strict`; only an instance that
            // survives that may ever be cited.
            if !self.store_overwrite_axiom_leaf_strict_checks(equality) {
                continue;
            }
            leaf_of.insert(equality, HypothesisLeaf::ArrayStoreOverwrite);
            pool.push(equality);
        }
    }

    /// Guard 7 for the store-over-store leaf: whether the `ArrayRowChain` leaf
    /// for `equality` is replayed by the UNTOUCHED strict checker.
    fn store_overwrite_axiom_leaf_strict_checks(&mut self, equality: TermId) -> bool {
        let negated = self.ctx.terms.mk_not(equality);
        if !matches!(self.ctx.terms.get(negated), TermData::Not(inner) if *inner == equality) {
            return false;
        }
        let mut probe = Proof::new();
        probe.steps.push(ProofStep::TheoryLemma {
            theory: "ArrayEUF".to_string(),
            clause: vec![equality],
            farkas: None,
            kind: ay_core::TheoryLemmaKind::ArrayRowChain,
            lia: None,
        });
        probe.steps.push(ProofStep::Assume(negated));
        probe.steps.push(ProofStep::Step {
            rule: AletheRule::Resolution,
            clause: Vec::new(),
            premises: vec![ProofId(0), ProofId(1)],
            args: Vec::new(),
        });
        ay_proof::check_proof_strict(&probe, &self.ctx.terms).is_ok()
    }

    /// Guard 7: whether the `ArraySelectStore { index_eq: true }` leaf for
    /// `equality` is replayed by the UNTOUCHED strict checker.
    ///
    /// The leaf is closed over the negation of its own unit clause, so the
    /// checker sees a complete refutation and has to run the array-axiom
    /// validator to accept it. Nothing about the instance is taken on the
    /// producer's word.
    fn row1_axiom_leaf_strict_checks(&mut self, equality: TermId) -> bool {
        let negated = self.ctx.terms.mk_not(equality);
        if !matches!(self.ctx.terms.get(negated), TermData::Not(inner) if *inner == equality) {
            return false;
        }
        let mut probe = Proof::new();
        probe.steps.push(ProofStep::TheoryLemma {
            theory: "ArrayEUF".to_string(),
            clause: vec![equality],
            farkas: None,
            kind: ay_core::TheoryLemmaKind::ArraySelectStore { index_eq: true },
            lia: None,
        });
        probe.steps.push(ProofStep::Assume(negated));
        probe.steps.push(ProofStep::Step {
            rule: AletheRule::Resolution,
            clause: Vec::new(),
            premises: vec![ProofId(0), ProofId(1)],
            args: Vec::new(),
        });
        ay_proof::check_proof_strict(&probe, &self.ctx.terms).is_ok()
    }
}
