// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Complementary and linear conjunction-collapse repair.

use super::*;

impl Executor {
    /// `(and .. p .. (not p) ..)` with a syntactically complementary conjunct
    /// pair: two `and_pos` extractions resolved to the empty clause.
    pub(super) fn rebuild_complementary_and_collapse(
        &mut self,
        proof: &mut Proof,
        authored_root: TermId,
        surface_arity: usize,
    ) -> bool {
        // The assumption authority is the immutable, index-aligned problem
        // root. Never rebuild this premise by elaborating the parsed operands:
        // comparison normalization can turn an authored
        // `(and (not (> x 10)) (> x 10))` into the derived
        // `(and (not (< 10 x)) (< 10 x))`, which is equivalent but is not an
        // asserted formula. Parsed syntax is used only to verify the arity.
        let x = authored_root;
        if !matches!(
            self.ctx.terms.get(x),
            TermData::App(Symbol::Named(op), a) if op == "and" && a.len() == surface_arity
        ) {
            return false;
        }
        // Collect every Bool node reachable through the `and`-tree of `x`,
        // recording the path (child indices) from the root. The complementary
        // pair need NOT be two top-level conjuncts: a conjunct may itself be a
        // nested `(and ..)`, so a literal `p` can sit one or more levels deep
        // while its complement `(not p)` is a sibling conjunct (the class
        // `(and .. (and .. p) .. (not p) ..)`). Each node's unit is derived by
        // the strictly-validated `and_pos` + resolution chain down its path.
        let mut nodes: Vec<(TermId, Vec<u32>)> = Vec::new();
        {
            let mut stack: Vec<(TermId, Vec<u32>)> = vec![(x, Vec::new())];
            while let Some((t, path)) = stack.pop() {
                if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(t) {
                    if name == "and" && !args.is_empty() {
                        let args = args.clone();
                        // Reverse push keeps the pop order left-to-right.
                        for (i, &child) in args.iter().enumerate().rev() {
                            let Ok(pos) = u32::try_from(i) else { continue };
                            let mut cp = path.clone();
                            cp.push(pos);
                            stack.push((child, cp));
                        }
                        continue;
                    }
                }
                if matches!(self.ctx.terms.sort(t), Sort::Bool) {
                    nodes.push((t, path));
                }
            }
        }
        // First-occurrence path per node (shortest is fine; any valid
        // extraction closes the proof). A node reachable only as the root `x`
        // itself is never recorded (the root is an `and`, descended above).
        let mut node_path: HashMap<TermId, Vec<u32>> = HashMap::default();
        for (t, p) in &nodes {
            node_path.entry(*t).or_insert_with(|| p.clone());
        }
        // Find a complementary pair `p` / `(not p)` where both are reachable.
        let Some((pos_term, neg_term)) = nodes.iter().find_map(|(t, _)| {
            let TermData::Not(inner) = self.ctx.terms.get(*t) else {
                return None;
            };
            let inner = *inner;
            node_path.contains_key(&inner).then_some((inner, *t))
        }) else {
            return false;
        };
        let pos_path = node_path[&pos_term].clone();
        let neg_path = node_path[&neg_term].clone();

        let mut new_proof = Proof::new();
        let assume_id = new_proof.add_assume(x, None);
        let (Some(pos_unit), Some(neg_unit)) = (
            Self::emit_and_pos_chain(
                &mut self.ctx.terms,
                &mut new_proof,
                assume_id,
                x,
                &pos_path,
                pos_term,
            ),
            Self::emit_and_pos_chain(
                &mut self.ctx.terms,
                &mut new_proof,
                assume_id,
                x,
                &neg_path,
                neg_term,
            ),
        ) else {
            return false;
        };
        new_proof.add_resolution(Vec::new(), pos_term, neg_unit, pos_unit);
        if !matches!(
            ay_proof::check_proof_strict(&new_proof, &self.ctx.terms),
            Ok(quality) if quality.trust_count == 0
        ) || ay_proof::validate_reachable_assumes_in_problem_scope(&new_proof, &[authored_root])
            .is_err()
        {
            return false;
        }
        *proof = new_proof;
        true
    }

    /// `(and c1 .. cn)` of pure linear-arithmetic atoms whose conjunction is
    /// arithmetically infeasible (the CAV09 fold-to-false family): synthesize
    /// a Farkas certificate over the POSITIVE pure-linear conjuncts with the
    /// LRA solver, keep only the conjuncts carrying a NONZERO coefficient
    /// (the certificate identifies exactly the participating atoms, so large
    /// conjunctions do not degenerate into one `and_pos` per conjunct),
    /// independently re-verify the pruned certificate at external
    /// `la_generic` strength plus a printable equality-sign orientation, and
    /// derive `and_pos` extraction + one `la_generic` lemma + resolutions to
    /// the empty clause. Fail-closed: negated/impure/duplicated conjuncts
    /// never enter the candidate set, and any failed synthesis or
    /// re-verification keeps the proof byte-identical.
    pub(super) fn rebuild_linear_and_collapse(
        &mut self,
        proof: &mut Proof,
        operands: &[FrontendTerm],
    ) -> bool {
        let mut conjs = Vec::with_capacity(operands.len());
        for op in operands {
            let Some(t) = self.raw_intern_surface(op) else {
                return false;
            };
            conjs.push(t);
        }
        // Re-intern the folded conjunction RAW (see the distinct emitter).
        let x = self
            .ctx
            .terms
            .mk_app(Symbol::named("and"), conjs.clone(), Sort::Bool);
        if !matches!(
            self.ctx.terms.get(x),
            TermData::App(Symbol::Named(op), a) if op == "and" && a.len() == conjs.len()
        ) {
            return false;
        }
        // Candidate conjuncts: POSITIVE pure linear-arithmetic atoms, first
        // occurrence only (a duplicated conjunct would double-count its
        // coefficient position; the first extraction suffices).
        let mut cand: Vec<usize> = Vec::new();
        for (i, &c) in conjs.iter().enumerate() {
            let pure = match self.ctx.terms.get(c) {
                TermData::App(Symbol::Named(op), args) if args.len() == 2 => match op.as_str() {
                    "<=" | "<" | ">=" | ">" => args
                        .iter()
                        .all(|&a| term_is_pure_linear_arith(&self.ctx.terms, a)),
                    "=" => equality_is_pure_linear_arith(&self.ctx.terms, c),
                    _ => false,
                },
                _ => false,
            };
            if pure && !conjs[..i].contains(&c) {
                cand.push(i);
            }
        }
        if cand.is_empty() {
            return false;
        }
        // Synthesize the certificate: assert ALL candidates into a fresh LRA
        // solver; the returned conflict names exactly the participating
        // atoms with their coefficients (so large conjunctions do not
        // degenerate into one `and_pos` per conjunct).
        let mut lra = ay_lra::LraSolver::new(&self.ctx.terms);
        lra.set_combined_theory_mode(true);
        for &i in &cand {
            ay_core::TheorySolver::register_atom(&mut lra, conjs[i]);
        }
        for &i in &cand {
            ay_core::TheorySolver::assert_literal(&mut lra, conjs[i], true);
        }
        let (lits, all) = match ay_core::TheorySolver::check(&mut lra) {
            ay_core::TheoryResult::UnsatWithFarkas(conflict) => {
                let lits = conflict.literals;
                match conflict.farkas {
                    Some(f) if f.coefficients.len() == lits.len() => (lits, f),
                    // No (or misaligned) certificate metadata: fall back to
                    // the all-ones candidate, judged solely by the
                    // independent re-verification below.
                    _ => {
                        let ones = FarkasAnnotation::from_ints(&vec![1i64; lits.len()]);
                        (lits, ones)
                    }
                }
            }
            // A conflict without Farkas metadata (e.g. a single conjunct
            // whose linear form cancels to `0 <= -1`): all-ones candidate,
            // fail-closed on the re-verification below.
            ay_core::TheoryResult::Unsat(lits) => {
                let ones = FarkasAnnotation::from_ints(&vec![1i64; lits.len()]);
                (lits, ones)
            }
            _ => return false,
        };
        if lits.is_empty() {
            return false;
        }
        // Map the conflict literals back to conjunct positions, dropping
        // zero-coefficient entries. Fail-closed on any literal that is not a
        // positively-asserted candidate conjunct (or appears twice).
        let mut sel: Vec<usize> = Vec::new();
        let mut coeffs = Vec::new();
        for (lit, coef) in lits.iter().zip(all.coefficients.iter()) {
            if num_traits::Zero::is_zero(coef) {
                continue;
            }
            if !lit.value {
                return false;
            }
            let Some(&i) = cand.iter().find(|&&i| conjs[i] == lit.term) else {
                return false;
            };
            if sel.contains(&i) {
                return false;
            }
            sel.push(i);
            coeffs.push(*coef);
        }
        // Deterministic conjunct order for stable printing.
        let mut order: Vec<usize> = (0..sel.len()).collect();
        order.sort_by_key(|&k| sel[k]);
        let sel: Vec<usize> = order.iter().map(|&k| sel[k]).collect();
        let coeffs: Vec<_> = order.iter().map(|&k| coeffs[k]).collect();
        if sel.is_empty() {
            return false;
        }
        let farkas = FarkasAnnotation::new(coeffs);
        let sel_conjs: Vec<TermId> = sel.iter().map(|&i| conjs[i]).collect();
        // Independent re-verification at external `la_generic` strength
        // (no congruence), plus the printable sign orientation (fail-closed).
        let conflict: Vec<TheoryLit> = sel_conjs.iter().map(|&c| TheoryLit::new(c, true)).collect();
        if ay_core::proof_validation::verify_farkas_conflict_lits_linear(
            &self.ctx.terms,
            &conflict,
            &farkas,
        )
        .is_err()
        {
            return false;
        }
        if ay_core::proof_validation::resolve_equality_coefficient_signs(
            &self.ctx.terms,
            &conflict,
            &farkas,
        )
        .is_none()
        {
            return false;
        }
        let terms = &mut self.ctx.terms;
        let not_x = terms.mk_not_raw(x);
        let clause: Vec<TermId> = sel_conjs.iter().map(|&c| terms.mk_not_raw(c)).collect();
        let mut new_proof = Proof::new();
        let assume_id = new_proof.add_assume(x, None);
        let mut units: Vec<ProofId> = Vec::with_capacity(sel.len());
        for (&i, &c) in sel.iter().zip(sel_conjs.iter()) {
            #[allow(clippy::cast_possible_truncation)]
            let ap = new_proof.add_rule_step(
                AletheRule::AndPos(i as u32),
                vec![not_x, c],
                Vec::new(),
                Vec::new(),
            );
            units.push(new_proof.add_resolution(vec![c], x, ap, assume_id));
        }
        let lemma = new_proof.add_step(ProofStep::TheoryLemma {
            theory: "LRA".to_string(),
            clause: clause.clone(),
            farkas: Some(farkas),
            kind: TheoryLemmaKind::LraFarkas,
            lia: None,
        });
        let mut current = lemma;
        for (k, (&c, &uid)) in sel_conjs.iter().zip(units.iter()).enumerate() {
            current = new_proof.add_resolution(clause[k + 1..].to_vec(), c, current, uid);
        }
        *proof = new_proof;
        // `x` is recursively raw-interned from the parsed conjunction above,
        // and the independently checked Farkas rebuild has now succeeded.
        // Record that exact source term so the final exporter accepts the
        // rebuilt Assume without granting authority to any generated leaf.
        self.record_rebuilt_authored_proof_premise(x);
        true
    }
}
