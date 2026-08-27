// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// ===========================================================================
// Promotion of an injected extensionality axiom whose witness reads a LATER
// preprocessing pass folded away (#folded-ext-by-pair).
//
// `generated_clause_bindings` is keyed by the exact clause TERM, recorded when
// the generator mints it. The eager BV/array lane then re-runs
// `expand_select_store_all_adaptive` over the whole assertion stack, so the
// clause that reaches the proof is the FOLD of the recorded one and the exact
// lookup misses — leaving the axiom as a premiseless `trust` step whose clause
// is not a theorem. These tests pin the pair-keyed recovery and, for every way
// it can be wrong, that the step is left exactly as it was.
// ===========================================================================

/// A RAW `(= a b)`. `mk_eq` DISTRIBUTES over an `ite`, turning
/// `(= (select a k) (ite c v r))` into `(ite c (= .. v) (= .. r))` — a
/// formula-level shape the rewrite that produces these clauses never emits.
/// `expand_select_store` rebuilds the equality with a bare `intern`, so the
/// fixture must too, or it would be testing a clause the producer cannot make.
fn raw_eq(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), vec![lhs, rhs], Sort::Bool)
}

/// A RAW `(or a b)`: `mk_or` sorts and dedups its arguments.
fn raw_or(terms: &mut TermStore, lits: Vec<TermId>) -> TermId {
    terms.mk_app(Symbol::named("or"), lits, Sort::Bool)
}

/// `(not (= a b))` as the problem, a minted witness for the pair, and the RAW
/// axiom clause recorded at the generation site — but NOT the folded one.
struct FoldedPairFixture {
    exec: Executor,
    a: TermId,
    chain: TermId,
    k: TermId,
    base: TermId,
    write_index: TermId,
    value: TermId,
    not_eq_ab: TermId,
}

impl FoldedPairFixture {
    fn new() -> Self {
        let mut exec = Executor::new();
        let array_sort = Sort::array(Sort::Int, Sort::Int);
        let a = exec.ctx.terms.mk_var("folded_a", array_sort.clone());
        let base = exec.ctx.terms.mk_var("folded_base", array_sort);
        let write_index = exec.ctx.terms.mk_var("folded_i", Sort::Int);
        let value = exec.ctx.terms.mk_var("folded_v", Sort::Int);
        let chain = exec.ctx.terms.mk_store(base, write_index, value);
        let minted = array_extensionality_witness(
            &mut exec.ctx.terms,
            &mut exec.array_ext_witness_cache,
            a,
            chain,
        );
        assert!(minted.is_some(), "fixture must mint an active witness");
        let k = match minted {
            Some(k) => k,
            None => a,
        };

        // The generation site records the RAW clause, with both reads unfolded.
        let eq_ab = raw_eq(&mut exec.ctx.terms, a, chain);
        let raw_sel_a = exec.ctx.terms.mk_select(a, k);
        let raw_sel_b = exec.ctx.terms.mk_select(chain, k);
        let raw_sel_eq = raw_eq(&mut exec.ctx.terms, raw_sel_a, raw_sel_b);
        let raw_not_sel_eq = exec.ctx.terms.mk_not(raw_sel_eq);
        let raw_axiom = raw_or(&mut exec.ctx.terms, vec![eq_ab, raw_not_sel_eq]);
        assert!(exec.array_ext_witness_cache.record_generated_clause(
            &exec.ctx.terms,
            raw_axiom,
            vec![ArrayExtWitnessBinding {
                witness: k,
                array_a: a,
                array_b: chain,
            }],
        ));

        let not_eq_ab = exec.ctx.terms.mk_not(eq_ab);
        exec.ctx
            .add_assertion_with_parsed(not_eq_ab, parsed_placeholder());
        Self {
            exec,
            a,
            chain,
            k,
            base,
            write_index,
            value,
            not_eq_ab,
        }
    }

    /// The value side `expand_select_over_store` produces for the chain:
    /// `ite((= i k), v, (select base k))`.
    fn folded_value(&mut self) -> TermId {
        let condition = self.exec.ctx.terms.mk_eq(self.write_index, self.k);
        let base_read = self.exec.ctx.terms.mk_select(self.base, self.k);
        self.exec.ctx.terms.mk_ite(condition, self.value, base_read)
    }

    /// `(or (= a C) (not (= (select a k) folded)))`, installed in the assertion
    /// stack and in a proof as the `trust` theory lemma the pipeline leaves.
    fn folded_axiom(&mut self, folded: TermId) -> (TermId, Proof) {
        let eq_ab = raw_eq(&mut self.exec.ctx.terms, self.a, self.chain);
        let sel_a = self.exec.ctx.terms.mk_select(self.a, self.k);
        let sel_eq = raw_eq(&mut self.exec.ctx.terms, sel_a, folded);
        let not_sel_eq = self.exec.ctx.terms.mk_not(sel_eq);
        let axiom = raw_or(&mut self.exec.ctx.terms, vec![eq_ab, not_sel_eq]);
        self.exec.ctx.assertions.push(axiom);
        let mut proof = Proof::new();
        proof.add_assume(self.not_eq_ab, None);
        proof.add_theory_lemma("array", vec![axiom]);
        // The exact-clause record is the thing that is MISSING; without that
        // this fixture would be testing the old arm.
        assert!(
            self.exec
                .array_ext_witness_cache
                .generated_clause_bindings(&self.exec.ctx.terms, axiom)
                .is_none(),
            "the folded clause must NOT be recorded, or the old arm is under test"
        );
        (axiom, proof)
    }
}

fn promoted_extensionality_count(proof: &Proof) -> usize {
    proof
        .steps
        .iter()
        .filter(|step| {
            matches!(
                step,
                ProofStep::TheoryLemma {
                    kind: TheoryLemmaKind::ArrayExtensionality,
                    ..
                }
            )
        })
        .count()
}

fn trust_lemma_count(proof: &Proof) -> usize {
    proof
        .steps
        .iter()
        .filter(|step| matches!(step, ProofStep::TheoryLemma { kind, .. } if kind.is_trust()))
        .count()
}

#[test]
fn a_folded_axiom_the_cache_never_saw_is_promoted_through_its_pair() {
    let mut f = FoldedPairFixture::new();
    let folded = f.folded_value();
    let (_axiom, mut proof) = f.folded_axiom(folded);
    f.exec.promote_array_extensionality_axioms(&mut proof);

    assert_eq!(
        promoted_extensionality_count(&proof),
        1,
        "the folded axiom must be promoted through the pair-keyed witness"
    );
    assert_eq!(trust_lemma_count(&proof), 0);
    let intro = proof
        .steps
        .iter()
        .find_map(|step| match step {
            ProofStep::Step {
                rule: AletheRule::ArrayExtDiffIntro,
                args,
                ..
            } => Some(args.clone()),
            _ => None,
        })
        .expect("promotion must append a witness introduction");
    assert_eq!(intro, vec![f.k, f.a, f.chain]);
    assert!(
        f.exec.unsat_proof_extensionality_certified(&proof),
        "the promoted folded axiom must survive the whole-proof provenance check"
    );
}

#[test]
fn a_folded_axiom_for_a_pair_with_no_minted_witness_stays_a_trust_lemma() {
    // Same clause shape, but the witness in it was minted for a DIFFERENT pair,
    // so the pair lookup finds nothing for `(a, other)`.
    let mut f = FoldedPairFixture::new();
    let folded = f.folded_value();
    let other = f
        .exec
        .ctx
        .terms
        .mk_var("folded_other", Sort::array(Sort::Int, Sort::Int));
    let eq_other = raw_eq(&mut f.exec.ctx.terms, f.a, other);
    let sel_a = f.exec.ctx.terms.mk_select(f.a, f.k);
    let sel_eq = raw_eq(&mut f.exec.ctx.terms, sel_a, folded);
    let not_sel_eq = f.exec.ctx.terms.mk_not(sel_eq);
    let axiom = raw_or(&mut f.exec.ctx.terms, vec![eq_other, not_sel_eq]);
    let mut proof = Proof::new();
    proof.add_assume(f.not_eq_ab, None);
    proof.add_theory_lemma("array", vec![axiom]);
    f.exec.promote_array_extensionality_axioms(&mut proof);

    assert_eq!(promoted_extensionality_count(&proof), 0);
    assert_eq!(
        trust_lemma_count(&proof),
        1,
        "a pair with no generation-site witness must leave the step untouched"
    );
}

#[test]
fn a_folded_axiom_whose_fold_names_the_wrong_value_stays_a_trust_lemma() {
    // The pair DOES have a minted witness, so only the independent fold
    // re-derivation can refuse this: the `then` branch names a value the chain
    // never writes.
    let mut f = FoldedPairFixture::new();
    let wrong = f.exec.ctx.terms.mk_var("folded_wrong", Sort::Int);
    let condition = f.exec.ctx.terms.mk_eq(f.write_index, f.k);
    let base_read = f.exec.ctx.terms.mk_select(f.base, f.k);
    let folded = f.exec.ctx.terms.mk_ite(condition, wrong, base_read);
    let (_axiom, mut proof) = f.folded_axiom(folded);
    f.exec.promote_array_extensionality_axioms(&mut proof);

    assert_eq!(promoted_extensionality_count(&proof), 0);
    assert_eq!(
        trust_lemma_count(&proof),
        1,
        "a fold that does not denote the read must leave the step untouched"
    );
}

#[test]
fn a_folded_axiom_whose_guard_tests_an_unrelated_index_stays_a_trust_lemma() {
    let mut f = FoldedPairFixture::new();
    let other_index = f.exec.ctx.terms.mk_var("folded_j", Sort::Int);
    let condition = f.exec.ctx.terms.mk_eq(other_index, f.k);
    let base_read = f.exec.ctx.terms.mk_select(f.base, f.k);
    let folded = f.exec.ctx.terms.mk_ite(condition, f.value, base_read);
    let (_axiom, mut proof) = f.folded_axiom(folded);
    f.exec.promote_array_extensionality_axioms(&mut proof);

    assert_eq!(promoted_extensionality_count(&proof), 0);
    assert_eq!(trust_lemma_count(&proof), 1);
}

#[test]
fn a_folded_axiom_whose_witness_was_retired_stays_a_trust_lemma() {
    // `begin_public_solve` retires the query's witnesses. A witness from a
    // PREVIOUS public query carries no authority in this one, and the pair
    // lookup must not resurrect it.
    let mut f = FoldedPairFixture::new();
    let folded = f.folded_value();
    let (_axiom, mut proof) = f.folded_axiom(folded);
    f.exec
        .array_ext_witness_cache
        .begin_public_solve(&f.exec.ctx.terms);
    f.exec.promote_array_extensionality_axioms(&mut proof);

    assert_eq!(promoted_extensionality_count(&proof), 0);
    assert_eq!(
        trust_lemma_count(&proof),
        1,
        "a retired witness must not license a promotion in a later query"
    );
}

#[test]
fn the_mirror_polarity_is_not_promoted() {
    // `(not (= a C)) ∨ (= (select a k) folded)` is the OTHER direction — a
    // theory-valid chain-read lemma that belongs to `ArrayRowChain`, not to the
    // authority-bearing extensionality schema. Promoting it would attach a
    // witness introduction to a clause that does not need one.
    let mut f = FoldedPairFixture::new();
    let folded = f.folded_value();
    let eq_ab = raw_eq(&mut f.exec.ctx.terms, f.a, f.chain);
    let not_eq_ab = f.exec.ctx.terms.mk_not(eq_ab);
    let sel_a = f.exec.ctx.terms.mk_select(f.a, f.k);
    let sel_eq = raw_eq(&mut f.exec.ctx.terms, sel_a, folded);
    let axiom = raw_or(&mut f.exec.ctx.terms, vec![not_eq_ab, sel_eq]);
    let mut proof = Proof::new();
    proof.add_assume(f.not_eq_ab, None);
    proof.add_theory_lemma("array", vec![axiom]);
    f.exec.promote_array_extensionality_axioms(&mut proof);

    assert_eq!(promoted_extensionality_count(&proof), 0);
    assert_eq!(trust_lemma_count(&proof), 1);
}

#[test]
fn a_three_literal_clause_is_not_promoted() {
    // The one-level schema has exactly two literals. A third literal makes the
    // clause a different (weaker) claim, and the pair-keyed arm must not treat
    // it as the axiom.
    let mut f = FoldedPairFixture::new();
    let folded = f.folded_value();
    let eq_ab = raw_eq(&mut f.exec.ctx.terms, f.a, f.chain);
    let sel_a = f.exec.ctx.terms.mk_select(f.a, f.k);
    let sel_eq = raw_eq(&mut f.exec.ctx.terms, sel_a, folded);
    let not_sel_eq = f.exec.ctx.terms.mk_not(sel_eq);
    let padding = f.exec.ctx.terms.mk_var("folded_pad", Sort::Bool);
    let axiom = raw_or(&mut f.exec.ctx.terms, vec![eq_ab, not_sel_eq, padding]);
    let mut proof = Proof::new();
    proof.add_assume(f.not_eq_ab, None);
    proof.add_theory_lemma("array", vec![axiom]);
    f.exec.promote_array_extensionality_axioms(&mut proof);

    assert_eq!(promoted_extensionality_count(&proof), 0);
    assert_eq!(trust_lemma_count(&proof), 1);
}
