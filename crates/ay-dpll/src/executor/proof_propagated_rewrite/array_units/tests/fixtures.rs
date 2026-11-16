// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(in crate::executor::proof_propagated_rewrite::array_units) struct Fixture {
    pub(in crate::executor::proof_propagated_rewrite::array_units) exec: Executor,
    pub(in crate::executor::proof_propagated_rewrite::array_units) roots: Vec<TermId>,
    pub(in crate::executor::proof_propagated_rewrite::array_units) term: TermId,
    pub(in crate::executor::proof_propagated_rewrite::array_units) variable: TermId,
    pub(in crate::executor::proof_propagated_rewrite::array_units) value: TermId,
}

impl Fixture {
    pub(in crate::executor::proof_propagated_rewrite::array_units) fn new() -> Self {
        let mut exec = Executor::new();
        let terms = &mut exec.ctx.terms;
        let guard = terms.mk_var("guard", Sort::Bool);
        let variable = terms.mk_var("variable", Sort::bitvec(129));
        let value = terms.mk_var("value", Sort::bitvec(129));
        let term = terms.mk_app(Symbol::named("="), [variable, value], Sort::Bool);
        let not_guard = terms.mk_not_raw(guard);
        let source = terms.mk_app(Symbol::named("or"), [not_guard, term], Sort::Bool);
        let roots = vec![guard, source];
        let mut proof = Proof::new();
        let activation = proof.add_assume(guard, None);
        let source_id = proof.add_assume(source, None);
        let clause = proof.add_rule_step(
            AletheRule::Or,
            vec![not_guard, term],
            vec![source_id],
            Vec::new(),
        );
        let conclusion = proof.add_resolution(vec![term], guard, clause, activation);
        let unit = ArrayUnitDerivation::checked(
            terms,
            &roots,
            Arc::new(proof),
            conclusion,
            term,
            &mut |_, _| true,
        )
        .expect("original guarded unit with an asserted activation");
        exec.propagated_value_provenance.array_units.push(unit);
        Self {
            exec,
            roots,
            term,
            variable,
            value,
        }
    }
}

pub(super) fn authenticate(
    terms: &TermStore,
    roots: &[TermId],
    proof: &Proof,
) -> ay_proof::AuthenticatedPremiseClauses {
    ay_proof::authenticate_premise_clauses_strict_with_context_and_progress(
        proof,
        terms,
        None,
        None,
        roots,
        &mut |_, _| true,
    )
    .expect("all replayed steps check against actual original roots")
}
