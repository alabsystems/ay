// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Admission checks for post-restoration quantified-model confirmation.

use super::{contains_quantifier, quantified_gate_model_independent, Executor, TermData, TermId};

impl Executor {
    /// Admit the historical vacuous-binder case or a model-independent
    /// existential prefix whose matrix is quantifier-free. The latter lets the
    /// ordinary checked ground witness solve certify a closed arithmetic
    /// existential after generated CEGQI assertions made generic validation
    /// inconclusive.
    pub(super) fn quantified_gate_restoration_candidate(&mut self, conjunct: TermId) -> bool {
        if self.quantified_gate_drop_vacuous_binders(conjunct) != conjunct {
            return true;
        }
        if !quantified_gate_model_independent(&self.ctx.terms, conjunct) {
            return false;
        }

        let mut cur = conjunct;
        let mut positive = true;
        let mut universal = None;
        let mut binder_count = 0usize;
        loop {
            let (class, vars, body) = match self.ctx.terms.get(cur).clone() {
                TermData::Not(inner) => {
                    positive = !positive;
                    cur = inner;
                    continue;
                }
                TermData::Forall(vars, body, _) => (positive, vars, body),
                TermData::Exists(vars, body, _) => (!positive, vars, body),
                _ => break,
            };
            if universal.is_some_and(|prior| prior != class) {
                return false;
            }
            universal = Some(class);
            binder_count = binder_count.saturating_add(vars.len());
            cur = body;
        }
        binder_count > 0 && universal == Some(false) && !contains_quantifier(&self.ctx.terms, cur)
    }
}

#[cfg(test)]
mod tests {
    use ay_core::{Sort, Symbol};

    use super::Executor;

    #[test]
    fn restoration_admits_only_closed_qf_existential_prefixes() {
        let mut executor = Executor::new();
        let x = executor.ctx.terms.mk_var("x", Sort::Int);
        let zero = executor.ctx.terms.mk_int(0.into());
        let body = executor
            .ctx
            .terms
            .mk_app(Symbol::named("="), [x, zero], Sort::Bool);
        let existential = executor
            .ctx
            .terms
            .mk_exists(vec![("x".to_string(), Sort::Int)], body);
        assert!(executor.quantified_gate_restoration_candidate(existential));

        let universal = executor
            .ctx
            .terms
            .mk_forall(vec![("x".to_string(), Sort::Int)], body);
        assert!(!executor.quantified_gate_restoration_candidate(universal));

        let free = executor.ctx.terms.mk_var("c", Sort::Int);
        let model_dependent = executor
            .ctx
            .terms
            .mk_app(Symbol::named("="), [x, free], Sort::Bool);
        let model_dependent = executor
            .ctx
            .terms
            .mk_exists(vec![("x".to_string(), Sort::Int)], model_dependent);
        assert!(!executor.quantified_gate_restoration_candidate(model_dependent));

        let y = executor.ctx.terms.mk_var("y", Sort::Int);
        let mixed_body = executor
            .ctx
            .terms
            .mk_app(Symbol::named("="), [x, y], Sort::Bool);
        let alternation = executor
            .ctx
            .terms
            .mk_forall(vec![("y".to_string(), Sort::Int)], mixed_body);
        let alternation = executor
            .ctx
            .terms
            .mk_exists(vec![("x".to_string(), Sort::Int)], alternation);
        assert!(!executor.quantified_gate_restoration_candidate(alternation));
    }
}
