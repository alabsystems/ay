// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Executor {
    /// Rebuild `s = "literal"` plus `str.len(s) = wrong` from exact authored
    /// roots using congruence, the independently checked constant-length
    /// theorem, equality transitivity, and a constant-arithmetic conflict.
    pub(super) fn replace_with_exact_authored_string_length_refutation(
        &mut self,
        proof: &mut Proof,
    ) {
        if self.check_proof_strict_with_datatypes(proof).is_ok() {
            return;
        }
        let authored = self.exact_concrete_authored_scope();
        for &binding_root in &authored {
            let Some((binding_left, binding_right)) =
                decode_eq_local(&self.ctx.terms, binding_root)
            else {
                continue;
            };
            let (string_term, literal_term, literal) = match (
                self.ctx.terms.get(binding_left),
                self.ctx.terms.get(binding_right),
            ) {
                (TermData::Const(Constant::String(literal)), _) => {
                    (binding_right, binding_left, literal.clone())
                }
                (_, TermData::Const(Constant::String(literal))) => {
                    (binding_left, binding_right, literal.clone())
                }
                _ => continue,
            };
            if self.ctx.terms.sort(string_term) != &Sort::String {
                continue;
            }

            for &length_root in &authored {
                if length_root == binding_root {
                    continue;
                }
                let Some((length_left, length_right)) =
                    decode_eq_local(&self.ctx.terms, length_root)
                else {
                    continue;
                };
                let mut matched = None;
                for (length_side, value_side) in
                    [(length_left, length_right), (length_right, length_left)]
                {
                    let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(length_side)
                    else {
                        continue;
                    };
                    if name == "str.len"
                        && args.as_slice() == [string_term]
                        && matches!(
                            self.ctx.terms.get(value_side),
                            TermData::Const(Constant::Int(_))
                        )
                    {
                        matched = Some((length_side, value_side));
                        break;
                    }
                }
                let Some((length_of_string, claimed_length)) = matched else {
                    continue;
                };

                let actual_length = self.ctx.terms.mk_int(BigInt::from(literal.chars().count()));
                if claimed_length == actual_length {
                    continue;
                }
                let length_of_literal =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("str.len"), [literal_term], Sort::Int);
                let congruence_equality = self.ctx.terms.mk_app(
                    Symbol::named("="),
                    [length_of_string, length_of_literal],
                    Sort::Bool,
                );
                let constant_length_equality = self.ctx.terms.mk_app(
                    Symbol::named("="),
                    [length_of_literal, actual_length],
                    Sort::Bool,
                );
                if !ay_proof::recognize_string_length_lemma(
                    &self.ctx.terms,
                    &[constant_length_equality],
                ) {
                    continue;
                }
                let derived_length_equality = self.ctx.terms.mk_app(
                    Symbol::named("="),
                    [length_of_string, actual_length],
                    Sort::Bool,
                );
                let impossible_constant_equality = self.ctx.terms.mk_app(
                    Symbol::named("="),
                    [claimed_length, actual_length],
                    Sort::Bool,
                );
                let impossible_constant_disequality =
                    self.ctx.terms.mk_not_raw(impossible_constant_equality);
                if !ay_core::proof_validation::recognize_lia_divisibility(
                    &self.ctx.terms,
                    &[impossible_constant_disequality],
                ) {
                    continue;
                }

                let mut candidate = Proof::new();
                let binding = candidate.add_assume(binding_root, None);
                let not_binding = self.ctx.terms.mk_not_raw(binding_root);
                let congruence = candidate.add_rule_step(
                    AletheRule::EqCongruent,
                    vec![not_binding, congruence_equality],
                    Vec::new(),
                    Vec::new(),
                );
                let congruence_unit = candidate.add_resolution(
                    vec![congruence_equality],
                    binding_root,
                    congruence,
                    binding,
                );
                let constant_length = candidate.add_theory_lemma_with_kind(
                    "strings",
                    vec![constant_length_equality],
                    TheoryLemmaKind::StringLengthLemma,
                );
                let first_transitivity = candidate.add_rule_step(
                    AletheRule::EqTransitive,
                    vec![
                        self.ctx.terms.mk_not_raw(congruence_equality),
                        self.ctx.terms.mk_not_raw(constant_length_equality),
                        derived_length_equality,
                    ],
                    Vec::new(),
                    Vec::new(),
                );
                let first_residual = candidate.add_resolution(
                    vec![
                        self.ctx.terms.mk_not_raw(constant_length_equality),
                        derived_length_equality,
                    ],
                    congruence_equality,
                    first_transitivity,
                    congruence_unit,
                );
                let derived_length = candidate.add_resolution(
                    vec![derived_length_equality],
                    constant_length_equality,
                    first_residual,
                    constant_length,
                );
                let authored_length = candidate.add_assume(length_root, None);
                let second_transitivity = candidate.add_rule_step(
                    AletheRule::EqTransitive,
                    vec![
                        self.ctx.terms.mk_not_raw(length_root),
                        self.ctx.terms.mk_not_raw(derived_length_equality),
                        impossible_constant_equality,
                    ],
                    Vec::new(),
                    Vec::new(),
                );
                let second_residual = candidate.add_resolution(
                    vec![
                        self.ctx.terms.mk_not_raw(derived_length_equality),
                        impossible_constant_equality,
                    ],
                    length_root,
                    second_transitivity,
                    authored_length,
                );
                let impossible_constant = candidate.add_resolution(
                    vec![impossible_constant_equality],
                    derived_length_equality,
                    second_residual,
                    derived_length,
                );
                let arithmetic_conflict = candidate.add_step(ProofStep::TheoryLemma {
                    theory: "LIA".to_string(),
                    clause: vec![impossible_constant_disequality],
                    farkas: Some(FarkasAnnotation::new(vec![num_rational::Rational64::from(
                        1,
                    )])),
                    kind: TheoryLemmaKind::LiaGeneric,
                    lia: Some(ay_core::LiaAnnotation::Divisibility),
                });
                candidate.add_resolution(
                    Vec::new(),
                    impossible_constant_equality,
                    impossible_constant,
                    arithmetic_conflict,
                );

                if ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, &authored)
                    .is_ok()
                    && Self::proof_derives_empty_clause(&candidate)
                    && self.check_proof_strict_with_datatypes(&candidate).is_ok()
                {
                    *proof = candidate;
                    return;
                }
            }
        }
    }
}
