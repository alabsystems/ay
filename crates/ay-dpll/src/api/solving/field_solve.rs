// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Owned conjunction decision using the existing sparse field engine.
//! Candidates supply neither verdict nor model authority: SAT replays authored
//! roots in the independent model kernel; UNSAT reconstructs a native theorem.
use super::tactic_model::TacticModelConverter;
use super::tactics::TacticFailure;
use ay_core::kani_compat::DetHashSet;
use ay_core::term::{
    reserve_counted, CountedBuiltin, CountedTermBuilder, TermConstructionAdmission,
};
use ay_core::{
    Constant, Proof, ProofStep, Sort, Symbol, TermData, TermId, TermStore, TheoryLemmaKind,
};

fn failed() -> TacticFailure {
    TacticFailure::new("ff-solve original admission or typed witness refused")
}
struct Borrowed<'a>(&'a dyn TermConstructionAdmission);
impl TermConstructionAdmission for Borrowed<'_> {
    fn admit(
        &self,
        work: usize,
        bytes: usize,
    ) -> Result<(), ay_core::original_query::CountedAdmissionError> {
        self.0.admit(work, bytes)
    }
    fn refuse(
        &self,
        error: ay_core::original_query::CountedAdmissionError,
    ) -> ay_core::original_query::CountedAdmissionError {
        self.0.refuse(error)
    }
}

fn copy<T: Copy>(
    input: &[T],
    owner: &dyn TermConstructionAdmission,
) -> Result<Vec<T>, TacticFailure> {
    owner.admit(input.len(), 0).map_err(|_| failed())?;
    let mut out = Vec::new();
    reserve_counted(&mut out, input.len(), owner).map_err(|_| failed())?;
    out.extend_from_slice(input);
    Ok(out)
}

// Validate the actual named vocabulary and typed DAG before the algebra parser
// sees it. No uninterpreted/indexed alias or malformed source gains arithmetic
// semantics through a coincidentally equal printed name.
pub(super) fn source(
    terms: &TermStore,
    roots: &[TermId],
    owner: &dyn TermConstructionAdmission,
) -> Result<Option<DetHashSet<TermId>>, TacticFailure> {
    let mut seen = Vec::new();
    reserve_counted(&mut seen, terms.len(), owner).map_err(|_| failed())?;
    owner.admit(terms.len(), 0).map_err(|_| failed())?;
    seen.resize(terms.len(), false);
    let mut stack = copy(roots, owner)?;
    let mut active = Vec::new();
    for &root in roots {
        owner.admit(1, 0).map_err(|_| failed())?;
        if root.index() >= terms.len() || terms.sort(root) != &Sort::Bool {
            return Err(failed());
        }
    }
    while let Some(id) = stack.pop() {
        owner.admit(1, 0).map_err(|_| failed())?;
        if id.index() >= terms.len() {
            return Err(failed());
        }
        if seen[id.index()] {
            continue;
        }
        seen[id.index()] = true;
        reserve_counted(&mut active, 1, owner).map_err(|_| failed())?;
        active.push(id);
        let children = match terms.get(id) {
            TermData::Const(Constant::Bool(_)) if terms.sort(id) == &Sort::Bool => &[][..],
            TermData::Const(Constant::FiniteField { value, field })
                if *value < field.modulus() && terms.sort(id) == &Sort::FiniteField(*field) =>
            {
                &[]
            }
            TermData::Var(..) if matches!(terms.sort(id), Sort::FiniteField(_)) => &[],
            TermData::Not(child) if terms.sort(id) == &Sort::Bool => std::slice::from_ref(child),
            TermData::App(Symbol::Named(name), args) => {
                owner
                    .admit(args.len().checked_add(name.len()).ok_or_else(failed)?, 0)
                    .map_err(|_| failed())?;
                if terms.is_declared_function(name) {
                    return Ok(None);
                }
                if args.iter().any(|child| child.index() >= id.index()) {
                    return Err(failed());
                }
                let valid = match name.as_str() {
                    "and" if terms.sort(id) == &Sort::Bool => {
                        args.iter().all(|child| terms.sort(*child) == &Sort::Bool)
                    }
                    "not" if terms.sort(id) == &Sort::Bool && args.len() == 1 => {
                        terms.sort(args[0]) == &Sort::Bool
                    }
                    "=" | "distinct" if terms.sort(id) == &Sort::Bool && args.len() >= 2 => {
                        matches!(terms.sort(args[0]), Sort::FiniteField(_))
                            && args
                                .iter()
                                .all(|child| terms.sort(*child) == terms.sort(args[0]))
                    }
                    "ff.neg" if args.len() == 1 => {
                        matches!(terms.sort(id), Sort::FiniteField(_))
                            && terms.sort(args[0]) == terms.sort(id)
                    }
                    "ff.add" | "ff.mul" | "ff.bitsum" if args.len() >= 2 => {
                        matches!(terms.sort(id), Sort::FiniteField(_))
                            && args
                                .iter()
                                .all(|child| terms.sort(*child) == terms.sort(id))
                    }
                    _ => false,
                };
                if !valid {
                    return Ok(None);
                }
                args.as_slice()
            }
            _ => return Ok(None),
        };
        reserve_counted(&mut stack, children.len(), owner).map_err(|_| failed())?;
        for &child in children {
            owner.admit(1, 0).map_err(|_| failed())?;
            if child.index() >= id.index() {
                return Err(failed());
            }
            if matches!(terms.get(id), TermData::Not(..)) && terms.sort(child) != &Sort::Bool {
                return Err(failed());
            }
            stack.push(child);
        }
    }
    let storage = active
        .len()
        .checked_mul(std::mem::size_of::<TermId>())
        .and_then(|n| n.checked_mul(8))
        .and_then(|n| n.checked_add(4096))
        .ok_or_else(failed)?;
    owner.admit(active.len(), storage).map_err(|_| failed())?;
    let mut result = DetHashSet::default();
    result.try_reserve(active.len()).map_err(|_| failed())?;
    for id in active {
        owner.admit(1, 0).map_err(|_| failed())?;
        result.insert(id);
    }
    Ok(Some(result))
}

pub(super) fn independent_refutation(
    terms: &mut TermStore,
    roots: &[TermId],
    owner: &dyn TermConstructionAdmission,
) -> Result<bool, TacticFailure> {
    let borrowed = Borrowed(owner);
    let mut clause = Vec::new();
    reserve_counted(&mut clause, roots.len(), owner).map_err(|_| failed())?;
    {
        let mut builder =
            CountedTermBuilder::with_admission(terms, &borrowed).map_err(|_| failed())?;
        for &root in roots {
            owner.admit(1, 0).map_err(|_| failed())?;
            clause.push(
                builder
                    .apply(CountedBuiltin::Not, &[root])
                    .map_err(|_| failed())?,
            );
        }
    }
    let mut remaining = copy(&clause, owner)?;
    let mut proof = Proof::new();
    let steps = roots
        .len()
        .checked_mul(2)
        .and_then(|n| n.checked_add(1))
        .ok_or_else(failed)?;
    if u32::try_from(steps).is_err() {
        return Ok(false);
    }
    reserve_counted(&mut proof.steps, steps, owner).map_err(|_| failed())?;
    owner
        .admit("FiniteField".len(), "FiniteField".len())
        .map_err(|_| failed())?;
    let mut prior = proof.add_step(ProofStep::TheoryLemma {
        theory: "FiniteField".into(),
        clause,
        farkas: None,
        kind: TheoryLemmaKind::FiniteFieldIdeal,
        lia: None,
    });
    for &root in roots {
        owner.admit(remaining.len(), 0).map_err(|_| failed())?;
        let assume = proof.add_assume(root, None);
        remaining.remove(0);
        prior = proof.add_resolution(copy(&remaining, owner)?, root, assume, prior);
    }
    // Price the bounded checker's outer clause/step carriers before its first
    // allocation; its independent algebra/evaluation then pays actual progress.
    let bytes = steps
        .checked_mul(std::mem::size_of::<Option<Vec<TermId>>>())
        .and_then(|n| {
            roots
                .len()
                .checked_mul(roots.len())
                .and_then(|pairs| pairs.checked_mul(2 * std::mem::size_of::<TermId>()))
                .and_then(|b| n.checked_add(b))
        })
        .ok_or_else(failed)?;
    owner.admit(steps, bytes).map_err(|_| failed())?;
    let checked = ay_proof::check_proof_strict_with_context_and_progress(
        &proof,
        terms,
        None,
        None,
        Some(roots),
        &mut |work, bytes| owner.admit(work, bytes).is_ok(),
    );
    owner.check().map_err(|_| failed())?;
    Ok(checked.is_ok_and(|quality| quality.is_complete()))
}

pub(super) fn apply(
    terms: &mut TermStore,
    roots: &[TermId],
    converter: &TacticModelConverter,
    owner: &dyn TermConstructionAdmission,
) -> Result<(Vec<TermId>, TacticModelConverter), TacticFailure> {
    owner.check().map_err(|_| failed())?;
    if !converter.valid(terms) {
        return Err(failed());
    }
    if !converter.is_active() {
        if roots.is_empty() {
            // Even an empty goal retains the independent original-root gate;
            // a preceding transform cannot manufacture a witness by dropping
            // obligations. No field domain or assignment is guessed here.
            let converter = converter.fixed_field(terms, Vec::new(), roots, owner)?;
            return Ok((Vec::new(), converter));
        }
        if let Some(seen) = source(terms, roots, owner)? {
            use crate::executor::finite_field::{tactic_ideal_candidate, TacticFieldCandidate};
            match tactic_ideal_candidate(terms, roots, &seen, owner) {
                Some(TacticFieldCandidate::Model(rows)) => {
                    let converter = converter.fixed_field(terms, rows, roots, owner)?;
                    owner.check().map_err(|_| failed())?;
                    return Ok((Vec::new(), converter));
                }
                Some(TacticFieldCandidate::Contradiction) => {
                    if independent_refutation(terms, roots, owner)? {
                        let borrowed = Borrowed(owner);
                        let no = CountedTermBuilder::with_admission(terms, &borrowed)
                            .map_err(|_| failed())?
                            .boolean(false)
                            .map_err(|_| failed())?;
                        let output = copy(&[no], owner)?;
                        return Ok((output, converter.clone()));
                    }
                }
                None => {}
            }
        }
    }
    owner.check().map_err(|_| failed())?;
    Ok((copy(roots, owner)?, converter.clone()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::api::{Logic, Model, ModelValue, Solver, Tactic, Term};
    fn fixture(body: &str) -> (Solver, Vec<Term>) {
        let mut solver = Solver::new(Logic::All);
        let roots = solver
            .parse_smtlib2(body.split("(apply").next().unwrap())
            .unwrap();
        (solver, roots)
    }
    fn value(model: &Model, key: &str, p: u32) -> u32 {
        match model.finite_field_val(key).unwrap() {
            ModelValue::FiniteField { value, field } if field.modulus() == p => *value,
            _ => panic!("wrong typed field model"),
        }
    }

    #[test]
    fn field_solve_composes_with_shared_timed_parameterized_simplification() {
        use crate::api::solving::tactic_parameters::{
            TacticInstance, TacticParameterValue, TacticParameters,
        };
        let (mut solver, roots) = fixture(
            "(set-logic QF_FF) (declare-const x (_ FiniteField 65537)) \
             (assert (= (ff.mul x x) #f1m65537))",
        );
        let mut parameters = TacticParameters::default();
        parameters
            .set("elim_and", TacticParameterValue::Bool(true))
            .unwrap();
        let tactic = Tactic::Shared(std::sync::Arc::new(TacticInstance::new(Tactic::TryFor(
            Box::new(Tactic::WithParams(
                Box::new(Tactic::Simplify.then(Tactic::FieldSolve)),
                parameters,
            )),
            5000,
        ))));
        let operation = solver.begin_tactic_operation().unwrap();
        assert!(tactic
            .unsupported_goal_proof_transport_admitted(operation.admission())
            .unwrap());
        drop(operation);
        let goal = solver
            .apply_tactic_subgoals_converted(&tactic, &roots, 0, None)
            .unwrap()
            .remove(0);
        assert!(goal.formulas.is_empty());
        let model = solver
            .convert_tactic_model(goal.model_converter.as_ref().unwrap(), &Model::empty())
            .unwrap();
        let x = u64::from(value(&model, "x", 65537));
        assert_eq!(x * x % 65537, 1);
        assert_eq!(solver.assertions(), roots);
    }

    #[test]
    fn field_solve_actual_conjunction_decisions_reconstruct_and_check_authored_models() {
        for (index, body) in include_str!("../../../tests/fixtures/finite_field/solve_tactic.smt2")
            .split("(reset)")
            .enumerate()
        {
            let (mut solver, roots) = fixture(body);
            let goal = solver
                .apply_tactic_subgoals_converted(&Tactic::FieldSolve, &roots, 0, None)
                .unwrap()
                .remove(0);
            assert_eq!(solver.assertions(), roots);
            if matches!(index, 0 | 3) {
                assert_eq!(goal.formulas.len(), 1);
                assert!(matches!(
                    solver.terms().get(goal.formulas[0].id()),
                    TermData::Const(Constant::Bool(false))
                ));
                assert!(
                    solver.check_sat().is_unsat(),
                    "ordinary native engine remains usable"
                );
            } else {
                assert!(goal.formulas.is_empty());
                let converter = goal.model_converter.unwrap();
                let model = solver
                    .convert_tactic_model(&converter, &Model::empty())
                    .unwrap();
                let x = u64::from(value(&model, "x", 65537));
                let y = u64::from(value(&model, "y", 65537));
                assert_eq!(x * y % 65537, 1);
                if index == 1 {
                    assert_eq!(x * x % 65537, 1);
                }
                assert!(
                    solver.check_sat().is_sat(),
                    "ordinary native fuel entry remains usable"
                );
                assert_eq!(solver.assertions(), roots);
            }
        }
    }
    #[test]
    fn field_solve_models_agree_with_independent_exhaustive_small_field_truth() {
        for p in [2u32, 3, 7] {
            for a in 0..p {
                for b in 0..p {
                    let body=format!("(set-logic QF_FF) (declare-const x (_ FiniteField {p})) (declare-const y (_ FiniteField {p})) (assert (= (ff.mul x x) #f{a}m{p})) (assert (= (ff.mul x y) #f{b}m{p}))");
                    let (mut solver, roots) = fixture(&body);
                    let sat = (0..p).any(|x| (0..p).any(|y| x * x % p == a && x * y % p == b));
                    let goal = solver
                        .apply_tactic_subgoals_converted(&Tactic::FieldSolve, &roots, 0, None)
                        .unwrap()
                        .remove(0);
                    if sat {
                        assert!(goal.formulas.is_empty(), "F{p}: x²={a},xy={b}");
                        let model = solver
                            .convert_tactic_model(
                                goal.model_converter.as_ref().unwrap(),
                                &Model::empty(),
                            )
                            .unwrap();
                        let x = value(&model, "x", p);
                        let y = value(&model, "y", p);
                        assert_eq!((x * x % p, x * y % p), (a, b));
                    } else {
                        assert_eq!(goal.formulas.len(), 1);
                        assert!(
                            matches!(
                                solver.terms().get(goal.formulas[0].id()),
                                TermData::Const(Constant::Bool(false))
                            ),
                            "F{p}: x²={a},xy={b}"
                        );
                    }
                }
            }
        }
    }
    #[test]
    fn field_solve_paid_many_equations_and_wide_variadic_models_have_no_source_size_gate() {
        let mut input = String::from("(set-logic QF_FF) (declare-const x (_ FiniteField 65537))");
        for n in 0..350 {
            input.push_str(&format!(" (assert (= (ff.add x #f{n}m65537) #f{n}m65537))"));
        }
        let (mut solver, roots) = fixture(&input);
        assert!(roots.len() > 64 && solver.terms().len() > 1024);
        let goal = solver
            .apply_tactic_subgoals_converted(&Tactic::FieldSolve, &roots, 0, None)
            .unwrap()
            .remove(0);
        assert!(goal.formulas.is_empty());
        let model = solver
            .convert_tactic_model(goal.model_converter.as_ref().unwrap(), &Model::empty())
            .unwrap();
        assert_eq!(value(&model, "x", 65537), 0);
        assert_eq!(solver.assertions(), roots);

        let mut input = String::from(
            "(set-logic QF_FF) (declare-const x (_ FiniteField 65537)) (assert (= (ff.add x",
        );
        for _ in 0..1100 {
            input.push_str(" #f1m65537");
        }
        input.push_str(") #f1100m65537))");
        let (mut solver, roots) = fixture(&input);
        let goal = solver
            .apply_tactic_subgoals_converted(&Tactic::FieldSolve, &roots, 0, None)
            .unwrap()
            .remove(0);
        assert!(goal.formulas.is_empty());
        let model = solver
            .convert_tactic_model(goal.model_converter.as_ref().unwrap(), &Model::empty())
            .unwrap();
        assert_eq!(value(&model, "x", 65537), 0);
        assert_eq!(solver.assertions(), roots);
    }
    #[test]
    fn field_solve_fixed_witness_copy_foreign_conflict_and_model_disabled_boundaries() {
        let body = include_str!("../../../tests/fixtures/finite_field/solve_tactic.smt2")
            .split("(reset)")
            .nth(1)
            .unwrap();
        let (mut solver, roots) = fixture(body);
        let goal = solver
            .apply_tactic_subgoals_converted(&Tactic::FieldSolve, &roots, 0, None)
            .unwrap()
            .remove(0);
        assert!(goal.formulas.is_empty());
        let converter = goal.model_converter.unwrap();
        let copied = converter.clone();
        let model = solver
            .convert_tactic_model(&copied, &Model::empty())
            .unwrap();
        let mut forged = Model::empty();
        let field = ay_core::FiniteFieldSort::new(65537).unwrap();
        forged.field_values.insert(
            "x".into(),
            ModelValue::FiniteField {
                value: (value(&model, "x", 65537) + 1) % 65537,
                field,
            },
        );
        assert!(solver.convert_tactic_model(&copied, &forged).is_err());
        assert!(solver
            .convert_tactic_model(&converter, &Model::empty())
            .is_ok());
        let operation = solver.begin_tactic_operation().unwrap();
        let data = solver
            .copy_unconverted_tactic_model_in_operation(&operation, &converter, &Model::empty())
            .unwrap();
        assert!(
            data.field_values.is_empty(),
            "models-disabled DATA copying cannot claim witness reconstruction"
        );
        drop(operation);
        let (other, _) = fixture(body);
        assert!(other
            .convert_tactic_model(&converter, &Model::empty())
            .is_err());
        assert_eq!(solver.assertions(), roots);
        let mut empty = Solver::new(Logic::All);
        let goal = empty
            .apply_tactic_subgoals_converted(&Tactic::FieldSolve, &[], 0, None)
            .unwrap()
            .remove(0);
        assert!(goal.formulas.is_empty());
        assert!(empty
            .convert_tactic_model(goal.model_converter.as_ref().unwrap(), &Model::empty())
            .is_ok());
    }
    #[test]
    fn field_solve_unsupported_bool_and_mixed_domains_keep_original_goals() {
        for body in [
            "(declare-const x (_ FiniteField 7)) (assert (or (= x #f1m7) (= x #f2m7)))",
            "(declare-const x (_ FiniteField 7)) (declare-const y (_ FiniteField 11)) (assert (= x #f1m7)) (assert (= y #f2m11))",
            "(declare-const x Int) (assert (= x 1))",
        ] {
            let (mut solver,roots)=fixture(body);
            let before=solver.terms().snapshot_stamp();
            let goal=solver.apply_tactic_subgoals_converted(&Tactic::FieldSolve,&roots,0,None).unwrap().remove(0);
            assert_eq!(goal.formulas,roots);
            assert!(!goal.model_converter.unwrap().is_active());
            assert_eq!(solver.terms().snapshot_stamp(),before);
        }
    }
    #[test]
    fn field_solve_native_first_stop_never_renews_and_fresh_request_recovers() {
        let body = include_str!("../../../tests/fixtures/finite_field/solve_tactic.smt2")
            .split("(reset)")
            .nth(1)
            .unwrap();
        let (mut solver, roots) = fixture(body);
        let before = solver.terms().snapshot_stamp();
        let request = solver.begin_model_evaluation_read();
        solver.interrupt();
        assert!(solver
            .apply_tactic_subgoals_converted(&Tactic::FieldSolve, &roots, 0, None)
            .is_err());
        solver.clear_interrupt();
        assert!(solver
            .apply_tactic_subgoals_converted(&Tactic::FieldSolve, &roots, 0, None)
            .is_err());
        assert_eq!(
            solver.executor.tactic_refusal_origin(),
            Some(crate::UnknownOrigin::InterruptFlag)
        );
        drop(request);
        assert_eq!(solver.terms().snapshot_stamp(), before);
        assert!(solver
            .apply_tactic_subgoals_converted(&Tactic::FieldSolve, &roots, 0, None)
            .unwrap()[0]
            .formulas
            .is_empty());
        solver.set_term_memory_limit(Some(0));
        let request = solver.begin_model_evaluation_read();
        assert!(solver
            .apply_tactic_subgoals_converted(&Tactic::FieldSolve, &roots, 0, None)
            .is_err());
        solver.set_term_memory_limit(None);
        assert!(solver
            .apply_tactic_subgoals_converted(&Tactic::FieldSolve, &roots, 0, None)
            .is_err());
        assert_eq!(
            solver.executor.tactic_refusal_origin(),
            Some(crate::UnknownOrigin::MemoryBudget)
        );
        drop(request);
        assert!(solver
            .apply_tactic_subgoals_converted(&Tactic::FieldSolve, &roots, 0, None)
            .unwrap()[0]
            .formulas
            .is_empty());
    }
}
