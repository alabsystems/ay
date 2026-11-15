// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit pins for the guarded-instance clause derivation
//! (#guarded-instance-checked-derivation).

use super::*;
use crate::ematching::ForallInstantiationProvenance;
use crate::executor::Executor;

/// The guarded lane's canonical shape: the universal is a disjunct, and the
/// sibling `c` is forced false only through a two-step chain, so the universal
/// is not entailed and every instance of it is a guarded clause. UNSAT.
const GUARD_FORCED: &str = r#"
    (set-logic UFLIA)
    (declare-fun f (Int) Int)
    (declare-const c Bool)
    (declare-const d Bool)
    (assert (or c (forall ((x Int)) (> (f x) 0))))
    (assert (or (not c) d))
    (assert (not d))
    (assert (< (f 1) 0))
"#;

/// The same clause with the sibling disjunct asserted TRUE. SAT: `c` holds
/// and the universal may be false. The unguarded instance `(> (f 1) 0)` would
/// refute it; the resolvent `(or c (> (f 1) 0))` does not.
const GUARD_SATISFIABLE: &str = r#"
    (set-logic UFLIA)
    (declare-fun f (Int) Int)
    (declare-const c Bool)
    (assert (or c (forall ((x Int)) (> (f x) 0))))
    (assert c)
    (assert (< (f 1) 0))
"#;

/// `GUARD_FORCED` with the clause written as `(ite c true ...)`, which
/// elaboration folds into the same `(or c Q)` root. UNSAT.
const GUARD_FORCED_ITE: &str = r#"
    (set-logic UFLIA)
    (declare-fun f (Int) Int)
    (declare-const c Bool)
    (declare-const d Bool)
    (assert (ite c true (forall ((x Int)) (> (f x) 0))))
    (assert (or (not c) d))
    (assert (not d))
    (assert (< (f 1) 0))
"#;

/// Load `input` (declarations and assertions only) into a fresh executor with
/// the query epoch a translation is attempted under.
fn loaded(input: &str) -> Executor {
    let commands = ay_frontend::parse(input).expect("fixture parses");
    let mut exec = Executor::new();
    assert!(
        exec.execute_all(&commands)
            .expect("fixture loads")
            .is_empty(),
        "fixture must contain declarations and assertions only"
    );
    exec.begin_unsat_query_epoch(&exec.ctx.assertions.clone());
    exec.bind_unsat_query_assumptions(&[]);
    exec
}

/// The authored `or` root carrying a universal literal, and that universal.
fn guarded_clause(exec: &Executor) -> (TermId, TermId) {
    for &root in &exec.ctx.assertions {
        let TermData::App(Symbol::Named(name), args) = exec.ctx.terms.get(root) else {
            continue;
        };
        if name != "or" {
            continue;
        }
        if let Some(&forall) = args
            .iter()
            .find(|&&arg| matches!(exec.ctx.terms.get(arg), TermData::Forall(..)))
        {
            return (root, forall);
        }
    }
    panic!("the fixture has an `or` root with a universal literal");
}

/// Record the guarded instance of `quantifier` at `x := 1`, exactly as
/// `add_guarded_instance_clauses` records an asserted clause.
fn record_guarded_instance_at_one(exec: &mut Executor, quantifier: TermId) {
    let one = exec.ctx.terms.mk_int(1.into());
    let TermData::Forall(binders, body, _) = exec.ctx.terms.get(quantifier).clone() else {
        panic!("the guarded source is a forall");
    };
    let instance =
        crate::cegqi::lra_nested::tree::instantiate(&mut exec.ctx.terms, body, &binders, &[one])
            .expect("the instance at 1 is exact");
    exec.guarded_instance_records
        .push(ForallInstantiationProvenance {
            quantifier,
            binding: vec![one],
            instance,
        });
}

fn count_rule(proof: &Proof, rule: &AletheRule) -> usize {
    proof
        .steps
        .iter()
        .filter(|step| matches!(step, ProofStep::Step { rule: r, .. } if r == rule))
        .count()
}

/// THE CAPABILITY. A recorded guarded instance is enough for consequence
/// replay to derive the refutation from the authored scope: the clause
/// `(or c Q)` is clausified, `forall_inst` instantiates `Q`, and the resolvent
/// `(or c B[1])` closes the ground refutation. Nothing is assumed but the
/// authored roots, and the strict checker accepts the whole proof.
///
/// MUTATION: drop the `plan_guarded_clausal_instances` call from
/// `build_authored_consequence_replay_refutation` and the replay declines
/// ("no derivable recorded instance"), so the first assertion fails.
#[test]
fn a_recorded_guarded_instance_is_derived_by_forall_inst_from_its_authored_clause() {
    let mut exec = loaded(GUARD_FORCED);
    let (clause, quantifier) = guarded_clause(&exec);
    record_guarded_instance_at_one(&mut exec, quantifier);
    assert!(
        exec.try_translate_authored_consequence_replay_unsat(),
        "the resolvent (or c (f 1 > 0)) with the authored ground roots is UNSAT"
    );
    let proof = exec
        .last_proof
        .clone()
        .expect("translation installs last_proof");
    let not_quantifier = exec.ctx.terms.mk_not_raw(quantifier);
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step { rule: AletheRule::ForallInst, clause, .. }
                if matches!(
                    exec.ctx.terms.get(clause[0]),
                    TermData::App(_, args) if args.first() == Some(&not_quantifier)
                )
        )),
        "the guarded instance is derived by `forall_inst` on the authored universal"
    );
    assert!(
        count_rule(&proof, &AletheRule::Or) >= 2,
        "the authored clause and the `forall_inst` disjunction are both clausified"
    );
    assert!(
        proof
            .steps
            .iter()
            .any(|step| matches!(step, ProofStep::Assume(term) if *term == clause)),
        "the authored clause is assumed as written"
    );
    let authored = exec.exact_concrete_authored_scope();
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &authored).is_ok());
    let quality = exec
        .check_proof_strict_with_datatypes(&proof)
        .expect("the derivation is strictly checkable");
    assert!(quality.is_complete(), "no trust and no hole: {quality:?}");
}

/// NEGATIVE TWIN: the SAME record on the satisfiable sibling. The planned
/// consequence keeps the guard's sibling literal — it is the resolvent on the
/// proxy, never the bare instance — so with `c` true it refutes nothing, and
/// no proof is installed.
///
/// MUTATION: plan the bare instance `B[1]` instead of the resolvent (drop the
/// `Keep` literals) — `close_clause_as_formula` then refuses the stitch, and
/// the strict twin below refuses the inference itself.
#[test]
fn the_same_record_on_a_satisfiable_sibling_derives_nothing() {
    let mut exec = loaded(GUARD_SATISFIABLE);
    let (_, quantifier) = guarded_clause(&exec);
    record_guarded_instance_at_one(&mut exec, quantifier);
    assert!(
        !exec.try_translate_authored_consequence_replay_unsat(),
        "(or c (f 1 > 0)) is implied, and satisfiable beside c and f 1 < 0"
    );
    assert!(
        exec.last_proof.is_none(),
        "a declined replay installs nothing"
    );
}

/// NEGATIVE TWIN at the checker: the bare instance is NOT implied by the
/// authored clause. A proof that resolves `(cl c Q)` against the
/// `forall_inst` clause and claims `(cl B[1])` — dropping the sibling literal,
/// i.e. treating the guarded instance as a top-level fact — is refused at that
/// step, while the identical proof concluding the resolvent `(cl c B[1])`
/// validates every step (so the refusal is the inference's, not the shape's).
#[test]
fn the_strict_checker_refuses_the_bare_instance_of_a_disjunct_universal() {
    let mut exec = loaded(GUARD_FORCED);
    let (clause, quantifier) = guarded_clause(&exec);
    let one = exec.ctx.terms.mk_int(1.into());
    let TermData::Forall(binders, body, _) = exec.ctx.terms.get(quantifier).clone() else {
        panic!("forall");
    };
    let instance =
        crate::cegqi::lra_nested::tree::instantiate(&mut exec.ctx.terms, body, &binders, &[one])
            .expect("exact instance");
    let TermData::App(_, literals) = exec.ctx.terms.get(clause).clone() else {
        panic!("or root");
    };
    let not_quantifier = exec.ctx.terms.mk_not_raw(quantifier);
    let implication = exec.ctx.terms.mk_app(
        Symbol::named("or"),
        vec![not_quantifier, instance],
        Sort::Bool,
    );
    let resolve_to = |conclusion: Vec<TermId>| {
        let mut proof = Proof::new();
        let assumed = proof.add_assume(clause, None);
        let clausified =
            proof.add_rule_step(AletheRule::Or, literals.clone(), vec![assumed], Vec::new());
        let instantiated = proof.add_rule_step(
            AletheRule::ForallInst,
            vec![implication],
            Vec::new(),
            vec![one],
        );
        let split = proof.add_rule_step(
            AletheRule::Or,
            vec![not_quantifier, instance],
            vec![instantiated],
            Vec::new(),
        );
        let _ = proof.add_resolution(conclusion, quantifier, clausified, split);
        proof
    };
    let sibling = literals[0];
    // Neither proof reaches the empty clause, so the checker always ends on
    // `FinalClauseNotEmpty` once every step validated. That is the CONTROL:
    // the resolvent is a valid inference and only the missing refutation
    // remains.
    let control = exec.check_proof_strict_with_datatypes(&resolve_to(vec![sibling, instance]));
    assert!(
        matches!(
            control,
            Err(ay_proof::ProofCheckError::FinalClauseNotEmpty { .. })
        ),
        "control: every step of the resolvent (cl c B[1]) validates; got {control:?}"
    );
    let bare = exec.check_proof_strict_with_datatypes(&resolve_to(vec![instance]));
    assert!(
        bare.is_err()
            && !matches!(
                bare,
                Err(ay_proof::ProofCheckError::FinalClauseNotEmpty { .. })
            ),
        "resolving (cl c Q) with (cl (not Q) B) yields (cl c B), never (cl B): the \
         resolution step itself must be refused; got {bare:?}"
    );
}

/// PRESENTATION GATE. Elaboration folds `(ite c true Q)` into the very same
/// `(or c Q)` root, but the printer cannot `assume` a binder-bearing root in a
/// shape its source row does not have: a stitched proof over it renders an
/// `assume` the input never states, which the pinned checker rejects. So the
/// folded root gets no plan, while the twin written as the `or` does.
///
/// MUTATION: make `guarded_source_is_written_as_this_clause` return `true`
/// and the ite fixture is planned (its CLI document then fails carcara at the
/// `assume`, measured: `invalid`).
#[test]
fn a_root_written_as_another_connective_gets_no_guarded_plan() {
    for (fixture, written_as_or) in [(GUARD_FORCED, true), (GUARD_FORCED_ITE, false)] {
        let mut exec = loaded(fixture);
        let (_, quantifier) = guarded_clause(&exec);
        record_guarded_instance_at_one(&mut exec, quantifier);
        let authored = exec.exact_concrete_authored_scope();
        let closure = exec.authored_and_conjunct_closure(&authored);
        let mut plan = ay_core::kani_compat::DetHashMap::default();
        let mut instances = Vec::new();
        exec.plan_guarded_clausal_instances(&closure, &mut plan, &mut instances, MAX_INSTANCES);
        assert_eq!(
            !instances.is_empty(),
            written_as_or,
            "a guarded plan exists exactly when the root is written as the `or` \
             (written_as_or={written_as_or}, planned={instances:?})"
        );
    }
}

/// Four guarded universals beside a sibling literal that keeps a quantifier,
/// then a plannable guarded clause over a fifth universal.
const QUANTIFIED_SIBLING_THEN_PLANNABLE: &str = r#"
    (set-logic UFLIA)
    (declare-fun f0 (Int) Int)
    (declare-fun f1 (Int) Int)
    (declare-fun f2 (Int) Int)
    (declare-fun f3 (Int) Int)
    (declare-fun g (Int) Int)
    (declare-fun p (Int Int) Bool)
    (declare-const c Bool)
    (declare-const d Bool)
    (declare-const e Bool)
    (assert (or c (forall ((x Int)) (> (f0 x) 0)) (forall ((x Int)) (> (f1 x) 0))
                  (forall ((x Int)) (> (f2 x) 0)) (forall ((x Int)) (> (f3 x) 0))
                  (and d (forall ((x Int)) (exists ((y Int)) (p x y))))))
    (assert (or e (forall ((x Int)) (> (g x) 0))))
"#;

/// Four guarded universals beside a ground sibling: every combination of
/// their bindings is a distinct quantifier-free consequence.
const FOUR_GUARDED: &str = r#"
    (set-logic UFLIA)
    (declare-fun f0 (Int) Int)
    (declare-fun f1 (Int) Int)
    (declare-fun f2 (Int) Int)
    (declare-fun f3 (Int) Int)
    (declare-const c Bool)
    (assert (or c (forall ((x Int)) (> (f0 x) 0)) (forall ((x Int)) (> (f1 x) 0))
                  (forall ((x Int)) (> (f2 x) 0)) (forall ((x Int)) (> (f3 x) 0))))
"#;

/// The authored `or` roots carrying a universal literal, in assertion order.
fn guarded_roots(exec: &Executor) -> Vec<TermId> {
    exec.ctx
        .assertions
        .iter()
        .copied()
        .filter(|&root| {
            matches!(
                exec.ctx.terms.get(root),
                TermData::App(Symbol::Named(name), args) if name == "or"
                    && args.iter().any(|&arg| matches!(exec.ctx.terms.get(arg), TermData::Forall(..)))
            )
        })
        .collect()
}

/// Record the guarded instances `x := 0..count` of every direct universal
/// literal of `root`, as `add_guarded_instance_clauses` records them; returns
/// how many universals were recorded.
fn record_bindings_of_every_universal(exec: &mut Executor, root: TermId, count: i64) -> usize {
    let TermData::App(_, literals) = exec.ctx.terms.get(root).clone() else {
        panic!("or root");
    };
    let mut universals = 0;
    for quantifier in literals {
        let TermData::Forall(binders, body, _) = exec.ctx.terms.get(quantifier).clone() else {
            continue;
        };
        universals += 1;
        for value in 0..count {
            let value = exec.ctx.terms.mk_int(value.into());
            let instance = crate::cegqi::lra_nested::tree::instantiate(
                &mut exec.ctx.terms,
                body,
                &binders,
                &[value],
            )
            .expect("exact instance");
            exec.guarded_instance_records
                .push(ForallInstantiationProvenance {
                    quantifier,
                    binding: vec![value],
                    instance,
                });
        }
    }
    universals
}

/// BUDGET, declined side. Every consequence keeps the clause's unguarded
/// literals, so a clause beside a quantified sibling declines EVERY
/// combination of its recorded bindings (here `8^4 = 4096`). The planner must
/// skip it without walking that cross product: walked, it interned an `or`
/// per combination (CLI, measured: `unsat` in 0.09 s became `canceled` at
/// 120 s and 3.4 GB on a 15-binding twin), and with the combination budget in
/// force it would spend the whole budget on nothing and starve the plannable
/// clause after it.
///
/// MUTATION (measured): drop the quantified-literal pre-check and the later
/// clause gets no plan, because the declined clause exhausts
/// `MAX_GUARDED_COMBINATIONS`. The unbounded planner first proposed (no
/// pre-check, no budget, the quantifier check after interning) interns 4,097
/// terms here where one is expected.
#[test]
fn a_clause_with_a_quantified_sibling_is_never_walked() {
    let mut exec = loaded(QUANTIFIED_SIBLING_THEN_PLANNABLE);
    let roots = guarded_roots(&exec);
    assert_eq!(roots.len(), 2, "two guarded `or` roots: {roots:?}");
    let (declined, plannable) = (roots[0], roots[1]);
    assert_eq!(
        record_bindings_of_every_universal(&mut exec, declined, 8),
        4
    );
    assert_eq!(
        record_bindings_of_every_universal(&mut exec, plannable, 1),
        1
    );
    let authored = exec.exact_concrete_authored_scope();
    let closure = exec.authored_and_conjunct_closure(&authored);
    let at = |root| closure.ordered.iter().position(|&term| term == root);
    assert!(
        matches!((at(declined), at(plannable)), (Some(first), Some(second)) if first < second),
        "the declined clause is planned FIRST, so a walk of it would spend the budget"
    );
    let before = exec.ctx.terms.len();
    let mut plan = ay_core::kani_compat::DetHashMap::default();
    let mut instances = Vec::new();
    exec.plan_guarded_clausal_instances(&closure, &mut plan, &mut instances, MAX_INSTANCES);
    assert_eq!(
        instances.len(),
        1,
        "only the plannable clause: {instances:?}"
    );
    assert!(
        matches!(
            plan.get(&instances[0]),
            Some(ConsequencePlan::ClausalInstance { source, .. }) if *source == plannable
        ),
        "the one plan is the later clause's resolvent"
    );
    assert_eq!(
        exec.ctx.terms.len() - before,
        instances.len(),
        "the declined clause interns nothing; the planned one interns its `or`"
    );
}

/// BUDGET, planned side: with no instance cap in force, one planning pass
/// visits at most `MAX_GUARDED_COMBINATIONS` combinations (`8^4 = 4096`
/// distinct quantifier-free consequences are available here).
///
/// MUTATION: drop the budget and all 4,096 are planned.
#[test]
fn the_guarded_cross_product_stops_at_its_combination_budget() {
    let mut exec = loaded(FOUR_GUARDED);
    let roots = guarded_roots(&exec);
    assert_eq!(
        record_bindings_of_every_universal(&mut exec, roots[0], 8),
        4
    );
    let authored = exec.exact_concrete_authored_scope();
    let closure = exec.authored_and_conjunct_closure(&authored);
    let mut plan = ay_core::kani_compat::DetHashMap::default();
    let mut instances = Vec::new();
    exec.plan_guarded_clausal_instances(&closure, &mut plan, &mut instances, usize::MAX);
    assert_eq!(instances.len(), MAX_GUARDED_COMBINATIONS);
}
