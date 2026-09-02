// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn sole_array_constructor_inference_stays_free_only_for_unobserved_disequality() {
    let exec = loaded(
        r#"
            (declare-datatype U ((mk (g (Array Int Bool)))))
            (declare-fun f (Int) U)
            (assert (not (= (f 0) (f 1))))
            (assert (is-mk (f 0)))
        "#,
    );
    let model = Model::empty();
    let mut builder = exec.dt_collect(&model, &[]).expect("fixture collects");
    assert!(builder.force_constructors());
    let calls: Vec<TermId> = builder
        .terms
        .iter()
        .copied()
        .filter(|&term| {
            matches!(exec.ctx.terms.get(term), TermData::App(symbol, _) if symbol.name() == "f")
        })
        .collect();
    assert_eq!(calls.len(), 2);
    let tested_term = builder
        .tester_apps
        .iter()
        .find(|(_, ctor, _)| ctor == "mk")
        .map(|(_, _, argument)| *argument)
        .expect("fixture retains the positive tester");
    let tested = class_for_term(&builder, tested_term);
    let free_term = calls
        .into_iter()
        .find(|&term| class_for_term(&builder, term) != tested)
        .expect("fixture has a second disequal class");
    let free = class_for_term(&builder, free_term);
    let tested_force = forced_constructor(&builder, tested);
    assert_eq!(tested_force.ctor, "mk");
    assert_eq!(tested_force.origin, ConstructorForceOrigin::PositiveTester);
    assert!(tested_force.vary_free_fields);
    let free_force = forced_constructor(&builder, free);
    assert_eq!(free_force.ctor, "mk");
    assert_eq!(free_force.origin, ConstructorForceOrigin::InferredSole);
    assert!(free_force.vary_free_fields);

    let mut no_disequality = exec.dt_collect(&model, &[]).expect("control collects");
    no_disequality.diseq.clear();
    assert!(no_disequality.force_constructors());
    let control_root = class_for_term(&no_disequality, free_term);
    let control_force = forced_constructor(&no_disequality, control_root);
    assert_eq!(control_force.ctor, "mk");
    assert_eq!(control_force.origin, ConstructorForceOrigin::InferredSole);
    assert!(
        !control_force.vary_free_fields,
        "without a disequality, ordinary sole-constructor inference is unchanged"
    );
}

#[test]
fn observed_array_field_keeps_sole_constructor_inference_forced() {
    let exec = loaded(
        r#"
            (declare-datatype U ((mk (g (Array Int Bool)))))
            (declare-fun f (Int) U)
            (assert (not (= (f 0) (f 1))))
            (assert (= (select (g (f 1)) 0) true))
        "#,
    );
    let model = Model::empty();
    let mut builder = exec.dt_collect(&model, &[]).expect("fixture collects");
    let observed = builder
        .sel_apps
        .iter()
        .find(|(_, selector, _)| selector == "g")
        .map(|(_, _, argument)| *argument)
        .expect("fixture retains the observed g application");
    assert!(builder.force_constructors());
    let observed_root = class_for_term(&builder, observed);
    let force = forced_constructor(&builder, observed_root);
    assert_eq!(force.ctor, "mk");
    assert_eq!(force.origin, ConstructorForceOrigin::InferredSole);
    assert!(!force.vary_free_fields);
}

#[test]
fn generated_unrooted_array_field_does_not_block_free_variation() {
    let mut exec = loaded(
        r#"
            (declare-datatype U ((mk (g (Array Int Bool)))))
            (declare-fun f (Int) U)
            (assert (not (= (f 0) (f 1))))
        "#,
    );
    let argument = exec
        .ctx
        .terms
        .term_ids()
        .find(|&term| {
            matches!(exec.ctx.terms.get(term), TermData::App(symbol, _) if symbol.name() == "f")
        })
        .expect("fixture retains a datatype call");
    let generated = exec.ctx.terms.mk_app(
        ay_core::Symbol::named("g"),
        [argument],
        Sort::Array(Box::new(ay_core::ArraySort::new(Sort::Int, Sort::Bool))),
    );
    let model = Model::empty();
    let mut builder = exec
        .dt_collect(&model, &[generated])
        .expect("generated bridge root collects");
    assert!(builder
        .sel_apps
        .iter()
        .any(|(application, selector, _)| *application == generated && selector == "g"));
    assert!(!builder
        .datatype_array_required_terms
        .as_ref()
        .is_some_and(|required| required.contains(&generated)));
    assert!(builder.force_constructors());
    let root = class_for_term(&builder, argument);
    let force = forced_constructor(&builder, root);
    assert_eq!(force.ctor, "mk");
    assert_eq!(force.origin, ConstructorForceOrigin::InferredSole);
    assert!(force.vary_free_fields);
}

#[test]
fn singleton_datatype_disequality_cannot_receive_two_values() {
    let exec = loaded(
        r#"
            (declare-datatypes ((Only 0)) (((only))))
            (declare-fun f ((_ BitVec 1)) Only)
            (declare-fun g ((_ BitVec 1)) Only)
            (assert (not (= (f #b0) (g #b0))))
        "#,
    );
    let mut model = Model::empty();
    assert!(
        exec.dt_collect(&model, &[]).is_some(),
        "the singleton fixture must enter datatype construction"
    );

    let mut apps: HashMap<String, TermId> = HashMap::default();
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut stack = exec.ctx.assertions.clone();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match exec.ctx.terms.get(term) {
            TermData::App(sym, args) => {
                if matches!(sym.name(), "f" | "g") {
                    apps.insert(sym.name().to_string(), term);
                }
                stack.extend(args.iter().copied());
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => stack.extend([*c, *a, *b]),
            _ => {}
        }
    }
    let f = *apps.get("f").expect("f application");
    let g = *apps.get("g").expect("g application");

    let constructed = exec.construct_total_datatype_model(
        &mut model,
        &[],
        &DatatypeArrayConstructionAuthorization::Ordinary,
    );
    let app_values: Vec<_> = [f, g]
        .into_iter()
        .filter_map(|term| model.dt_ground.get(&term))
        .collect();
    assert!(
        constructed > 0 && !app_values.is_empty(),
        "the admitted fixture must produce concrete ground evidence"
    );
    assert!(
        app_values.len() == 1
            || (app_values.len() == 2
                && dt_canonical_string(app_values[0]) == dt_canonical_string(app_values[1])),
        "a singleton sort cannot supply two distinct application values: {app_values:?}"
    );
}

#[test]
fn single_constructor_array_owner_flattens_to_validated_field_representation() {
    let mut exec = loaded(
        r#"
            (declare-datatypes
                ((PbLit 0) (PbTerm 0) (PbObjective 0) (Result 0))
                (
                    ((PbLit_mk
                        (PbLit_var (_ BitVec 32))
                        (PbLit_negated Bool)))
                    ((PbTerm_mk
                        (PbTerm_coeff (_ BitVec 128))
                        (PbTerm_lits (Array (_ BitVec 64) PbLit))))
                    ((PbObjective_mk
                        (PbObjective_terms (Array (_ BitVec 64) PbTerm))))
                    ((Result_ok (Result_value (_ BitVec 128)))
                     (Result_err))
                ))
            (declare-const objective PbObjective)
            (declare-const assignment (Array (_ BitVec 64) Bool))
            (declare-const result Result)
            (declare-fun checked
                ((Array (_ BitVec 64) PbTerm) (Array (_ BitVec 64) Bool))
                Result)
            (assert (= result
                (checked (PbObjective_terms objective) assignment)))
        "#,
    );

    let (owner_name, field_sort) = exec
        .ctx
        .datatype_iter()
        .find_map(|(name, constructors)| {
            let [constructor] = constructors else {
                return None;
            };
            let fields = exec.ctx.constructor_selector_info(constructor)?;
            let [(_, field_sort @ Sort::Array(_))] = fields else {
                return None;
            };
            Some((name.to_string(), field_sort.clone()))
        })
        .expect("fixture must contain one single-array-field datatype");

    let mut seen = HashSet::default();
    let mut stack = exec.ctx.assertions.clone();
    let mut saw_owner = false;
    let mut saw_exact_field = false;
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        saw_owner |= matches!(
            exec.ctx.terms.sort(term),
            Sort::Uninterpreted(name) if name == &owner_name
        );
        saw_exact_field |= exec.ctx.terms.sort(term) == &field_sort;
        match exec.ctx.terms.get(term) {
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(condition, then_term, else_term) => {
                stack.extend([*condition, *then_term, *else_term]);
            }
            _ => {}
        }
    }
    assert!(
        !saw_owner && saw_exact_field,
        "single-constructor lowering must validate the exact field array, not fabricate an \
         absent {owner_name} owner (owner={saw_owner}, field={saw_exact_field})"
    );
    assert!(
        exec.authored_datatype_array_construction_cells()
            .expect("authored capability census stays bounded")
            .is_empty(),
        "a bare Array<_, PbTerm> field container is not a stamped datatype-cell owner"
    );

    let probe_model = Model::empty();
    let probe = exec
        .dt_collect(&probe_model, &[])
        .expect("flattened opaque fixture must still collect its Result component");
    assert!(
        probe
            .members
            .keys()
            .all(|root| probe.class_sort_name(*root).as_deref() != Some(&owner_name)),
        "completion must not synthesize a datatype owner absent from the lowered query"
    );

    let result = exec.check_sat().expect("tiny flattened fixture must solve");
    assert_eq!(
        result,
        crate::executor_types::SolveResult::Sat,
        "flattened field-array fixture unexpectedly declined: reason={:?}; detail={:?}",
        exec.unknown_reason(),
        exec.statistics().get_string("unknown.detail")
    );
    assert!(
        exec.last_model_validated,
        "the exact flattened field-array representation must receive sealed independent \
         model-validation evidence"
    );
}
