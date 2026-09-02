// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn datatype_valued_let_blocks_same_sort_opaque_completion() {
    let mut exec = loaded(
        r#"
            (declare-datatype D ((D_zero) (D_one)))
            (declare-fun opaque ((_ BitVec 1)) D)
            (assert (= (opaque #b0) D_zero))
        "#,
    );
    let mut seen = HashSet::default();
    let mut stack = exec.ctx.assertions.clone();
    let mut opaque = None;
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match exec.ctx.terms.get(term) {
            TermData::App(symbol, args) => {
                if symbol.name() == "opaque" {
                    opaque = Some(term);
                }
                stack.extend(args.iter().copied());
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(condition, then_term, else_term) => {
                stack.extend([*condition, *then_term, *else_term]);
            }
            _ => {}
        }
    }
    let opaque = opaque.expect("fixture must contain the datatype-valued UF application");
    // Parser elaboration normally substitutes source `let`s.  Inject the
    // low-level form adversarially because internal rewrites can still
    // construct it and the collector must fail closed for every TermData.
    let opaque_let = exec.ctx.terms.mk_let(Vec::new(), opaque);
    let extra_root = exec.ctx.terms.mk_eq(opaque_let, opaque);

    let preflight = exec
        .preflight_opaque_dt_collection(&[extra_root])
        .expect("bounded adversarial fixture must pass resource preflight");
    let (_, _, opaque_apps, names, members, strict) = preflight.into_parts();
    assert!(strict, "fixture must exercise strict opaque collection");
    assert!(opaque_apps.contains(&opaque));
    let retained = exec
        .opaque_dt_constructible_names(&[extra_root], &names, &members, &opaque_apps)
        .expect("bounded datatype inventory must classify exactly");
    assert!(
        !retained.contains("D"),
        "an unsupported datatype-valued let must block its same-sort component: {retained:?}"
    );
    assert!(
        exec.dt_collect(&Model::empty(), &[extra_root]).is_none(),
        "collection must fail closed instead of omitting the datatype-valued let"
    );
}

#[test]
fn opaque_completion_retains_structured_datatype_for_gate_projection() {
    let exec = loaded(
        r#"
            (declare-datatypes
                ((PbLit 0) (PbTerm 0) (PbObjective 0) (EvalError 0) (Result 0))
                (
                    ((PbLit_mk
                        (PbLit_var (_ BitVec 32))
                        (PbLit_negated Bool)))
                    ((PbTerm_mk
                        (PbTerm_coeff (_ BitVec 128))
                        (PbTerm_lits (Array (_ BitVec 64) PbLit))))
                    ((PbObjective_empty)
                     (PbObjective_mk
                        (PbObjective_terms (Array (_ BitVec 64) PbTerm))))
                    ((EvalError_overflow))
                    ((Result_ok (Result_value (_ BitVec 128)))
                     (Result_err (Result_error EvalError)))
                ))
            (declare-const objective PbObjective)
            (declare-const term PbTerm)
            (declare-const assignment (Array (_ BitVec 64) Bool))
            (declare-const result Result)
            (declare-fun checked
                ((Array (_ BitVec 64) PbTerm) (Array (_ BitVec 64) Bool))
                Result)
            (assert (= result
                (checked (PbObjective_terms objective) assignment)))
            (assert ((_ is PbObjective_mk) objective))
            (assert (= term
                (select (PbObjective_terms objective) #x0000000000000000)))
        "#,
    );
    let preflight = exec
        .preflight_opaque_dt_collection(&[])
        .expect("bounded opaque fixture must pass preflight");
    let (_, _, opaque_apps, names, members, strict) = preflight.into_parts();
    assert!(strict, "the fixture must exercise strict opaque collection");
    let retained = exec
        .opaque_dt_constructible_names(&[], &names, &members, &opaque_apps)
        .expect("bounded schemas must classify exactly");

    assert!(
        retained.contains("Result") && retained.contains("EvalError"),
        "the unrelated scalar Result component must remain constructible: {retained:?}"
    );
    assert!(retained.contains("PbLit"));
    assert!(
        retained.contains("PbTerm"),
        "an exactly typed canonical array select retains its structured datatype result: \
         {retained:?}"
    );
    assert!(
        retained.contains("PbObjective"),
        "an array carrier is an extensional boundary, so its owner remains constructible: \
         {retained:?}"
    );

    let probe_model = Model::empty();
    let mut probe = exec
        .dt_collect(&probe_model, &[])
        .expect("the classified fixture must collect");
    assert!(probe.force_constructors());
    probe.add_observation_disequalities();
    assert!(probe.construct_all(), "bounded fixture must construct");
    let class_schemas: Vec<String> = probe
        .members
        .keys()
        .map(|root| {
            let sort_name = probe.class_sort_name(*root);
            let constructors: Vec<String> = sort_name
                .as_ref()
                .and_then(|name| exec.ctx.datatype_constructors(name))
                .into_iter()
                .flatten()
                .map(|constructor| {
                    format!(
                        "{constructor}:{:?}",
                        exec.ctx.constructor_selector_info(constructor)
                    )
                })
                .collect();
            let members: Vec<_> = probe
                .members
                .get(root)
                .into_iter()
                .flatten()
                .map(|member| {
                    let term = probe.terms[*member];
                    (term, exec.ctx.terms.sort(term).clone())
                })
                .collect();
            format!("root={root} sort={sort_name:?} ctors={constructors:?} members={members:?}")
        })
        .collect();
    let mut assertion_seen = HashSet::default();
    let mut assertion_stack = exec.ctx.assertions.clone();
    let mut assertion_rows = Vec::new();
    while let Some(term) = assertion_stack.pop() {
        if !assertion_seen.insert(term) {
            continue;
        }
        assertion_rows.push(format!(
            "{term:?} sort={:?} data={:?}",
            exec.ctx.terms.sort(term),
            exec.ctx.terms.get(term)
        ));
        match exec.ctx.terms.get(term) {
            TermData::App(_, args) => assertion_stack.extend(args.iter().copied()),
            TermData::Not(inner) => assertion_stack.push(*inner),
            TermData::Ite(condition, then_term, else_term) => {
                assertion_stack.extend([*condition, *then_term, *else_term]);
            }
            _ => {}
        }
    }
    let (objective_root, objective_ctor, objective_selector) = probe
        .members
        .keys()
        .find_map(|root| {
            let sort_name = probe.class_sort_name(*root)?;
            let constructors = exec.ctx.datatype_constructors(&sort_name)?;
            constructors.iter().find_map(|constructor| {
                let fields = exec.ctx.constructor_selector_info(constructor)?;
                let [(selector, Sort::Array(_))] = fields else {
                    return None;
                };
                Some((*root, constructor.clone(), selector.clone()))
            })
        })
        .unwrap_or_else(|| {
            panic!(
                "collector must retain the unique one-array-field class: names={names:?} \
                 retained={retained:?} classes={class_schemas:#?} \
                 assertions={assertion_rows:#?}"
            )
        });
    let objective_sources: Vec<_> = probe
        .sel_apps
        .iter()
        .filter(|(_, selector, argument)| {
            selector == &objective_selector
                && probe
                    .index
                    .get(argument)
                    .is_some_and(|index| probe.class_of[*index] == objective_root)
        })
        .map(|(app, _, _)| (*app, probe.scalar_term_value(*app)))
        .collect();
    assert!(
        matches!(
            probe.values.get(&objective_root),
            Some(Some(ModelValue::Datatype { ctor, args }))
                if ctor == &objective_ctor
                    && matches!(args.as_slice(), [ModelValue::Array(_)])
        ),
        "objective class must construct exactly: forced={:?} conflicted={} sources={:?} value={:?}",
        probe
            .info
            .get(&objective_root)
            .and_then(|info| info.forced.as_ref())
            .map(|forced| forced.ctor.as_str()),
        probe
            .info
            .get(&objective_root)
            .is_some_and(|info| info.conflicted),
        objective_sources,
        probe.values.get(&objective_root),
    );

    let mut model = Model::empty();
    assert!(
        exec.construct_total_datatype_model(
            &mut model,
            &[],
            &DatatypeArrayConstructionAuthorization::Ordinary,
        ) > 0,
        "structured schema must not discard unrelated opaque completion"
    );
    let (objective, objective_value) = model
        .dt_ground
        .iter()
        .find(|(_, value)| {
            matches!(
                value,
                ModelValue::Datatype { ctor, args }
                    if ctor == &objective_ctor
                        && matches!(args.as_slice(), [ModelValue::Array(_)])
            )
        })
        .unwrap_or_else(|| {
            panic!(
                "objective must retain its exact constructor/array value: {:?}",
                model.dt_ground
            )
        });
    assert!(
        matches!(
            objective_value,
            ModelValue::Datatype { ctor, args }
                if ctor == &objective_ctor
                    && matches!(args.as_slice(), [ModelValue::Array(_)])
        ),
        "objective must retain its exact constructor/array value: {:?}",
        objective_value
    );
    assert!(
        !model
            .dt_pins
            .keys()
            .any(|term| matches!(exec.ctx.terms.sort(*term), Sort::Array(_))),
        "an array term has no lossless EvalValue pin; the structured gate path owns it"
    );
    assert!(
        !model.dt_pins.contains_key(objective),
        "an array-containing datatype has no scalar canonical pin; its exact dt_ground tree owns it"
    );
    let pbterm_values: Vec<_> = model
        .dt_ground
        .iter()
        .filter(|(term, _)| {
            exec.datatype_sort_name(exec.ctx.terms.sort(**term))
                .as_deref()
                == Some("PbTerm")
        })
        .map(|(_, value)| value)
        .collect();
    assert!(
        pbterm_values.len() >= 2
            && pbterm_values.iter().all(|value| {
                matches!(
                    value,
                    ModelValue::Datatype { ctor, args }
                        if ctor == "PbTerm_mk"
                            && matches!(
                                args.as_slice(),
                                [ModelValue::BitVec { width: 128, .. }, ModelValue::Array(_)]
                            )
                )
            })
            && pbterm_values
                .windows(2)
                .all(|pair| dt_canonical_string(pair[0]) == dt_canonical_string(pair[1])),
        "the seed and canonical select must share one exact constructor/arity value: \
         {pbterm_values:?}"
    );
}

#[test]
fn structured_ground_finalization_exhaustion_is_atomic() {
    let exec = loaded(
        r#"
            (declare-datatype Box
                ((Box_empty)
                 (Box_mk (Box_payload (Array Int Int)))))
            (declare-const input (Array Int Int))
            (declare-fun opaque_box ((Array Int Int)) Box)
            (assert ((_ is Box_mk) (opaque_box input)))
        "#,
    );
    let model = Model::empty();
    {
        let mut builder = exec
            .dt_collect(&model, &[])
            .expect("bounded opaque fixture must enter construction");
        assert!(!builder.terms.is_empty());
        assert!(builder.force_constructors());
        builder.add_observation_disequalities();
        assert!(builder.construct_all());

        // Exhaust exactly at the first retained ground clone. `finish`
        // assembles into local vectors and must return no partial result;
        // the caller cannot mutate the model until all charges succeed.
        builder.work_budget = OpaqueDtConstructionBudget::with_limit(0);
        assert!(builder.finish().is_none());
    }
    assert!(model.dt_ground.is_empty());
    assert!(model.dt_pins.is_empty());
}
