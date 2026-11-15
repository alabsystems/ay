// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::executor::model::Model;
use ay_core::kani_compat::DetHashMap;
use num_bigint::BigInt;
use std::time::Duration;

mod captured;
mod resources;

const DECLARATIONS: &str = r#"
(set-logic ALL)
(declare-fun f (Bool (_ BitVec 8)) (_ BitVec 8))
(declare-fun x () (_ BitVec 8))
(declare-fun fill () (_ BitVec 8))
(declare-fun length () (_ BitVec 64))
(declare-fun a () (Array (_ BitVec 64) (_ BitVec 8)))
(declare-fun __gpc1 () (_ BitVec 64))
"#;
const ASSIGNMENT: &str = "(assert (and (= fill (f true x)) (= length #x0000000000000041)))";
const QUANTIFIED: &str = "(assert (forall ((ay!source!0_8 (_ BitVec 64)) (ay!source!1_9 (_ BitVec 64))) (or (= (f true x) (select a ay!source!0_8)) (not (bvult ay!source!0_8 length)))))";
const READ: &str = "(assert (or (= (f true x) (select a __gpc1)) (not (bvult __gpc1 length))))";
const COUNTEREXAMPLE: &str = "(assert (or (and (bvult __gpc1 length) (bvule #x0000000000000020 __gpc1) (not (= fill (select a __gpc1)))) (= length #x0000000000000000)))";
const HEADS: [&str; 6] = ["__gpc1", "a", "f", "fill", "length", "x"];

fn source(satisfiable: bool, quantified: bool) -> String {
    let last = if satisfiable {
        COUNTEREXAMPLE.replace(
            "(not (= fill (select a __gpc1)))",
            "(= fill (select a __gpc1))",
        )
    } else {
        COUNTEREXAMPLE.to_string()
    };
    format!(
        "{DECLARATIONS}\n{ASSIGNMENT}\n{}\n{READ}\n{last}",
        if quantified { QUANTIFIED } else { "" }
    )
}

fn prepared(satisfiable: bool) -> Executor {
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    exec.set_verification_level(crate::VerificationLevel::ProofChecked);
    exec.set_timeout(Some(Duration::from_secs(15)));
    exec.set_term_memory_limit(Some(128 * 1024 * 1024));
    exec.execute_all(&ay_frontend::parse(&source(satisfiable, true)).unwrap())
        .unwrap();
    assert_eq!(exec.ctx.assertions.len(), 4);
    exec
}

fn term(exec: &mut Executor, spelling: &str) -> TermId {
    let commands = ay_frontend::parse(&format!("(get-value ({spelling}))")).unwrap();
    let ay_frontend::Command::GetValue(terms) = &commands[0] else {
        panic!("get-value fixture");
    };
    exec.ctx.elaborate_surface_subterm(&terms[0].1).unwrap()
}

fn bindings(exec: &Executor) -> Vec<CheckedProjectionBinding> {
    HEADS
        .iter()
        .map(|&name| {
            let info = exec.ctx.symbol_info(name).unwrap();
            exec.ctx
                .check_projection_declaration(&ay_frontend::ProjectionBindingRequest {
                    symbol: Symbol::named(name),
                    parameter_sorts: info.arg_sorts.clone(),
                    result_sort: info.sort.clone(),
                })
                .unwrap()
        })
        .collect()
}

fn pin_fixture(exec: &mut Executor) -> Vec<TermId> {
    let samples = [
        ("__gpc1", 32),
        ("(select a __gpc1)", 0),
        ("(f true x)", 0),
        ("fill", 0),
        ("length", 65),
        ("x", 0),
    ];
    let mut model = Model::empty();
    let mut values = DetHashMap::default();
    let mut ids = Vec::new();
    for (spelling, value) in samples {
        let id = term(exec, spelling);
        values.insert(id, BigInt::from(value));
        ids.push(id);
    }
    model.bv_model = Some(ay_bv::BvModel {
        values,
        term_to_bits: DetHashMap::default(),
        bool_overrides: DetHashMap::default(),
    });
    exec.last_model = Some(model);
    ids
}

fn seed(exec: &mut Executor) -> Option<Vec<TermId>> {
    let roots = exec.ctx.assertions.clone();
    let bindings = bindings(exec);
    build(
        exec,
        &roots,
        &bindings.iter().collect::<Vec<_>>(),
        &mut 20_000,
        ay_core::time::Instant::now() + Duration::from_secs(2),
    )
}

fn observation_diagnostic(exec: &Executor, roots: &[TermId]) -> String {
    let declarations = bindings(exec);
    let mut selected = vec![None; declarations.len()];
    let mut work = 20_000;
    let mut never = || false;
    let mut budget = Budget {
        remaining: &mut work,
        deadline: ay_core::time::Instant::now() + Duration::from_secs(1),
        stopped: false,
        stop: &mut never,
    };
    let admitted = census(
        exec,
        roots,
        &declarations.iter().collect::<Vec<_>>(),
        &mut selected,
        &mut Vec::new(),
        &mut budget,
    )
    .is_some();
    let details: Vec<_> = HEADS
        .iter()
        .zip(selected)
        .map(|(name, term)| {
            let probes = (|| {
                let model = exec.last_model.as_ref()?;
                let term = term?;
                let raw_cap = model.bv_model.as_ref().map_or(0, |bv| bv.values.capacity());
                budget.charge(
                    exec,
                    raw_cap
                        .checked_add(model.completed_values.capacity())?
                        .checked_add(100)?,
                )?;
                let raw = model
                    .bv_model
                    .as_ref()
                    .and_then(|bv| bv.values.get(&term))
                    .map(|value| (value.sign(), value.bits()));
                Some((raw, model.completed_values.contains_key(&term)))
            })();
            format!("{name}: term={term:?}, raw_sign_bits_and_completed={probes:?}")
        })
        .collect();
    format!(
        "census={admitted}, remaining={work}, model={}, [{}]",
        exec.last_model.is_some(),
        details.join("; ")
    )
}

fn certify(exec: &mut Executor) -> Option<()> {
    let roots = exec.ctx.assertions.clone();
    exec.const_interp_cert_inner(
        &roots,
        crate::logic_detection::LogicCategory::QfBvLiaIndep,
        super::super::ConstInterpCertMode::On,
        ay_core::time::Instant::now() + Duration::from_secs(2),
        super::super::ConstInterpCandidateSource::FixedFamily,
        &mut Default::default(),
    )
}

#[test]
fn complete_direct_observations_seed_one_exact_interpretation() {
    let mut exec = prepared(true);
    pin_fixture(&mut exec);
    let roots = exec.ctx.assertions.clone();
    let result = seed(&mut exec).expect("six exact direct observations produce one complete guess");
    assert_eq!(result.len(), 6);
    for (index, expected) in [(0, 32), (2, 0), (3, 0), (4, 65), (5, 0)] {
        let TermData::Const(Constant::BitVec { value, .. }) = exec.ctx.terms.get(result[index])
        else {
            panic!("closed scalar");
        };
        assert_eq!(value, &BigInt::from(expected));
    }
    assert_eq!(
        flat(exec.ctx.terms.sort(result[1])),
        Some(FlatSort::Array(64, 8))
    );
    assert_eq!(
        exec.ctx.assertions, roots,
        "candidate nomination never edits authored roots"
    );
    assert!(
        certify(&mut exec).is_some(),
        "only all-original-root certification installs a witness"
    );
}

#[test]
fn missing_observations_and_malformed_present_values_decline_without_fallback() {
    for index in 0..6 {
        let mut exec = prepared(true);
        let ids = pin_fixture(&mut exec);
        exec.last_model
            .as_mut()
            .unwrap()
            .bv_model
            .as_mut()
            .unwrap()
            .values
            .remove(&ids[index]);
        assert!(
            seed(&mut exec).is_none(),
            "missing observation for {} must decline",
            HEADS[index]
        );
        assert!(exec.const_interp_cert_witness_state.is_none());
    }
    for bad in [
        BigInt::from(-1),
        BigInt::from(256),
        BigInt::from(1) << 100_000usize,
    ] {
        let mut exec = prepared(true);
        let ids = pin_fixture(&mut exec);
        let model = exec.last_model.as_mut().unwrap();
        model.bv_model.as_mut().unwrap().values.insert(ids[3], bad);
        model.completed_values.insert(
            ids[3],
            EvalValue::BitVec {
                value: BigInt::from(0),
                width: 8,
            },
        );
        assert!(
            seed(&mut exec).is_none(),
            "a malformed present raw pin cannot use a valid fallback"
        );
    }
    let mut exec = prepared(true);
    let ids = pin_fixture(&mut exec);
    exec.last_model
        .as_mut()
        .unwrap()
        .bv_model
        .as_mut()
        .unwrap()
        .term_to_bits
        .insert(ids[3], Vec::new());
    assert!(
        seed(&mut exec).is_none(),
        "present bit-row width must agree exactly"
    );
}

#[test]
fn primitive_completion_is_only_a_missing_nullary_bv_fallback() {
    let mut exec = prepared(true);
    let ids = pin_fixture(&mut exec);
    let model = exec.last_model.as_mut().unwrap();
    model.bv_model.as_mut().unwrap().values.remove(&ids[4]);
    model.completed_values.insert(
        ids[4],
        EvalValue::BitVec {
            value: BigInt::from(65),
            width: 64,
        },
    );
    assert!(seed(&mut exec).is_some());
    let model = exec.last_model.as_mut().unwrap();
    model.completed_values.insert(
        ids[4],
        EvalValue::BitVec {
            value: BigInt::from(65),
            width: 8,
        },
    );
    assert!(
        seed(&mut exec).is_none(),
        "completed width is exact, not just a range check"
    );
    for index in [1, 2] {
        let mut exec = prepared(true);
        let ids = pin_fixture(&mut exec);
        let model = exec.last_model.as_mut().unwrap();
        model.bv_model.as_mut().unwrap().values.remove(&ids[index]);
        model.completed_values.insert(
            ids[index],
            EvalValue::BitVec {
                value: BigInt::from(0),
                width: 8,
            },
        );
        assert!(
            seed(&mut exec).is_none(),
            "no completed UF or array-point recovery"
        );
    }
}

#[test]
fn conflicting_raw_guesses_cannot_bypass_any_original_root() {
    for (index, wrong) in [(0, 0), (1, 1), (2, 1), (3, 1), (4, 64)] {
        let mut exec = prepared(true);
        let ids = pin_fixture(&mut exec);
        let width = exec.ctx.terms.sort(ids[index]).bitvec_width().unwrap();
        let model = exec.last_model.as_mut().unwrap();
        let correct = model.bv_model.as_ref().unwrap().values[&ids[index]].clone();
        model.completed_values.insert(
            ids[index],
            EvalValue::BitVec {
                value: correct,
                width,
            },
        );
        model
            .bv_model
            .as_mut()
            .unwrap()
            .values
            .insert(ids[index], BigInt::from(wrong));
        assert!(
            seed(&mut exec).is_some(),
            "well-typed raw observations remain untrusted guesses"
        );
        assert!(
            certify(&mut exec).is_none(),
            "{} disagreement must lose at whole-source certification",
            HEADS[index]
        );
        assert!(exec.const_interp_cert_witness_state.is_none());
    }
    let mut original = prepared(false);
    pin_fixture(&mut original);
    assert!(
        certify(&mut original).is_none(),
        "matching cells falsify the original counterexample root"
    );
    let mut incompatible = prepared(true);
    incompatible
        .execute_all(&ay_frontend::parse("(assert (= (f false x) #x01))").unwrap())
        .unwrap();
    pin_fixture(&mut incompatible);
    assert!(
        seed(&mut incompatible).is_some(),
        "a sampled point does not prove a constant function"
    );
    assert!(
        certify(&mut incompatible).is_none(),
        "every additional original ground point is an obligation"
    );
}

#[test]
fn second_pass_and_legacy_small_head_envelope_do_not_use_the_seed() {
    let mut exec = prepared(true);
    pin_fixture(&mut exec);
    let roots = exec.ctx.assertions.clone();
    assert!(exec
        .const_interp_cert_inner(
            &roots,
            crate::logic_detection::LogicCategory::QfBvLiaIndep,
            super::super::ConstInterpCertMode::On,
            ay_core::time::Instant::now() + Duration::from_secs(2),
            super::super::ConstInterpCandidateSource::WithProblemConstants,
            &mut Default::default(),
        )
        .is_none());
    let mut small = Executor::new();
    // A bare `forall q. f(q) = 0` is adopted as a definitional macro before
    // this certificate runs. Unsigned `f(q) <= 0` expresses the same BV8
    // constraint but keeps one genuine uninterpreted head for this route.
    small.execute_all(&ay_frontend::parse("(set-logic ALL) (declare-fun f ((_ BitVec 8)) (_ BitVec 8)) (assert (forall ((q (_ BitVec 8))) (bvule (f q) #x00)))").unwrap()).unwrap();
    assert_eq!(small.ctx.assertions.len(), 1);
    assert!(small.ctx.adopted_macro_interp("f").is_none());
    let TermData::Forall(_, body, _) = small.ctx.terms.get(small.ctx.assertions[0]) else {
        panic!("legacy certificate fixture must retain its forall");
    };
    assert!(
        matches!(small.ctx.terms.get(*body), TermData::App(Symbol::Named(name), arguments)
            if name.as_str() == "bvule" && arguments.len() == 2),
        "the original body must remain a live BV comparison, not a folded constant"
    );
    assert!(small.last_model.is_none());
    assert!(
        certify(&mut small).is_some(),
        "legacy one-head fixed-family grant still needs no observations"
    );
}
