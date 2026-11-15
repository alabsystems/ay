// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Model-value regression tests included in `independent_gate::tests` so their
// fully-qualified test names remain stable.

/// COMPLETION-ORDERING REGRESSION (#array-completion-order, seed 21453).
///
/// A witness that VALIDATES under the gate's evaluator but is EMITTED with a
/// different value is an invalid witness. The concrete class: a combined
/// AUFLIA solve commits an Int variable's value to the arithmetic (LIA)
/// model, while a STALE value survives in the merged EUF `term_values` map.
/// `evaluate_var` — the value the gate checks — resolves LIA-FIRST (so the
/// gate validated `i = 0`), but `(get-model)` used to read the merged EUF
/// map FIRST for EVERY sort, so it printed the stale EUF value `-2`. The
/// emitted model then FALSIFIED the formula (`(= 0 i)` became `(= 0 -2)`)
/// even though the gate had confirmed the LIA witness. `(get-model)` now
/// skips the EUF map for Int/Real, so an arithmetic variable prints the same
/// LIA/LRA value the gate validated — emit stays faithful to validation.
#[test]
fn get_model_int_prefers_lia_over_stale_euf_term_value() {
    let (mut exec, outputs) =
        solved("(set-logic QF_UFLIA)(declare-fun i () Int)(assert (<= i i))(check-sat)");
    assert_eq!(outputs[0], "sat");
    let i = exec.ctx.terms.mk_var("i", Sort::Int);

    // The validated model commits `i = 0` in LIA; a STALE EUF entry says -2.
    let mut lia = DetHashMap::default();
    lia.insert(i, BigInt::from(0));
    let mut euf = ay_euf::EufModel::default();
    euf.term_values.insert(i, "-2".to_string());
    exec.last_model = Some(Model {
        quantified_confirmation_seal: Default::default(),
        quantified_grant_model_seal: Default::default(),
        sat_model: vec![],
        term_to_var: DetHashMap::default(),
        bool_overrides: DetHashMap::default(),
        euf_model: Some(euf),
        materialized_scalar_functions: Default::default(),
        array_model: None,
        lra_model: None,
        lia_model: Some(LiaModel { values: lia }),
        bv_model: None,
        fp_model: None,
        string_model: None,
        seq_model: None,
        projection_ufs: Default::default(),
        certified_total_ufs: Default::default(),
        certified_const_interps: Default::default(),
        formula_neutral_function_defaults: Default::default(),
        completed_values: DetHashMap::default(),
        field_assignments: Default::default(),
        dt_ground: DetHashMap::default(),
        dt_pins: DetHashMap::default(),
        dt_array_field_classes: Vec::new(),
        residual_arrays: None,
        functional_arrays: None,
        _scalar_candidate_memory: None,
        construction_owner: None,
    });
    exec.last_result = Some(SolveResult::Sat);

    let model_str = exec.model();
    assert!(
        model_str.contains("i () Int 0"),
        "get-model must emit the gate-validated LIA value 0 (LIA-first, like \
             evaluate_var), not the stale merged-EUF value; got: {model_str}"
    );
    assert!(
        !model_str.contains("(- 2)"),
        "get-model must NOT emit the stale merged-EUF value -2; got: {model_str}"
    );
}

/// A ∀∃ alternation whose truth depends on the EMITTED VALUE of a model
/// constant. `∀x:Int. ∃y:Int. (y = 1 ∧ x·y ≥ x + c)` forces `y := 1`, so
/// the alternation says exactly `c ≤ 0` (z3 5.0.0 differential, measured:
/// `sat` with `(= c 0)`, `unsat` with `(= c 5)`).
///
/// It is deliberately NONLINEAR (`x·y`) so `deep_qe` cannot eliminate the
/// alternation and the general route stays non-decisive — the ∀∃ witness
/// route is the only lane that can decide it.
const FORALL_EXISTS_MODEL_SENSITIVE: &str = "(set-logic NIA)\
         (declare-fun c () Int)\
         (assert (forall ((x Int)) (exists ((y Int)) (and (= y 1) (>= (* x y) (+ x c))))))";

/// Load [`FORALL_EXISTS_MODEL_SENSITIVE`] and publish `c := value` as the
/// emitted witness, with NO `check-sat` — the gate is exercised on a model
/// this test chose, so the two legs below differ in the MODEL alone.
#[cfg(test)]
fn forall_exists_gate_with_c(value: i64) -> Executor {
    let commands = parse(FORALL_EXISTS_MODEL_SENSITIVE).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("execute succeeds");
    let c = exec.ctx.terms.mk_var("c", Sort::Int);
    exec.last_model = Some(synthetic_lia_model(&[(c, value)]));
    exec
}

/// THE NON-VACUITY BAR for the ∀∃ witness route.
///
/// A confirm that did not actually evaluate the quantified body under the
/// emitted model would pass the first leg and the second one too. This
/// test holds the FORMULA and the CODE PATH fixed and varies only the
/// model:
///
/// * `c = 0` — the synthesised witness `y := 1` reduces the conjunct to
///   the ground obligation `¬(sk·1 ≥ sk + 0)`, which is UNSAT, so the gate
///   CONFIRMS and the `Sat` survives with the quantified-gate marker;
/// * `c = 5` — the same witness yields `¬(sk·1 ≥ sk + 5)`, which is
///   SATISFIABLE, no other candidate discharges, and the gate fails closed
///   to `Unknown`.
///
/// The second leg is a MUTANT MODEL the gate must reject, and does.
#[test]
fn forall_exists_witness_route_confirm_is_model_sensitive() {
    let mut honest = forall_exists_gate_with_c(0);
    assert_eq!(
        honest.apply_quantified_model_failclosed_gate(SolveResult::Sat),
        SolveResult::Sat,
        "the ∀∃ witness route must confirm the alternation under c = 0"
    );
    assert_eq!(
        honest
            .last_statistics
            .get_string("model_check_gate.quantified"),
        Some("confirmed"),
        "the Sat must survive because the QUANTIFIED gate confirmed the \
             alternation — not because some lane bypassed it"
    );

    let mut mutant = forall_exists_gate_with_c(5);
    assert_eq!(
        mutant.apply_quantified_model_failclosed_gate(SolveResult::Sat),
        SolveResult::Unknown,
        "a model that FALSIFIES the alternation must never be confirmed"
    );
    assert_ne!(
        mutant
            .last_statistics
            .get_string("model_check_gate.quantified"),
        Some("confirmed"),
        "the mutant model must not be recorded as a quantified-gate confirm"
    );
}

/// The witness route is CONFIRM-ONLY over a genuinely quantifier-free
/// obligation: it must decline when no candidate term witnesses the
/// existential. `∀x:Int. ∃y:Int. (y ≤ x ∧ y ≥ x+1)` is FALSE for every
/// `x`, so every candidate leaves the negated obligation satisfiable and
/// the gate must fail closed even though the sentence is closed and
/// alternating — the same shape the route confirms above.
#[test]
fn forall_exists_witness_route_declines_when_no_witness_exists() {
    let commands = parse(
        "(set-logic NIA)\
             (assert (forall ((x Int)) (exists ((y Int)) \
                (and (<= y x) (>= y (+ x 1)) (>= (* x x) 0)))))",
    )
    .expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("execute succeeds");
    exec.last_model = Some(synthetic_lia_model(&[]));
    assert_eq!(
        exec.apply_quantified_model_failclosed_gate(SolveResult::Sat),
        SolveResult::Unknown,
        "an unwitnessable ∀∃ must never be confirmed by the witness route"
    );
}

#[cfg(test)]
fn fp_value(sign: bool, exponent: u64, significand: u128, eb: u32, sb: u32) -> ModelValue {
    ModelValue::FloatingPoint {
        sign,
        exponent,
        significand,
        exponent_bits: eb,
        significand_bits: sb,
    }
}

/// The minted literal must READ BACK as exactly the value it pins — that
/// round trip is the whole reason a wrong pin cannot manufacture a
/// confirmation. Checked on the classes whose bits differ only in ways an
/// approximate conversion would erase.
#[test]
fn fp_pin_literal_round_trips_bit_for_bit() {
    let mut terms = TermStore::new();
    let sort = Sort::FloatingPoint(8, 24);
    for mv in [
        fp_value(false, 0, 0, 8, 24),         // +zero
        fp_value(true, 0, 0, 8, 24),          // -zero
        fp_value(false, 127, 0, 8, 24),       // 1.0
        fp_value(true, 0, 1, 8, 24),          // -smallest subnormal
        fp_value(false, 255, 0, 8, 24),       // +oo
        fp_value(true, 255, 0, 8, 24),        // -oo
        fp_value(false, 255, 1 << 22, 8, 24), // quiet NaN
        fp_value(true, 255, 0x2b, 8, 24),     // NaN, sign + payload set
    ] {
        let term =
            fp_model_value_to_literal(&mut terms, &mv, &sort).expect("Float32 value is exact");
        let TermData::App(sym, args) = terms.get(term).clone() else {
            panic!("expected an `fp` application");
        };
        assert_eq!(sym.name(), "fp");
        let fields: Vec<ModelValue> = args
            .iter()
            .map(|&a| match terms.get(a) {
                TermData::Const(ay_core::term::Constant::BitVec { value, width }) => {
                    ModelValue::BitVec {
                        width: *width,
                        value: value.clone(),
                    }
                }
                other => panic!("expected a bitvector field, got {other:?}"),
            })
            .collect();
        let back = ay_model_check::fp::from_field_bitvectors(&fields)
            .expect("the minted fields must re-read");
        let (ModelValue::FloatingPoint { .. }, ModelValue::FloatingPoint { .. }) = (&mv, &back)
        else {
            panic!("round trip changed the value kind");
        };
        let key = |v: &ModelValue| match v {
            ModelValue::FloatingPoint {
                sign,
                exponent,
                significand,
                exponent_bits,
                significand_bits,
            } => (
                *sign,
                *exponent,
                *significand,
                *exponent_bits,
                *significand_bits,
            ),
            _ => unreachable!(),
        };
        assert_eq!(key(&mv), key(&back), "minted literal is not the same value");
    }
    // +0 and -0 must not collapse onto one term.
    let pos = fp_model_value_to_literal(&mut terms, &fp_value(false, 0, 0, 8, 24), &sort);
    let neg = fp_model_value_to_literal(&mut terms, &fp_value(true, 0, 0, 8, 24), &sort);
    assert_ne!(pos, neg, "+zero and -zero must pin to DISTINCT literals");
}

/// Everything the arm cannot mint bit-exactly must return `None`, which
/// leaves the leaf free and clears `total` — today's fail-closed
/// behaviour, never a plausible neighbouring value.
#[test]
fn fp_pin_literal_fails_closed_off_format() {
    let mut terms = TermStore::new();
    // Value's format disagrees with the leaf's sort.
    assert!(fp_model_value_to_literal(
        &mut terms,
        &fp_value(false, 0, 0, 11, 53),
        &Sort::FloatingPoint(8, 24)
    )
    .is_none());
    // Exponent field wider than its declared width.
    assert!(fp_model_value_to_literal(
        &mut terms,
        &fp_value(false, 256, 0, 8, 24),
        &Sort::FloatingPoint(8, 24)
    )
    .is_none());
    // Significand field wider than its declared width.
    assert!(fp_model_value_to_literal(
        &mut terms,
        &fp_value(false, 0, 1 << 23, 8, 24),
        &Sort::FloatingPoint(8, 24)
    )
    .is_none());
    // A fraction wider than the physical carrier cannot be pinned exactly.
    assert!(fp_model_value_to_literal(
        &mut terms,
        &fp_value(false, 0, 0, 15, 130),
        &Sort::FloatingPoint(15, 130)
    )
    .is_none());
    // Not a floating-point value at all.
    assert!(fp_model_value_to_literal(
        &mut terms,
        &ModelValue::Bool(true),
        &Sort::FloatingPoint(8, 24)
    )
    .is_none());
}

/// THE BARRIER FOR THE LOAD-BEARING ARM. Review found that reverting the
/// `ModelValue::FloatingPoint` arm of `model_value_to_pin_term` to `None`
/// — undoing every one of the ~490 verdicts this change publishes — left
/// the whole suite green, because the two FP tests call
/// `fp_model_value_to_literal` DIRECTLY and never reach the dispatcher.
/// This test enters through `model_value_to_pin_term`, so a no-op arm
/// fails it.
///
/// The property that matters is not merely "returns Some": it is that the
/// pin is a CLOSED FP LITERAL the nested solve cannot reinterpret. An
/// opaque element would let the solve pick a different float and confirm a
/// model that says something else — which is how a wrong `sat` would be
/// manufactured here.
#[test]
fn fp_leaf_pins_through_the_dispatcher_to_a_closed_literal() {
    let mut terms = TermStore::new();
    let mut elems = QuantifiedGateElements::default();
    let sort = Sort::FloatingPoint(8, 24);
    // +0.0f32: sign 0, exponent 0x00, significand 0.
    let value = ModelValue::FloatingPoint {
        sign: false,
        exponent: 0,
        significand: 0,
        exponent_bits: 8,
        significand_bits: 24,
    };
    let term = model_value_to_pin_term(&mut terms, &value, &sort, &mut elems, None)
        .expect("an FP model value must pin through the dispatcher");
    // It must NOT be an opaque uninterpreted element.
    assert!(
        elems.by_token.is_empty(),
        "an FP leaf must pin to a literal, never mint an opaque gate element"
    );
    // And the pinned term must be closed: no free variables to reinterpret.
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        match terms.get(t).clone() {
            TermData::Var(..) => panic!("FP pin must be closed, found a variable"),
            TermData::App(_, args) => stack.extend(args),
            _ => {}
        }
    }
}

#[test]
fn binary128_pin_dispatch_preserves_all_literal_fields() {
    let mut terms = TermStore::new();
    let mut elems = QuantifiedGateElements::default();
    let sort = Sort::FloatingPoint(15, 113);
    let fraction = (1u128 << 111) | (1u128 << 64) | (1u128 << 63) | 1;
    let mut pins = Vec::new();
    for (sign, exponent, significand) in [
        (false, 0, 0),
        (true, 0, 0),
        (false, 0x3fff, fraction),
        (true, 0x3fff, fraction),
        (false, 0, 1),
        (true, 0x7ffe, (1u128 << 112) - 1),
        (false, 0x7fff, 0),
        (true, 0x7fff, fraction), // Literal NaN sign/payload must not be normalized.
    ] {
        let value = fp_value(sign, exponent, significand, 15, 113);
        let pin = model_value_to_pin_term(&mut terms, &value, &sort, &mut elems, None)
            .expect("binary128 must reach the exact dispatcher arm");
        assert_eq!(terms.sort(pin), &sort);
        let TermData::App(symbol, args) = terms.get(pin) else {
            panic!("expected a closed fp literal");
        };
        assert_eq!(symbol.name(), "fp");
        assert_eq!(args.len(), 3);
        let mut fields = Vec::new();
        for (&arg, (expected, width)) in args.iter().zip([
            (u128::from(u8::from(sign)), 1),
            (u128::from(exponent), 15),
            (significand, 112),
        ]) {
            let TermData::Const(ay_core::term::Constant::BitVec {
                value,
                width: actual,
            }) = terms.get(arg)
            else {
                panic!("an FP field must be a constant, not a free pin");
            };
            assert_eq!((*actual, value), (width, &BigInt::from(expected)));
            fields.push(ModelValue::BitVec {
                width,
                value: value.clone(),
            });
        }
        let ModelValue::FloatingPoint {
            sign: s,
            exponent: e,
            significand: m,
            exponent_bits: eb,
            significand_bits: sb,
        } = ay_model_check::fp::from_field_bitvectors(&fields).unwrap()
        else {
            panic!("independent literal reader changed the value kind");
        };
        assert_eq!((s, e, m, eb, sb), (sign, exponent, significand, 15, 113));
        pins.push(pin);
    }
    assert_ne!(pins[0], pins[1], "the sign of zero must survive the pin");
    assert!(
        elems.by_token.is_empty(),
        "no opaque elements may substitute for FP fields"
    );
}

#[test]
fn binary128_pin_refuses_bad_fields_without_interning_a_replacement() {
    let mut terms = TermStore::new();
    let mut elems = QuantifiedGateElements::default();
    for (value, sort) in [
        (
            fp_value(false, 1 << 15, 0, 15, 113),
            Sort::FloatingPoint(15, 113),
        ),
        (
            fp_value(false, 0, 1u128 << 112, 15, 113),
            Sort::FloatingPoint(15, 113),
        ),
        (
            fp_value(false, 0, u128::MAX, 15, 113),
            Sort::FloatingPoint(15, 113),
        ),
        (fp_value(false, 0, 1, 15, 113), Sort::FloatingPoint(11, 53)),
        (fp_value(false, 0, 1, 15, 113), Sort::Bool),
        // The fixed carrier ends at 128 stored fraction bits. Wider data
        // belongs in FloatingPointExact, whose controlled pin path is separate.
        (fp_value(false, 0, 0, 15, 130), Sort::FloatingPoint(15, 130)),
        (
            fp_value(false, 0, 0, 15, ay_fp::MAX_ENCODING_SIGNIFICAND_BITS + 1),
            Sort::FloatingPoint(15, ay_fp::MAX_ENCODING_SIGNIFICAND_BITS + 1),
        ),
        (fp_value(false, 0, 0, 64, 114), Sort::FloatingPoint(64, 114)),
        (fp_value(false, 0, 0, 15, 0), Sort::FloatingPoint(15, 0)),
    ] {
        let before = terms.len();
        assert!(fp_model_value_to_literal(&mut terms, &value, &sort).is_none());
        assert!(model_value_to_pin_term(&mut terms, &value, &sort, &mut elems, None).is_none());
        assert_eq!(
            terms.len(),
            before,
            "refusal must not mint a neighboring literal"
        );
        assert!(elems.by_token.is_empty());
    }
}

#[test]
fn fp_pin_preserves_native_129_bit_format_and_full_fraction() {
    let mut terms = TermStore::new();
    let mut elems = QuantifiedGateElements::default();
    let sort = Sort::FloatingPoint(15, 129);
    let value = fp_value(true, 127, u128::MAX, 15, 129);
    let pin = model_value_to_pin_term(&mut terms, &value, &sort, &mut elems, None).unwrap();
    let ay_core::TermData::App(_, fields) = terms.get(pin) else {
        panic!("an FP pin must retain its three fields");
    };
    assert_eq!(fields.len(), 3);
    for (&field, (expected, width)) in fields.iter().zip([(1u128, 1), (127, 15), (u128::MAX, 128)])
    {
        let ay_core::TermData::Const(ay_core::Constant::BitVec {
            value,
            width: actual,
        }) = terms.get(field)
        else {
            panic!("an FP field must be an exact bitvector");
        };
        assert_eq!((*actual, value), (width, &BigInt::from(expected)));
    }
    assert!(elems.by_token.is_empty());
}

/// A `RoundingMode` leaf must pin to the MODE, not to an opaque gate
/// element the nested solve is free to reinterpret.
#[test]
fn rounding_mode_pins_to_the_literal_not_an_opaque_element() {
    let mut terms = TermStore::new();
    let mut elems = QuantifiedGateElements::default();
    let sort = Sort::Uninterpreted("RoundingMode".to_string());
    for (token, short) in [
        ("roundNearestTiesToEven", "RNE"),
        ("RNE", "RNE"),
        ("roundTowardZero", "RTZ"),
        ("RTP", "RTP"),
    ] {
        let term = model_value_to_pin_term(
            &mut terms,
            &ModelValue::Uninterpreted(token.to_string()),
            &sort,
            &mut elems,
            None,
        )
        .expect("a named rounding mode is exactly expressible");
        let TermData::App(sym, args) = terms.get(term).clone() else {
            panic!("expected a nullary rounding-mode application");
        };
        assert_eq!(sym.name(), short);
        assert!(args.is_empty());
    }
    assert!(
        elems.by_token.is_empty(),
        "no opaque element constant may be minted for a rounding mode"
    );
    // A token that names no mode fails closed rather than inventing one.
    assert!(model_value_to_pin_term(
        &mut terms,
        &ModelValue::Uninterpreted("@RoundingMode!0".to_string()),
        &sort,
        &mut elems,
        None,
    )
    .is_none());
}
