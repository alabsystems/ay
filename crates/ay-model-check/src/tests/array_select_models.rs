// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `tests` to preserve test FQNs.

#[test]
fn array_select_seed21011_distinct_indices_equal_reads_refute() {
    // The seed-21011 shape: `(< (select A0 idx1) (select A0 idx2))` with DISTINCT
    // index values (idx1 = 0, idx2 = -5) that the model reads to the SAME element
    // (both 1). The array leaf A0 is NOT reconstructable (unpinned), so the gate
    // reads each `select` through the model; the two reads key differently
    // (distinct index values) and keep their committed value 1, so `(< 1 1)` is
    // `false` — a caught wrong witness. Pinning that array model into z3 is
    // UNSAT; the gate demotes the `sat` to `unknown`.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let a0 = ts.mk_var("A0", asort); // deliberately unpinned as a leaf
    let idx1 = ts.mk_int(int(0));
    let idx2 = ts.mk_int(int(-5));
    let sel1 = app(&mut ts, "select", &[a0, idx1], Sort::Int);
    let sel2 = app(&mut ts, "select", &[a0, idx2], Sort::Int);
    let lt = app(&mut ts, "<", &[sel1, sel2], Sort::Bool);
    let m = ArraySelectStubModel::new()
        .sel(sel1, ModelValue::Int(int(1)))
        .sel(sel2, ModelValue::Int(int(1)));
    assert_violates(&verdict(&ts, &m, &[lt]));
}

#[test]
fn array_select_collapsed_indices_refute_strict_inequality() {
    // Collapse analogue of the UF case: two reads of the SAME array A0 at index
    // values that COINCIDE (i = 0 and 3*i = 0) must denote the same element, yet
    // the model pins them to different values (5 and 7). The gate collapses them
    // to one value (first-wins), so `(> read read)` is `false`. Honouring the
    // per-read pins (7 > 5) would confirm an internally-inconsistent array model;
    // the value-keyed graph exposes it instead.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let a0 = ts.mk_var("A0", asort); // unpinned leaf
    let i = ts.mk_var("i", Sort::Int);
    let three = ts.mk_int(int(3));
    let mul = app(&mut ts, "*", &[three, i], Sort::Int); // 3*i = 0
    let sel_lo = app(&mut ts, "select", &[a0, i], Sort::Int); // A0[i]
    let sel_hi = app(&mut ts, "select", &[a0, mul], Sort::Int); // A0[3*i]
    let gt = app(&mut ts, ">", &[sel_hi, sel_lo], Sort::Bool);
    let m = ArraySelectStubModel::new()
        .leaf(i, ModelValue::Int(int(0)))
        .sel(sel_hi, ModelValue::Int(int(7)))
        .sel(sel_lo, ModelValue::Int(int(5)));
    assert_violates(&verdict(&ts, &m, &[gt]));
}

#[test]
fn array_select_equal_cross_extension_indices_fail_closed() {
    // These two exact algebraic index values both denote +sqrt(2), but their
    // root objects use different isolating intervals. After the first read
    // fixes A[sqrt(2)] = 5, an undecidable representation-level comparison at
    // the second read cannot authorize a separate A[sqrt(2)] = 7 entry.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Real, Sort::Int);
    let array = ts.mk_var("A", asort); // deliberately unreconstructable
    let left_index = ts.mk_var("left-index", Sort::Real);
    let right_index = ts.mk_var("right-index", Sort::Real);
    let left_read = app(&mut ts, "select", &[array, left_index], Sort::Int);
    let right_read = app(&mut ts, "select", &[array, right_index], Sort::Int);
    let model = ArraySelectStubModel::new()
        .leaf(
            left_index,
            sqrt_two_between(
                BigRational::from_integer(int(1)),
                BigRational::from_integer(int(2)),
            ),
        )
        .leaf(
            right_index,
            sqrt_two_between(
                BigRational::new(int(4), int(3)),
                BigRational::new(int(3), int(2)),
            ),
        )
        .sel(left_read, ModelValue::Int(int(5)))
        .sel(right_read, ModelValue::Int(int(7)));
    let evaluator = Evaluator::new(&ts, &model);

    assert!(matches!(
        evaluator.evaluate(left_read),
        EvalOutcome::Value(ModelValue::Int(value)) if value == int(5)
    ));
    match evaluator.evaluate(right_read) {
        EvalOutcome::Unevaluable(reason) => {
            assert!(reason.contains("cannot decide congruence-key equality"));
            assert!(reason.contains("algebraic equality across different extensions"));
        }
        other => panic!("ambiguous second array key must fail closed, got {other:?}"),
    }
}

#[test]
fn array_select_via_model_distinct_reads_confirm_valid_model() {
    // NO OVER-REFUTATION: distinct index values (a = 5, b = 7) key the two reads
    // differently, so each keeps its own committed value (A0[a] = 1 > A0[b] = 0)
    // and the witness is CONFIRMED. The select-via-model fallback must not
    // over-refute a genuinely-valid array model.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let a0 = ts.mk_var("A0", asort);
    let a = ts.mk_var("a", Sort::Int);
    let b = ts.mk_var("b", Sort::Int);
    let sel_a = app(&mut ts, "select", &[a0, a], Sort::Int);
    let sel_b = app(&mut ts, "select", &[a0, b], Sort::Int);
    let gt = app(&mut ts, ">", &[sel_a, sel_b], Sort::Bool);
    let m = ArraySelectStubModel::new()
        .leaf(a, ModelValue::Int(int(5)))
        .leaf(b, ModelValue::Int(int(7)))
        .sel(sel_a, ModelValue::Int(int(1)))
        .sel(sel_b, ModelValue::Int(int(0)));
    assert_confirmed(&verdict(&ts, &m, &[gt]));
}

#[test]
fn array_select_coincident_reads_confirm_when_consistent() {
    // NO OVER-REFUTATION under coincidence: two reads of the same array at
    // coinciding index values (i = 0, 3*i = 0) that the model pins CONSISTENTLY
    // (both 4). `(= A0[i] A0[3*i])` is `(= 4 4)` = true — the single-valuedness
    // collapse yields the shared value, not a spurious violation.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let a0 = ts.mk_var("A0", asort);
    let i = ts.mk_var("i", Sort::Int);
    let three = ts.mk_int(int(3));
    let mul = app(&mut ts, "*", &[three, i], Sort::Int);
    let sel_lo = app(&mut ts, "select", &[a0, i], Sort::Int);
    let sel_hi = app(&mut ts, "select", &[a0, mul], Sort::Int);
    let eq = app(&mut ts, "=", &[sel_lo, sel_hi], Sort::Bool);
    let m = ArraySelectStubModel::new()
        .leaf(i, ModelValue::Int(int(0)))
        .sel(sel_lo, ModelValue::Int(int(4)))
        .sel(sel_hi, ModelValue::Int(int(4)));
    assert_confirmed(&verdict(&ts, &m, &[eq]));
}

#[test]
fn array_select_unpinned_read_cannot_confirm() {
    // If neither the array leaf NOR the per-read value is pinned, the `select` is
    // unevaluable and the gate fails closed (never assumed) — CannotConfirm.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let a0 = ts.mk_var("A0", asort);
    let a = ts.mk_var("a", Sort::Int);
    let sel = app(&mut ts, "select", &[a0, a], Sort::Int);
    let zero = ts.mk_int(int(0));
    let gt = app(&mut ts, ">", &[sel, zero], Sort::Bool);
    let m = ArraySelectStubModel::new().leaf(a, ModelValue::Int(int(5))); // no select pin
    assert_cannot(&verdict(&ts, &m, &[gt]));
}

#[test]
fn array_select_reconstructable_leaf_still_uses_structural_path() {
    // When the array leaf IS reconstructable (pinned as a concrete array value),
    // the structural path handles the read and the model's per-read pins are
    // IGNORED — even a contradictory per-read pin cannot override the real array.
    // `(= (select A0 1) 9)` with A0 = const-0 is `(= 0 9)` = false (structural),
    // regardless of a bogus `array_select_value` pin of 9.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let a0 = ts.mk_var("A0", asort);
    let one = ts.mk_int(int(1));
    let nine = ts.mk_int(int(9));
    let sel = app(&mut ts, "select", &[a0, one], Sort::Int);
    let eq = app(&mut ts, "=", &[sel, nine], Sort::Bool);
    let m = ArraySelectStubModel::new()
        .leaf(
            a0,
            ModelValue::Array(Box::new(ArrayValue {
                default: ModelValue::Int(int(0)),
                store: vec![],
            })),
        )
        .sel(sel, ModelValue::Int(int(9))); // bogus pin — must be ignored
    assert_violates(&verdict(&ts, &m, &[eq]));
}

#[test]
fn seed21425_shape_emitted_array_model_is_refuted() {
    // Exact seed-21425 shape (arrays fuzz) with the INVALID array model AY
    // emitted (its get-model output pins UNSAT in z3). Given that emitted model
    // as leaf values, the gate's array-`select` evaluation ground-falsifies AY's
    // own assertion — `(= -5 (select A0 -5))` is `(= -5 0)` under the emitted
    // A0 = store(const 0, -3, 2) — and reports ModelViolates. This localizes the
    // (separate, deeper) AUFLIA residual to model RECONSTRUCTION/COMPLETION: the
    // gate's evaluation is correct; the emitted array's default is simply not
    // present in `array_model` at gate time (see report).
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let a0 = ts.mk_var("A0", asort.clone());
    let a1 = ts.mk_var("A1", asort.clone());
    let a2 = ts.mk_var("A2", asort.clone());
    let i0 = ts.mk_var("i0", Sort::Int);
    let i1 = ts.mk_var("i1", Sort::Int);
    let i2 = ts.mk_var("i2", Sort::Int);
    let i3 = ts.mk_var("i3", Sort::Int);
    let b0 = ts.mk_var("b0", Sort::Bool);
    let n5 = ts.mk_int(int(-5));
    let n3 = ts.mk_int(int(-3));
    let n2 = ts.mk_int(int(-2));
    let two = ts.mk_int(int(2));
    let five = ts.mk_int(int(5));
    let six = ts.mk_int(int(6));
    let c24 = ts.mk_int(int(24));
    let four = ts.mk_int(int(4));
    // D1 = (< (select (store (store A0 -2 (- i1)) 6 i0) (+ i2 6)) (+ i0 (- i3)))
    let neg_i1 = app(&mut ts, "-", &[i1], Sort::Int);
    let s1 = app(&mut ts, "store", &[a0, n2, neg_i1], asort.clone());
    let s2 = app(&mut ts, "store", &[s1, six, i0], asort.clone());
    let i2p6 = app(&mut ts, "+", &[i2, six], Sort::Int);
    let sel_d1 = app(&mut ts, "select", &[s2, i2p6], Sort::Int);
    let neg_i3 = app(&mut ts, "-", &[i3], Sort::Int);
    let i0mi3 = app(&mut ts, "+", &[i0, neg_i3], Sort::Int);
    let d1 = app(&mut ts, "<", &[sel_d1, i0mi3], Sort::Bool);
    // A2eq = (= -5 (select A0 -5))
    let sel_a0m5 = app(&mut ts, "select", &[a0, n5], Sort::Int);
    let a2eq = app(&mut ts, "=", &[n5, sel_a0m5], Sort::Bool);
    // NEQ = (not (= (select A0 -3) (select (store (store A1 6 2) i0 (ite (<= 24 (+ i1 i3)) -3 i0)) i3)))
    let sel_a0m3 = app(&mut ts, "select", &[a0, n3], Sort::Int);
    let a1s1 = app(&mut ts, "store", &[a1, six, two], asort.clone());
    let i1pi3 = app(&mut ts, "+", &[i1, i3], Sort::Int);
    let le = app(&mut ts, "<=", &[c24, i1pi3], Sort::Bool);
    let ite = ts.mk_ite(le, n3, i0);
    let a1s2 = app(&mut ts, "store", &[a1s1, i0, ite], asort.clone());
    let sel_a1 = app(&mut ts, "select", &[a1s2, i3], Sort::Int);
    let eqn = app(&mut ts, "=", &[sel_a0m3, sel_a1], Sort::Bool);
    let neq = ts.mk_not(eqn);
    // C1 = (< (select A2 (+ i2 2)) (select A2 5))
    let i2p2 = app(&mut ts, "+", &[i2, two], Sort::Int);
    let sel_a2a = app(&mut ts, "select", &[a2, i2p2], Sort::Int);
    let sel_a2b = app(&mut ts, "select", &[a2, five], Sort::Int);
    let c1 = app(&mut ts, "<", &[sel_a2a, sel_a2b], Sort::Bool);
    // C2 = (< (select A2 i3) (select A1 4))
    let sel_a2c = app(&mut ts, "select", &[a2, i3], Sort::Int);
    let sel_a1b = app(&mut ts, "select", &[a1, four], Sort::Int);
    let c2 = app(&mut ts, "<", &[sel_a2c, sel_a1b], Sort::Bool);
    let and = app(&mut ts, "and", &[b0, a2eq, neq, c1, c2], Sort::Bool);
    let asrt = app(&mut ts, "or", &[d1, and], Sort::Bool);
    // AY's INVALID emitted model.
    let arr = |d: i64, kv: &[(i64, i64)]| {
        ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::Int(int(d)),
            store: kv
                .iter()
                .map(|(k, v)| (ModelValue::Int(int(*k)), ModelValue::Int(int(*v))))
                .collect(),
        }))
    };
    let m = StubModel::new()
        .with(a0, arr(0, &[(-3, 2)]))
        .with(a1, arr(1, &[(4, 2)]))
        .with(a2, arr(0, &[(7, -1), (-4, 1)]))
        .with(i0, ModelValue::Int(int(-10)))
        .with(i1, ModelValue::Int(int(0)))
        .with(i2, ModelValue::Int(int(5)))
        .with(i3, ModelValue::Int(int(-4)))
        .with(b0, ModelValue::Bool(true));
    assert_violates(&verdict(&ts, &m, &[asrt]));
}
