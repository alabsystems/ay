// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `tests` to preserve test FQNs.

#[test]
fn seq_map_applies_the_function_as_array_pointwise() {
    let f = mvarr_i(0, &[(1, 3), (2, 4)]);
    let mapped = seq::eval("seq.map", &[f.clone(), mvseq_i(&[1, 2])]).unwrap();
    assert_eq!(ints_of(&mapped), vec![3, 4]);
    // The default covers indices with no pin.
    let mapped = seq::eval("seq.map", &[f, mvseq_i(&[1, 7])]).unwrap();
    assert_eq!(ints_of(&mapped), vec![3, 0]);
    // Length is preserved, so the empty sequence maps to the empty sequence.
    let empty = seq::eval("seq.map", &[mvarr_i(5, &[]), mvseq_i(&[])]).unwrap();
    assert_eq!(ints_of(&empty), Vec::<i64>::new());
    // A non-array function operand is unevaluable, never a guessed value.
    assert!(seq::eval("seq.map", &[ModelValue::Int(int(1)), mvseq_i(&[1])]).is_err());
}

#[test]
fn seq_mapi_curries_the_index_outermost() {
    // f[i][e]: at index 0 add 10, at index 1 add 20.
    let f = mvarr2_i(
        mvarr_i(0, &[]),
        &[(0, mvarr_i(0, &[(5, 15)])), (1, mvarr_i(0, &[(6, 26)]))],
    );
    let mapped = seq::eval(
        "seq.mapi",
        &[f.clone(), ModelValue::Int(int(0)), mvseq_i(&[5, 6])],
    )
    .unwrap();
    assert_eq!(ints_of(&mapped), vec![15, 26]);
    // The index operand is the BASE, so it offsets every element position.
    let shifted = seq::eval("seq.mapi", &[f, ModelValue::Int(int(1)), mvseq_i(&[6])]).unwrap();
    assert_eq!(ints_of(&shifted), vec![26]);
}

#[test]
fn seq_foldl_chains_the_accumulator_outermost() {
    // f[acc][e] = acc + e, pinned over exactly the reachable pairs.
    let f = mvarr2_i(
        mvarr_i(0, &[]),
        &[
            (0, mvarr_i(0, &[(1, 1), (2, 2)])),
            (1, mvarr_i(0, &[(2, 3)])),
            (3, mvarr_i(0, &[(4, 7)])),
        ],
    );
    let folded = seq::eval(
        "seq.foldl",
        &[f.clone(), ModelValue::Int(int(0)), mvseq_i(&[1, 2, 4])],
    )
    .unwrap();
    assert_eq!(int_of(&folded), int(7));
    // Over the EMPTY sequence the fold IS the accumulator — `f` is never
    // applied, so it need not even be well-shaped beyond being an array.
    let identity = seq::eval("seq.foldl", &[f, ModelValue::Int(int(42)), mvseq_i(&[])]).unwrap();
    assert_eq!(int_of(&identity), int(42));
    // A curried layer that is not an array fails closed.
    assert!(seq::eval(
        "seq.foldl",
        &[
            mvarr_i(0, &[(0, 9)]),
            ModelValue::Int(int(0)),
            mvseq_i(&[1])
        ],
    )
    .is_err());
}

#[test]
fn seq_foldli_chains_index_then_accumulator() {
    // f[i][acc][e]: only the (i=0, acc=0, e=5) and (i=1, acc=5, e=6) steps.
    let inner0 = mvarr2_i(mvarr_i(0, &[]), &[(0, mvarr_i(0, &[(5, 5)]))]);
    let inner1 = mvarr2_i(mvarr_i(0, &[]), &[(5, mvarr_i(0, &[(6, 11)]))]);
    let f = ModelValue::Array(Box::new(ArrayValue {
        default: inner0.clone(),
        store: vec![
            (ModelValue::Int(int(0)), inner0),
            (ModelValue::Int(int(1)), inner1),
        ],
    }));
    let folded = seq::eval(
        "seq.foldli",
        &[
            f,
            ModelValue::Int(int(0)),
            ModelValue::Int(int(0)),
            mvseq_i(&[5, 6]),
        ],
    )
    .unwrap();
    assert_eq!(int_of(&folded), int(11));
}

#[test]
fn seq_replace_all_semantics() {
    assert_eq!(ra(&[1, 2, 1], &[1], &[9]), vec![9, 2, 9]); // both occurrences
    assert_eq!(ra(&[1, 1, 1], &[1, 1], &[0]), vec![0, 1]); // non-overlapping l-to-r
    assert_eq!(ra(&[1, 2], &[], &[9]), vec![1, 2]); // empty src -> unchanged
    assert_eq!(ra(&[1, 2], &[3], &[9]), vec![1, 2]); // not found -> unchanged
    assert_eq!(ra(&[1, 2], &[1], &[8, 8]), vec![8, 8, 2]); // expanding dst
    assert_eq!(ra(&[1, 2, 1], &[1], &[]), vec![2]); // deleting dst
    assert_eq!(ra(&[1, 1], &[1, 1], &[9]), vec![9]); // whole-sequence match
}
