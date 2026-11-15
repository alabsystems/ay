// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Boundaries of the asserted-equality select fallback
//! (`resolve_select_via_asserted_equality`, #aufbv-nonbv-elem).
//!
//! The fallback answers a `(select arr i)` the array/BV/EUF models could not
//! value, from a TOP-LEVEL `(= leaf select)`. Two properties are load-bearing
//! and neither was tested before 2026-09-14:
//!
//!  * it must stay OUT of the way of the equality-carrier completion pass,
//!    which owns every element sort `completion::carrier_sort_key` accepts —
//!    see the `completion/datatype_arrays` battery for what answering ahead of
//!    that pass costs; and
//!  * on the sorts it does own (Bool is the case it was written for) it must
//!    require the asserted anchors to AGREE. Returning the first anchor with a
//!    value publishes a definite element for a read the candidate commits two
//!    ways.
//!
//! The pair below is a capability control and its negative twin: the single
//! anchor must still resolve, so the narrowing did not answer the conflict by
//! disabling the lane.

use super::*;

/// `arr : Array BV64 Bool`, a read of it, and the two Bool leaves used as
/// anchors (`p` true, `q` false in the model). A BV model is present but empty,
/// which is exactly the eager-bit-blast state the fallback exists for: the read
/// has no bit-blasted value and no array-model entry.
struct BoolReadFixture {
    exec: Executor,
    model: Model,
    read: TermId,
    p: TermId,
    q: TermId,
}

impl BoolReadFixture {
    fn new() -> Self {
        let mut exec = Executor::new();
        let arr = exec
            .ctx
            .terms
            .mk_var("arr", Sort::array(Sort::bitvec(64), Sort::Bool));
        let index = exec.ctx.terms.mk_var("index", Sort::bitvec(64));
        let read = exec.ctx.terms.mk_select(arr, index);
        let p = exec.ctx.terms.mk_var("p", Sort::Bool);
        let q = exec.ctx.terms.mk_var("q", Sort::Bool);
        let mut model = empty_model();
        model.bv_model = Some(BvModel {
            values: HashMap::default(),
            term_to_bits: HashMap::default(),
            bool_overrides: HashMap::default(),
        });
        model.bool_overrides.insert(p, true);
        model.bool_overrides.insert(q, false);
        Self {
            exec,
            model,
            read,
            p,
            q,
        }
    }

    fn assert_eq_anchor(&mut self, leaf: TermId) {
        let equality = self.exec.ctx.terms.mk_eq(self.read, leaf);
        self.exec.ctx.assertions.push(equality);
    }

    fn eval_read(&self) -> EvalValue {
        self.exec.evaluate_term(&self.model, self.read)
    }
}

#[test]
fn bool_element_read_still_resolves_through_a_single_asserted_anchor() {
    let mut fixture = BoolReadFixture::new();
    assert_eq!(
        fixture.eval_read(),
        EvalValue::Unknown,
        "with no anchor the read has no value at all"
    );
    let p = fixture.p;
    fixture.assert_eq_anchor(p);
    assert_eq!(
        fixture.eval_read(),
        EvalValue::Bool(true),
        "a Bool element sort is not a completion carrier, so this lane still owns it"
    );
}

#[test]
fn bool_element_read_with_disagreeing_asserted_anchors_stays_unevaluable() {
    let mut fixture = BoolReadFixture::new();
    let (p, q) = (fixture.p, fixture.q);
    fixture.assert_eq_anchor(p);
    fixture.assert_eq_anchor(q);
    assert_eq!(
        fixture.eval_read(),
        EvalValue::Unknown,
        "`(= r p)` and `(= r q)` with `p != q` is an inconsistent candidate; \
         answering with whichever assertion is scanned first publishes a \
         definite element for a read committed two ways"
    );

    // Order independence: the conflict is a property of the assertion SET, not
    // of which anchor the scan reaches first.
    let mut reversed = BoolReadFixture::new();
    reversed.assert_eq_anchor(q);
    reversed.assert_eq_anchor(p);
    assert_eq!(reversed.eval_read(), EvalValue::Unknown);
}

#[test]
fn uninterpreted_element_read_is_left_to_the_equality_carrier_completion() {
    // The same shape at an UNINTERPRETED element sort: the completion pass owns
    // it, so this lane must decline even though a single consistent anchor is
    // present and carries a committed class. Declining is what lets the read
    // reach `unknown_idx` in the completion snapshot and receive a materialized
    // carrier entry — see `completion::datatype_arrays::tests`.
    let mut exec = Executor::new();
    let packet = Sort::Uninterpreted("Packet".to_string());
    let arr = exec
        .ctx
        .terms
        .mk_var("arr", Sort::array(Sort::bitvec(64), packet.clone()));
    let index = exec.ctx.terms.mk_var("index", Sort::bitvec(64));
    let read = exec.ctx.terms.mk_select(arr, index);
    let anchor = exec.ctx.terms.mk_var("anchor", packet);
    let equality = exec.ctx.terms.mk_eq(read, anchor);
    exec.ctx.assertions.push(equality);

    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: HashMap::default(),
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::default(),
    });
    let euf = model.euf_model.get_or_insert_with(EufModel::default);
    euf.term_values.insert(anchor, "@Packet!0".to_string());
    euf.sort_elements
        .insert("Packet".to_string(), vec!["@Packet!0".to_string()]);

    assert_eq!(
        exec.evaluate_term(&model, anchor),
        EvalValue::Element("@Packet!0".to_string()),
        "the anchor itself is committed"
    );
    assert_eq!(
        exec.evaluate_term(&model, read),
        EvalValue::Unknown,
        "an uninterpreted element sort is a completion carrier; this lane must \
         not answer ahead of the pass that records the value in the model"
    );
}
