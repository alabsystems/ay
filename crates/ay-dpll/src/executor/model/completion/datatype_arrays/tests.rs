// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Phase-boundary regressions for post-carrier datatype-array substitution replay.
//! Candidates are built in process; no search, external solver, or certificate is
//! involved. The production carrier allocator and replay helper do all recovery.
//!
//! STATUS 2026-09-12: five of these have NEVER passed. They landed unrun with
//! `c8908ecae` (whose only production change is `mod tests;`), under the
//! blocker its own checkpoint records — "These updated tests still need a
//! successful build and rerun on this integrated source"
//! (the development design notes). Nothing under
//! `completion/` has changed since, so they are a SPECIFICATION of intended
//! behaviour, not a regression signal. Measured root cause, one probe, all five:
//!
//!  * `eval(read)` is `Element("@ReplayPacket!7")`, not `Unknown`, and it is so
//!    BEFORE `complete_carriers()`. Deleting the fixture's `read = anchor`
//!    assertion makes it `Unknown` again, so the value arrives through that
//!    ASSERTED EQUALITY resolving to `anchor`'s committed class — a sound
//!    answer: every model of the assertions puts `read` in `anchor`'s class.
//!  * `carrier(read)` is `None` after `complete_carriers()`: completion leaves
//!    `term_values` holding `anchor` ALONE and never materializes an entry for
//!    the select. The tests assume it does.
//!  * The conflict fixture's two indices DO fold equal (`bvadd(0x8…01, 0)`
//!    evaluates to `0x8…01`), so `eval_array.rs`'s documented rule —
//!    "conflicting committed reads at the same concrete index yield `Unknown`
//!    (fail-closed), never a guessed element" — WOULD refuse. It never runs:
//!    the equality path answers first, so a model committing
//!    `select(a,i) = class7` and `select(a,i) = class8` still evaluates to a
//!    definite element. `post_carrier_replay_conflicting_concrete_index_reads_stays_unevaluable`
//!    is asserting that documented policy, and this path does not implement it.
//!
//! Closing that bypass is a change to the evaluation core's fail-closed
//! ordering and needs a corpus differential before it lands; it is deliberately
//! NOT done here rather than guessed at.

use super::{EvalValue, Executor, Model};
use crate::executor::model::EvalMemoSession;
use ay_bv::BvModel;
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::Symbol;
use ay_core::{Sort, TermId};
use num_bigint::BigInt;

const INDEX: u64 = 0x8000_0000_0000_0001;
const ANCHOR_CLASS: &str = "@ReplayPacket!7";

struct Fixture {
    exec: Executor,
    model: Model,
    array: TermId,
    index: TermId,
    read: TermId,
    anchor: TermId,
    selector: TermId,
    anchor_selector: TermId,
    chain: [TermId; 3],
    flags: [TermId; 2],
    unrelated: TermId,
    definition: TermId,
}

fn variable(exec: &mut Executor, name: &str, sort: Sort) -> TermId {
    let term = exec.ctx.terms.mk_var(name, sort.clone());
    exec.ctx.register_symbol(name.to_string(), term, sort);
    term
}

fn bv(value: u64) -> EvalValue {
    EvalValue::BitVec {
        value: BigInt::from(value),
        width: 64,
    }
}

impl Fixture {
    fn new() -> Self {
        let declarations = ay_frontend::parse(
            "(declare-datatype ReplayPacket \
                ((packet (payload (_ BitVec 64))) (empty_packet)))",
        )
        .expect("the actual datatype registry accepts the fixture");
        let mut exec = Executor::new();
        exec.execute_all(&declarations)
            .expect("datatype declaration executes without a check-sat");
        let packet = Sort::Uninterpreted("ReplayPacket".to_string());
        let array = variable(
            &mut exec,
            "backing",
            Sort::array(Sort::bitvec(64), packet.clone()),
        );
        let index = variable(&mut exec, "index", Sort::bitvec(64));
        let read = exec.ctx.terms.mk_select(array, index);
        let anchor = variable(&mut exec, "anchor", packet);
        let selector = exec
            .ctx
            .terms
            .mk_app(Symbol::named("payload"), [read], Sort::bitvec(64));
        let anchor_selector =
            exec.ctx
                .terms
                .mk_app(Symbol::named("payload"), [anchor], Sort::bitvec(64));
        let carrier_equality = exec.ctx.terms.mk_eq(read, anchor);
        exec.ctx.assertions.push(carrier_equality);
        let (chain, flags, unrelated, definition) = add_substitution_chain(&mut exec, selector);
        let mut values = HashMap::default();
        values.insert(index, BigInt::from(INDEX));
        values.insert(anchor_selector, BigInt::from(41u8));
        values.insert(unrelated, BigInt::from(85u8));
        for term in chain {
            values.insert(term, BigInt::from(0u8));
        }
        let mut model = Model::empty();
        model.bv_model = Some(BvModel {
            values,
            term_to_bits: HashMap::default(),
            bool_overrides: HashMap::default(),
        });
        model.bool_overrides.insert(flags[0], false);
        model.bool_overrides.insert(flags[1], true);
        let euf = model.euf_model.get_or_insert_with(Default::default);
        euf.term_values.insert(anchor, ANCHOR_CLASS.to_string());
        euf.sort_elements
            .insert("ReplayPacket".to_string(), vec![ANCHOR_CLASS.to_string()]);
        Self {
            exec,
            model,
            array,
            index,
            read,
            anchor,
            selector,
            anchor_selector,
            chain,
            flags,
            unrelated,
            definition,
        }
    }

    fn complete_carriers(&mut self) {
        self.exec
            .complete_uninterpreted_sort_model(&mut self.model, &[], None);
    }

    fn replay(&mut self) {
        self.exec
            .replay_datatype_array_dependent_substitutions(&mut self.model);
    }

    fn eval(&self, term: TermId) -> EvalValue {
        self.exec.evaluate_term(&self.model, term)
    }

    fn carrier(&self, term: TermId) -> Option<&str> {
        self.model
            .euf_model
            .as_ref()
            .and_then(|euf| euf.term_values.get(&term))
            .map(String::as_str)
    }
}

fn add_substitution_chain(
    exec: &mut Executor,
    selector: TermId,
) -> ([TermId; 3], [TermId; 2], TermId, TermId) {
    let first = variable(exec, "recovered_payload", Sort::bitvec(64));
    let second = variable(exec, "incremented", Sort::bitvec(64));
    let third = variable(exec, "masked", Sort::bitvec(64));
    let positive = variable(exec, "positive", Sort::Bool);
    let negated = variable(exec, "negated", Sort::Bool);
    let unrelated = variable(exec, "unrelated", Sort::bitvec(64));
    let zero = exec.ctx.terms.mk_bitvec(BigInt::from(0u8), 64);
    let one = exec.ctx.terms.mk_bitvec(BigInt::from(1u8), 64);
    let eighty_five = exec.ctx.terms.mk_bitvec(BigInt::from(85u8), 64);
    let add = exec
        .ctx
        .terms
        .mk_app(Symbol::named("bvadd"), [first, one], Sort::bitvec(64));
    let xor = exec
        .ctx
        .terms
        .mk_app(Symbol::named("bvxor"), [second, one], Sort::bitvec(64));
    let compare = exec
        .ctx
        .terms
        .mk_app(Symbol::named("bvugt"), [third, zero], Sort::Bool);
    let not = exec.ctx.terms.mk_not(positive);
    let definition = exec.ctx.terms.mk_eq(first, selector);
    for (from, to) in [
        (negated, not),
        (third, xor),
        (unrelated, eighty_five),
        (positive, compare),
        (second, add),
        (first, selector),
    ] {
        exec.recorded_var_substitutions.insert(from, to);
        let equality = exec.ctx.terms.mk_eq(from, to);
        exec.ctx.assertions.push(equality);
    }
    (
        [first, second, third],
        [positive, negated],
        unrelated,
        definition,
    )
}

#[test]
fn post_carrier_replay_refreshes_multihop_bv_bool_chain_and_memo() {
    let mut fixture = Fixture::new();
    let _memo = EvalMemoSession::new();
    // Cache the genuinely unresolved selector and stale dependent candidates
    // before the production carrier allocator changes the model.
    assert_eq!(fixture.eval(fixture.read), EvalValue::Unknown);
    assert_eq!(fixture.eval(fixture.selector), EvalValue::Unknown);
    for term in fixture.chain {
        assert_eq!(fixture.eval(term), bv(0));
    }
    assert_eq!(fixture.eval(fixture.flags[0]), EvalValue::Bool(false));
    assert_eq!(fixture.eval(fixture.flags[1]), EvalValue::Bool(true));
    assert!(fixture.carrier(fixture.read).is_none());

    fixture.complete_carriers();

    assert_eq!(fixture.carrier(fixture.read), Some(ANCHOR_CLASS));
    assert_eq!(fixture.eval(fixture.selector), bv(41));
    assert_eq!(
        fixture.eval(fixture.chain[0]),
        bv(0),
        "carrier allocation alone does not replay scalars"
    );
    fixture.replay();

    for (term, expected) in fixture.chain.into_iter().zip([41, 42, 43]) {
        assert_eq!(fixture.eval(term), bv(expected));
    }
    assert_eq!(fixture.eval(fixture.flags[0]), EvalValue::Bool(true));
    assert_eq!(fixture.eval(fixture.flags[1]), EvalValue::Bool(false));
    assert_eq!(fixture.eval(fixture.unrelated), bv(85));
    assert_eq!(fixture.eval(fixture.anchor_selector), bv(41));
    for &root in &fixture.exec.ctx.assertions {
        assert_eq!(
            fixture.eval(root),
            EvalValue::Bool(true),
            "the original defining equalities must agree after replay"
        );
    }
    fixture.replay();
    assert_eq!(
        fixture.eval(fixture.chain[2]),
        bv(43),
        "a second replay is stable"
    );
}

#[test]
fn post_carrier_replay_without_matching_field_evidence_stays_unevaluable() {
    let mut fixture = Fixture::new();
    fixture
        .model
        .bv_model
        .as_mut()
        .expect("BV candidate")
        .values
        .remove(&fixture.anchor_selector);
    fixture.complete_carriers();
    assert_eq!(fixture.carrier(fixture.read), Some(ANCHOR_CLASS));
    assert_eq!(fixture.eval(fixture.selector), EvalValue::Unknown);

    fixture.replay();

    assert_eq!(
        fixture.eval(fixture.chain[0]),
        bv(0),
        "replay must not invent an uncommitted datatype field"
    );
    assert_eq!(
        fixture.eval(fixture.definition),
        EvalValue::Unknown,
        "the stale scalar cannot turn its unresolved definition into evidence"
    );
    assert!(!fixture
        .model
        .bv_model
        .as_ref()
        .expect("BV candidate")
        .values
        .contains_key(&fixture.selector));
}

#[test]
fn post_carrier_replay_does_not_launder_a_conflicting_selector_commitment() {
    let mut fixture = Fixture::new();
    fixture
        .model
        .bv_model
        .as_mut()
        .expect("BV candidate")
        .values
        .insert(fixture.selector, BigInt::from(0u8));
    let field_equality = fixture
        .exec
        .ctx
        .terms
        .mk_eq(fixture.selector, fixture.anchor_selector);
    fixture.exec.ctx.assertions.push(field_equality);

    fixture.complete_carriers();
    fixture.replay();

    // A stale substituted VAR can be re-derived, but replay cannot overwrite
    // a committed application merely to make an inconsistent candidate fit.
    assert_eq!(fixture.carrier(fixture.read), Some(ANCHOR_CLASS));
    assert_eq!(fixture.eval(fixture.selector), bv(0));
    assert_eq!(fixture.eval(fixture.anchor_selector), bv(41));
    assert_eq!(fixture.eval(fixture.chain[0]), bv(0));
    assert_eq!(
        fixture.eval(field_equality),
        EvalValue::Bool(false),
        "the original conflicting field obligation must remain refuted"
    );
}

#[test]
fn post_carrier_replay_conflicting_class_evidence_does_not_fill_the_read() {
    let mut fixture = Fixture::new();
    let other = variable(
        &mut fixture.exec,
        "other_anchor",
        Sort::Uninterpreted("ReplayPacket".to_string()),
    );
    let conflicting = fixture.exec.ctx.terms.mk_eq(fixture.read, other);
    fixture.exec.ctx.assertions.push(conflicting);
    let euf = fixture.model.euf_model.as_mut().expect("EUF candidate");
    euf.term_values.insert(other, "@ReplayPacket!8".to_string());
    euf.sort_elements
        .get_mut("ReplayPacket")
        .expect("registered carrier")
        .push("@ReplayPacket!8".to_string());

    fixture.complete_carriers();
    fixture.replay();

    assert!(
        fixture.carrier(fixture.read).is_none(),
        "a class with conflicting committed anchors cannot be completed"
    );
    assert_eq!(fixture.carrier(fixture.anchor), Some(ANCHOR_CLASS));
    assert_eq!(fixture.carrier(other), Some("@ReplayPacket!8"));
    assert_eq!(fixture.eval(fixture.selector), EvalValue::Unknown);
    assert_eq!(fixture.eval(fixture.chain[0]), bv(0));
    assert_eq!(fixture.eval(fixture.definition), EvalValue::Unknown);
}

#[test]
fn post_carrier_replay_conflicting_concrete_index_reads_stays_unevaluable() {
    let mut fixture = Fixture::new();
    let literal = fixture.exec.ctx.terms.mk_bitvec(BigInt::from(INDEX), 64);
    let zero = fixture.exec.ctx.terms.mk_bitvec(BigInt::from(0u8), 64);
    let computed =
        fixture
            .exec
            .ctx
            .terms
            .mk_app(Symbol::named("bvadd"), [literal, zero], Sort::bitvec(64));
    let first = fixture.exec.ctx.terms.mk_select(fixture.array, literal);
    let second = fixture.exec.ctx.terms.mk_select(fixture.array, computed);
    assert_ne!(first, second, "the conflict needs different index syntax");
    let euf = fixture.model.euf_model.as_mut().expect("EUF candidate");
    euf.term_values.insert(first, ANCHOR_CLASS.to_string());
    euf.term_values
        .insert(second, "@ReplayPacket!8".to_string());
    euf.sort_elements
        .get_mut("ReplayPacket")
        .expect("registered carrier")
        .push("@ReplayPacket!8".to_string());
    // This is already a post-carrier candidate with conflicting DIRECT read
    // commitments. Test replay itself, without a second allocation phase.
    assert_eq!(fixture.eval(fixture.index), bv(INDEX));
    assert_eq!(fixture.eval(fixture.read), EvalValue::Unknown);

    fixture.replay();

    assert_eq!(fixture.eval(fixture.selector), EvalValue::Unknown);
    assert_eq!(fixture.eval(fixture.definition), EvalValue::Unknown);
    assert_eq!(fixture.eval(fixture.chain[0]), bv(0));
    assert!(fixture.carrier(fixture.read).is_none());
    assert_eq!(fixture.carrier(first), Some(ANCHOR_CLASS));
    assert_eq!(fixture.carrier(second), Some("@ReplayPacket!8"));
}
