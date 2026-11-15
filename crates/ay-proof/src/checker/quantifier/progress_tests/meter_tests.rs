// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn blocked_name_set_clone_precharges_long_strings_and_table_capacity() {
    let mut names = HashSet::default();
    names.insert("long".repeat(2_048));
    let mut work = 0;
    let mut saw_string = false;
    let mut progress = |_: usize, bytes: usize| {
        saw_string |= bytes == 8_192;
        bytes < 8_192
    };
    let mut meter = QuantifierMeter::new(ProofId(0), "forall_inst", &mut work, &mut progress);
    assert_resource(meter.clone_names(&names));
    assert!(saw_string);
    assert_eq!(names.len(), 1);
}

#[test]
fn growing_name_tables_charge_old_long_keys_before_rehash() {
    let mut names = HashSet::default();
    names.insert("long".repeat(2_048));
    let mut index = 0;
    while names.len() < names.capacity() {
        names.insert(format!("s{index}"));
        index += 1;
    }
    let mut work = 0;
    let mut saw_long = false;
    let mut progress = |work: usize, _: usize| {
        saw_long |= work >= 8_192;
        work < 8_192
    };
    let mut meter = QuantifierMeter::new(ProofId(0), "forall_inst", &mut work, &mut progress);
    assert_resource(meter.name_set_entry(&names, "new"));
    assert!(saw_long);

    let mut names = HashMap::default();
    names.insert("long".repeat(2_048), 0u32);
    let mut index = 0;
    while names.len() < names.capacity() {
        names.insert(format!("s{index}"), index);
        index += 1;
    }
    let mut work = 0;
    let mut saw_long = false;
    let mut progress = |work: usize, _: usize| {
        saw_long |= work >= 8_192;
        work < 8_192
    };
    let mut meter = QuantifierMeter::new(ProofId(0), "forall_inst", &mut work, &mut progress);
    assert_resource(meter.name_map_entry(&names, "new"));
    assert!(saw_long);
}

#[test]
fn substitution_matcher_charges_duplicate_frame_pushes_independently() {
    let fixture = Fixture::new(2_048);
    let mut work = 0;
    let mut total = 0usize;
    let mut progress = |delta: usize, _: usize| {
        total += delta;
        total < 512
    };
    let mut meter = QuantifierMeter::new(ProofId(0), "forall_inst", &mut work, &mut progress);
    assert_resource(substitution::matches_single_substitution(
        &fixture.terms,
        fixture.body,
        fixture.instance,
        "meter_x",
        fixture.witness,
        &mut meter,
    ));
    assert_eq!(
        work, 1,
        "refusal occurs during root fan-out, not after visiting duplicate pairs"
    );
}

#[test]
fn caller_budget_is_not_reset_between_quantifier_checks() {
    let fixture = Fixture::new(1);
    let mut allowance = 0usize;
    fixture
        .validate(Rule::ForallInst, &mut |_, bytes| {
            allowance += bytes;
            true
        })
        .expect("measure small check");
    let mut spent = 0usize;
    let mut progress = |_: usize, bytes: usize| {
        let Some(next) = spent.checked_add(bytes) else {
            return false;
        };
        if next > allowance {
            return false;
        }
        spent = next;
        true
    };
    fixture
        .validate(Rule::ForallInst, &mut progress)
        .expect("first check fits allowance");
    assert_resource(fixture.validate(Rule::Skolem, &mut progress));
    assert_eq!(spent, allowance);
}

fn skolem_work(terms: &TermStore, equality: TermId, witness: TermId) -> usize {
    let mut spent = 0usize;
    validate_sko_forall_with_progress(
        terms,
        ProofId(0),
        &[equality],
        0,
        &[witness],
        &mut |work, _| {
            spent = spent.checked_add(work).expect("small registry fixture");
            true
        },
    )
    .expect("valid registered witness");
    spent
}

#[test]
fn ghost_registrations_increase_lookup_charge_without_new_terms_and_survive_clone() {
    let mut fixture = Fixture::new(1);
    let before = skolem_work(&fixture.terms, fixture.equality, fixture.witness);
    let term_count = fixture.terms.len();
    for index in 0..1_024 {
        fixture.terms.mark_skolem_symbol(format!("ghost_{index}"));
    }
    assert_eq!(fixture.terms.len(), term_count);
    assert!(fixture.terms.checker_visible_metadata_generation() > term_count as u64);
    let after = skolem_work(&fixture.terms, fixture.equality, fixture.witness);
    assert!(after > before);
    let cloned = fixture.terms.clone();
    assert_eq!(
        cloned.checker_visible_metadata_generation(),
        fixture.terms.checker_visible_metadata_generation()
    );
    assert_eq!(
        skolem_work(&cloned, fixture.equality, fixture.witness),
        after
    );
}

#[test]
fn queue_cap_refuses_before_an_additional_reservation() {
    let mut work = 0;
    let mut progress = |_: usize, _: usize| true;
    let mut meter = QuantifierMeter::new(ProofId(0), "forall_inst", &mut work, &mut progress);
    let mut queue = vec![TermId(0); SKOLEM_TERM_WORK_LIMIT];
    let capacity = queue.capacity();
    assert_resource(meter.push(&mut queue, TermId(1)));
    assert_eq!(queue.len(), SKOLEM_TERM_WORK_LIMIT);
    assert_eq!(queue.capacity(), capacity);
}
