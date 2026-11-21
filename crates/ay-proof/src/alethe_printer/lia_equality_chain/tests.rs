// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::{FarkasAnnotation, Sort, TheoryLemmaKind};

struct Fixture {
    terms: TermStore,
    clause: [TermId; 3],
    vars: [TermId; 4],
}

impl Fixture {
    fn through_middle(&mut self, middle: TermId) {
        let ab = self
            .terms
            .mk_app(Symbol::named("="), [self.vars[0], middle], Sort::Bool);
        let bc = self
            .terms
            .mk_app(Symbol::named("="), [middle, self.vars[2]], Sort::Bool);
        let ac = self
            .terms
            .mk_app(Symbol::named("="), [self.vars[0], self.vars[2]], Sort::Bool);
        self.clause = [self.terms.mk_not_raw(ab), self.terms.mk_not_raw(bc), ac];
    }

    fn new() -> Self {
        let mut terms = TermStore::new();
        let vars = ["a", "b", "c", "d"].map(|name| terms.mk_var(name, Sort::Int));
        let ab = terms.mk_app(Symbol::named("="), [vars[0], vars[1]], Sort::Bool);
        let bc = terms.mk_app(Symbol::named("="), [vars[1], vars[2]], Sort::Bool);
        let ac = terms.mk_app(Symbol::named("="), [vars[0], vars[2]], Sort::Bool);
        let clause = [terms.mk_not_raw(ab), terms.mk_not_raw(bc), ac];
        Self {
            terms,
            clause,
            vars,
        }
    }

    fn format(
        &self,
        clause: &[TermId],
        overrides: Option<&HashMap<TermId, String>>,
    ) -> Option<String> {
        AlethePrinter::new_with_overrides_and_budget(&self.terms, overrides, Some(SCREEN_WORK))
            .format_checked_lia_equality_chain(ProofId(7), &TheoryLemmaKind::LiaGeneric, clause)
    }

    fn supported(&self, clause: &[TermId], overrides: Option<&HashMap<TermId, String>>) -> bool {
        let mut work = SCREEN_WORK;
        checked_lia_equality_chain_lowering_supported(
            &self.terms,
            &TheoryLemmaKind::LiaGeneric,
            clause,
            overrides,
            &mut work,
        )
    }
}

#[test]
fn lia_equality_chain_checks_native_and_printed_orientation_and_preserves_order() {
    let fixture = Fixture::new();
    for clause in [
        fixture.clause,
        [fixture.clause[2], fixture.clause[1], fixture.clause[0]],
    ] {
        for flipped in 0..4 {
            let mut overrides = HashMap::default();
            match flipped {
                1 => {
                    overrides.insert(fixture.clause[0], "(not (= b a))".into());
                }
                2 => {
                    overrides.insert(fixture.clause[1], "(not (= c b))".into());
                }
                3 => {
                    overrides.insert(fixture.clause[2], "(= c a)".into());
                }
                _ => {}
            }
            let text = fixture
                .format(&clause, Some(&overrides))
                .expect("checked chain");
            assert!(fixture.supported(&clause, Some(&overrides)));
            assert!(text.contains(":rule eq_transitive"), "{text}");
            assert!(!text.contains(":rule hole"), "{text}");
            if clause != fixture.clause {
                assert!(text.contains(":rule reordering"), "{text}");
                assert!(
                    text.contains("(cl (= a c)") || text.contains("(cl (= c a)"),
                    "{text}"
                );
            }
        }
    }
}

#[test]
fn lia_equality_chain_reordering_checks_exact_occurrences_and_printed_literals() {
    let fixture = Fixture::new();
    let ids = fixture.clause;
    let printed = ["p".into(), "q".into(), "r".into()];
    assert!(printed_reordering_matches_exact_occurrences(
        &ids,
        &printed,
        &[ids[2], ids[0], ids[1]],
        &["r".into(), "p".into(), "q".into()]
    ));
    for (original, rendered) in [
        (ids, ["p".into(), "q".into(), "forged".into()]),
        (ids, ["q".into(), "p".into(), "r".into()]),
        ([ids[0], ids[0], ids[2]], printed.clone()),
    ] {
        assert!(!printed_reordering_matches_exact_occurrences(
            &ids, &printed, &original, &rendered,
        ));
    }
    let repeated = [ids[0], ids[0], ids[2]];
    let texts = ["p".into(), "p".into(), "r".into()];
    assert!(printed_reordering_matches_exact_occurrences(
        &repeated,
        &texts,
        &[ids[2], ids[0], ids[0]],
        &["r".into(), "p".into(), "p".into()]
    ));
    assert!(!printed_reordering_matches_exact_occurrences(
        &repeated,
        &texts,
        &[ids[2], ids[0], ids[0]],
        &["r".into(), "p".into(), "q".into()]
    ));
}

#[test]
fn lia_equality_chain_does_not_consume_or_reorder_producer_hints() {
    let fixture = Fixture::new();
    let step = ProofStep::TheoryLemma {
        theory: "arith".into(),
        clause: fixture.clause.to_vec(),
        farkas: Some(FarkasAnnotation::from_ints(&[999, -999, 42])),
        kind: TheoryLemmaKind::LiaGeneric,
        lia: None,
    };
    let original = step.clone();
    let text = AlethePrinter::new(&fixture.terms)
        .format_step(&step, ProofId(7))
        .unwrap();
    assert!(text.contains(":rule eq_transitive"));
    assert!(!text.contains(":args"));
    assert_eq!(step, original);
}

#[test]
fn lia_equality_chain_refuses_missing_links_forged_targets_polarity_and_nonbinary_atoms() {
    let mut fixture = Fixture::new();
    let forged = fixture.terms.mk_app(
        Symbol::named("="),
        [fixture.vars[0], fixture.vars[3]],
        Sort::Bool,
    );
    assert!(!fixture.supported(&[fixture.clause[0], fixture.clause[1], forged], None));
    let positive_ab = match fixture.terms.get(fixture.clause[0]) {
        TermData::Not(inner) => *inner,
        _ => unreachable!(),
    };
    assert!(!fixture.supported(&[positive_ab, fixture.clause[1], fixture.clause[2]], None));
    let nary = fixture
        .terms
        .mk_app(Symbol::named("="), &fixture.vars[..3], Sort::Bool);
    let not_nary = fixture.terms.mk_not_raw(nary);
    assert!(!fixture.supported(&[not_nary, fixture.clause[1], fixture.clause[2]], None));
    assert!(!fixture.supported(
        &[TermId(u32::MAX), fixture.clause[1], fixture.clause[2]],
        None
    ));
    assert!(!fixture.supported(&fixture.clause[..2], None));
}

#[test]
fn lia_equality_chain_refuses_noninteger_and_malformed_sort_atoms() {
    for sort in [Sort::Real, Sort::Bool] {
        let mut fixture = Fixture::new();
        let other = fixture.terms.mk_var("other", sort);
        let mismatch =
            fixture
                .terms
                .mk_app(Symbol::named("="), [fixture.vars[0], other], Sort::Bool);
        let not_mismatch = fixture.terms.mk_not_raw(mismatch);
        assert!(!fixture.supported(&[not_mismatch, fixture.clause[1], fixture.clause[2]], None));
    }
    let mut fixture = Fixture::new();
    let bad = fixture.terms.mk_app(
        Symbol::named("="),
        [fixture.vars[0], fixture.vars[1]],
        Sort::Int,
    );
    assert!(!fixture.supported(&[bad, fixture.clause[1], fixture.clause[2]], None));
}

#[test]
fn lia_equality_chain_refuses_irrelevant_and_branching_edges_even_when_printed_rule_is_weaker() {
    let mut fixture = Fixture::new();
    let extra = fixture.terms.mk_app(
        Symbol::named("="),
        [fixture.vars[2], fixture.vars[3]],
        Sort::Bool,
    );
    let neg_extra = fixture.terms.mk_not_raw(extra);
    assert!(!fixture.supported(
        &[
            fixture.clause[0],
            neg_extra,
            fixture.clause[1],
            fixture.clause[2]
        ],
        None
    ));
    assert!(printed_eq_transitive_chain_holds(&[
        "(not (= a b))",
        "(not (= c d))",
        "(not (= b c))",
        "(= a c)"
    ]));
    assert!(!printed_eq_transitive_chain_holds(&[
        "(not (= a d))",
        "(not (= a b))",
        "(not (= b c))",
        "(= a c)"
    ]));
}

#[test]
fn lia_equality_chain_refuses_changed_interiors_outer_shells_and_targets() {
    let fixture = Fixture::new();
    for (term, text) in [
        (fixture.vars[1], "true"),
        (fixture.clause[0], "(= a b)"),
        (fixture.clause[0], "(not (= a d))"),
        (fixture.clause[2], "(= a d)"),
    ] {
        let overrides = HashMap::from_iter([(term, text.into())]);
        assert!(!fixture.supported(&fixture.clause, Some(&overrides)));
        assert!(fixture.format(&fixture.clause, Some(&overrides)).is_none());
    }
}

#[test]
fn lia_equality_chain_generic_kind_and_existing_two_literal_gap_do_not_gain_credit() {
    let fixture = Fixture::new();
    let printer = AlethePrinter::new(&fixture.terms);
    assert!(printer
        .format_checked_lia_equality_chain(ProofId(7), &TheoryLemmaKind::Generic, &fixture.clause)
        .is_none());
    assert!(printer
        .format_checked_lia_equality_chain(
            ProofId(7),
            &TheoryLemmaKind::LiaGeneric,
            &fixture.clause[..2]
        )
        .is_none());
}

#[test]
fn lia_equality_chain_cancellation_and_shared_budget_refuse_without_a_fallback() {
    let fixture = Fixture::new();
    let mut no_work = 0;
    assert!(!checked_lia_equality_chain_lowering_supported(
        &fixture.terms,
        &TheoryLemmaKind::LiaGeneric,
        &fixture.clause,
        None,
        &mut no_work
    ));
    let mut tiny_work = 1;
    assert!(!checked_lia_equality_chain_lowering_supported(
        &fixture.terms,
        &TheoryLemmaKind::LiaGeneric,
        &fixture.clause,
        None,
        &mut tiny_work
    ));
    assert_eq!(tiny_work, 0);
    let mut polls = 0;
    let mut stop = || {
        polls += 1;
        false
    };
    let printer = AlethePrinter::new(&fixture.terms).with_emission_progress(&mut stop);
    assert!(printer
        .format_checked_lia_equality_chain(
            ProofId(7),
            &TheoryLemmaKind::LiaGeneric,
            &fixture.clause
        )
        .is_none());
    assert!(printer.emission_progress.refused());
    drop(printer);
    drop(stop);
    assert_eq!(polls, 1);
}

#[test]
fn lia_equality_chain_captures_the_existing_check_stop() {
    let fixture = Fixture::new();
    let _stop = ay_core::resource::enter_check_stop(std::sync::Arc::new(|| true));
    assert!(!fixture.supported(&fixture.clause, None));
}

#[test]
fn lia_equality_chain_oversized_selected_rendering_is_refused_before_copy() {
    let fixture = Fixture::new();
    let overrides = HashMap::from_iter([(fixture.vars[1], "huge".repeat(2 * 1024 * 1024))]);
    assert!(!fixture.supported(&fixture.clause, Some(&overrides)));
}

#[test]
fn lia_equality_chain_raw_name_literal_depth_and_expansion_are_bounded() {
    let mut fixture = Fixture::new();
    let huge = fixture.terms.mk_var(&"x".repeat(257), Sort::Int);
    fixture.through_middle(huge);
    assert!(!fixture.supported(&fixture.clause, None));

    let mut fixture = Fixture::new();
    let huge = fixture
        .terms
        .mk_int(num_bigint::BigInt::from(1) << 1024usize);
    fixture.through_middle(huge);
    assert!(!fixture.supported(&fixture.clause, None));

    for shared in [false, true] {
        let mut fixture = Fixture::new();
        let zero = fixture.terms.mk_int(0.into());
        let mut middle = fixture.vars[1];
        for _ in 0..if shared { 13 } else { 65 } {
            middle = fixture.terms.mk_app(
                Symbol::named("+"),
                [middle, if shared { middle } else { zero }],
                Sort::Int,
            );
        }
        fixture.through_middle(middle);
        assert!(!fixture.supported(&fixture.clause, None));
    }
}

#[test]
fn lia_equality_chain_forged_cycles_and_malformed_builtin_interiors_never_reach_printing() {
    let mut fixture = Fixture::new();
    let zero = fixture.terms.mk_int(0.into());
    let future = TermId(u32::try_from(fixture.terms.len()).unwrap());
    let cycle = fixture
        .terms
        .mk_app(Symbol::named("+"), [future, zero], Sort::Int);
    assert_eq!(cycle, future);
    fixture.through_middle(cycle);
    assert!(!fixture.supported(&fixture.clause, None));

    let mut fixture = Fixture::new();
    let boolean = fixture.terms.mk_var("p", Sort::Bool);
    let malformed = fixture
        .terms
        .mk_app(Symbol::named("+"), [boolean], Sort::Int);
    fixture.through_middle(malformed);
    assert!(!fixture.supported(&fixture.clause, None));
}

#[test]
fn lia_equality_chain_bounded_literal_envelope_keeps_an_honest_decline() {
    for width in [MAX_LITERALS, MAX_LITERALS + 1] {
        let mut fixture = Fixture::new();
        let vars: Vec<_> = (0..width)
            .map(|index| fixture.terms.mk_var(&format!("n{index}"), Sort::Int))
            .collect();
        let mut clause = Vec::new();
        for pair in vars.windows(2) {
            let eq = fixture.terms.mk_app(Symbol::named("="), pair, Sort::Bool);
            clause.push(fixture.terms.mk_not_raw(eq));
        }
        clause.push(fixture.terms.mk_app(
            Symbol::named("="),
            [vars[0], vars[width - 1]],
            Sort::Bool,
        ));
        assert_eq!(fixture.supported(&clause, None), width == MAX_LITERALS);
    }
}
