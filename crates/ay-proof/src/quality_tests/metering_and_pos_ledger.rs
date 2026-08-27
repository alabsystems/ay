// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The guard-mutation ledger for `SemanticChargeClass::AndPosShallowMatch`.
//!
//! Split from `metering_and_pos_bounds.rs` so each file stays inside the
//! repository's 500-line ceiling.

/// Each guard deleted or weakened, `cargo test -p ay-proof --lib` run
/// UNFILTERED over the whole crate, the failures OBSERVED, then restored.
/// Every row below is a measured result; none is a prediction, and the
/// per-row test lists are the harness's own output rather than a recollection.
///
/// Twelve mutations, TWELVE RED, none needing a pair or a triple to become
/// observable. That is a result, not a claim of thoroughness: the two a
/// pair-hunt was expected for — the `clause.len() != 2` guard (a longer clause
/// is refused by `validate_and_pos`'s OWN length guard before a matcher runs)
/// and the `.min` cap (the `General` product is usually the larger of the two
/// anyway) — each turned out to be caught alone, by the routing NEGATIVE and by
/// the tightening sweep's small-`unfolded` rows respectively.
///
/// One row is recorded as caught by something OTHER than a work-bound
/// assertion, and says so.
pub(super) const AND_POS_CHARGE_LEDGER: &[(&str, &str)] = &[
    (
        "and_pos_matchers_are_shallow: the `decode_app(lit, \"or\")` literal \
         check DELETED",
        "RED x3 — a_doubling_and_pos_still_keeps_the_general_product, \
         and_pos_routes_to_the_shallow_class_only_when_the_matchers_cannot_recurse \
         (NEGATIVE 1), the_and_pos_wire_text_is_unchanged_by_the_charge_model. \
         SOUNDNESS-RELEVANT: without it the doubling step is billed a few \
         thousand work units for >= 2^20 real matcher primitives.",
    ),
    (
        "and_pos_matchers_are_shallow: the `strip_not(lit)` negand check DELETED",
        "RED x2 — a_doubling_negand_reaches_the_second_call_site_and_is_still_refused \
         and the routing test (NEGATIVE 2). This is the SECOND call site: \
         `matches_positive_literal_of_term` strips the `not` and hands the inner \
         `or` to the same De Morgan arm one level down, so a clause with NO \
         `or`-headed literal still reaches the recursion. The refutation fixture \
         checks that a literal guard would not have caught it.",
    ),
    (
        "and_pos_matchers_are_shallow: `\"or\"` changed to `\"and\"` in BOTH \
         checks",
        "RED x6 — the routing test, all three adversarial bound tests, the \
         payload-floor test and the printer test. The gate names the DUAL \
         connective; naming the same one is a no-op that admits every \
         `or`-headed literal.",
    ),
    (
        "and_pos_matchers_are_shallow: the `decode_app(source, \"and\")` check \
         DELETED",
        "RED — the routing test (NEGATIVE 3). Without an `and`-headed source, \
         `decode_ite(source)` is no longer structurally `None` and the ITE arm \
         recurses into both branches.",
    ),
    (
        "and_pos_matchers_are_shallow: the `clause.len() != 2` guard DELETED",
        "RED — the routing test (NEGATIVE 5). Expected to need a PAIR, because a \
         longer clause is refused by `validate_and_pos`'s own length guard \
         before a matcher runs; measured RED alone. The guard is kept because \
         the `53 + 2n` derivation quantifies over exactly two literals.",
    ),
    (
        "and_pos_matchers_are_shallow: `source_term` read from `clause.first()` \
         instead of `args.first()`",
        "RED x6 — the routing test (NEGATIVE 4) and every bound test. The gate \
         must decide the SAME step `validate_step` hands the validator \
         (`checker/mod.rs` passes `args.first().copied()`), or it is a claim \
         about a different function.",
    ),
    (
        "is_and_pos_shallow_match: `AletheRule::AndNeg` added to the pattern",
        "RED — the routing test (NEGATIVE 6). Recorded because the `and_neg` \
         pass's OWN guard, and_neg_is_not_admitted_to_any_dag_bounded_class, \
         does NOT catch it: it probes an `and_neg` step with an empty clause and \
         no `:args`, which this gate declines for unrelated reasons. NEGATIVE 6 \
         uses a two-literal clause with a source, and that is what makes the \
         mutation observable.",
    ),
    (
        "and_pos_shallow_match_charge: the `.min(replaced_general_product(..))` \
         cap DELETED",
        "RED — the_shallow_class_never_charges_more_than_the_general_product. \
         The sweep's small-`unfolded` rows are where the cap binds \
         (`32*work + 32` over `work * 1`), and they are in the sweep precisely \
         so this row is a measurement. The cap is what makes the corpus-wide \
         `ResourceLimit` count unable to RISE without a corpus argument.",
    ),
    (
        "and_pos_shallow_match_charge: bytes changed from `payload.bytes` to \
         `4 * payload.bytes`",
        "RED x2 — the_shallow_class_never_charges_more_than_the_general_product \
         (`assert_eq!(bytes, stats.bytes)`) and \
         a_deeply_shared_store_chain_and_pos_is_charged_on_its_dag. A byte-limb \
         change would make this something other than a pure work-side tightening \
         and could newly refuse on bytes.",
    ),
    (
        "and_pos_shallow_match_charge: the `+ AND_POS_SHALLOW_WORK_FACTOR` \
         constant tail DELETED",
        "RED x2 — the_measured_clearsy_payload_is_the_one_this_class_fixes \
         (1_309_536 becomes 1_309_504) and \
         a_deeply_shared_store_chain_and_pos_is_charged_on_its_dag. A `work = 0` \
         payload must still be charged for the constant-time guards.",
    ),
    (
        "AND_POS_SHALLOW_WORK_FACTOR lowered from 32 to 1",
        "RED x2 — the_measured_clearsy_payload_is_the_one_this_class_fixes and \
         the_metering_still_refuses_an_oversized_and_pos_proof (the 350M/32 \
         refusal threshold). HONESTLY RECORDED: it is NOT caught by any \
         `tight >= ops` or `tight >= 53 + 2n` assertion, because at factor 1 the \
         model still bounds every fixture measured — the payload walk debits at \
         least one unit per child slot of every reachable node AND re-debits the \
         tree unfolding into the same counter, while the validator scans the \
         source's argument list at most twice. 32 is HEADROOM over a counted \
         derivation (`53 + 2n <= 32*work + 32`), not a fitted constant, and the \
         direction of that headroom is fail-closed.",
    ),
    (
        "checker/boolean.rs `matches_negation_of_term`: the De Morgan arms \
         DELETED",
        "RED x7 — including checker::tests::ite_negation_shape_tests::\
         and_pos_accepts_nnf_ite_inside_de_morgan_gate, both `and_neg` \
         refutation tests, and ALL THREE mirror/refutation tests on this side. \
         Deleting them is what a RULE-WIDE DAG-bounded charge would require, and \
         it changes what the checker ACCEPTS — which is why this pass gates on \
         the STEP and leaves every validator byte-identical.",
    ),
];

#[test]
fn and_pos_charge_ledger_is_present() {
    assert!(AND_POS_CHARGE_LEDGER.len() >= 8);
}
