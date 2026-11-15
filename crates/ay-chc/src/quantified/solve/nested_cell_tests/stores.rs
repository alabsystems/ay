// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[derive(Clone, Copy)]
enum Write {
    Preserve,
    Corrupt,
}

fn source(write: Write) -> QuantifiedChcProblem {
    let value = match write {
        Write::Preserve => "fill",
        Write::Corrupt => "(bvadd fill (_ bv1 8))",
    };
    let row = "(select (fld_data outer) update_row)";
    let transition = format!(
        "(assert (forall ((outer Outer) (fill (_ BitVec 8))
                          (update_row (_ BitVec 64)) (update_col (_ BitVec 64)))
          (=> (and (P outer fill)
                   (bvult update_row (fld_len outer))
                   (bvult update_col (fld_len {row})))
              (P (mkOuter (fld_ptr outer) (fld_len outer) (fld_cap outer)
                   (store (fld_data outer) update_row
                     (mkInner (fld_ptr {row}) (fld_len {row}) (fld_cap {row})
                       (store (fld_data {row}) update_col {value}))))
                 fill))))
         (check-sat)"
    );
    // Put the transition after the query deliberately: certification must
    // visit every original clause, not stop at the first false-headed rule.
    QuantifiedChcProblem::parse_smtlib(
        &script(Premise::Full, Query::SameRow).replace("(check-sat)", &transition),
    )
    .expect("nested Vec store source admission")
}

/// #nested-array-quarantine-datatype-fields RE-PIN (was
/// `nested_vec_store_transition_preserves_frames_and_rechecks_every_clause`,
/// 8fb6cc0f4). This source used to certify `Safe`, but each AY discharge that
/// took it there -- the depth-0 counterexample refutation and the consecution
/// obligation, a read-over-write through `(store (fld_data outer) row (mkInner
/// .. (store (fld_data row) col fill)))` -- is an UNSAT over arrays nested in
/// datatype fields whose only admission was `discharged-trust`, a fresh
/// executor re-running the same combination. The public nested-array
/// quarantine now resolves declared record carriers, so those UNSATs are
/// withheld exactly as their directly nested twins always were, and the
/// correct transition is `Unknown`.
///
/// Counterfactual: re-open the carrier bypass and the first assertion sees
/// `Safe` on an idle host; break the store frames so the correct write is
/// refuted and it sees `Unsafe`. Under heavy load `Unknown` alone cannot tell
/// the quarantine from a starved solve (the old `Safe` pin was measured
/// failing to `Unknown` under load at the base).
///
/// The depth-0 counterexample refutation has since gained a checked
/// authority: with no diagonal instance of its frame axiom it carries a
/// trust-free strict proof, pinned (strict-proof admission, never
/// `discharged-trust`) by ay-dpll's `executor::check_sat::
/// nested_array_quarantine::tests::
/// the_model_checker_consumer_nested_vec_frame_refutation_publishes_only_on_a_strict_proof`.
/// The consecution obligation has not, so the transition stays `Unknown`.
/// Restore the `Safe` pin, with its obligation-shape and recheck assertions,
/// once it does.
#[test]
#[timeout(180000)]
fn nested_vec_store_transition_is_never_refuted_and_trust_only_discharges_stay_withheld() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(TERM_BUDGET));
    let deadline = Instant::now() + Duration::from_secs(120);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    let token = CancellationToken::new();
    let source = source(Write::Preserve);
    assert_eq!(source.source_problem().clauses().len(), 3);
    assert!(
        matches!(
            source.solve(Duration::from_secs(45), Some(TERM_BUDGET), &token),
            QuantifiedChcResult::Unknown
        ),
        "a correctly framed nested store must never be refuted, and its \
         trust-only nested-array discharges must stay withheld"
    );
    // A concrete reachable counterexample writes 8 at [33][64] in an outer
    // Vec of length 100 with inner lengths 100 and every valid cell initially
    // 7. Both update guards and the beyond-32 query guards hold.
    let corrupted = self::source(Write::Corrupt);
    assert!(!matches!(
        corrupted.solve(
            deadline
                .saturating_duration_since(Instant::now())
                .min(Duration::from_secs(30)),
            Some(TERM_BUDGET),
            &token,
        ),
        QuantifiedChcResult::Safe(_)
    ));
    assert!(Instant::now() < deadline);
}
