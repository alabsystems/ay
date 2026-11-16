// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `test_proof_artifact.rs` to preserve the existing test
// fully qualified names.

// `export_last_unsat_artifact`'s canonical-spelling rescue and the verdict
// gate that bounds it.
//
// Three cells of one boundary:
//
//   * the rescue RUNS and the verdict is accepted  -> artifact published;
//   * the rescue RUNS and the verdict is `Rejected` -> artifact withdrawn;
//   * the print refusal is not the authored channel's doing -> no rescue at
//     all, and the artifact stays withdrawn.
//
// Each of the first two carries a negative control that isolates the gate
// from every other reason this boundary returns `None`.
//
// THE TWO CELLS USE DIFFERENT AUTHORED-SPELLING REFUSALS, and deliberately so.
// Which spellings the printer can project is not a fixed property: it improves
// as bridges are added, and a fixture chosen for the refusal it provokes today
// stops provoking one tomorrow. The boundary under test does not depend on any
// particular refusal — `canonical_rescue` is set by the RETRY, whatever raised
// the refusal — so each cell picks a shape that is measured to refuse now, and
// each guards that measurement explicitly so a printer improvement fails the
// test loudly as fixture drift rather than silently emptying it.
//
//   * ACCEPTED cell: an authored CONSTANT-FOLDED BV index spelled differently
//     at its two uses (`(bvudiv #x20 #x02)` and `(bvudiv #x40 #x04)`, both
//     the canonical `#b00010000`) inside a ROW1 congruence lift -> the
//     printer refuses with `InvalidCongruenceStep`. (The cell used the plain
//     numeral `#x10` until the printer learned to bridge alternate spellings
//     of one bit-vector literal with `refl`, then `(bvadd #x08 #x08)` at both
//     uses until the raw-root ground closure became the last wire-gap retry
//     for a native-strict proof: it refutes the authored roots through the
//     one shared authored term. Both shapes now print directly and are pinned
//     trust-free in group_proofs
//     `test_carcara_trust_free_authored_bv_literal_congruence_premise` and
//     `test_carcara_trust_free_authored_folded_bv_index_shared_term`.)
//   * REJECTED cell: an authored GROUPING the printer cannot project `and_pos`
//     through -> `InvalidSurfaceStep`.

/// The authored grouping from `5da3d563d`, which the Alethe printer cannot
/// project `and_pos` through for the fixture below.
///
/// Elaboration folds `(and false ..)` to `false`, `(or LIVE false)` to `LIVE`,
/// and flattens `LIVE`'s conjuncts into the top-level conjunction, so a bound
/// such as `(<= x 10)` is a canonical TOP-LEVEL conjunct while the retained
/// source still nests it two levels down inside the `or`. The proof's
/// `and_pos` steps index the canonical conjunction, and the printer must find
/// an `and_pos` / `cong` / `comp_simplify` chain that projects that conjunct
/// off the authored grouping.
///
/// MEASURED: whether it finds one depends on the BODY. For the QF_NIA body the
/// rejected cell uses it still cannot, and that cell guards the refusal. For a
/// linear body it now can — upstream taught the printer that projection — which
/// is why the accepted cell no longer uses this grouping.
#[cfg(test)]
fn folded_authored_grouping(decls: &str, body: &str) -> String {
    format!(
        "{decls}\n\
         (assert (and (<= 0 x) (<= x 100) (<= 0 y) (<= y 100)\n\
           (or (and (not taken) (<= 0 x) (<= x 10) (<= 0 y) (<= y 10) {body})\n\
               (and false (<= 0 x) (<= x 10) (<= 0 y) (<= y 10) {body}))))\n"
    )
}

/// The same conjuncts, authored in the CANONICAL spelling the folding above
/// elaborates to. Nothing is nested, so the printer has nothing to refuse.
#[cfg(test)]
fn flat_authored_grouping(decls: &str, body: &str) -> String {
    format!(
        "{decls}\n\
         (assert (and (<= 0 x) (<= x 100) (<= 0 y) (<= y 100)\n\
           (not taken) (<= 0 x) (<= x 10) (<= 0 y) (<= y 10) {body}))\n"
    )
}

#[cfg(test)]
const RESCUE_FIXTURE_DECLS: &str = "(declare-const taken Bool)\n\
     (declare-const x Int)\n\
     (declare-const y Int)\n\
     (declare-const a Int)";

/// The ROW1 derived-index-equality refutation of
/// `qfabv_row1_derived_index_equality_is_strict_verified`, with each use of
/// the index authored in a caller-chosen spelling of one constant (a BV
/// numeral, or a constant-folded term such as `(bvudiv #x20 #x02)`).
///
/// `p0 = P0_INDEX`, `p1 = P1_INDEX`, `mem2 = store(mem, p0, WRITTEN)` and
/// `(select mem2 p1) = READ_BACK` is UNSAT: the cell just written cannot read
/// back a different value. The refutation reaches the index equality by
/// transitivity through the shared constant, so it carries a `cong` step whose
/// operands are that constant — printed from the AUTHORED spelling on one side
/// and the canonical one on the other.
#[cfg(test)]
fn row1_derived_index_equality(
    p0_index: &str,
    p1_index: &str,
    written: &str,
    read_back: &str,
) -> String {
    format!(
        "(declare-const mem (Array (_ BitVec 8) (_ BitVec 8)))\n\
         (declare-const p0 (_ BitVec 8))\n\
         (declare-const p1 (_ BitVec 8))\n\
         (declare-const mem2 (Array (_ BitVec 8) (_ BitVec 8)))\n\
         (assert (= p0 {p0_index}))\n\
         (assert (= p1 {p1_index}))\n\
         (assert (= mem2 (store mem p0 {written})))\n\
         (assert (= (select mem2 p1) {read_back}))\n"
    )
}

/// Assert that this solve's ORDINARY Alethe render was refused for the
/// AUTHORED SPELLING and that withholding the authored overrides rescues it.
///
/// Both halves are load-bearing. The first puts `export_last_unsat_artifact`
/// into its broad `Err(_)` arm; the second establishes that the arm's own
/// `?` / `.ok()?` both succeed, so anything the boundary does with the
/// artifact after that point is the VERDICT GATE's doing and nothing else's.
///
/// `expected` names the refusal this fixture is CHOSEN for, and `what` says
/// what the fixture does to provoke it. Both cells below guard their own
/// refusal rather than accepting any `Err`, so an upstream printer improvement
/// that makes a fixture printable fails here as drift instead of quietly
/// leaving the gate untested — which is exactly how the accepted cell's
/// previous fixture was caught.
#[cfg(test)]
fn assert_authored_spelling_refusal_is_rescued(
    solver: &Solver,
    what: &str,
    expected: impl Fn(&ay_proof::AlethePrintError) -> bool,
) {
    let ordinary = solver
        .executor
        .try_export_last_proof_alethe_for_problem_scope();
    assert!(
        matches!(&ordinary, Some(Err(error)) if expected(error)),
        "fixture drift: {what} must make the printer refuse; got {ordinary:?}",
    );
    let canonical = solver
        .executor
        .try_export_last_proof_alethe_for_problem_scope_canonical();
    assert!(
        matches!(canonical, Some(Ok(_))),
        "fixture drift: withholding the authored overrides must RESCUE this \
         render, or the verdict gate below is never reached; got {canonical:?}",
    );
}

/// A print refusal the AUTHORED SPELLING caused, on a refutation the strict
/// checker ACCEPTS, is rescued into a published artifact.
///
/// This is `5da3d563d`'s whole point and the accepted side of the verdict gate
/// in `export_last_unsat_artifact`. It uses the ROW1 derived-index-equality
/// refutation of
/// `api::tests::test_proof_artifact::qfabv_row1_derived_index_equality_is_strict_verified`,
/// pinned at the boundary itself, stating each step of the mechanism rather
/// than only its outcome.
///
/// The authored spelling here is a CONSTANT-FOLDED index, written differently
/// at its two uses: `(bvudiv #x20 #x02)` for `p0` and `(bvudiv #x40 #x04)` for
/// `p1`. Elaboration folds both, and `#b00010000` is the canonical term the
/// strict checker validated. The refutation lifts the derived index equality
/// onto the store through a `cong` step, and printing that step from the
/// authored overrides puts two spellings of one constant in congruent
/// positions. They are not two spellings of one literal (which the printer
/// bridges with `refl`, and which is why this cell no longer uses the plain
/// numeral `#x10`), and no arithmetic identity the printer knows relates
/// them, so it refuses:
///
///     InvalidCongruenceStep { id: ProofId(4), reason: "printed congruence
///     operands are not position-preserving congruence over exact arithmetic
///     identities; left=\"(bvudiv #x20 #x02)\"; right=\"#b00010000\";
///     canonical=\"#b00010000\"" }
///
/// Nor does the raw-root ground closure, the last wire-gap retry for a
/// native-strict proof, replace the refutation with one of the AUTHORED roots,
/// and that is why the two uses are spelled differently. With one folded
/// spelling at both (`(bvadd #x08 #x08)`, this cell's previous fixture) `p0`
/// and `p1` equal one authored term, the closure merges them by transitivity
/// without evaluating it, and its refutation prints as authored and Carcara
/// `valid` (group_proofs
/// `test_carcara_trust_free_authored_folded_bv_index_shared_term`). Two
/// spellings meet only by EVALUATION, and `bvudiv` is outside the closure's
/// `EVALUATED_OPERATORS`: pinned Carcara refuses the divider steps that
/// evaluation prints. (Two `bvadd` spellings refuse today too, but only
/// because neither use is the constant an evaluation would meet at: a
/// completeness gap of the closure, not a guard.)
///
/// It is RIGHT to refuse — it must never disclose a document AY cannot replay
/// — and the derivation is untouched by it: the canonical re-render succeeds
/// and the strict checker accepts.
///
/// The CONTROL re-authors the identical problem in the canonical binary
/// spelling. Nothing is refused, no rescue runs, and the same `Verified`
/// verdict is published — so the refusal above is the authored SPELLING's
/// doing and not the derivation's. Together with
/// [`assert_authored_spelling_refusal_is_rescued`], that makes publication
/// here attributable to the rescue and to nothing else.
///
/// Note what is published: `alethe` and `alethe_problem_smt2` are the
/// CANONICAL render, not the authored text. The rescue restores the DECISION
/// this boundary would have taken had the spelling been printable; it does not
/// restore the spelling.
#[test]
fn a_rescued_authored_spelling_refusal_publishes_an_accepted_verdict() {
    let mut solver = Solver::new(Logic::QfAbv);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(&row1_derived_index_equality(
            "(bvudiv #x20 #x02)",
            "(bvudiv #x40 #x04)",
            "#xAA",
            "#xBB",
        ))
        .expect("parse the folded-index ROW1 derived-index-equality fixture");
    assert!(solver.check_sat().is_unsat());

    assert_authored_spelling_refusal_is_rescued(
        &solver,
        "the authored `(bvudiv #x20 #x02)` index against the canonical \
         `#b00010000` in a ROW1 congruence lift, beside a differently \
         spelled second use the ground closure cannot meet without \
         evaluating `bvudiv`",
        |error| {
            matches!(
                error,
                ay_proof::AlethePrintError::InvalidCongruenceStep { .. }
            )
        },
    );
    solver
        .last_strict_proof_quality()
        .expect("the refutation must be retained")
        .unwrap_or_else(|error| panic!("fixture drift: strict checker rejected it: {error}"));

    let artifact = solver
        .export_last_unsat_artifact()
        .expect("an authored-spelling refusal over an ACCEPTED verdict must publish");
    assert!(
        matches!(&artifact.strict_verdict, StrictProofVerdict::Verified(_)),
        "{:?}",
        artifact.strict_verdict,
    );
    // The disclosed document is the canonical spelling, paired with the
    // canonical problem transport so the two agree throughout.
    assert_ne!(artifact.alethe, "");
    assert!(
        artifact.alethe_problem_smt2.is_some(),
        "the rescued document must ship its paired canonical problem transport",
    );
    assert!(
        !artifact.alethe.contains("bvudiv"),
        "the published document must be the CANONICAL render, not the authored \
         spelling the printer refused:\n{}",
        artifact.alethe,
    );
    // A caller that holds its own (AUTHORED) problem — a push/pop session —
    // cannot check the canonical document against it, so the session export
    // ships the canonical problem after a rescue too, the same bytes.
    let session = solver
        .export_last_unsat_artifact_without_problem_transport()
        .expect("the session export publishes the same rescued artifact");
    assert_eq!(session.alethe, artifact.alethe);
    assert_eq!(
        session.alethe_problem_smt2, artifact.alethe_problem_smt2,
        "a rescued document must carry the canonical problem it matches, \
         whatever transport the caller asked for",
    );

    // CONTROL. The identical problem, authored in the canonical binary
    // spelling: no refusal, no rescue, and the same verdict is published.
    let mut control = Solver::new(Logic::QfAbv);
    control.set_produce_proofs(true);
    control
        .parse_smtlib2(&row1_derived_index_equality(
            "#b00010000",
            "#b00010000",
            "#b10101010",
            "#b10111011",
        ))
        .expect("parse the binary-authored ROW1 derived-index-equality fixture");
    assert!(control.check_sat().is_unsat());
    assert!(
        matches!(
            control
                .executor
                .try_export_last_proof_alethe_for_problem_scope(),
            Some(Ok(_)),
        ),
        "control drift: the canonical numeral spelling must print without a \
         refusal, or the refusal above is not the authored spelling's doing",
    );
    let published = control
        .export_last_unsat_artifact()
        .expect("without a rescue, an accepted verdict publishes exactly as before");
    assert!(
        matches!(&published.strict_verdict, StrictProofVerdict::Verified(_)),
        "control drift: expected the same verified verdict, got {:?}",
        published.strict_verdict,
    );
}

/// The verdict gate itself: an authored-spelling refusal, a successful
/// canonical rescue, over a refutation the strict checker REJECTS. The
/// artifact must be withdrawn again.
///
/// Before `5da3d563d` every print refusal returned `None` here, so publishing
/// this would be new behaviour that the rescue never claimed: a document on
/// the record where there had never been one, read by any consumer that
/// inspects `alethe` without inspecting the verdict.
///
/// Two controls make this a test OF THE GATE rather than of anything else that
/// returns `None`:
///
///   * [`assert_authored_spelling_refusal_is_rescued`] establishes that the
///     rescue's `?` and `.ok()?` both succeed, so the boundary really does
///     reach the gate with an artifact in hand;
///   * `flat_authored_grouping` re-authors the identical conjuncts in the
///     canonical spelling. Nothing is refused, so no rescue runs, and the very
///     same `Rejected` verdict IS published. A rejected verdict is not what
///     withdraws an artifact at this boundary — a rejected verdict reached
///     THROUGH THE RESCUE is.
#[test]
fn a_rescued_authored_spelling_refusal_may_not_publish_a_rejected_verdict() {
    // `(= (* a a) 2)` has no integer solution, and the refutation leans on a
    // `Generic` theory lemma the strict checker will not validate. Best-effort
    // collection is what retains such a proof: an explicit `:produce-proofs`
    // demand makes the artifact mandatory, and the certification funnel then
    // withholds the verdict itself rather than publishing an unchecked one.
    const REJECTED_BODY: &str = "(= (* a a) 2)";

    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfNia);
    solver.set_best_effort_produce_proofs(1_000_000);
    solver
        .parse_smtlib2(&folded_authored_grouping(
            RESCUE_FIXTURE_DECLS,
            REJECTED_BODY,
        ))
        .expect("parse the folded authored grouping");
    assert!(solver.check_sat().is_unsat());

    assert_authored_spelling_refusal_is_rescued(
        &solver,
        "the authored grouping, whose `and_pos` projection the printer cannot \
         find for this body",
        |error| matches!(error, ay_proof::AlethePrintError::InvalidSurfaceStep { .. }),
    );
    let strict_error = solver
        .last_strict_proof_quality()
        .expect("the refutation must be retained")
        .expect_err("fixture drift: the strict checker must REJECT this refutation");
    assert!(
        solver.export_last_unsat_artifact().is_none(),
        "the canonical-spelling rescue may only ever turn a `None` into a \
         strictly ACCEPTED artifact; this verdict is {strict_error}",
    );

    // CONTROL. The identical conjuncts, authored canonically: no refusal, no
    // rescue, and the same rejected verdict is published as it always was.
    #[allow(deprecated)]
    let mut control = Solver::new(Logic::QfNia);
    control.set_best_effort_produce_proofs(1_000_000);
    control
        .parse_smtlib2(&flat_authored_grouping(RESCUE_FIXTURE_DECLS, REJECTED_BODY))
        .expect("parse the flat authored grouping");
    assert!(control.check_sat().is_unsat());
    assert!(
        matches!(
            control
                .executor
                .try_export_last_proof_alethe_for_problem_scope(),
            Some(Ok(_)),
        ),
        "control drift: the canonical spelling must print without a refusal",
    );
    let published = control
        .export_last_unsat_artifact()
        .expect("without a rescue, a rejected verdict publishes exactly as before");
    assert!(
        matches!(&published.strict_verdict, StrictProofVerdict::Rejected(_)),
        "control drift: expected the same rejected verdict, got {:?}",
        published.strict_verdict,
    );
}

/// `export_last_unsat_artifact` rescues a print refusal by RE-RENDERING the
/// same checked refutation with the authored source-syntax overrides withheld.
/// That rescue is for one thing only: a refusal the AUTHORED SPELLING caused.
///
/// The discriminator is the retry itself, not the error type — `AlethePrintError`
/// carries no provenance field and every variant the authored channel can raise
/// is also raised for causes that have nothing to do with it. So this pins the
/// third cell: a refusal the authored channel did NOT cause is not rescued and
/// the artifact is still withdrawn, even though `check_proof_strict` ACCEPTS
/// the derivation and a native bundle for it is exportable and
/// offline-recheckable.
///
/// The refusal here is `UnavailableAuthenticatedSurface`: a sealed finite-enum
/// proof whose external presentation authority is absent. Withholding a
/// presentation preference cannot conjure that authority, which is exactly why
/// this must not become an artifact.
///
/// MEASURED, and stated exactly because the two outcomes are not the same
/// fact: the canonical exporter does not raise this refusal again — it
/// DECLINES the fixture outright and returns `None`, because a sealed
/// finite-enum proof's surface overrides are its authority rather than a
/// presentation preference, so there is no canonical spelling to fall back to.
/// Either outcome withdraws the artifact, and the boundary treats them alike;
/// the assertions below still distinguish them, so a change from one to the
/// other cannot pass unnoticed.
#[test]
fn an_override_independent_print_refusal_still_withdraws_the_artifact() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfDt);
    solver.set_produce_proofs(true);
    let mut deep_true = "true".to_string();
    for _ in 0..300 {
        deep_true = format!("(not {deep_true})");
    }
    let script = format!(
        "(declare-datatype Unit ((u0) (u1) (u2)))\n\
         (declare-const p0 Unit)\n\
         (declare-const p1 Unit)\n\
         (declare-const p2 Unit)\n\
         (declare-const p3 Unit)\n\
         (assert {deep_true})\n\
         (assert (distinct p0 p1))\n\
         (assert (not (= p0 p2)))\n\
         (assert (not (= p0 p3)))\n\
         (assert (not (= p1 p2)))\n\
         (assert (not (= p1 p3)))\n\
         (assert (not (= p2 p3)))\n"
    );
    solver
        .parse_smtlib2(&script)
        .expect("parse surface-less finite-enum clique");
    assert!(solver.check_sat().is_unsat());

    // The derivation is sound: the strict checker accepts it, so nothing about
    // the PROOF is what withdraws the artifact.
    solver
        .last_strict_proof_quality()
        .expect("the refutation must be retained")
        .unwrap_or_else(|error| panic!("strict checker rejected the refutation: {error}"));

    // The refusal is a print refusal, and an override-independent one.
    let ordinary = solver
        .executor
        .try_export_last_proof_alethe_for_problem_scope();
    assert!(
        matches!(
            ordinary,
            Some(Err(
                ay_proof::AlethePrintError::UnavailableAuthenticatedSurface { .. }
            ))
        ),
        "{ordinary:?}",
    );
    // Withholding the authored spellings does not make it printable. For this
    // sealed fixture the canonical exporter declines outright rather than
    // raising the same error, and `None` is the exact observation.
    let canonical = solver
        .executor
        .try_export_last_proof_alethe_for_problem_scope_canonical();
    assert!(
        canonical.is_none(),
        "a sealed finite-enum proof has no canonical fallback spelling; got {canonical:?}",
    );
    assert!(
        solver.export_last_unsat_artifact().is_none(),
        "only an AUTHORED-SPELLING refusal may be rescued into an artifact",
    );
}
