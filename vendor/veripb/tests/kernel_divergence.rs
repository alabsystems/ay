//! The reject path of `--kernel-verify`.
//!
//! `tests/kernel_verify.rs` pins that the bridge's hooks *fire* (the coverage
//! snapshot) and that the flag never changes a verdict on the corpus. Neither
//! pins the thing that makes the flag more than a counter: that a live result
//! the kernel *disagrees with* is **rejected**. No corpus instance triggers a
//! divergence — none can, since the corpus is a set of proofs the live checker
//! gets right — so without this file a bridge whose comparators all returned
//! `Ok(None)` would pass the whole test tree.
//!
//! Every case here is a pair: a wrong live result that must produce
//! `CheckingError::KernelDivergence`, next to the honest twin that must be
//! accepted. Without the twin the file could pass vacuously by erroring on
//! everything. Assertions are on the *variant*, never on the message text,
//! which is prose and will drift.
//!
//! This is also why `kernel_bridge`'s comparators are `pub`: they are the API
//! this file drives directly, one wrong answer at a time, which no end-to-end
//! proof can reach.

use malachite_bigint::BigInt;
use veripb_checker::database::Database;
use veripb_checker::error::CheckingError;
use veripb_checker::kernel_bridge::{
    verify_contradiction, verify_db_lookup, verify_db_solution, verify_implication,
    verify_objective_value, verify_pol, verify_solution, verify_trivial,
};
use veripb_formula::clause::Clause;
use veripb_formula::pb_constraint::constraint_from_terms;
use veripb_formula::prelude::*;
use veripb_rules::Instruction;

fn lit(var: usize, positive: bool) -> Lit {
    Lit::from_var(var, !positive)
}

/// `sum coeff_i * lit_i >= degree` in the live representation.
fn pb(terms: &[(i64, Lit)], degree: i64) -> PBConstraintEnum {
    constraint_from_terms(
        terms
            .iter()
            .map(|&(c, l)| GeneralPBTerm::new(c, l))
            .collect(),
        degree,
    )
}

fn clause(lits: &[Lit]) -> PBConstraintEnum {
    Clause::from_unnormalized_lits(lits.to_vec())
}

fn diverged<T: std::fmt::Debug>(r: &Result<T, CheckingError>) -> bool {
    matches!(r, Err(CheckingError::KernelDivergence(_)))
}

// ---------------------------------------------------------------------------
// pol
// ---------------------------------------------------------------------------

/// The highest-value case: the live checker claims a `pol` derivation produced
/// something the kernel's replay of the same program did not.
#[test]
fn verify_pol_rejects_a_result_the_replay_does_not_reach() {
    let x1 = lit(1, true);
    let x2 = lit(2, true);
    let x3 = lit(3, true);
    let db = Database::from_formula(vec![clause(&[x1, x2]), clause(&[lit(1, false), x3])]);
    let program = [
        Instruction::ConstraintId(1),
        Instruction::ConstraintId(2),
        Instruction::Add,
    ];

    // The honest twin: adding `x1 + x2 >= 1` and `~x1 + x3 >= 1` cancels the
    // `x1` pair and leaves `x2 + x3 >= 1`.
    let honest = verify_pol(&program, &db, None, &pb(&[(1, x2), (1, x3)], 1));
    assert!(
        matches!(&honest, Ok(outcome) if outcome.check.is_none()),
        "the true sum must be re-derived, got {honest:?}"
    );

    // One unit stronger than the derivation yields. This is the class of
    // wrong-verdict defect the flag exists to catch: a degree that came out
    // too high turns satisfiable formulas into refutations.
    let wrong = verify_pol(&program, &db, None, &pb(&[(1, x2), (1, x3)], 2));
    assert!(
        diverged(&wrong),
        "a too-strong pol result must diverge, got {wrong:?}"
    );
}

/// The other `pol` rejection: the replay ends with a different stack shape
/// than the live machine did, so the two did not execute the same program.
#[test]
fn verify_pol_rejects_a_stack_shape_mismatch() {
    let x1 = lit(1, true);
    let x2 = lit(2, true);
    let db = Database::from_formula(vec![clause(&[x1, x2]), clause(&[lit(1, false)])]);
    // Two pushes and no `Add`: the live machine handed back one constraint.
    let program = [Instruction::ConstraintId(1), Instruction::ConstraintId(2)];
    let wrong = verify_pol(&program, &db, None, &pb(&[(1, x2)], 1));
    assert!(
        diverged(&wrong),
        "a leftover shadow stack must diverge, got {wrong:?}"
    );
}

// ---------------------------------------------------------------------------
// trivial / db-lookup / contradiction
// ---------------------------------------------------------------------------

#[test]
fn verify_trivial_rejects_a_constraint_with_a_positive_degree() {
    let x1 = lit(1, true);
    // `x1 + x2 >= 1` is not trivially true.
    let wrong = verify_trivial(&clause(&[x1, lit(2, true)]));
    assert!(
        diverged(&wrong),
        "a non-trivial accept must diverge, got {wrong:?}"
    );
    // `x1 >= 0` is: the normalized degree is at most zero.
    assert_eq!(verify_trivial(&pb(&[(1, x1)], 0)).unwrap(), None);
}

#[test]
fn verify_db_lookup_rejects_two_unequal_constraints() {
    let x1 = lit(1, true);
    let goal = clause(&[x1, lit(2, true)]);
    let found = clause(&[x1]);
    assert!(
        diverged(&verify_db_lookup(&goal, &found)),
        "a lookup that found a different constraint must diverge"
    );
    assert_eq!(verify_db_lookup(&goal, &goal.clone()).unwrap(), None);
}

#[test]
fn verify_contradiction_rejects_a_satisfiable_constraint() {
    let x1 = lit(1, true);
    assert!(
        diverged(&verify_contradiction(&clause(&[x1]))),
        "`x1 >= 1` is satisfiable and must not pass as a contradiction"
    );
    // The genuine article: `0 >= 1`.
    assert_eq!(verify_contradiction(&pb(&[], 1)).unwrap(), None);
}

// ---------------------------------------------------------------------------
// solutions
// ---------------------------------------------------------------------------

fn assignment(values: &[(usize, bool)], size: usize) -> Assignment<BooleanVar> {
    let mut a = Assignment::<BooleanVar>::with_size(size);
    for &(var, value) in values {
        a.set_value(var, BoolValue::Assigned(value));
    }
    a
}

#[test]
fn verify_solution_rejects_a_falsifying_assignment() {
    let x1 = lit(1, true);
    let constraints = vec![clause(&[x1])];
    assert!(
        diverged(&verify_solution(
            &constraints,
            &assignment(&[(1, false)], 2)
        )),
        "an assignment falsifying an original constraint must diverge"
    );
    assert_eq!(
        verify_solution(&constraints, &assignment(&[(1, true)], 2)).unwrap(),
        None
    );
}

#[test]
fn verify_db_solution_rejects_a_falsifying_assignment() {
    let x1 = lit(1, true);
    let mut db = Database::from_formula(vec![clause(&[x1])]);
    // TRAP: `Database::from_formula` leaves `unique_constraints` empty — it is
    // filled lazily — so without this the check iterates zero constraints and
    // returns `Ok(None)` on any assignment at all. Do not "simplify" it away.
    db.update_unique_index(&mut veripb_checker::utils::new_veripb_propagation_engine())
        .expect("indexing a two-constraint database cannot fail");
    assert!(
        diverged(&verify_db_solution(&db, &assignment(&[(1, false)], 2))),
        "an assignment falsifying a database constraint must diverge"
    );
    assert_eq!(
        verify_db_solution(&db, &assignment(&[(1, true)], 2)).unwrap(),
        None
    );
}

// ---------------------------------------------------------------------------
// objective values
// ---------------------------------------------------------------------------

#[test]
fn verify_objective_value_rejects_a_wrong_total() {
    let x1 = lit(1, true);
    let objective = PBObjective::from_terms(
        vec![GeneralPBTerm::new(BigInt::from(3), x1)],
        BigInt::from(0),
        false,
    );
    let a = assignment(&[(1, true)], 2);
    assert_eq!(
        verify_objective_value(&objective, &a, &BigInt::from(3)).unwrap(),
        None
    );
    assert!(
        diverged(&verify_objective_value(&objective, &a, &BigInt::from(5))),
        "a claimed value the exact recomputation contradicts must diverge"
    );
    // The second arm: an objective literal the assignment leaves unassigned,
    // so the claimed value cannot be recomputed at all.
    let unassigned = Assignment::<BooleanVar>::with_size(2);
    assert!(
        diverged(&verify_objective_value(
            &objective,
            &unassigned,
            &BigInt::from(0)
        )),
        "an unassigned objective literal must diverge"
    );
}

// ---------------------------------------------------------------------------
// implication: no divergence arm, but no false accept either
// ---------------------------------------------------------------------------

/// `verify_implication` has no divergence arm by design — the live `implies()`
/// may accept shapes the proved chain cannot reconstruct, and that is a
/// counted skip. What must never happen is an `Ok(None)` on a non-implication:
/// that would be the chain claiming a derivation it did not perform.
#[test]
fn verify_implication_never_accepts_a_non_implication() {
    let x1 = lit(1, true);
    let x2 = lit(2, true);
    let weak = clause(&[x1, x2]);
    let strong = clause(&[x1]);
    assert_eq!(
        verify_implication(&strong, &weak).unwrap(),
        None,
        "`x1 >= 1` implies `x1 + x2 >= 1` and the chain must derive it"
    );
    assert_ne!(
        verify_implication(&weak, &strong).unwrap(),
        None,
        "`x1 + x2 >= 1` does not imply `x1 >= 1` and must never be accepted"
    );
}

// ---------------------------------------------------------------------------
// a generic guard against a comparator that stops comparing
// ---------------------------------------------------------------------------

/// Brute-force oracle over three variables: whatever the comparators accept
/// must be semantically justified. This is what would catch a comparator that
/// starts returning `Ok(None)` unconditionally even on shapes no hand-written
/// case above covers.
#[test]
fn every_accept_is_semantically_justified_on_small_random_constraints() {
    // xorshift64, so the test is deterministic and needs no dependency.
    let mut s: u64 = 0x9E37_79B9_7F4A_7C15;
    let mut next = || {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        s
    };
    let models = |c: &PBConstraintEnum| -> Vec<bool> {
        (0u32..8)
            .map(|bits| {
                let a = assignment(
                    &[(1, bits & 1 != 0), (2, bits & 2 != 0), (3, bits & 4 != 0)],
                    4,
                );
                c.is_satisfied(&a)
            })
            .collect()
    };
    let mut random_constraint = || {
        let mut terms: Vec<GeneralPBTerm<i64>> = Vec::new();
        for v in 1..=3 {
            if next() % 4 == 0 {
                continue;
            }
            let coeff = (next() % 7) as i64 - 3;
            let positive = next() % 2 == 0;
            terms.push(GeneralPBTerm::new(coeff, lit(v, positive)));
        }
        constraint_from_terms(terms, (next() % 8) as i64 - 2)
    };

    let mut trivial_accepts = 0usize;
    let mut implication_accepts = 0usize;
    for _ in 0..20_000 {
        let a = random_constraint();
        let b = random_constraint();
        let ma = models(&a);
        let mb = models(&b);

        if verify_trivial(&a).is_ok_and(|r| r.is_none()) {
            assert!(
                ma.iter().all(|&m| m),
                "accepted a non-tautology as trivial: {a:?}"
            );
            trivial_accepts += 1;
        }
        if verify_contradiction(&a).is_ok_and(|r| r.is_none()) {
            assert!(
                ma.iter().all(|&m| !m),
                "accepted a satisfiable constraint as 0 >= 1: {a:?}"
            );
        }
        if verify_implication(&a, &b).is_ok_and(|r| r.is_none()) {
            assert!(
                ma.iter().zip(&mb).all(|(&x, &y)| !x || y),
                "accepted a non-implication: {a:?} |= {b:?}"
            );
            implication_accepts += 1;
        }
    }
    // The oracle must actually reach the accepting paths, or it proves
    // nothing about them.
    assert!(
        trivial_accepts > 100,
        "only {trivial_accepts} trivial accepts generated"
    );
    assert!(
        implication_accepts > 100,
        "only {implication_accepts} implication accepts generated"
    );
}

// ---------------------------------------------------------------------------
// the RUP replays and the shadow-slot comparisons
// ---------------------------------------------------------------------------

/// The reject arms the eight comparators above do not reach.
///
/// Everything before this module drives a comparator that takes a live result
/// and re-judges it. Six further `KernelDivergence` sites live behind the RUP
/// replays and the shadow database, and none of them had a test: each could be
/// replaced by an unconditional accept and the whole workspace suite stayed
/// green — including `tests/kernel_verify_expected.txt`, since a neutered arm
/// still counts its step as *verified*, so not even a re-bless would have
/// exposed it. One of the six is the arm the README credits with catching two
/// of the eighteen wrong verdicts (`RUP conflict certificate rejected by the
/// proved kernel: NoConflict`).
///
/// Same discipline as the rest of the file: every case is a wrong/honest pair,
/// and assertions are on the `CheckingError` *variant*, never on message prose.
///
/// This is a module rather than more free functions only so that the extra
/// imports it needs sit next to the tests that use them.
mod rup_replay_and_shadow_slots {
    use super::{clause, diverged, lit, pb};
    use std::rc::Rc;
    use veripb_checker::config::CheckerConfig;
    use veripb_checker::context::Context;
    use veripb_checker::database::Database;
    use veripb_checker::kernel_bridge::{
        KernelShadowDb, consume_implication_derivation, consume_pol, shadow_record_added,
        verify_hinted_rup, verify_pol, verify_rup_certificate, verify_substituted_implication,
    };
    use veripb_formula::prelude::*;
    use veripb_propagator::propagation_engine::KernelCertificate;
    use veripb_propagator::trail::{Propagation, Reason, Trail};
    use veripb_rules::Instruction;

    /// A `--kernel-verify` context with an empty shadow database.
    fn context() -> Context {
        Context::new(
            CheckerConfig {
                kernel_verify: true,
                ..Default::default()
            },
            Default::default(),
            None,
        )
    }

    /// A certificate that claims the constraint at live id 1 is the conflict,
    /// with no propagations before it.
    fn conflict_at_id_1(database: &Database) -> KernelCertificate {
        KernelCertificate {
            steps: Vec::new(),
            conflict: Reason::Constraint(Rc::clone(database.get_entry_usize(1).unwrap())),
            negated: None,
        }
    }

    /// A shadow database whose slot at live id 1 holds the literal axiom
    /// `x1 >= 0`, built entirely through the public bridge API.
    ///
    /// `shadow_init` is deliberately not used: it takes the slots straight from
    /// a live database, so it can only ever produce a shadow that *agrees* with
    /// one. Driving `consume_pol` on a literal-axiom program and then
    /// `shadow_record_added` mirrors what a real run does — a rule offers a
    /// kernel-justified constraint, the checker stores it at the next id — and
    /// leaves the slot free to be compared against a *different* live database
    /// below. Slot 0 is a hole, as it is in a real run: live id 0 is the
    /// never-populated dummy entry.
    fn shadow_holding_the_axiom_at_id_1(axiom: &PBConstraintEnum, x1: Lit) -> KernelShadowDb {
        let mut context = context();
        let empty = Database::from_formula(Vec::new());
        shadow_record_added(&mut context, 0, axiom, "live id 0 is the dummy entry");
        consume_pol(
            &mut context,
            &empty,
            &[Instruction::LiteralAxiom(x1)],
            axiom,
        )
        .expect("a literal axiom is kernel-justified from nothing");
        shadow_record_added(
            &mut context,
            1,
            axiom,
            "unreached: the pol above justified it",
        );
        context
            .kernel_shadow
            .take()
            .expect("kernel_verify was on, so the context has a shadow")
    }

    /// The arm README.md credits with catching wrong-verdict defects 10 and 18:
    /// the checker reports a RUP conflict, and the kernel's replay of the very
    /// same trail reaches no conflict at all.
    #[test]
    fn verify_rup_certificate_rejects_a_conflict_the_kernel_replay_does_not_reach() {
        let x1 = lit(1, true);
        let x2 = lit(2, true);

        // `x1 + x2 >= 1` is not conflicting under the empty assignment, so
        // naming it as the conflict is a claim the kernel must refuse.
        let database = Database::from_formula(vec![clause(&[x1, x2])]);
        let wrong = verify_rup_certificate(None, &conflict_at_id_1(&database), &database, None);
        assert!(
            diverged(&wrong),
            "a conflict claim the kernel replay does not reach must diverge, got {wrong:?}"
        );

        // The honest twin: `0 >= 1` really is conflicting.
        let database = Database::from_formula(vec![pb(&[], 1)]);
        let honest = verify_rup_certificate(None, &conflict_at_id_1(&database), &database, None);
        assert!(
            matches!(&honest, Ok(outcome) if outcome.check.is_none()),
            "a genuine `0 >= 1` conflict must be re-derived, got {honest:?}"
        );
    }

    /// The same rejection with a shadow attached, so the *substituted* replay
    /// is covered too. `ReasonView::replay` re-runs the whole check on the
    /// unsubstituted constraints before it diverges, precisely so that
    /// substituting proved normal forms can never cost a verdict; the case
    /// above only reaches the unsubstituted path.
    #[test]
    fn verify_rup_certificate_rejects_a_non_conflict_through_the_substituted_replay_too() {
        let x1 = lit(1, true);
        let axiom = pb(&[(1, x1)], 0);
        let shadow = shadow_holding_the_axiom_at_id_1(&axiom, x1);

        // The live database agrees with the shadow, so the replay really is
        // substituted -- and `x1 >= 0` is not a conflict either way.
        let database = Database::from_formula(vec![axiom.clone()]);
        let wrong =
            verify_rup_certificate(None, &conflict_at_id_1(&database), &database, Some(&shadow));
        assert!(
            diverged(&wrong),
            "a non-conflict must still diverge once the reason came from a shadow slot, \
             got {wrong:?}"
        );
    }

    /// Hinted RUP names its reasons by database id instead of carrying an
    /// engine certificate, so it has its own replay and its own rejection: the
    /// checker accepted the step, and kernel propagation over exactly those
    /// hints reaches a fixpoint with no conflict.
    #[test]
    fn verify_hinted_rup_rejects_hints_that_do_not_propagate_to_a_conflict() {
        let x1 = lit(1, true);
        let x2 = lit(2, true);

        // `x1 + x2 >= 1` does not imply `x1 >= 1`: negating the target leaves
        // `x2` free, so propagation stops without a conflict.
        let database = Database::from_formula(vec![clause(&[x1, x2])]);
        let hints = [(1usize, Rc::clone(database.get_entry_usize(1).unwrap()))];
        let wrong = verify_hinted_rup(&clause(&[x1]), &hints, &database, None);
        assert!(
            diverged(&wrong),
            "a hinted RUP whose hints reach no conflict must diverge, got {wrong:?}"
        );

        // The honest twin: `x1 >= 1` does imply `x1 + x2 >= 1`.
        let database = Database::from_formula(vec![clause(&[x1])]);
        let hints = [(1usize, Rc::clone(database.get_entry_usize(1).unwrap()))];
        let honest = verify_hinted_rup(&clause(&[x1, x2]), &hints, &database, None);
        assert!(
            matches!(&honest, Ok(outcome) if outcome.check.is_none()),
            "a hinted RUP the hints do imply must be re-derived, got {honest:?}"
        );
    }

    /// Substituted implication is accepted by certifying every trail literal
    /// the source consumed as a unit derived from the trail prefix. A literal
    /// whose stated reason does not propagate it is the rejection.
    #[test]
    fn verify_substituted_implication_rejects_a_trail_unit_the_kernel_cannot_certify() {
        let x1 = lit(1, true);
        let x2 = lit(2, true);
        // id 1 is `x2 >= 1`, id 2 is `x1 >= 1`.
        let database = Database::from_formula(vec![clause(&[x2]), clause(&[x1])]);
        let unit = |id: usize| {
            let mut trail = Trail::with_size(8);
            trail
                .push(
                    Propagation::new(
                        x1,
                        Reason::Constraint(Rc::clone(database.get_entry_usize(id).unwrap())),
                    ),
                    false,
                )
                .expect("a fresh trail accepts an unassigned literal");
            trail
        };

        // `x2 >= 1` does not propagate `x1`, so the trail unit cannot be
        // certified from it.
        let wrong = verify_substituted_implication(&clause(&[x1]), &clause(&[x1]), &unit(1));
        assert!(
            diverged(&wrong),
            "a trail unit the kernel cannot certify must diverge, got {wrong:?}"
        );

        // The honest twin: `x1 >= 1` is exactly the reason that propagates it.
        let honest = verify_substituted_implication(&clause(&[x1]), &clause(&[x1]), &unit(2));
        assert_eq!(
            honest.as_ref().ok().copied(),
            Some(None),
            "the reason that really propagates the literal must be accepted, got {honest:?}"
        );
    }

    /// The three shadow-slot-versus-live-entry comparisons, which are the whole
    /// point of §7.4's "strengthened leaves": a `pol` leaf, a RUP reason and an
    /// implication source are each replayed as the *shadow slot's* constraint,
    /// and the live entry at that id must still be it. A mismatch means the
    /// live database drifted from the derivation that produced it, which is a
    /// divergence and never a skip.
    ///
    /// Each case runs the same shadow against two live databases: one holding
    /// the constraint the shadow justified (accepted) and one holding something
    /// else at the same id (rejected).
    #[test]
    fn a_shadow_slot_that_is_not_the_live_entry_diverges_at_every_site_that_reads_one() {
        let x1 = lit(1, true);
        let x2 = lit(2, true);
        let axiom = pb(&[(1, x1)], 0);
        let agreeing = Database::from_formula(vec![axiom.clone()]);
        let drifted = Database::from_formula(vec![clause(&[x1, x2])]);

        // (a) `resolve_pol_leaf`: a `ConstraintId` leaf of a `pol` program.
        let shadow = shadow_holding_the_axiom_at_id_1(&axiom, x1);
        let leaf = [Instruction::ConstraintId(1)];
        let wrong = verify_pol(&leaf, &drifted, Some(&shadow), &clause(&[x1, x2]));
        assert!(
            diverged(&wrong),
            "a pol leaf whose slot is not the live entry must diverge, got {wrong:?}"
        );
        let honest = verify_pol(&leaf, &agreeing, Some(&shadow), &axiom);
        assert!(
            matches!(&honest, Ok(outcome) if outcome.check.is_none()),
            "the same leaf over the agreeing database must be re-derived, got {honest:?}"
        );

        // (b) `resolve_reason`: the same id reached as a RUP reason.
        let wrong =
            verify_rup_certificate(None, &conflict_at_id_1(&drifted), &drifted, Some(&shadow));
        assert!(
            diverged(&wrong),
            "a RUP reason whose slot is not the live entry must diverge, got {wrong:?}"
        );

        // (c) `implication_derivation_outcome`, reached through its public
        // wrapper because the tier-level function is private. `x1 >= 0` is
        // implied by everything, so only the slot comparison can reject here.
        let mut ctx = context();
        ctx.kernel_shadow = Some(shadow_holding_the_axiom_at_id_1(&axiom, x1));
        let wrong = consume_implication_derivation(&mut ctx, &drifted, 1, &axiom);
        assert!(
            diverged(&wrong),
            "an implication source whose slot is not the live entry must diverge, got {wrong:?}"
        );

        let mut ctx = context();
        ctx.kernel_shadow = Some(shadow_holding_the_axiom_at_id_1(&axiom, x1));
        let honest = consume_implication_derivation(&mut ctx, &agreeing, 1, &axiom);
        assert!(
            honest.is_ok(),
            "the same derivation over the agreeing database must be accepted, got {honest:?}"
        );
        assert_eq!(
            ctx.kernel_stats.implication_verified, 1,
            "the accepted derivation must be counted as re-derived, not skipped: {:?}",
            ctx.kernel_stats.skipped
        );
    }
}

// ---------------------------------------------------------------------------
// the formula cross-check
// ---------------------------------------------------------------------------

/// Drive `shadow_init`'s formula cross-check directly: write `text` to a
/// file with the given extension, hand the checker `stored` as the formula it
/// parsed out of it, and see whether the two are found to agree.
///
/// `names` is the variable-name table in index order, i.e. what the parser
/// would have interned; that mapping is the *only* thing the cross-check
/// takes from the parser's side of the world, and handing it deliberately
/// wrong names is how the defect-16 case below is expressed.
///
/// Returns the checking error, if any, together with the run's statistics.
fn cross_check(
    text: &str,
    extension: &str,
    names: &[&str],
    stored: Vec<PBConstraintEnum>,
    objective: Option<PBObjective>,
) -> (
    Option<CheckingError>,
    veripb_checker::kernel_bridge::KernelStats,
) {
    let (error, context) = cross_check_context(text, extension, names, stored, objective);
    (error, context.kernel_stats)
}

/// As [`cross_check`], but handing back the whole context rather than only
/// the statistics.
///
/// The cross-check's effect is not confined to a counter: what it underwrites
/// is the shadow database's formula slots, so a stand-down has to be visible
/// in the *composition* verdict too, and only the context carries that.
fn cross_check_context(
    text: &str,
    extension: &str,
    names: &[&str],
    stored: Vec<PBConstraintEnum>,
    objective: Option<PBObjective>,
) -> (Option<CheckingError>, veripb_checker::prelude::Context) {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join(format!("formula.{extension}"));
    std::fs::write(&path, text).expect("write formula");
    let mut var_names = VarNameManager::default();
    for name in names {
        var_names.add_by_name(name);
    }
    let config = veripb_checker::config::CheckerConfig {
        formula_path: path,
        kernel_verify: true,
        ..Default::default()
    };
    let mut context = veripb_checker::prelude::Context::new(config, var_names, None);
    context.objective = objective;
    let database = Database::from_formula(stored);
    let outcome = veripb_checker::kernel_bridge::shadow_init(&mut context, &database)
        .err()
        .map(|(error, _line)| error);
    (outcome, context)
}

/// The honest twin: the stored formula *is* the file, so nothing is reported
/// and every constraint is counted as cross-checked.
#[test]
fn formula_cross_check_accepts_the_formula_the_file_spells() {
    let (error, stats) = cross_check(
        "* #variable= 2 #constraint= 2\n1 x1 1 x2 >= 1 ;\n2 ~x1 >= 1 ;\n",
        "opb",
        &["x1", "x2"],
        vec![
            clause(&[lit(0, true), lit(1, true)]),
            pb(&[(2, lit(0, false))], 1),
        ],
        None,
    );
    assert!(error.is_none(), "{error:?}");
    assert_eq!(stats.formula_constraints_cross_checked, 2);
    assert!(stats.skipped.is_empty(), "{:?}", stats.skipped);
}

/// The comparison is up to the kernel's proved normalization, not byte
/// equality: the checker legitimately merges the two `x1` terms and cancels
/// the `~x1`, and that is not a divergence.
#[test]
fn formula_cross_check_accepts_a_constraint_the_checker_normalized() {
    let (error, stats) = cross_check(
        "1 x1 1 x1 1 ~x1 >= 1 ;\n",
        "opb",
        &["x1"],
        // 1 x1 + 1 x1 + 1 ~x1 >= 1  is  1 x1 >= 0 after merging and cancelling.
        vec![pb(&[(1, lit(0, true))], 0)],
        None,
    );
    assert!(error.is_none(), "{error:?}");
    assert_eq!(stats.formula_constraints_cross_checked, 1);
}

/// A constraint the file spells and the checker did not store. This is the
/// shape of every truncation defect.
#[test]
fn formula_cross_check_rejects_a_dropped_constraint() {
    let (error, _) = cross_check(
        "1 x1 >= 1 ;\n1 x2 >= 1 ;\n",
        "opb",
        &["x1", "x2"],
        vec![clause(&[lit(0, true)])],
        None,
    );
    assert!(
        matches!(error, Some(CheckingError::KernelDivergence(_))),
        "{error:?}"
    );
}

/// Defect 17's shape: a unit clause stored as the *empty* clause, i.e. as a
/// contradiction. This is the case that used to report `nothing outside the
/// proved fragment` and then compose end to end.
#[test]
fn formula_cross_check_rejects_a_unit_clause_stored_as_the_empty_clause() {
    let (error, _) = cross_check(
        "p cnf 2 2\n1 0\n-2 0\n",
        "cnf",
        &["", "x1", "x2"],
        vec![clause(&[lit(1, true)]), clause(&[])],
        None,
    );
    assert!(
        matches!(error, Some(CheckingError::KernelDivergence(_))),
        "{error:?}"
    );
}

/// Defect 16's shape: the two hard clauses `1` and `-01` name one variable,
/// but the parser interned the spellings and stored constraints over two.
#[test]
fn formula_cross_check_rejects_a_variable_split_by_its_spelling() {
    let split = cross_check(
        "h 1 0\nh -01 0\n",
        "wcnf",
        // What the defective parser interned: "x1" from `1` and "x01" from `01`.
        &["x1", "x01"],
        vec![clause(&[lit(0, true)]), clause(&[lit(1, false)])],
        Some(PBObjective::from_terms(vec![], BigInt::from(0), false)),
    );
    assert!(
        matches!(split.0, Some(CheckingError::KernelDivergence(_))),
        "{:?}",
        split.0
    );
    // The honest twin: one variable, as the format says.
    let canonical = cross_check(
        "h 1 0\nh -01 0\n",
        "wcnf",
        &["x1"],
        vec![clause(&[lit(0, true)]), clause(&[lit(0, false)])],
        Some(PBObjective::from_terms(vec![], BigInt::from(0), false)),
    );
    assert!(canonical.0.is_none(), "{:?}", canonical.0);
    assert_eq!(canonical.1.formula_constraints_cross_checked, 2);
    assert_eq!(canonical.1.formula_objectives_cross_checked, 1);
}

/// The WCNF objective is where the whole soft-clause half of the format
/// lands, so it is cross-checked too: a unit soft clause on `1` must pay for
/// `x1`, not for some other variable. (This is the half of defect 16 that the
/// constraint comparison alone cannot see, because the soft clause stores no
/// constraint at all.)
#[test]
fn formula_cross_check_rejects_an_objective_over_the_wrong_variable() {
    let stored_objective = |var: usize| {
        Some(PBObjective::from_terms(
            vec![GeneralPBTerm::new(BigInt::from(1), lit(var, true))],
            BigInt::from(0),
            false,
        ))
    };
    let wrong = cross_check(
        "h 1 0\n1 -01 0\n",
        "wcnf",
        &["x1", "x01"],
        vec![clause(&[lit(0, true)])],
        stored_objective(1),
    );
    assert!(
        matches!(wrong.0, Some(CheckingError::KernelDivergence(_))),
        "{:?}",
        wrong.0
    );
    let right = cross_check(
        "h 1 0\n1 -01 0\n",
        "wcnf",
        &["x1"],
        vec![clause(&[lit(0, true)])],
        stored_objective(0),
    );
    assert!(right.0.is_none(), "{:?}", right.0);
    assert_eq!(right.1.formula_objectives_cross_checked, 1);
}

/// Values outside `i64` are compared at the complete coefficient tier, not
/// stood down at: `1 x1 <= -9223372036854775808` is `-1 x1 >= 2^63`, and the
/// degree is exactly the value defect 6 wrapped.
#[test]
fn formula_cross_check_compares_constraints_outside_i64() {
    use std::str::FromStr;
    let two_to_the_63 = BigInt::from_str("9223372036854775808").unwrap();
    let stored = constraint_from_terms(
        vec![GeneralPBTerm::new(BigInt::from(-1), lit(0, true))],
        two_to_the_63.clone(),
    );
    let (error, stats) = cross_check(
        "1 x1 <= -9223372036854775808 ;\n",
        "opb",
        &["x1"],
        vec![stored],
        None,
    );
    assert!(error.is_none(), "{error:?}");
    assert_eq!(stats.formula_constraints_cross_checked, 1);

    // The wrapped reading defect 6 produced instead.
    let wrapped = constraint_from_terms(
        vec![GeneralPBTerm::new(-1_i64, lit(0, true))],
        -9223372036854775807_i64,
    );
    let (error, _) = cross_check(
        "1 x1 <= -9223372036854775808 ;\n",
        "opb",
        &["x1"],
        vec![wrapped],
        None,
    );
    assert!(
        matches!(error, Some(CheckingError::KernelDivergence(_))),
        "{error:?}"
    );
}

/// The second reader is not the authority on what is a legal formula file, so
/// a file it cannot read stands the cross-check down under a named reason
/// rather than rejecting the proof.
#[test]
fn formula_cross_check_stands_down_on_a_file_it_cannot_read() {
    let (error, stats) = cross_check(
        "1 x1 >= ;\n",
        "opb",
        &["x1"],
        vec![clause(&[lit(0, true)])],
        None,
    );
    assert!(error.is_none(), "{error:?}");
    assert_eq!(stats.formula_constraints_cross_checked, 0);
    assert_eq!(stats.skipped.get("formula-second-reader-refused"), Some(&1));
}

/// A stand-down must not leave the composition claim intact.
///
/// The pair is one `#` apart. Both formulas end in the empty constraint
/// `>= 1`, so both give the shadow a slot that satisfies the
/// `checker_sound` hypotheses at id 2 and both *would* compose. The clean one
/// does. The `#` one — a file the checker's OPB parser reads without
/// complaint, because it stops at the `;`, and the second reader refuses,
/// because it has no token for `#` — must not, because nothing established
/// that the formula the slots were filled from is the formula on disk.
///
/// Before this was fixed the stand-down bumped a skip counter and nothing
/// else, so the run printed `COMPOSED: ... over the stored formula` with a
/// taint census of `none`: the summary was at its most confident exactly
/// where the one premise it could not check had gone unchecked.
#[test]
fn a_cross_check_stand_down_taints_the_composition_claim() {
    let compose = |text: &str| {
        let (error, mut context) = cross_check_context(
            text,
            "opb",
            &["x1"],
            vec![clause(&[lit(0, true)]), clause(&[])],
            None,
        );
        assert!(error.is_none(), "{error:?}");
        // The empty constraint the formula's second line spells, at id 2.
        veripb_checker::kernel_bridge::shadow_record_refutation(&mut context, 2);
        (
            context.kernel_stats.clone(),
            veripb_checker::kernel_bridge::composition_summary(&context).expect("a shadow exists"),
        )
    };

    let (clean_stats, clean) = compose("1 x1 >= 1 ;\n>= 1 ;\n");
    assert!(
        clean.contains("kernel-compose: COMPOSED"),
        "the honest twin must still compose: {clean}"
    );
    assert!(
        clean.contains(
            "0 unjustified slot(s) and 0 subproof premise(s) recorded over the run: none"
        ),
        "the honest twin must carry no taint: {clean}"
    );
    assert_eq!(clean_stats.formula_constraints_cross_checked, 2);

    let (junk_stats, junk) = compose("1 x1 >= 1 ; #\n>= 1 ;\n");
    assert_eq!(
        junk_stats.skipped.get("formula-second-reader-refused"),
        Some(&1),
        "the reader's refusal is still a counted skip: {:?}",
        junk_stats.skipped
    );
    assert!(
        junk.contains("kernel-compose: NOT composed"),
        "a run whose formula was never cross-checked must not claim composition: {junk}"
    );
    assert!(
        junk.contains("formula-second-reader-refused"),
        "the composition line must name why: {junk}"
    );
    assert!(
        junk.contains("2 unjustified slot(s)"),
        "both formula slots are holes, and the census counts them as \
         UNJUSTIFIED -- a refused cross-check is a gap, not a subproof \
         premise: {junk}"
    );
}

/// The same, for a formula with nothing in it to hole.
///
/// Tainting the formula slots is what normally carries a stand-down into the
/// composition verdict, and a formula with no constraints has no such slot.
/// The verdict must still not be `COMPOSED`, because `DbOk.init` over the
/// empty `F` is a claim about the file just as much as over a full one.
#[test]
fn a_cross_check_stand_down_taints_a_formula_with_no_constraints_too() {
    let (error, mut context) = cross_check_context("1 x1 >= ;\n", "opb", &["x1"], vec![], None);
    assert!(error.is_none(), "{error:?}");
    veripb_checker::kernel_bridge::shadow_record_refutation(&mut context, 0);
    let summary =
        veripb_checker::kernel_bridge::composition_summary(&context).expect("a shadow exists");
    assert!(
        summary.contains("kernel-compose: NOT composed")
            && summary.contains("formula-second-reader-refused"),
        "{summary}"
    );
}

#[test]
fn formula_cross_check_stands_down_when_the_file_is_gone() {
    let config = veripb_checker::config::CheckerConfig {
        formula_path: std::path::PathBuf::from("/nonexistent/formula.opb"),
        kernel_verify: true,
        ..Default::default()
    };
    let mut context =
        veripb_checker::prelude::Context::new(config, VarNameManager::default(), None);
    let database = Database::from_formula(vec![clause(&[lit(0, true)])]);
    let outcome = veripb_checker::kernel_bridge::shadow_init(&mut context, &database);
    assert!(outcome.is_ok());
    assert_eq!(
        context.kernel_stats.skipped.get("formula-file-unreadable"),
        Some(&1)
    );
}

/// With `--kernel-verify` off there is no shadow and no cross-check, and a
/// mismatched formula file must not make the run fail.
#[test]
fn formula_cross_check_does_not_run_without_the_flag() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("formula.opb");
    std::fs::write(&path, "1 x1 >= 1 ;\n1 x2 >= 1 ;\n").expect("write");
    let config = veripb_checker::config::CheckerConfig {
        formula_path: path,
        kernel_verify: false,
        ..Default::default()
    };
    let mut context =
        veripb_checker::prelude::Context::new(config, VarNameManager::default(), None);
    let database = Database::from_formula(vec![]);
    assert!(veripb_checker::kernel_bridge::shadow_init(&mut context, &database).is_ok());
    assert!(context.kernel_stats.skipped.is_empty());
}

/// A DIMACS variable index is read by the format's own rule (`x<i>`), not
/// through the checker's name table, which the `p cnf` header sizes. Under
/// `--lenient-header-counts` an under-declared header leaves a legitimate
/// clause naming a variable the table does not reach, and reporting a
/// divergence there would be a complaint about the header rather than about
/// the formula.
#[test]
fn formula_cross_check_reads_dimacs_indices_by_the_format_not_the_name_table() {
    let (error, stats) = cross_check(
        "p cnf 1 2\n1 0\n2 0\n",
        "cnf",
        // What the checker builds from an under-declared `p cnf 1 ...`.
        &["", "x1"],
        vec![clause(&[lit(1, true)]), clause(&[lit(2, true)])],
        None,
    );
    assert!(error.is_none(), "{error:?}");
    assert_eq!(stats.formula_constraints_cross_checked, 2);
}

/// Defect 7's shape, at the formula-storage step rather than in the parser:
/// normalizing `1 x1 1 ~x1 >= i64::MIN` cancels the pair and lowers the
/// degree by one, which used to wrap to `i64::MAX` and store a trivially true
/// input constraint as the empty contradiction. The second reader hands the
/// kernel the constraint as written and lets the proved `normC` do the
/// cancelling, so the wrap has nowhere to hide.
#[test]
fn formula_cross_check_rejects_a_cancellation_that_wrapped() {
    let text = "1 x1 1 ~x1 >= -9223372036854775808 ;\n";
    let wrapped = cross_check(text, "opb", &["x1"], vec![clause(&[])], None);
    assert!(
        matches!(wrapped.0, Some(CheckingError::KernelDivergence(_))),
        "{:?}",
        wrapped.0
    );
    // The honest twin: the exact cancellation, one below `i64::MIN`.
    use std::str::FromStr;
    let exact = constraint_from_terms(
        Vec::<GeneralPBTerm<BigInt>>::new(),
        BigInt::from_str("-9223372036854775809").unwrap(),
    );
    let right = cross_check(text, "opb", &["x1"], vec![exact], None);
    assert!(right.0.is_none(), "{:?}", right.0);
}

// ---------------------------------------------------------------------------
// the formula cross-check on inputs that cannot be read twice
// ---------------------------------------------------------------------------
//
// These two drive the shipped binary rather than `shadow_init`, because what
// they pin is a property of the whole run: `--kernel-verify` must never turn
// an accept into a reject, and must never turn a terminating run into a
// hanging one. The cross-check re-reads the formula *by path*, and a shell
// hands the checker paths that do not survive a second reading; every one of
// them used to look exactly like a truncated file.

/// A `sh -c` command, for the FIFO writer.
#[cfg(unix)]
fn shell(script: String) -> std::process::Child {
    std::process::Command::new("sh")
        .arg("-c")
        .arg(script)
        .spawn()
        .expect("spawn sh")
}

/// Wait for `child`, killing it and failing the test if it outlives the
/// deadline. A regression here **blocks forever** (`read` on a FIFO with no
/// writer), so waiting without a deadline would hang the suite instead of
/// failing it.
#[cfg(unix)]
fn output_before(mut child: std::process::Child, what: &str) -> std::process::Output {
    use std::time::{Duration, Instant};
    let deadline = Instant::now() + Duration::from_secs(60);
    loop {
        match child.try_wait().expect("try_wait") {
            Some(_) => return child.wait_with_output().expect("collect output"),
            None if Instant::now() < deadline => std::thread::sleep(Duration::from_millis(20)),
            None => {
                let _ = child.kill();
                let _ = child.wait();
                panic!(
                    "{what} did not finish within 60s: the run is blocked reading the formula a \
                     second time"
                );
            }
        }
    }
}

/// The formula and proof both reproducers use: a two-line contradiction and
/// the three-step refutation of it.
#[cfg(unix)]
fn unsat_pair(dir: &std::path::Path) -> (std::path::PathBuf, std::path::PathBuf) {
    let formula = dir.join("f.opb");
    let proof = dir.join("p.pbp");
    std::fs::write(
        &formula,
        "* #variable= 1 #constraint= 2\n1 x1 >= 1 ;\n1 ~x1 >= 1 ;\n",
    )
    .expect("write formula");
    std::fs::write(
        &proof,
        "pseudo-Boolean proof version 3.0\nf 2;\nrup >= 1;\noutput NONE;\nconclusion UNSAT;\n\
         end pseudo-Boolean proof;\n",
    )
    .expect("write proof");
    (formula, proof)
}

/// Assert that a run stood the cross-check down instead of rejecting, and
/// that the composition claim was qualified accordingly.
#[cfg(unix)]
fn assert_stood_down_not_rejected(out: &std::process::Output, what: &str) {
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success(),
        "--kernel-verify must not reject a proof it verifies without the flag ({what}):\n{stderr}"
    );
    assert!(
        stdout.contains("s VERIFIED UNSATISFIABLE"),
        "the verdict must be unchanged ({what}):\n{stdout}"
    );
    assert!(
        stdout.contains("formula-file-not-rereadable"),
        "the stand-down must be counted under its own name ({what}):\n{stdout}"
    );
    assert!(
        stdout.contains("kernel-compose: NOT composed"),
        "a run whose formula was never cross-checked must not claim composition ({what}):\n{stdout}"
    );
}

/// A FIFO — which is what `veripb --kernel-verify <(cat f.opb) proof.pbp`
/// hands the checker on every platform.
///
/// The parser consumes the bytes; a second `read` of the same path returns
/// nothing at best and **blocks forever** at worst, waiting for a writer that
/// has already exited. The run used to exit 1 with `Kernel verification
/// divergence: the file has 0 constraint(s), the checker stored 2 ... Report
/// this.` on a proof the same binary verified at exit 0 without the flag.
#[cfg(unix)]
#[test]
fn kernel_verify_stands_down_on_a_fifo_rather_than_rejecting_or_hanging() {
    let dir = tempfile::tempdir().expect("tempdir");
    let (formula, proof) = unsat_pair(dir.path());
    let fifo = dir.path().join("formula_fifo");
    assert!(
        std::process::Command::new("mkfifo")
            .arg(&fifo)
            .status()
            .expect("run mkfifo")
            .success(),
        "mkfifo {} failed",
        fifo.display()
    );

    // The writer blocks until the checker opens the FIFO, and exits once the
    // checker has read it — which is exactly why a second read finds nobody.
    let mut writer = shell(format!("cat {} > {}", formula.display(), fifo.display()));
    let child = std::process::Command::new(env!("CARGO_BIN_EXE_veripb"))
        .arg("--kernel-verify")
        .arg(&fifo)
        .arg(&proof)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("spawn veripb");
    let out = output_before(child, "the FIFO run");
    let _ = writer.wait();
    assert_stood_down_not_rejected(&out, "a FIFO formula");
}

/// `/dev/stdin` on macOS, where `open` **dups** the descriptor the parser
/// already read to the end instead of reopening the object it names.
///
/// `stat` sees the regular file behind it and reports a regular file, so the
/// file-type check cannot catch this one; what catches it is that the fresh
/// `File::open` came back positioned at end-of-file, which a real `open` of a
/// regular file never does. Linux reopens through `/proc/self/fd`, so there
/// the second reading succeeds and the cross-check runs normally — the
/// behaviour is genuinely per-platform, and so is this test.
#[cfg(target_os = "macos")]
#[test]
fn kernel_verify_stands_down_on_a_dup_of_an_already_read_descriptor() {
    let dir = tempfile::tempdir().expect("tempdir");
    let (formula, proof) = unsat_pair(dir.path());
    let child = std::process::Command::new(env!("CARGO_BIN_EXE_veripb"))
        .arg("--kernel-verify")
        .arg("/dev/stdin")
        .arg(&proof)
        .stdin(std::fs::File::open(&formula).expect("open formula"))
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("spawn veripb");
    let out = output_before(child, "the /dev/stdin run");
    assert_stood_down_not_rejected(&out, "/dev/stdin");
}
