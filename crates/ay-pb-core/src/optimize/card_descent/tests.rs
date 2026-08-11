//! Unit tests for `super` (card_descent.rs).
//! Extracted to keep the production module readable.

use super::cover::CoverView;
use super::*;
use crate::parse_opb;

fn parse(input: &str) -> PbInstance {
    parse_opb(input).expect("test OPB should parse")
}

/// A 5-cycle dominating-set instance: every vertex must be dominated by itself
/// or a neighbour. The optimum is 2 (e.g. {x1, x3}).
const CYCLE5: &str = "* #variable= 5 #constraint= 5\n\
min: +1 x1 +1 x2 +1 x3 +1 x4 +1 x5 ;\n\
+1 x1 +1 x2 +1 x5 >= 1 ;\n\
+1 x2 +1 x1 +1 x3 >= 1 ;\n\
+1 x3 +1 x2 +1 x4 >= 1 ;\n\
+1 x4 +1 x3 +1 x5 >= 1 ;\n\
+1 x5 +1 x4 +1 x1 >= 1 ;\n";

/// A weighted covering instance with coefficients > 1 and rhs > 1, the shape of
/// the PB06 `domset_v500_e2000_w30` family.
const WEIGHTED_COVER: &str = "* #variable= 6 #constraint= 4\n\
min: +1 x1 +1 x2 +1 x3 +1 x4 +1 x5 +1 x6 ;\n\
+5 x1 +3 x2 +2 x3 >= 5 ;\n\
+4 x2 +4 x4 +1 x5 >= 4 ;\n\
+2 x3 +6 x5 +3 x6 >= 6 ;\n\
+7 x1 +2 x4 +2 x6 >= 4 ;\n";

fn view_of(instance: &PbInstance) -> Option<CoverView> {
    let objective = instance.objective.as_ref().expect("objective required");
    build_cover_view(instance, objective)
}

/// Swap budget for the tests: no wall-clock deadline anywhere in this file, so
/// every run terminates purely on this deterministic cap.
const TEST_SWAPS: u64 = 200_000;

/// The best feasible point of a bounded run: its exact objective plus the
/// assignment last streamed through `on_improve` (the search reports the
/// assignment on the stream, not in its return value).
struct Best {
    objective: i128,
    assignment: Vec<bool>,
}

fn run(instance: &PbInstance) -> Option<Best> {
    let objective = instance.objective.as_ref().expect("objective required");
    let mut last: Option<Vec<bool>> = None;
    let value = search_with_budget(
        instance,
        objective,
        None,
        &|| false,
        &mut |_, model| last = Some(model.to_vec()),
        TEST_SWAPS,
    )?;
    Some(Best {
        objective: value,
        assignment: last.expect("a returned objective implies a streamed model"),
    })
}

// ---------------------------------------------------------------------------
// Applicability gate
// ---------------------------------------------------------------------------

#[test]
fn accepts_unicost_covering_instances() {
    let instance = parse(CYCLE5);
    let view = view_of(&instance).expect("5-cycle domset is unicost covering");
    assert_eq!(view.num_rows(), 5);
    assert_eq!(view.ground.len(), 5);
}

#[test]
fn declines_weighted_objective() {
    let instance = parse("* #variable= 2 #constraint= 1\nmin: +1 x1 +3 x2 ;\n+1 x1 +1 x2 >= 1 ;\n");
    assert!(
        view_of(&instance).is_none(),
        "mixed objective weights must decline"
    );
}

#[test]
fn declines_equality_row() {
    let instance = parse("* #variable= 2 #constraint= 1\nmin: +1 x1 +1 x2 ;\n+1 x1 +1 x2 = 1 ;\n");
    assert!(view_of(&instance).is_none(), "an `=` row must decline");
}

#[test]
fn declines_non_monotone_row() {
    // `+2 x1 -1 x2 >= 1` is decreasing in x2, so fixing |S| is not lossless.
    let instance = parse("* #variable= 2 #constraint= 1\nmin: +1 x1 +1 x2 ;\n+2 x1 -1 x2 >= 1 ;\n");
    assert!(
        view_of(&instance).is_none(),
        "a negative coefficient must decline"
    );
}

#[test]
fn declines_constrained_but_unpriced_variable() {
    let instance = parse("* #variable= 2 #constraint= 1\nmin: +1 x1 ;\n+1 x1 +1 x2 >= 1 ;\n");
    assert!(
        view_of(&instance).is_none(),
        "x2 is constrained but not priced, so |S| is not the objective"
    );
}

#[test]
fn normalizes_negated_literals_into_the_covering_form() {
    // `-3 ~x1 >= -2` is `3 x1 >= 1` after expanding `~x1 = 1 - x1`: monotone.
    let instance = parse(
        "* #variable= 2 #constraint= 2\nmin: +1 x1 +1 x2 ;\n\
-3 ~x1 >= -2 ;\n+1 x2 >= 1 ;\n",
    );
    let view = view_of(&instance).expect("negated-literal row normalizes to covering form");
    assert_eq!(view.num_rows(), 2);
    let row: Vec<(u32, i64)> = view.row_entries(0).collect();
    assert_eq!(row, vec![(0, 3)]);
    assert_eq!(view.rhs[0], 1);
}

#[test]
fn drops_trivially_true_rows() {
    let instance = parse(
        "* #variable= 2 #constraint= 2\nmin: +1 x1 +1 x2 ;\n\
+1 x1 +1 x2 >= 0 ;\n+1 x1 >= 1 ;\n",
    );
    let view = view_of(&instance).expect("covering instance");
    assert_eq!(
        view.num_rows(),
        1,
        "the `>= 0` row is satisfied by everything"
    );
    assert_eq!(view.ground, vec![0], "x2 only occurs in the dropped row");
}

#[test]
fn declines_unsatisfiable_row() {
    let instance = parse("* #variable= 2 #constraint= 1\nmin: +1 x1 +1 x2 ;\n+1 x1 +1 x2 >= 3 ;\n");
    assert!(
        view_of(&instance).is_none(),
        "a row that cannot reach its rhs must decline"
    );
}

// ---------------------------------------------------------------------------
// The fixed-cardinality invariant
// ---------------------------------------------------------------------------

/// DETERMINISTIC: every `swap_step` preserves `|S|` exactly, from a whole
/// sweep of seeds and every reachable cardinality on both test instances.
#[test]
fn swap_step_preserves_cardinality() {
    for source in [CYCLE5, WEIGHTED_COVER] {
        let instance = parse(source);
        let view = view_of(&instance).expect("covering instance");
        for seed in 0..16u64 {
            for size in 1..=view.ground.len() {
                let mut descent = Descent::new(&view, seed);
                let selection: Vec<u32> = view.ground.iter().copied().take(size).collect();
                descent.set_selection(&selection);
                assert_eq!(descent.selection().len(), size);
                for step in 0..200 {
                    descent.swap_step();
                    assert_eq!(
                        descent.selection().len(),
                        size,
                        "seed {seed} size {size} step {step}: swap must preserve |S|"
                    );
                    let distinct: std::collections::BTreeSet<u32> =
                        descent.selection().iter().copied().collect();
                    assert_eq!(distinct.len(), size, "selection must stay a SET");
                }
            }
        }
    }
}

/// `set_selection` must re-derive the whole violation structure, not patch it:
/// the state after a shrink must be bit-identical to a state built from
/// scratch with the same members.
#[test]
fn set_selection_rederives_state_from_scratch() {
    let instance = parse(WEIGHTED_COVER);
    let view = view_of(&instance).expect("covering instance");
    let mut walked = Descent::new(&view, 7);
    walked.set_selection(&[0, 1, 2, 3]);
    for _ in 0..50 {
        walked.swap_step();
    }
    let target = vec![1u32, 4, 5];
    walked.set_selection(&target);

    let mut fresh = Descent::new(&view, 7);
    fresh.set_selection(&target);
    assert_eq!(walked.lhs, fresh.lhs, "row LHS must be re-derived");
    assert_eq!(
        walked.total_shortfall, fresh.total_shortfall,
        "shortfall total must be re-derived"
    );
    let walked_viol: std::collections::BTreeSet<u32> = walked.violated.iter().copied().collect();
    let fresh_viol: std::collections::BTreeSet<u32> = fresh.violated.iter().copied().collect();
    assert_eq!(walked_viol, fresh_viol, "violated set must be re-derived");
    assert_eq!(walked.is_feasible(), fresh.is_feasible());
}

/// The incremental `lhs` / `violated` / `total_shortfall` bookkeeping must
/// agree with a from-scratch recomputation after an arbitrary swap walk.
#[test]
fn incremental_state_matches_recomputation() {
    let instance = parse(WEIGHTED_COVER);
    let view = view_of(&instance).expect("covering instance");
    let mut descent = Descent::new(&view, 11);
    descent.set_selection(&[0, 2, 4]);
    for _ in 0..500 {
        descent.swap_step();
        let members = descent.selection().to_vec();
        let mut fresh = Descent::new(&view, 11);
        fresh.set_selection(&members);
        assert_eq!(descent.lhs, fresh.lhs);
        assert_eq!(descent.total_shortfall, fresh.total_shortfall);
        assert_eq!(descent.is_feasible(), fresh.is_feasible());
    }
}

// ---------------------------------------------------------------------------
// Feasibility of what the search reports
// ---------------------------------------------------------------------------

#[test]
fn reported_solution_is_feasible_and_matches_its_objective() {
    for source in [CYCLE5, WEIGHTED_COVER] {
        let instance = parse(source);
        let objective = instance.objective.as_ref().expect("objective required");
        let result = run(&instance).expect("descent finds a feasible point");
        assert!(
            verify_all_constraints(&instance.constraints, &result.assignment),
            "reported assignment must satisfy every original constraint"
        );
        assert_eq!(
            result.objective,
            eval_objective(objective, &result.assignment),
            "reported objective must be the exact evaluation"
        );
    }
}

/// NEGATIVE CONTROL for `reported_solution_is_feasible_and_matches_its_objective`:
/// the same assertions applied to a DELIBERATELY BROKEN assignment must FAIL.
/// Without this, a checker that always passed would look identical.
#[test]
fn feasibility_check_rejects_a_broken_assignment() {
    let instance = parse(CYCLE5);
    let objective = instance.objective.as_ref().expect("objective required");
    let result = run(&instance).expect("descent finds a feasible point");

    // Control 1: dropping a chosen vertex must break some row.
    let mut broken = result.assignment.clone();
    let chosen = broken
        .iter()
        .position(|value| *value)
        .expect("a non-empty dominating set");
    broken[chosen] = false;
    assert!(
        !verify_all_constraints(&instance.constraints, &broken),
        "NEGATIVE CONTROL: the feasibility checker must reject a stripped assignment"
    );

    // Control 2: the objective check must reject a mis-stated value.
    assert_ne!(
        result.objective + 1,
        eval_objective(objective, &result.assignment),
        "NEGATIVE CONTROL: the objective check must reject an off-by-one value"
    );

    // Control 3: the all-false assignment is infeasible for a covering instance.
    let empty = vec![false; result.assignment.len()];
    assert!(
        !verify_all_constraints(&instance.constraints, &empty),
        "NEGATIVE CONTROL: the empty selection covers nothing"
    );
}

#[test]
fn reaches_the_optimum_on_the_five_cycle() {
    let instance = parse(CYCLE5);
    let result = run(&instance).expect("descent finds a feasible point");
    assert_eq!(result.objective, 2, "the 5-cycle dominating number is 2");
}

#[test]
fn streams_monotonically_improving_incumbents() {
    let instance = parse(WEIGHTED_COVER);
    let objective = instance.objective.as_ref().expect("objective required");
    let mut seen: Vec<i128> = Vec::new();
    let result = search_with_budget(
        &instance,
        objective,
        None,
        &|| false,
        &mut |value, model| {
            assert!(
                verify_all_constraints(&instance.constraints, model),
                "every streamed incumbent must be feasible"
            );
            seen.push(value);
        },
        TEST_SWAPS,
    )
    .expect("descent finds a feasible point");
    assert!(!seen.is_empty(), "at least one incumbent must be streamed");
    assert!(
        seen.windows(2).all(|pair| pair[0] > pair[1]),
        "streamed objectives must strictly improve: {seen:?}"
    );
    assert_eq!(*seen.last().expect("non-empty"), result);
}

#[test]
fn honours_an_immediate_stop() {
    let instance = parse(CYCLE5);
    let objective = instance.objective.as_ref().expect("objective required");
    assert!(
        search(&instance, objective, None, &|| true, &mut |_, _| {}).is_none(),
        "a pre-tripped stop signal must produce no work and no incumbent"
    );
}
