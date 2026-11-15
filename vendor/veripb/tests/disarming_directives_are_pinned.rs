//! Every instance-level directive that WEAKENS a check is pinned here.
//!
//! `tests/integration.rs` reads the second line of each `.pbp` and honours
//! three directives that make a lane check less than it otherwise would:
//!
//!   * `INTEGRATION-TEST: ignore(check|elaborate|both)` — the named lane is not
//!     run at all, via `with_ignored_flag`;
//!   * `INTEGRATION-TEST: allow-unchecked-deletion` — drops `force_checked_deletion`;
//!   * `INTEGRATION-TEST: lenient-header-counts` — downgrades the DIMACS header
//!     check to warn-only.
//!
//! Each is legitimate, and each is also a way to make a failing instance stop
//! failing. Nothing pinned *which* instances used them, so adding a directive
//! to a red instance turned it green with no reviewable artifact: an ignored
//! trial is reported as `ignored`, not as a gap in coverage, and a suite whose
//! ignore-count silently grows still prints `ok`.
//!
//! The table below is that artifact. Adding, removing or retargeting a
//! directive now requires editing this file, so it appears in the diff next to
//! the instance it disarms.
//!
//! `no_incorrect_instance_is_silenced_in_the_check_lane` is a stronger rule and
//! not merely a pin: for an instance under `tests/instances/incorrect/`, the
//! `check` lane is the assertion that the checker REFUSES the proof. Silencing
//! that lane would let a genuinely-accepted bad proof sit in the tree reported
//! as `ignored`. `ignore(elaborate)` on such an instance is fine — refusal is
//! still asserted — and one instance relies on exactly that today.

/// `(correct|incorrect, version, instance stem, directive)`, sorted.
const PINNED_DIRECTIVES: &[(&str, &str, &str, &str)] = &[
    (
        "correct",
        "version2",
        "assumption_rule",
        "ignore(elaborate)",
    ),
    (
        "correct",
        "version2",
        "conclusion_BOUNDS_optimal",
        "ignore(elaborate)",
    ),
    (
        "correct",
        "version2",
        "pre_order_aux_var_already_used",
        "ignore(elaborate)",
    ),
    (
        "correct",
        "version3",
        "annotated_assertion_blank",
        "ignore(elaborate)",
    ),
    (
        "correct",
        "version3",
        "annotated_assertion_comment",
        "ignore(elaborate)",
    ),
    (
        "correct",
        "version3",
        "annotated_assertion_hints",
        "ignore(elaborate)",
    ),
    (
        "correct",
        "version3",
        "annotated_assertion_ids",
        "ignore(elaborate)",
    ),
    (
        "correct",
        "version3",
        "annotated_assertion_named",
        "ignore(elaborate)",
    ),
    ("correct", "version3", "assertion_rule", "ignore(elaborate)"),
    (
        "correct",
        "version3",
        "cnf_under_declared_counts_lenient",
        "lenient-header-counts",
    ),
    (
        "correct",
        "version3",
        "conclusion_BOUNDS_optimal",
        "ignore(elaborate)",
    ),
    (
        "correct",
        "version3",
        "dominance_proofgoal_outside_scope",
        "ignore(elaborate)",
    ),
    (
        "correct",
        "version3",
        "implication_return_hint",
        "ignore(elaborate)",
    ),
    (
        "correct",
        "version3",
        "solution_checking_solx",
        "ignore(elaborate)",
    ),
    (
        "correct",
        "version3",
        "solution_logging_max_objective",
        "ignore(elaborate)",
    ),
    (
        "correct",
        "version3",
        "strengthening_to_core-deletion_subproof",
        "allow-unchecked-deletion",
    ),
    (
        "incorrect",
        "version3",
        "cnf_under_declared_variable_index",
        "lenient-header-counts",
    ),
    (
        "incorrect",
        "version3",
        "conclusion_sat_after_unchecked_deletion",
        "allow-unchecked-deletion",
    ),
    (
        "incorrect",
        "version3",
        "enumeration_incorrect_number",
        "ignore(elaborate)",
    ),
];

fn observed() -> Vec<(String, String, String, String)> {
    let mut rows = Vec::new();
    for correct in ["correct", "incorrect"] {
        for version in ["version2", "version3"] {
            let pattern = format!("./tests/instances/{correct}/{version}/*.pbp");
            let mut paths: Vec<_> = glob::glob(&pattern).expect("bad glob").flatten().collect();
            paths.sort();
            for path in paths {
                let text = std::fs::read_to_string(&path).unwrap_or_default();
                let Some(second) = text.lines().nth(1) else {
                    continue;
                };
                let Some((_, directive)) = second.trim().split_once("INTEGRATION-TEST:") else {
                    continue;
                };
                rows.push((
                    correct.to_string(),
                    version.to_string(),
                    path.file_stem().unwrap().to_str().unwrap().to_string(),
                    directive.trim().to_string(),
                ));
            }
        }
    }
    rows
}

#[test]
fn every_disarming_directive_is_pinned() {
    let got = observed();
    assert!(
        !got.is_empty(),
        "found no INTEGRATION-TEST directives at all -- this test would be \
         vacuous, and the instance tree has presumably moved"
    );
    let want: Vec<_> = PINNED_DIRECTIVES
        .iter()
        .map(|(a, b, c, d)| (a.to_string(), b.to_string(), c.to_string(), d.to_string()))
        .collect();

    let added: Vec<_> = got.iter().filter(|r| !want.contains(r)).collect();
    let removed: Vec<_> = want.iter().filter(|r| !got.contains(r)).collect();
    assert!(
        added.is_empty() && removed.is_empty(),
        "the set of check-weakening directives has changed.\n\
         newly disarmed (not in the pin): {added:#?}\n\
         pinned but no longer present:    {removed:#?}\n\
         If this is intended, update PINNED_DIRECTIVES in this file -- that \
         edit is the point, because it puts the weakening in the diff."
    );
}

#[test]
fn no_incorrect_instance_is_silenced_in_the_check_lane() {
    let silenced: Vec<_> = observed()
        .into_iter()
        .filter(|(correct, _, _, directive)| {
            correct == "incorrect" && (directive == "ignore(both)" || directive == "ignore(check)")
        })
        .collect();
    assert!(
        silenced.is_empty(),
        "these instances live under tests/instances/incorrect/, so the `check` \
         lane is what asserts the checker REFUSES them -- and that lane has \
         been switched off: {silenced:#?}\n\
         A proof the checker wrongly ACCEPTS would then be reported as \
         `ignored` rather than as a failure. Use ignore(elaborate) if only \
         elaboration is broken."
    );
}
