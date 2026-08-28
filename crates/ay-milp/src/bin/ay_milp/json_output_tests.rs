// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Tests for the `--format json` output contract.

use super::*;
use ay_milp::{Model, UnknownReason};

/// The `--format json` line for an outcome, built exactly as `cmd_solve`
/// builds it: `verdict_line` then `solve_json_line`. Only the numbers are
/// stand-ins.
fn emit(o: &Outcome) -> String {
    let mut m = Model::new();
    m.add_col(0.0, 1.0);
    let scale = BigRational::one();
    let (status, value, detail) = verdict_line(o, &m, &scale, 1.5, 7);
    // `7` total nodes, of which `5` are proof tree and `2` heuristic sub-MIP —
    // distinct stand-ins so a swapped pair of arguments shows up as a wrong value
    // rather than as three equal sevens.
    solve_json_line(
        &status,
        value.as_deref(),
        None,
        detail.as_deref(),
        1.5,
        7,
        5,
        2,
        0,
    )
}

fn parse(line: &str) -> serde_json::Value {
    serde_json::from_str(line)
        .unwrap_or_else(|e| panic!("`--format json` emitted invalid JSON: {e}\n  {line}"))
}

fn point() -> Vec<BigRational> {
    vec![BigRational::zero()]
}

/// EVERY `UnknownReason` in `outcome.rs`, in declaration order. `Outcome`
/// and `UnknownReason` are `#[non_exhaustive]`, so this crate cannot get a
/// compile-time exhaustiveness check on them — `outcome.rs`'s
/// `cli_json_coverage` test carries that check (it lives in the defining
/// crate, where the match IS exhaustive) and names this list.
fn every_unknown_reason() -> Vec<UnknownReason> {
    vec![
        UnknownReason::Timeout,
        UnknownReason::Interrupted,
        UnknownReason::IterationLimit,
        UnknownReason::MemoryLimit,
        UnknownReason::CertificateUnavailable,
        UnknownReason::SolverIncomplete {
            detail: "branch-and-bound could not settle every node".to_owned(),
        },
        UnknownReason::WitnessRejected {
            detail: "the verdict's point is infeasible".to_owned(),
        },
    ]
}

/// EVERY `Outcome` in `outcome.rs`, in declaration order, paired with the
/// status token the CLI must print for it.
fn every_outcome() -> Vec<(&'static str, Outcome)> {
    let mut v = vec![
        (
            "OPTIMAL",
            Outcome::Optimal {
                value: BigRational::zero(),
                model_values: point(),
                cert: None,
            },
        ),
        (
            "FEASIBLE",
            Outcome::Feasible {
                model_values: point(),
                incumbent_only: true,
                dual_bound: None,
            },
        ),
        (
            "INFEASIBLE",
            Outcome::Infeasible {
                cert: None,
                tree_cert: None,
            },
        ),
        ("UNBOUNDED", Outcome::Unbounded),
        (
            "BOUND",
            Outcome::Bound {
                dual_bound: BigRational::zero(),
                rigorous: true,
            },
        ),
    ];
    v.extend(
        every_unknown_reason()
            .into_iter()
            .map(|reason| ("UNKNOWN", Outcome::Unknown { reason })),
    );
    v
}

/// THE REGRESSION. Before the fix, `verdict_line` returned
/// `UNKNOWN SolverIncomplete { detail: "branch-and-bound could not settle
/// every node" }` as the whole status and it was interpolated raw into the
/// `"status"` literal, so the inner quotes terminated the string and a real
/// parser stopped at the `S` of `SolverIncomplete`.
#[test]
fn a_debug_payload_status_is_still_json() {
    let line = emit(&Outcome::Unknown {
        reason: UnknownReason::SolverIncomplete {
            detail: "branch-and-bound could not settle every node".to_owned(),
        },
    });
    let v = parse(&line);
    assert_eq!(v["status"], "UNKNOWN");
    assert_eq!(
        v["detail"],
        "SolverIncomplete { detail: \"branch-and-bound could not settle every node\" }",
        "the payload must survive the round trip, not just parse"
    );
}

/// Not just the observed one: every status the CLI can print. (`OTHER` is
/// covered separately — a future `#[non_exhaustive]` variant cannot be
/// constructed here to reach the arm that produces it.)
#[test]
fn every_status_emits_valid_json() {
    for (want, o) in every_outcome() {
        let line = emit(&o);
        let v = parse(&line);
        assert_eq!(v["status"], want, "wrong status token for {o:?}\n  {line}");
        // The status is the discriminator, so it must stay a bare token —
        // a `Debug` blob smuggled back in would parse but be unmatchable.
        assert!(
            v["status"]
                .as_str()
                .is_some_and(|s| s.chars().all(|c| c.is_ascii_uppercase() || c == '-')),
            "status must be an enumerable token, got {:?}",
            v["status"]
        );
        assert!(v["time"].is_number() && v["nodes"].is_number());
        // THE COMPARABILITY SPLIT IS PART OF THE CONTRACT, and it is ADDITIVE:
        // `nodes` keeps its historical meaning (every node the process explored,
        // heuristic sub-MIP trees included) and the two new keys decompose it.
        // `root_nodes` is the field that compares to Gurobi's `Model.NodeCount`,
        // which excludes the sub-MIPs its heuristics run. A consumer that reads
        // `nodes` alone is comparing two different quantities.
        assert!(
            v["root_nodes"].is_number() && v["submip_nodes"].is_number(),
            "the json line must carry the root/sub-MIP split\n  {line}"
        );
        assert_eq!(
            v["nodes"].as_u64(),
            Some(
                v["root_nodes"].as_u64().unwrap_or_default()
                    + v["submip_nodes"].as_u64().unwrap_or_default()
            ),
            "nodes must remain the SUM of the split, not be redefined as its root part\n  {line}"
        );
    }
}

/// The `OTHER` arm carries a whole `Outcome`'s `Debug`, not a reason's, and
/// `#[non_exhaustive]` means no variant reaching it can be constructed from
/// this crate. Drive the emission path with exactly the string that arm
/// builds so the catch-all is not the one shape nobody ever parsed.
#[test]
fn the_non_exhaustive_catch_all_emits_valid_json() {
    let blob = format!(
        "{:?}",
        Outcome::Unknown {
            reason: UnknownReason::SolverIncomplete {
                detail: "a \"quoted\" payload".to_owned(),
            },
        }
    );
    let line = solve_json_line("OTHER", None, None, Some(&blob), 1.5, 7, 5, 2, 0);
    let v = parse(&line);
    assert_eq!(v["status"], "OTHER");
    assert_eq!(v["detail"], blob);
}

/// ⚠ A partial escape is the same bug with a smaller trigger. The quote is
/// what broke today; a backslash, a newline, a tab or a bare control
/// character each break a quote-only escaper. `Debug` renders some of these
/// itself, so drive the escaper directly as well as through an outcome.
#[test]
fn escaping_covers_more_than_the_double_quote() {
    let nasty = "quote \" backslash \\ newline \n cr \r tab \t bs \u{8} ff \u{c} nul \u{0} \
                 unit-sep \u{1f} unicode ü▲";
    let line = emit(&Outcome::Unknown {
        reason: UnknownReason::WitnessRejected {
            detail: nasty.to_owned(),
        },
    });
    let v = parse(&line);
    assert_eq!(v["status"], "UNKNOWN");
    assert_eq!(
        v["detail"],
        format!(
            "{:?}",
            UnknownReason::WitnessRejected {
                detail: nasty.to_owned()
            }
        ),
        "the escaped detail must decode back to the exact Debug string"
    );

    // And the escaper on its own, against a real parser's idea of a string.
    let escaped = json_escape(nasty);
    let round: serde_json::Value = serde_json::from_str(&format!("\"{escaped}\""))
        .unwrap_or_else(|e| panic!("json_escape produced an unparseable literal: {e}"));
    assert_eq!(round, nasty);
    assert!(
        !escaped.contains('\n') && !escaped.contains('\t'),
        "raw control characters are not legal inside a JSON string: {escaped:?}"
    );
}

/// The line (non-JSON) shape is frozen — the journal's measurement scripts
/// read it — so splitting status/detail must re-join byte for byte.
#[test]
fn the_line_format_is_unchanged_by_the_split() {
    let mut m = Model::new();
    m.add_col(0.0, 1.0);
    let scale = BigRational::one();
    let o = Outcome::Unknown {
        reason: UnknownReason::SolverIncomplete {
            detail: "branch-and-bound could not settle every node".to_owned(),
        },
    };
    let (status, value, detail) = verdict_line(&o, &m, &scale, 1.5, 7);
    let rejoined = format!(
        "{status}{} {}",
        detail.map_or(String::new(), |d| format!(" {d}")),
        value.as_deref().unwrap_or("-")
    );
    assert_eq!(
        rejoined,
        "UNKNOWN SolverIncomplete { detail: \"branch-and-bound could not settle every node\" } -"
    );
}
