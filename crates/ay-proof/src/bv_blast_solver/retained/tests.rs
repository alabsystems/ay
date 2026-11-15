// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

mod arithmetic;
mod resources;

fn limits() -> BvExprProofLimits {
    BvExprProofLimits::conservative_external(Instant::now() + Duration::from_secs(60), 100)
}

fn gate_limits(limits: &BvExprProofLimits) -> BvBlastValidateLimits {
    BvBlastValidateLimits {
        deadline: limits.resolution.deadline,
        max_vars: 4096,
        max_bit_lemmas: 4096,
        max_clauses: 16000,
        max_clause_literals: 64,
        max_original_literals: 64000,
        max_resolution_steps: 100,
        max_derived_literals: 10000,
        max_work: 1_000_000,
    }
}

fn expression() -> BvExpr {
    BvExpr::leaf("a", 1)
}

// Frozen canonical CNF for a == a: [e,a], [e,!a], [!e].
// First prove [e] under !e, then resolve it against original 3.
fn payload() -> RetainedBvRefutation {
    RetainedBvRefutation {
        version: VERSION,
        rows: vec![
            RetainedRupRow {
                id: 4,
                literals: vec![2],
                hints: vec![1, 2],
            },
            RetainedRupRow {
                id: 5,
                literals: vec![],
                hints: vec![3, 4],
            },
        ],
        empty_clause_id: 5,
    }
}

fn read(
    payload: &RetainedBvRefutation,
    limits: &BvExprProofLimits,
) -> Result<(), BvExprExportError> {
    let a = expression();
    replay_bv_expr_refutation(
        &a,
        &a,
        Some(payload),
        limits,
        &gate_limits(limits),
        &mut || true,
    )
}

#[test]
fn retained_capture_replays_offline_after_all_producer_owners_drop() {
    let serialized = {
        let a = expression();
        let limits = limits();
        let produced =
            capture_bv_expr_refutation(&a, &a, &limits, &gate_limits(&limits), &mut || true)
                .unwrap();
        serde_json::to_vec(&produced).unwrap()
    };
    // This test's JSON allocation is outside the bounded in-memory API.
    let independent: RetainedBvRefutation = serde_json::from_slice(&serialized).unwrap();
    let mut limits = limits();
    limits.resolution.max_conflicts = Some(0);
    limits.resolution.max_decisions = Some(0);
    limits.resolution.max_backward_reconstruction_bytes = 0;
    limits.resolution.max_pending_deletions = 0;
    read(&independent, &limits).unwrap();
    read(&payload(), &limits).unwrap();
    // The transport owns no originals, variable namespace or checked flag.
    let object: serde_json::Value = serde_json::from_slice(&serialized).unwrap();
    assert_eq!(object.as_object().unwrap().len(), 3);
}

#[test]
fn retained_sat_neighbors_and_changed_source_never_fall_back_to_search() {
    let a = expression();
    let limits = limits();
    let mut transferred = payload();
    transferred.rows[0].id = 100;
    transferred.rows[1].id = 101;
    transferred.rows[1].hints[1] = 100;
    transferred.empty_clause_id = 101;
    read(&transferred, &limits).unwrap();
    for rhs in [
        BvExpr::leaf("b", 1),
        BvExpr::not(a.clone()),
        BvExpr::const_val(0, 1),
    ] {
        // Keep IDs beyond the neighbor's originals so rejection is by fresh
        // source-CNF RUP replay, not merely an original/derived ID collision.
        let neighbor = cnf::build_bv_expr_cnf(&a, &rhs, &limits, &mut || true).unwrap();
        assert!(neighbor.clauses.len() < 100);
        let rejected = replay_bv_expr_refutation(
            &a,
            &rhs,
            Some(&transferred),
            &limits,
            &gate_limits(&limits),
            &mut || true,
        );
        assert!(
            matches!(rejected, Err(BvExprExportError::RefutationNotSurfaceable(message))
            if message.starts_with("bounded resolution proof failed:"))
        );
        assert!(matches!(
            capture_bv_expr_refutation(&a, &rhs, &limits, &gate_limits(&limits), &mut || true),
            Err(BvExprExportError::NoRefutation)
        ));
    }
    assert!(replay_bv_expr_refutation(
        &a,
        &BvExpr::leaf("a", 2),
        Some(&payload()),
        &limits,
        &gate_limits(&limits),
        &mut || true
    )
    .is_err());
    assert!(
        replay_bv_expr_refutation(&a, &a, None, &limits, &gate_limits(&limits), &mut || true)
            .is_err()
    );
}

#[test]
fn retained_rows_hints_literals_version_and_terminal_are_untrusted() {
    read(&payload(), &limits()).unwrap();
    for mutation in 0..12 {
        let mut changed = payload();
        match mutation {
            0 => changed.version += 1,
            1 => changed.rows.clear(),
            2 => changed.empty_clause_id = 4,
            3 => changed.rows[1].literals.push(0),
            4 => changed.rows[0].id = 3,
            5 => changed.rows[1].id = 4,
            6 => changed.rows.swap(0, 1),
            7 => changed.rows[0].literals[0] ^= 1,
            8 => changed.rows[0].literals[0] = u32::MAX,
            9 => changed.rows[1].hints = vec![0],
            10 => changed.rows[1].hints = vec![5],
            11 => changed.rows[1].hints = vec![3],
            _ => unreachable!(),
        }
        assert!(read(&changed, &limits()).is_err(), "mutation {mutation}");
    }
    // A monotone ID gap does not authorize a hint to a missing prior clause.
    let mut missing = payload();
    missing.rows[1].id = 7;
    missing.empty_clause_id = 7;
    missing.rows[1].hints = vec![6];
    assert!(read(&missing, &limits()).is_err());
}

#[test]
fn retained_schema_refuses_unknown_duplicate_and_missing_fields() {
    let bytes = serde_json::to_string(&payload()).unwrap();
    for changed in [
        bytes.replacen("{", "{\"checked\":true,", 1),
        bytes.replacen("{", "{\"version\":1,", 1),
        bytes.replace("\"empty_clause_id\":5", "\"unrecognized\":5"),
        bytes.replacen("\"id\":4", "\"id\":4,\"num_vars\":2", 1),
    ] {
        assert!(serde_json::from_str::<RetainedBvRefutation>(&changed).is_err());
    }
}

#[test]
fn retained_canonical_reconstruction_still_checks_gate_and_original_binding() {
    let a = expression();
    let limits = limits();
    let graph = cnf::build_bv_expr_cnf(&a, &a, &limits, &mut || true)
        .unwrap()
        .into_graph();
    let payload = payload();
    let mut control = Control::new(&limits);
    let shape = control.payload(&payload, &mut || true).unwrap();
    control.graph(&graph, &mut || true).unwrap();
    let dag = codec::decode(&payload, shape, &graph, &mut control, &mut || true).unwrap();
    for mutation in 0..4 {
        let mut proof = compact::ExprRefutation {
            graph: graph.clone(),
            dag: dag.clone(),
        };
        match mutation {
            0 => proof.graph.bit_lemmas[0].kind = BitLemmaKind::Not,
            1 => proof.graph.bit_lemmas[0].ins[0] = 2,
            2 => proof.dag.original_clauses.swap(0, 1),
            3 => proof.dag.original_clauses[0].1[0] = Literal::from_index(3),
            _ => unreachable!(),
        }
        assert!(proof
            .validate(&limits, &gate_limits(&limits), &mut || true)
            .is_err());
    }
}
