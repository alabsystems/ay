// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

mod cleanup;
mod malformed;
mod resources;
mod stops;

const JSON: &[u8] = br#"{"version":1,"rows":[{"id":4,"literals":[2],"hints":[1,2]},{"id":5,"literals":[],"hints":[3,4]}],"empty_clause_id":5}"#;

struct Fixture {
    wire: WireLimits,
    proof: BvExprProofLimits,
    gates: BvBlastValidateLimits,
}

impl Fixture {
    fn new() -> Self {
        let deadline = Instant::now() + Duration::from_secs(60);
        Self {
            wire: WireLimits {
                max_json_bytes: 65536,
                max_rows: 100,
                max_literals: 1000,
                max_hints: 1000,
                max_work: 2_000_000,
                max_storage_bytes: 1024 * 1024,
                deadline,
            },
            proof: BvExprProofLimits::conservative_external(deadline, 100),
            gates: BvBlastValidateLimits {
                deadline: Some(deadline),
                max_vars: 4096,
                max_bit_lemmas: 4096,
                max_clauses: 16000,
                max_clause_literals: 64,
                max_original_literals: 64000,
                max_resolution_steps: 100,
                max_derived_literals: 10000,
                max_work: 1_000_000,
            },
        }
    }
    fn decode(&self, bytes: &[u8]) -> WireOutcome<RetainedBvRefutation> {
        decode(bytes, &self.wire, &self.proof, &self.gates, &mut || true)
    }
    fn encode(&self, payload: &RetainedBvRefutation) -> WireOutcome<Vec<u8>> {
        encode(payload, &self.wire, &self.proof, &self.gates, &mut || true)
    }
}

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

#[test]
fn bounded_wire_is_canonical_and_round_trips_without_proof_authority() {
    let fixture = Fixture::new();
    let encoded = fixture.encode(&payload());
    let bytes = encoded.result.unwrap();
    assert_eq!(bytes, JSON);
    assert_eq!(bytes, serde_json::to_vec(&payload()).unwrap());
    assert_eq!(
        encoded.usage.returned_owned_bytes,
        size_of::<Vec<u8>>() + bytes.capacity()
    );
    let decoded = fixture.decode(&bytes);
    let value = decoded.result.unwrap();
    assert_eq!(value, payload());
    let owned = size_of::<RetainedBvRefutation>()
        + value.rows.capacity() * size_of::<RetainedRupRow>()
        + value
            .rows
            .iter()
            .map(|row| {
                row.literals.capacity() * size_of::<u32>() + row.hints.capacity() * size_of::<u64>()
            })
            .sum::<usize>();
    assert_eq!(decoded.usage.returned_owned_bytes, owned);
    assert!(decoded.usage.peak_storage_bytes >= bytes.len() + lexical::OPAQUE_BYTES + owned);
}

#[test]
fn valid_escaped_keys_field_order_whitespace_and_integer_boundaries_decode() {
    let fixture = Fixture::new();
    let reordered = br#" { "empty_clause_id":5,"rows":[{"hints":[1,2],"literals":[2],"id":4},{"literals":[],"id":5,"hints":[3,4]}],"\u0076\u0065\u0072\u0073\u0069\u006f\u006e":1 } "#;
    assert_eq!(fixture.decode(reordered).result, Ok(payload()));
    let escaped_terminal = std::str::from_utf8(JSON).unwrap().replace(
        "empty_clause_id",
        r"\u0065\u006d\u0070\u0074\u0079\u005f\u0063\u006c\u0061\u0075\u0073\u0065\u005f\u0069\u0064",
    );
    assert_eq!(
        fixture.decode(escaped_terminal.as_bytes()).result,
        Ok(payload())
    );
    let mut maximal = payload();
    maximal.rows[0].id = u64::MAX - 1;
    maximal.rows[0].literals[0] = u32::MAX;
    maximal.rows[1].id = u64::MAX;
    maximal.rows[1].hints[1] = u64::MAX - 1;
    maximal.empty_clause_id = u64::MAX;
    let bytes = fixture.encode(&maximal).result.unwrap();
    assert_eq!(fixture.decode(&bytes).result, Ok(maximal));
}

#[test]
fn decoded_rows_still_require_source_bound_independent_replay() {
    let mut fixture = Fixture::new();
    fixture.proof.resolution.max_conflicts = Some(0);
    fixture.proof.resolution.max_decisions = Some(0);
    fixture.proof.resolution.max_backward_reconstruction_bytes = 0;
    fixture.proof.resolution.max_pending_deletions = 0;
    let value = fixture.decode(JSON).result.unwrap();
    let a = BvExpr::leaf("a", 1);
    replay_bv_expr_refutation(
        &a,
        &a,
        Some(&value),
        &fixture.proof,
        &fixture.gates,
        &mut || true,
    )
    .unwrap();
    assert!(replay_bv_expr_refutation(
        &a,
        &BvExpr::not(a.clone()),
        Some(&value),
        &fixture.proof,
        &fixture.gates,
        &mut || true
    )
    .is_err());
    let mut corrupted = value;
    corrupted.rows[1].hints = vec![4]; // Wire-valid but missing final conflict.
    let encoded = fixture.encode(&corrupted).result.unwrap();
    let decoded = fixture.decode(&encoded).result.unwrap();
    assert!(replay_bv_expr_refutation(
        &a,
        &a,
        Some(&decoded),
        &fixture.proof,
        &fixture.gates,
        &mut || true
    )
    .is_err());
}
