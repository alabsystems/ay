// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Differential-parser gate harness: prints a stable SHA-256 digest of the
//! fully parsed `PbInstance` / `WboInstance` for each input file, one line per
//! file (`<digest-or-error>  <path>`). Run against two builds (old and new
//! parser) and diff the outputs — any changed line is a parser regression.
//!
//!     cargo run --release -p ay-pb --example parse_digest -- FILE...
//!
//! The digest covers EVERY field the solver consumes: `num_vars`,
//! `num_constraints`, per-row `rel`/`rhs` and each term's coefficient and
//! literals (var + negation), plus the objective. Parse errors digest as the
//! full error `Display` string so error behavior is locked too.

use sha2::{Digest, Sha256};

fn hash_terms(hasher: &mut Sha256, terms: &[ay_pb::PbTerm]) {
    hasher.update((terms.len() as u64).to_le_bytes());
    for term in terms {
        hasher.update(term.coeff.to_le_bytes());
        hasher.update((term.lits.len() as u64).to_le_bytes());
        for lit in &term.lits {
            hasher.update(lit.var.to_le_bytes());
            hasher.update([u8::from(lit.negated)]);
        }
    }
}

fn hash_constraint(hasher: &mut Sha256, c: &ay_pb::PbConstraint) {
    hash_terms(hasher, &c.terms);
    hasher.update([match c.rel {
        ay_pb::PbRel::Ge => 0u8,
        ay_pb::PbRel::Eq => 1u8,
        other => unreachable!("parser only produces Ge/Eq, got {other:?}"),
    }]);
    hasher.update(c.rhs.to_le_bytes());
}

fn digest_opb(instance: &ay_pb::PbInstance) -> String {
    let mut hasher = Sha256::new();
    hasher.update(instance.num_vars.to_le_bytes());
    hasher.update(instance.num_constraints.to_le_bytes());
    hasher.update((instance.constraints.len() as u64).to_le_bytes());
    for c in &instance.constraints {
        hash_constraint(&mut hasher, c);
    }
    match &instance.objective {
        None => hasher.update([0u8]),
        Some(obj) => {
            hasher.update([1u8]);
            hash_terms(&mut hasher, &obj.terms);
        }
    }
    format!("{:x}", hasher.finalize())
}

fn digest_wbo(instance: &ay_pb::WboInstance) -> String {
    let mut hasher = Sha256::new();
    hasher.update(instance.num_vars.to_le_bytes());
    match instance.top_cost {
        None => hasher.update([0u8]),
        Some(top) => {
            hasher.update([1u8]);
            hasher.update(top.to_le_bytes());
        }
    }
    hasher.update((instance.hard_constraints.len() as u64).to_le_bytes());
    for c in &instance.hard_constraints {
        hash_constraint(&mut hasher, c);
    }
    hasher.update((instance.soft_constraints.len() as u64).to_le_bytes());
    for (cost, c) in &instance.soft_constraints {
        hasher.update(cost.to_le_bytes());
        hash_constraint(&mut hasher, c);
    }
    format!("{:x}", hasher.finalize())
}

fn main() {
    for path in std::env::args().skip(1) {
        let text = match std::fs::read_to_string(&path) {
            Ok(text) => text,
            Err(err) => {
                println!("READ-ERROR({err})  {path}");
                continue;
            }
        };
        let line = if path.ends_with(".wbo") {
            match ay_pb::parse_wbo(&text) {
                Ok(instance) => digest_wbo(&instance),
                Err(err) => format!("PARSE-ERROR({err})"),
            }
        } else {
            match ay_pb::parse_opb(&text) {
                Ok(instance) => digest_opb(&instance),
                Err(err) => format!("PARSE-ERROR({err})"),
            }
        };
        println!("{line}  {path}");
    }
}
