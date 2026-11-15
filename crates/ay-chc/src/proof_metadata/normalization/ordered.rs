// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Indexed source identity: do not sort clauses or body predicate positions.

use super::payload::DatatypeRefs;
use super::*;

/// Domain of an overlay whose spelling references no datatype sort: the
/// bytes are exactly the ones v1 always produced.
const ORDERED_DOMAIN_V1: &[u8] = b"ay.chc-source-clause-sequence/v1\0";
/// Domain of an overlay whose spelling references a datatype sort by its
/// content address (see `payload`).
const ORDERED_DOMAIN_V2: &[u8] = b"ay.chc-source-clause-sequence/v2\0";

struct SpelledClause {
    premises: Vec<String>,
    constraint: String,
    head: String,
}

/// The overlay under both domains at once. Which domain names it is known
/// only once every clause is spelled; hashing each clause as it is spelled
/// keeps one clause's spelling in memory, not the whole problem's.
struct Digests {
    v1: Sha256,
    v2: Sha256,
}

impl Digests {
    fn new() -> Self {
        let mut v1 = Sha256::new();
        v1.update(ORDERED_DOMAIN_V1);
        let mut v2 = Sha256::new();
        v2.update(ORDERED_DOMAIN_V2);
        Self { v1, v2 }
    }

    fn update(&mut self, bytes: &[u8]) {
        self.v1.update(bytes);
        self.v2.update(bytes);
    }

    fn update_field<P: Progress>(&mut self, value: &str, progress: &mut P) -> Result<(), P::Error> {
        update_field(&mut self.v1, value, progress)?;
        update_field(&mut self.v2, value, progress)
    }
}

pub(super) fn hash<P: Progress>(
    problem: &ChcProblem,
    progress: &mut P,
) -> Result<String, P::Error> {
    progress.poll()?;
    // Only a spelling that referenced a datatype sort is v2.
    let mut refs = DatatypeRefs::default();
    let pred_names = text::predicate_names(problem, progress, &mut refs)?;
    let mut digests = Digests::new();
    digests.update(&(problem.clauses().len() as u64).to_le_bytes());
    for (clause_index, clause) in problem.clauses().iter().enumerate() {
        progress.poll()?;
        let spelled = spell_clause(clause, &pred_names, progress, &mut refs)?;
        digests.update(&(clause_index as u64).to_le_bytes());
        match clause.source_query_ordinal {
            Some(ordinal) => {
                digests.update(&[1]);
                digests.update(&(ordinal as u64).to_le_bytes());
            }
            None => digests.update(&[0]),
        }
        match clause
            .action_id
            .and_then(|action| problem.action_name(action))
        {
            Some(action) => {
                digests.update(&[1]);
                digests.update_field(action, progress)?;
            }
            None => digests.update(&[0]),
        }
        digests.update(&(spelled.premises.len() as u64).to_le_bytes());
        for premise in &spelled.premises {
            digests.update_field(premise, progress)?;
        }
        digests.update_field(&spelled.constraint, progress)?;
        digests.update_field(&spelled.head, progress)?;
    }
    let digest = if refs.is_empty() {
        digests.v1
    } else {
        digests.v2
    };
    finish_hash(digest, progress)
}

fn spell_clause<P: Progress>(
    clause: &HornClause,
    pred_names: &BTreeMap<usize, String>,
    progress: &mut P,
    refs: &mut DatatypeRefs,
) -> Result<SpelledClause, P::Error> {
    let mut premises = Vec::with_capacity(clause.body.predicates.len());
    for (predicate, arguments) in &clause.body.predicates {
        premises.push(payload::predicate_app(
            *predicate, arguments, pred_names, progress, refs,
        )?);
    }
    let constraint = match &clause.body.constraint {
        Some(expression) => payload::expression(expression, pred_names, progress, refs)?,
        None => "true".to_string(),
    };
    let head = match &clause.head {
        ClauseHead::False => "false".to_string(),
        ClauseHead::Predicate(predicate, arguments) => {
            payload::predicate_app(*predicate, arguments, pred_names, progress, refs)?
        }
    };
    Ok(SpelledClause {
        premises,
        constraint,
        head,
    })
}

fn update_field<P: Progress>(
    digest: &mut Sha256,
    value: &str,
    progress: &mut P,
) -> Result<(), P::Error> {
    progress.poll()?;
    digest.update((value.len() as u64).to_le_bytes());
    update_bytes(digest, value.as_bytes(), progress)
}
