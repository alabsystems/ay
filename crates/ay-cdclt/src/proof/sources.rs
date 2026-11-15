// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The recorded justifications of a refutation, indexed by clause identity
//! (the encoding's clauses and the kernel's records; see the parent module).

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{ClausificationProof, CnfClause, TermId, TheoryLemmaKind};
use ay_sat::Literal;

use crate::engine::RecordedStep;

/// Sorted, deduplicated literals: the identity of a clause.
pub(super) fn key(lits: &[Literal]) -> Vec<Literal> {
    let mut k = lits.to_vec();
    k.sort_unstable();
    k.dedup();
    k
}

/// The recorded justifications, indexed by clause identity.
pub(super) struct Sources<'a> {
    pub(super) cnf_annotations: &'a [Option<ClausificationProof>],
    /// Input clause identity -> encoding clause index.
    pub(super) input: HashMap<Vec<Literal>, usize>,
    /// Encoding clause index of an assertion's unit -> the assertion.
    pub(super) roots: HashMap<usize, TermId>,
    /// Kernel record identity -> record index (a certified record first).
    pub(super) record: HashMap<Vec<Literal>, usize>,
    /// Literal -> records containing it (for traced subsets of a record).
    pub(super) by_literal: HashMap<Literal, Vec<usize>>,
    pub(super) record_keys: Vec<Vec<Literal>>,
}

impl<'a> Sources<'a> {
    pub(super) fn new(
        assertions: &[TermId],
        cnf: &[CnfClause],
        annotations: &'a [Option<ClausificationProof>],
        records: &[RecordedStep],
    ) -> Self {
        let mut input: HashMap<Vec<Literal>, usize> = HashMap::default();
        let mut roots: HashMap<usize, TermId> = HashMap::default();
        let mut next_root = assertions.iter();
        for (idx, clause) in cnf.iter().enumerate() {
            let lits: Vec<Literal> = clause
                .literals()
                .iter()
                .map(|&d| Literal::from_dimacs(d))
                .collect();
            input.entry(key(&lits)).or_insert(idx);
            // Tseitin annotates every clause but the unit asserting each root,
            // and emits those units in assertion order.
            if annotations.get(idx).is_some_and(Option::is_none) {
                if let Some(&assertion) = next_root.next() {
                    roots.insert(idx, assertion);
                }
            }
        }
        let mut record: HashMap<Vec<Literal>, usize> = HashMap::default();
        let mut by_literal: HashMap<Literal, Vec<usize>> = HashMap::default();
        let mut record_keys = Vec::with_capacity(records.len());
        for (idx, step) in records.iter().enumerate() {
            let k = key(&step.sat_clause);
            let certified =
                step.hint.kind != TheoryLemmaKind::Generic || !step.hint.premises.is_empty();
            match record.get(&k) {
                Some(&old)
                    if certified
                        && records[old].hint.kind == TheoryLemmaKind::Generic
                        && records[old].hint.premises.is_empty() =>
                {
                    record.insert(k.clone(), idx);
                }
                Some(_) => {}
                None => {
                    record.insert(k.clone(), idx);
                }
            }
            for &lit in &k {
                by_literal.entry(lit).or_default().push(idx);
            }
            record_keys.push(k);
        }
        Self {
            cnf_annotations: annotations,
            input,
            roots,
            record,
            by_literal,
            record_keys,
        }
    }

    /// Records whose clause contains every literal of `lits`.
    pub(super) fn supersets(&self, lits: &[Literal]) -> Vec<usize> {
        let Some(shortest) = lits
            .iter()
            .filter_map(|l| self.by_literal.get(l))
            .min_by_key(|v| v.len())
        else {
            return Vec::new();
        };
        if lits.iter().any(|l| !self.by_literal.contains_key(l)) {
            return Vec::new();
        }
        shortest
            .iter()
            .copied()
            .filter(|&r| {
                let k = &self.record_keys[r];
                lits.iter().all(|l| k.binary_search(l).is_ok())
            })
            .collect()
    }
}
