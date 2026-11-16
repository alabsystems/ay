// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kitten's certificate of an UNSAT answer: the learned clauses of its
//! clausal core, each with the clauses its conflict analysis resolved.

use super::*;
use std::collections::HashMap;

/// An antecedent of a core lemma.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CoreAntecedent {
    /// An environment clause, by the id it was added with
    /// (`add_clause_with_id`).
    Original(u32),
    /// An earlier lemma of the same core, by its index.
    Lemma(u32),
}

/// The learned clauses in the clausal core of kitten's last UNSAT answer, in
/// derivation order with literals in the external encoding, and for each the
/// clauses it was learned from. Every lemma is RUP over its antecedents, so
/// over the environment clauses plus the lemmas before it: adding them in
/// order to a DRAT/VeriPB proof makes the implied unit or binary RUP too
/// (Kissat sweep.c save_core / add_core), and on the VeriPB route the
/// antecedents let each step name what it follows from.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct CoreLemmas {
    pub(crate) lemmas: Vec<Vec<u32>>,
    pub(crate) antecedents: Vec<Vec<CoreAntecedent>>,
    /// The core's root when it is an environment clause, by its id: an
    /// assumption failure that resolved a single clause takes that clause as
    /// its failing clause and learns nothing, so it alone certifies the fact.
    pub(crate) root_original: Option<u32>,
}

impl Kitten {
    /// The core lemmas of the last UNSAT answer — a real inconsistency or an
    /// assumption failure. Empty unless antecedent tracking is on.
    pub(crate) fn core_lemmas_external(&mut self) -> CoreLemmas {
        let mut core = CoreLemmas::default();
        if !self.track_antecedents {
            return core;
        }
        let root = if self.inconsistent != INVALID {
            self.inconsistent
        } else if self.failing != INVALID {
            self.failing
        } else {
            return core;
        };
        if (self.clause_flags(root) & LEARNED_FLAG) == 0 {
            core.root_original = Some(self.clause_data[root as usize]);
        }
        self.reset_core_marks();
        let mut queue: Vec<u32> = vec![root];
        let mut qi = 0;
        while qi < queue.len() {
            let ref_ = queue[qi];
            qi += 1;
            if (self.clause_flags(ref_) & CORE_FLAG) != 0 {
                continue;
            }
            self.set_clause_flag(ref_, CORE_FLAG);
            if (self.clause_flags(ref_) & LEARNED_FLAG) != 0 {
                let aux = self.clause_data[ref_ as usize] as usize;
                let size = self.clause_size(ref_) as usize;
                let ante_start = ref_ as usize + 3 + size;
                for j in 0..aux {
                    let ante_ref = self.clause_data[ante_start + j];
                    if ante_ref != INVALID {
                        queue.push(ante_ref);
                    }
                }
            }
        }
        let mut lemma_index: HashMap<u32, u32> = HashMap::new();
        let mut offset = self.end_original;
        while offset + 2 < self.clause_data.len() {
            let aux = self.clause_data[offset] as usize;
            let size = self.clause_data[offset + 1] as usize;
            let flags = self.clause_data[offset + 2];
            let learned = (flags & LEARNED_FLAG) != 0;
            if learned && (flags & CORE_FLAG) != 0 {
                let lits: Vec<u32> = (0..size)
                    .map(|i| {
                        let il = self.clause_data[offset + 3 + i];
                        self.int_to_ext[(il / 2) as usize] * 2 + (il & 1)
                    })
                    .collect();
                let ante_start = offset + 3 + size;
                let antecedents: Vec<CoreAntecedent> = (0..aux)
                    .filter_map(|j| {
                        let ante_ref = self.clause_data[ante_start + j];
                        if ante_ref == INVALID {
                            None
                        } else if (self.clause_flags(ante_ref) & LEARNED_FLAG) == 0 {
                            Some(CoreAntecedent::Original(
                                self.clause_data[ante_ref as usize],
                            ))
                        } else {
                            lemma_index
                                .get(&ante_ref)
                                .map(|&i| CoreAntecedent::Lemma(i))
                        }
                    })
                    .collect();
                lemma_index.insert(offset as u32, core.lemmas.len() as u32);
                core.lemmas.push(lits);
                core.antecedents.push(antecedents);
            }
            offset += 3 + size + if learned { aux } else { 0 };
        }
        core
    }
}
