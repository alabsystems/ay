// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Term scanning infrastructure for sequence theory.

// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::{Symbol, TermData, TermId};

/// Allowlist of Seq operations with full axiom support in the theory solver.
/// Any `seq.*` operation NOT in this list triggers Unknown (not false SAT).
/// Uses a positive allowlist instead of a negative blocklist so that newly-parsed
/// seq operations cannot silently become uninterpreted functions (#6026).
pub(super) const SUPPORTED_SEQ_OPS: &[&str] = &[
    "seq.len",
    "seq.unit",
    "seq.empty",
    "seq.++",
    "seq.nth",
    "seq.contains",
    "seq.extract",
    "seq.prefixof",
    "seq.suffixof",
    "seq.indexof",
    "seq.last_indexof",
    "seq.replace",
    // NOTE: seq.to_re, seq.in_re, seq.map, seq.mapi, seq.foldl, seq.foldli
    // are parsed (#6030) but NOT in this allowlist — solver returns Unknown.
    // Add to this list when axiom generation is implemented.
    // seq.map/seq.mapi/seq.foldl/seq.foldli: finitely-unfoldable occurrences
    // are ELIMINATED before this guard by `unfold_ho_seq_ops` (#ho-seq, see
    // ho_unfold.rs); the tokens stay off the allowlist so anything the
    // unfolder cannot bound still fails closed to Unknown.
];
/// Seq structure terms collected from assertion scan.
///
/// Supports incremental scanning: `scan_roots()` can be called multiple times
/// with different root term sets, and dedup sets ensure each seq operation is
/// collected at most once (#6005).
pub(super) struct SeqTermScan {
    /// `(seq.len(x), x)` pairs.
    pub(super) len_terms: Vec<(TermId, TermId)>,
    /// `seq.unit(x)` term IDs.
    pub(super) unit_terms: Vec<TermId>,
    /// `seq.empty` term IDs.
    pub(super) empty_terms: Vec<TermId>,
    /// `(seq.++(a,b), [a,b])` pairs.
    pub(super) concat_terms: Vec<(TermId, Vec<TermId>)>,
    /// `(seq.nth(s, i), s, i)` triples.
    pub(super) nth_terms: Vec<(TermId, TermId, TermId)>,
    /// `(seq.contains(s, t), s, t)` triples (#5841).
    pub(super) contains_terms: Vec<(TermId, TermId, TermId)>,
    /// `(seq.extract(s, i, n), s, i, n)` 4-tuples (#5841).
    pub(super) extract_terms: Vec<(TermId, TermId, TermId, TermId)>,
    /// `(seq.prefixof(s, t), s, t)` triples (#5841).
    pub(super) prefixof_terms: Vec<(TermId, TermId, TermId)>,
    /// `(seq.suffixof(s, t), s, t)` triples (#5841).
    pub(super) suffixof_terms: Vec<(TermId, TermId, TermId)>,
    /// `(seq.indexof(s, t, i), s, t, i)` 4-tuples (#5841).
    pub(super) indexof_terms: Vec<(TermId, TermId, TermId, TermId)>,
    /// `(seq.last_indexof(s, t), s, t)` triples (#6030).
    pub(super) last_indexof_terms: Vec<(TermId, TermId, TermId)>,
    /// `(seq.replace(u, s, t), u, s, t)` 4-tuples (#5841).
    pub(super) replace_terms: Vec<(TermId, TermId, TermId, TermId)>,
    /// Whether any axiom-supported operation was found (triggers LIA routing).
    pub(super) has_axiom_ops: bool,
    /// Dedup sets for incremental scanning (#6005).
    seen_len: HashSet<TermId>,
    seen_unit: HashSet<TermId>,
    seen_empty: HashSet<TermId>,
    seen_concat: HashSet<TermId>,
    seen_nth: HashSet<TermId>,
    seen_contains: HashSet<TermId>,
    seen_extract: HashSet<TermId>,
    seen_prefixof: HashSet<TermId>,
    seen_suffixof: HashSet<TermId>,
    seen_indexof: HashSet<TermId>,
    seen_last_indexof: HashSet<TermId>,
    seen_replace: HashSet<TermId>,
    /// Term IDs already visited during scanning.
    visited: HashSet<TermId>,
}

impl SeqTermScan {
    pub(super) fn new() -> Self {
        Self {
            len_terms: Vec::new(),
            unit_terms: Vec::new(),
            empty_terms: Vec::new(),
            concat_terms: Vec::new(),
            nth_terms: Vec::new(),
            contains_terms: Vec::new(),
            extract_terms: Vec::new(),
            prefixof_terms: Vec::new(),
            suffixof_terms: Vec::new(),
            indexof_terms: Vec::new(),
            last_indexof_terms: Vec::new(),
            replace_terms: Vec::new(),
            has_axiom_ops: false,
            seen_len: HashSet::default(),
            seen_unit: HashSet::default(),
            seen_empty: HashSet::default(),
            seen_concat: HashSet::default(),
            seen_nth: HashSet::default(),
            seen_contains: HashSet::default(),
            seen_extract: HashSet::default(),
            seen_prefixof: HashSet::default(),
            seen_suffixof: HashSet::default(),
            seen_indexof: HashSet::default(),
            seen_last_indexof: HashSet::default(),
            seen_replace: HashSet::default(),
            visited: HashSet::default(),
        }
    }

    /// Scan a set of root terms for seq operations, appending to existing results.
    /// Dedup sets ensure each term is collected at most once even across multiple
    /// `scan_roots` calls (#6005).
    pub(super) fn scan_roots(&mut self, terms: &ay_core::term::TermStore, roots: &[TermId]) {
        let mut stack: Vec<TermId> = roots.to_vec();

        while let Some(term) = stack.pop() {
            if !self.visited.insert(term) {
                continue;
            }
            match terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    if name == "seq.len" && args.len() == 1 && self.seen_len.insert(args[0]) {
                        self.len_terms.push((term, args[0]));
                    }
                    if name == "seq.unit" && args.len() == 1 && self.seen_unit.insert(term) {
                        self.unit_terms.push(term);
                    }
                    if name == "seq.empty" && args.is_empty() && self.seen_empty.insert(term) {
                        self.empty_terms.push(term);
                    }
                    if name == "seq.++" && args.len() >= 2 && self.seen_concat.insert(term) {
                        self.concat_terms.push((term, args.clone()));
                    }
                    if name == "seq.nth" && args.len() == 2 && self.seen_nth.insert(term) {
                        self.nth_terms.push((term, args[0], args[1]));
                    }
                    if name == "seq.contains" && args.len() == 2 && self.seen_contains.insert(term)
                    {
                        self.contains_terms.push((term, args[0], args[1]));
                        self.has_axiom_ops = true;
                    }
                    if name == "seq.extract" && args.len() == 3 && self.seen_extract.insert(term) {
                        self.extract_terms.push((term, args[0], args[1], args[2]));
                        self.has_axiom_ops = true;
                    }
                    if name == "seq.prefixof" && args.len() == 2 && self.seen_prefixof.insert(term)
                    {
                        self.prefixof_terms.push((term, args[0], args[1]));
                        self.has_axiom_ops = true;
                    }
                    if name == "seq.suffixof" && args.len() == 2 && self.seen_suffixof.insert(term)
                    {
                        self.suffixof_terms.push((term, args[0], args[1]));
                        self.has_axiom_ops = true;
                    }
                    if name == "seq.indexof" && args.len() == 3 && self.seen_indexof.insert(term) {
                        self.indexof_terms.push((term, args[0], args[1], args[2]));
                        self.has_axiom_ops = true;
                    }
                    if name == "seq.last_indexof"
                        && args.len() == 2
                        && self.seen_last_indexof.insert(term)
                    {
                        self.last_indexof_terms.push((term, args[0], args[1]));
                        self.has_axiom_ops = true;
                    }
                    if name == "seq.replace" && args.len() == 3 && self.seen_replace.insert(term) {
                        self.replace_terms.push((term, args[0], args[1], args[2]));
                        self.has_axiom_ops = true;
                    }
                    for arg in args {
                        stack.push(*arg);
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                _ => {}
            }
        }
    }

    /// Number of axiom-generating operations found so far.
    pub(super) fn axiom_op_count(&self) -> usize {
        self.contains_terms.len()
            + self.extract_terms.len()
            + self.prefixof_terms.len()
            + self.suffixof_terms.len()
            + self.indexof_terms.len()
            + self.last_indexof_terms.len()
            + self.replace_terms.len()
    }

    /// Snapshot current term counts so a subsequent `scan_roots` can identify
    /// which terms are new. Used by the two-pass architecture (#6005) to avoid
    /// re-axiomatizing terms from the first pass (which creates duplicate Skolems).
    pub(super) fn snapshot(&self) -> SeqTermOffsets {
        SeqTermOffsets {
            len: self.len_terms.len(),
            unit: self.unit_terms.len(),
            empty: self.empty_terms.len(),
            concat: self.concat_terms.len(),
            nth: self.nth_terms.len(),
            contains: self.contains_terms.len(),
            extract: self.extract_terms.len(),
            prefixof: self.prefixof_terms.len(),
            suffixof: self.suffixof_terms.len(),
            indexof: self.indexof_terms.len(),
            last_indexof: self.last_indexof_terms.len(),
            replace: self.replace_terms.len(),
        }
    }

    /// Create a new `SeqTermScan` containing only terms added after the given
    /// snapshot offsets. The dedup/visited sets are NOT copied since the new
    /// scan is only used for axiom generation, not further scanning.
    pub(super) fn new_terms_since(&self, offsets: &SeqTermOffsets) -> Self {
        let mut new_scan = Self::new();
        new_scan.len_terms = self.len_terms[offsets.len..].to_vec();
        new_scan.unit_terms = self.unit_terms[offsets.unit..].to_vec();
        new_scan.empty_terms = self.empty_terms[offsets.empty..].to_vec();
        new_scan.concat_terms = self.concat_terms[offsets.concat..].to_vec();
        new_scan.nth_terms = self.nth_terms[offsets.nth..].to_vec();
        new_scan.contains_terms = self.contains_terms[offsets.contains..].to_vec();
        new_scan.extract_terms = self.extract_terms[offsets.extract..].to_vec();
        new_scan.prefixof_terms = self.prefixof_terms[offsets.prefixof..].to_vec();
        new_scan.suffixof_terms = self.suffixof_terms[offsets.suffixof..].to_vec();
        new_scan.indexof_terms = self.indexof_terms[offsets.indexof..].to_vec();
        new_scan.last_indexof_terms = self.last_indexof_terms[offsets.last_indexof..].to_vec();
        new_scan.replace_terms = self.replace_terms[offsets.replace..].to_vec();
        new_scan.has_axiom_ops = new_scan.axiom_op_count() > 0;
        new_scan
    }
}

/// Snapshot of `SeqTermScan` term counts at a point in time.
/// Used to identify which terms are "new" after an incremental `scan_roots` call.
pub(super) struct SeqTermOffsets {
    pub(super) len: usize,
    pub(super) unit: usize,
    pub(super) empty: usize,
    pub(super) concat: usize,
    pub(super) nth: usize,
    pub(super) contains: usize,
    pub(super) extract: usize,
    pub(super) prefixof: usize,
    pub(super) suffixof: usize,
    pub(super) indexof: usize,
    pub(super) last_indexof: usize,
    pub(super) replace: usize,
}
