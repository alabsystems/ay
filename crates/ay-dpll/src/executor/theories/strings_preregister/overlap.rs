// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Prefix/suffix overlap constant equality inference for string pre-registration.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::TermId;

use super::super::super::Executor;
use super::OverlapMergeResult;

impl Executor {
    /// Infer exact string equalities from prefix/suffix overlap with fixed length.
    ///
    /// Handles direct predicates:
    /// - `str.prefixof(p, x)`, `str.suffixof(s, x)`
    ///
    /// If `len(x) = n` and `n` exactly closes the prefix/suffix overlap
    /// (`overlap = |p| + |s| - n`) with consistent overlap characters, `x` is
    /// uniquely determined and we add `x = merged_constant`.
    pub(in crate::executor) fn preregister_overlap_constant_equalities(
        &mut self,
        assertions: &[TermId],
    ) -> Vec<TermId> {
        let mut prefixes: HashMap<TermId, Vec<String>> = HashMap::default();
        let mut suffixes: HashMap<TermId, Vec<String>> = HashMap::default();
        let mut exact_lengths: HashMap<TermId, usize> = HashMap::default();

        for &term in assertions {
            let (atom, positive) = match self.ctx.terms.get(term) {
                TermData::Not(inner) => (*inner, false),
                _ => (term, true),
            };
            if !positive {
                continue;
            }

            let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(atom) else {
                continue;
            };

            match name.as_str() {
                "=" if args.len() == 2 => {
                    let lhs = args[0];
                    let rhs = args[1];

                    if let Some((x, n)) = self.extract_strlen_eq_const(lhs, rhs) {
                        exact_lengths.insert(x, n);
                    }
                    if let Some((x, n)) = self.extract_strlen_eq_const(rhs, lhs) {
                        exact_lengths.insert(x, n);
                    }

                    self.collect_concat_edge_constants(lhs, rhs, &mut prefixes, &mut suffixes);
                }
                "str.prefixof" if args.len() == 2 => {
                    if let TermData::Const(Constant::String(p)) = self.ctx.terms.get(args[0]) {
                        prefixes.entry(args[1]).or_default().push(p.clone());
                    }
                }
                "str.suffixof" if args.len() == 2 => {
                    if let TermData::Const(Constant::String(s)) = self.ctx.terms.get(args[0]) {
                        suffixes.entry(args[1]).or_default().push(s.clone());
                    }
                }
                _ => {}
            }
        }

        let mut inferred = Vec::new();
        let mut seen = HashSet::default();

        for (&x, &target_len) in &exact_lengths {
            let Some(ps) = prefixes.get(&x) else {
                continue;
            };
            let Some(ss) = suffixes.get(&x) else {
                continue;
            };

            for p in ps {
                for s in ss {
                    match Self::merge_prefix_suffix_exact_len(p, s, target_len) {
                        OverlapMergeResult::Merged(merged) => {
                            let const_term = self.ctx.terms.mk_string(merged);
                            let eq = self.ctx.terms.mk_eq(x, const_term);
                            if seen.insert(eq) {
                                inferred.push(eq);
                            }
                        }
                        OverlapMergeResult::Conflict => {
                            // Overlap chars mismatch or target_len too short:
                            // prefix + suffix + length is provably impossible.
                            inferred.push(self.ctx.terms.false_term());
                            return inferred;
                        }
                        OverlapMergeResult::Undetermined => {}
                    }
                }
            }
        }

        inferred
    }

    pub(in crate::executor) fn extract_strlen_eq_const(
        &self,
        maybe_len: TermId,
        maybe_const: TermId,
    ) -> Option<(TermId, usize)> {
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(maybe_len) else {
            return None;
        };
        if name != "str.len" || args.len() != 1 {
            return None;
        }
        let TermData::Const(Constant::Int(n)) = self.ctx.terms.get(maybe_const) else {
            return None;
        };
        let v: usize = n.try_into().ok()?;
        Some((args[0], v))
    }

    pub(in crate::executor) fn collect_concat_edge_constants(
        &self,
        lhs: TermId,
        rhs: TermId,
        prefixes: &mut HashMap<TermId, Vec<String>>,
        suffixes: &mut HashMap<TermId, Vec<String>>,
    ) {
        self.collect_concat_edge_constants_one_way(lhs, rhs, prefixes, suffixes);
        self.collect_concat_edge_constants_one_way(rhs, lhs, prefixes, suffixes);
    }

    pub(in crate::executor) fn collect_concat_edge_constants_one_way(
        &self,
        maybe_concat: TermId,
        target: TermId,
        prefixes: &mut HashMap<TermId, Vec<String>>,
        suffixes: &mut HashMap<TermId, Vec<String>>,
    ) {
        let Some((prefix, suffix)) = self.concat_edge_constants(maybe_concat) else {
            return;
        };

        if let Some(p) = prefix {
            prefixes.entry(target).or_default().push(p);
        }
        if let Some(s) = suffix {
            suffixes.entry(target).or_default().push(s);
        }
    }

    pub(in crate::executor) fn concat_edge_constants(
        &self,
        maybe_concat: TermId,
    ) -> Option<(Option<String>, Option<String>)> {
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(maybe_concat) else {
            return None;
        };
        if name != "str.++" || args.is_empty() {
            return None;
        }

        let mut prefix = String::new();
        for &arg in args {
            match self.ctx.terms.get(arg) {
                TermData::Const(Constant::String(s)) => prefix.push_str(s),
                _ => break,
            }
        }
        let prefix = (!prefix.is_empty()).then_some(prefix);

        let mut suffix = String::new();
        for &arg in args.iter().rev() {
            match self.ctx.terms.get(arg) {
                TermData::Const(Constant::String(s)) => {
                    suffix.insert_str(0, s);
                }
                _ => break,
            }
        }
        let suffix = (!suffix.is_empty()).then_some(suffix);

        if prefix.is_none() && suffix.is_none() {
            return None;
        }
        Some((prefix, suffix))
    }

    pub(super) fn merge_prefix_suffix_exact_len(
        prefix: &str,
        suffix: &str,
        target_len: usize,
    ) -> OverlapMergeResult {
        let p_chars: Vec<char> = prefix.chars().collect();
        let s_chars: Vec<char> = suffix.chars().collect();
        let p_len = p_chars.len();
        let s_len = s_chars.len();

        // If target is longer than concatenation, there is free middle content.
        // This helper only handles exact, uniquely-determined overlap cases.
        if target_len > p_len + s_len {
            return OverlapMergeResult::Undetermined;
        }

        let overlap = p_len + s_len - target_len;
        // target_len < min(p_len, s_len): prefix or suffix alone exceeds the
        // target length, which is impossible.
        if overlap > p_len.min(s_len) {
            return OverlapMergeResult::Conflict;
        }
        debug_assert!(
            overlap <= p_len && overlap <= s_len,
            "BUG: merge_prefix_suffix_exact_len overlap {overlap} exceeds prefix len {p_len} or suffix len {s_len}"
        );

        // Overlapping characters must agree; mismatch → provably UNSAT.
        if overlap > 0 && p_chars[p_len - overlap..] != s_chars[..overlap] {
            return OverlapMergeResult::Conflict;
        }

        let mut merged = String::new();
        merged.extend(p_chars.iter());
        merged.extend(s_chars[overlap..].iter());
        if merged.chars().count() != target_len {
            return OverlapMergeResult::Undetermined;
        }
        OverlapMergeResult::Merged(merged)
    }
}
