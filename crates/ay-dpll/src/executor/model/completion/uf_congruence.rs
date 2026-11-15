// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! UF congruence for synthesized uninterpreted-sort carrier classes.
//!
//! Phase 3 of model completion (`complete_uninterpreted_sort_model`) mints one
//! abstract element per equality class of the eager BV/AUFBV lane's
//! uninterpreted-sort carriers, merging two carriers only on an equality atom
//! the model commits to. Variable substitution can leave an application of
//! the AUTHORED assertions linked to the solve by no atom at all: once
//! `x = c0` eliminates `x`, the SAT problem holds `(= (f c0) c0)` and never
//! `(f x)`. `(f x)` then received a fresh element of its own and
//! `(or (= (f x) c0) (= (f x) c1))` evaluated to false — a satisfiable QF_UFBV
//! problem answered `unknown` (2026-10-09 audit lv9 under LNH symmetry
//! breaking's least-index pin `x = c0`, and lv10 with the pin authored).
//!
//! Functional consistency makes two applications of one function at equal
//! arguments ONE element in every model, so their classes are merged before
//! any element is minted, to a fixpoint (a merge can make further argument
//! tuples equal). This is not SAT authority: a merge only removes a split no
//! model could realize, and the strict and independent gates still re-check
//! every assertion. Two applications that already carry different elements put
//! their class in the existing `blocked_class` path, so a candidate that
//! splits one function point fails closed rather than minting a value.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData;
use ay_core::{Sort, TermId};

use super::Model;
use crate::executor::Executor;

fn find(parent: &mut [usize], mut x: usize) -> usize {
    while parent[x] != x {
        parent[x] = parent[parent[x]];
        x = parent[x];
    }
    x
}

/// Join the classes of `a` and `b`; whether they were apart.
fn union(parent: &mut [usize], a: usize, b: usize) -> bool {
    let ra = find(parent, a);
    let rb = find(parent, b);
    if ra == rb {
        return false;
    }
    parent[ra] = rb;
    true
}

impl Executor {
    /// Merge the classes (`parent`, a union-find over `carrier_terms`) of
    /// uninterpreted-sort applications of one declared function whose
    /// arguments are equal in the model: a carrier argument through its class,
    /// any other argument through its exactly evaluated value. Carriers that
    /// already resolve to the same committed element (`resolved_elem`) are one
    /// class first. Runs to a fixpoint.
    pub(super) fn close_carrier_classes_under_congruence(
        &self,
        model: &Model,
        carrier_terms: &[TermId],
        index_of: &HashMap<TermId, usize>,
        resolved_elem: &HashMap<usize, String>,
        parent: &mut [usize],
    ) {
        self.join_carriers_of_one_committed_element(carrier_terms, resolved_elem, parent);

        // The applications, with their non-carrier argument values evaluated
        // once; an argument the model does not determine excludes the
        // application (the pre-existing behavior).
        #[derive(Clone, PartialEq, Eq, Hash)]
        enum ArgKey {
            /// A carrier argument: its position, or (in a point) its class root.
            Class(usize),
            /// Any other argument: its exactly evaluated model atom.
            Value(String),
        }
        let mut apps: Vec<(usize, &str, Vec<ArgKey>)> = Vec::new();
        'apps: for (idx, &term) in carrier_terms.iter().enumerate() {
            if !matches!(self.ctx.terms.sort(term), Sort::Uninterpreted(_)) {
                continue;
            }
            let TermData::App(sym, args) = self.ctx.terms.get(term) else {
                continue;
            };
            let name = sym.name();
            if args.is_empty()
                || Self::is_known_theory_symbol(name)
                || self.ctx.is_constructor(name).is_some()
                || self.is_exact_dt_internal_symbol(name)
            {
                continue;
            }
            let mut keys = Vec::with_capacity(args.len());
            for &arg in args {
                if let Some(&arg_idx) = index_of.get(&arg) {
                    keys.push(ArgKey::Class(arg_idx));
                    continue;
                }
                match self.eval_value_to_model_atom(&self.evaluate_term(model, arg)) {
                    Some(value) => keys.push(ArgKey::Value(value)),
                    None => continue 'apps,
                }
            }
            apps.push((idx, name, keys));
        }
        if apps.len() < 2 {
            return;
        }
        loop {
            let mut changed = false;
            let mut first_at: HashMap<(&str, Vec<ArgKey>), usize> = HashMap::default();
            for (idx, name, keys) in &apps {
                let point: Vec<ArgKey> = keys
                    .iter()
                    .map(|key| match key {
                        ArgKey::Class(arg_idx) => ArgKey::Class(find(parent, *arg_idx)),
                        ArgKey::Value(value) => ArgKey::Value(value.clone()),
                    })
                    .collect();
                match first_at.get(&(*name, point.clone())) {
                    Some(&first) => changed |= union(parent, first, *idx),
                    None => {
                        first_at.insert((*name, point), *idx);
                    }
                }
            }
            if !changed {
                break;
            }
        }
    }

    /// One committed element is one model value: carriers of an uninterpreted
    /// sort that resolve to the same element (`resolved_elem`) are one class.
    fn join_carriers_of_one_committed_element(
        &self,
        carrier_terms: &[TermId],
        resolved_elem: &HashMap<usize, String>,
        parent: &mut [usize],
    ) {
        let mut by_elem: HashMap<(&Sort, &str), usize> = HashMap::default();
        let mut resolved: Vec<(&usize, &String)> = resolved_elem.iter().collect();
        resolved.sort_unstable();
        for (&idx, elem) in resolved {
            let sort = self.ctx.terms.sort(carrier_terms[idx]);
            if !matches!(sort, Sort::Uninterpreted(_)) {
                continue;
            }
            match by_elem.get(&(sort, elem.as_str())) {
                Some(&first) => {
                    union(parent, first, idx);
                }
                None => {
                    by_elem.insert((sort, elem.as_str()), idx);
                }
            }
        }
    }
}
