// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Deep chains of the builtin `and` / `or`, built with one constructor call.
//!
//! `TermStore::mk_and` / `mk_or` flatten nested applications of themselves,
//! sort and deduplicate on every call. Elaborating a chain
//! `(and (and (and a b) c) … z)` bottom-up therefore built one intermediate
//! conjunction per level, each holding every leaf below it: quadratic time and
//! memory in the chain's length. QF_IDL mathsat `post_office` PO4-8-PO4 nests
//! 16,763 levels; its `--z3-mode` run was still elaborating that assertion 6 s
//! into a `-T:10` run (sampled: `elaborate_app` → `mk_and`), at 789 MB, and ended
//! in the watchdog's hard exit. z3 answers it in 0.16 s.
//!
//! A chain whose nested elaboration would build at least
//! [`MIN_NESTED_WORK`] leaf slots in intermediate terms is gathered here
//! instead: its leaves, in the left-to-right order the nested elaboration
//! visits them, go to one `mk_and`/`mk_or` call. The result is the same
//! connective over the same leaves; only the intermediate terms are never
//! built.
//!
//! Gathering also renumbers the term store (the intermediates no longer take
//! ids, and leaves are interned before them rather than between them), and
//! some searches are sensitive to that numbering. So a chain is gathered only
//! where the quadratic construction is a real cost. The first criterion, 64
//! nested applications, also gathered chains a few hundred deep whose nested
//! construction is cheap, and the renumbering alone lost `sat` verdicts:
//! QF_UFLIA mathsat `Hash` `hash_sat_09_07` (depth 368) answered `sat` in
//! 0.8-1.8 s and then `unknown` at `-T:30` 6/6, and the base binary given a
//! pre-flattened copy reproduced the loss exactly. The same held for
//! `hash_sat_05_14` (229), `hash_sat_08_11` (439) and Wisa `xs-14-20` (110).
//! Shallower nests elaborate exactly as before.

use crate::command::Term as ParsedTerm;

use super::Context;

/// Leaf slots the nested elaboration of a chain must build in intermediate
/// terms before the chain is gathered. A chain of depth `d` builds about
/// `d^2 / 2`, so this is a depth of about 1,450: the post_office and fischer
/// chains (4,800-46,000 deep) are gathered, the Hash and Wisa chains (at most
/// 1,200) are not.
const MIN_NESTED_WORK: usize = 1 << 20;

/// Nested applications counted before [`nested_construction_work`] stops
/// counting and reports the chain as worth gathering.
const MAX_COUNTED_NESTED: usize = 1 << 16;

impl Context {
    /// The leaves of a deep chain of the builtin `name` (`and` or `or`) rooted
    /// at an application with arguments `args`, or `None` when `name` is not
    /// the builtin connective here or the chain is shallow.
    pub(super) fn deep_connective_chain_leaves<'source>(
        &self,
        name: &str,
        args: &'source [ParsedTerm],
    ) -> Option<Vec<&'source ParsedTerm>> {
        if !matches!(name, "and" | "or")
            || self.fun_defs.contains_key(name)
            || self.symbols.contains_key(name)
            || self.overloaded_symbols.contains_key(name)
        {
            return None;
        }
        if !self.shared_connective_scan(name, args) {
            return None;
        }
        if nested_construction_work(name, args) < MIN_NESTED_WORK {
            return None;
        }
        // A nested application with no arguments is an arity error the nested
        // elaboration reports; gathering would drop it silently.
        collect_leaves(name, args)
    }
}

/// The leaf slots the nested elaboration of these arguments would build in
/// intermediate terms: for every application of `name` under them (through
/// applications of `name` only), the number of leaves below it. Saturates at
/// `usize::MAX` once [`MAX_COUNTED_NESTED`] applications have been seen.
fn nested_construction_work(name: &str, args: &[ParsedTerm]) -> usize {
    // Pre-order list of the nested applications, each with its parent's index
    // (`None` for a child of the root) and its own direct leaf count.
    let mut nodes: Vec<(Option<usize>, usize)> = Vec::new();
    let mut stack: Vec<(&ParsedTerm, Option<usize>)> = args.iter().map(|a| (a, None)).collect();
    while let Some((term, parent)) = stack.pop() {
        let ParsedTerm::App(inner, inner_args) = term else {
            continue;
        };
        if inner != name {
            continue;
        }
        if nodes.len() >= MAX_COUNTED_NESTED {
            return usize::MAX;
        }
        let index = nodes.len();
        let direct_leaves = inner_args
            .iter()
            .filter(|arg| !matches!(arg, ParsedTerm::App(head, _) if head == name))
            .count();
        nodes.push((parent, direct_leaves));
        stack.extend(inner_args.iter().map(|arg| (arg, Some(index))));
    }
    // Children follow their parents in pre-order, so a reverse sweep sees
    // every node's subtree complete before it adds the node to its parent.
    let mut below: Vec<usize> = nodes.iter().map(|&(_, leaves)| leaves).collect();
    let mut work = 0usize;
    for index in (0..nodes.len()).rev() {
        work = work.saturating_add(below[index]);
        if let Some(parent) = nodes[index].0 {
            below[parent] = below[parent].saturating_add(below[index]);
        }
    }
    work
}

/// The non-`name` arguments under `args`, depth first, left to right: the
/// order in which elaborating the nested applications visits them. `None`
/// when a nested application of `name` has no arguments.
fn collect_leaves<'source>(
    name: &str,
    args: &'source [ParsedTerm],
) -> Option<Vec<&'source ParsedTerm>> {
    let mut leaves = Vec::new();
    let mut stack: Vec<&ParsedTerm> = args.iter().rev().collect();
    while let Some(term) = stack.pop() {
        match term {
            ParsedTerm::App(inner, inner_args) if inner == name => {
                if inner_args.is_empty() {
                    return None;
                }
                stack.extend(inner_args.iter().rev());
            }
            leaf => leaves.push(leaf),
        }
    }
    Some(leaves)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sym(s: &str) -> ParsedTerm {
        ParsedTerm::Symbol(s.to_string())
    }

    fn app(name: &str, args: Vec<ParsedTerm>) -> ParsedTerm {
        ParsedTerm::App(name.to_string(), args)
    }

    /// `(and (and (and x0 x1) x2) … xn)` as the arguments of the root.
    fn left_chain(name: &str, n: usize) -> Vec<ParsedTerm> {
        let mut term = app(name, vec![sym("x0"), sym("x1")]);
        for i in 2..n {
            term = app(name, vec![term, sym(&format!("x{i}"))]);
        }
        match &term {
            ParsedTerm::App(_, args) => args.clone(),
            _ => unreachable!(),
        }
    }

    #[test]
    fn leaves_come_out_in_elaboration_order() {
        let args = left_chain("and", 200);
        let leaves = collect_leaves("and", &args).expect("no empty application");
        let names: Vec<String> = leaves
            .iter()
            .map(|t| match t {
                ParsedTerm::Symbol(s) => s.clone(),
                _ => String::new(),
            })
            .collect();
        let expected: Vec<String> = (0..200).map(|i| format!("x{i}")).collect();
        assert_eq!(names, expected);
    }

    #[test]
    fn gathered_leaves_borrow_the_original_boundary_source() {
        let args = vec![app(
            "and",
            vec![sym("a"), app("or", vec![sym("b"), sym("c")])],
        )];
        let leaves = collect_leaves("and", &args).unwrap();
        let ParsedTerm::App(_, nested) = &args[0] else {
            panic!("and")
        };
        assert!(std::ptr::eq(leaves[0], &raw const nested[0]));
        assert!(std::ptr::eq(leaves[1], &raw const nested[1]));
    }

    #[test]
    fn other_connectives_and_annotations_are_leaves() {
        let args = vec![
            app("and", vec![sym("a"), app("or", vec![sym("b"), sym("c")])]),
            sym("d"),
        ];
        let leaves = collect_leaves("and", &args).expect("no empty application");
        assert_eq!(leaves.len(), 3);
        assert_eq!(*leaves[1], app("or", vec![sym("b"), sym("c")]));
    }

    /// A chain deep enough that its nested construction is quadratic work.
    const DEEP: usize = 2_000;

    #[test]
    fn only_chains_with_quadratic_construction_are_gathered() {
        let ctx = Context::new();
        assert!(ctx
            .deep_connective_chain_leaves("and", &left_chain("and", 10))
            .is_none());
        let deep = left_chain("or", DEEP);
        let leaves = ctx
            .deep_connective_chain_leaves("or", &deep)
            .expect("a deep chain is gathered");
        assert_eq!(leaves.len(), DEEP);
        assert!(ctx
            .deep_connective_chain_leaves("xor", &left_chain("xor", DEEP))
            .is_none());
    }

    /// Chains a few hundred deep (the QF_UFLIA Hash and Wisa families, up to
    /// 1,200) are cheap to build nested and keep the nested numbering:
    /// gathering them renumbered the term store and lost `sat` verdicts.
    #[test]
    fn a_chain_of_a_few_hundred_levels_keeps_the_nested_elaboration() {
        let ctx = Context::new();
        for depth in [64, 110, 368, 439, 1_200] {
            assert!(
                ctx.deep_connective_chain_leaves("and", &left_chain("and", depth))
                    .is_none(),
                "depth {depth} must elaborate nested"
            );
        }
        // A wide tree of many small conjunctions costs linear work.
        let wide: Vec<ParsedTerm> = (0..5_000)
            .map(|i| app("and", vec![sym(&format!("a{i}")), sym(&format!("b{i}"))]))
            .collect();
        assert!(ctx.deep_connective_chain_leaves("and", &wide).is_none());
    }

    #[test]
    fn the_nested_work_of_a_chain_is_its_triangular_leaf_count() {
        // (and (and (and x0 x1) x2) x3) under the root: nested nodes hold 2
        // and 3 leaves; the root's own leaves are not intermediate work.
        assert_eq!(
            nested_construction_work("and", &left_chain("and", 4)),
            2 + 3
        );
        assert_eq!(
            nested_construction_work("and", &left_chain("and", 100)),
            (2..100).sum::<usize>()
        );
    }

    #[test]
    fn an_empty_nested_application_is_left_to_the_nested_elaboration() {
        let mut args = left_chain("and", DEEP);
        args.push(app("and", vec![]));
        assert!(Context::new()
            .deep_connective_chain_leaves("and", &args)
            .is_none());
    }
}
