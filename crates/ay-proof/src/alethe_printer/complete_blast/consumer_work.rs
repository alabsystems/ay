// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The consumer's own measure of a document: its zero-extension normalizer's
//! work (clean `carcara_verify/zero_extend.rs`, `MAX_WORK` 4,000,000 per
//! certificate), counted from the printed TEXT.
//!
//! The normalizer rewrites every term of the certificate once before any
//! rule is checked, and refuses the certificate outright past its budget.
//! It charges one unit per command, and for every term it is handed — each
//! `define-fun` body, each clause literal, each `:args` term — one unit per
//! node it visits: a node it has seen before costs one, a new one two plus
//! one per child, and each child is visited in turn. Premise names cost
//! nothing.
//!
//! [`normalizer_work`] counts the same walk with nodes identified by their
//! TEXT. The consumer identifies terms structurally, which can only merge
//! more of them, and a head this module does not know as a built-in operator
//! is counted as an application whose function is one more child; so the
//! count is an upper bound of the consumer's. Anything it cannot read is
//! refused (`None`), never guessed at.
//!
//! Only Clean's adapter post-pass charges this budget (Clean `ba5e28ff5` on,
//! until the reading moves into its parser). A Clean that reads `zero_extend`
//! at its parse boundary, under the consumer rule `dialect:expand_zero_extend`
//! (`CleanOnlySpelling::consumer_rule`), bounds no certificate's size this
//! way; this mirror stays, as the conservative choice, until every
//! production Clean does.

use super::selfcheck::{balanced, tokens};
use ay_core::kani_compat::DetHashSet;

/// Heads the consumer parses as built-in operators (`Term::Op`), whose
/// children are exactly their arguments. Every other head of an application
/// is counted as a function symbol, one child more.
const BUILT_IN: &[&str] = &[
    "not", "and", "or", "xor", "=>", "=", "distinct", "ite", "bvnot", "bvand", "bvor", "bvxor",
    "bvnand", "bvnor", "bvxnor", "bvcomp", "bvneg", "bvadd", "bvsub", "bvmul", "bvudiv", "bvurem",
    "bvsdiv", "bvsrem", "bvsmod", "bvshl", "bvlshr", "bvashr", "bvult", "bvule", "bvugt", "bvuge",
    "bvslt", "bvsle", "bvsgt", "bvsge", "concat", "select", "store", "@bbterm", "@pbbterm", "cl",
    "+", "-", "*", "<", "<=", ">", ">=",
];

/// The normalizer's work for `document`: its `define-fun`s, `assume`s,
/// `anchor`s and `step`s, line by line. `None` when a line cannot be read.
pub(super) fn normalizer_work(document: &str) -> Option<usize> {
    let mut walk = Walk::default();
    for line in document.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let inner = balanced(line)?.strip_prefix('(')?.strip_suffix(')')?;
        let parts = tokens(inner)?;
        match parts.as_slice() {
            ["define-fun", name, "()", _sort, body] => {
                walk.term(body)?;
                // A reference to the constant is its (now seen) body.
                walk.seen.insert(name);
            }
            ["assume", _, term] => {
                walk.charge(1)?;
                walk.term(term)?;
            }
            ["anchor", ..] => walk.charge(1)?,
            ["step", _, clause, rest @ ..] => {
                walk.charge(1)?;
                let literals = clause.strip_prefix("(cl")?.strip_suffix(')')?;
                for literal in tokens(literals)? {
                    walk.term(literal)?;
                }
                if let Some(at) = rest.iter().position(|part| *part == ":args") {
                    let group = rest.get(at + 1)?;
                    for arg in tokens(group.strip_prefix('(')?.strip_suffix(')')?)? {
                        walk.term(arg)?;
                    }
                }
            }
            _ => return None,
        }
    }
    Some(walk.work)
}

#[derive(Default)]
struct Walk<'d> {
    seen: DetHashSet<&'d str>,
    work: usize,
}

impl<'d> Walk<'d> {
    fn charge(&mut self, units: usize) -> Option<()> {
        self.work = self.work.checked_add(units)?;
        Some(())
    }

    /// Visit `term`: one unit when seen before, else two plus its children.
    fn term(&mut self, term: &'d str) -> Option<()> {
        if !self.seen.insert(term) {
            return self.charge(1);
        }
        self.charge(2)?;
        // An atom, or a literal `(_ bvN W)`, has no children.
        let Some(inner) = term.strip_prefix('(') else {
            return Some(());
        };
        if inner.starts_with("_ ") {
            return Some(());
        }
        let parts = tokens(inner.strip_suffix(')')?)?;
        let (head, args) = parts.split_first()?;
        if let Some(indexed) = head.strip_prefix("(_ ") {
            // `((_ extract i j) x)`: the indices are children too.
            let indices = tokens(indexed.strip_suffix(')')?)?;
            let indices = indices.get(1..)?;
            self.charge(indices.len() + args.len())?;
            for index in indices {
                self.term(index)?;
            }
        } else if BUILT_IN.contains(head) {
            self.charge(args.len())?;
        } else {
            self.charge(args.len() + 1)?;
            self.term(head)?;
        }
        for arg in args {
            self.term(arg)?;
        }
        Some(())
    }
}

#[cfg(test)]
mod tests {
    use super::normalizer_work;

    /// Hand-counted: a definition, a new and a repeated literal, an argument.
    #[test]
    fn the_walk_counts_new_nodes_once_and_repeats_as_one() {
        let document = "(define-fun g () Bool (and a b))\n\
                        (step t1 (cl (not g) g) :rule resolution :args ((cl g)))\n\
                        (step t2 (cl (not g)) :rule resolution :premises (t1))\n";
        // define-fun: (and a b) 2+2, a 2, b 2                          = 8
        // t1: command 1; (not g) 2+1, g 1; g 1; (cl g) 2+1, g 1      = 10
        // t2: command 1; (not g) 1                                     = 2
        assert_eq!(normalizer_work(document), Some(20));
        // An unknown head is a function: one child more, and itself a node.
        assert_eq!(normalizer_work("(assume h (f a))"), Some(1 + 2 + 2 + 2 + 2));
        assert_eq!(normalizer_work("(step t1 (cl (not a)"), None);
    }
}
