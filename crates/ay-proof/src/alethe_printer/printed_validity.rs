// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Does a PRINTED clause prove itself?
//!
//! WHY THIS EXISTS. A premise-free step claims its clause out of nothing, so
//! its clause has to be VALID. When the printer cannot spell such a step as
//! the rule it names it has three outcomes, and exactly one of them is honest
//! for any given step:
//!
//! * emit the rule anyway — ships a step the external checker refuses
//!   (`invalid`), the defect this printer's judgements exist to stop;
//! * `:rule hole` — a PUBLISHED document carrying an unchecked obligation.
//!   Pinned carcara does not check holes, so it answers `holey` and the
//!   obligation is taken on AY's word. That is honest only while the clause is
//!   true. MEASURED 2026-09-17: a hand-built document whose only unchecked
//!   step is `(step t1 (cl (not (or a b c)) a b) :rule hole)` refutes a
//!   SATISFIABLE problem and pinned carcara answers `holey`, exit 0.
//! * decline the document — no certificate, and the caller's
//!   unverifiable-proof path fires.
//!
//! This module decides between the second and the third: it certifies, from
//! the printed text and nothing else, that a clause is a propositional
//! tautology. It is SOUND and deliberately INCOMPLETE — a clause it cannot
//! certify is declined, never holed, so an incompleteness costs a document and
//! never ships a false claim.
//!
//! Reading the printed text is the whole point. The term store says the step
//! is fine (AY derived it); the defect class this campaign chases is precisely
//! that "the object AY verifies and the object it ships are not the same
//! object", because a surface override maps a TERM to a spelling and a
//! composite override quotes its own spelling of every subterm.

use super::split_application;

/// Structural recursion bound. Printed gates in the corpus nest a few dozen
/// deep at most (`iso_icl1206`'s five-leaf left-nested `or` is 4); anything
/// past this is treated as an opaque atom, which can only lose a certificate.
const MAX_DEPTH: usize = 64;

/// Bound on the number of printed units extracted from one clause. Past it the
/// certificate is refused rather than paid for.
const MAX_UNITS: usize = 4096;

/// Strip matched `(not (not X))` pairs off the front of a printed term.
fn strip_double_negation(term: &str) -> String {
    let mut current = term.trim().to_string();
    loop {
        let Some(once) = split_application(&current, "not") else {
            return current;
        };
        let [inner] = once.as_slice() else {
            return current;
        };
        let Some(twice) = split_application(inner, "not") else {
            return current;
        };
        let [innermost] = twice.as_slice() else {
            return current;
        };
        current = innermost.clone();
    }
}

/// The spelling-insensitive key for a printed term.
///
/// Two things are normalised, and only two, because each is a logical identity
/// the checker itself relies on: `(not (not X))` is `X`, and `(= u v)` is
/// `(= v u)`. The second is what `iso_icl1206`'s holed gate turns on — one
/// `TermId` printed in both orientations inside one step — and it is sound for
/// every sort, `Bool` included, where `=` is the biconditional.
fn canonical(term: &str, depth: usize) -> String {
    let stripped = strip_double_negation(term);
    if depth == 0 {
        return stripped;
    }
    if let Some(once) = split_application(&stripped, "not") {
        if let [inner] = once.as_slice() {
            return format!("(not {})", canonical(inner, depth - 1));
        }
    }
    if let Some(operands) = split_application(&stripped, "=") {
        if let [left, right] = operands.as_slice() {
            let left = canonical(left, depth - 1);
            let right = canonical(right, depth - 1);
            return if left <= right {
                format!("(= {left} {right})")
            } else {
                format!("(= {right} {left})")
            };
        }
    }
    stripped
}

/// The disjuncts a printed term is equivalent to.
///
/// `(or ..)` flattens, `(=> a b)` is `(or (not a) b)`, and `(not (and ..))` is
/// the De Morgan disjunction of the negated conjuncts. Everything else is one
/// disjunct — including `(not (or ..))`, which is a CONJUNCTION and must not
/// be taken apart here.
fn push_disjuncts(term: &str, out: &mut Vec<String>, depth: usize) {
    if depth == 0 || out.len() >= MAX_UNITS {
        out.push(strip_double_negation(term));
        return;
    }
    let stripped = strip_double_negation(term);
    if let Some(operands) = split_application(&stripped, "or") {
        for operand in operands {
            push_disjuncts(&operand, out, depth - 1);
        }
        return;
    }
    if let Some(operands) = split_application(&stripped, "=>") {
        if let [antecedent, consequent] = operands.as_slice() {
            push_disjuncts(&format!("(not {antecedent})"), out, depth - 1);
            push_disjuncts(consequent, out, depth - 1);
            return;
        }
    }
    if let Some(once) = split_application(&stripped, "not") {
        if let [inner] = once.as_slice() {
            if let Some(conjuncts) = split_application(inner, "and") {
                for conjunct in conjuncts {
                    push_disjuncts(&format!("(not {conjunct})"), out, depth - 1);
                }
                return;
            }
        }
    }
    out.push(stripped);
}

/// The conjuncts a printed term is equivalent to — the dual of
/// [`push_disjuncts`].
fn push_conjuncts(term: &str, out: &mut Vec<String>, depth: usize) {
    if depth == 0 || out.len() >= MAX_UNITS {
        out.push(strip_double_negation(term));
        return;
    }
    let stripped = strip_double_negation(term);
    if let Some(operands) = split_application(&stripped, "and") {
        for operand in operands {
            push_conjuncts(&operand, out, depth - 1);
        }
        return;
    }
    if let Some(once) = split_application(&stripped, "not") {
        if let [inner] = once.as_slice() {
            if let Some(disjuncts) = split_application(inner, "or") {
                for disjunct in disjuncts {
                    push_conjuncts(&format!("(not {disjunct})"), out, depth - 1);
                }
                return;
            }
            if let Some(operands) = split_application(inner, "=>") {
                if let [antecedent, consequent] = operands.as_slice() {
                    push_conjuncts(antecedent, out, depth - 1);
                    push_conjuncts(&format!("(not {consequent})"), out, depth - 1);
                    return;
                }
            }
        }
    }
    out.push(stripped);
}

/// Is this printed clause a propositional tautology, provably, from its own
/// text?
///
/// Sound and incomplete. Two certificates, each a one-line refutation of "all
/// these literals are false at once":
///
/// * **gate** — some literal is `(not N)` and every disjunct of `N` is itself a
///   literal of the clause. If every literal is false then `N` is true, so some
///   disjunct of `N` is true, and that disjunct is a literal of the clause.
///   Contradiction. This is the `or_pos` gate's own certificate:
///   `(cl (not (or a b)) a b c)`.
/// * **and** — some literal is `(and c1 .. ck)` and every `(not ci)` is a
///   literal of the clause. If every literal is false then each `ci` is true,
///   so the conjunction is true. Contradiction. This is the De Morgan
///   `and_pos` gate's certificate: `(cl (or (not p) (not q)) p)` reaches it
///   through the disjunct flattening.
///
/// Each degenerates to "some literal and its negation are both here" when the
/// term is not a connective, so the complementary-pair case needs no third
/// rule.
pub(super) fn printed_clause_is_certainly_valid(literals: &[String]) -> bool {
    let mut units: Vec<String> = Vec::new();
    for literal in literals {
        push_disjuncts(literal, &mut units, MAX_DEPTH);
        if units.len() >= MAX_UNITS {
            return false;
        }
    }
    let keys: Vec<String> = units
        .iter()
        .map(|unit| canonical(unit, MAX_DEPTH))
        .collect();
    let present = |term: &str| {
        let key = canonical(term, MAX_DEPTH);
        keys.contains(&key)
    };

    for unit in &units {
        let Some(once) = split_application(unit, "not") else {
            continue;
        };
        let [negated] = once.as_slice() else {
            continue;
        };
        let mut leaves: Vec<String> = Vec::new();
        push_disjuncts(negated, &mut leaves, MAX_DEPTH);
        if leaves.len() >= MAX_UNITS {
            continue;
        }
        if !leaves.is_empty() && leaves.iter().all(|leaf| present(leaf)) {
            return true;
        }
    }

    for unit in &units {
        if split_application(unit, "not").is_some() {
            continue;
        }
        let mut conjuncts: Vec<String> = Vec::new();
        push_conjuncts(unit, &mut conjuncts, MAX_DEPTH);
        if conjuncts.len() >= MAX_UNITS {
            continue;
        }
        if !conjuncts.is_empty()
            && conjuncts
                .iter()
                .all(|conjunct| present(&format!("(not {conjunct})")))
        {
            return true;
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::printed_clause_is_certainly_valid;

    fn clause(literals: &[&str]) -> Vec<String> {
        literals.iter().map(|l| (*l).to_string()).collect()
    }

    /// The `or_pos` gate whose printed arity is SMALLER than the traced tail.
    /// Every printed disjunct of the gate is a clause literal, so the extra
    /// tail literal cannot make the clause false.
    #[test]
    fn a_gate_whose_disjuncts_are_all_present_is_certified() {
        assert!(printed_clause_is_certainly_valid(&clause(&[
            "(not (or a b))",
            "a",
            "b",
            "c"
        ])));
    }

    /// The `or_pos` gate whose printed arity is LARGER than the traced tail —
    /// a disjunct the authored spelling still quotes and the traced clause has
    /// pruned. Set that disjunct true and everything else false: the clause is
    /// FALSE, so no hole may be emitted for it.
    #[test]
    fn a_gate_with_an_unmatched_disjunct_is_refused() {
        assert!(!printed_clause_is_certainly_valid(&clause(&[
            "(not (or a b c))",
            "a",
            "b"
        ])));
    }

    /// The respelling class: the gate's source prints as something with no
    /// relation to the tail at all.
    #[test]
    fn a_gate_respelled_to_an_unrelated_term_is_refused() {
        assert!(!printed_clause_is_certainly_valid(&clause(&[
            "(not (= p q))",
            "a",
            "b"
        ])));
    }

    /// `iso_icl1206`'s `t405`, reduced: the gate's leaf and the traced literal
    /// are the two orientations of ONE equality. `=` is symmetric, so the
    /// clause is valid and the hole is honest.
    #[test]
    fn one_equality_orientation_between_gate_and_tail_is_certified() {
        assert!(printed_clause_is_certainly_valid(&clause(&[
            "(not (or (or a (= y x)) c))",
            "a",
            "(= x y)",
            "c"
        ])));
    }

    /// The mutation differential for the rule above: a leaf that is a
    /// DIFFERENT statement, not the same one written backwards.
    #[test]
    fn a_leaf_that_is_not_an_orientation_flip_is_refused() {
        assert!(!printed_clause_is_certainly_valid(&clause(&[
            "(not (or (or a (= y z)) c))",
            "a",
            "(= x y)",
            "c"
        ])));
    }

    /// The De Morgan `and_pos` gate: the gate literal is the or-form and the
    /// tail is one conjunct, so the clause holds a complementary pair once the
    /// printed `or` is flattened.
    #[test]
    fn a_de_morgan_and_pos_gate_is_certified() {
        assert!(printed_clause_is_certainly_valid(&clause(&[
            "(or (not p) (not qq) (not r))",
            "qq"
        ])));
    }

    /// The same shape with the conjunct that is NOT in the printed gate.
    #[test]
    fn a_de_morgan_gate_missing_its_conjunct_is_refused() {
        assert!(!printed_clause_is_certainly_valid(&clause(&[
            "(or (not p) (not r))",
            "qq"
        ])));
    }

    /// The `(not (and ..))` surface an `or_pos` source can carry: the gate
    /// literal double-negates to the conjunction itself, and every negated
    /// conjunct is a clause literal.
    #[test]
    fn a_doubly_negated_conjunction_gate_is_certified() {
        assert!(printed_clause_is_certainly_valid(&clause(&[
            "(not (not (and a b)))",
            "(not a)",
            "(not b)"
        ])));
    }

    /// `implies_pos` over the printed implication surface.
    #[test]
    fn an_implication_gate_is_certified() {
        assert!(printed_clause_is_certainly_valid(&clause(&[
            "(not (=> a b))",
            "(not a)",
            "b"
        ])));
    }

    /// An implication gate whose consequent is not the traced literal.
    #[test]
    fn an_implication_gate_with_a_foreign_consequent_is_refused() {
        assert!(!printed_clause_is_certainly_valid(&clause(&[
            "(not (=> a b))",
            "(not a)",
            "c"
        ])));
    }

    /// The equality normalisation must not reach across a DIFFERENT head: a
    /// flipped `<=` is not the same atom as its reverse.
    #[test]
    fn a_flipped_order_atom_is_not_treated_as_an_equality_flip() {
        assert!(!printed_clause_is_certainly_valid(&clause(&[
            "(not (or (<= a b)))",
            "(<= b a)"
        ])));
    }

    /// A clause with no gate and no complementary pair certifies nothing.
    #[test]
    fn an_ordinary_unsatisfiable_looking_clause_is_refused() {
        assert!(!printed_clause_is_certainly_valid(&clause(&[
            "a", "b", "c"
        ])));
    }

    /// A DOCUMENTED INCOMPLETENESS, pinned so it is a decision and not a
    /// surprise: the equality normalisation runs at the top of a literal and
    /// under `not`/`=`, not through an arbitrary application head. An equality
    /// flipped inside `(f ..)` is not certified, so the step is DECLINED. That
    /// costs a document and never ships a false claim, which is the direction
    /// this certificate is allowed to be wrong in.
    #[test]
    fn an_equality_flipped_under_a_function_head_is_not_certified() {
        assert!(!printed_clause_is_certainly_valid(&clause(&[
            "(not (or (f (= y x))))",
            "(f (= x y))"
        ])));
    }
}
