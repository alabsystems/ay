// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An authored clause whose disjunctive connectives elaboration flattened
//! into one canonical `or` (#screened-surface-gaps).
//!
//! Elaboration rewrites every disjunctive connective of a formula into one
//! flat disjunction of literals: `(not (and g (not E)))` becomes
//! `(or E' (not g'))`, `(=> G (or C R))` becomes `(or C' R' (not G'))`,
//! `(=> G (not (and P Q)))` becomes `(or (not P') (not Q') (not G'))`, and a
//! literal the authored text repeats is kept once. An authored universal keeps
//! its own spelling inside `forall_inst`, so without a derived equality the
//! confined-instance pass declines and the `or` that clausifies the instance
//! prints the authored text against a canonical clause and is holed. MEASURED
//! at 938ec0327: each of those bodies published `unsat` with one `hole` there.
//! The same equality serves the authored-`assume` bridge
//! (`authored_assume/document_canonical.rs`) and the quantified `and_pos`
//! projection under `bind` (`surface_and_pos/quantified_body.rs`).
//!
//! The authored text unfolds through `(or a1 .. an)` (literals `ai`),
//! `(=> a b)` (literals `(not a)` and `b`), `(not (and c1 .. cn))` (literals
//! `(not ci)`) and `(not (not x))` (literal `x`) down to its leaf literals.
//! Every leaf is paired with a canonical disjunct (exact text first, else a
//! derived equality; a repeated leaf may share one) and every disjunct must be
//! claimed; a clause the consumers of the authored term already print is left
//! to them ([`consumers_print`]). The equality is then the propositional
//! two-way implication, each direction one `resolution` over stock
//! pinned-carcara tautologies:
//!
//! ```text
//! (cl (not S) O):  or_pos / implies_pos / and_neg per connective,
//!                  or_neg per disjunct, equiv_pos2 per re-spelled leaf
//! (cl S (not O)):  or_neg / implies_neg1+2 / and_pos per connective child,
//!                  or_pos over the disjuncts, equiv_pos1 per re-spelled leaf
//! (cl (= S O)):    equiv_neg1, equiv_neg2 and three resolutions
//! ```
//!
//! A double negation needs no step: pinned carcara's `resolution`
//! (`checker/rules/resolution.rs`) matches a pivot with `n` leading negations
//! against `n - 1` or `n + 1`, and its RUP fallback compares literals modulo
//! their negation parity, so `(not (not x))` is the literal `x` there. Each
//! direction is unit propagation from the negated conclusion over these
//! clauses, which that fallback decides. Any other shape declines.

use super::super::*;
use super::{CanonicalNode, Derivation, SchemaTier, MAX_PRINTED_EQUIVALENCE_NODES};

/// Cap on the connectives plus leaves one authored clause unfolds to.
const MAX_UNFOLDED_LITERALS: usize = 128;
/// Cap on the connective nesting one authored clause unfolds through.
const MAX_UNFOLD_DEPTH: usize = 32;

/// One disjunctive connective of the authored text.
enum Connective {
    /// `(or a1 .. an)`, with the printed `ai`.
    Or { text: String, operands: Vec<String> },
    /// `(=> a b)`.
    Implies {
        text: String,
        antecedent: String,
        consequent: String,
    },
    /// `(not (and c1 .. cn))`, with the printed `(and ..)` and `ci`.
    NegatedAnd {
        text: String,
        conjunction: String,
        conjuncts: Vec<String>,
    },
    /// `(not (not x))`: no step (see the module comment).
    DoubleNegation,
}

/// The authored clause: its connectives, outermost first, and its leaves.
struct UnfoldedClause {
    connectives: Vec<Connective>,
    leaves: Vec<String>,
}

/// One leaf and the canonical disjunct it becomes.
struct PairedLeaf {
    leaf: usize,
    disjunct: usize,
    /// The step concluding `(= leaf disjunct)`, when the texts differ.
    equality: Option<String>,
}

/// The connective `literal` is, with the literals it unfolds to, or `None`
/// for a leaf.
fn unfold_connective(literal: &str) -> Option<(Connective, Vec<String>)> {
    if let Some(operands) = split_application(literal, "or").filter(|parts| parts.len() >= 2) {
        let children = operands.clone();
        let text = literal.to_string();
        return Some((Connective::Or { text, operands }, children));
    }
    if let Some(parts) = split_application(literal, "=>") {
        let [antecedent, consequent] = <[String; 2]>::try_from(parts).ok()?;
        let children = vec![format!("(not {antecedent})"), consequent.clone()];
        let text = literal.to_string();
        let connective = Connective::Implies {
            text,
            antecedent,
            consequent,
        };
        return Some((connective, children));
    }
    let [operand] = <[String; 1]>::try_from(split_application(literal, "not")?).ok()?;
    if let Some(conjuncts) = split_application(&operand, "and").filter(|parts| parts.len() >= 2) {
        let children = conjuncts.iter().map(|c| format!("(not {c})")).collect();
        let connective = Connective::NegatedAnd {
            text: literal.to_string(),
            conjunction: operand,
            conjuncts,
        };
        return Some((connective, children));
    }
    let [core] = <[String; 1]>::try_from(split_application(&operand, "not")?).ok()?;
    Some((Connective::DoubleNegation, vec![core]))
}

/// `surface` unfolded to its leaves in left-to-right order, or `None` when it
/// is no connective or exceeds the caps.
fn unfold_authored_clause(surface: &str) -> Option<UnfoldedClause> {
    let mut clause = UnfoldedClause {
        connectives: Vec::new(),
        leaves: Vec::new(),
    };
    let mut pending: Vec<(String, usize)> = vec![(surface.to_string(), 0)];
    let mut visited = 0usize;
    while let Some((literal, depth)) = pending.pop() {
        visited += 1;
        if visited > MAX_UNFOLDED_LITERALS || depth > MAX_UNFOLD_DEPTH {
            return None;
        }
        match unfold_connective(&literal) {
            Some((connective, children)) => {
                clause.connectives.push(connective);
                pending.extend(children.into_iter().rev().map(|child| (child, depth + 1)));
            }
            None => clause.leaves.push(literal),
        }
    }
    (!clause.connectives.is_empty()).then_some(clause)
}

impl AlethePrinter<'_> {
    /// `(= surface canonical)` for an authored clause whose leaves are the
    /// canonical `or`'s disjuncts, or `false` with `derivation` unchanged
    /// (always, on a first attempt).
    pub(super) fn flattened_clause_equivalence(
        &self,
        id: &str,
        surface: &str,
        canonical: CanonicalNode<'_>,
        depth: usize,
        derivation: &mut Derivation,
    ) -> bool {
        if derivation.tier != SchemaTier::Extended {
            return false;
        }
        let Some(disjuncts) = self.canonical_printed_children(canonical, "or") else {
            return false;
        };
        let Some(clause) = unfold_authored_clause(surface) else {
            return false;
        };
        let unfolded = clause.connectives.len() + clause.leaves.len();
        if derivation.nodes.saturating_add(unfolded) > MAX_PRINTED_EQUIVALENCE_NODES {
            return false;
        }
        derivation.nodes += unfolded;
        let checkpoint = derivation.steps.len();
        let derived = self
            .pair_flattened_leaves(id, &clause.leaves, &disjuncts, depth, derivation)
            .is_some_and(|paired| {
                let texts: Vec<&str> = disjuncts.iter().map(|(_, text)| text.as_str()).collect();
                if consumers_print(&clause, &paired, &texts) {
                    return false;
                }
                let shape = FlattenedClause {
                    surface,
                    disjunction: canonical.text,
                    clause: &clause,
                    disjuncts: &texts,
                    paired: &paired,
                };
                emit_flattened_clause_equivalence(id, shape, derivation)
            });
        if !derived {
            derivation.steps.truncate(checkpoint);
        }
        derived
    }

    /// Each leaf's disjunct: exact text, then a derived equality, first onto
    /// an unclaimed disjunct and then onto a claimed one (elaboration keeps a
    /// repeated literal once). `None` unless every disjunct is claimed.
    fn pair_flattened_leaves(
        &self,
        id: &str,
        leaves: &[String],
        disjuncts: &[(TermId, String)],
        depth: usize,
        derivation: &mut Derivation,
    ) -> Option<Vec<PairedLeaf>> {
        let mut claimed = vec![false; disjuncts.len()];
        let mut paired: Vec<Option<PairedLeaf>> = leaves.iter().map(|_| None).collect();
        for shared in [false, true] {
            for derived in [false, true] {
                for (leaf, literal) in leaves.iter().enumerate() {
                    if paired[leaf].is_some() {
                        continue;
                    }
                    let leg = format!("{id}.uq{leaf}");
                    let found = (0..disjuncts.len()).find(|&j| {
                        if claimed[j] != shared {
                            return false;
                        }
                        if !derived {
                            return disjuncts[j].1 == *literal;
                        }
                        let checkpoint = derivation.steps.len();
                        let node = CanonicalNode {
                            term: disjuncts[j].0,
                            text: &disjuncts[j].1,
                        };
                        let related = self.derive_printed_equivalence(
                            &leg,
                            literal,
                            node,
                            depth + 1,
                            derivation,
                        );
                        if !related {
                            derivation.steps.truncate(checkpoint);
                        }
                        related
                    });
                    if let Some(disjunct) = found {
                        claimed[disjunct] = true;
                        paired[leaf] = Some(PairedLeaf {
                            leaf,
                            disjunct,
                            equality: derived.then_some(leg),
                        });
                    }
                }
            }
        }
        if claimed.contains(&false) {
            return None;
        }
        paired.into_iter().collect()
    }
}

/// A clause the consumers of the authored term already print, so deriving it
/// would only re-spell a document that already checks: one kind of
/// connective throughout (a regrouped or reordered disjunction, a flat or
/// nested negated conjunction, a right-nested implication), with one leaf per
/// disjunct that is the disjunct's own text or that text with one equality's
/// operands swapped. MEASURED at 938ec0327: `bool_logic.smt2` from
/// `fuzz/seeds/smtlib_parser` (`(or (not p) q)` against `(or q (not p))`), a
/// universal over `(or (q x) (or (r x) (p x)))`, a ground
/// `(not (and (= b (f a)) (= c (f b))))`, and a ground and a quantified
/// `(not (and (and A B) C))` all published carcara-valid documents with no
/// bridge. The `or_pos` De Morgan repair (`or_pos_de_morgan_surface.rs`) and
/// the `implies_pos` chain of an `or` decomposition over `(=> a (=> b c))`
/// (`lib_tests.rs`, which also pins that a forged decomposition fails loudly)
/// are pinned. That chain has no `or_pos` twin: a ground `(=> a (=> b c))` a
/// Tseitin `or_pos` consumes is still holed, and stays so here rather than
/// route around the pinned repair. Mixed connectives, a double negation, a
/// repeated literal or another re-spelling are printed by no consumer:
/// `(not (and g (not E)))`, `(=> x (or y z))` and the six authored disjuncts
/// of `evals/repros/interpolation_spike/mini_check_i_and_b.smt2` against
/// their four canonical ones each published a `hole`.
fn consumers_print(clause: &UnfoldedClause, paired: &[PairedLeaf], disjuncts: &[&str]) -> bool {
    let Some(first) = clause.connectives.first() else {
        return false;
    };
    let kind = std::mem::discriminant(first);
    !matches!(first, Connective::DoubleNegation)
        && clause
            .connectives
            .iter()
            .all(|connective| std::mem::discriminant(connective) == kind)
        && paired.len() == disjuncts.len()
        && paired.iter().all(|pair| {
            let (leaf, disjunct) = (&clause.leaves[pair.leaf], disjuncts[pair.disjunct]);
            pair.equality.is_none() || is_equality_reversal(leaf, disjunct)
        })
}

/// `leaf` is `disjunct` with one equality's operands swapped, under the same
/// number (at most one) of negations.
fn is_equality_reversal(leaf: &str, disjunct: &str) -> bool {
    let negated = |text: &str| {
        split_application(text, "not").and_then(|parts| <[String; 1]>::try_from(parts).ok())
    };
    let (leaf, disjunct) = match (negated(leaf), negated(disjunct)) {
        (Some([leaf]), Some([disjunct])) => (leaf, disjunct),
        (None, None) => (leaf.to_string(), disjunct.to_string()),
        _ => return false,
    };
    printed_equality_flip(&leaf).is_some_and(|flipped| flipped == disjunct)
}

mod emission;
use emission::{emit_flattened_clause_equivalence, FlattenedClause};

#[cfg(test)]
mod tests;
