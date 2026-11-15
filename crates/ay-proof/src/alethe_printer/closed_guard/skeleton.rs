// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The Boolean skeleton of a printed clause, and the clauses that state it.
//!
//! Every formula is read off the PRINTED text. A node is interned by its
//! CARCARA identity: bit-vector literals are compared by value and width
//! (`#x07` and `#b00000111` are one lexer token in the pinned checker), and
//! whitespace is normalized. Nothing else is identified, so two spellings the
//! checker would parse differently are never merged.

use super::{
    parse_printed_bitvec_literal, split_application, split_smt_term_slices_bounded, HashMap,
    MAX_CLAUSE_BYTES, MAX_DEPTH, MAX_NODES,
};

/// A skeleton node: never a negation (`not` shells live in [`Lit::nots`]).
pub(super) type NodeId = usize;

/// A printed literal: `nots` leading `not` shells around one node.
///
/// Pinned carcara resolves `t` with `(not t)` and `(not t)` with
/// `(not (not t))` — the shell counts must differ by exactly one — so the
/// count is kept exact instead of being folded into a polarity.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) struct Lit {
    pub(super) node: NodeId,
    pub(super) nots: u8,
}

/// Deepest shell count a printed literal may carry (rules add one more).
const MAX_PRINTED_NOTS: u8 = 2;
/// Deepest shell count any emitted clause may carry.
const MAX_EMITTED_NOTS: u8 = 3;

impl Lit {
    /// The same node under one more `not`.
    pub(super) fn negated(self) -> Option<Self> {
        let nots = self.nots.checked_add(1)?;
        (nots <= MAX_EMITTED_NOTS).then_some(Self {
            node: self.node,
            nots,
        })
    }

    /// The value the literal takes when its node has `value`.
    pub(super) fn holds_when(self, value: bool) -> bool {
        value != (self.nots % 2 == 1)
    }
}

/// The Boolean connective a node stands for.
pub(super) enum Kind {
    /// Opaque, or decided by `atoms`.
    Atom,
    And(Vec<Lit>),
    Or(Vec<Lit>),
    Implies(Lit, Lit),
}

pub(super) struct Node {
    /// The first printed spelling seen; every emitted step reuses it.
    pub(super) text: String,
    pub(super) kind: Kind,
}

/// Where a clause of the propagation set comes from.
pub(super) enum Origin {
    /// A premise-free tautology rule whose conclusion is exactly the clause,
    /// with the operand index `and_pos` and `or_neg` take as `:args`.
    Tautology(&'static str, Option<usize>),
    /// `(cl (not E) F)` (`forward`) or `(cl E (not F))`, where `F` is `E`
    /// with its equality operands swapped: `eq_symmetric` then `equiv1`/`equiv2`.
    Symmetry {
        equality: NodeId,
        flipped: NodeId,
        forward: bool,
    },
    /// The unit clause of a decided closed atom.
    Decided(NodeId),
}

pub(super) struct Clause {
    pub(super) lits: Vec<Lit>,
    pub(super) origin: Origin,
}

#[derive(Default)]
pub(super) struct Skeleton {
    pub(super) nodes: Vec<Node>,
    index: HashMap<String, NodeId>,
}

impl Skeleton {
    /// The literal a printed formula denotes.
    pub(super) fn literal(&mut self, text: &str, depth: usize) -> Option<Lit> {
        let mut current = text.trim().to_string();
        let mut nots = 0u8;
        while let Some(inner) = split_application(&current, "not") {
            let [inner]: [String; 1] = inner.try_into().ok()?;
            nots = nots.checked_add(1)?;
            if nots > MAX_PRINTED_NOTS {
                return None;
            }
            current = inner;
        }
        let node = self.node(&current, depth)?;
        Some(Lit { node, nots })
    }

    fn node(&mut self, text: &str, depth: usize) -> Option<NodeId> {
        if depth > MAX_DEPTH || text.len() > MAX_CLAUSE_BYTES {
            return None;
        }
        let key = carcara_key(text, 0)?;
        if let Some(&id) = self.index.get(&key) {
            return Some(id);
        }
        let kind = self.connective(text, depth)?;
        if self.nodes.len() >= MAX_NODES {
            return None;
        }
        let id = self.nodes.len();
        self.nodes.push(Node {
            text: text.to_string(),
            kind,
        });
        self.index.insert(key, id);
        Some(id)
    }

    fn connective(&mut self, text: &str, depth: usize) -> Option<Kind> {
        for head in ["and", "or"] {
            if let Some(args) = split_application(text, head) {
                if args.len() < 2 {
                    return Some(Kind::Atom);
                }
                let lits = args
                    .iter()
                    .map(|arg| self.literal(arg, depth + 1))
                    .collect::<Option<Vec<_>>>()?;
                return Some(if head == "and" {
                    Kind::And(lits)
                } else {
                    Kind::Or(lits)
                });
            }
        }
        if let Some(args) = split_application(text, "=>") {
            // A right-associative chain is not the binary shape the
            // `implies_*` rules state; it stays opaque.
            let [antecedent, consequent]: [String; 2] = match args.try_into() {
                Ok(pair) => pair,
                Err(_) => return Some(Kind::Atom),
            };
            let antecedent = self.literal(&antecedent, depth + 1)?;
            let consequent = self.literal(&consequent, depth + 1)?;
            return Some(Kind::Implies(antecedent, consequent));
        }
        Some(Kind::Atom)
    }

    /// The node whose carcara identity is `text`, if the skeleton has one.
    pub(super) fn find(&self, text: &str) -> Option<NodeId> {
        self.index.get(&carcara_key(text, 0)?).copied()
    }

    /// The literal spelled with its exact `not` shells.
    pub(super) fn text(&self, lit: Lit) -> String {
        let mut out = String::new();
        for _ in 0..lit.nots {
            out.push_str("(not ");
        }
        out.push_str(&self.nodes[lit.node].text);
        for _ in 0..lit.nots {
            out.push(')');
        }
        out
    }

    /// The Tseitin clauses of every connective node and the symmetry clauses
    /// of every equality printed in both orientations, in rule order.
    pub(super) fn structural_clauses(&self) -> Option<Vec<Clause>> {
        let mut clauses = Vec::new();
        for (id, node) in self.nodes.iter().enumerate() {
            let gate = Lit { node: id, nots: 0 };
            let not_gate = gate.negated()?;
            match &node.kind {
                Kind::And(args) => {
                    for (index, arg) in args.iter().enumerate() {
                        let lits = vec![not_gate, *arg];
                        clauses.push(tautology("and_pos", Some(index), lits));
                    }
                    let mut lits = vec![gate];
                    for arg in args {
                        lits.push(arg.negated()?);
                    }
                    clauses.push(tautology("and_neg", None, lits));
                }
                Kind::Or(args) => {
                    let mut lits = vec![not_gate];
                    lits.extend(args.iter().copied());
                    clauses.push(tautology("or_pos", None, lits));
                    for (index, arg) in args.iter().enumerate() {
                        let lits = vec![gate, arg.negated()?];
                        clauses.push(tautology("or_neg", Some(index), lits));
                    }
                }
                Kind::Implies(antecedent, consequent) => {
                    let lits = vec![not_gate, antecedent.negated()?, *consequent];
                    clauses.push(tautology("implies_pos", None, lits));
                    let lits = vec![gate, *antecedent];
                    clauses.push(tautology("implies_neg1", None, lits));
                    let lits = vec![gate, consequent.negated()?];
                    clauses.push(tautology("implies_neg2", None, lits));
                }
                Kind::Atom => self.symmetry_clauses(id, &mut clauses)?,
            }
        }
        Some(clauses)
    }

    fn symmetry_clauses(&self, id: NodeId, clauses: &mut Vec<Clause>) -> Option<()> {
        let Some(operands) = split_application(&self.nodes[id].text, "=") else {
            return Some(());
        };
        let [left, right]: [String; 2] = match operands.try_into() {
            Ok(pair) => pair,
            Err(_) => return Some(()),
        };
        let Some(flipped) = self.find(&format!("(= {right} {left})")) else {
            return Some(());
        };
        // One pair per unordered couple; a self-symmetric `(= t t)` needs none.
        if flipped <= id {
            return Some(());
        }
        let equality = Lit { node: id, nots: 0 };
        let other = Lit {
            node: flipped,
            nots: 0,
        };
        for forward in [true, false] {
            let lits = if forward {
                vec![equality.negated()?, other]
            } else {
                vec![equality, other.negated()?]
            };
            clauses.push(Clause {
                lits,
                origin: Origin::Symmetry {
                    equality: id,
                    flipped,
                    forward,
                },
            });
        }
        Some(())
    }
}

fn tautology(rule: &'static str, index: Option<usize>, lits: Vec<Lit>) -> Clause {
    Clause {
        lits,
        origin: Origin::Tautology(rule, index),
    }
}

/// The pinned checker's identity for a printed term: whitespace-normalized,
/// with every bit-vector literal spelled `#b` at its exact width.
pub(super) fn carcara_key(text: &str, depth: usize) -> Option<String> {
    if depth > 2 * MAX_DEPTH + 64 {
        return None;
    }
    let text = text.trim();
    if let Some((value, width)) = parse_printed_bitvec_literal(text) {
        let digits = value.to_str_radix(2);
        let width = usize::try_from(width).ok()?;
        if digits.len() > width {
            return None;
        }
        return Some(format!("#b{}{digits}", "0".repeat(width - digits.len())));
    }
    let Some(inner) = text.strip_prefix('(').and_then(|t| t.strip_suffix(')')) else {
        return Some(text.to_string());
    };
    let parts = split_smt_term_slices_bounded(inner, MAX_NODES * 64, MAX_CLAUSE_BYTES).ok()?;
    let mut out = String::from("(");
    for (index, part) in parts.iter().enumerate() {
        if index > 0 {
            out.push(' ');
        }
        out.push_str(&carcara_key(part, depth + 1)?);
    }
    out.push(')');
    Some(out)
}
