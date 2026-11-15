// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! AY relies on Clean's consumer rule `dialect:expand_zero_extend`
//! (`ay_proof::CleanOnlySpelling::consumer_rule`) through one shape only: a
//! `refl` step `(= ((_ zero_extend k) t) D)` whose right side `D` IS the
//! definition, `(concat Z t)` with `Z` the all-zero word of width `k`
//! (spelled `#b0…0` or `(_ bv0 k)`, one term to either checker), or `t` itself
//! when `k = 0`.
//!
//! A step CROSSES the operator when, after the proof's `define-fun`s are
//! expanded, one side of its equality is a `zero_extend` application and the
//! other is not. Every crossing step must be that identity, except:
//!
//! * a transport step (`TRANSPORT`), whose conclusion its premises fix term
//!   for term;
//! * an `evaluate` step over CLOSED values (`is_closed`): the packed word lane
//!   prints one per assignment of a narrow source's bits, and pinned Carcara
//!   computes `zero_extend` on a value itself, so such a step relies on no
//!   reading of the operator.
//!
//! Anything else (a `cong` from the operator to a `concat`, an identity with a
//! wrong zero width, swapped operands, another operand, the operator on the
//! right, an `evaluate` over a symbolic word) is a defect: either a reliance on
//! more than the rule, or a step the rule does not make true.

use super::dialect::{equality, steps};
use super::document::{Document, Node};

/// One crossing step: its id, and why it is not the identity (`None` when it
/// is).
pub(super) struct Crossing {
    pub(super) id: String,
    pub(super) defect: Option<String>,
}

/// Rules whose conclusion is fixed by their premises term for term (a chain's
/// end points, a swapped equality, the literals left after resolving on
/// syntactically equal pivots), so a crossing there relies on nothing. A rule
/// outside this list that crosses the operator is a defect until it is shown
/// to be one of these: fail closed.
const TRANSPORT: &[&str] = &["trans", "symm", "resolution", "th_resolution"];

/// A `zero_extend` application, read off the document.
enum Extension {
    /// `((_ zero_extend k) operand)`.
    Of { k: usize, operand: u32 },
    /// An application of `zero_extend` with an index that is not one
    /// numeral, or not one operand: never an identity.
    Malformed,
}

/// The `zero_extend` application `id` is, if it is one.
fn zero_extend_of(document: &Document, id: u32) -> Option<Extension> {
    let Node::List(children) = document.node(id) else {
        return None;
    };
    let (&head, operands) = children.split_first()?;
    let (name, indices) = document.indexed_name(head)?;
    if name != "zero_extend" {
        return None;
    }
    let k = match indices.as_slice() {
        [k] => document.atom_text(*k).and_then(|k| k.parse().ok()),
        _ => None,
    };
    Some(match (k, operands) {
        (Some(k), [operand]) => Extension::Of {
            k,
            operand: *operand,
        },
        _ => Extension::Malformed,
    })
}

/// Whether `id` is the all-zero word of width `k`: `#b` and `k` zeros, or
/// `(_ bv0 k)`.
fn is_zero_word(document: &Document, id: u32, k: usize) -> bool {
    if let Some(atom) = document.atom_text(id) {
        return atom
            .strip_prefix("#b")
            .is_some_and(|digits| digits.len() == k && digits.bytes().all(|b| b == b'0'));
    }
    match document.node(id) {
        Node::List(children) => match children.as_slice() {
            [underscore, value, width] => {
                document.is_atom(*underscore, "_")
                    && document.is_atom(*value, "bv0")
                    && document.atom_text(*width).and_then(|w| w.parse().ok()) == Some(k)
            }
            _ => false,
        },
        Node::Atom(_) => false,
    }
}

/// Whether `id` is a closed value pinned Carcara's `evaluate` computes: a
/// Boolean literal, a `#b`/`#x` literal, `(_ bvN w)`, or an `@bbterm` of
/// closed bits. Deliberately narrow: a symbol, or any operator not listed
/// here, is not closed, and an `evaluate` crossing over it stays a defect.
fn is_closed(document: &Document, id: u32) -> bool {
    match document.node(id) {
        Node::Atom(atom) => {
            matches!(atom.as_str(), "true" | "false")
                || atom
                    .strip_prefix("#b")
                    .is_some_and(|d| !d.is_empty() && d.bytes().all(|b| b == b'0' || b == b'1'))
                || atom
                    .strip_prefix("#x")
                    .is_some_and(|d| !d.is_empty() && d.bytes().all(|b| b.is_ascii_hexdigit()))
        }
        Node::List(children) => match children.as_slice() {
            [underscore, value, width] if document.is_atom(*underscore, "_") => {
                let numeral = |text: Option<&str>| {
                    text.is_some_and(|t| !t.is_empty() && t.bytes().all(|b| b.is_ascii_digit()))
                };
                numeral(
                    document
                        .atom_text(*value)
                        .and_then(|v| v.strip_prefix("bv")),
                ) && numeral(document.atom_text(*width))
            }
            _ => {
                document.head(id) == Some("@bbterm")
                    && document
                        .args(id)
                        .iter()
                        .all(|&bit| is_closed(document, bit))
            }
        },
    }
}

/// Why `right` is not the definition of `((_ zero_extend k) t)`.
fn not_the_definition(document: &Document, k: usize, t: u32, right: u32) -> Option<String> {
    if k == 0 {
        return (right != t).then(|| {
            format!(
                "((_ zero_extend 0) {}) is {}, not {}",
                document.show(t),
                document.show(t),
                document.show(right)
            )
        });
    }
    let defined = matches!(
        document.op(right, "concat").as_deref(),
        Some([zero, operand]) if *operand == t && is_zero_word(document, *zero, k)
    );
    (!defined).then(|| {
        format!(
            "the right side {} is not (concat Z {}) with Z the zero word of width {k}",
            document.show(right),
            document.show(t)
        )
    })
}

/// Every step of `proof` that crosses `zero_extend`, with its defect if it is
/// not the identity.
pub(super) fn zero_extend_crossings(proof: &str) -> Vec<Crossing> {
    let mut document = Document::read(proof);
    let mut crossings = Vec::new();
    for step in steps(&mut document) {
        let Some((left, right)) = equality(&step.clause) else {
            continue;
        };
        let (left, right) = (document.expand(left), document.expand(right));
        let (left_extends, right_extends) = (
            zero_extend_of(&document, left),
            zero_extend_of(&document, right),
        );
        if left_extends.is_some() == right_extends.is_some()
            || TRANSPORT.contains(&step.rule.as_str())
        {
            continue;
        }
        let rule = step.rule.as_str();
        let (extension, other) = match (&left_extends, &right_extends) {
            (Some(extension), _) => (extension, right),
            (_, Some(extension)) => (extension, left),
            (None, None) => continue,
        };
        if rule == "evaluate"
            && matches!(extension, Extension::Of { operand, .. } if is_closed(&document, *operand))
            && is_closed(&document, other)
        {
            continue;
        }
        let defect = match (&left_extends, rule) {
            (None, _) => Some(format!(
                "the zero_extend application {} is on the right",
                document.show(right)
            )),
            (Some(Extension::Malformed), _) => Some(format!(
                "{} is not ((_ zero_extend k) t) with one numeral k",
                document.show(left)
            )),
            (Some(Extension::Of { k, operand }), "refl") => {
                not_the_definition(&document, *k, *operand, right)
            }
            (Some(Extension::Of { .. }), _) => Some(format!(
                "crosses zero_extend with rule {rule}, not with the refl identity"
            )),
        };
        crossings.push(Crossing {
            id: step.id.clone(),
            defect: defect.map(|why| format!("step {} ({rule}): {why}", step.id)),
        });
    }
    crossings
}

/// The crossing steps that are not the identity: what AY must never print.
pub(crate) fn zero_extend_identity_defects(proof: &str) -> Vec<String> {
    zero_extend_crossings(proof)
        .into_iter()
        .filter_map(|crossing| crossing.defect)
        .collect()
}

/// The detector refuses what the consumer's reading does not make true, and
/// what relies on more than the rule. Each wrong identity is spelled by hand.
#[test]
fn the_zero_extend_reliance_detector_refuses_what_the_consumer_refused() {
    let identities = "\
(define-fun w () (_ BitVec 6) ((_ zero_extend 2) x))
(define-fun z () (_ BitVec 2) #b00)
(define-fun c () (_ BitVec 4) (@bbterm true false true true))
(step r (cl (= ((_ zero_extend 2) x) (concat (_ bv0 2) x))) :rule refl)
(step b (cl (= ((_ zero_extend 2) x) (concat #b00 x))) :rule refl)
(step n (cl (= w (concat z x))) :rule refl)
(step e (cl (= ((_ zero_extend 0) x) x)) :rule refl)
(step t (cl (= w (@bbterm a b c d false false))) :rule trans :premises (n m))
(step u (cl (= (@bbterm a b c d false false) w)) :rule symm :premises (t))
(step v (cl (= w (@bbterm a b c d false false))) :rule resolution :premises (t q))
(step k (cl (= ((_ zero_extend 2) x) ((_ zero_extend 2) y))) :rule cong)
(step closed (cl (= ((_ zero_extend 2) c) #b001101)) :rule evaluate)
(step literal (cl (= ((_ zero_extend 4) #x5) (_ bv5 8))) :rule evaluate)
";
    assert_eq!(
        zero_extend_identity_defects(identities),
        Vec::<String>::new()
    );
    let crossing: Vec<String> = zero_extend_crossings(identities)
        .into_iter()
        .map(|c| c.id)
        .collect();
    assert_eq!(crossing, ["r", "b", "n", "e"]);

    for (wrong, why) in [
        (
            "(step s (cl (= ((_ zero_extend 2) x) (concat (_ bv0 3) x))) :rule refl)",
            "not (concat Z",
        ),
        (
            "(step s (cl (= ((_ zero_extend 2) x) (concat #b0 x))) :rule refl)",
            "not (concat Z",
        ),
        (
            "(step s (cl (= ((_ zero_extend 2) x) (concat x (_ bv0 2)))) :rule refl)",
            "not (concat Z",
        ),
        (
            "(step s (cl (= ((_ zero_extend 2) x) (concat (_ bv0 2) y))) :rule refl)",
            "not (concat Z",
        ),
        (
            "(step s (cl (= ((_ zero_extend 2) x) (concat #b01 x))) :rule refl)",
            "not (concat Z",
        ),
        (
            "(step s (cl (= ((_ zero_extend 2) x) ((_ sign_extend 2) x))) :rule refl)",
            "not (concat Z",
        ),
        (
            "(step s (cl (= ((_ zero_extend 0) x) (concat #b0 x))) :rule refl)",
            "zero_extend 0",
        ),
        (
            "(step s (cl (= (concat (_ bv0 2) x) ((_ zero_extend 2) x))) :rule refl)",
            "is on the right",
        ),
        (
            "(step s (cl (= ((_ zero_extend k) x) (concat (_ bv0 2) x))) :rule refl)",
            "one numeral k",
        ),
        (
            "(define-fun w () (_ BitVec 6) ((_ zero_extend 2) x))\n\
             (step s (cl (= w (concat (@bbterm false false) x))) :rule cong :premises (p q))",
            "with rule cong",
        ),
        (
            "(step s (cl (= ((_ zero_extend 2) x) (concat (_ bv0 2) x))) :rule all_simplify)",
            "with rule all_simplify",
        ),
        // `evaluate` decides closed values only: over a symbol, or a closed
        // operand equated with a symbolic side, it is a crossing like any other.
        (
            "(step s (cl (= ((_ zero_extend 2) x) #b001101)) :rule evaluate)",
            "with rule evaluate",
        ),
        (
            "(step s (cl (= ((_ zero_extend 2) (@bbterm true x)) #b0011)) :rule evaluate)",
            "with rule evaluate",
        ),
        (
            "(step s (cl (= ((_ zero_extend 2) #b11) (concat #b00 x))) :rule evaluate)",
            "with rule evaluate",
        ),
    ] {
        let defects = zero_extend_identity_defects(wrong);
        assert!(
            matches!(defects.as_slice(), [one] if one.starts_with("step s ") && one.contains(why)),
            "{wrong}: {defects:?}"
        );
    }
}
