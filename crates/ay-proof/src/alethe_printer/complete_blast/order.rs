// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The derived order predicates `bvugt`, `bvuge`, `bvule`, `bvsgt`, `bvsge`
//! and `bvsle` in the complete blast.
//!
//! The pinned checker bit-blasts only `bvult` (`bitblast_ult`) and `bvslt`
//! (`bitblast_slt`): no `bitblast_*` conclusion carries a derived comparison.
//! Its pseudo-Boolean family has a rule for every one of them, which is how
//! the unsigned-duality lowering and the packed circuit's `order_duality`
//! already relate a derived comparison to its primitive. Here the relation
//! reaches the SAT layer as clauses, each derived by a rule the consumer
//! re-checks from the printed text:
//!
//! * `pbblast_{op}` proves `(= (op x y) A)` and `pbblast_{prim}` proves
//!   `(= (prim x' y') B)`, where `(prim x' y')` is the primitive the identity
//!   names (`(bvsgt x y)` is `(bvslt y x)`, `(bvsge x y)` is
//!   `(not (bvslt x y))`) and `A`, `B` are the rules' own integer constraints
//!   over the operands' value sums. Each sum is a proof-local `Int`
//!   definition, as the packed circuit names them, so both constraints read
//!   the same few names and the printer's own `la_generic` judgement decides
//!   them over those names. `equiv1`/`equiv2` split each equality into the two
//!   clauses the SAT layer reads.
//! * For a strict comparison the two constraints are the same text — both
//!   rules take the same difference at the same threshold — so they are one
//!   atom. For a non-strict one, `A` is `D >= 0` and `B` is `-D >= 1` for the
//!   same difference `D`, and `la_generic` proves both halves of `A <-> ~B`:
//!   `(cl (not A) (not B))` and `(cl A B)` (Farkas coefficients `1 1`, with
//!   integer strengthening for the second).
//! * The primitive atom is bit-blasted by [`Blaster::theory_atom`] exactly as a
//!   source `bvult`/`bvslt` is.
//!
//! Nothing is assumed: a wrong threshold, operand order or identity makes a
//! `pbblast_*` or `la_generic` step fail at the consumer, and the refutation
//! over these clauses must still exist before anything is printed.

use super::*;

/// The primitive a derived comparison is decided through: its predicate,
/// whether the identity swaps the operands, and whether it negates the
/// primitive (the non-strict comparisons).
fn primitive_of(op: &str) -> Option<(&'static str, AtomKind, bool, bool)> {
    Some(match op {
        "bvugt" => ("bvult", AtomKind::UnsignedLessThan, true, false),
        "bvuge" => ("bvult", AtomKind::UnsignedLessThan, false, true),
        "bvule" => ("bvult", AtomKind::UnsignedLessThan, true, true),
        "bvsgt" => ("bvslt", AtomKind::SignedLessThan, true, false),
        "bvsge" => ("bvslt", AtomKind::SignedLessThan, false, true),
        "bvsle" => ("bvslt", AtomKind::SignedLessThan, true, true),
        _ => return None,
    })
}

/// The value sums of one operand, each a proof-local `Int` name: the whole
/// word for an unsigned comparison, the low bits and the weighted sign bit for
/// a signed one (the split the pseudo-Boolean rules read).
enum Sums {
    Unsigned(String),
    Signed { low: String, sign: String },
}

/// The integer constraint `pbblast_{op}` equates `(op a b)` with, spelled as
/// the packed circuit's `order`/`signed_order` spell it: the difference of the
/// two values (the second operand's minus the first's for `lt`/`le`) at
/// threshold 1 for a strict comparison and 0 otherwise.
fn constraint(op: &str, a: &Sums, b: &Sums) -> Option<String> {
    let threshold = u8::from(matches!(op, "bvult" | "bvugt" | "bvslt" | "bvsgt"));
    let (first, second) = if matches!(op, "bvult" | "bvule" | "bvslt" | "bvsle") {
        (b, a)
    } else {
        (a, b)
    };
    Some(match (first, second) {
        (Sums::Unsigned(first), Sums::Unsigned(second)) => {
            format!("(>= (- {first} {second}) {threshold})")
        }
        (
            Sums::Signed {
                low: first_low,
                sign: first_sign,
            },
            Sums::Signed {
                low: second_low,
                sign: second_sign,
            },
        ) => format!(
            "(>= (+ (- {first_low} {first_sign}) (- {second_sign} {second_low})) {threshold})"
        ),
        _ => return None,
    })
}

impl Blaster<'_, '_> {
    /// The Boolean reference of `(op left right)` for a derived comparison
    /// `op`, with the clauses that tie it to its bit-blasted primitive; see
    /// the module docs. `None` for any other operator or an unsupported width.
    pub(super) fn derived_order_atom(
        &mut self,
        op: &str,
        left: usize,
        right: usize,
    ) -> Option<SRef> {
        let (primitive, kind, swapped, negated) = primitive_of(op)?;
        let width = self.words[left].width;
        let signed = matches!(kind, AtomKind::SignedLessThan);
        if self.words[right].width != width || width > MAX_WIDTH || width < 1 + u32::from(signed) {
            return None;
        }
        let primitive_atom = if swapped {
            self.theory_atom(right, left, kind)?
        } else {
            self.theory_atom(left, right, kind)?
        };
        let x = self.value_sums(left, signed)?;
        let y = self.value_sums(right, signed)?;
        let derived_constraint = constraint(op, &x, &y)?;
        let primitive_constraint = if swapped {
            constraint(primitive, &y, &x)?
        } else {
            constraint(primitive, &x, &y)?
        };
        if !negated && derived_constraint != primitive_constraint {
            return None;
        }
        let derived = self.circuit.theory(format!(
            "({op} {} {})",
            self.word_ref(left),
            self.word_ref(right)
        ));
        let a = self.circuit.atom(derived_constraint);
        let b = self.circuit.atom(primitive_constraint);
        self.equate(derived, a, op)?;
        self.equate(primitive_atom, b, primitive)?;
        if negated {
            self.la_clause(vec![a.not()?, b.not()?])?;
            self.la_clause(vec![a, b])?;
        }
        Some(derived)
    }

    /// Name the value sums of one word as `Int` definitions.
    fn value_sums(&mut self, word: usize, signed: bool) -> Option<Sums> {
        let reference = self.word_ref(word);
        let width = self.words[word].width;
        if !signed {
            let sum = AlethePrinter::pbblast_value_sum(&reference, width);
            return Some(Sums::Unsigned(self.bind_int_reference(&sum)?));
        }
        let msb = width - 1;
        let low = AlethePrinter::pbblast_value_sum(&reference, msb);
        Some(Sums::Signed {
            low: self.bind_int_reference(&low)?,
            sign: format!(
                "(* {} ((_ @int_of {msb}) {reference}))",
                num_bigint::BigInt::from(1u8) << msb
            ),
        })
    }

    /// A proof-local `Int` name for `body`, defined after every gate interned
    /// so far so the definition list stays topologically sorted.
    fn bind_int_reference(&mut self, body: &str) -> Option<String> {
        self.flush_gate_definitions()?;
        let name = format!("{}n{}", self.prefix, self.next_id);
        self.next_id += 1;
        let definition = format!("(define-fun {name} () Int {body})\n");
        self.charge(definition.len())?;
        self.definitions.push_str(&definition);
        Some(name)
    }

    /// `pbblast_{op}` proves `(= atom constraint)`; plan its two halves.
    fn equate(&mut self, atom: SRef, constraint: SRef, op: &str) -> Option<()> {
        let rule = format!("pbblast_{op}");
        if !ay_core::is_checkable_alethe_rule(&rule) {
            return None;
        }
        let equality = self.step_name(".oq");
        self.push_step(&format!(
            "(step {equality} (cl (= {} {})) :rule {rule})",
            self.circuit.text(atom),
            self.circuit.text(constraint)
        ))?;
        // The two halves spell their rule names literally, so the wire-rule
        // inventory sees (and probes the pinned checker for) exactly what is
        // printed.
        let forward = vec![atom.not()?, constraint];
        let step = self.step_name(".os");
        self.push_step(&format!(
            "(step {step} {} :rule equiv1 :premises ({equality}))",
            self.clause_text(&forward)
        ))?;
        self.plan(forward, ClauseEmit::Existing(step))?;
        let backward = vec![atom, constraint.not()?];
        let step = self.step_name(".os");
        self.push_step(&format!(
            "(step {step} {} :rule equiv2 :premises ({equality}))",
            self.clause_text(&backward)
        ))?;
        self.plan(backward, ClauseEmit::Existing(step))?;
        Some(())
    }

    /// One `la_generic` clause over two constraints, Farkas coefficients `1 1`.
    fn la_clause(&mut self, lits: Vec<SRef>) -> Option<()> {
        let step = self.step_name(".ol");
        self.push_step(&format!(
            "(step {step} {} :rule la_generic :args (1 1))",
            self.clause_text(&lits)
        ))?;
        self.plan(lits, ClauseEmit::Existing(step))
    }
}

#[cfg(test)]
#[path = "order_tests.rs"]
mod tests;
