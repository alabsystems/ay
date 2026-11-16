// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl Circuit<'_, '_, '_> {
    fn order(&mut self, op: &str, x: &str, y: &str, width: usize) -> Option<Equality> {
        if width == 0 || width > MAX_WIDTH {
            return None;
        }
        if matches!(op, "bvslt" | "bvsle" | "bvsgt" | "bvsge") {
            return self.signed_order(op, x, y, width);
        }
        let a = AlethePrinter::pbblast_value_sum(x, width as u32);
        let b = AlethePrinter::pbblast_value_sum(y, width as u32);
        let a = self.proof.define_term(&a, "Int")?;
        let b = self.proof.define_term(&b, "Int")?;
        let (a, b) = if matches!(op, "bvult" | "bvule") {
            (b, a)
        } else {
            (a, b)
        };
        let threshold = usize::from(matches!(op, "bvult" | "bvugt"));
        self.proof.equality(
            &format!("({op} {x} {y})"),
            &format!("(>= (- {a} {b}) {threshold})"),
            &format!("pbblast_{op}"),
            &[],
        )
    }

    // Carcara's signed PB rules separate the low-bit sum from the negative
    // sign contribution. Keep that exact syntax; the subsequent la_generic
    // steps independently check the strict/non-strict integer duality.
    fn signed_order(&mut self, op: &str, x: &str, y: &str, width: usize) -> Option<Equality> {
        if !(2..=MAX_WIDTH).contains(&width) {
            return None;
        }
        let msb = width - 1;
        let a = AlethePrinter::pbblast_value_sum(x, msb as u32);
        let b = AlethePrinter::pbblast_value_sum(y, msb as u32);
        let a = self.proof.define_term(&a, "Int")?;
        let b = self.proof.define_term(&b, "Int")?;
        let sx = format!("(* {} ((_ @int_of {msb}) {x}))", 1u128 << msb);
        let sy = format!("(* {} ((_ @int_of {msb}) {y}))", 1u128 << msb);
        let (a, sx, b, sy) = if matches!(op, "bvslt" | "bvsle") {
            (b, sy, a, sx)
        } else {
            (a, sx, b, sy)
        };
        let threshold = usize::from(matches!(op, "bvslt" | "bvsgt"));
        self.proof.equality(
            &format!("({op} {x} {y})"),
            &format!("(>= (+ (- {a} {sx}) (- {sy} {b})) {threshold})"),
            &format!("pbblast_{op}"),
            &[],
        )
    }

    pub(super) fn order_duality(
        &mut self,
        op: &str,
        x: &str,
        y: &str,
        width: usize,
    ) -> Option<Equality> {
        let a = self.order(op, x, y, width)?;
        let primitive = if matches!(op, "bvsgt" | "bvsle" | "bvsge") {
            "bvslt"
        } else {
            "bvult"
        };
        let b = if matches!(op, "bvugt" | "bvule" | "bvsgt" | "bvsle") {
            self.order(primitive, y, x, width)?
        } else {
            self.order(primitive, x, y, width)?
        };
        if matches!(op, "bvugt" | "bvsgt") {
            let reverse = self.proof.equality(&b.right, &b.left, "symm", &[&b.step])?;
            return self.proof.chain(a, reverse);
        }
        if !matches!(op, "bvuge" | "bvule" | "bvsge" | "bvsle") {
            return None;
        }
        let lhs = &a.right;
        let rhs = &b.right;
        let eq = format!("(= {lhs} (not {rhs}))");
        let first = self.proof.fresh();
        self.proof.named_step(
            &first,
            &format!("(not {lhs}) (not {rhs})"),
            "la_generic",
            &[],
            " :args (1 1)",
        )?;
        let second = self.proof.fresh();
        self.proof.named_step(
            &second,
            &format!("{lhs} {rhs}"),
            "la_generic",
            &[],
            " :args (1 1)",
        )?;
        let n1 = self.proof.step(
            &format!("{eq} (not {lhs}) (not (not {rhs}))"),
            "equiv_neg1",
            &[],
        )?;
        let n2 = self
            .proof
            .step(&format!("{eq} {lhs} (not {rhs})"), "equiv_neg2", &[])?;
        let r1 = self
            .proof
            .step(&format!("{eq} (not {rhs})"), "resolution", &[&n2, &first])?;
        let r2 = self.proof.step(
            &format!("{eq} (not (not {rhs})) {rhs}"),
            "resolution",
            &[&n1, &second],
        )?;
        let r3 = self.proof.step(
            &format!("{eq} (not (not {rhs}))"),
            "resolution",
            &[&r2, &r1],
        )?;
        let nn = self
            .proof
            .step(&format!("(not (not (not {rhs}))) {rhs}"), "not_not", &[])?;
        let r4 = self
            .proof
            .step(&format!("{eq} {rhs}"), "resolution", &[&r3, &nn])?;
        let done = self.proof.step(&eq, "resolution", &[&r4, &r1])?;
        let middle = Equality {
            left: lhs.clone(),
            right: format!("(not {rhs})"),
            step: done,
        };
        let not_b = self.proof.congruence("not", &[b])?;
        let reverse = self
            .proof
            .equality(&not_b.right, &not_b.left, "symm", &[&not_b.step])?;
        let prefix = self.proof.chain(a, middle)?;
        self.proof.chain(prefix, reverse)
    }
}
