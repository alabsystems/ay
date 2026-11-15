// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Which pairings of a congruence's PRINTED argument list with its INTERNAL
//! one the bridge is allowed to consider, and in what order.

use super::*;

#[cfg(test)]
#[path = "readings/operand_order_tests.rs"]
mod operand_order_tests;
#[cfg(test)]
#[path = "readings/premise_order_tests.rs"]
mod premise_order_tests;

impl AlethePrinter<'_> {
    /// Every pairing of the PRINTED argument list with the internal one that
    /// this step could mean, most conservative first.
    ///
    /// The first reading is always the stored order — position `k` of the
    /// printed application against position `k` of the term DAG — which is
    /// what this decoder returned before there was a list, so a step that
    /// renders today renders byte-identically.
    ///
    /// A second reading is added when a whole-application surface override
    /// PERMUTES the printed operands. `split_application` reads the argument
    /// order off the printed text, and an override supplies the AUTHOR's
    /// spelling; for an operator whose internal form is order-normalized that
    /// is not the stored order. Measured on
    /// `benchmarks/smt/QF_ABV/csplit_repro_100selects_unsat.smt2`, whose
    /// `(assert (not (= (select arr2 idx) val1)))` interns as
    /// `(= val1 (select arr2 idx))` once ROW1 identifies the two: step `t6`
    /// printed `(= (select arr2 idx) val1)` over internal args
    /// `[val1, (select arr2 idx)]`, the stored reading paired the printed
    /// `(select arr2 idx)` with the internal `val1`, that position looked
    /// internally REFLEXIVE between two unrelated spellings, the narrow
    /// multiplication repair correctly declined — and, the exporter correctly
    /// refusing a `:rule trust` fallback (#8821), the query published `unsat`
    /// with NO Alethe document at all, though its own premise `t5` proves
    /// exactly `(= (select arr2 idx) val1)`.
    ///
    /// WHY BOTH READINGS, AND WHY IN THIS ORDER. Neither is right on its own,
    /// because a printed operand list that is a permutation of the rendered
    /// internal one is genuinely AMBIGUOUS: the override may have commuted the
    /// operands, or equality substitution may have re-spelled one operand as
    /// the other. `implied_equality_inside_a_congruence` is the second shape —
    /// `(= _4 |k#s1_0|)` printed as the authored `(= |k#s1_0| _4)` because the
    /// problem implies the two are equal — and there the stored reading is the
    /// correct one, discharged by the authored-implication bridge. So the
    /// stored reading is tried first and the permuted one only on its refusal;
    /// each is then validated by the SAME unchanged machinery (a certified
    /// premise over the exact internal endpoints, or a repair whose printed
    /// endpoints match byte-for-byte), so a reading that is not the step's
    /// meaning cannot be accepted — it refuses, and the loop moves on.
    pub(super) fn decode_surface_congruence(
        &self,
        clause: &[TermId],
        args: &[TermId],
    ) -> Result<Vec<SurfaceCongruenceApplication>, String> {
        if self.term_overrides.is_none() || !args.is_empty() {
            return Ok(Vec::new());
        }
        let [conclusion] = clause else {
            return Ok(Vec::new());
        };
        let TermData::App(Symbol::Named(equality), equality_args) = self.terms.get(*conclusion)
        else {
            return Ok(Vec::new());
        };
        let [left, right] = equality_args.as_slice() else {
            return Ok(Vec::new());
        };
        let (
            TermData::App(left_symbol, left_internal_args),
            TermData::App(right_symbol, right_internal_args),
        ) = (self.terms.get(*left), self.terms.get(*right))
        else {
            return Ok(Vec::new());
        };
        if equality != "="
            || left_symbol != right_symbol
            || left_internal_args.len() != right_internal_args.len()
        {
            return Ok(Vec::new());
        }
        let operator = Self::format_symbol(left_symbol);
        let Some(left_args) = split_application(&self.format_term(*left), &operator) else {
            return Ok(Vec::new());
        };
        let Some(right_args) = split_application(&self.format_term(*right), &operator) else {
            return Ok(Vec::new());
        };
        if left_args.len() != right_args.len() || left_args.len() != left_internal_args.len() {
            return Err("surface congruence changed the certified application arity".to_string());
        }
        let stored = SurfaceCongruenceApplication {
            left_args,
            right_args,
            left_internal_args: left_internal_args.clone(),
            right_internal_args: right_internal_args.clone(),
        };
        let permuted = self
            .internal_args_in_printed_order(&stored.left_args, left_internal_args)
            .map(|left| SurfaceCongruenceApplication {
                left_args: stored.left_args.clone(),
                right_args: stored.right_args.clone(),
                left_internal_args: left,
                right_internal_args: self
                    .internal_args_in_printed_order(&stored.right_args, right_internal_args)
                    .unwrap_or_else(|| right_internal_args.clone()),
            });
        let flipped_equalities = if operator == "=" && stored.left_args.len() == 2 {
            flipped_equality_readings(&stored)
        } else {
            Vec::new()
        };
        let mut readings = vec![stored];
        readings.extend(permuted);
        readings.extend(flipped_equalities);
        Ok(readings)
    }
}

/// The readings of a congruence between two EQUALITIES in which one or both
/// printed equalities spell their operands in the opposite order from the
/// term DAG, most conservative first.
///
/// THE SHAPE. `mk_eq` orders an equality's operands canonically and the
/// surface-override ledger keeps the AUTHOR's spelling: the authored
/// `(= x2 (+ x0 0))` interns as `(= x0 x2)`, so a congruence from it to
/// `(= x0 3)` prints `(= (= x2 (+ x0 0)) (= x0 3))`. Read in printed order the
/// first position pairs the spelling of `x2` with `x0`, which no premise
/// relates; read with the left equality's operands swapped back, position 0
/// is the reflexive `x0` (printed `(+ x0 0)` and `x0`, one `sum_simplify`) and
/// position 1 is the certified premise `(= x2 3)`. Measured on the
/// OR-substitution fuzz (`left="x2"; right="x0"`).
///
/// WHY THE CHECKER ACCEPTS IT. Pinned Carcara's `cong` treats a conclusion
/// equating two equalities specially: it accepts the premises against the
/// operands of either side in either order (`check_cong` over the four
/// flips), and the premises of these readings are ordered by the swapped
/// positions. Each reading is validated by the same machinery as the stored
/// one (premises matched by INTERNAL endpoints, repairs whose printed
/// endpoints match byte for byte), so a swap that is not the step's meaning
/// refuses and the loop moves on.
fn flipped_equality_readings(
    stored: &SurfaceCongruenceApplication,
) -> Vec<SurfaceCongruenceApplication> {
    let swapped = |args: &[String]| -> Vec<String> { args.iter().rev().cloned().collect() };
    [(true, false), (false, true), (true, true)]
        .into_iter()
        .map(|(flip_left, flip_right)| SurfaceCongruenceApplication {
            left_args: if flip_left {
                swapped(&stored.left_args)
            } else {
                stored.left_args.clone()
            },
            right_args: if flip_right {
                swapped(&stored.right_args)
            } else {
                stored.right_args.clone()
            },
            left_internal_args: stored.left_internal_args.clone(),
            right_internal_args: stored.right_internal_args.clone(),
        })
        .collect()
}

/// Whether a reading's premise order is the stored one.
///
/// A reading that needs no repair step can still pair the printed positions
/// with the certified premises in a DIFFERENT order: an authored override on
/// the left application permutes its operands. Pinned carcara 1.1.0 consumes
/// `cong` premises in printed argument order, so only the stored order is
/// left to the byte-identical default rendering; any other ships with the
/// reading's order. MEASURED on `(assert (< x 3))`, `(assert (or (not (< x
/// 3)) r))`, `(assert (not r))`: the override `(or (not (< x 3)) r)` over the
/// interned `(or r (not (< x 3)))` validated under the permuted reading with
/// no repair, the bridge returned nothing, and the default rendering shipped
/// `:premises (t5 t9)` in stored order, which carcara refused ("premise '(=
/// r false)' doesn't justify conclusion arguments '(not (< x 3))' and
/// 'false'") in a `trust_free=yes` document; `(t9 t5)` is `valid`.
pub(super) fn in_stored_order(ordered: &[String], premises: &[SurfaceCongruencePremise]) -> bool {
    ordered.len() == premises.len()
        && ordered
            .iter()
            .zip(premises)
            .all(|(ordered, premise)| *ordered == premise.id.to_string())
}
