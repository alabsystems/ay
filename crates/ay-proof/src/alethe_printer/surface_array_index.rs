// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Transport a read-over-write theorem across checked surface-index folds.
//!
//! Two bridges live here, one per ROW1 arm. `format_array_zero_index_bridge`
//! carries a UNIT ROW1 over a bit-vector `(bvadd x #x0)` spelling;
//! `format_row1_guard_index_bridge` carries a CONDITIONAL ROW1's guard over an
//! arithmetic `(+ x 0)` one. Both exist for the same reason — the authored
//! surface channel holds one spelling per `TermId` and a problem file can
//! author two for terms elaboration folded together — and neither asserts
//! anything: every step they emit is re-derived by the pinned checker.

use super::*;

impl AlethePrinter<'_> {
    pub(super) fn format_array_zero_index_bridge(
        &self,
        id: ProofId,
        clause: &[TermId],
    ) -> Option<String> {
        let crate::checker::ArraySelectStorePrinterTerms::Row1 {
            row,
            select,
            base_array,
            store_index,
            value,
            read_index,
            guard: None,
            packed_or: None,
        } = crate::checker::array_select_store_printer_terms(self.terms, clause, true)?
        else {
            return None;
        };
        if store_index != read_index || self.work_budget_exhausted() {
            return None;
        }
        let TermData::Var(name, _) = self.terms.get(store_index) else {
            return None;
        };
        if !matches!(self.terms.sort(store_index), Sort::BitVec(_)) {
            return None;
        }
        let canonical = quote_symbol(name);
        let printed = self.format_term(select);
        let [store, read]: [String; 2] = split_application(&printed, "select")?.try_into().ok()?;
        let [base, written, stored]: [String; 3] =
            split_application(&store, "store")?.try_into().ok()?;
        let value = self.format_term(value);
        if base != self.format_term(base_array)
            || !surface_literal::equal_modulo_bitvec_literal_spelling(&stored, &value)
            || [&printed, &canonical, &value]
                .iter()
                .any(|term| term.len() > 8192)
        {
            return None;
        }
        let forward = format!("(= {printed} {value})");
        let reverse = format!("(= {value} {printed})");
        let conclusion = self.format_term(row);
        if conclusion != forward && conclusion != reverse {
            return None;
        }
        let mut steps =
            self.zero_index_surface_steps(&format!("{id}.read"), &read, &canonical, read_index)?;
        steps.extend(self.zero_index_surface_steps(
            &format!("{id}.write"),
            &written,
            &canonical,
            store_index,
        )?);
        let same_index = format!("(select {store} {written})");
        let tail = format!(
            "(step {id}.writes (cl (= {canonical} {written})) :rule symm :premises ({id}.write))\n\
             (step {id}.indices (cl (= {read} {written})) :rule trans :premises ({id}.read {id}.writes))\n\
             (step {id}.read_cong (cl (= {printed} {same_index})) :rule cong :premises ({id}.indices))\n\
             (step {id}.idx (cl (= {same_index} {value})) :rule arrays_idx)\n\
             (step {id}.row (cl {forward}) :rule trans :premises ({id}.read_cong {id}.idx))\n"
        );
        let final_step = if conclusion == reverse {
            format!("(step {id} (cl {reverse}) :rule symm :premises ({id}.row))")
        } else {
            format!(
                "(step {id}.value (cl (= {value} {value})) :rule refl)\n\
                     (step {id} (cl {forward}) :rule trans :premises ({id}.row {id}.value))"
            )
        };
        self.charge((tail.len() + final_step.len()) as u64);
        if self.work_budget_exhausted() {
            return None;
        }
        steps.push(tail);
        steps.push(final_step);
        let output = steps.join("\n");
        (output.len() <= 32 * 1024 * 1024).then_some(output)
    }

    fn zero_index_surface_steps(
        &self,
        id: &str,
        surface: &str,
        canonical: &str,
        term: TermId,
    ) -> Option<Vec<String>> {
        if surface != canonical {
            return self.format_bv_add_zero_surface_equivalence(id, surface, canonical, term);
        }
        let step = format!("(step {id} (cl (= {canonical} {canonical})) :rule refl)");
        self.charge(step.len() as u64);
        (!self.work_budget_exhausted()).then_some(vec![step])
    }
}

/// One conditional-ROW1 guard whose PRINTED surface spells the certified index
/// pair differently from the way those two indices print on their own.
pub(super) struct Row1GuardIndexBridge {
    /// The equality the local subproof assumes: the guard's own inner text,
    /// verbatim, so `subproof :discharge` concludes exactly the printed guard.
    pub assumed_equality: String,
    /// `true` when the bridged index equality is `(= store_index read_index)`.
    pub forward: bool,
    /// The bridge steps, each line terminated, or empty.
    pub steps: String,
    /// The step id that carries the bridged index equality.
    pub premise: String,
}

impl AlethePrinter<'_> {
    /// Derive the certified index equality from a conditional ROW1 guard whose
    /// printed surface is a DIFFERENT authored spelling of the same pair.
    ///
    /// WHY THE SHAPE EXISTS. The authored-surface channel keeps ONE spelling
    /// per `TermId`, and `collect_deep_array_surface_overrides` (ay-dpll,
    /// `executor/proof_surface_syntax.rs`) deliberately keeps the OUTERMOST
    /// authored spelling when elaboration folds a parent and a child onto the
    /// same term — its own comment names `(+ (- x 1) 0)` / `(- x 1)`. A problem
    /// file that BOTH asserts `(= (seq_offset s) 0)` at top level AND reads
    /// `(+ (seq_offset s) 0)` inside an authored `store` therefore gives the
    /// guard's equality node one authored text and the read index another. Each
    /// text is needed verbatim by the `assume` that carries its own assertion,
    /// so neither can simply be dropped; they meet only here, inside this
    /// lemma's own subproof, and until this bridge existed that meeting
    /// declined the whole export (`conditional ROW1 guard surface override
    /// changes the certified index pair`).
    ///
    /// NOTHING IS TAKEN ON THE PRODUCER'S WORD.
    /// `array_select_store_printer_terms` has already established that the
    /// guard term IS `(not (= store_index read_index))` over those exact two
    /// `TermId`s; this only decides how to SPELL that fact. Each emitted step
    /// is re-derived by the checker: `poly_simp` proves a polynomial identity
    /// between two printed spellings (probed on carcara 1.1.0, git 9a352ee:
    /// `(= (+ x 0) x)` is `valid`), `trans` is premise-checked, and
    /// `printed_poly_simp_holds` — the replay of the pinned checker's own
    /// normalizer that `judge_printed_la_generic` runs over every rendered
    /// `poly_simp` anyway — must answer `Some(true)` HERE before the step is
    /// emitted at all. A spelling pair it does not decide affirmatively
    /// returns `None` and leaves the caller's existing refusal exactly as it
    /// was.
    pub(super) fn format_row1_guard_index_bridge(
        &self,
        id: ProofId,
        printed_guard: &str,
        store_index: &str,
        read_index: &str,
    ) -> Option<Row1GuardIndexBridge> {
        const MAX_GUARD_SURFACE: usize = 8192;
        if self.work_budget_exhausted()
            || [printed_guard, store_index, read_index]
                .iter()
                .any(|text| text.len() > MAX_GUARD_SURFACE)
        {
            return None;
        }
        let negated = split_application(printed_guard, "not")?;
        let [inner] = negated.as_slice() else {
            return None;
        };
        let sides = split_application(inner, "=")?;
        let [left, right] = sides.as_slice() else {
            return None;
        };
        for forward in [true, false] {
            let (first, second) = if forward {
                (store_index, read_index)
            } else {
                (read_index, store_index)
            };
            let head_id = format!("{id}.gsa");
            let tail_id = format!("{id}.gsb");
            let (Some(head), Some(tail)) = (
                Self::printed_index_surface_step(&head_id, first, left),
                Self::printed_index_surface_step(&tail_id, right, second),
            ) else {
                continue;
            };
            if head.is_empty() && tail.is_empty() {
                // Both sides already spell the certified pair, so the caller's
                // own byte comparison covers this guard; never shadow it here.
                continue;
            }
            let mut steps = String::new();
            let mut premises = Vec::with_capacity(3);
            if !head.is_empty() {
                steps.push_str(&head);
                steps.push('\n');
                premises.push(head_id);
            }
            premises.push(format!("{id}.h"));
            if !tail.is_empty() {
                steps.push_str(&tail);
                steps.push('\n');
                premises.push(tail_id);
            }
            let derived = format!("(= {first} {second})");
            let _ = std::fmt::Write::write_fmt(
                &mut steps,
                format_args!(
                    "(step {id}.gs (cl {derived}) :rule trans :premises ({}))\n",
                    premises.join(" ")
                ),
            );
            self.charge(steps.len() as u64);
            if self.work_budget_exhausted() {
                return None;
            }
            return Some(Row1GuardIndexBridge {
                assumed_equality: inner.clone(),
                forward,
                steps,
                premise: format!("{id}.gs"),
            });
        }
        None
    }

    /// `Some("")` when the two printed spellings are the same term to the
    /// checker, `Some(step)` when a `poly_simp` the pinned checker's own
    /// replay ACCEPTS carries `left` to `right`, and `None` otherwise.
    fn printed_index_surface_step(id: &str, left: &str, right: &str) -> Option<String> {
        if surface_literal::same_printed_term(left, right) {
            return Some(String::new());
        }
        (la_generic_surface::printed_poly_simp_holds(left, right) == Some(true))
            .then(|| format!("(step {id} (cl (= {left} {right})) :rule poly_simp)"))
    }
}

#[cfg(test)]
mod tests;
