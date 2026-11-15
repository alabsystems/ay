// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A fresh variable's binary clauses introduced through one pseudo-Boolean
//! definition instead of one redundance step each.

use super::*;

impl<W: Write> VeripbWriter<W> {
    /// Log the clauses (x ∨ f_1) … (x ∨ f_n) of a fresh variable `x` (for
    /// factoring, its dividers) as one definition, `red n x 1 f_1 … 1 f_n >= n
    /// : x -> 1 ;` (x or the conjunction of the f), each clause as `rup`
    /// hinted by it, and the definition deleted by id.
    ///
    /// The official check scans its whole database for every `red` step, to
    /// find the constraints the witness touches; the clauses one by one cost n
    /// such scans, the definition one. The definition's witness touches only
    /// constraints on `x`, so `x` must be fresh or the caller must have
    /// written what it needs (factoring writes its blocked clause
    /// (¬x ∨ ¬f_1 ∨ … ∨ ¬f_n) first, which the witness turns into a clause
    /// the negated definition implies).
    ///
    /// `Ok(false)` with nothing written when there are fewer than two clauses
    /// (the definition would be the clause itself), when the writer cannot
    /// number its lines, or when it no longer accepts steps.
    pub fn add_conjunction_dividers(
        &mut self,
        fresh: Literal,
        factors: &[Literal],
    ) -> io::Result<bool> {
        if factors.len() < 2 || !self.accepting() {
            return Ok(false);
        }
        let Some(base) = self.original_constraints else {
            return Ok(false);
        };
        let Some(def_seq) = self.derived_seq.checked_add(1) else {
            return Ok(false);
        };
        let Some(def_id) = base.checked_add(def_seq) else {
            return Ok(false);
        };
        let n = factors.len() as u64;
        let result = self.write_line(|line| {
            line.extend_from_slice(b"red ");
            push_u64_decimal(line, n);
            line.push(b' ');
            push_literal_name(line, fresh);
            for &f in factors {
                line.extend_from_slice(b" 1 ");
                push_literal_name(line, f);
            }
            line.extend_from_slice(b" >= ");
            push_u64_decimal(line, n);
            line.extend_from_slice(b" : ");
            push_witness_substitution(line, &[fresh]);
            line.extend_from_slice(b" ;");
        });
        self.latch(result)?;
        self.derived_seq = def_seq;
        self.added_count = self.added_count.saturating_add(1);
        self.note_fresh(&[fresh])?;
        self.note_fresh(factors)?;
        for &f in factors {
            self.add_rup(&[fresh, f], &[def_id])?;
        }
        let result = self.write_line(|line| {
            line.extend_from_slice(b"del id ");
            push_u64_decimal(line, def_id);
            line.extend_from_slice(b" ;");
        });
        self.latch(result)?;
        self.deleted_count = self.deleted_count.saturating_add(1);
        self.id_deletions = self.id_deletions.saturating_add(1);
        Ok(true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::Variable;

    fn pos(v: u32) -> Literal {
        Literal::positive(Variable(v))
    }

    fn neg(v: u32) -> Literal {
        Literal::negative(Variable(v))
    }

    /// The toy factoring of (x1∨x3)(x2∨x3)(x1∨x4)(x2∨x4) by fresh x5 that the
    /// pinned VeriPB elaborated and CP2026 CakePB verified (2026-09-30), with
    /// the blocked clause at id 8 as factoring writes it.
    #[test]
    fn test_dividers_are_hinted_by_one_definition_deleted_by_id() {
        let mut w = VeripbWriter::with_original_constraints(Vec::new(), 7);
        w.add(&[neg(4), neg(0), neg(1)]).expect("write");
        assert!(w
            .add_conjunction_dividers(pos(4), &[pos(0), pos(1)])
            .expect("write"));
        assert_eq!(w.constraint_id(&[pos(4), pos(0)]), Some(10));
        assert_eq!(w.constraint_id(&[pos(1), pos(4)]), Some(11));
        w.add_rup(&[neg(4), pos(2)], &[8, 1, 2]).expect("write");
        let out = String::from_utf8(w.into_inner().expect("no io error")).expect("utf8");
        assert_eq!(
            out,
            "pseudo-Boolean proof version 3.0\n\
             red 1 ~x5 1 ~x1 1 ~x2 >= 1 : x5 -> 0 ;\n\
             red 2 x5 1 x1 1 x2 >= 2 : x5 -> 1 ;\n\
             rup 1 x5 1 x1 >= 1 : 9 ;\n\
             rup 1 x5 1 x2 >= 1 : 9 ;\n\
             del id 9 ;\n\
             rup 1 ~x5 1 x3 >= 1 : 8 1 2 ;\n"
        );
    }

    #[test]
    fn test_a_single_divider_or_an_unnumbered_writer_writes_nothing() {
        let mut w = VeripbWriter::with_original_constraints(Vec::new(), 7);
        assert!(!w
            .add_conjunction_dividers(pos(4), &[pos(0)])
            .expect("write"));
        let mut w = VeripbWriter::new(Vec::new());
        assert!(!w
            .add_conjunction_dividers(pos(4), &[pos(0), pos(1)])
            .expect("write"));
        assert_eq!(w.added_count(), 0);
    }
}
