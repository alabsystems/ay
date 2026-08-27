// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! VeriPB (pseudo-Boolean proof, version 3.0) writer.
//!
//! # Why this exists
//!
//! AY's symmetry-breaking routes (the aux-free WLOG chains and the orbitope
//! staircase) derive clauses that are *substitution redundant* (SR), not RUP or
//! RAT. On the DRAT surface those are serialized as DSR `a`-lines carrying a
//! substitution witness — and only `dsr-trim` accepts them: `drat-trim` and
//! `dpr-trim` both return `s NOT VERIFIED` (measured 2026-08-24). The official
//! SAT-COMP 2026 checker menu is `dpr-trim` / `gratgen` / `VeriPB`, the
//! registrant declares one up front, and a rejected UNSAT proof is
//! disqualifying — so on the DRAT surface the whole symmetry bucket has to be
//! clamped off (see `proof_capability::declared_checker_accepts_sr_witnesses`).
//!
//! VeriPB is the way back: it is on the menu AND its `red` (redundance-based
//! strengthening) rule takes a substitution witness natively, which is exactly
//! the SR side condition
//!
//! ```text
//!     F ∧ ¬C ⊨ (F ∧ C)↾ω
//! ```
//!
//! that `dsr-trim` checks. The correspondence is direct, so this writer is a
//! serializer, not a translator with a proof obligation of its own.
//!
//! # Rule mapping
//!
//! | AY proof step                       | VeriPB rule                          |
//! |-------------------------------------|--------------------------------------|
//! | `add(C)`, C non-empty               | `red <C> : x_p -> 1 ;` (p = `C[0]`)  |
//! | `add(C)`, C empty                   | `rup >= 1 ;` + output/conclusion tail|
//! | `add_pr(C, w)` / `add_sr(C, w)`     | `red <C> : <ω(w)> ;`                 |
//! | `delete(C)`                         | `del spec <C> ;`                     |
//!
//! Plain additions become `red` with the *pivot* witness rather than `rup`
//! because a DRAT `a`-line is RAT on its first literal, not necessarily RUP:
//! extension-variable definitions (the Tseitin-chunked XOR ladders) and the
//! HHW image-and-chain fragment are RAT-only. `red C : p -> 1` is exactly the
//! RAT condition on `p`, and it subsumes RUP — VeriPB tries a whole-subproof
//! RUP autoprove first, so a genuinely-RUP addition costs the same as `rup`.
//!
//! # Formula file
//!
//! VeriPB parses DIMACS CNF directly (variable `i` is `x<i>`, clause = sum of
//! literals `>= 1`), so no OPB translation is emitted or needed: the checker is
//! invoked as `veripb <instance>.cnf <proof>.pbp`.
//!
//! # Which VeriPB
//!
//! Not any of them. Published 3.0.2 carries eight confirmed wrong-verdict
//! defects — it prints `s VERIFIED UNSATISFIABLE` for satisfiable formulas
//! given the right small proof — so this crate's claims are made against the
//! checker `ci/veripb.pin` names (upstream `4bb10c2c` plus the reviewed AY
//! soundness patch), which must reject all nine `ci/veripb-soundness/`
//! fixtures before any verdict of its own is believed. Measured 2026-08-24 on
//! this machine: a stock build of upstream `main` ACCEPTED five of those nine;
//! the pinned build rejected all nine. Every number in this module's history
//! is a pinned-checker number.
//!
//! # Conclusion
//!
//! The trailer (`output NONE; conclusion UNSAT; end pseudo-Boolean proof;`) is
//! written when the empty clause is added, which is the single centralized
//! UNSAT finalization point (`solve::finalize_unsat`). Writes after that are
//! no-ops: VeriPB ignores everything past the end line, and a doubled trailer
//! would be a parse error. A run that never derives the empty clause leaves an
//! unterminated file, which is the correct outcome — a non-UNSAT proof sidecar
//! is deleted by the caller.

use crate::literal::Literal;
use std::io::{self, Write};

const VERIPB_HEADER: &[u8] = b"pseudo-Boolean proof version 3.0\n";
const VERIPB_TRAILER: &[u8] = b"output NONE;\nconclusion UNSAT;\nend pseudo-Boolean proof;\n";

const VERIPB_LINE_INITIAL_CAPACITY: usize = 256;
const VERIPB_LINE_MAX_RETAINED_CAPACITY: usize = 256 * 1024;

/// The image of a variable's *positive* literal under a witness substitution.
///
/// Mirrors `ay_drat_check::checker::sr::SubImage`: `dsr-trim` stores the image
/// of the positive literal and re-applies the sign on lookup, so a mapping read
/// off a negative source literal is stored negated.
#[derive(Clone, Copy, PartialEq, Eq)]
enum SubImage {
    True,
    False,
    Lit(Literal),
}

impl SubImage {
    fn negate(self) -> Self {
        match self {
            Self::True => Self::False,
            Self::False => Self::True,
            Self::Lit(lit) => Self::Lit(lit.negated()),
        }
    }
}

/// Write `x<n>` / `~x<n>` for a literal, using VeriPB's DIMACS-CNF variable
/// naming (`i` ↦ `x<i>`).
fn push_literal_name(buf: &mut Vec<u8>, lit: Literal) {
    let dimacs = lit.to_dimacs();
    if dimacs < 0 {
        buf.push(b'~');
    }
    buf.push(b'x');
    push_u32_decimal(buf, dimacs.unsigned_abs());
}

fn push_u32_decimal(buf: &mut Vec<u8>, mut value: u32) {
    if value == 0 {
        buf.push(b'0');
        return;
    }
    let mut digits = [0u8; 10];
    let mut len = 0;
    while value != 0 {
        digits[len] = b'0' + (value % 10) as u8;
        value /= 10;
        len += 1;
    }
    for digit in digits[..len].iter().rev() {
        buf.push(*digit);
    }
}

/// Serialize a clause as an OPB-style constraint: `1 l1 1 l2 ... >= 1`.
///
/// The empty clause is `>= 1` — a degree-1 constraint with no terms, i.e.
/// contradiction, which is what VeriPB expects from `rup >= 1 ;`.
fn push_clause_constraint(buf: &mut Vec<u8>, clause: &[Literal]) {
    for lit in clause {
        buf.extend_from_slice(b"1 ");
        push_literal_name(buf, *lit);
        buf.push(b' ');
    }
    buf.extend_from_slice(b">= 1");
}

/// Serialize a DSR/DPR witness token stream as a VeriPB substitution.
///
/// Layout (identical to `DratWriter::add_sr` and `dsr-trim`'s
/// `parse_sr_clause_and_witness`): `pivot [pr-atoms…] [pivot(sep) (l m)…]`.
/// `witness[0]` is the pivot and maps to true; atoms before the second pivot
/// occurrence each map to true (the PR part); after the separating second
/// pivot, tokens are read in `(l, m)` pairs giving `σ(l) = m`.
///
/// Assignments are normalized to the positive literal's image exactly as
/// `Subst::set` does, so the emitted `x<v> -> …` mappings are the same map the
/// SR kernel builds. Re-assignment of a variable keeps its first emission slot
/// and takes the last value (`dsr-trim` permits this only for the pivot
/// variable); VeriPB rejects a substitution that names one variable twice.
fn push_witness_substitution(buf: &mut Vec<u8>, witness: &[Literal]) {
    let Some(&pivot) = witness.first() else {
        return;
    };

    // Witnesses are short (a transposition chain over one symmetry generator),
    // so a linear-scan association list beats allocating a variable-indexed map
    // per step.
    let mut map: Vec<(u32, SubImage)> = Vec::with_capacity(witness.len());
    let set = |map: &mut Vec<(u32, SubImage)>, lit: Literal, image: SubImage| {
        let stored = if lit.is_positive() {
            image
        } else {
            image.negate()
        };
        let var = lit.variable().0;
        if let Some(entry) = map.iter_mut().find(|(existing, _)| *existing == var) {
            entry.1 = stored;
        } else {
            map.push((var, stored));
        }
    };

    set(&mut map, pivot, SubImage::True);

    let mut seen_divider = false;
    let mut index = 1;
    while index < witness.len() {
        let lit = witness[index];
        if seen_divider {
            // Substitution part: (l, m) pairs. A dangling half-pair is a
            // malformed witness; stop rather than invent a mapping — the
            // checker then rejects the step, which is the fail-closed outcome.
            let Some(&mapped) = witness.get(index + 1) else {
                break;
            };
            set(&mut map, lit, SubImage::Lit(mapped));
            index += 2;
        } else if lit == pivot {
            seen_divider = true;
            index += 1;
        } else {
            set(&mut map, lit, SubImage::True);
            index += 1;
        }
    }

    for (position, (var, image)) in map.iter().enumerate() {
        if position > 0 {
            buf.push(b' ');
        }
        buf.push(b'x');
        push_u32_decimal(buf, var.saturating_add(1));
        buf.extend_from_slice(b" -> ");
        match image {
            SubImage::True => buf.push(b'1'),
            SubImage::False => buf.push(b'0'),
            SubImage::Lit(lit) => push_literal_name(buf, *lit),
        }
    }
}

/// VeriPB proof writer.
///
/// Error handling matches [`super::DratWriter`]: on the first write failure
/// `io_failed` latches and every later write is a no-op, so a truncated proof
/// is detected once at finalization instead of raising per-step errors through
/// the solver.
pub struct VeripbWriter<W: Write> {
    writer: W,
    line: Vec<u8>,
    added_count: u64,
    deleted_count: u64,
    io_failed: bool,
    header_written: bool,
    /// Set once the trailer is written; later writes are dropped.
    concluded: bool,
}

impl<W: Write> VeripbWriter<W> {
    /// Create a VeriPB proof writer. VeriPB has no binary encoding, so this is
    /// the only constructor.
    pub fn new(writer: W) -> Self {
        Self {
            writer,
            line: Vec::with_capacity(VERIPB_LINE_INITIAL_CAPACITY),
            added_count: 0,
            deleted_count: 0,
            io_failed: false,
            header_written: false,
            concluded: false,
        }
    }

    /// True while the writer still accepts steps.
    fn accepting(&self) -> bool {
        !self.io_failed && !self.concluded
    }

    fn ensure_header(&mut self) -> io::Result<()> {
        if self.header_written {
            return Ok(());
        }
        self.header_written = true;
        self.writer.write_all(VERIPB_HEADER)
    }

    /// Build one rule line into the reusable buffer and write it.
    fn write_line(&mut self, build: impl FnOnce(&mut Vec<u8>)) -> io::Result<()> {
        self.ensure_header()?;
        if self.line.capacity() > VERIPB_LINE_MAX_RETAINED_CAPACITY {
            self.line = Vec::with_capacity(VERIPB_LINE_INITIAL_CAPACITY);
        } else {
            self.line.clear();
        }
        build(&mut self.line);
        self.line.push(b'\n');
        // `self.line` is borrowed immutably here while `self.writer` is
        // borrowed mutably; split the borrow explicitly.
        let Self { writer, line, .. } = self;
        writer.write_all(line)
    }

    fn latch(&mut self, result: io::Result<()>) -> io::Result<()> {
        if let Err(error) = result {
            self.io_failed = true;
            return Err(error);
        }
        Ok(())
    }

    /// Log a derived clause.
    ///
    /// Non-empty clauses become `red <C> : <C[0] ↦ true> ;` (the RAT condition
    /// on the DRAT pivot, which subsumes RUP). The empty clause becomes
    /// `rup >= 1 ;` followed by the output/conclusion trailer.
    pub fn add(&mut self, clause: &[Literal]) -> io::Result<()> {
        if !self.accepting() {
            return Ok(());
        }
        if clause.is_empty() {
            let result = self
                .write_line(|line| line.extend_from_slice(b"rup >= 1 ;"))
                .and_then(|()| self.writer.write_all(VERIPB_TRAILER));
            self.latch(result)?;
            self.concluded = true;
            self.added_count += 1;
            return Ok(());
        }
        let pivot = clause[0];
        let result = self.write_line(|line| {
            line.extend_from_slice(b"red ");
            push_clause_constraint(line, clause);
            line.extend_from_slice(b" : ");
            push_witness_substitution(line, &[pivot]);
            line.extend_from_slice(b" ;");
        });
        self.latch(result)?;
        self.added_count += 1;
        Ok(())
    }

    /// Log a propagation-redundancy (DPR) step.
    ///
    /// The witness layout is the assignment-only prefix of the SR stream, so it
    /// shares [`Self::add_sr`]'s serializer.
    pub fn add_pr(&mut self, clause: &[Literal], witness: &[Literal]) -> io::Result<()> {
        self.add_sr(clause, witness)
    }

    /// Log a substitution-redundancy (SR) step — the symmetry routes' output.
    ///
    /// `witness` is the same token stream `DratWriter::add_sr` serializes, so
    /// the two surfaces stay byte-for-byte equivalent in *content*; only the
    /// encoding differs.
    pub fn add_sr(&mut self, clause: &[Literal], witness: &[Literal]) -> io::Result<()> {
        debug_assert!(
            !clause.is_empty() && witness.first() == clause.first(),
            "BUG: SR/DSR witness must begin by repeating the clause pivot clause[0]"
        );
        if !self.accepting() {
            return Ok(());
        }
        let result = self.write_line(|line| {
            line.extend_from_slice(b"red ");
            push_clause_constraint(line, clause);
            if !witness.is_empty() {
                line.extend_from_slice(b" : ");
                push_witness_substitution(line, witness);
            }
            line.extend_from_slice(b" ;");
        });
        self.latch(result)?;
        self.added_count += 1;
        Ok(())
    }

    /// Log a clause deletion as `del spec <C> ;`.
    ///
    /// Deletions are not optional here. AY's `adv_gc` route collapses shuffled
    /// at-most-one ladders into their pairwise closure (RUP additions *plus*
    /// deletions) before the orbitope detector runs, and the subsequent SR
    /// witnesses are redundant only against the collapsed formula: dropping the
    /// `d` lines makes `adv_gc_n100_k10` fail with an unprovable proofgoal on a
    /// ladder clause that should no longer be in the database (measured).
    ///
    /// Deleting a formula (core) constraint makes VeriPB run a checked-deletion
    /// check; when that fails it prints one warning and downgrades to unchecked
    /// deletion for the rest of the proof. That is harmless for a refutation —
    /// deletion only weakens the database, so a contradiction derived after it
    /// is still a contradiction from a subset of the input — and this writer
    /// claims `output NONE`, i.e. no reformulation guarantee that the downgrade
    /// could invalidate.
    pub fn delete(&mut self, clause: &[Literal]) -> io::Result<()> {
        if !self.accepting() {
            return Ok(());
        }
        let result = self.write_line(|line| {
            line.extend_from_slice(b"del spec ");
            push_clause_constraint(line, clause);
            line.extend_from_slice(b" ;");
        });
        self.latch(result)?;
        self.deleted_count += 1;
        Ok(())
    }

    /// Clauses successfully added.
    pub fn added_count(&self) -> u64 {
        self.added_count
    }

    /// Clauses successfully deleted.
    pub fn deleted_count(&self) -> u64 {
        self.deleted_count
    }

    /// True if any write failed.
    pub fn has_io_error(&self) -> bool {
        self.io_failed
    }

    /// True once the output/conclusion trailer has been written.
    pub fn is_concluded(&self) -> bool {
        self.concluded
    }

    /// Flush the underlying writer (no-op after an I/O failure).
    pub fn flush(&mut self) -> io::Result<()> {
        if self.io_failed {
            return Ok(());
        }
        let result = self.writer.flush();
        if let Err(error) = result {
            self.io_failed = true;
            return Err(error);
        }
        Ok(())
    }

    /// Recover the inner writer.
    ///
    /// # Errors
    ///
    /// Returns an error if any write failed, which means the proof stream is
    /// truncated.
    pub fn into_inner(self) -> io::Result<W> {
        if self.io_failed {
            return Err(io::Error::other(
                "VeriPB proof writer encountered I/O error during solve",
            ));
        }
        Ok(self.writer)
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

    fn render(steps: impl FnOnce(&mut VeripbWriter<Vec<u8>>)) -> String {
        let mut writer = VeripbWriter::new(Vec::new());
        steps(&mut writer);
        String::from_utf8(writer.into_inner().expect("no io error")).expect("utf8")
    }

    #[test]
    fn test_plain_addition_is_red_with_the_drat_pivot() {
        // Variable(0) is DIMACS 1: a DRAT `a`-line is RAT on its first literal,
        // which is `red C : x1 -> 1`.
        let out = render(|w| {
            w.add(&[pos(0), neg(1)]).expect("write");
        });
        assert_eq!(
            out,
            "pseudo-Boolean proof version 3.0\nred 1 x1 1 ~x2 >= 1 : x1 -> 1 ;\n"
        );
    }

    #[test]
    fn test_negative_pivot_maps_the_variable_to_false() {
        let out = render(|w| {
            w.add(&[neg(4)]).expect("write");
        });
        assert!(out.ends_with("red 1 ~x5 >= 1 : x5 -> 0 ;\n"), "{out}");
    }

    #[test]
    fn test_empty_clause_writes_rup_contradiction_and_the_trailer() {
        let out = render(|w| {
            w.add(&[]).expect("write");
        });
        assert_eq!(
            out,
            "pseudo-Boolean proof version 3.0\nrup >= 1 ;\noutput NONE;\nconclusion UNSAT;\n\
             end pseudo-Boolean proof;\n"
        );
    }

    #[test]
    fn test_steps_after_the_conclusion_are_dropped() {
        let out = render(|w| {
            w.add(&[]).expect("write");
            w.add(&[pos(0)]).expect("write");
            w.delete(&[pos(1)]).expect("write");
        });
        assert_eq!(out.matches("end pseudo-Boolean proof;").count(), 1);
        assert!(!out.contains("x1"), "{out}");
    }

    #[test]
    fn test_php_sr_witness_translates_to_a_veripb_substitution() {
        // The aux-free PHP shape from `build_php_aux_free_sr`: clause (¬x5),
        // witness [¬x5, x3, ¬x5(sep), (x4 x6) (x6 x4)] — pivot to false, the PR
        // atom to true, then the pigeon-swap transposition.
        let clause = [neg(4)];
        let witness = [neg(4), pos(2), neg(4), pos(3), pos(5), pos(5), pos(3)];
        let out = render(|w| {
            w.add_sr(&clause, &witness).expect("write");
        });
        assert!(
            out.ends_with("red 1 ~x5 >= 1 : x5 -> 0 x3 -> 1 x4 -> x6 x6 -> x4 ;\n"),
            "{out}"
        );
    }

    #[test]
    fn test_substitution_image_of_variable_one_is_not_the_constant_one() {
        // Regression: the image literal `x1` and the constant `1` are distinct
        // in VeriPB, and conflating them silently rewrites the witness (it made
        // php_sudoku's staircase unprovable at goal 29 during bring-up).
        let clause = [neg(3)];
        let witness = [neg(3), pos(0), neg(3), pos(1), pos(0)];
        let out = render(|w| {
            w.add_sr(&clause, &witness).expect("write");
        });
        assert!(out.ends_with("x2 -> x1 ;\n"), "{out}");
    }

    #[test]
    fn test_negative_source_literal_negates_the_image() {
        // σ(¬x2) = x3 is stored as the positive literal's image: x2 -> ~x3.
        let clause = [pos(0)];
        let witness = [pos(0), pos(0), neg(1), pos(2)];
        let out = render(|w| {
            w.add_sr(&clause, &witness).expect("write");
        });
        assert!(
            out.ends_with("red 1 x1 >= 1 : x1 -> 1 x2 -> ~x3 ;\n"),
            "{out}"
        );
    }

    #[test]
    fn test_deletion_is_emitted_as_del_spec() {
        let out = render(|w| {
            w.delete(&[pos(0), neg(2)]).expect("write");
        });
        assert!(out.ends_with("del spec 1 x1 1 ~x3 >= 1 ;\n"), "{out}");
    }

    #[test]
    fn test_counts_track_additions_and_deletions() {
        let mut writer = VeripbWriter::new(Vec::new());
        writer.add(&[pos(0)]).expect("write");
        writer.add_sr(&[neg(1)], &[neg(1)]).expect("write");
        writer.delete(&[pos(0)]).expect("write");
        assert_eq!(writer.added_count(), 2);
        assert_eq!(writer.deleted_count(), 1);
        assert!(!writer.is_concluded());
        writer.add(&[]).expect("write");
        assert!(writer.is_concluded());
    }

    #[test]
    fn test_dangling_substitution_half_pair_is_dropped_rather_than_invented() {
        let clause = [pos(0)];
        let witness = [pos(0), pos(0), pos(1)];
        let out = render(|w| {
            w.add_sr(&clause, &witness).expect("write");
        });
        assert!(out.ends_with("red 1 x1 >= 1 : x1 -> 1 ;\n"), "{out}");
    }
}
