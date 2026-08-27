// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Export LRAT proofs to Lean4 proof terms (Phase 1, #8253; Phase 2, #8697).
//!
//! Two emission modes are supported:
//!
//! 1. **Data-only** ([`write_lean4_lrat`]): emits the proof steps as Lean4
//!    data only. The file parses but makes no soundness claim (no theorem).
//!    Kept for backward compatibility with the `--proof file.lean4` CLI
//!    output that predates kernel verification.
//!
//! 2. **Checker-acceptance** ([`write_lean4_lrat_kernel`]): emits a fully
//!    self-contained Lean4 file that defines a Reverse-Unit-Propagation
//!    (RUP) checker, encodes the original clauses + proof steps as data,
//!    and asserts `theorem proof_valid : lratCheck originalClauses
//!    proofSteps = true := by native_decide`. If the proof is unsound,
//!    this checker rejects the file. Its own soundness is unproved, so this
//!    form is diagnostic only; [`write_lean4_verified`] is verdict authority.
//! The kernel definition is self-contained (no imports beyond Lean4 core):
//! - `Literal` as `Int` (positive = positive polarity, negative = negated)
//! - `Clause` as `List Literal`
//! - `LratAddStep` as a structure with clause id, derived clause, and hints
//! - `rupCheck` for propositional RUP verification
//! - `lratCheck` walks proof steps, extending the clause table, requiring
//!   the last step to be the empty clause
//! ## Propositional scope
//!
//! Kernel-checked output currently covers **propositional UNSAT only**. The
//! hint list is interpreted as a RUP chain; negative hints (RAT witness
//! boundaries / deletion markers) are skipped in this minimal checker.
//! Theory reasoning (LIA, BV, UF) is deferred to future phases — those
//! proofs are emitted via the Alethe path.

use std::io::{self, Write};

use crate::proof_certificate::ProofStep;

/// Write a sequence of LRAT proof steps as a self-contained Lean4 file.
///
/// Original clause IDs are inferred from the proof steps: any hint ID that
/// is not produced by a proof step is an original input clause.
///
/// # Arguments
///
/// * `steps` - The LRAT proof steps (from `ProofCertificate::materialize()`)
/// * `writer` - Output destination
///
/// # Errors
///
/// Returns `io::Error` if writing fails.
pub(crate) fn write_lean4_lrat(steps: &[ProofStep], writer: &mut dyn Write) -> io::Result<()> {
    if steps.is_empty() {
        writeln!(writer, "-- Auto-generated LRAT proof from AY")?;
        writeln!(writer, "-- Empty proof (no steps)")?;
        return Ok(());
    }

    // Determine original clause IDs: any hint ID not produced by a proof step.
    let derived: crate::kani_compat::DetHashSet<u64> = steps.iter().map(|s| s.clause_id).collect();
    let mut original_ids: Vec<u64> = steps
        .iter()
        .flat_map(|s| s.hints.iter().copied())
        .filter(|&id| id > 0)
        .map(|id| id as u64)
        .filter(|&id| !derived.contains(&id))
        .collect();
    original_ids.sort_unstable();
    original_ids.dedup();

    // Header
    writeln!(writer, "-- Auto-generated LRAT proof from AY")?;
    writeln!(
        writer,
        "-- Original clauses referenced: {}, proof steps: {}",
        original_ids.len(),
        steps.len()
    )?;
    writeln!(writer)?;
    writeln!(writer, "namespace AY.LratProof")?;
    writeln!(writer)?;

    // Type abbreviations
    writeln!(
        writer,
        "/-- A literal is an integer: positive for variable, negative for negated variable. -/"
    )?;
    writeln!(writer, "abbrev Literal := Int")?;
    writeln!(writer, "abbrev Clause := List Literal")?;
    writeln!(writer, "abbrev ClauseId := Nat")?;
    writeln!(writer)?;

    // LratAddStep structure
    writeln!(
        writer,
        "/-- An LRAT addition step: derives a new clause from antecedent hints. -/"
    )?;
    writeln!(writer, "structure LratAddStep where")?;
    writeln!(writer, "  id : ClauseId")?;
    writeln!(writer, "  clause : Clause")?;
    writeln!(writer, "  hints : List Int")?;
    writeln!(writer, "  deriving Repr, BEq")?;
    writeln!(writer)?;

    // Emit proof steps as a Lean4 list
    writeln!(
        writer,
        "/-- The LRAT proof steps deriving contradiction from the original clauses. -/"
    )?;
    writeln!(writer, "def proofSteps : List LratAddStep := [")?;
    for (i, step) in steps.iter().enumerate() {
        let lits = format_lean_int_list(&step.dimacs_literals());
        let hints = format_lean_hint_list(&step.hints);
        let comma = if i + 1 < steps.len() { "," } else { "" };
        writeln!(
            writer,
            "  {{ id := {}, clause := {lits}, hints := {hints} }}{comma}",
            step.clause_id
        )?;
    }
    writeln!(writer, "]")?;
    writeln!(writer)?;

    // Emit metadata about the final step (should be the empty clause)
    if let Some(last) = steps.last() {
        if last.literals.is_empty() {
            writeln!(
                writer,
                "/-- The final step derives the empty clause (contradiction). -/"
            )?;
            writeln!(writer, "def emptyClauseId : ClauseId := {}", last.clause_id)?;
        } else {
            writeln!(
                writer,
                "-- WARNING: last proof step is not the empty clause"
            )?;
            writeln!(
                writer,
                "-- Last step clause_id={} has {} literals",
                last.clause_id,
                last.literals.len()
            )?;
        }
    }
    writeln!(writer)?;

    // Emit original clause ID list (for reference / checking)
    writeln!(
        writer,
        "/-- Original input clause IDs referenced by the proof. -/"
    )?;
    let orig_ids_str = format_lean_nat_list(&original_ids);
    writeln!(
        writer,
        "def originalClauseIds : List ClauseId := {orig_ids_str}"
    )?;
    writeln!(writer)?;

    // Emit the number of proof steps for verification metadata
    writeln!(writer, "/-- Total number of LRAT addition steps. -/")?;
    writeln!(writer, "def proofStepCount : Nat := {}", steps.len())?;
    writeln!(writer)?;

    writeln!(writer, "end AY.LratProof")?;
    Ok(())
}

/// Write a self-contained Lean4 LRAT checker-acceptance artifact.
///
/// Unlike [`write_lean4_lrat`], this emitter produces a self-contained Lean4
/// file that includes:
/// 1. The original clauses (as `List (ClauseId × Clause)`)
/// 2. The proof steps
/// 3. A definition of a propositional RUP checker (`lratCheck`)
/// 4. `theorem proof_valid : lratCheck originalClauses proofSteps = true`
///    closed by `native_decide`
///
/// The Lean4 kernel rejects the file if `lratCheck` evaluates to `false` on the
/// emitted data. Because this file also defines `lratCheck`, acceptance alone
/// does not prove UNSAT and must not authorize a solver verdict. Use
/// [`write_lean4_verified`] for that implication.
///
/// The clauses must use DIMACS literal encoding (positive int for positive
/// polarity of variable `v` = `v`, negative int for negated polarity).
/// Variable numbering follows DIMACS convention (starts at 1).
///
/// # Arguments
///
/// * `original_clauses` - slice of `(clause_id, dimacs_literals)` for every
///   original input clause referenced by the proof. Clause IDs must be unique
///   and must not collide with any `ProofStep::clause_id`.
/// * `steps` - LRAT proof steps produced by backward reconstruction.
/// * `writer` - output destination.
///
/// # Errors
///
/// Returns [`io::Error`] if writing fails.
pub(crate) fn write_lean4_lrat_kernel(
    original_clauses: &[(u64, Vec<i32>)],
    steps: &[ProofStep],
    writer: &mut dyn Write,
) -> io::Result<()> {
    // Header
    writeln!(
        writer,
        "-- Auto-generated LRAT proof from AY (kernel-checked; #8697)."
    )?;
    writeln!(
        writer,
        "-- Original clauses: {}, proof steps: {}",
        original_clauses.len(),
        steps.len()
    )?;
    writeln!(
        writer,
        "-- Checker: propositional RUP, verified by Lean 4 via native_decide."
    )?;
    writeln!(writer)?;
    writeln!(writer, "namespace AY.LratProof")?;
    writeln!(writer)?;

    // Self-contained kernel definitions.
    write_kernel_prelude(writer)?;

    // Emit original clauses.
    writeln!(
        writer,
        "/-- Original input clauses (DIMACS literal encoding). -/"
    )?;
    writeln!(
        writer,
        "def originalClauses : List (ClauseId × Clause) := ["
    )?;
    for (i, (cid, lits)) in original_clauses.iter().enumerate() {
        let lits_str = format_lean_int_list(lits);
        let comma = if i + 1 < original_clauses.len() {
            ","
        } else {
            ""
        };
        writeln!(writer, "  ({cid}, {lits_str}){comma}")?;
    }
    writeln!(writer, "]")?;
    writeln!(writer)?;

    // Emit proof steps.
    writeln!(
        writer,
        "/-- LRAT proof steps (each derives a new clause via RUP). -/"
    )?;
    writeln!(writer, "def proofSteps : List LratAddStep := [")?;
    for (i, step) in steps.iter().enumerate() {
        let lits = format_lean_int_list(&step.dimacs_literals());
        let hints = format_lean_hint_list(&step.hints);
        let comma = if i + 1 < steps.len() { "," } else { "" };
        writeln!(
            writer,
            "  {{ id := {}, clause := {lits}, hints := {hints} }}{comma}",
            step.clause_id
        )?;
    }
    writeln!(writer, "]")?;
    writeln!(writer)?;

    // The actual kernel-checked theorem. `native_decide` compiles `lratCheck`
    // to efficient code and evaluates it; if the result is not `true`, Lean
    // rejects the file.
    writeln!(
        writer,
        "/-- Soundness theorem: the emitted proof is a valid LRAT refutation."
    )?;
    writeln!(
        writer,
        "    If this definition fails to elaborate, the Lean kernel has rejected the proof. -/"
    )?;
    writeln!(
        writer,
        "theorem proof_valid : lratCheck originalClauses proofSteps = true := by native_decide"
    )?;
    writeln!(writer)?;

    writeln!(writer, "end AY.LratProof")?;
    Ok(())
}

/// Write a Lean4 UNSAT proof GROUNDED IN THE VERIFIED CHECKER SOUNDNESS THEOREM.
///
/// Unlike [`write_lean4_lrat_kernel`] (which re-defines an UNVERIFIED `lratCheck`
/// and only asserts `lratCheck … = true`, leaving acceptance⟹unsat untrusted),
/// this emitter imports the machine-checked `AySoundness.lratCheck_sound`
/// (`verification/lean/AySoundness/Lrat.lean`, `#print axioms` = `[propext,
/// Quot.sound]`) and produces a kernel-checked theorem
///
/// ```lean
/// theorem unsat : Unsat (clauses original) :=
///   lratCheck_sound (by decide) (by decide) proof_valid
/// ```
///
/// so the verdict's soundness rests only on the verified checker + Lean's kernel
/// — the solver's search is never trusted. `proof_valid` discharges the
/// per-problem `lratCheck … = true` by pure `decide`, under explicit finite
/// recursion and heartbeat ceilings (the native compiler is NOT in the TCB); its
/// proof-of-concept is `AySoundness/EndToEnd.lean`.
///
/// The emitted file `import`s `AySoundness.Lrat`, so it must be checked with the
/// `AySoundness` library on `LEAN_PATH` (e.g. built via the
/// `verification/lean` lake project), not as a free-standing `lean FILE`.
///
/// Same argument contract as [`write_lean4_lrat_kernel`].
pub(crate) fn write_lean4_verified(
    original_clauses: &[(u64, Vec<i32>)],
    steps: &[ProofStep],
    writer: &mut dyn Write,
) -> io::Result<()> {
    writeln!(writer, "import AySoundness.Lrat")?;
    writeln!(writer, "set_option maxRecDepth 100000")?;
    writeln!(writer, "set_option maxHeartbeats 10000000")?;
    writeln!(
        writer,
        "-- Auto-generated by AY. UNSAT grounded in the VERIFIED checker:"
    )?;
    writeln!(
        writer,
        "-- `AySoundness.lratCheck_sound` (machine-checked: accepts ⟹ Unsat)."
    )?;
    writeln!(
        writer,
        "-- Original clauses: {}, proof steps: {}.",
        original_clauses.len(),
        steps.len()
    )?;
    writeln!(writer, "open AySoundness")?;
    writeln!(writer, "namespace AY.LratProofVerified")?;
    writeln!(writer)?;

    // Original input clauses, in the verified checker's tuple format.
    writeln!(writer, "def original : List (Cid × Clause) := [")?;
    for (i, (cid, lits)) in original_clauses.iter().enumerate() {
        let lits_str = format_lean_int_list(lits);
        let comma = if i + 1 < original_clauses.len() {
            ","
        } else {
            ""
        };
        writeln!(writer, "  ({cid}, {lits_str}){comma}")?;
    }
    writeln!(writer, "]")?;
    writeln!(writer)?;

    // LRAT proof steps as `(id, clause, hints)` tuples.
    writeln!(writer, "def proof : List (Cid × Clause × List Int) := [")?;
    for (i, step) in steps.iter().enumerate() {
        let lits = format_lean_int_list(&step.dimacs_literals());
        let hints = format_lean_hint_list(&step.hints);
        let comma = if i + 1 < steps.len() { "," } else { "" };
        writeln!(writer, "  ({}, {lits}, {hints}){comma}", step.clause_id)?;
    }
    writeln!(writer, "]")?;
    writeln!(writer)?;

    // Per-problem certificate check (pure kernel reduction).
    writeln!(
        writer,
        "theorem proof_valid : lratCheck original proof = true := by decide"
    )?;
    // The grounded soundness theorem: acceptance ⟹ genuine unsatisfiability,
    // via the machine-checked `lratCheck_sound`.
    writeln!(
        writer,
        "/-- The input clause set is unsatisfiable — verified by Lean's kernel\n    through the machine-checked `lratCheck_sound`. -/"
    )?;
    writeln!(writer, "theorem unsat : Unsat (clauses original) :=")?;
    writeln!(
        writer,
        "  lratCheck_sound (original := original) (proof := proof) (by decide) (by decide) proof_valid"
    )?;
    writeln!(writer)?;
    writeln!(writer, "end AY.LratProofVerified")?;
    Ok(())
}

/// Write the self-contained Lean4 kernel definitions used by
/// [`write_lean4_lrat_kernel`]. The prelude defines the LRAT RUP checker
/// without relying on any external Lean libraries.
fn write_kernel_prelude(writer: &mut dyn Write) -> io::Result<()> {
    writeln!(
        writer,
        "/-- A literal is an integer: positive for variable, negative for negated variable. -/"
    )?;
    writeln!(writer, "abbrev Literal := Int")?;
    writeln!(writer, "abbrev Clause := List Literal")?;
    writeln!(writer, "abbrev ClauseId := Nat")?;
    writeln!(writer)?;
    writeln!(
        writer,
        "/-- An LRAT addition step: derives a new clause from antecedent hints. -/"
    )?;
    writeln!(writer, "structure LratAddStep where")?;
    writeln!(writer, "  id : ClauseId")?;
    writeln!(writer, "  clause : Clause")?;
    writeln!(writer, "  hints : List Int")?;
    writeln!(writer, "  deriving Repr, BEq")?;
    writeln!(writer)?;
    writeln!(writer, "def negLit (l : Literal) : Literal := -l")?;
    writeln!(writer, "abbrev Assign := List Literal")?;
    writeln!(
        writer,
        "def litTrue (a : Assign) (l : Literal) : Bool := a.contains l"
    )?;
    writeln!(
        writer,
        "def litFalse (a : Assign) (l : Literal) : Bool := a.contains (negLit l)"
    )?;
    writeln!(writer)?;
    writeln!(
        writer,
        "/-- Return the sole unassigned literal of c under a, if exactly one exists. -/"
    )?;
    writeln!(
        writer,
        "def findUnit : Assign -> Clause -> Option Literal -> Option Literal"
    )?;
    writeln!(writer, "  | _, [], unassigned => unassigned")?;
    writeln!(writer, "  | a, l :: rest, unassigned =>")?;
    writeln!(writer, "    if litTrue a l then none")?;
    writeln!(
        writer,
        "    else if litFalse a l then findUnit a rest unassigned"
    )?;
    writeln!(writer, "    else")?;
    writeln!(writer, "      match unassigned with")?;
    writeln!(writer, "      | none => findUnit a rest (some l)")?;
    writeln!(writer, "      | some _ => none")?;
    writeln!(writer)?;
    writeln!(
        writer,
        "def clauseFalsified (a : Assign) (c : Clause) : Bool := c.all (fun l => litFalse a l)"
    )?;
    writeln!(writer)?;
    writeln!(
        writer,
        "def lookupClause (table : List (ClauseId × Clause)) (id : ClauseId) : Option Clause :="
    )?;
    writeln!(
        writer,
        "  (table.find? (fun p => p.fst == id)).map (fun p => p.snd)"
    )?;
    writeln!(writer)?;
    writeln!(
        writer,
        "/-- Walk RUP hints: each hint's clause must become a unit (or conflict) under the"
    )?;
    writeln!(
        writer,
        "    accumulated assignment. Negative hints (RAT / deletion markers) are skipped. -/"
    )?;
    writeln!(
        writer,
        "def rupStep (table : List (ClauseId × Clause)) (a : Assign) (hints : List Int) : Bool :="
    )?;
    writeln!(writer, "  match hints with")?;
    writeln!(writer, "  | [] => false")?;
    writeln!(writer, "  | h :: rest =>")?;
    writeln!(writer, "    if h <= 0 then rupStep table a rest")?;
    writeln!(writer, "    else")?;
    writeln!(writer, "      let id := h.toNat")?;
    writeln!(writer, "      match lookupClause table id with")?;
    writeln!(writer, "      | none => false")?;
    writeln!(writer, "      | some c =>")?;
    writeln!(writer, "        if clauseFalsified a c then true")?;
    writeln!(writer, "        else")?;
    writeln!(writer, "          match findUnit a c none with")?;
    writeln!(writer, "          | none => false")?;
    writeln!(writer, "          | some l => rupStep table (l :: a) rest")?;
    writeln!(writer)?;
    writeln!(
        writer,
        "def rupCheck (table : List (ClauseId × Clause)) (target : Clause) (hints : List Int) : Bool :="
    )?;
    writeln!(writer, "  let init : Assign := target.map negLit")?;
    writeln!(writer, "  rupStep table init hints")?;
    writeln!(writer)?;
    writeln!(
        writer,
        "def checkStep (table : List (ClauseId × Clause)) (step : LratAddStep) : Bool :="
    )?;
    writeln!(writer, "  rupCheck table step.clause step.hints")?;
    writeln!(writer)?;
    writeln!(
        writer,
        "/-- Walk proof steps, extending the clause table. Require the final step to be [] . -/"
    )?;
    writeln!(
        writer,
        "def lratCheckAux : List (ClauseId × Clause) -> List LratAddStep -> Bool"
    )?;
    writeln!(writer, "  | _, [] => false")?;
    writeln!(
        writer,
        "  | table, [last] => last.clause.isEmpty && checkStep table last"
    )?;
    writeln!(writer, "  | table, s :: rest =>")?;
    writeln!(writer, "    if checkStep table s then")?;
    writeln!(
        writer,
        "      lratCheckAux ((s.id, s.clause) :: table) rest"
    )?;
    writeln!(writer, "    else")?;
    writeln!(writer, "      false")?;
    writeln!(writer)?;
    writeln!(
        writer,
        "def lratCheck (original : List (ClauseId × Clause)) (proof : List LratAddStep) : Bool :="
    )?;
    writeln!(writer, "  lratCheckAux original proof")?;
    writeln!(writer)?;
    Ok(())
}

/// Format a slice of `i32` as a Lean4 list of `Int`.
fn format_lean_int_list(values: &[i32]) -> String {
    if values.is_empty() {
        return "[]".to_string();
    }
    let items: Vec<String> = values.iter().map(ToString::to_string).collect();
    format!("[{}]", items.join(", "))
}

/// Format a slice of `u64` as a Lean4 list of `Nat`.
fn format_lean_nat_list(values: &[u64]) -> String {
    if values.is_empty() {
        return "[]".to_string();
    }
    let items: Vec<String> = values.iter().map(ToString::to_string).collect();
    format!("[{}]", items.join(", "))
}

/// Format a slice of `i64` LRAT hints as a Lean4 list of `Int`.
///
/// Positive values are clause-ID references; negative values are RAT witness
/// boundaries. Both are emitted as Lean4 integers.
fn format_lean_hint_list(values: &[i64]) -> String {
    if values.is_empty() {
        return "[]".to_string();
    }
    let items: Vec<String> = values.iter().map(ToString::to_string).collect();
    format!("[{}]", items.join(", "))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::{Literal, Variable};
    use crate::proof_certificate::{ProofCertificate, ProofCompleteness::Complete};
    use crate::solver::backward_proof::LratStep;

    fn make_small_unsat_steps() -> Vec<LratStep> {
        // Simple UNSAT proof for: (x) ^ (~x) = UNSAT
        // Original clause 1: [x]  (clause_id=1)
        // Original clause 2: [~x] (clause_id=2)
        // Derived step: empty clause from clauses 1 and 2
        vec![LratStep {
            clause_id: 3,
            literals: vec![],
            hints: vec![1i64, 2],
        }]
    }

    fn make_medium_unsat_steps() -> Vec<LratStep> {
        // Medium UNSAT proof:
        // Clause 1: [x, y]     (original, id=1)
        // Clause 2: [x, ~y]    (original, id=2)
        // Clause 3: [~x, y]    (original, id=3)
        // Clause 4: [~x, ~y]   (original, id=4)
        //
        // Step 5: [x] from clauses 1, 2 (resolve on y)
        // Step 6: [~x] from clauses 3, 4 (resolve on y)
        // Step 7: [] from steps 5, 6 (resolve on x)
        let v0 = Variable(0);
        vec![
            LratStep {
                clause_id: 5,
                literals: vec![Literal::positive(v0)],
                hints: vec![1i64, 2],
            },
            LratStep {
                clause_id: 6,
                literals: vec![Literal::negative(v0)],
                hints: vec![3i64, 4],
            },
            LratStep {
                clause_id: 7,
                literals: vec![],
                hints: vec![5i64, 6],
            },
        ]
    }

    #[test]
    fn test_lean4_export_empty_proof() {
        let cert = ProofCertificate::empty();
        let mut buf = Vec::new();
        cert.write_lean4(&mut buf)
            .expect("write_lean4 should succeed on empty proof");
        let output = String::from_utf8(buf).expect("should be valid UTF-8");
        assert!(
            output.contains("Empty proof"),
            "empty proof should indicate no steps"
        );
    }

    #[test]
    fn test_lean4_verified_emits_grounded_shape() {
        // (x) ∧ (¬x): clauses 1=[x], 2=[¬x]; proof derives the empty clause.
        let cert = ProofCertificate::from_backward_result(make_small_unsat_steps(), Complete);
        let originals: Vec<(u64, Vec<i32>)> = vec![(1, vec![1]), (2, vec![-1])];
        let mut buf = Vec::new();
        cert.write_lean4_verified(&originals, &mut buf)
            .expect("write_lean4_verified should succeed");
        let out = String::from_utf8(buf).expect("utf-8");
        assert!(
            out.contains("import AySoundness.Lrat"),
            "must import the verified checker:\n{out}"
        );
        assert!(
            out.contains("lratCheck_sound"),
            "must ground in lratCheck_sound:\n{out}"
        );
        assert!(
            out.contains("theorem unsat : Unsat (clauses original)"),
            "must conclude Unsat:\n{out}"
        );
        assert!(out.contains("set_option maxRecDepth 100000"));
        assert!(out.contains("set_option maxHeartbeats 10000000"));
        assert!(
            out.contains("proof_valid : lratCheck original proof = true"),
            "must check the certificate:\n{out}"
        );
        // Do not redefine lratCheck or use native_decide for soundness.
        assert!(
            !out.contains("native_decide"),
            "verified shape uses pure decide, not native_decide:\n{out}"
        );
        assert!(
            !out.contains("def lratCheck "),
            "must not re-define an unverified checker:\n{out}"
        );
    }

    #[test]
    fn test_lean4_export_small_unsat() {
        let cert = ProofCertificate::from_backward_result(make_small_unsat_steps(), Complete);
        let mut buf = Vec::new();
        cert.write_lean4(&mut buf)
            .expect("write_lean4 should succeed");
        let output = String::from_utf8(buf).expect("should be valid UTF-8");

        // Verify structural elements
        assert!(
            output.contains("namespace AY.LratProof"),
            "should have namespace declaration"
        );
        assert!(
            output.contains("abbrev Literal := Int"),
            "should define Literal type"
        );
        assert!(
            output.contains("structure LratAddStep"),
            "should define LratAddStep"
        );
        assert!(
            output.contains("def proofSteps"),
            "should define proofSteps"
        );
        assert!(
            output.contains("def emptyClauseId"),
            "should identify empty clause"
        );
        assert!(
            output.contains("end AY.LratProof"),
            "should close namespace"
        );

        // Verify the step content
        assert!(
            output.contains("id := 3"),
            "should contain clause_id 3 for the derived empty clause"
        );
        assert!(
            output.contains("clause := []"),
            "empty clause should have empty literal list"
        );
        assert!(
            output.contains("hints := [1, 2]"),
            "should reference original clauses 1 and 2"
        );

        // Original clause IDs
        assert!(
            output.contains("originalClauseIds"),
            "should list original clause IDs"
        );
    }

    #[test]
    fn test_lean4_export_medium_unsat() {
        let cert = ProofCertificate::from_backward_result(make_medium_unsat_steps(), Complete);
        let mut buf = Vec::new();
        cert.write_lean4(&mut buf)
            .expect("write_lean4 should succeed");
        let output = String::from_utf8(buf).expect("should be valid UTF-8");

        // Should have 3 proof steps
        assert!(
            output.contains("proofStepCount : Nat := 3"),
            "should report 3 proof steps, got: {output}"
        );

        // Step 5: [x] from 1, 2
        assert!(
            output.contains("id := 5"),
            "should contain step with clause_id 5"
        );

        // Step 7: empty clause
        assert!(
            output.contains("id := 7"),
            "should contain step with clause_id 7"
        );
        assert!(
            output.contains("emptyClauseId : ClauseId := 7"),
            "final step should be empty clause with id 7"
        );

        // Original clauses: 1, 2, 3, 4
        assert!(
            output.contains("[1, 2, 3, 4]"),
            "should reference original clauses 1-4"
        );
    }

    #[test]
    fn test_lean4_export_dimacs_literal_encoding() {
        // Verify that DIMACS encoding is used: variable 0 -> 1, variable 1 -> 2, etc.
        let v0 = Variable(0);
        let v1 = Variable(1);
        let steps = vec![
            LratStep {
                clause_id: 3,
                literals: vec![Literal::positive(v0), Literal::negative(v1)],
                hints: vec![1i64, 2],
            },
            LratStep {
                clause_id: 4,
                literals: vec![],
                hints: vec![3i64, 1],
            },
        ];
        let cert = ProofCertificate::from_backward_result(steps, Complete);
        let mut buf = Vec::new();
        cert.write_lean4(&mut buf)
            .expect("write_lean4 should succeed");
        let output = String::from_utf8(buf).expect("should be valid UTF-8");

        // Variable(0) positive -> DIMACS 1, Variable(1) negative -> DIMACS -2
        assert!(
            output.contains("[1, -2]"),
            "should encode literals as DIMACS integers, got: {output}"
        );
    }

    #[test]
    fn test_lean4_output_is_valid_lean_syntax() {
        // Basic syntactic validation: balanced braces, no obvious Lean parse errors
        let cert = ProofCertificate::from_backward_result(make_medium_unsat_steps(), Complete);
        let mut buf = Vec::new();
        cert.write_lean4(&mut buf)
            .expect("write_lean4 should succeed");
        let output = String::from_utf8(buf).expect("should be valid UTF-8");

        // Check balanced braces
        let open_braces = output.chars().filter(|&c| c == '{').count();
        let close_braces = output.chars().filter(|&c| c == '}').count();
        assert_eq!(
            open_braces, close_braces,
            "braces should be balanced: {open_braces} open, {close_braces} close"
        );

        // Check balanced brackets
        let open_brackets = output.chars().filter(|&c| c == '[').count();
        let close_brackets = output.chars().filter(|&c| c == ']').count();
        assert_eq!(
            open_brackets, close_brackets,
            "brackets should be balanced: {open_brackets} open, {close_brackets} close"
        );

        // No empty lines inside the list (would be a syntax error)
        let in_list = output
            .split("def proofSteps")
            .nth(1)
            .and_then(|s| s.split(']').next());
        if let Some(list_body) = in_list {
            assert!(
                !list_body.contains("\n\n"),
                "proof steps list should not contain empty lines"
            );
        }
    }

    // ----- Kernel-checked emitter (#8697) -----

    #[test]
    fn test_lean4_kernel_export_small_unsat() {
        // UNSAT from (x) AND (~x).
        let originals: Vec<(u64, Vec<i32>)> = vec![(1, vec![1]), (2, vec![-1])];
        let steps = make_small_unsat_steps();
        let cert = ProofCertificate::from_backward_result(steps, Complete);
        let mut buf = Vec::new();
        cert.write_lean4_kernel(&originals, &mut buf)
            .expect("kernel-checked emitter should succeed");
        let output = String::from_utf8(buf).expect("valid UTF-8");

        // Structural: must contain the kernel theorem.
        assert!(
            output.contains("theorem proof_valid"),
            "kernel output must contain proof_valid theorem"
        );
        assert!(
            output.contains("native_decide"),
            "kernel output must close theorem with native_decide"
        );
        assert!(
            output.contains("def lratCheck"),
            "kernel output must define lratCheck"
        );
        assert!(
            output.contains("def rupStep"),
            "kernel output must define rupStep"
        );
        // Original clause [1] must be present as Lean data.
        assert!(
            output.contains("(1, [1])"),
            "originalClauses must list clause id 1 with lit [1], got:\n{output}"
        );
        assert!(
            output.contains("(2, [-1])"),
            "originalClauses must list clause id 2 with lit [-1]"
        );
    }

    #[test]
    fn test_lean4_kernel_export_balanced_syntax() {
        let originals: Vec<(u64, Vec<i32>)> = vec![
            (1, vec![1, 2]),
            (2, vec![1, -2]),
            (3, vec![-1, 2]),
            (4, vec![-1, -2]),
        ];
        let steps = make_medium_unsat_steps();
        let cert = ProofCertificate::from_backward_result(steps, Complete);
        let mut buf = Vec::new();
        cert.write_lean4_kernel(&originals, &mut buf)
            .expect("kernel-checked emitter should succeed");
        let output = String::from_utf8(buf).expect("valid UTF-8");

        // Balanced delimiters.
        assert_eq!(
            output.chars().filter(|&c| c == '[').count(),
            output.chars().filter(|&c| c == ']').count(),
            "brackets must balance"
        );
        assert_eq!(
            output.chars().filter(|&c| c == '{').count(),
            output.chars().filter(|&c| c == '}').count(),
            "braces must balance"
        );
        assert_eq!(
            output.chars().filter(|&c| c == '(').count(),
            output.chars().filter(|&c| c == ')').count(),
            "parens must balance"
        );
        assert!(output.contains("namespace AY.LratProof"));
        assert!(output.contains("end AY.LratProof"));
    }

    #[test]
    fn test_lean4_kernel_export_empty_originals() {
        // Degenerate case: no original clauses (would never happen in
        // practice, but should still produce syntactically valid output).
        let originals: Vec<(u64, Vec<i32>)> = vec![];
        let steps = make_small_unsat_steps();
        let cert = ProofCertificate::from_backward_result(steps, Complete);
        let mut buf = Vec::new();
        cert.write_lean4_kernel(&originals, &mut buf)
            .expect("kernel-checked emitter should succeed on empty originals");
        let output = String::from_utf8(buf).expect("valid UTF-8");

        // `originalClauses` must still be emitted as the empty list.
        assert!(
            output.contains("def originalClauses : List (ClauseId × Clause) := [\n]"),
            "empty clause list must emit `:= [\\n]`, got:\n{output}"
        );
    }

    // ----- Legacy data-only emitter (#8253) -----

    #[test]
    fn test_format_lean_int_list_empty() {
        assert_eq!(format_lean_int_list(&[]), "[]");
    }

    #[test]
    fn test_format_lean_int_list_single() {
        assert_eq!(format_lean_int_list(&[42]), "[42]");
    }

    #[test]
    fn test_format_lean_int_list_multiple() {
        assert_eq!(format_lean_int_list(&[1, -2, 3]), "[1, -2, 3]");
    }

    #[test]
    fn test_format_lean_nat_list_empty() {
        assert_eq!(format_lean_nat_list(&[]), "[]");
    }

    #[test]
    fn test_format_lean_nat_list_multiple() {
        assert_eq!(format_lean_nat_list(&[1, 2, 3]), "[1, 2, 3]");
    }

    // ----- Lean4 kernel end-to-end verification (#8697, feature-gated) -----
    //
    // These tests require `lean` on PATH. They are behind the `lean-integration`
    // feature so that default `cargo test` does not depend on Lean4 being
    // installed. Run with:
    //     cargo test -p ay-sat --features lean-integration lean4_kernel_
    #[cfg(feature = "lean-integration")]
    mod lean_integration {
        use super::*;
        use std::process::Command;

        fn run_lean(source: &str) -> (std::process::ExitStatus, String) {
            let dir = tempfile::tempdir().expect("tempdir");
            let path = dir.path().join("proof.lean");
            let mut f = std::fs::File::create(&path).expect("create tmp");
            f.write_all(source.as_bytes()).expect("write tmp");
            drop(f);
            let out = Command::new("lean")
                .arg(&path)
                .output()
                .expect("failed to spawn `lean`; install via elan");
            let combined = format!(
                "{}{}",
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            );
            (out.status, combined)
        }

        #[test]
        fn test_lean4_kernel_accepts_valid_proof() {
            // (x) AND (~x) -> UNSAT, derived in one step.
            let originals: Vec<(u64, Vec<i32>)> = vec![(1, vec![1]), (2, vec![-1])];
            let steps = make_small_unsat_steps();
            let cert = ProofCertificate::from_backward_result(steps, Complete);
            let mut buf = Vec::new();
            cert.write_lean4_kernel(&originals, &mut buf)
                .expect("kernel emitter");
            let src = String::from_utf8(buf).expect("utf8");
            let (status, out) = run_lean(&src);
            assert!(
                status.success(),
                "Lean should accept valid proof, got:\n{out}\n---\nSource:\n{src}"
            );
        }

        #[test]
        fn test_lean4_kernel_accepts_medium_proof() {
            // (x,y) (x,~y) (~x,y) (~x,~y) -> UNSAT.
            let originals: Vec<(u64, Vec<i32>)> = vec![
                (1, vec![1, 2]),
                (2, vec![1, -2]),
                (3, vec![-1, 2]),
                (4, vec![-1, -2]),
            ];
            let steps = make_medium_unsat_steps();
            let cert = ProofCertificate::from_backward_result(steps, Complete);
            let mut buf = Vec::new();
            cert.write_lean4_kernel(&originals, &mut buf)
                .expect("kernel emitter");
            let src = String::from_utf8(buf).expect("utf8");
            let (status, out) = run_lean(&src);
            assert!(
                status.success(),
                "Lean should accept medium proof, got:\n{out}\n---\nSource:\n{src}"
            );
        }

        #[test]
        fn test_lean4_kernel_rejects_unsound_proof() {
            // Claim UNSAT for (x) alone, which is SAT. The emitted theorem
            // must be rejected by Lean's kernel.
            let originals: Vec<(u64, Vec<i32>)> = vec![(1, vec![1])];
            // Fake step: clause_id=2, empty clause, hint=1 only. Under RUP,
            // negating [] gives assign=[]; clause [1] is not falsified and
            // has unit l=1 -- but no more hints, so rupStep returns false.
            let steps: Vec<LratStep> = vec![LratStep {
                clause_id: 2,
                literals: vec![],
                hints: vec![1i64],
            }];
            let cert = ProofCertificate::from_backward_result(steps, Complete);
            let mut buf = Vec::new();
            cert.write_lean4_kernel(&originals, &mut buf)
                .expect("kernel emitter");
            let src = String::from_utf8(buf).expect("utf8");
            let (status, out) = run_lean(&src);
            assert!(
                !status.success(),
                "Lean should REJECT unsound proof, but accepted it. Output:\n{out}"
            );
            // Lean should specifically complain that `native_decide` evaluated
            // the proposition to false.
            assert!(
                out.contains("native_decide") || out.contains("is false"),
                "expected native_decide rejection message, got:\n{out}"
            );
        }
    }
}
