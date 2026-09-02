// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Certified-UNSAT orchestration for the DEC-LIN-CERT track: solve a PB
//! instance's CNF encoding with ay-sat (DRAT proof logging on), then lift the
//! DRAT refutation into a VeriPB v3 proof of the *original PB* instance's
//! unsatisfiability ([`super::drat_lift`]).
//!
//! This is option 2 of the CERT plan (proof-log the strong SAT-encoding path):
//! it reuses AY's strongest decision engine (ay-sat) plus its existing DRAT
//! emission, so the certified path is as capable as the uncertified one for the
//! aux-free instance class (and grows with the encoder-aux increments).
//!
//! SOUNDNESS: [`certify_decision_unsat`] returns proof *text* only; it is NOT
//! trusted until re-checked with the external VeriPB checker (verify-before-
//! claim). A `None` or a proof that fails to verify must never change the
//! reported SAT/UNSAT status — certification is strictly additive.

mod certified_bb;
mod clique_coloring;
mod cp_replay;
mod frustrated_cycle;
mod handshake_parity;
mod layered_pebbling;
mod lp_dual_floor;
mod odd_cycle_cover;

pub use clique_coloring::certify_opt_lin_clique_coloring;
pub use frustrated_cycle::certify_opt_lin_frustrated_cycle;
pub use handshake_parity::certify_opt_lin_handshake_parity;
pub use layered_pebbling::certify_opt_lin_layered_pebbling;
pub use odd_cycle_cover::certify_opt_lin_odd_cycle_cover;

use std::time::Instant;

use ay_sat::{Literal, ProofOutput, SatResult, Solver};

use super::drat_lift::{emit_decision_unsat_proof, parse_aux_free_drat};
use super::reified_encoding::{
    emit_sinz_introductions_pol_derived_weighted, encode_instance_proof_producing,
};
use super::route_budget::CertRouteBudget;
use super::steps::{ConstraintId, ProofStep};
use super::veripb::{
    format_lit, veripb_input_constraint_count, veripb_input_row_ids, write_opt_conclusion_hinted,
    VeriPbWriter,
};
use crate::encoding::CnfEncoder;
use crate::types::{PbConstraint, PbInstance, PbLit, PbObjective, PbRel, PbTerm};

/// Emits a direct OPT-LIN lower bound by reconstructing a tight complemented-space dual with checked non-negative arithmetic and bounded denominator.
/// `None` withholds only the certificate; returned text is untrusted until the external VeriPB verify-before-claim gate accepts it.
pub fn certify_opt_lin_lp_dual_floor(
    instance: &PbInstance,
    incumbent: &[bool],
    optimum: i128,
) -> Option<String> {
    lp_dual_floor::certify_opt_lin_lp_dual_floor(instance, incumbent, optimum)
}

/// Reports what the LP RELAXATION says about `optimum` — NOT whether the
/// emitter fired. Measurement-only.
///
/// READ THE NAME WITH CARE; it promises more than it delivers, and an audit
/// caught a census quoting it as emitter behaviour. It answers "is there an
/// LP-dual floor reaching the optimum, and if not why not", which is a fact
/// about the relaxation. Whether a CERTIFICATE is emitted additionally depends
/// on the incumbent, the denominator cap, and the search actually finishing —
/// `fx57`/`fx60` are the standing counterexamples: this reports a usable floor
/// while the run emits nothing, because what failed there was the search under
/// `--proof`, not the floor.
///
/// A future rename to `lp_relaxation_diagnosis` would be an improvement; it is
/// deferred only because the name appears in recorded measurements.
pub fn lp_dual_floor_diagnosis(instance: &PbInstance, optimum: i128) -> String {
    lp_dual_floor::lp_dual_floor_diagnosis(instance, optimum)
}

/// CERTIFIED LP BRANCH-AND-BOUND: an OPT-LIN optimality proof built from a
/// LITERAL SPLIT rather than from a structural fact, for the
/// `ceil(LP*) = optimum - 1` instances no cut and no counting argument reaches.
///
/// This is an ENGINE route, not a ninth family: it requires only `>=` rows and a
/// linear `min:` over plain positive literals. The full derivation, the two
/// defects it does not inherit from its prototype, and the deterministic COUNT
/// budgets are on [`certified_bb`].
///
/// `None` withholds only the certificate; returned text is untrusted until the
/// external VeriPB verify-before-claim gate accepts it.
pub fn certify_opt_lin_certified_bb(
    instance: &PbInstance,
    incumbent: &[bool],
    optimum: i128,
) -> Option<String> {
    certified_bb::certify_opt_lin_certified_bb(instance, incumbent, optimum)
}

/// Reports what [`certify_opt_lin_certified_bb`]'s search concluded, keeping
/// "this optimum is refuted BY A WITNESS" and "I could not close this tree in
/// budget" apart in writing. Measurement-only; never called by the certificate
/// chain.
pub fn certified_bb_diagnosis(instance: &PbInstance, incumbent: &[bool], optimum: i128) -> String {
    certified_bb::certified_bb_diagnosis(instance, incumbent, optimum)
}

/// Solve `instance` via its CNF encoding with DRAT proof logging and, on UNSAT,
/// return a VeriPB v3 proof text refuting the original PB instance. Returns
/// `None` when the instance is satisfiable, the solve is inconclusive, or the
/// encoding introduces auxiliary variables the lifter does not yet handle
/// (aux-free gate — the proof is withheld, the answer is not).
pub fn certify_decision_unsat(instance: &PbInstance) -> Option<String> {
    certify_decision_unsat_interruptible(instance, &|| false)
}

/// Like [`certify_decision_unsat`] but cooperatively interruptible via
/// `should_stop` (consulted during CNF encoding and the SAT solve), so it can be
/// driven under a competition deadline. Returns `None` if interrupted, SAT,
/// inconclusive, or not aux-free-liftable — the certificate is withheld, never a
/// wrong status.
pub fn certify_decision_unsat_interruptible(
    instance: &PbInstance,
    should_stop: &dyn Fn() -> bool,
) -> Option<String> {
    if should_stop() {
        return None;
    }
    // The proof-producing COMPACT path (Sinz encoding + `red` aux introductions)
    // now CERTIFIES each constraint's top register via a cutting-plane
    // (`pol`) telescope ([`emit_sinz_introductions_pol_derived_weighted`]) rather
    // than (unsoundly) asserting it: the final constraint-assertion unit `[r_top]`
    // is neither a definitional `red` (force-true proofgoal on the backward clause
    // is not auto-provable) nor RUP from {input PB row + definition}; it needs the
    // cutting-plane register⇔constraint bridge (Gocht & Nordström, "Certified CNF
    // Translations for Pseudo-Boolean Solving", SAT 2022). That telescope is now
    // implemented and VeriPB-verified for cardinality AND weighted PB.
    //
    // The compact path stays behind an opt-in env var so the DEFAULT (and
    // competition) behavior is the WORKING aux-free RUP lift — zero regression.
    // Under the flag, the compact route is tried FIRST and, when it cannot produce
    // a reliable certificate (its DRAT refutation learns clauses over Sinz aux
    // *registers*, which do not lift to PB-level RUP — see
    // [`certify_decision_unsat_compact`]), it returns `None` and we FALL BACK to
    // the aux-free path. So enabling the flag can only ADD certificates (it
    // certifies instances whose aux-free DRAT references aux vars and is therefore
    // declined), never remove one. Both routes are re-checked by the external
    // VeriPB checker before any CERTIFIED claim (verify-before-claim).
    // DEFAULT ON: try the compact path first (kill switch AY_PB_NO_COMPACT_CERT).
    // Safe to default-on because the liftability gate makes it strictly additive
    // (declines -> aux-free fallback; can only ADD certificates) and every claim
    // is re-checked by the external VeriPB checker. Validated: Hamming-20-10-05-10
    // (aux-free declined) now certifies via compact; Hamming-20-10-03-08 still
    // certifies via fallback with negligible overhead.
    if crate::ab_switches::get().compact_cert {
        if let Some(ppe) = encode_instance_proof_producing(instance) {
            if let Some(proof) = certify_decision_unsat_compact(instance, ppe, should_stop) {
                return Some(proof);
            }
            if should_stop() {
                return None;
            }
            // Compact declined (non-liftable aux-register DRAT, SAT, or interrupt):
            // fall through to the aux-free lift so we never regress an instance the
            // aux-free path could already certify.
        }
    }
    certify_decision_unsat_aux_free(instance, should_stop)
}

/// Compact (proof-producing Sinz) certified-UNSAT route. Solves the Sinz CNF with
/// DRAT logging, then emits a VeriPB proof = per-constraint `red` introductions of
/// the Sinz definition clauses + a cutting-plane derivation of each top register
/// `r_top >= 1` (so the encoding semantics are in the proof database) followed by
/// the lifted DRAT refutation.
///
/// Returns `None` on SAT / inconclusive / interrupt, OR when the DRAT refutation
/// is NOT liftable: the lift is gated at `num_pb_vars` (not `max_var`). The Sinz
/// telescope only certifies each row's *top register* `r_top >= 1` — it does NOT
/// reconstruct the full `r(i,j) <=> count` bridge as cutting planes — so a learned
/// clause over an intermediate Sinz *register* (`var > num_pb_vars`) is not
/// PB-level RUP and would fail VeriPB. When the SAT solver finds the contradiction
/// purely at the PB-variable level (no aux-register learned clauses), the DRAT
/// lifts 1:1 over {input rows + `red` Sinz defs + derived `r_top`s} and VeriPB
/// verifies. Otherwise we decline so the caller falls back to the aux-free lift —
/// `None` is a withheld certificate, never a wrong status.
fn certify_decision_unsat_compact(
    instance: &PbInstance,
    ppe: super::reified_encoding::ProofProducingEncoding,
    should_stop: &dyn Fn() -> bool,
) -> Option<String> {
    let proof = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(ppe.max_var as usize, proof);
    // Disable variable-introducing inprocessing: any solver variable above
    // `max_var` would not be in the VeriPB database (we only `red`-introduce the
    // encoding's aux vars), so the lift would reject it. With these off, every
    // learned clause is a RUP resolvent over {PB vars ∪ Sinz aux}.
    solver.set_sbva_enabled(false);
    solver.set_factor_enabled(false);
    solver.set_decompose_enabled(false);
    solver.set_condition_enabled(false);
    for clause in &ppe.clauses {
        let lits: Vec<Literal> = clause.iter().map(|&l| Literal::from_dimacs(l)).collect();
        solver.add_clause(lits);
    }

    let sat = solver.solve_interruptible(should_stop).into_inner();
    if ay_core::misc_cli_flags().cert_debug {
        eprintln!("c [cert/compact] sat result = {sat:?}");
    }
    if !matches!(sat, SatResult::Unsat(_)) {
        return None;
    }

    let drat = solver.take_proof_writer()?.into_vec().ok()?;
    if ay_core::misc_cli_flags().cert_debug {
        // Debug-only one-shot count; not worth a bytecount dependency.
        #[allow(clippy::naive_bytecount)]
        let lines = drat.iter().filter(|&&b| b == b'\n').count();
        eprintln!("c [cert/compact] drat bytes={} lines={lines}", drat.len());
    }
    // LIFTABILITY GATE (cheap, up front): the telescope only certifies each row's
    // TOP register, so the DRAT refutation lifts to PB-level RUP only if it never
    // learns a clause over an intermediate Sinz *register* (`var > num_pb_vars`).
    // Check that before doing the (potentially large) telescope work; if the DRAT
    // references aux vars, decline so the caller falls back to the aux-free lift.
    if parse_aux_free_drat(&drat, instance.num_vars).is_none() {
        if ay_core::misc_cli_flags().cert_debug {
            eprintln!(
                "c [cert/compact] DRAT references Sinz aux registers; not PB-RUP-liftable, \
                 declining (caller falls back to aux-free)"
            );
        }
        return None;
    }
    let f_count = veripb_input_constraint_count(instance).ok()?;
    let mut writer = VeriPbWriter::new(Vec::<u8>::new(), f_count).ok()?;
    // 1) For each Sinz encoding: `red`-introduce its definition clauses (so the
    //    encoding CNF is in the proof DB) AND **derive** its top register
    //    `r(n-1, rhs-1) >= 1` by a checked cutting-plane (`pol`) telescope from the
    //    (literal-normalized) input row + those definitions. This replaces the old
    //    `rup`/force-`red` assertion of `[r_top]`, which VeriPB rejected (the
    //    backward-clause proofgoal is not auto-provable; `r_top` is not RUP from
    //    {input row + defs}). With every Sinz definition `red`-introduced and each
    //    `r_top >= 1` derived, the proof DB now contains the full Sinz CNF
    //    semantics, so the PB-level DRAT lift in step 2 has the constraints it
    //    needs. `input_row_id` points straight at VeriPB's stored
    //    (literal-normalized) row — see `SinzConstraintCert` for why no extra
    //    normalization step is needed even for negative input coefficients.
    for cert in &ppe.encodings {
        emit_sinz_introductions_pol_derived_weighted(
            &mut writer,
            &cert.encoding,
            &cert.coeffs,
            &cert.lits,
            cert.rhs,
            cert.input_row_id,
        )
        .ok()?;
    }
    // 2) Lift the DRAT refutation as `rup` steps, gated at `num_pb_vars`. The
    //    telescope above only certified each row's TOP register `r_top >= 1`, not
    //    the full per-register `r(i,j) <=> count` bridge, so a learned clause over
    //    an intermediate Sinz *register* (`var > num_pb_vars`) would not be
    //    PB-level RUP. `emit_decision_unsat_proof` returns `None` in that case, so
    //    we decline (caller falls back to aux-free) rather than emit an
    //    unverifiable proof. When the contradiction is found purely over PB vars,
    //    every learned clause is RUP over {input rows + `red` Sinz defs + derived
    //    `r_top`s} and VeriPB verifies.
    let conclusion_id = emit_decision_unsat_proof(&mut writer, &drat, instance.num_vars).ok()??;
    writer.conclude_unsat(conclusion_id).ok()?;
    String::from_utf8(writer.into_inner()).ok()
}

/// Aux-free certified-UNSAT route (the original lift): solve the aux-free CNF
/// encoding with DRAT logging and lift it 1:1 to VeriPB `rup` steps. Used when
/// the compact encoder declines.
fn certify_decision_unsat_aux_free(
    instance: &PbInstance,
    should_stop: &dyn Fn() -> bool,
) -> Option<String> {
    let mut stop_for_encode = || should_stop();
    let encoded = CnfEncoder::encode_instance_interruptible(instance, &mut stop_for_encode)?;

    let proof = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(encoded.num_vars as usize, proof);
    // Disable variable-introducing inprocessing (SBVA / factoring / decomposition /
    // conditioning): these emit RAT clauses over fresh solver variables (index >
    // num_pb_vars) that the aux-free RUP lifter cannot translate. With them off,
    // every learned clause is a RUP resolvent over the original variables, so the
    // DRAT lifts 1:1 to VeriPB.
    solver.set_sbva_enabled(false);
    solver.set_factor_enabled(false);
    solver.set_decompose_enabled(false);
    solver.set_condition_enabled(false);
    for clause in &encoded.clauses {
        let lits: Vec<Literal> = clause.iter().map(|&l| Literal::from_dimacs(l)).collect();
        solver.add_clause(lits);
    }

    let sat = solver.solve_interruptible(should_stop).into_inner();
    if ay_core::misc_cli_flags().cert_debug {
        eprintln!("c [cert] sat result = {sat:?}");
    }
    if !matches!(sat, SatResult::Unsat(_)) {
        return None; // SAT / Unknown / interrupted: DRAT certifies UNSAT only.
    }

    let drat = solver.take_proof_writer()?.into_vec().ok()?;
    if ay_core::misc_cli_flags().cert_debug {
        // Debug-only one-shot count; not worth a bytecount dependency.
        #[allow(clippy::naive_bytecount)]
        let lines = drat.iter().filter(|&&b| b == b'\n').count();
        eprintln!("c [cert] drat bytes={} lines={lines}", drat.len());
    }

    let f_count = veripb_input_constraint_count(instance).ok()?;
    let mut writer = VeriPbWriter::new(Vec::<u8>::new(), f_count).ok()?;
    let conclusion_id = emit_decision_unsat_proof(&mut writer, &drat, instance.num_vars).ok()??;
    writer.conclude_unsat(conclusion_id).ok()?;
    String::from_utf8(writer.into_inner()).ok()
}

/// DEC-LIN-CERT, SAT verdicts: assemble a SOLUTION-ONLY VeriPB proof — no
/// derivation, just `output NONE` + `conclusion SAT : <witness>`. The checker
/// validates the witness against the ORIGINAL problem, and because the witness
/// is embedded in the conclusion (not `sol`-logged) the proof verifies
/// identically in checked and unchecked deletion modes.
///
/// Returns `None` (certificate withheld) if `assignment` does not cover
/// exactly the instance's declared variables or is infeasible — the caller
/// must never ship a witness it has not verified (belt), and the checker
/// re-validates regardless (braces).
///
/// Also withheld when the instance carries an OBJECTIVE. `conclusion SAT` is
/// a DECISION-only conclusion: VeriPB 3.0.2 rejects it outright against an OPB
/// with a `min:` line ("The 'conclusion SAT' can only be used for decision
/// instances, but the input problem contains an objective."). An optimization
/// instance needs a `conclusion BOUNDS` with a *derived* lower bound, which
/// this solution-only route cannot supply, so it fails closed rather than
/// shipping a proof the checker will reject.
pub fn solution_only_sat_proof(instance: &PbInstance, assignment: &[bool]) -> Option<String> {
    if instance.objective.is_some() {
        return None;
    }
    if assignment.len() != instance.num_vars as usize {
        return None;
    }
    if !crate::eval::verify_all_constraints(&instance.constraints, assignment) {
        return None;
    }
    let f_count = veripb_input_constraint_count(instance).ok()?;
    let mut writer = VeriPbWriter::new(Vec::<u8>::new(), f_count).ok()?;
    writer.conclude_sat(assignment).ok()?;
    String::from_utf8(writer.into_inner()).ok()
}

/// OPT-LIN-CERT: assemble a VeriPB *optimization* proof certifying that
/// `optimum` is the exact minimum of `instance`'s linear objective.
///
/// The certificate has two halves, mirroring the OPT-LIN-CERT lever:
///   1. **Upper bound (feasibility).** A `soli` (solution-improving) row logs the
///      `incumbent` model. VeriPB checks that model satisfies every input
///      constraint, records the upper bound `obj(incumbent) = optimum`, AND — the
///      key mechanism — adds the *objective-improving constraint* `obj <= optimum-1`
///      to its constraint database (see `solution_logging.rs`: it emits
///      `-Σ c_i x_i >= 1 + const - optimum`).
///   2. **Lower bound (certified UNSAT of "can we do strictly better").** We solve
///      the *augmented* instance `{instance ∧ obj <= optimum-1}` with ay-sat under
///      DRAT logging; on UNSAT we lift the refutation to VeriPB `rup` steps. Each
///      `rup` is checked against the whole current database — which already holds
///      the soli-added `obj <= optimum-1` row — so the lifted refutation closes
///      out the lower bound. The final empty clause makes the database
///      contradictory under `obj <= optimum-1`, which is exactly the lower-bound
///      justification VeriPB needs for `conclusion BOUNDS optimum optimum`.
///
/// Returns the proof *text* only (never trusted until re-checked by the external
/// VeriPB checker — verify-before-claim). Returns `None` (certificate withheld,
/// status unaffected) when: the instance has no objective; the incumbent does not
/// achieve `optimum`; the augmented refutation needs auxiliary variables the
/// aux-free lifter cannot yet express; or the augmented instance does not solve
/// to UNSAT within the deadline.
///
/// SOUNDNESS: every emitted line is either a `soli` (checked: the model must be
/// feasible and its value must match) or a `rup` (checked by VeriPB). No unchecked
/// assertion is emitted. The reported optimum is never changed by a `None` here.
pub fn certify_opt_lin_bounds(
    instance: &PbInstance,
    incumbent: &[bool],
    optimum: i128,
) -> Option<String> {
    certify_opt_lin_bounds_interruptible(instance, incumbent, optimum, &|| false)
}

/// Interruptible variant of [`certify_opt_lin_bounds`].
pub fn certify_opt_lin_bounds_interruptible(
    instance: &PbInstance,
    incumbent: &[bool],
    optimum: i128,
    should_stop: &dyn Fn() -> bool,
) -> Option<String> {
    if should_stop() {
        return None;
    }
    let objective = instance.objective.as_ref()?;
    // Only single-literal (linear) objective terms are handled by the
    // objective-improving expression we mirror here.
    if objective.terms.iter().any(|t| t.lits.len() != 1) {
        return None;
    }
    // The `soli` row must be a COMPLETE assignment over the instance's variables:
    // require the incumbent to cover exactly `num_vars` so every declared variable
    // is fixed (an incomplete soli row makes VeriPB reject the model).
    if incumbent.len() != instance.num_vars as usize {
        return None;
    }

    // Confirm the incumbent is feasible and achieves `optimum` (the soli row will
    // be rejected by VeriPB otherwise, but checking here keeps us fail-closed and
    // lets us decline cheaply).
    let value = evaluate_linear_objective(objective, incumbent)?;
    if value != optimum {
        return None;
    }
    if !crate::eval::verify_all_constraints(&instance.constraints, incumbent) {
        return None;
    }

    // Build the augmented instance {instance ∧ obj <= optimum-1}. The
    // objective-improving constraint in >= normal form is `-Σ c_i x_i >= 1 - optimum`
    // (i.e. `Σ c_i x_i <= optimum - 1`), exactly what `soli` adds to the database.
    let improving = objective_improving_constraint(objective, optimum);
    let mut augmented = instance.clone();
    augmented.constraints.push(improving);
    augmented.num_constraints = augmented.constraints.len() as u32;

    let mut stop_for_encode = || should_stop();
    let encoded = CnfEncoder::encode_instance_interruptible(&augmented, &mut stop_for_encode)?;

    let proof = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(encoded.num_vars as usize, proof);
    // Same inprocessing lockdown as the decision path: keep every learned clause a
    // RUP resolvent over the original PB variables so the DRAT lifts 1:1.
    solver.set_sbva_enabled(false);
    solver.set_factor_enabled(false);
    solver.set_decompose_enabled(false);
    solver.set_condition_enabled(false);
    for clause in &encoded.clauses {
        let lits: Vec<Literal> = clause.iter().map(|&l| Literal::from_dimacs(l)).collect();
        solver.add_clause(lits);
    }

    let sat = solver.solve_interruptible(should_stop).into_inner();
    if ay_core::misc_cli_flags().cert_debug {
        eprintln!("c [cert/opt] augmented sat result = {sat:?}");
    }
    if !matches!(sat, SatResult::Unsat(_)) {
        // Either the incumbent is NOT optimal (a strictly better solution exists),
        // or the solve was inconclusive. Withhold the certificate; never claim.
        return None;
    }

    let drat = solver.take_proof_writer()?.into_vec().ok()?;

    // Header counts only the ORIGINAL input rows; the `obj <= optimum-1` row is
    // contributed to the database by the `soli` rule, not by `f`.
    let f_count = veripb_input_constraint_count(instance).ok()?;
    let mut writer = VeriPbWriter::new(Vec::<u8>::new(), f_count).ok()?;

    // 1) Upper bound + objective-improving constraint: log the incumbent.
    writer
        .log_step(ProofStep::SolutionImproving(format_assignment(incumbent)))
        .ok()?;

    // 2) Lower bound: lift the augmented-instance refutation as `rup` steps. The
    //    soli-added `obj <= optimum-1` constraint is already in the database, so the
    //    refutation that used it verifies. `num_vars` gates on PB variables only —
    //    the augmented constraint shares the original variable set.
    let contradiction_id =
        emit_decision_unsat_proof(&mut writer, &drat, instance.num_vars).ok()??;

    // 3) Conclude BOUNDS optimum optimum, hinting the contradiction row for the
    //    lower bound and the incumbent for the upper bound so the conclusion
    //    verifies in unchecked-deletion mode too (where `soli`-logged solutions
    //    are discounted; see `conclude_opt_hinted`).
    writer.set_opt_bounds(optimum, optimum).ok()?;
    writer
        .conclude_opt_hinted(Some(contradiction_id), Some(&format_assignment(incumbent)))
        .ok()?;
    String::from_utf8(writer.into_inner()).ok()
}

/// OPT-LIN-CERT, PB-NATIVE lower bound: same two-halves certificate as
/// [`certify_opt_lin_bounds`], but the lower bound is closed by refuting the
/// augmented instance `{instance ∧ obj <= optimum-1}` with the NATIVE
/// proof-logging PB CDCL solver — checked cutting-planes (`pol`) and `rup`
/// steps over the ORIGINAL PB variables — instead of a CNF encoding plus a
/// DRAT lift.
///
/// # Why this route exists (the aux-heavy gap)
///
/// Both CNF lower-bound routes decline on rows that need aux-heavy encodings:
/// the compact (Sinz) route's aux count is `lits * rhs`, which blows
/// `PROOF_PRODUCING_AUX_BUDGET` for big thresholds (a single `>= 2^47` row is
/// enough), and the aux-free route declines because the solver's adder/BDD
/// encodings put aux variables in the learned DRAT clauses. The PB-native
/// refutation introduces NO auxiliary variables at all — conflict analysis
/// derives whatever addition/division/saturation cuts it needs and logs each
/// one as a checked step — so coefficient magnitude never forces a decline.
///
/// # Proof stream layout
///
///   1. Header `f f_count` (ORIGINAL rows only), then `soli(incumbent)`:
///      VeriPB re-validates the model, records the upper bound, and installs
///      the objective-improving row `obj <= optimum-1` at id `f_count+1` —
///      exactly the id the solver's imported-input map assigns the improving
///      row (it is pushed LAST onto the augmented instance), so solver and
///      checker stay in id lockstep
///      (`PbCdclSolver::with_appended_proof_tap_interruptible` verifies
///      the alignment before any step is emitted).
///   2. The solver's refutation of the augmented instance
///      (`PbCdclSolver::solve_refutation_only_interruptible`): every learned
///      constraint is a checked `pol`/`rup` step, ending in a derived
///      contradiction row (no conclusion block).
///   3. `conclusion BOUNDS optimum optimum`, hinted with the contradiction row
///      (lower bound) and the inline incumbent witness (upper bound) so the
///      conclusion also verifies in unchecked-deletion mode.
///
/// SOUNDNESS: returns proof *text* only — never trusted until re-checked by
/// the external VeriPB checker (verify-before-claim). Every emitted line is a
/// checked rule; a bug here can only make the checker reject (a withheld
/// certificate), never accept a false bound. Returns `None` (certificate
/// withheld, status unaffected) when: no objective; a non-linear objective
/// term; an incomplete, infeasible, or non-optimum incumbent; an
/// objective-negation overflow; the augmented instance does not refute within
/// the deadline; or any proof step fails to emit.
pub fn certify_opt_lin_bounds_pb(
    instance: &PbInstance,
    incumbent: &[bool],
    optimum: i128,
) -> Option<String> {
    certify_opt_lin_bounds_pb_interruptible(instance, incumbent, optimum, &|| false)
}

/// Interruptible variant of [`certify_opt_lin_bounds_pb`].
pub fn certify_opt_lin_bounds_pb_interruptible(
    instance: &PbInstance,
    incumbent: &[bool],
    optimum: i128,
    should_stop: &dyn Fn() -> bool,
) -> Option<String> {
    if should_stop() {
        return None;
    }
    let objective = instance.objective.as_ref()?;
    // Only single-literal (linear) objective terms are handled by the
    // objective-improving expression we mirror here.
    if objective.terms.iter().any(|t| t.lits.len() != 1) {
        return None;
    }
    // The `soli` row must be a COMPLETE assignment over the instance's variables.
    if incumbent.len() != instance.num_vars as usize {
        return None;
    }
    // Fail-closed: the incumbent must be feasible and achieve `optimum`, else
    // the soli row is rejected and the bound is wrong. Decline cheaply here.
    let value = evaluate_linear_objective(objective, incumbent)?;
    if value != optimum {
        return None;
    }
    if !crate::eval::verify_all_constraints(&instance.constraints, incumbent) {
        return None;
    }
    // `objective_improving_constraint` negates every coefficient and computes
    // `1 - optimum`; decline the (pathological) shapes where either overflows
    // i128 rather than wrap.
    if objective.terms.iter().any(|t| t.coeff == i128::MIN) {
        return None;
    }
    1i128.checked_sub(optimum)?;

    // Build the augmented instance {instance ∧ obj <= optimum-1}. The improving
    // row is pushed LAST so `build_imported_input_constraint_ids` assigns it
    // id `f_count+1` — exactly the id VeriPB's `soli` installs the same
    // constraint at. The objective is stripped: the lower bound is a pure
    // DECISION refutation.
    let improving = objective_improving_constraint(objective, optimum);
    let mut augmented = instance.clone();
    augmented.constraints.push(improving);
    augmented.num_constraints = augmented.constraints.len() as u32;
    augmented.objective = None;

    // Header counts only the ORIGINAL input rows; the `obj <= optimum-1` row is
    // contributed to the database by the `soli` rule, not by `f`. The sink is
    // shared so the proof text can be read back after the tap serializer (which
    // takes ownership of the writer) has drained.
    let f_count = veripb_input_constraint_count(instance).ok()?;
    let sink = SharedProofSink::default();
    let mut writer = VeriPbWriter::new(sink.clone(), f_count).ok()?;

    // 1) Upper bound: log the incumbent. VeriPB installs `obj <= optimum-1` at
    //    id f_count+1, matching the writer's allocated id, so the solver's id
    //    counter continues in lockstep with the checker's.
    writer
        .log_step(ProofStep::SolutionImproving(format_assignment(incumbent)))
        .ok()?;

    // 2) Lower bound: native PB refutation of the augmented instance, appended
    //    to the same stream through the PROOF TAP (the tap's dense proven
    //    round-to-one analysis derives the division-strengthened lemmas that
    //    huge-coefficient rows need; the legacy synchronous writer path cannot
    //    refute them in practical budgets). Every learned constraint is a
    //    checked `pol`/`rup` step over {input rows + soli row}; the
    //    contradiction row id is kept for the conclusion hint.
    let route_started = std::time::Instant::now();
    let mut solver = crate::cdcl::PbCdclSolver::with_appended_proof_tap_interruptible(
        &augmented,
        writer,
        should_stop,
    )
    .ok()?;
    let result = solver.solve_refutation_only_interruptible(should_stop);
    if ay_core::misc_cli_flags().cert_debug {
        eprintln!(
            "c [cert/opt-pb] augmented pb-cdcl result = {result:?} ({}ms)",
            route_started.elapsed().as_millis(),
        );
    }
    if !matches!(result, crate::cdcl::PbCdclResult::Unsatisfiable) {
        // The incumbent is NOT optimal (a strictly better solution exists) or
        // the solve was inconclusive: withhold the certificate, never claim.
        return None;
    }
    let contradiction_id = solver.take_unsat_contradiction_proof_id()?;
    // Claim-commit handshake: `conclude_proof` shuts the tap serializer down
    // (drain + flush) and surfaces any buffered proof error — a voided proof
    // must decline here, before the conclusion is appended.
    solver.conclude_proof().ok()?;
    drop(solver);

    // 3) Conclude BOUNDS optimum optimum with both verification hints (see the
    //    aux-free route): contradiction row for the lower bound, incumbent
    //    witness for the upper bound, keeping the conclusion checkable in
    //    unchecked-deletion mode. The tap protocol has no OPT conclusion record
    //    and the serializer consumed the writer, so the block is appended
    //    straight to the (fully drained) sink via the SHARED formatter that
    //    also backs `VeriPbWriter::conclude_opt_hinted`.
    {
        let mut tail = sink.clone();
        write_opt_conclusion_hinted(
            &mut tail,
            optimum,
            Some(contradiction_id),
            optimum,
            Some(&format_assignment(incumbent)),
        )
        .ok()?;
    }
    String::from_utf8(sink.take()?).ok()
}

/// Shared in-memory proof sink: lets [`certify_opt_lin_bounds_pb_interruptible`]
/// read the proof text back after the `VeriPbWriter` has been moved into — and
/// dropped by — the proof-tap serializer thread.
#[derive(Clone, Default)]
struct SharedProofSink(std::sync::Arc<std::sync::Mutex<Vec<u8>>>);

impl SharedProofSink {
    /// Takes the accumulated proof bytes. `None` only if the lock was poisoned
    /// (a panic mid-write), in which case the certificate is withheld.
    fn take(&self) -> Option<Vec<u8>> {
        let mut guard = self.0.lock().ok()?;
        Some(std::mem::take(&mut *guard))
    }
}

impl std::io::Write for SharedProofSink {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        let mut guard = self
            .0
            .lock()
            .map_err(|_| std::io::Error::other("proof sink lock poisoned"))?;
        guard.extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

/// `ceil(a / d)` for `d >= 1`, exact over `i128`.
fn ceil_div_i128(a: i128, d: i128) -> Option<i128> {
    if d < 1 {
        return None;
    }
    let q = a.checked_div_euclid(d)?;
    let r = a.checked_rem_euclid(d)?;
    if r == 0 {
        Some(q)
    } else {
        q.checked_add(1)
    }
}

/// DIRECT OPT-LIN-CERT lower bound: emit the Chvátal–Gomory *aggregation floor*
/// certificate straight to VeriPB `pol`, WITHOUT refuting the augmented instance.
///
/// The two `certify_opt_lin_bounds{,_compact}` routes prove the lower bound by
/// refuting `{constraints ∧ obj <= optimum-1}` with the SAT engine and lifting the
/// DRAT — which needs the refutation to be *found* in budget. For covering-style
/// instances a valid `Σ obj_c[v] x_v >= optimum` floor is instead a short cutting-
/// plane aggregation that AY already computes internally
/// ([`super::optimum_check::build_aggregation_floor_cert`]) but never *emitted*.
/// This closes that gap: it re-derives the same aggregation while tracking the
/// ORIGINAL constraint ids, emits it as `pol`, and adds the `soli`-installed
/// `obj <= optimum-1` row to reach the `0 >= 1` contradiction — a direct
/// `BOUNDS optimum optimum` proof VeriPB accepts.
///
/// Construction (mirrors `build_aggregation_floor_cert`, over the `>=` covering
/// rows whose every term is a plain positive literal that is also in the objective):
///   `colsum[v] = Σ row coeffs on v`, `rhs_sum = Σ rhs`,
///   `M = cs/cv = max_v colsum[v]/obj_c[v]`; ADD all rows, SCALE by `cv`,
///   DIVIDE (ceil) by `cs`, LIFT each var by `(obj_c[v] - ⌈cv·colsum[v]/cs⌉)·x_v`,
///   yielding EXACTLY `Σ obj_c[v] x_v >= ⌈cv·rhs_sum/cs⌉`. Emitted only when that
///   floor `== optimum` (so it certifies the incumbent) and the incumbent is
///   re-verified feasible with value `optimum` (the `soli` row).
///
/// SOUNDNESS: returns proof *text* only, re-checked by the external VeriPB checker
/// before any CERTIFIED claim. Every emitted `pol` step is an ADD / non-negative
/// SCALE / ceil-DIVIDE / `x>=0`-LIFT of rows entailed by the instance, so the
/// derivation is a valid cutting-plane proof of the floor; a wrong construction can
/// only make VeriPB reject (never accept a false bound). `None` = certificate
/// withheld, status unaffected.
pub fn certify_opt_lin_direct_aggregation_floor(
    instance: &PbInstance,
    incumbent: &[bool],
    optimum: i128,
) -> Option<String> {
    let objective = instance.objective.as_ref()?;
    // Objective must be a sum of plain positive literals (the liftable slice).
    let mut objc: std::collections::BTreeMap<u32, i128> = std::collections::BTreeMap::new();
    if objective.terms.is_empty() {
        return None;
    }
    for term in &objective.terms {
        let [lit] = term.lits.as_slice() else {
            return None;
        };
        if lit.negated || lit.var == 0 || term.coeff <= 0 {
            return None;
        }
        *objc.entry(lit.var).or_insert(0) = objc
            .get(&lit.var)
            .copied()
            .unwrap_or(0)
            .checked_add(term.coeff)?;
    }

    // The `soli` row must be a COMPLETE, feasible, optimum-achieving assignment.
    if incumbent.len() != instance.num_vars as usize {
        return None;
    }
    if evaluate_linear_objective(objective, incumbent)? != optimum {
        return None;
    }
    if !crate::eval::verify_all_constraints(&instance.constraints, incumbent) {
        return None;
    }

    // Select covering rows (same predicate as build_aggregation_floor_cert),
    // citing each row's VeriPB `f` id.
    //
    // NOT `idx + 1`. VeriPB imports an `=` row as TWO consecutive constraints
    // (the `>=` half then the `<=` half), so every equality BEFORE a selected
    // row shifts that row's id. `veripb_input_row_ids` is the one definition of
    // that map and shares `veripb_row_id_width` with the `f` header count, so
    // the header and the hints cannot disagree again. Before this, on
    // `normalized-fx57.opb` (57 equalities), the emitter cited id 3286 for the
    // row VeriPB had at 3343: a legal `pol` over the WRONG row, which parsed
    // fine and then failed the `conclusion BOUNDS` hint check.
    let row_ids = veripb_input_row_ids(instance).ok()?;
    let mut selected_ids: Vec<ConstraintId> = Vec::new();
    let mut colsum: std::collections::BTreeMap<u32, i128> = std::collections::BTreeMap::new();
    let mut rhs_sum: i128 = 0;
    for (idx, c) in instance.constraints.iter().enumerate() {
        if c.rel != PbRel::Ge || c.rhs <= 0 {
            continue;
        }
        let row_ok = c.terms.iter().all(|t| match t.lits.as_slice() {
            [lit] => !lit.negated && lit.var != 0 && t.coeff > 0 && objc.contains_key(&lit.var),
            _ => false,
        });
        if !row_ok {
            continue;
        }
        rhs_sum = rhs_sum.checked_add(c.rhs)?;
        for t in &c.terms {
            let v = t.lits[0].var;
            *colsum.entry(v).or_insert(0) =
                colsum.get(&v).copied().unwrap_or(0).checked_add(t.coeff)?;
        }
        selected_ids.push(*row_ids.get(idx)?);
    }
    if selected_ids.is_empty() || rhs_sum <= 0 || colsum.is_empty() {
        return None;
    }

    // M = cs/cv = max_v colsum[v]/objc[v], via exact cross-multiplication.
    let mut best_cs: i128 = 0;
    let mut best_cv: i128 = 1;
    for (&v, &cs) in &colsum {
        let cv = *objc.get(&v)?;
        if cs.checked_mul(best_cv)? > best_cs.checked_mul(cv)? {
            best_cs = cs;
            best_cv = cv;
        }
    }
    if best_cs < 1 {
        return None;
    }
    let floor = ceil_div_i128(rhs_sum.checked_mul(best_cv)?, best_cs)?;
    // Only a floor that MEETS the incumbent certifies OPTIMUM.
    if floor != optimum {
        return None;
    }

    // ---- Emit the VeriPB proof. ----
    let f_count = veripb_input_constraint_count(instance).ok()?;
    // Fail closed rather than cite a row VeriPB did not import. `row_ids` and
    // `f_count` come from the same width function, so this can only fire if
    // that shared definition is edited inconsistently — which is exactly the
    // class of change that produced the fx57 defect. Emitting nothing costs one
    // certificate; emitting a hint out of range costs a rejected proof next to
    // an `s OPTIMUM FOUND`.
    if selected_ids.iter().any(|id| id.get() > f_count) {
        return None;
    }
    let mut writer = VeriPbWriter::new(Vec::<u8>::new(), f_count).ok()?;

    // Upper bound: log the incumbent; VeriPB installs `obj <= optimum-1`.
    let soli_id = writer
        .log_step(ProofStep::SolutionImproving(format_assignment(incumbent)))
        .ok()?;

    // ADD all selected rows -> Σ colsum[v] x_v >= rhs_sum.
    let mut cur = if selected_ids.len() == 1 {
        selected_ids[0]
    } else {
        let mut expr = format!("{} {} +", selected_ids[0], selected_ids[1]);
        for &id in &selected_ids[2..] {
            expr.push_str(&format!(" {id} +"));
        }
        expr.push_str(" ;");
        writer.log_step(ProofStep::Polynomial(expr)).ok()?
    };
    // SCALE by cv (Multiply requires k >= 1; skip the no-op).
    if best_cv >= 2 {
        cur = writer.log_step(ProofStep::Multiply(cur, best_cv)).ok()?;
    }
    // DIVIDE (ceil) by cs.
    if best_cs >= 2 {
        cur = writer.log_step(ProofStep::Divide(cur, best_cs)).ok()?;
    }
    // LIFT each objective var up to its objective coefficient with `x_v >= 0`.
    for (&v, &want) in &objc {
        let cs_v = colsum.get(&v).copied().unwrap_or(0);
        let have = ceil_div_i128(cs_v.checked_mul(best_cv)?, best_cs)?;
        let lift = want.checked_sub(have)?;
        if lift < 0 {
            return None; // unsound shape (should not happen by the M bound)
        }
        if lift == 0 {
            continue;
        }
        let expr = if lift == 1 {
            format!("{cur} x{v} + ;")
        } else {
            format!("{cur} x{v} {lift} * + ;")
        };
        cur = writer.log_step(ProofStep::Polynomial(expr)).ok()?;
    }

    // The floor `Σ objc[v] x_v >= optimum` + the soli row `obj <= optimum-1`
    // (`-Σ objc[v] x_v >= 1 - optimum`) sum to `0 >= 1` — the contradiction that
    // closes the lower bound.
    let contradiction_id = writer.log_step(ProofStep::Addition(cur, soli_id)).ok()?;

    // Hint both conclusion sides (contradiction row + inline incumbent) so the
    // conclusion also verifies in unchecked-deletion mode, where soli-logged
    // solutions are discounted (see `conclude_opt_hinted`).
    writer.set_opt_bounds(optimum, optimum).ok()?;
    writer
        .conclude_opt_hinted(Some(contradiction_id), Some(&format_assignment(incumbent)))
        .ok()?;
    String::from_utf8(writer.into_inner()).ok()
}

/// TRIVIAL zero-floor OPT-LIN-CERT: when the optimum is 0 and the objective is a sum
/// of plain positive literals with non-negative coefficients, `obj >= 0` holds by
/// non-negativity of the variables alone — no constraints needed. Emit it as
/// `Σ c_j·(x_j >= 0)` and add the `soli`-installed `obj <= -1` to reach `0 >= 1`.
///
/// This is the floor the native path misses on fully-satisfiable instances (e.g. a WBO
/// with 0 falsified-soft cost after projection), where it otherwise falls back to an
/// unverifiable `rup >= 1`. Sound: `x_j >= 0` are the boolean lower-bound axioms and
/// every coefficient is `>= 0`, so the derivation is a valid CG proof of `obj >= 0`;
/// self-checked (the emitted floor equals the objective with RHS 0) before return.
pub fn certify_opt_lin_trivial_zero_floor(
    instance: &PbInstance,
    incumbent: &[bool],
    optimum: i128,
) -> Option<String> {
    if optimum != 0 {
        return None;
    }
    let objective = instance.objective.as_ref()?;
    // Objective: plain positive literals, non-negative coefficients, at least one > 0.
    let mut obj: std::collections::BTreeMap<u32, i128> = std::collections::BTreeMap::new();
    for term in &objective.terms {
        let [lit] = term.lits.as_slice() else {
            return None;
        };
        if lit.negated || lit.var == 0 || term.coeff < 0 {
            return None;
        }
        *obj.entry(lit.var).or_insert(0) = obj
            .get(&lit.var)
            .copied()
            .unwrap_or(0)
            .checked_add(term.coeff)?;
    }
    if obj.is_empty() || obj.values().all(|&c| c == 0) {
        return None;
    }
    let n = instance.num_vars as usize;
    if incumbent.len() != n {
        return None;
    }
    if evaluate_linear_objective(objective, incumbent)? != 0 {
        return None;
    }
    if !crate::eval::verify_all_constraints(&instance.constraints, incumbent) {
        return None;
    }

    let f_count = veripb_input_constraint_count(instance).ok()?;
    let mut writer = VeriPbWriter::new(Vec::<u8>::new(), f_count).ok()?;
    let soli_id = writer
        .log_step(ProofStep::SolutionImproving(format_assignment(incumbent)))
        .ok()?;
    // Σ c_j·(x_j >= 0)  =>  obj >= 0.
    let terms: Vec<(u32, i128)> = obj
        .iter()
        .filter(|&(_, &c)| c > 0)
        .map(|(&v, &c)| (v, c))
        .collect();
    let mut expr = if terms[0].1 == 1 {
        format!("x{}", terms[0].0)
    } else {
        format!("x{} {} *", terms[0].0, terms[0].1)
    };
    for &(v, c) in &terms[1..] {
        if c == 1 {
            expr.push_str(&format!(" x{v} +"));
        } else {
            expr.push_str(&format!(" x{v} {c} * +"));
        }
    }
    expr.push_str(" ;");
    let floor = writer.log_step(ProofStep::Polynomial(expr)).ok()?;
    let contradiction_id = writer.log_step(ProofStep::Addition(floor, soli_id)).ok()?;
    writer.set_opt_bounds(0, 0).ok()?;
    // Hinted conclusion: required in unchecked-deletion mode (see
    // `conclude_opt_hinted`).
    writer
        .conclude_opt_hinted(Some(contradiction_id), Some(&format_assignment(incumbent)))
        .ok()?;
    String::from_utf8(writer.into_inner()).ok()
}

/// STRONGLY-CORRELATED KNAPSACK optimality certificate — a CONSTANT-SIZE (13-line)
/// proof for the `knapPI_3` class that defeats LP floors and CDCL refutation alike.
///
/// # Recognized shape (fail-closed on anything else)
///
/// A SINGLE `>=` constraint that normalizes to a knapsack `Σ w_j x_j <= C`
/// (`w_j >= 1`), a plain single-literal objective `min Σ (-v_j) x_j` (maximize
/// `Σ v_j x_j`), with a UNIFORM surplus `K = v_j − w_j > 0` for every item, and the
/// cardinality bound EXACTLY tight: `C + K·k_max = −optimum`, where `k_max` is the
/// largest m with (sum of the m smallest weights) `<= C`.
///
/// # Certificate (verified end-to-end on the real 1000-item knapPI_3_200)
///
///   1. `soli(incumbent)` — installs `obj <= optimum−1`.
///   2. `red` reify `s := x_{n+1}` with the threshold pair
///      D3: `(k+1)·~s + Σx >= k+1` (s → at least k+1 chosen; witness `s -> 0`),
///      D4: `(n−k)·s + Σ~x >= n−k` (~s → at most k chosen; witness `s -> 1`).
///   3. `pol` shim derivation: `D3·w_(k+1) + Σ_light (w_(k+1)−w_i)·~x_i +
///      Σ_heavy (w_i−w_(k+1))·x_i + row` — the LP dual of "k+1 items weigh at least
///      the k+1 smallest" — yields `(k+1)·w_(k+1)·~s >= S_(k+1) − C > 0`.
///   4. `pol s <margin> d` — saturate + divide: `~s >= 1` (k+1 items cannot fit).
///   5. `pol D4 + (n−k)·(~s>=1)` — the CARDINALITY row `Σ~x >= n−k` (`Σx <= k`).
///   6. `pol row + K·cardinality` — the objective floor `obj >= optimum`; `+ soli`
///      → `0 >= 1`; hinted `conclusion BOUNDS`.
///
/// SOUNDNESS: proof text only, re-checked by VeriPB (verify-before-claim); the `red`
/// steps are definitional reifications over a FRESH variable (witness discharges the
/// proofgoals); every `pol` step is a non-negative combination / division of entailed
/// rows and literal axioms. All recognizer arithmetic is checked `i128`; any mismatch
/// (non-uniform K, non-tight bound, non-positive margin) declines — never a wrong claim.
pub fn certify_opt_lin_knapsack_cardinality(
    instance: &PbInstance,
    incumbent: &[bool],
    optimum: i128,
) -> Option<String> {
    let objective = instance.objective.as_ref()?;
    // Exactly one >= row; all single-literal plain-positive terms on row + objective.
    if instance.constraints.len() != 1 {
        return None;
    }
    let row = &instance.constraints[0];
    if row.rel != PbRel::Ge {
        return None;
    }
    let n = instance.num_vars as usize;
    if incumbent.len() != n || n == 0 {
        return None;
    }
    // Row must normalize to `Σ w_j x_j <= C` i.e. all row coeffs negative on plain
    // literals: -w_j x_j >= -C. (knapPI shape; decline anything else.)
    let mut w = vec![0i128; n + 1];
    for t in &row.terms {
        let [lit] = t.lits.as_slice() else {
            return None;
        };
        if lit.negated || lit.var == 0 || lit.var as usize > n || t.coeff >= 0 {
            return None;
        }
        if w[lit.var as usize] != 0 {
            return None; // duplicate var
        }
        w[lit.var as usize] = -t.coeff; // weight > 0
    }
    if row.rhs >= 0 {
        return None;
    }
    let cap = -row.rhs; // C > 0
                        // Objective: -v_j x_j per item, all vars covered, v_j > w_j with uniform K.
    let mut v = vec![0i128; n + 1];
    for t in &objective.terms {
        let [lit] = t.lits.as_slice() else {
            return None;
        };
        if lit.negated || lit.var == 0 || lit.var as usize > n || t.coeff >= 0 {
            return None;
        }
        if v[lit.var as usize] != 0 {
            return None;
        }
        v[lit.var as usize] = -t.coeff; // value > 0
    }
    let mut surplus: Option<i128> = None;
    for j in 1..=n {
        if w[j] <= 0 || v[j] <= 0 {
            return None; // every var must be a weighted, valued item
        }
        let k = v[j].checked_sub(w[j])?;
        if k <= 0 {
            return None;
        }
        match surplus {
            None => surplus = Some(k),
            Some(s) if s != k => return None, // non-uniform: decline
            _ => {}
        }
    }
    let surplus = surplus?;
    // k_max by sorted-prefix; margin from the (k_max+1)-th smallest.
    let mut order: Vec<usize> = (1..=n).collect();
    order.sort_by_key(|&j| (w[j], j));
    let mut acc: i128 = 0;
    let mut kmax = 0usize;
    for &j in &order {
        let next = acc.checked_add(w[j])?;
        if next <= cap {
            acc = next;
            kmax += 1;
        } else {
            break;
        }
    }
    if kmax == 0 || kmax >= n {
        return None; // degenerate: no cardinality argument
    }
    let w_k1 = w[order[kmax]]; // (k_max+1)-th smallest weight
    let s_k1 = acc.checked_add(w_k1)?; // sum of k_max+1 smallest
    let margin = s_k1.checked_sub(cap)?;
    if margin <= 0 {
        return None; // should be impossible by kmax construction; fail-closed
    }
    // The cardinality bound must be EXACTLY tight: optimum == -(C + K*kmax).
    let bound = cap.checked_add(surplus.checked_mul(i128::try_from(kmax).ok()?)?)?;
    if optimum != bound.checked_neg()? {
        return None;
    }
    // Incumbent must be feasible and achieve the optimum.
    if evaluate_linear_objective(objective, incumbent)? != optimum {
        return None;
    }
    if !crate::eval::verify_all_constraints(&instance.constraints, incumbent) {
        return None;
    }

    // ---- Emit ----
    let f_count = veripb_input_constraint_count(instance).ok()?; // = 1
    let mut writer = VeriPbWriter::new(Vec::<u8>::new(), f_count).ok()?;
    let soli_id = writer
        .log_step(ProofStep::SolutionImproving(format_assignment(incumbent)))
        .ok()?;
    let sv = n + 1; // fresh reification variable
    let k1 = kmax + 1;
    let nk = n - kmax;
    // D3: (k+1)~s + Σx >= k+1  (witness s -> 0 trivially satisfies it)
    let mut d3 = format!("+{k1} ~x{sv} ");
    for j in 1..=n {
        use std::fmt::Write as _;
        let _ = write!(d3, "+1 x{j} ");
    }
    use std::fmt::Write as _;
    let _ = write!(d3, ">= {k1} ");
    let d3_id = writer
        .log_step(ProofStep::Red(d3, format!("x{sv} -> 0 ;")))
        .ok()?;
    // D4: (n-k)s + Σ~x >= n-k  (witness s -> 1)
    let mut d4 = format!("+{nk} x{sv} ");
    for j in 1..=n {
        let _ = write!(d4, "+1 ~x{j} ");
    }
    let _ = write!(d4, ">= {nk} ");
    let d4_id = writer
        .log_step(ProofStep::Red(d4, format!("x{sv} -> 1 ;")))
        .ok()?;
    // Shim derivation: D3*w_k1 + light-shims + heavy-shims + row.
    let light: std::collections::BTreeSet<usize> = order[..kmax].iter().copied().collect();
    let mut expr = format!("{d3_id} {w_k1} *");
    for &j in &order[..kmax] {
        let d = w_k1 - w[j];
        if d == 1 {
            let _ = write!(expr, " ~x{j} +");
        } else if d > 1 {
            let _ = write!(expr, " ~x{j} {d} * +");
        }
    }
    for j in 1..=n {
        if light.contains(&j) {
            continue;
        }
        let d = w[j] - w_k1;
        if d == 1 {
            let _ = write!(expr, " x{j} +");
        } else if d > 1 {
            let _ = write!(expr, " x{j} {d} * +");
        }
    }
    let _ = write!(expr, " 1 + ;");
    let p1 = writer.log_step(ProofStep::Polynomial(expr)).ok()?;
    // saturate + divide by margin: ~s >= 1
    let p2 = writer
        .log_step(ProofStep::Polynomial(format!("{p1} s {margin} d ;")))
        .ok()?;
    // D4 + (n-k)*(~s >= 1): the cardinality row Σ~x >= n-k
    let p3 = writer
        .log_step(ProofStep::Polynomial(format!("{d4_id} {p2} {nk} * + ;")))
        .ok()?;
    // row + K*cardinality: the objective floor; then + soli -> contradiction
    let p4 = writer
        .log_step(ProofStep::Polynomial(format!("1 {p3} {surplus} * + ;")))
        .ok()?;
    let contradiction_id = writer.log_step(ProofStep::Addition(p4, soli_id)).ok()?;
    writer.set_opt_bounds(optimum, optimum).ok()?;
    writer
        .conclude_opt_hinted(Some(contradiction_id), Some(&format_assignment(incumbent)))
        .ok()?;
    String::from_utf8(writer.into_inner()).ok()
}

/// OPT-LIN-CERT, COMPACT lower bound: same two-halves certificate as
/// [`certify_opt_lin_bounds`], but the lower bound is closed by the COMPACT
/// (proof-producing Sinz) route (`certify_decision_unsat_compact`) instead of
/// the aux-free lift. This certifies optimization instances whose augmented
/// `{instance ∧ obj <= optimum-1}` refutation needs auxiliary register variables
/// the aux-free lifter cannot express (any `>=` direction with threshold `>= 2`,
/// including the objective-improving row itself once `optimum >= 3`).
///
/// # How the two halves are assembled into ONE VeriPB writer
///
///   1. **Upper bound.** `soli(incumbent)` logs the model AND makes VeriPB
///      auto-install the objective-improving constraint `obj <= optimum-1` into
///      its database. Empirically (VeriPB 3.0.2, `--trace`) that constraint is
///      assigned ConstraintId `f_count + 1` — the *next* id after the `f` input
///      rows — which is exactly the id [`VeriPbWriter`] allocates for the `soli`
///      step. So our id counter stays in lockstep with VeriPB's after the soli.
///   2. **Per-constraint Sinz introductions + top-register telescope.** For every
///      `>=` direction encoded by the compact encoder we `red`-introduce its Sinz
///      definition clauses and `pol`-derive its top register, via
///      `emit_sinz_introductions_pol_derived_weighted`. The improving row is the
///      LAST constraint of the augmented instance, so the compact encoder records
///      its `input_row_id` as `f_count + 1` — precisely the soli-installed id. The
///      same `obj <= optimum-1` constraint is therefore BOTH installed by `soli`
///      (id `f_count+1`) AND Sinz-encoded with its telescope reading from that id;
///      this redundancy is intended (the telescope reads the stored row, it does
///      not re-add it), and VeriPB accepts it.
///   3. **Lower bound.** The lifted augmented-instance DRAT refutation as `rup`
///      steps; every learned clause is RUP over {input rows + soli row + `red`
///      Sinz defs + derived top registers}.
///   4. `conclusion BOUNDS optimum optimum`.
///
/// # Liftability gate (why this can only ADD certificates)
///
/// The telescope only certifies each row's TOP register, not the full per-register
/// bridge, so a DRAT clause over an intermediate Sinz *register* would not be
/// PB-level RUP. We gate at `augmented.num_vars` (= `instance.num_vars`, since the
/// improving row introduces no new variables): if the refutation references any
/// Sinz aux register we return `None`. A `None` here is a withheld certificate; the
/// caller keeps the aux-free [`certify_opt_lin_bounds`] (and, ultimately, the
/// reported optimum) untouched. Every emitted proof is re-checked by the external
/// VeriPB checker before any CERTIFIED claim (verify-before-claim).
///
/// SOUNDNESS: returns proof *text* only. Returns `None` (certificate withheld,
/// status unaffected) when: no objective; a non-linear objective term; an
/// incomplete incumbent; the incumbent is infeasible or does not achieve
/// `optimum`; the compact encoder declines the augmented instance; the augmented
/// instance does not solve to UNSAT within the deadline; or the refutation is not
/// PB-RUP-liftable.
pub fn certify_opt_lin_bounds_compact(
    instance: &PbInstance,
    incumbent: &[bool],
    optimum: i128,
) -> Option<String> {
    certify_opt_lin_bounds_compact_interruptible(instance, incumbent, optimum, &|| false)
}

/// Interruptible variant of [`certify_opt_lin_bounds_compact`].
pub fn certify_opt_lin_bounds_compact_interruptible(
    instance: &PbInstance,
    incumbent: &[bool],
    optimum: i128,
    should_stop: &dyn Fn() -> bool,
) -> Option<String> {
    if should_stop() {
        return None;
    }
    let objective = instance.objective.as_ref()?;
    // Only single-literal (linear) objective terms are handled by the
    // objective-improving expression we mirror here.
    if objective.terms.iter().any(|t| t.lits.len() != 1) {
        return None;
    }
    // The `soli` row must be a COMPLETE assignment over the instance's variables.
    if incumbent.len() != instance.num_vars as usize {
        return None;
    }
    // Fail-closed: the incumbent must be feasible and achieve `optimum`, else the
    // soli row is rejected and the bound is wrong. Decline cheaply here.
    let value = evaluate_linear_objective(objective, incumbent)?;
    if value != optimum {
        return None;
    }
    if !crate::eval::verify_all_constraints(&instance.constraints, incumbent) {
        return None;
    }

    // Build the augmented instance {instance ∧ obj <= optimum-1}. The improving row
    // is pushed LAST so the compact encoder assigns it `input_row_id = f_count+1`,
    // which is exactly the id VeriPB's `soli` installs the same constraint at.
    let improving = objective_improving_constraint(objective, optimum);
    let mut augmented = instance.clone();
    augmented.constraints.push(improving);
    augmented.num_constraints = augmented.constraints.len() as u32;

    // Encode the AUGMENTED instance COMPACT (Sinz). Decline (-> caller's aux-free
    // path) if the compact encoder cannot express this shape.
    let ppe = encode_instance_proof_producing(&augmented)?;
    if should_stop() {
        return None;
    }

    let proof = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = Solver::with_proof_output(ppe.max_var as usize, proof);
    // Inprocessing lockdown: any solver variable above `max_var` would not be in
    // the VeriPB database (we only `red`-introduce the encoding's aux registers),
    // so the lift would reject it. With these off, every learned clause is a RUP
    // resolvent over {PB vars ∪ Sinz aux}.
    solver.set_sbva_enabled(false);
    solver.set_factor_enabled(false);
    solver.set_decompose_enabled(false);
    solver.set_condition_enabled(false);
    for clause in &ppe.clauses {
        let lits: Vec<Literal> = clause.iter().map(|&l| Literal::from_dimacs(l)).collect();
        solver.add_clause(lits);
    }

    let sat = solver.solve_interruptible(should_stop).into_inner();
    if ay_core::misc_cli_flags().cert_debug {
        eprintln!("c [cert/opt-compact] augmented sat result = {sat:?}");
    }
    if !matches!(sat, SatResult::Unsat(_)) {
        // The incumbent is NOT optimal (a strictly better solution exists) or the
        // solve was inconclusive: withhold the certificate, never claim.
        return None;
    }

    let drat = solver.take_proof_writer()?.into_vec().ok()?;
    if ay_core::misc_cli_flags().cert_debug {
        // Debug-only one-shot count; not worth a bytecount dependency.
        #[allow(clippy::naive_bytecount)]
        let lines = drat.iter().filter(|&&b| b == b'\n').count();
        eprintln!(
            "c [cert/opt-compact] drat bytes={} lines={lines}",
            drat.len()
        );
    }
    // LIFTABILITY GATE: the telescope only certifies each row's TOP register, so the
    // DRAT lifts to PB-level RUP only if it never learns a clause over an
    // intermediate Sinz register (`var > num_vars`). The improving row adds no new
    // variable, so the PB-variable bound is `instance.num_vars`. Decline (caller
    // falls back to the aux-free opt-cert) when the refutation touches aux.
    if parse_aux_free_drat(&drat, instance.num_vars).is_none() {
        if ay_core::misc_cli_flags().cert_debug {
            eprintln!(
                "c [cert/opt-compact] DRAT references Sinz aux registers; not PB-RUP-liftable, \
                 declining (caller falls back to aux-free opt-cert)"
            );
        }
        return None;
    }

    // Header counts only the ORIGINAL input rows; the `obj <= optimum-1` row is
    // contributed by `soli`, not by `f`.
    let f_count = veripb_input_constraint_count(instance).ok()?;
    let mut writer = VeriPbWriter::new(Vec::<u8>::new(), f_count).ok()?;

    // 1) Upper bound: log the incumbent. VeriPB installs `obj <= optimum-1` at id
    //    f_count+1; this matches the writer's next allocated id, keeping our id
    //    counter in lockstep with VeriPB's for the telescope `pol` references.
    writer
        .log_step(ProofStep::SolutionImproving(format_assignment(incumbent)))
        .ok()?;

    // 2) For each Sinz encoding: `red`-introduce its definition clauses and
    //    `pol`-derive its top register from the (literal-normalized) input row +
    //    those definitions. The improving row's `input_row_id` is f_count+1 — the
    //    soli-installed constraint — so its telescope reads the soli row.
    for cert in &ppe.encodings {
        emit_sinz_introductions_pol_derived_weighted(
            &mut writer,
            &cert.encoding,
            &cert.coeffs,
            &cert.lits,
            cert.rhs,
            cert.input_row_id,
        )
        .ok()?;
    }

    // 3) Lower bound: lift the augmented refutation as `rup` steps, gated at
    //    `num_vars`. Every learned clause is RUP over {input rows + soli row +
    //    `red` Sinz defs + derived top registers}; if any clause references an aux
    //    register, `emit_decision_unsat_proof` returns None and we decline.
    let contradiction_id =
        emit_decision_unsat_proof(&mut writer, &drat, instance.num_vars).ok()??;

    // 4) Conclude BOUNDS optimum optimum with both verification hints (see the
    //    aux-free route): contradiction row for the lower bound, incumbent
    //    witness for the upper bound, keeping the conclusion checkable in
    //    unchecked-deletion mode.
    writer.set_opt_bounds(optimum, optimum).ok()?;
    writer
        .conclude_opt_hinted(Some(contradiction_id), Some(&format_assignment(incumbent)))
        .ok()?;
    String::from_utf8(writer.into_inner()).ok()
}

/// `true` iff `assignment` is complete for the instance and satisfies every row.
///
/// Shared by every STRUCTURAL certifier (`frustrated_cycle`, `odd_cycle_cover`).
/// It is the only thing standing between a bogus incumbent and a published
/// `conclusion BOUNDS opt <= obj <= opt`, so it is deliberately independent of
/// however the solver decided the point was feasible, and it is deliberately in
/// ONE place: a second copy is a second chance to get the completeness test or
/// the `Eq` case wrong in a file nobody diffs against the first.
pub(super) fn incumbent_is_feasible(instance: &PbInstance, assignment: &[bool]) -> bool {
    if assignment.len() < instance.num_vars as usize {
        return false;
    }
    instance.constraints.iter().all(|constraint| {
        let mut total: i128 = 0;
        for term in &constraint.terms {
            let mut satisfied = true;
            for lit in &term.lits {
                let Some(&value) = assignment.get((lit.var as usize).wrapping_sub(1)) else {
                    return false;
                };
                if !(value ^ lit.negated) {
                    satisfied = false;
                    break;
                }
            }
            if satisfied {
                total += term.coeff;
            }
        }
        match constraint.rel {
            PbRel::Ge => total >= constraint.rhs,
            PbRel::Eq => total == constraint.rhs,
        }
    })
}

/// Evaluates a linear (single-literal-term) objective under `assignment`
/// (`assignment[v-1]` is the value of variable `v`). Returns `None` if a literal
/// references a variable outside the assignment.
fn evaluate_linear_objective(objective: &PbObjective, assignment: &[bool]) -> Option<i128> {
    let mut value: i128 = 0;
    for term in &objective.terms {
        let lit = term.lits.first()?;
        let var_value = *assignment.get((lit.var as usize).checked_sub(1)?)?;
        let lit_true = var_value ^ lit.negated;
        if lit_true {
            value += term.coeff;
        }
    }
    Some(value)
}

/// Builds the objective-improving constraint `Σ c_i x_i <= optimum - 1`, expressed
/// in `>=` normal form (`PbRel::Ge`) as `Σ (-c_i) x_i >= 1 - optimum`. This is the
/// exact constraint VeriPB's `soli` rule installs in its database, so the augmented
/// instance's CNF encoding (and hence the lifted refutation) lines up with it.
fn objective_improving_constraint(objective: &PbObjective, optimum: i128) -> PbConstraint {
    let terms = objective
        .terms
        .iter()
        .filter_map(|t| {
            let lit = t.lits.first()?;
            Some(PbTerm {
                coeff: -t.coeff,
                lits: vec![PbLit {
                    var: lit.var,
                    negated: lit.negated,
                }],
            })
        })
        .collect();
    PbConstraint {
        terms,
        rel: PbRel::Ge,
        rhs: 1 - optimum,
    }
}

/// Formats a complete assignment as a space-separated VeriPB literal list (no
/// trailing `;`), as `SolutionImproving` expects. `assignment[v-1]` is variable
/// `v`'s value.
fn format_assignment(assignment: &[bool]) -> String {
    let mut out = String::new();
    for (index, &value) in assignment.iter().enumerate() {
        if !out.is_empty() {
            out.push(' ');
        }
        out.push_str(&format_lit(PbLit {
            var: (index + 1) as u32,
            negated: !value,
        }));
    }
    out
}

/// The name of the OPT-LIN certificate route that produced a proof.
///
/// Diagnostics only: which route fired never changes a verdict, an objective or
/// a byte of stdout. It exists so a miss can be attributed to a route instead of
/// to "the chain", which is what the coverage census had to reconstruct by hand.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OptLinCertRoute {
    /// `obj >= 0` for a non-negative objective whose optimum is 0.
    TrivialZeroFloor,
    /// The knapsack cardinality floor (the knapPI class).
    KnapsackCardinality,
    /// The clique-colouring structural floor, whose LP dual is always 0.
    CliqueColoring,
    /// The equality-handshake parity structural floor (`evencolouring`), whose
    /// LP dual is always 0 because the fractional edge point is feasible at
    /// cost 0; the odd handshake total is invisible to the relaxation.
    HandshakeParity,
    /// A direct Chvátal-Gomory aggregation floor; no refutation needed.
    DirectAggregationFloor,
    /// The exact rational LP dual, un-complemented into instance rows.
    LpDualFloor,
    /// The signed-graph frustration-index structural floor, whose LP dual is
    /// always 0 because the half-integral sign point is feasible at cost 0.
    FrustratedCycle,
    /// The odd-cycle vertex-cover structural floor, whose LP dual is capped at
    /// `V/2` because the all-half point is feasible, strictly below the optimum.
    OddCycleCover,
    /// The layered group-division DAG floor (`linearized_pebbling`), whose LP
    /// dual is capped strictly below the optimum because the per-group halves
    /// the LP must carry are re-rounded by DIVISION at every group.
    LayeredPebbling,
    /// Certified LP branch-and-bound: a LITERAL split whose leaves close as
    /// clauses and resolve to the empty clause. The only ENGINE route — it
    /// needs no structural fact, only `>=` rows and a linear `min:`.
    CertifiedBb,
    /// Augmented-instance refutation lifted through the compact Sinz encoding.
    BoundsCompact,
    /// Augmented-instance refutation lifted aux-free.
    Bounds,
    /// Augmented-instance refutation by the proof-logging PB-native CDCL.
    BoundsPbNative,
}

/// SEARCH rungs in the OPT-LIN chain — `bounds_compact`, `bounds` (aux-free)
/// and `bounds_pb` — i.e. the ones that consult `should_stop` and can therefore
/// consume a budget. The eight floor rungs are pure arithmetic (or count-bounded
/// structure recovery) and are NOT scheduled, so they are not counted here.
const OPT_LIN_SEARCH_ROUTES: u32 = 3;

impl OptLinCertRoute {
    /// Stable kebab-case label, for `--cert-debug` output and reports.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::TrivialZeroFloor => "trivial-zero-floor",
            Self::KnapsackCardinality => "knapsack-cardinality",
            Self::CliqueColoring => "clique-coloring",
            Self::HandshakeParity => "handshake-parity",
            Self::DirectAggregationFloor => "direct-aggregation-floor",
            Self::LpDualFloor => "lp-dual-floor",
            Self::FrustratedCycle => "frustrated-cycle",
            Self::OddCycleCover => "odd-cycle-cover",
            Self::LayeredPebbling => "layered-pebbling",
            Self::CertifiedBb => "certified-bb",
            Self::BoundsCompact => "bounds-compact",
            Self::Bounds => "bounds-auxfree",
            Self::BoundsPbNative => "bounds-pb-native",
        }
    }
}

/// THE OPT-LIN certificate chain: every floor/refutation route this crate has,
/// in the one order that is allowed to exist, tried cheapest-first.
///
/// # Why this function exists
///
/// Until this was factored out, the chain lived as hand-copied `.or_else(...)`
/// ladders inside `crates/ay-pb/src/bin/ay.rs` — and only there. Each new
/// emitter (`trivial_zero_floor`, `knapsack_cardinality`,
/// `direct_aggregation_floor`, `lp_dual_floor`, `bounds_pb`, `clique_coloring`)
/// was wired into that binary's two copies and into no other caller, so the
/// SHIPPED CLI (`crates/ay/src/cmd_pb.rs`), which had forked the ladder back
/// when it had only two rungs, silently kept a two-route chain while the
/// competition binary grew to eight. Measured consequence: on the same
/// instances at the same budget, `ay-pb` certified nine optima the CLI did not,
/// and none the other way round.
///
/// A chain that is copied is a chain that drifts. This is the single definition;
/// callers get new routes by existing.
///
/// # Order
///
/// Strictly cheapest-first, so an expensive route can never eat the budget of a
/// cheap one that would have succeeded:
///
/// 1. `trivial_zero_floor` — O(n) syntactic, optimum-0 non-negative objectives.
/// 2. `knapsack_cardinality` — O(n log n), the knapPI class, ~13 lines of proof.
/// 3. `clique_coloring` — O(1) header pre-gate; the structural family whose LP
///    relaxation *and* full level-1 RLT lift are both exactly 0, so no dual
///    floor can ever fire on it.
/// 4. `handshake_parity` — O(1) header pre-gate (`|objective| == #constraint`);
///    the equality-handshake family (`evencolouring`), where summing every row
///    cancels each edge variable into an even coefficient against an ODD
///    right-hand-side total, so the slack sum is odd and `obj >= min_v w_v` —
///    a parity the LP relaxation (exactly 0 at the fractional edge point)
///    cannot express and one cutting-planes division extracts. Pure single-pass
///    arithmetic, no search.
/// 5. `direct_aggregation_floor` — a short Chvátal-Gomory aggregation, no SAT
///    refutation needed; certifies covering-tight optima the refutations cannot
///    reach in budget.
/// 6. `lp_dual_floor` — the exact rational LP dual, un-complemented; the only
///    route for tight-LP maximisation optima.
/// 7. `frustrated_cycle` — O(1) header pre-gate; the signed-graph frustration
///    index, whose LP relaxation is exactly 0 at the half-integral sign point,
///    so no dual floor can ever fire on it either. Late among the floor rungs
///    because its on-family cost is a search rather than a formula: every
///    cheaper route gets its chance first, and off-family instances pay three
///    integer comparisons.
/// 8. `odd_cycle_cover` — O(1) header pre-gate plus an O(1) first-row probe;
///    pure minimum vertex cover, certified by disjoint odd-cycle cuts plus a
///    maximum matching. `ceil(LP*) < optimum` throughout the family, so no
///    dual floor reaches it. LAST of the floor rungs, for `frustrated_cycle`'s
///    reason: its on-family cost is a (count-bounded) search.
/// 9. `bounds_compact` — augmented refutation with Sinz aux registers (broadest
///    refutation coverage).
/// 10. `bounds` — the aux-free lift.
/// 11. `bounds_pb` — PB-native refutation; last, so it can only ADD
///    certificates the CNF routes declined.
///
/// # Budget
///
/// TWO KINDS OF RUNG, AND THEY ARE SCHEDULED DIFFERENTLY.
///
/// Routes 1-8 are pure arithmetic on the instance and the incumbent: they do not
/// consult `should_stop`. They are called DIRECTLY, outside the scheduler, and
/// that is deliberate and load-bearing — a caller whose deadline has already
/// passed still gets every floor route. Gating them behind a budget that can be
/// zero would LOSE certificates the CLI gets today;
/// `floor_routes_still_fire_with_an_already_expired_deadline` is the regression
/// test.
///
/// Rungs 6-8 (`lp_dual_floor`, `frustrated_cycle`, `odd_cycle_cover`) are the
/// ones whose on-family cost is not a formula: they run a simplex, separate
/// cycles, or solve a packing (LP, respectively matching). All three are
/// bounded by deterministic COUNTS (`MAX_DUAL_SOLVE_POLLS` stop polls for the
/// dual solve; rows, pool, rounds, pivots — and in `odd_cycle_cover` the
/// Hopcroft-Karp and two-colour phases charge the same relaxation budget)
/// rather than by a clock, precisely so that they can live outside the
/// scheduler without either eating a budget or making the emitted bytes depend
/// on machine load. `lp_dual_floor` learned this the measured way: its budget
/// used to be a private one-minute WALL deadline taken at rung entry, which is
/// how a 5 s `--timeout` proof run spent 60-65 s (2026-08-29 definitive
/// census: `aim-200-2_0-yes1-2`, `knapPI_11_1000_1000_5`,
/// `mult_diagcomm_..._nbits_16`) and then failed to certify anyway.
/// Off-family instances never reach that work: cheap structural gates decide
/// it.
///
/// Routes 9-11 are SEARCH, and they are the ones that can eat a chain. Each gets
/// a deadline of its own out of `deadline` via [`CertRouteBudget`]: rung `i` of
/// `n` remaining gets `remaining / n`, and time an earlier rung did not spend
/// rolls forward. Passing `deadline: None` keeps the uncapped behaviour.
///
/// THE BUDGET LIVES HERE, NOT AT THE CALL SITES. It was originally written at
/// one call site in `crates/ay-pb/src/bin/ay.rs`, and when this chain was
/// factored into the library the budget stayed behind — so the three search
/// rungs went back to sharing one deadline for every caller of this function.
/// Measured on `evencolouring_..._nvert_071` through `ay pb solve --timeout
/// 120000`, with the shared deadline:
///
/// ```text
///   bounds-compact    slice=shared  elapsed=81914ms -> none
///   bounds-auxfree    slice=shared  elapsed=0ms     -> none
///   bounds-pb-native  slice=shared  elapsed=0ms     -> none      s UNKNOWN
/// ```
///
/// `bounds-pb-native` is the rung that certifies that instance. A chain whose
/// budget is copied is a budget that drifts, exactly as the chain itself did.
///
/// # Soundness
///
/// This function chooses an order; it derives nothing. Every rung independently
/// re-verifies that the incumbent is complete, feasible and achieves `optimum`,
/// and returns `None` rather than a doubtful proof. The returned text is proof
/// text only — untrusted until the external pinned VeriPB checker accepts it —
/// and `None` must never change a reported status. Certification is strictly
/// additive.
pub fn certify_opt_lin_any_interruptible(
    instance: &PbInstance,
    incumbent: &[bool],
    optimum: i128,
    deadline: Option<Instant>,
    should_stop: &dyn Fn() -> bool,
) -> Option<(String, OptLinCertRoute)> {
    // RUNGS 1-8: pure arithmetic, NOT scheduled. They never poll `should_stop`,
    // so they must not be put behind a budget that can be zero — a caller that
    // reaches certification with its deadline already spent (which is the
    // normal case for the CLI) still gets every one of them.
    let floor = certify_opt_lin_trivial_zero_floor(instance, incumbent, optimum)
        .map(|p| (p, OptLinCertRoute::TrivialZeroFloor))
        .or_else(|| {
            certify_opt_lin_knapsack_cardinality(instance, incumbent, optimum)
                .map(|p| (p, OptLinCertRoute::KnapsackCardinality))
        })
        .or_else(|| {
            certify_opt_lin_clique_coloring(instance, incumbent, optimum)
                .map(|p| (p, OptLinCertRoute::CliqueColoring))
        })
        .or_else(|| {
            certify_opt_lin_handshake_parity(instance, incumbent, optimum)
                .map(|p| (p, OptLinCertRoute::HandshakeParity))
        })
        .or_else(|| {
            certify_opt_lin_direct_aggregation_floor(instance, incumbent, optimum)
                .map(|p| (p, OptLinCertRoute::DirectAggregationFloor))
        })
        .or_else(|| {
            certify_opt_lin_lp_dual_floor(instance, incumbent, optimum)
                .map(|p| (p, OptLinCertRoute::LpDualFloor))
        })
        .or_else(|| {
            certify_opt_lin_frustrated_cycle(instance, incumbent, optimum)
                .map(|p| (p, OptLinCertRoute::FrustratedCycle))
        })
        .or_else(|| {
            certify_opt_lin_odd_cycle_cover(instance, incumbent, optimum)
                .map(|p| (p, OptLinCertRoute::OddCycleCover))
        })
        .or_else(|| {
            certify_opt_lin_layered_pebbling(instance, incumbent, optimum)
                .map(|p| (p, OptLinCertRoute::LayeredPebbling))
        })
        // LAST among the unscheduled rungs, and deliberately so. It is the only
        // one that opens a SEARCH TREE, so it is much the most expensive — but
        // its budget is a deterministic COUNT (nodes, depth, LP polls), not the
        // caller's clock, so it still belongs here rather than in the scheduled
        // block: a CLI whose deadline is already spent when certification starts
        // (the normal case) must still get it, and giving it a wall slice would
        // make its emitted bytes depend on machine load.
        .or_else(|| {
            certify_opt_lin_certified_bb(instance, incumbent, optimum)
                .map(|p| (p, OptLinCertRoute::CertifiedBb))
        });
    if floor.is_some() {
        return floor;
    }

    // RUNGS 9-11: SEARCH, one deadline each. `bounds_pb_native` is last and is
    // the rung that closes the most misses, so it is precisely the one a shared
    // deadline starves.
    let mut budget = CertRouteBudget::new(deadline, OPT_LIN_SEARCH_ROUTES, should_stop);
    let mut pbp = budget
        .run(OptLinCertRoute::BoundsCompact.as_str(), |stop| {
            certify_opt_lin_bounds_compact_interruptible(instance, incumbent, optimum, stop)
        })
        .map(|p| (p, OptLinCertRoute::BoundsCompact));
    if pbp.is_none() {
        pbp = budget
            .run(OptLinCertRoute::Bounds.as_str(), |stop| {
                certify_opt_lin_bounds_interruptible(instance, incumbent, optimum, stop)
            })
            .map(|p| (p, OptLinCertRoute::Bounds));
    }
    if pbp.is_none() {
        pbp = budget
            .run(OptLinCertRoute::BoundsPbNative.as_str(), |stop| {
                certify_opt_lin_bounds_pb_interruptible(instance, incumbent, optimum, stop)
            })
            .map(|p| (p, OptLinCertRoute::BoundsPbNative));
    }
    pbp
}

/// FLOORS AS BOUNDS: the structural floors the CERTIFIERS can prove, computed
/// BEFORE the search so they can serve as its initial dual bound.
///
/// # Why this exists
///
/// At the 5 s protocol the odd-cycle family's certificates never fired: the
/// route runs only AFTER the search proves optimality, which on that family
/// the search cannot do (`oddrowevencolsquare_dim_022`: search dual 253
/// against optimum 264 at any budget measured) — while the certifier proves
/// the exact optimal floor from structure in under a millisecond. Installing
/// that floor as the search's dual bound inverts the dependency:
/// `floor == incumbent` upgrades the verdict to OPTIMUM the moment the
/// incumbent exists, and the certificate chain then runs with the whole
/// remaining budget — where the same recovery emits the route in microseconds.
///
/// # The chain, and why it has TWO rungs today
///
/// * `odd_cycle_cover::recovered_floor` — the first certifier family whose
///   proven floor was NOT already feeding the search. Its soundness argument
///   (pure integer counting over a fail-closed recovery) is on the function.
/// * `handshake_parity::recovered_floor` — same bar, same shape: a total
///   fail-closed recovery and a pure integer-counting bound (`min_v w_v` from
///   the odd handshake total). On `evencolouring_opt_unit` `nvert_351..501`
///   the search holds the optimal incumbent `1` within seconds and can prove
///   nothing at any measured budget; `floor == incumbent` is the whole
///   verdict.
/// * `direct-aggregation-floor` is NOT here: its bound is arithmetically the
///   same `ceil(rhs_sum·cv/cs)` surrogate that
///   `crate::cdcl::aggregation_objective_lower_bound_from_constraints`
///   already contributes to `objective_lower_bound_from_constraints`, which
///   both wiring sites consult first — adding it would recompute an installed
///   bound.
/// * `clique-coloring` is NOT here: `crate::optimize::clique_coloring`
///   already answers that family exactly as a pre-solve shortcut
///   (`portfolio.rs`), so a floor cannot move a verdict on it.
/// * `frustrated-cycle` is NOT here YET: its packing columns come from
///   float-LP separation, and the frustration property of each priced column
///   is re-established only by the emission's layer-4 replay — below the bar
///   for a verdict-bearing pre-search floor. Adding it requires an integer
///   re-verification of every nonzero column first.
///
/// # Soundness contract (the caller's, enforced here)
///
/// * The floor is a bound on `instance.objective`; a caller optimizing ANY
///   other objective must get `None` — checked against the passed
///   `objective`, fail-closed, AFTER the ns-scale recovery gates so the
///   check's `O(#objective)` cost is only ever paid on-family.
/// * The returned floor may only ever TIGHTEN a search dual bound
///   (`max`-combined / published to a monotone-max bus), never replace a
///   better one — that is the wiring sites' obligation, recorded here because
///   this is the function they all call.
/// * A floor from here never skips evidence: the verdict paths it can flip
///   re-verify the incumbent's feasibility (`optimum_upgrade_guard` /
///   `sanitize_optimization_incumbent`), and the certificate chain still runs
///   and emits for the pinned checker exactly as before.
pub fn recovered_structural_search_floor(
    instance: &PbInstance,
    objective: &PbObjective,
) -> Option<i128> {
    let floor = odd_cycle_cover::recovered_floor(instance)
        .or_else(|| handshake_parity::recovered_floor(instance))
        .or_else(|| layered_pebbling::recovered_floor(instance))?;
    // The recovery bounded `instance.objective`; refuse any caller whose
    // search objective is not literally that objective.
    if instance.objective.as_ref() != Some(objective) {
        return None;
    }
    Some(floor)
}

/// CONSTRUCTED WITNESS for the layered group-division family: the optimal
/// incumbent the certifier's own fail-closed recovery can BUILD, for the
/// members where [`recovered_structural_search_floor`] installs the exact
/// floor but the search cannot find a matching incumbent within budget.
///
/// Returns the witness and its exact objective value (== the recovered
/// floor). The full construction and soundness argument live on
/// [`layered_pebbling::constructed_optimum_witness`]; the summary is that
/// setting exactly `f(r)` variables of each group true meets every row by
/// the floor recurrence's own definition, and the point is then re-verified
/// against every ORIGINAL row with its objective recomputed exactly — the
/// same bar every search incumbent passes. The caller owes the returned
/// witness no trust: it is a CANDIDATE incumbent like any other, and the
/// certificate chain plus the pinned external checker re-derive both bounds
/// before anything is claimed to a user.
///
/// The `objective` identity check mirrors [`recovered_structural_search_floor`]:
/// a caller optimizing any objective other than the instance's own must get
/// `None`, fail-closed.
pub fn layered_pebbling_constructed_optimum(
    instance: &PbInstance,
    objective: &PbObjective,
) -> Option<(Vec<bool>, i128)> {
    let witness = layered_pebbling::constructed_optimum_witness(instance)?;
    if instance.objective.as_ref() != Some(objective) {
        return None;
    }
    Some(witness)
}

#[cfg(test)]
mod direct_floor_tests {
    use super::*;
    use crate::types::{PbConstraint, PbInstance, PbLit, PbObjective, PbRel, PbTerm};

    fn plit(var: u32) -> PbLit {
        PbLit {
            var,
            negated: false,
        }
    }
    fn term(coeff: i128, var: u32) -> PbTerm {
        PbTerm {
            coeff,
            lits: vec![plit(var)],
        }
    }
    fn ge(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
        PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs,
        }
    }

    /// Triangle covering: min x1+x2+x3 s.t. every edge covered. Optimum = 2.
    /// colsum[v]=2, M=2, floor=ceil(3/2)=2 == optimum -> the direct aggregation
    /// floor certifies it. Locks in the emitter shape (soli + pol + BOUNDS).
    #[test]
    fn direct_aggregation_floor_emits_for_triangle_cover() {
        let objective = PbObjective {
            terms: vec![term(1, 1), term(1, 2), term(1, 3)],
        };
        let instance = PbInstance {
            num_vars: 3,
            num_constraints: 3,
            constraints: vec![
                ge(vec![term(1, 1), term(1, 2)], 1),
                ge(vec![term(1, 2), term(1, 3)], 1),
                ge(vec![term(1, 1), term(1, 3)], 1),
            ],
            objective: Some(objective),
        };
        // Incumbent {x1,x2} (covers all edges), value 2 = optimum.
        let incumbent = vec![true, true, false];
        let proof = certify_opt_lin_direct_aggregation_floor(&instance, &incumbent, 2)
            .expect("direct aggregation floor should certify the triangle cover optimum");
        assert!(proof.contains("soli"), "proof must log the incumbent");
        assert!(
            proof.contains("pol"),
            "proof must contain the CG derivation"
        );
        assert!(
            proof.contains("conclusion BOUNDS 2 : ") && proof.contains(" 2 : "),
            "proof must conclude hinted BOUNDS 2 2, got:\n{proof}"
        );
    }

    /// A non-tight floor (LP gap) must DECLINE, never emit an unsound bound.
    #[test]
    fn direct_aggregation_floor_declines_when_not_tight() {
        // min x1+x2 s.t. x1+x2>=1. LP/agg floor = 1, but pass a wrong "optimum" 2.
        let instance = PbInstance {
            num_vars: 2,
            num_constraints: 1,
            constraints: vec![ge(vec![term(1, 1), term(1, 2)], 1)],
            objective: Some(PbObjective {
                terms: vec![term(1, 1), term(1, 2)],
            }),
        };
        // Floor is 1; claiming optimum 2 must be refused (floor != optimum).
        assert!(certify_opt_lin_direct_aggregation_floor(&instance, &[true, true], 2).is_none());
    }

    /// Negative-objective (maximization) is out of this builder's slice: decline.
    #[test]
    fn direct_aggregation_floor_declines_negative_objective() {
        let instance = PbInstance {
            num_vars: 2,
            num_constraints: 1,
            constraints: vec![ge(vec![term(1, 1), term(1, 2)], 1)],
            objective: Some(PbObjective {
                terms: vec![term(-1, 1), term(-1, 2)],
            }),
        };
        assert!(certify_opt_lin_direct_aggregation_floor(&instance, &[true, true], -2).is_none());
    }

    /// Tight-LP MAXIMIZATION: `max x1+x2 s.t. x1+x2<=1` (`min -x1-x2 s.t.
    /// -x1-x2>=-1`), optimum -1, LP-tight. The LP-dual floor certifies it (the
    /// aggregation floor cannot — negative objective). Incumbent {x1}.
    #[test]
    fn lp_dual_floor_certifies_tight_maximization() {
        let instance = PbInstance {
            num_vars: 2,
            num_constraints: 1,
            constraints: vec![ge(vec![term(-1, 1), term(-1, 2)], -1)],
            objective: Some(PbObjective {
                terms: vec![term(-1, 1), term(-1, 2)],
            }),
        };
        let proof = certify_opt_lin_lp_dual_floor(&instance, &[true, false], -1)
            .expect("LP-dual floor should certify the tight maximization optimum");
        assert!(proof.contains("soli"));
        assert!(
            proof.contains("conclusion BOUNDS -1 : ") && proof.contains(" -1 : "),
            "must conclude hinted BOUNDS -1 -1, got:\n{proof}"
        );
    }

    /// Trivial zero-floor: `min x1+x2 s.t. x1+x2>=0` (trivially SAT), optimum 0,
    /// incumbent all-false. `obj >= 0` by non-negativity certifies it.
    #[test]
    fn trivial_zero_floor_certifies_optimum_zero() {
        let instance = PbInstance {
            num_vars: 2,
            num_constraints: 1,
            constraints: vec![ge(vec![term(1, 1), term(1, 2)], 0)],
            objective: Some(PbObjective {
                terms: vec![term(1, 1), term(1, 2)],
            }),
        };
        let proof = certify_opt_lin_trivial_zero_floor(&instance, &[false, false], 0)
            .expect("trivial zero-floor should certify optimum 0");
        assert!(proof.contains("soli"));
        assert!(
            proof.contains("conclusion BOUNDS 0 : ") && proof.contains(" 0 : "),
            "must conclude hinted BOUNDS 0 0, got:\n{proof}"
        );
    }

    /// Strongly-correlated knapsack: 4 items, w={4,4,4,5}, C=9, v=w+10 → k_max=2,
    /// optimum −29 = −(9 + 10·2), cardinality bound exactly tight. The constant-size
    /// reified-threshold certificate must emit and conclude BOUNDS −29 −29.
    /// (Hand-verified against real VeriPB before codifying.)
    #[test]
    fn knapsack_cardinality_certifies_strongly_correlated() {
        let instance = PbInstance {
            num_vars: 4,
            num_constraints: 1,
            constraints: vec![ge(
                vec![term(-4, 1), term(-4, 2), term(-4, 3), term(-5, 4)],
                -9,
            )],
            objective: Some(PbObjective {
                terms: vec![term(-14, 1), term(-14, 2), term(-14, 3), term(-15, 4)],
            }),
        };
        // incumbent {x3, x4}: weight 9 <= 9, value 29 -> obj -29.
        let proof =
            certify_opt_lin_knapsack_cardinality(&instance, &[false, false, true, true], -29)
                .expect("strongly-correlated knapsack must certify");
        assert!(proof.contains("soli"));
        assert!(proof.contains("red "), "must reify the threshold");
        assert!(
            proof.contains("conclusion BOUNDS -29 : ") && proof.contains(" -29 : "),
            "must conclude hinted BOUNDS -29 -29, got:\n{proof}"
        );
    }

    /// Non-uniform surplus (v−w differs) must decline — the cardinality bound
    /// argument only holds for the uniform strongly-correlated shape.
    #[test]
    fn knapsack_cardinality_declines_non_uniform_surplus() {
        let instance = PbInstance {
            num_vars: 2,
            num_constraints: 1,
            constraints: vec![ge(vec![term(-4, 1), term(-4, 2)], -7)],
            objective: Some(PbObjective {
                terms: vec![term(-14, 1), term(-13, 2)],
            }),
        };
        assert!(certify_opt_lin_knapsack_cardinality(&instance, &[true, false], -14).is_none());
    }

    /// Trivial zero-floor declines a non-zero optimum.
    #[test]
    fn trivial_zero_floor_declines_nonzero_optimum() {
        let instance = PbInstance {
            num_vars: 1,
            num_constraints: 1,
            constraints: vec![ge(vec![term(1, 1)], 1)],
            objective: Some(PbObjective {
                terms: vec![term(1, 1)],
            }),
        };
        assert!(certify_opt_lin_trivial_zero_floor(&instance, &[true], 1).is_none());
    }

    /// The LP-dual floor also certifies a POSITIVE-objective tight-LP optimum
    /// (the sign gate was removed: it runs after the aggregation floor declines,
    /// covering non-covering positive instances like fir/5_10/mps).
    #[test]
    fn lp_dual_floor_certifies_positive_objective_tight_lp() {
        let instance = PbInstance {
            num_vars: 2,
            num_constraints: 1,
            constraints: vec![ge(vec![term(1, 1), term(1, 2)], 1)],
            objective: Some(PbObjective {
                terms: vec![term(1, 1), term(1, 2)],
            }),
        };
        let proof = certify_opt_lin_lp_dual_floor(&instance, &[true, false], 1)
            .expect("tight-LP positive objective should certify via the LP dual");
        assert!(
            proof.contains("conclusion BOUNDS 1 : ") && proof.contains(" 1 : "),
            "must conclude hinted BOUNDS 1 .. 1, got:\n{proof}"
        );
    }

    /// Builds the PB25 `ihalainen/PBO-clique-coloring` shape at (n, t):
    /// choose a graph on `n` vertices that is `t`-colourable and place vertices
    /// into `n` clique slots; pay 1 per empty slot. Optimum is `n - t`, because
    /// the occupied slots hold pairwise-adjacent vertices and a `t`-colourable
    /// graph has no clique of size `t + 1` (this is `omega(G) <= chi(G)`, i.e.
    /// pigeonhole). Variable layout, 1-based:
    ///   `M[i][j] = 1 + i*n + j`             vertex `i` occupies slot `j`
    ///   `o[j]    = 1 + n*n + j`             slot `j` is empty (the objective)
    ///   `C[v][k] = 1 + n*n + n + v*t + k`   vertex `v` has colour `k`
    ///   `e[p]    = 1 + n*n + n + n*t + p`   edge `p`, over pairs `i < i'`
    fn clique_colouring(n: u32, t: u32) -> PbInstance {
        let m = |i: u32, j: u32| 1 + i * n + j;
        let o = |j: u32| 1 + n * n + j;
        let c = |v: u32, k: u32| 1 + n * n + n + v * t + k;
        let pairs: Vec<(u32, u32)> = (0..n)
            .flat_map(|i| (i + 1..n).map(move |x| (i, x)))
            .collect();
        let e = |p: usize| 1 + n * n + n + n * t + u32::try_from(p).expect("pair index fits u32");
        let mut rows = Vec::new();
        for j in 0..n {
            // slot `j` is occupied, or `o[j]` is paid
            let mut r = vec![term(1, o(j))];
            r.extend((0..n).map(|i| term(1, m(i, j))));
            rows.push(ge(r, 1));
        }
        for i in 0..n {
            // a vertex occupies at most one slot
            rows.push(ge((0..n).map(|j| term(-1, m(i, j))).collect(), -1));
        }
        for (p, &(i, ii)) in pairs.iter().enumerate() {
            // two vertices in DISTINCT slots must be adjacent
            for a in 0..n {
                for b in 0..n {
                    if a != b {
                        rows.push(ge(
                            vec![term(1, e(p)), term(-1, m(i, a)), term(-1, m(ii, b))],
                            -1,
                        ));
                    }
                }
            }
        }
        for v in 0..n {
            // every vertex gets a colour
            rows.push(ge((0..t).map(|k| term(1, c(v, k))).collect(), 1));
        }
        for (p, &(i, ii)) in pairs.iter().enumerate() {
            // adjacent vertices do not share a colour
            for k in 0..t {
                rows.push(ge(
                    vec![term(-1, e(p)), term(-1, c(i, k)), term(-1, c(ii, k))],
                    -2,
                ));
            }
        }
        PbInstance {
            num_vars: n * n + n + n * t + u32::try_from(pairs.len()).expect("pairs fit u32"),
            num_constraints: u32::try_from(rows.len()).expect("row count fits u32"),
            constraints: rows,
            objective: Some(PbObjective {
                terms: (0..n).map(|j| term(1, o(j))).collect(),
            }),
        }
    }

    /// THE NEGATIVE, made executable: for clique-coloring the LP relaxation
    /// optimum is EXACTLY 0 while the integer optimum is `n - t`, so **no**
    /// LP-dual floor certificate can ever fire on this family — not with more
    /// budget, not with a better vertex, not with a bigger denominator cap.
    ///
    /// The witness is checkable by hand: put every vertex fractionally in every
    /// slot (`M[i][j] = 1/n`), give every vertex every colour (`C[v][k] = 1/t`),
    /// and leave every edge and payment variable at 0. Scaled by `n*t` (so the
    /// arithmetic below is exact integer arithmetic) each row holds:
    ///   slot   `o_j + sum_i M[i][j] >= 1`         -> `n * t >= n * t`
    ///   vertex `sum_j M[i][j] <= 1`               -> `n * t <= n * t`
    ///   edge   `e >= M[i][a] + M[i'][b] - 1`      -> `0 >= 2t - n*t`, true for n >= 2
    ///   colour `sum_k C[v][k] >= 1`               -> `n * t >= n * t`
    ///   proper `e + C[i][k] + C[i'][k] <= 2`      -> `2n <= 2*n*t`, true for t >= 1
    /// and the objective is 0. Because every objective coefficient is `+1` and
    /// `x >= 0`, `LP* >= 0` too, so `LP* = 0` exactly.
    ///
    /// Cross-checked 2026-08-27 against the four corpus members that deliver a
    /// worthless dual point — n=7-t=3, n=8-t=3, n=10-t=3, n=10-t=9 — where an
    /// independent LP engine and an exact rational primal witness both put
    /// `LP* = 0` against optima 4/5/7/1.
    #[test]
    fn clique_colouring_lp_relaxation_is_exactly_zero_so_no_dual_floor_can_fire() {
        for (n, t) in [(4u32, 2u32), (4, 3), (5, 2), (5, 3)] {
            let instance = clique_colouring(n, t);
            // The uniform witness, scaled by `n*t` to stay in exact integers.
            let scale = i128::from(n) * i128::from(t);
            let value = |var: u32| -> i128 {
                if var <= n * n {
                    i128::from(t) // M[i][j] = 1/n
                } else if var <= n * n + n {
                    0 // o[j] = 0
                } else if var <= n * n + n + n * t {
                    i128::from(n) // C[v][k] = 1/t
                } else {
                    0 // e[p] = 0
                }
            };
            for row in &instance.constraints {
                let lhs: i128 = row
                    .terms
                    .iter()
                    .map(|term| {
                        term.coeff * value(term.lits.first().expect("unit literal row").var)
                    })
                    .sum();
                assert!(
                    lhs >= row.rhs * scale,
                    "uniform witness violates a row at n={n} t={t}: {lhs} < {}",
                    row.rhs * scale
                );
            }
            let objective: i128 = instance
                .objective
                .as_ref()
                .expect("objective")
                .terms
                .iter()
                .map(|term| term.coeff * value(term.lits.first().expect("unit literal").var))
                .sum();
            assert_eq!(objective, 0, "witness objective must be 0 at n={n} t={t}");
        }
    }

    /// The companion behavioural half: with `LP* = 0` and optimum `n - t = 2`,
    /// the LP-dual emitter must DECLINE rather than emit anything. A proof here
    /// would be a proof of a bound the LP dual cannot support, which is the
    /// worst defect this crate can have.
    #[test]
    fn clique_colouring_lp_dual_floor_declines_fail_closed() {
        let instance = clique_colouring(4, 2);
        // Optimum-2 model: vertices 0,1 in slots 0,1 with distinct colours and
        // the edge between them present; slots 2,3 empty. Verified feasible.
        let mut incumbent = vec![false; instance.num_vars as usize];
        for var in [1u32, 6, 19, 20, 21, 24, 25, 27, 29] {
            incumbent[var as usize - 1] = true;
        }
        assert!(
            certify_opt_lin_lp_dual_floor(&instance, &incumbent, 2).is_none(),
            "LP-dual floor must decline when LP* = 0 but the optimum is 2"
        );
    }
}

#[cfg(test)]
mod chain_tests {
    use super::*;
    use crate::types::{PbConstraint, PbInstance, PbLit, PbObjective, PbRel, PbTerm};
    use std::time::Duration;

    fn plit(var: u32) -> PbLit {
        PbLit {
            var,
            negated: false,
        }
    }
    fn term(coeff: i128, var: u32) -> PbTerm {
        PbTerm {
            coeff,
            lits: vec![plit(var)],
        }
    }
    fn ge(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
        PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs,
        }
    }

    /// Triangle covering, optimum 2 — the direct-aggregation floor's own
    /// fixture. The chain must reach it and must SAY which rung reached it.
    fn triangle_cover() -> PbInstance {
        PbInstance {
            num_vars: 3,
            num_constraints: 3,
            constraints: vec![
                ge(vec![term(1, 1), term(1, 2)], 1),
                ge(vec![term(1, 2), term(1, 3)], 1),
                ge(vec![term(1, 1), term(1, 3)], 1),
            ],
            objective: Some(PbObjective {
                terms: vec![term(1, 1), term(1, 2), term(1, 3)],
            }),
        }
    }

    #[test]
    fn chain_reaches_the_floor_routes_and_names_the_rung() {
        let instance = triangle_cover();
        let incumbent = vec![true, true, false];
        let (proof, route) =
            certify_opt_lin_any_interruptible(&instance, &incumbent, 2, None, &|| false)
                .expect("the chain must reach the direct-aggregation floor");
        assert_eq!(route, OptLinCertRoute::DirectAggregationFloor);
        assert_eq!(route.as_str(), "direct-aggregation-floor");
        assert!(proof.contains("conclusion BOUNDS 2"), "proof was:\n{proof}");
    }

    /// THE BUDGET PROPERTY THE SHIPPED CLI DEPENDS ON. The CLI's certificate
    /// stage is entered after the native proof-logging phase has already spent
    /// the caller's deadline, so `should_stop()` is routinely true on the first
    /// poll. The five floor rungs are pure arithmetic and must fire anyway; only
    /// the three search rungs are allowed to decline early. If this test ever
    /// fails, wiring the chain into a starved caller stops buying anything and
    /// the CLI silently returns to its two-route coverage.
    #[test]
    fn floor_routes_still_fire_with_an_already_expired_deadline() {
        let instance = triangle_cover();
        let incumbent = vec![true, true, false];
        // BOTH kinds of exhaustion at once: an absolute deadline that expired
        // a second ago AND a `should_stop` that is already true.
        let expired = Instant::now()
            .checked_sub(Duration::from_secs(1))
            .expect("a one-second-old instant exists on every supported clock");
        let (proof, route) =
            certify_opt_lin_any_interruptible(&instance, &incumbent, 2, Some(expired), &|| true)
                .expect("floor routes must not consult should_stop");
        assert_eq!(route, OptLinCertRoute::DirectAggregationFloor);
        assert!(proof.contains("conclusion BOUNDS 2"), "proof was:\n{proof}");
    }

    /// FAIL CLOSED. An incumbent that does not achieve the claimed optimum must
    /// produce NO proof from ANY rung — a certificate for a bound the instance
    /// does not support is the worst defect this module can have.
    #[test]
    fn chain_declines_when_the_incumbent_does_not_achieve_the_claim() {
        let instance = triangle_cover();
        // {x1,x2,x3} has value 3, not 2.
        let incumbent = vec![true, true, true];
        assert!(
            certify_opt_lin_any_interruptible(&instance, &incumbent, 2, None, &|| false).is_none(),
            "the chain must not certify an optimum its incumbent does not reach"
        );
    }

    /// THE SCHEDULER MUST BE SIZED FOR EVERY SEARCH RUNG. `CertRouteBudget`
    /// hands rung `i` of `n` a slice of `remaining / n`; if a search rung is
    /// added to the chain and `OPT_LIN_SEARCH_ROUTES` is not bumped with it,
    /// the extra rung runs with `routes_left` already 0 and takes ALL of what
    /// is left — the starvation defect, reintroduced by addition. The match is
    /// exhaustive on purpose: a new variant will not compile until it is
    /// classified.
    #[test]
    fn the_scheduler_is_sized_for_every_search_rung() {
        let mut search = 0u32;
        for route in [
            OptLinCertRoute::TrivialZeroFloor,
            OptLinCertRoute::KnapsackCardinality,
            OptLinCertRoute::CliqueColoring,
            OptLinCertRoute::HandshakeParity,
            OptLinCertRoute::DirectAggregationFloor,
            OptLinCertRoute::LpDualFloor,
            OptLinCertRoute::FrustratedCycle,
            OptLinCertRoute::OddCycleCover,
            OptLinCertRoute::LayeredPebbling,
            OptLinCertRoute::CertifiedBb,
            OptLinCertRoute::BoundsCompact,
            OptLinCertRoute::Bounds,
            OptLinCertRoute::BoundsPbNative,
        ] {
            let consults_should_stop = match route {
                OptLinCertRoute::TrivialZeroFloor
                | OptLinCertRoute::KnapsackCardinality
                | OptLinCertRoute::CliqueColoring
                | OptLinCertRoute::HandshakeParity
                | OptLinCertRoute::DirectAggregationFloor
                | OptLinCertRoute::LpDualFloor
                | OptLinCertRoute::FrustratedCycle
                | OptLinCertRoute::OddCycleCover
                | OptLinCertRoute::LayeredPebbling
                // Bounded by deterministic COUNTS (nodes, depth, LP polls), not
                // by the caller's clock: it never polls `should_stop`, so it is
                // NOT a scheduled rung.
                | OptLinCertRoute::CertifiedBb => false,
                OptLinCertRoute::BoundsCompact
                | OptLinCertRoute::Bounds
                | OptLinCertRoute::BoundsPbNative => true,
            };
            search += u32::from(consults_should_stop);
        }
        assert_eq!(
            OPT_LIN_SEARCH_ROUTES, search,
            "the per-route budget must be sized for exactly the search rungs"
        );
    }

    /// A claim BELOW the true optimum must also be refused: the floor rungs
    /// derive the bound themselves and must not be talked into a smaller one.
    #[test]
    fn chain_declines_a_claim_below_the_true_optimum() {
        let instance = triangle_cover();
        let incumbent = vec![true, true, false];
        assert!(
            certify_opt_lin_any_interruptible(&instance, &incumbent, 1, None, &|| false).is_none(),
            "the chain must not certify a bound below the instance's optimum"
        );
    }
}
