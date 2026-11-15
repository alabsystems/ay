//! Common helper functions for writing an elaborated proof.

use std::rc::Rc;

use malachite_bigint::BigInt;
use veripb_formula::{
    lit::Lit,
    prelude::{
        Assignment, BooleanVar, DBConstraint, PBConstraintEnum, PBObjective, Substitution,
        ToPrettyString, VarIdx, VarNameLookup, VarNameManager,
    },
    propagation::RUPHint,
};

use super::{ConstraintLookup, Elaborator};
use crate::{Bound, Instruction, ObjectiveUpdateType, ProofgoalID, SolutionRuleOutput, keywords};

// Helpers writing specific lines and subproofs of the elaborated proof.
// `_header` methods write a rule's opening line up to `: subproof`;
// `_tail` methods write the subproof body after the proofgoal header.
impl Elaborator {
    /// Writes the output-proof ID of the database constraint at `index`.
    pub(crate) fn write_constraint_out_id(
        &mut self,
        database: &impl ConstraintLookup,
        index: usize,
    ) {
        let constraint = database
            .get_entry_usize(index)
            .expect("constraint already accessed");
        self.write_display(
            constraint
                .get_out_id(index)
                .expect("constraint should have output ID"),
        );
    }

    pub fn write_load_formula(&mut self, formula_size: usize) {
        self.write("f ");
        self.write_display(formula_size);
        self.writeln(";");
    }

    /// Writes `conclusion NONE;`.
    pub fn write_conclusion_none(&mut self) {
        self.write("conclusion NONE");
        self.writeln(";");
    }

    /// Writes `conclusion SAT[ : <solution>];`.
    pub fn write_conclusion_sat(
        &mut self,
        var_names: &impl VarNameLookup,
        propagated_solution: Option<&Assignment<BooleanVar>>,
    ) {
        self.write("conclusion SAT");
        if let Some(assignment) = propagated_solution {
            self.write(" : ");
            self.write(&assignment.to_pretty_string(var_names));
        }
        self.writeln(";");
    }

    /// Writes `conclusion UNSAT : <id>;`.
    pub fn write_conclusion_unsat(
        &mut self,
        database: &impl ConstraintLookup,
        contradicting_id: usize,
    ) {
        self.write("conclusion UNSAT : ");
        self.write_constraint_out_id(database, contradicting_id);
        self.writeln(";");
    }

    /// Writes `conclusion BOUNDS <lb> : <id> <ub>[ : <solution>];`.
    pub fn write_conclusion_bounds(
        &mut self,
        database: &impl ConstraintLookup,
        var_names: &impl VarNameLookup,
        lower_bound: &Bound,
        upper_bound: &Bound,
        contradicting_id: usize,
        propagated_solution: Option<&Assignment<BooleanVar>>,
    ) {
        self.write("conclusion BOUNDS ");
        self.write(&lower_bound.to_string());
        self.write(" : ");
        self.write_constraint_out_id(database, contradicting_id);
        self.write(" ");
        self.write(&upper_bound.to_string());
        if *upper_bound != Bound::Unbounded
            && let Some(assignment) = propagated_solution
        {
            self.write(" : ");
            self.write(&assignment.to_pretty_string(var_names));
        }
        self.writeln(";");
    }

    /// Writes `conclusion ENUMERATION_COMPLETE <count> : <id>;`.
    pub fn write_conclusion_enumeration_complete(
        &mut self,
        database: &impl ConstraintLookup,
        solution_count: &Bound,
        contradicting_id: usize,
    ) {
        self.write("conclusion ");
        self.write(keywords::ENUMERATION_COMPLETE);
        self.write(" ");
        self.write(&solution_count.to_string());
        self.write(" : ");
        self.write_constraint_out_id(database, contradicting_id);
        self.writeln(";");
    }

    /// Writes `conclusion ENUMERATION_PARTIAL <count>;`.
    pub fn write_conclusion_enumeration_partial(&mut self, solution_count: &Bound) {
        self.write("conclusion ");
        self.write(keywords::ENUMERATION_PARTIAL);
        self.write(" ");
        self.write(&solution_count.to_string());
        self.writeln(";");
    }

    /// Appends each RUP hint; `NegatedPremise` becomes `negated_premise_id`, or `~` if absent.
    pub fn write_rup_hints(&mut self, rup_hints: &[RUPHint], negated_premise_id: Option<usize>) {
        for hint in rup_hints {
            self.write(" ");
            match hint {
                RUPHint::ConstraintId(id) => self.write_display(id),
                RUPHint::NegatedPremise => match negated_premise_id {
                    Some(id) => self.write_display(id),
                    None => self.write("~"),
                },
            }
        }
    }

    /// Write a RUP step with `rup_hints`.
    pub fn write_rup_step(
        &mut self,
        constraint: &PBConstraintEnum,
        rup_hints: &[RUPHint],
        var_lookup: &impl VarNameLookup,
    ) {
        self.write_indent();
        self.write("rup ");
        self.write(&constraint.to_pretty_string(var_lookup));
        self.write(" :");
        self.write_rup_hints(rup_hints, None);
        self.writeln(";");
    }

    /// Write an ia step with a mandatory hint (`premise_id`).
    pub fn write_ia_step(
        &mut self,
        constraint: &PBConstraintEnum,
        database: &impl ConstraintLookup,
        premise_id: usize,
        var_lookup: &impl VarNameLookup,
    ) {
        self.write_indent();
        self.write("ia ");
        self.write(&constraint.to_pretty_string(var_lookup));
        self.write(" : ");
        self.write_constraint_out_id(database, premise_id);
        self.writeln(";");
    }

    /// Write header for starting a top-level subproof.
    pub(crate) fn write_subproof_rule_header(
        &mut self,
        rule_str: &str,
        leading: Option<&str>,
        constraint: Option<&Rc<DBConstraint>>,
        witness: Option<&Substitution>,
        var_lookup: Option<&impl VarNameLookup>,
    ) {
        self.write(rule_str);
        self.write(" ");
        if let Some(leading) = leading {
            self.write(leading);
            self.write(" ");
        }
        if let Some(constraint) = constraint {
            self.write(
                &constraint
                    .to_pretty_string(var_lookup.expect("need var names for constraint printing")),
            );
        }
        if let Some(witness) = witness {
            self.write(" :");
            if !witness.is_empty() {
                self.write(
                    &witness
                        .to_pretty_string(var_lookup.expect("need var names for witness printing")),
                );
            }
        }
        self.writeln(" : subproof");
        self.inc_indent();
    }

    /// Write the header of a `pbc`-rule starting a subproof.
    pub fn write_pbc_header(
        &mut self,
        constraint: &Rc<DBConstraint>,
        var_lookup: &impl VarNameLookup,
    ) {
        self.write_subproof_rule_header("pbc", None, Some(constraint), None, Some(var_lookup));
    }

    /// Write the header of a `red`-rule starting a subproof.
    pub fn write_red_header(
        &mut self,
        constraint: &Rc<DBConstraint>,
        witness: &Substitution,
        var_lookup: &impl VarNameLookup,
    ) {
        self.write_subproof_rule_header(
            "red",
            None,
            Some(constraint),
            Some(witness),
            Some(var_lookup),
        );
    }

    /// Write the header of a `dom`-rule starting a subproof.
    pub fn write_dom_header(
        &mut self,
        constraint: &Rc<DBConstraint>,
        witness: &Substitution,
        var_lookup: &impl VarNameLookup,
    ) {
        self.write_subproof_rule_header(
            "dom",
            None,
            Some(constraint),
            Some(witness),
            Some(var_lookup),
        );
    }

    /// Write the header of a `delc`-rule starting a subproof.
    pub fn write_delc_subproof_header(
        &mut self,
        deletion_id: usize,
        witness: Option<&Substitution>,
        var_lookup: Option<&impl VarNameLookup>,
    ) {
        let id = deletion_id.to_string();
        self.write_subproof_rule_header("delc", Some(&id), None, witness, var_lookup);
    }

    /// Write the header of a `preserved_add`-rule starting a subproof.
    pub fn write_preserved_add(
        &mut self,
        var: VarIdx,
        constraint: &Rc<DBConstraint>,
        var_lookup: &impl VarNameLookup,
    ) {
        let name = var.to_pretty_string(var_lookup) + " :";
        self.write_subproof_rule_header(
            keywords::PRESERVED_ADD,
            Some(&name),
            Some(constraint),
            None,
            Some(var_lookup),
        );
    }

    /// Write the header of a `preserved_rm`-rule starting a subproof.
    pub fn write_preserved_rm(
        &mut self,
        var: VarIdx,
        constraint: &Rc<DBConstraint>,
        var_lookup: &impl VarNameLookup,
    ) {
        let name = var.to_pretty_string(var_lookup) + " :";
        self.write_subproof_rule_header(
            keywords::PRESERVED_RM,
            Some(&name),
            Some(constraint),
            None,
            Some(var_lookup),
        );
    }

    /// Write the header of a `proofgoal` subproof.
    pub fn write_proofgoal(
        &mut self,
        goal_id: &ProofgoalID,
        constraint_lookup: Option<&impl ConstraintLookup>,
    ) {
        self.write_indent();
        self.write("proofgoal ");
        self.write_proofgoal_id(goal_id, constraint_lookup);
        self.inc_indent();
    }

    /// Write ending a subproof with `qed` **without** constraint ID.
    pub fn write_qed(&mut self) {
        self.dec_indent();
        self.write_indent();
        self.writeln("qed;");
    }

    /// Write ending a subproof with `qed` with constraint ID.
    pub fn write_qed_with_id(&mut self, id: usize) {
        self.dec_indent();
        self.write_indent();
        self.write("qed : ");
        self.write_display(id);
        self.writeln(";");
    }

    /// Write ending a subproof with `qed` with the **next** constraint ID as hint.
    pub fn write_qed_with_next_id(&mut self) {
        let next_id = self.inc_id();
        self.write_qed_with_id(next_id);
    }

    /// Write a cutting planes derivation given a sequence of instructions
    /// in reverse polish notation.
    pub fn write_pol_step(
        &mut self,
        instructions: &[Instruction],
        constaint_lookup: Option<&impl ConstraintLookup>,
        var_lookup: Option<&impl VarNameLookup>,
    ) {
        self.write_indent();
        self.write("pol");
        for instruction in instructions.iter() {
            self.write(" ");
            match instruction {
                Instruction::ConstraintId(index) => {
                    self.write_constraint_out_id(
                        constaint_lookup.expect("need constraint lookup to write pol id"),
                        *index as usize,
                    );
                }
                Instruction::LiteralAxiom(lit) => self.write(&lit.to_pretty_string(
                    var_lookup.expect("need var lookup to write pol literal axiom"),
                )),
                Instruction::NormalizedFormDivide(big_int) => {
                    self.write(&big_int.to_string());
                    self.write(" d");
                }
                Instruction::VariableFormDivide(big_int) => {
                    self.write(&big_int.to_string());
                    self.write(" c");
                }
                Instruction::NormalizedFormMIR(big_int) => {
                    self.write(&big_int.to_string());
                    self.write(" n");
                }
                Instruction::VariableFormMIR(big_int) => {
                    self.write(&big_int.to_string());
                    self.write(" m");
                }
                Instruction::Multiply(big_int) => {
                    self.write(&big_int.to_string());
                    self.write(" *");
                }
                Instruction::Weaken(var) => {
                    self.write(&var.to_pretty_string(
                        var_lookup.expect("need var lookup to write pol weakening step"),
                    ));
                    self.write(" w");
                }
                Instruction::Add => self.write("+"),
                Instruction::Saturate => self.write("s"),
                Instruction::LowerRHS(amount) => {
                    self.write(&amount.to_string());
                    self.write(" -");
                }
            }
        }
        self.writeln(";");
    }

    /// Write `pol <id> ;` at the current indent.
    pub fn write_pol_single_id(&mut self, id: usize) {
        self.write_indent();
        self.write("pol");
        self.write(" ");
        self.write_display(id);
        self.writeln(";");
    }

    /// Writes `pol <a> <b> <scale> * +` at the current indent
    fn write_pol_add_scaled(&mut self, a: usize, b: usize, scale: &BigInt) {
        self.write_indent();
        self.write("pol ");
        self.write_display(a);
        self.write(" ");
        self.write_display(b);
        self.write(" ");
        self.write_display(scale);
        self.write(" * +");
    }

    /// Write the `obji`-rule.
    pub fn write_objective_value(&mut self, value: &BigInt) {
        self.write("obji");
        self.write(" ");
        self.write_display(value);
        self.writeln(";");
    }

    /// Write a list of variables with the current indent.
    pub(crate) fn write_indented_var_list(
        &mut self,
        keyword: &str,
        vars: &[VarIdx],
        var_lookup: &impl VarNameLookup,
    ) {
        self.write_indent();
        self.write(keyword);
        for &var in vars {
            self.write(" ");
            self.write(var_lookup.get_name(var));
        }
        self.writeln(";");
    }

    /// Writes a `reflexivity` block whose every proofgoal is discharged by the
    /// negation of a trivial goal, which is contradicting on its own.
    ///
    /// `num_premises` is the number of *specification* constraints of the
    /// order. Nothing of them is written here — but the block written here is
    /// read back by a checker, and when it re-runs `proof` the `OrderProofRule`
    /// pushes one substituted premise per specification constraint into the
    /// order's sub-database *before* the first `proofgoal` pushes its negated
    /// goal. Each of those premises takes
    /// an output id. Skipping them here made every `qed : <id>` hint name a
    /// premise instead of the negated goal, so an order with a non-empty
    /// `spec` and an auto-proven reflexivity elaborated into a proof that does
    /// not re-check ("The constraint with ID n is not contradicting, as
    /// specified by the hint").
    pub fn write_trivial_reflexivity_subproof(
        &mut self,
        num_premises: usize,
        num_proof_goals: usize,
    ) {
        self.write_indent();
        self.writeln("reflexivity");
        self.inc_indent();
        self.write_indent();
        self.writeln("proof");
        self.inc_indent();
        self.current_id += num_premises;
        for id in 1..=num_proof_goals {
            self.write_proofgoal(
                &ProofgoalID::Internal(id),
                Option::<&Rc<DBConstraint>>::None,
            );
            self.write_qed_with_next_id();
        }
        self.write_qed();
        self.dec_indent();
        self.write_indent();
        self.writeln("end;")
    }

    /// Writes a proofgoal reference: `#id` for internal goals, else the constraint's output ID.
    pub fn write_proofgoal_id(
        &mut self,
        goal_id: &ProofgoalID,
        constraint_lookup: Option<&impl ConstraintLookup>,
    ) {
        match goal_id {
            ProofgoalID::Internal(id) => {
                self.write("#");
                self.write_display(id);
                self.end_line();
            }
            ProofgoalID::Database(id) => {
                let id = *id as usize;
                let constraint = constraint_lookup
                    .expect("cannot elaborate database id without constraint or database")
                    .get_entry_usize(id)
                    .expect("constraint already accessed before");
                let out_id = constraint
                    .get_out_id(id)
                    .expect("database proofgoal should have same ID as a database constraint");
                self.write_display(out_id);
                self.end_line();
            }
        }
    }

    /// Write that the next constraint in the subproof is equal to a found constraint, showing contradiction.
    pub fn write_existing_constraint_subproof_tail(&mut self, found_constraint: &Rc<DBConstraint>) {
        let found_constraint_id = found_constraint
            .get_out_id(found_constraint.get_some_id())
            .expect("should have output ID");
        self.write_indent();
        self.write("pol ");
        self.write_inc_id();
        self.write(" ");
        self.write_display(found_constraint_id);
        self.writeln(" + ;");
        self.write_qed_with_next_id();
    }

    /// Write a `delc` step with an explicit subproof where the deleted constraint is equivalent to a constraint in the database.
    pub fn write_existing_constraint_checked_deletion(
        &mut self,
        deletion_id: usize,
        found_constraint: &Rc<DBConstraint>,
    ) {
        self.write_delc_subproof_header(
            deletion_id,
            Some(&Substitution::with_size(0)),
            Option::<&VarNameManager>::None,
        );
        self.write_existing_constraint_subproof_tail(found_constraint);
    }

    /// Writes the subproof for a proofgoal discharged by an equal constraint
    /// already in the database.
    ///
    /// `goal_constraint` is the goal itself and `found_constraint` the
    /// database constraint that matched it: two different constraints that
    /// merely compare equal, each with its own output IDs. The header names
    /// the *goal* (a `ProofgoalID::Database(id)` is written as the output ID
    /// registered for input ID `id`, which only the goal carries), while the
    /// body cites the *found* constraint. Passing the found constraint for
    /// both aborts the elaborator on any goal this path reaches.
    pub fn write_existing_constraint_subproof(
        &mut self,
        goal_id: &ProofgoalID,
        goal_constraint: &Rc<DBConstraint>,
        found_constraint: &Rc<DBConstraint>,
    ) {
        self.write_proofgoal(goal_id, Some(goal_constraint));
        self.write_existing_constraint_subproof_tail(found_constraint);
    }

    /// Writes a RUP contradiction subproof body: the `rup >= 1` line and its `qed`.
    pub fn write_rup_contradiction_subproof_tail(
        &mut self,
        introduces_negated_goal: bool,
        rup_hints: &[RUPHint],
    ) {
        self.write_indent();
        self.write("rup >= 1 :");
        if introduces_negated_goal {
            let neg_proofgoal_id = self.inc_id();
            self.write_rup_hints(rup_hints, Some(neg_proofgoal_id));
        } else {
            self.write_rup_hints(rup_hints, None);
        }
        self.writeln(";");
        self.write_qed_with_next_id();
    }

    /// Write a proofgoal subproof that contradiction is implied by RUP.
    pub fn write_rup_contradiction_subproof(
        &mut self,
        goal_id: ProofgoalID,
        rup_constraint: Option<&Rc<DBConstraint>>,
        introduces_negated_goal: bool,
        rup_hints: &[RUPHint],
    ) {
        self.write_proofgoal(&goal_id, rup_constraint);
        self.write_rup_contradiction_subproof_tail(introduces_negated_goal, rup_hints);
    }

    /// Write a `delc` step with an explicit subproof where the deleted constraint is implied by RUP.
    pub fn write_rup_checked_deletion(&mut self, deletion_id: usize, rup_hints: &[RUPHint]) {
        self.write_delc_subproof_header(
            deletion_id,
            Some(&Substitution::with_size(0)),
            Option::<&VarNameManager>::None,
        );
        self.write_rup_contradiction_subproof_tail(true, rup_hints);
    }

    /// Writes a subproof for autoproving of a substituted implication proofgoal.
    #[allow(clippy::too_many_arguments)]
    pub fn write_substituted_implication_subproof(
        &mut self,
        goal_id: &ProofgoalID,
        implied_constraint: &Rc<DBConstraint>,
        premise: &Rc<DBConstraint>,
        trail: impl ExactSizeIterator<Item = Lit>,
        assignment: &Assignment<BooleanVar>,
        rup_hints: &[RUPHint],
        var_lookup: &impl VarNameLookup,
    ) {
        let trail_length = trail.len();
        self.write_proofgoal(goal_id, Some(implied_constraint));
        let neg_proofgoal_id = self.inc_id();

        // Get substitution as constraint.
        self.write_indent();
        self.write("rup");
        for lit in trail {
            self.write(" 1 ");
            self.write(&lit.to_pretty_string(var_lookup));
        }
        self.write(" >= ");
        self.write_display(trail_length);
        self.write(" : ");
        self.write_rup_hints(rup_hints, None);
        self.writeln(" ~ ;");
        let units_constraint_id = self.inc_id();

        // Apply substitution to premise.
        let premise_id = premise.get_out_id(premise.get_some_id()).unwrap();
        self.write_pol_add_scaled(premise_id, units_constraint_id, &premise.get_max_coeff());
        self.writeln(";");
        let sub_premise_id = self.inc_id();

        // Perform the syntactic implication.
        let sub_constraint = implied_constraint.substitute(assignment);
        self.write_indent();
        self.write("ia ");
        self.write(&sub_constraint.to_pretty_string(var_lookup));
        self.write(" : ");
        self.write_display(sub_premise_id);
        self.writeln(" ;");
        let sub_implication_id = self.inc_id();

        // Derive contradiction.
        self.write_pol_add_scaled(
            neg_proofgoal_id,
            units_constraint_id,
            &implied_constraint.get_max_coeff(),
        );
        self.write(" ");
        self.write_display(sub_implication_id);
        self.writeln(" + ;");
        self.write_qed_with_next_id();
    }

    /// Write a `deld`-rule step.
    pub fn write_derived_deletions(
        &mut self,
        derived_ids: &[usize],
        database: &impl ConstraintLookup,
    ) {
        self.write("deld");
        for &index in derived_ids.iter() {
            self.write(" ");
            self.write_constraint_out_id(database, index);
        }
        self.writeln(";");
    }

    /// Writes `delc <id> ...;` for core deletions whose obligation this run did
    /// **not** discharge.
    ///
    /// See [`Self::write_unchecked_deletion`] for what the bare form means and
    /// why it is safe. This is the same line for the case where the deletion
    /// check was never attempted (`--unchecked-deletion`, or any point after an
    /// earlier fallback has already lowered the guarantee), rather than
    /// attempted and failed.
    pub fn write_core_deletions_no_subproof(
        &mut self,
        core_ids: &[usize],
        database: &impl ConstraintLookup,
    ) {
        self.write("delc");
        for &index in core_ids.iter() {
            self.write(" ");
            self.write_constraint_out_id(database, index);
        }
        self.writeln(";");
    }

    /// Writes `delc <id>;` for a core deletion whose check this run attempted,
    /// failed, and fell back from.
    ///
    /// **The bare form is not "unchecked deletion" in the proof format.** There
    /// is no such rule: `delc` is documented (`proof_format_overview.md`,
    /// "(delc) Delete Core Constraint") as `del id` restricted to the core set,
    /// and deleting from the core is what carries the deletion obligation. So
    /// the line written here *states* the obligation this run dropped, and any
    /// consumer of the elaborated proof must either discharge it or lower its
    /// own guarantee exactly as this run did. The artifact therefore asks for
    /// at least as much as the run established, never less — a consumer that
    /// reads `delc <id>;` as licence to remove a core constraint for free is
    /// unsound on hand-written proofs too, not only on elaborated ones.
    ///
    /// What the bare form does *not* do is claim the obligation was met, and
    /// that is visible in the artifact: every core deletion the elaborator
    /// discharges is written in the subproof form by
    /// [`Self::write_existing_constraint_checked_deletion`],
    /// [`Self::write_rup_checked_deletion`] or
    /// [`Self::write_delc_subproof_header`] — `delc <id> : <witness> : subproof
    /// ... qed;` — and never as a bare `delc <id>;`. A bare `delc` in an
    /// elaborated proof means, and only ever means, "this run did not discharge
    /// this deletion". `tests/elaboration_unchecked_deletion.rs` pins both
    /// halves of that, because it is what makes the round trip faithful.
    pub fn write_unchecked_deletion(&mut self, out_id: usize) {
        self.write("delc ");
        self.write_display(out_id);
        self.writeln(";");
    }

    /// Write an empty `aux` variables line for an order definition.
    pub fn write_empty_aux(&mut self) {
        self.write_indent();
        self.writeln("aux;");
    }

    /// Write the end of a subcontext, which can be `qed` or `end` depending on the type of subcontext that is ended.
    pub fn write_subcontext_end(
        &mut self,
        qed: bool,
        optional_hint: Option<isize>,
        database: &impl ConstraintLookup,
    ) {
        self.dec_indent();
        self.write_indent();
        if qed {
            self.write("qed");
        } else {
            self.write("end");
        }
        if let Some(hint) = optional_hint {
            self.write(" : ");
            self.write_constraint_out_id(database, hint as usize);
        }
        self.writeln(";");
    }

    /// Write the `obju`-rule header.
    pub fn write_objective_update(
        &mut self,
        update_type: ObjectiveUpdateType,
        objective: &PBObjective,
        var_lookup: &impl VarNameLookup,
    ) {
        self.write("obju");
        self.write(" ");
        self.write_display(update_type);
        self.write(" ");
        self.write(&objective.to_pretty_string(var_lookup));
        self.writeln(" : subproof");
        self.inc_indent();
    }

    /// Write a solution logging rule. The `rule_output` deteimines the type of the solution logging rule.
    pub fn write_solution(
        &mut self,
        rule_output: &SolutionRuleOutput,
        solution: &Assignment<BooleanVar>,
        objective_value: Option<&BigInt>,
        var_lookup: &impl VarNameLookup,
    ) {
        match rule_output {
            SolutionRuleOutput::None => self.write("sol"),
            SolutionRuleOutput::Improving => self.write("soli"),
            SolutionRuleOutput::Excluding => self.write("solx"),
        }
        self.write(" ");
        self.write(&solution.to_pretty_string(var_lookup));
        if let Some(value) = objective_value {
            self.write(" : ");
            self.write_display(value);
        }
        self.writeln(";");
    }

    /// Write a `load_order`-rule.
    pub fn write_load_order(
        &mut self,
        name: Option<&str>,
        lits: &[Lit],
        var_lookup: &impl VarNameLookup,
    ) {
        self.write(keywords::LOAD_ORDER);
        self.write(" ");
        if let Some(name) = name {
            self.write(name);
            for &lit in lits {
                self.write(" ");
                if lit.is_negated() {
                    self.write("~");
                }
                self.write(var_lookup.get_name(lit.get_var()));
            }
        }
        self.writeln(";");
    }
}
