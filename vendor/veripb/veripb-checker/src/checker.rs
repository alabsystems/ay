//! Implementation of main [`ForwardsChecker`] proof processor.

use crate::context::Subcontext;
use crate::{
    config::RangeSet,
    error::ForwardsCheckerError,
    order::ActiveOrder,
    rules::{Checkable, CheckableRule, VeriPBRule},
};
use colored::Colorize;
use veripb_formula::prelude::*;
use veripb_parser::pbp_parser::proof_processor::ProofProcessor;
use veripb_rules::elaboration::{Elaboratable, Elaborator};

use crate::{context::Context, database::Database, error::CheckingError};

/// Main data structure of the VeriPB checker.
///
/// This data structure maintains the invariants of the proof.
///
/// To initalize the data structure, create a new [`ForwardsChecker`] using [`ForwardsChecker::new()`].
///
/// A rule can be checked using [`ForwardsChecker::execute_rule()`]
pub struct ForwardsChecker {
    pub context: Context,
    pub database: Database,
    returned_constraint_id: Option<isize>,
}

impl VarNameRecorder for ForwardsChecker {
    fn add_by_name(&mut self, name: &str) -> VarIdx {
        self.context.var_names.add_by_name(name)
    }
}

/// If an `active_order` is [`Some`], ensure the `var_id` is a valid auxiliary variable with respect to the order.
pub fn validate_aux_var(
    var_id: VarIdx,
    active_order: Option<&ActiveOrder>,
) -> Result<(), CheckingError> {
    if !active_order.is_none_or(|order| order.order.is_auxiliary_variable(var_id)) {
        return Err(CheckingError::InvalidAuxVar);
    }
    Ok(())
}

/// Give the auxiliary variables `vars` of a **version-2** order the version-3
/// spelling the elaborated proof has to use for them.
///
/// The version-3 grammar reads the `aux`, `fresh_aux_1` and `fresh_aux_2` lists
/// of an order with `is_var_allowed = false`, so every name in them must be an
/// `AuxiliaryVariable` token, which is to say `$`-prefixed. The version-2
/// grammar has no `$` at all. `-e` always writes version 3, so a version-2
/// order with a non-empty `aux` list elaborated into a file that does not
/// parse: "Expected an auxiliary variable or `;` but found `q1`". It checked at
/// exit 0 and elaborated at exit 0, and only re-checking the artifact showed it.
///
/// The rename is done in the variable-name table rather than at the point of
/// writing, and that is the whole reason it is correct. Every name in the
/// elaborated proof — the `aux` list, the `def` and `spec` constraints, the
/// witness of a `red` inside `spec`, the `fresh_aux_1`/`fresh_aux_2` lists, and
/// every later line that mentions the variable — is ultimately
/// `VarNameLookup::get_name` of the same [`VarIdx`]. There is one source of
/// names, so no write site can be missed and no *partial* rename is possible.
/// A partial one would be worse than the failure it fixes: it would parse, and
/// it would mean something else.
///
/// Two conditions have to hold, and neither is assumed:
///
/// * **Freshness of the new name.** No name a version-2 run can produce
///   contains `$` (see [`VarNameManager::make_auxiliary`]), so `$` + old name
///   is unused and unusable by anything else in the run. It cannot clash with a
///   name the proof introduces later either, because the new spelling is
///   registered in the table as the *same* index.
/// * **Freshness of the variable itself.** The elaborated proof is written line
///   by line as the proof is checked, so a rename only reaches lines not yet
///   written. Renaming a variable that has already been written — one that
///   occurs in the formula, which is *not* rewritten, or one an earlier proof
///   line used — is exactly the partial rename above. So the variable must be
///   one this very rule introduced: `Context::vars_known_before_rule` is the
///   size of the name table before this rule was parsed, and an index at least
///   that large has been seen nowhere before. The one older variable that is
///   still safe is one already carrying the `$` spelling, which in this dialect
///   can only mean an earlier list here renamed it. Anything else is refused
///   rather than elaborated, because no spelling of it would be faithful.
///
/// Nothing happens without `-e`: with no artifact to make well-formed there is
/// nothing to rename, and leaving the check-only path alone keeps this from
/// moving any verdict or diagnostic of a run that produces no proof.
pub fn give_version3_auxiliary_names(
    context: &mut Context,
    vars: &[VarIdx],
) -> Result<(), CheckingError> {
    // Version 3 already spells these `$name`; `make_auxiliary` would be a no-op,
    // but not entering at all keeps the version-3 path bit-for-bit as it was.
    if vars.is_empty() || context.elaborator.is_none() || context.major_version >= Some(3) {
        return Ok(());
    }
    for &var in vars {
        // A variable that is older than this rule but already carries the
        // version-3 spelling was renamed by an earlier list in this same run —
        // a second order reusing the name, say. Every occurrence written so far
        // therefore already uses that spelling, so there is nothing left to
        // make consistent and the rename below is a no-op. In a version-2 run a
        // `$` can only have come from `make_auxiliary`, because the dialect
        // cannot spell one, so this cannot be mistaken for a name the proof
        // brought with it.
        if var < context.vars_known_before_rule && !context.var_names.get_name(var).starts_with('$')
        {
            return Err(CheckingError::AuxVarNotFreshForElaboration(
                context.var_names.get_name(var).to_string(),
            ));
        }
        context.var_names.make_auxiliary(var);
    }
    Ok(())
}

/// Refuse a variable that an earlier `aux` list renamed to the version-3
/// auxiliary spelling, in a position where version 3 requires a plain name.
///
/// The rename above makes `q1` print as `$q1` everywhere, which is right for
/// the `aux`, `fresh_aux_1` and `fresh_aux_2` lists — version 3's grammar reads
/// those through `is_any_variable(_, is_var_allowed = false, is_aux_allowed =
/// true)` and accepts nothing else. It is wrong for `left`, `right` and
/// `fresh_right`, which are read with the opposite setting and reject a `$`
/// name.
///
/// So a version-2 proof that used `q1` as an auxiliary variable of one order
/// and then as a `left` variable of a second one elaborated into a version-3
/// proof that dies at parse: "Expected a variable or `;` but found `$q1`" —
/// verify 0, elaborate 0, unparseable artifact, which is the exact signature
/// the rename was added to remove, with the two namespaces swapped.
///
/// A version-2 constraint may still mention the variable: `$q1` is a legal name
/// in a version-3 constraint, and such an artifact re-checks. It is only the
/// variable *lists* that distinguish the two namespaces, so only they are
/// guarded here.
pub fn refuse_renamed_auxiliary_name(
    context: &Context,
    vars: &[VarIdx],
) -> Result<(), CheckingError> {
    if context.elaborator.is_none() || context.major_version >= Some(3) {
        return Ok(());
    }
    for &var in vars {
        let name = context.var_names.get_name(var);
        if name.starts_with('$') {
            return Err(CheckingError::RenamedAuxVarInPlainList(name.to_string()));
        }
    }
    Ok(())
}

/// [`refuse_renamed_auxiliary_name`], for rules that carry literals rather
/// than variables.
///
/// The first sweep guarded `left`, `right` and `fresh_right` and believed that
/// was the complete set of version-3 productions that reject the auxiliary
/// spelling. It was not: `load_order`'s argument list, the `sol`/`soli`/`solx`
/// solution, and a `conclusion SAT`/`BOUNDS` solution hint are all read with
/// `is_aux_allowed = false` too, and each is expressible in version 2 — so a
/// version-2 proof whose order made `q1` auxiliary and then wrote
/// `load_order simple q1`, `sol … q1` or `conclusion SAT : … q1` verified at
/// exit 0, elaborated at exit 0, and produced an artifact that died at parse.
/// The same signature the guard was added to remove, three more doors in.
pub fn refuse_renamed_auxiliary_name_in_lits(
    context: &Context,
    lits: &[Lit],
) -> Result<(), CheckingError> {
    if context.elaborator.is_none() || context.major_version >= Some(3) {
        return Ok(());
    }
    for lit in lits {
        let name = context.var_names.get_name(lit.get_var());
        if name.starts_with('$') {
            return Err(CheckingError::RenamedAuxVarInPlainList(name.to_string()));
        }
    }
    Ok(())
}

impl ProofProcessor for ForwardsChecker {
    type Error = ForwardsCheckerError;

    fn last_returned_constraint_id(&mut self) -> Option<isize> {
        self.get_returned_constraint_id()
    }

    fn process_version(&mut self, major: i64, minor: i64) {
        // Carefully update this if a major/minor version larger than 255 gets allowed!
        self.context.major_version = Some(major as u8);
        self.context.minor_version = Some(minor as u8);
    }

    fn process_var_name(
        &mut self,
        line: usize,
        name: &str,
        is_aux_var: bool,
    ) -> Result<usize, ForwardsCheckerError> {
        let var_id = self.context.var_names.add_by_name(name);
        if is_aux_var {
            validate_aux_var(var_id, self.context.active_order.as_ref())
                .map_err(|e| e.add_context(self.context.config.derivation_path.clone(), line))?;
        }
        Ok(var_id)
    }

    fn process_rule(&mut self, line: usize, rule: VeriPBRule) -> Result<(), ForwardsCheckerError> {
        self.execute_rule(line, rule)
    }

    fn should_trace(&self, line: usize) -> bool {
        self.context
            .should_trace(line, self.database.len() as isize)
    }
}

impl ForwardsChecker {
    /// Construct a new `ForwardsChecker` from an existing [`Context`] and a [`Formula`].
    ///
    /// The `formula` is used to initialize the database. The elaborator is initialized based on the elaborated proof file path given in the `config` of `context`.
    /// Under `--kernel-verify` this also runs the formula cross-check, so it
    /// can fail with a [`CheckingError::KernelDivergence`] before a single
    /// proof line has been read: the constraints the checker stored are not
    /// the constraints the formula file spells.
    pub fn new(mut context: Context, formula: Formula) -> Result<Self, ForwardsCheckerError> {
        // Defence in depth for the one invariant every unchecked accessor on the propagation
        // path rests on: that the variable-name table covers every literal of every stored
        // constraint. `PropagationEngine::init_trail` sizes the trail's `Assignment` from
        // `var_names.len()`, and the constraint scanners then read it with `get_unchecked`, so a
        // literal above that length is an out-of-bounds read on the accept/reject path -- and
        // was one, until the DIMACS CNF parser stopped returning the count its header declares
        // instead of the size of the variable space the file uses.
        //
        // Every parser is supposed to establish this (OPB and WCNF get it for free: they intern
        // each name as they meet it, so an index only exists once its table slot does), which is
        // exactly why it is worth checking once rather than trusting. It costs one pass over the
        // formula, and refusing is the safe direction: a run that cannot index its own formula
        // has no business printing a verdict about it.
        Self::check_formula_is_indexable(&context, &formula)
            .map_err(|error| error.add_context(context.config.formula_path.clone(), 0))?;

        // Initialize elaborator if needed.
        if let Some(output_file) = context.config.elaboration_path.clone() {
            let mut elaborator = Elaborator::new(output_file)?;
            elaborator.write_load_formula(formula.len());
            context.elaborator = Some(elaborator);
        }

        // Initialize database.
        let mut database = Database::from_formula(formula.constraints.clone());
        context.objective = formula.objective.clone();

        // Set up output constraint IDs for original constraints.
        if let Some(elaborator) = context.elaborator.as_mut() {
            for (orig_id, constraint) in database.entries.iter_mut().flatten().enumerate() {
                constraint.set_out_id(orig_id + 1, elaborator.inc_id());
            }
        }

        // Keep original constraints and objective.
        context.original_constraints = formula.constraints;
        context.original_objective = formula.objective;

        // Seed the kernel shadow database from what was actually stored
        // (`VeriPbCore.DbOk.init`; see `crate::kernel_bridge`), and — under
        // `--kernel-verify` — check that what was stored is what the formula
        // file on disk says, which `DbOk.init` itself assumes and cannot
        // establish.
        let formula_path = context.config.formula_path.clone();
        crate::kernel_bridge::shadow_init(&mut context, &database)
            .map_err(|(error, line)| error.add_context(formula_path, line))?;

        let verifier = ForwardsChecker {
            context,
            database,
            returned_constraint_id: None,
        };

        // The formula constraints are assigned IDs starting at 1, so print them
        // for full tracing or when specific IDs are selected with `--trace-ids`.
        if verifier.context.config.trace || verifier.context.config.trace_ids.is_some() {
            print_formula(
                verifier.context.config.trace,
                verifier.context.config.trace_ids.as_ref(),
                verifier.context.objective.as_ref(),
                &verifier.database,
                &verifier.context.var_names,
            );
        }

        Ok(verifier)
    }

    /// Check that every literal of the parsed formula has a slot in the variable-name table.
    ///
    /// The propagation path sizes its [`Assignment`] from `var_names.len()` and then reads it
    /// with `get_unchecked`, so this is the precondition of that `unsafe`. See the call in
    /// [`ForwardsChecker::new`].
    fn check_formula_is_indexable(
        context: &Context,
        formula: &Formula,
    ) -> Result<(), CheckingError> {
        let num_variables = context.var_names.len();
        let objective_max = formula
            .objective
            .as_ref()
            .and_then(|objective| objective.terms.keys().next_back().copied());
        let max_var = formula
            .constraints
            .iter()
            .filter_map(PBConstraintEnum::max_var_idx)
            .chain(objective_max)
            .max();
        match max_var {
            Some(index) if index >= num_variables => {
                Err(CheckingError::FormulaVariableNotInNameTable {
                    index,
                    num_variables,
                })
            }
            _ => Ok(()),
        }
    }

    /// Get the last returned constraint ID.
    ///
    /// This ID is usually the ID of the constraint that was just derived. For the `e` (equals) rule this is the ID of the constraint to which the given constraint is equal.
    pub fn get_returned_constraint_id(&mut self) -> Option<isize> {
        let result = self.returned_constraint_id;
        self.returned_constraint_id = None;
        result
    }

    /// Execute a rule.
    ///
    /// This performs the following checking in order:
    /// 1. Preliminary checks that this rule can be used.
    /// 2. Check that the rule can be applied and calculated the derived constraint.
    /// 3. Add the derived constraints to the database.
    /// 4. Elaborate the rule.
    /// 5. Delete constraints deleted by this rule.
    /// 6. Change the database.
    pub fn execute_rule(
        &mut self,
        line: usize,
        rule: VeriPBRule,
    ) -> Result<(), ForwardsCheckerError> {
        // Determine whether this rule should be traced. The next constraint ID
        // a rule introduces is the current database length.
        self.context.trace_enabled = self
            .context
            .should_trace(line, self.database.len() as isize);

        // Construct a CheckableRule from the VeriPBRule (may have extra members needed for checking)
        let mut rule: CheckableRule = rule.into();

        // Start this rule's kernel shadow bookkeeping with an empty queue of
        // offered slots (see `crate::kernel_bridge`).
        crate::kernel_bridge::shadow_begin_rule(&mut self.context);

        // A level set with `setlvl` tags constraints of the *problem*
        // database: `wiplvl` resolves the recorded indices there and nowhere
        // else, because levels and deletion are refused inside the four
        // order-definition subcontexts (see `OrderDefinitionPlacement`).
        // Those subcontexts install a scratch database instead
        // (`Subcontext::is_order_definition`), so while one is open,
        // `self.database.len()` below indexes the scratch database and must
        // not be recorded. Before this check it was: a `setlvl` before a
        // `def_order` filed every constraint of the definition's scratch
        // database under the level, and a later `wiplvl` deleted the problem
        // constraints at those indices — measured, it silently deleted
        // formula constraints the proof never tagged, and refused a
        // legitimate proof outright where a scratch index exceeded the
        // problem database. The definition's constraints need no level
        // bookkeeping of their own: they are discarded wholesale when their
        // block ends, and no deletion rule can reach them. See
        // `tests/instances/correct/version3/wipe_level_across_order_definition.pbp`.
        //
        // Read the stack *before* the rule runs: database swaps happen after
        // the additions below (step 6), so it is the pre-rule stack that says
        // which database the additions go into — at the `end` that pops an
        // order subcontext the scratch database is still installed, and at
        // the `def_order` that pushes one the problem database still is.
        let level_recording_suspended = self
            .context
            .subcontexts
            .iter()
            .any(Subcontext::is_order_definition);

        // Check that this rule may run where it is written.
        //
        // Two disjoint cases, because the two families of subcontext differ in
        // what they install. A subproof or proofgoal keeps the problem's
        // database and is filtered by `is_subproof_friendly`; the four
        // subcontexts an order definition opens install the *order's*
        // database instead and are filtered by the rule's
        // `OrderDefinitionPlacement`. Only the version-3 parser's `Scope`
        // ladder used to enforce the latter, which left every rule reachable
        // inside `pre_order ... end` in a version-2 proof — including `sol`,
        // whose check then passed vacuously against the empty order database,
        // and `strengthening_to_core`, which set its global flag after moving
        // that empty database to core. See `rules::OrderDefinitionPlacement`.
        let last_subcontext = self.context.subcontexts.last();
        if last_subcontext.is_some_and(Subcontext::is_subproof) {
            if !rule.is_subproof_friendly() {
                return Err(CheckingError::RuleNotSubproofFriendly(
                    rule.variant_name().to_string(),
                )
                .add_context(self.context.config.derivation_path.clone(), line)
                .into());
            }
        } else if !rule.order_definition_placement().permits(last_subcontext) {
            let context = last_subcontext.map_or("top level", Subcontext::kind_name);
            return Err(CheckingError::RuleNotAllowedInOrderDefinition {
                rule: rule.variant_name().to_string(),
                context,
            }
            .add_context(self.context.config.derivation_path.clone(), line)
            .into());
        }

        // Do the checks for the rule.
        let new_constraints = rule
            .compute(&mut self.context, &mut self.database)
            .map_err(|e| e.add_context(self.context.config.derivation_path.clone(), line))?;
        let num_new_constraints = new_constraints.len();

        // Add the new constraints.
        for constraint in new_constraints {
            if self.context.trace_enabled {
                println!(
                    "  ConstraintId {}: {}",
                    if rule.add_constraints_to_core(&self.context) {
                        self.database.len().to_string().yellow()
                    } else {
                        self.database.len().to_string().bright_green()
                    },
                    constraint
                        .constraint
                        .to_pretty_string(&self.context.var_names)
                        .blue()
                )
            }
            // Add constraint ID to current level — unless the constraint is
            // going into an order definition's scratch database, whose
            // indices `wiplvl` must never see (see
            // `level_recording_suspended` above).
            if !level_recording_suspended {
                if let Some(level) = self.context.current_level {
                    unsafe {
                        self.context
                            .level_ids
                            .get_unchecked_mut(level)
                            .push(self.database.len())
                    };
                }
            }
            // Mirror the addition in the kernel shadow database. This runs
            // before `add_constraint` so the id it records is the id the
            // live database is about to use.
            crate::kernel_bridge::shadow_record_added(
                &mut self.context,
                self.database.len(),
                &constraint.constraint,
                rule.kernel_slot_taint(),
            );
            // Add constraint to database.
            self.database.add_constraint(
                constraint,
                self.context.only_core || rule.add_constraints_to_core(&self.context),
            );
        }

        // Get ID of returned constraint.
        self.returned_constraint_id = rule
            .get_returned_id()
            .or_else(|| Some(std::cmp::max(self.database.len(), 1) as isize - 1));

        // Elaborate the rule.
        if let Some(elaborator) = self.context.elaborator.as_mut() {
            // Add output constraint ID for elaborated proof.
            let start_id_new_constraints = self.database.len() - num_new_constraints;
            for (constraint_id, constraint) in (start_id_new_constraints..).zip(
                self.database.entries[start_id_new_constraints..]
                    .iter()
                    .flatten(),
            ) {
                constraint.set_out_id(constraint_id, elaborator.inc_id());
            }

            rule.elaborate(elaborator, &self.database, &self.context.var_names)?;
        }

        // Delete constraints also implicit through ending subproofs.
        if let Some(deletion_sequence) = rule
            .get_deleted(&self.database)
            .map_err(|e| e.add_context(self.context.config.derivation_path.clone(), line))?
        {
            if self.context.trace_enabled {
                let deletion_string = deletion_sequence.trace_deletions(&self.database);
                if !deletion_string.is_empty() {
                    println!("  Deleting IDs: {deletion_string}");
                }
            }

            deletion_sequence
                .delete_constraints(&mut self.database, &mut self.context)
                .map_err(|e| e.add_context(self.context.config.derivation_path.clone(), line))?
        }

        // Change the currently considered database.
        if rule.swaps_database() {
            let (database, prop_engine) = rule.get_new_database();
            let old_database = std::mem::replace(&mut self.database, database);
            let old_prop_engine =
                std::mem::replace(&mut self.context.propagation_engine, prop_engine);
            rule.handle_old_database(&mut self.context, old_database, old_prop_engine);
        }

        // Close this rule off for `give_version3_auxiliary_names`: every name
        // interned up to here belongs to a rule that has been dealt with, so
        // anything the *next* rule's parse interns lands above this mark and is
        // recognisable as introduced by that rule. See `Context`.
        self.context.vars_known_before_rule = self.context.var_names.len();

        Ok(())
    }
}

/// Print the formula to the trace.
///
/// Can either trace everything, or a just selected range of ids (`trace_all` takes precedence).
pub fn print_formula(
    trace_all: bool,
    trace_ids: Option<&RangeSet>,
    objective: Option<&PBObjective>,
    database: &Database,
    var_names: &impl VarNameLookup,
) {
    if trace_all && let Some(objective) = objective {
        println!(
            "  {}: {}",
            "Objective".bright_green(),
            ("min ".to_owned() + objective.to_pretty_string(var_names).as_str()).green()
        )
    }
    for (idx, constraint) in database.entries.iter().enumerate() {
        if let Some(constraint) = constraint
            && (trace_all || trace_ids.is_some_and(|ids| ids.contains(idx)))
        {
            println!(
                "  ConstraintId {}: {}",
                idx.to_string().yellow(),
                constraint.constraint.to_pretty_string(var_names).blue()
            )
        }
    }
}
