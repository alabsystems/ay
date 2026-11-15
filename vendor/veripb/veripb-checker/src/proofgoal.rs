//! Datastructure for a [`Proofgoal`] of a top-level subproof.

use std::{
    fmt::{Display, Formatter},
    rc::Rc,
};

use colored::{ColoredString, Colorize};
use veripb_formula::prelude::*;
use veripb_rules::ProofgoalID;

use crate::{prelude::*, rules::ScopeId};

/// [`Proofgoal`] represents a subproof proof obligation.
#[derive(Debug, Default)]
pub struct Proofgoal {
    /// The set of extra premises in the check.
    premises: Vec<Rc<DBConstraint>>,
    /// The single constraint to be checked for entailment; assumed to be False if [`None`].
    conclusion: Option<Rc<DBConstraint>>,
    /// Restrictions that proofgoal can only be used in a specific scope if a scope is loaded.
    scope_restriction: Option<ScopeId>,
    /// An optional proofgoal means that it can be proven if wanted but it is not required.
    optional: bool,
}

impl Proofgoal {
    /// Construct a new [`Proofgoal`] where the single constraint `concl` has to be shown.
    ///
    /// The scope in which this [`Proofgoal`] can be proven may be restricted by `scope_restriction` and the [`Proofgoal`] might be optional.
    pub fn mk_single_constraint(
        concl: Rc<DBConstraint>,
        scope_restriction: Option<ScopeId>,
        optional: bool,
    ) -> Proofgoal {
        Proofgoal {
            premises: Vec::new(),
            conclusion: Some(concl),
            scope_restriction,
            optional,
        }
    }

    /// Construct a [`Proofgoal`] where contradiction has to be shown using additional `premises`.
    ///
    /// The scope in which this [`Proofgoal`] can be proven may be restricted by `scope_restriction`.
    pub fn mk_multi_constraint(
        premises: Vec<Rc<DBConstraint>>,
        scope_restriction: Option<ScopeId>,
    ) -> Proofgoal {
        Proofgoal {
            premises,
            conclusion: None,
            scope_restriction,
            ..Default::default()
        }
    }

    /// Construct a [`Proofgoal`] where the constraint `concl` has to be shown using additional `premises`.
    ///
    /// The scope in which this [`Proofgoal`] can be proven may be restricted by `scope_restriction`.
    pub fn mk_mixed(
        premises: Vec<Rc<DBConstraint>>,
        concl: Rc<DBConstraint>,
        scope_restriction: Option<ScopeId>,
    ) -> Proofgoal {
        Proofgoal {
            premises,
            conclusion: Some(concl),
            scope_restriction,
            ..Default::default()
        }
    }

    /// Turn the [`Proofgoal`] into a counterexample to show contradiction for the additional premises and the negated conclusion.
    pub fn into_counterexample(mut self) -> Vec<Rc<DBConstraint>> {
        if let Some(c) = self.conclusion {
            self.premises.push(Rc::new(c.negate()));
        }
        self.premises
    }

    /// Pretty print the [`Proofgoal`] for the trace.
    pub fn trace(&self, idstr: &str, var_names: &VarNameManager) {
        println!(
            "proofgoal {}: {}[{}]{}{}",
            idstr.purple(),
            if self.conclusion.is_none() { "~" } else { "" },
            self.premises
                .iter()
                .map(|c| c.to_pretty_string(var_names))
                .fold("".to_string(), |out, c| out.to_string() + ", " + c.as_str()),
            if self.conclusion.is_some() {
                " |- "
            } else {
                ""
            },
            if let Some(c) = &self.conclusion {
                c.to_pretty_string(var_names).blue()
            } else {
                "".blue()
            }
        )
    }

    /// Check if this [`Proofgoal`] can be shown in the given `scope`.
    #[inline]
    pub fn is_in_scope(&self, scope: ScopeId) -> bool {
        if let Some(restriction) = self.scope_restriction
            && restriction != scope
        {
            return false;
        }
        true
    }
}

/// Proof technique that was used to show a [`Proofgoal`].
#[derive(Debug)]
pub enum ProofTechnique {
    /// The [`Proofgoal`] conclusion is a trivial constraint.
    Trivial,
    /// The [`Proofgoal`] conclusion is equivalent to a constraint in the database.
    DBLookup,
    /// The [`Proofgoal`] conclusion is syntactically implied by an additional premise.
    PremiseImplies,
    /// The [`Proofgoal`] conclusion is syntactically implied by a constraint in the substituted database.
    DBImpliesSubstituted,
    /// The [`Proofgoal`] follows by RUP.
    IsRUP,
    /// The [`Proofgoal`] is optional and does not need to be proven.
    Optional,
}

impl Display for ProofTechnique {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Trivial => f.write_str("trivial"),
            Self::DBLookup => f.write_str("equal to a database constraint"),
            Self::PremiseImplies => f.write_str("implied by additional premise"),
            Self::DBImpliesSubstituted => {
                f.write_str("implied by a substituted database constraint")
            }
            Self::IsRUP => f.write_str("RUP"),
            Self::Optional => f.write_str("optional and does not need to be proven"),
        }
    }
}

impl Proofgoal {
    /// Try to automatically prove that the [`Proofgoal`] is implied, by showing that the conclusion can be derived using some common heuristics. If all heuristics are not successful, then an error is returned that the [`Proofgoal`] could not be automatically proven.
    ///
    /// The following heuristics are applied in order if the conclusion is to show contradiction:
    /// 1. If the [`Proofgoal`] is optional, then we can skip it.
    /// 2. Check if the database and the additional premises unit propagate to contradiction.
    ///
    /// The following heuristics are applied in order if the conclusion is to show the constraint C:
    /// 1. If the [`Proofgoal`] is optional, then we can skip it.
    /// 2. Check if C is a trivial constraint.
    /// 3. Check if C is implied by the additional `hint` constraint.
    /// 4. Check if C is equivalent to a constraint in the `database`.
    /// 5. Check if C implied by RUP.
    /// 6. Check if C substituted with unit propagations from the `database` is syntacticlly implied by any constraint in the `database` which is substituted with unit propagation from the `database`.
    #[inline]
    pub fn autoprove(
        &mut self,
        context: &mut Context,
        database: &mut Database,
        hint: &Option<Rc<DBConstraint>>,
        goal_id: ProofgoalID,
        elaborate_database_proofgoals: bool,
    ) -> Result<ProofTechnique, CheckingError> {
        if self.optional {
            return Ok(ProofTechnique::Optional);
        }

        match &self.conclusion {
            Some(constraint) => {
                // Check if constraint is trivial.
                if constraint.is_trivial() {
                    crate::kernel_bridge::consume_trivial(context, &constraint.constraint)?;
                    return Ok(ProofTechnique::Trivial);
                }

                // Check if the constraint is implied by the additional premise.
                if let Some(hint) = hint
                    && hint.implies(constraint)
                {
                    if context.config.kernel_verify {
                        match crate::kernel_bridge::verify_implication(
                            &hint.constraint,
                            &constraint.constraint,
                        ) {
                            Ok(None) => context.kernel_stats.implication_verified += 1,
                            Ok(Some(reason)) => context.kernel_stats.skip(reason),
                            Err(err) => return Err(err),
                        }
                    }
                    return Ok(ProofTechnique::PremiseImplies);
                }

                // Check if constraint already exists in the database.
                database.update_unique_index(&mut context.propagation_engine)?;
                if let Some(found_constraint) = database.lookup(constraint)
                    && (!context.only_core || found_constraint.is_core_constraint())
                {
                    crate::kernel_bridge::consume_db_lookup(
                        context,
                        &constraint.constraint,
                        &found_constraint.constraint,
                    )?;
                    if elaborate_database_proofgoals
                        && let Some(elaborator) = context.elaborator.as_mut()
                    {
                        elaborator.write_existing_constraint_subproof(
                            &goal_id,
                            constraint,
                            found_constraint,
                        );
                    }
                    return Ok(ProofTechnique::DBLookup);
                }

                context.propagation_engine.collect_kernel_certificate =
                    context.config.kernel_verify;
                database.update_propagation_index(&mut context.propagation_engine)?;
                let result = context.propagation_engine.reverse_unit_propagation_check(
                    &context.var_names,
                    self.premises.as_slice(),
                    Some(constraint),
                    context.only_core,
                    context.elaborator.is_some(),
                    false,
                );

                if result?.is_conflict() {
                    crate::kernel_bridge::consume_rup_conflict(
                        context,
                        database,
                        Some(&constraint.constraint),
                    )?;
                    if let Some(elaborator) = context.elaborator.as_mut() {
                        elaborator.write_rup_contradiction_subproof(
                            goal_id,
                            Some(constraint),
                            true,
                            &context.propagation_engine.rup_hints,
                        );
                    }
                    return Ok(ProofTechnique::IsRUP);
                }

                // Check if substituted constraint is implied by any constraint in the substituted database.
                if let Ok(hint) = check_substituted_implication(context, database, constraint, None)
                {
                    if let Some(elaborator) = context.elaborator.as_mut() {
                        context
                            .propagation_engine
                            .collect_propagated_assignment_hints();
                        let trail = context.propagation_engine.get_trail();

                        let premise = database.get_entry_usize(hint as usize)?;
                        elaborator.write_substituted_implication_subproof(
                            &goal_id,
                            constraint,
                            premise,
                            trail.trail.iter().map(|p| p.lit),
                            &trail.assignment,
                            &context.propagation_engine.rup_hints,
                            &context.var_names,
                        );
                    }
                    if context.config.kernel_verify {
                        // Re-derive the accept through the proved kernel: the
                        // trail is the propagated assignment the acceptance
                        // substituted with (the same state the elaborator
                        // branch above consumes), and the source is the
                        // database constraint the check found.
                        let premise = database.get_entry_usize(hint as usize)?;
                        let outcome = crate::kernel_bridge::verify_substituted_implication(
                            &premise.constraint,
                            &constraint.constraint,
                            context.propagation_engine.get_trail(),
                        );
                        match outcome {
                            Ok(None) => context.kernel_stats.substituted_implication_verified += 1,
                            Ok(Some(reason)) => context.kernel_stats.skip(reason),
                            Err(err) => return Err(err),
                        }
                    }
                    return Ok(ProofTechnique::DBImpliesSubstituted);
                }

                if context.config.trace_failed {
                    context.propagation_engine.reverse_unit_propagation_check(
                        &context.var_names,
                        self.premises.as_slice(),
                        Some(constraint),
                        context.only_core,
                        false,
                        true,
                    )?;
                }
            }
            None => {
                // If we do elaboration, add output constraint IDs to goal constraints and get the output proof buffer, as it might be required if a check succeeds.
                if let Some(elaborator) = context.elaborator.as_mut() {
                    for constraint in self.premises.iter_mut() {
                        constraint.set_out_id(0, elaborator.inc_id());
                    }
                }

                // Check if proofgoal constraints are RUP.
                context.propagation_engine.collect_kernel_certificate =
                    context.config.kernel_verify;
                database.update_propagation_index(&mut context.propagation_engine)?;
                if context
                    .propagation_engine
                    .reverse_unit_propagation_check(
                        &context.var_names,
                        self.premises.as_slice(),
                        None,
                        context.only_core,
                        context.elaborator.is_some(),
                        context.config.trace_failed,
                    )?
                    .is_conflict()
                {
                    crate::kernel_bridge::consume_rup_conflict(context, database, None)?;
                    if let Some(elaborator) = context.elaborator.as_mut() {
                        elaborator.write_rup_contradiction_subproof(
                            goal_id,
                            None,
                            false,
                            &context.propagation_engine.rup_hints,
                        );
                    }
                    return Ok(ProofTechnique::IsRUP);
                }
            }
        }
        Err(CheckingError::AutoprovingFailed(goal_id))
    }

    /// Pretty print that the constraint have been automatically proven using the `technique` for the trace.
    #[inline]
    pub fn trace_autoproven(&self, colored_id: ColoredString, technique: ProofTechnique) {
        println!("    proofgoal {colored_id} is {technique}");
    }

    /// Get and unwrap the conclusion constraint for this [`Proofgoal`].
    #[inline]
    pub fn unwrapped_conclusion(&self) -> &Rc<DBConstraint> {
        self.conclusion
            .as_ref()
            .expect("Expected a proofgoal with a specified conclusion!")
    }
}
