//! Submodule defining the [`Checkable`] trait for a rule and implementing the trait for all [`VeriPBRule`]s.

mod assertion;
mod comment;
pub mod conclusion;
mod core;
pub mod cutting_planes;
mod define_order;
pub mod deletion;
mod dom_strengthening;
pub mod end_proof;
mod end_subproof;
mod end_time;
mod equal_objective;
mod equal_preserved;
mod equals;
mod fail;
mod formula;
mod header;
mod implication;
mod is_deleted;
mod load_order;
mod objective_update;
mod order_aux_vars;
mod order_def;
mod order_def_constraint;
mod order_fresh_aux1;
mod order_fresh_aux2;
mod order_fresh_right_vars;
mod order_left_vars;
mod order_proof;
mod order_reflexivity;
mod order_right_vars;
mod order_specification;
mod order_transitivity;
mod order_vars;
mod output;
mod preserved_add;
mod preserved_rm;
mod proof_by_contradiction;
mod proofgoal;
mod red_strengthening;
mod rup;
mod scope;
mod set_level;
mod solution_logging;
mod start_time;
mod strengthening_to_core;
mod unimplemented;

use crate::context::Subcontext;
use spire_enum::prelude::{delegate_impl, delegated_enum};
use veripb_formula::prelude::DBConstraint;
use veripb_propagator::propagation_engine::PropagationEngine;

pub use veripb_rules::VeriPBRule;
use veripb_rules::elaboration::Elaboratable;
pub use veripb_rules::prelude::*;

use crate::{
    context::Context,
    database::Database,
    deletion_sequence::DeletionSequenceEnum,
    error::CheckingError,
    rules::{
        conclusion::ConclusionChecker, deletion::DeletionChecker, end_subproof::EndSubproofChecker,
        load_order::LoadOrderChecker, proofgoal::ProofgoalChecker,
        solution_logging::SolutionChecker,
    },
};

use std::{fmt::Debug, rc::Rc};

/// Trait for a [`VeriPBRule`] that is [`Checkable`] by the VeriPB [`ForwardsChecker`](crate::checker::ForwardsChecker).
pub trait Checkable: Debug + Elaboratable {
    /// Check the conditions for the rule and return the derived constraints.
    fn compute(
        &mut self,
        _context: &mut Context,
        _database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError>;

    /// Return the ids of constraints deleted by the rule.
    #[inline]
    fn get_deleted<'a>(
        &'a self,
        _database: &Database,
    ) -> Result<Option<DeletionSequenceEnum<'a>>, CheckingError> {
        Ok(None)
    }

    /// Get the constraint ID returned by this constraint. This is currently mainly used for `i` and `e` to get the constraint ID of the corresponding constraint.
    #[inline]
    fn get_returned_id(&self) -> Option<isize> {
        None
    }

    /// Returns `true` if the rule can be used within a subproof.
    ///
    /// By default, this function returns `false`. To change this behaviour, manually implement this function.
    #[inline]
    fn is_subproof_friendly(&self) -> bool {
        false
    }

    /// Return `true` if resulting constraints are added to the core set instead of the derived set by default.
    #[inline]
    fn add_constraints_to_core(&self, _context: &Context) -> bool {
        false
    }

    /// The taint reason recorded for a constraint this rule adds to the
    /// database that the kernel bridge did not justify (see
    /// [`crate::kernel_bridge::KernelShadowDb`]).
    ///
    /// The default makes *silence the tainted case*: a rule that adds a
    /// constraint without offering the bridge a justification produces a
    /// named hole, never a trusted slot. Rules whose acceptance rests on a
    /// meta-step the proved kernel does not model override this with the
    /// name of that meta-step, so the composition census reads like the
    /// coverage census.
    #[inline]
    fn kernel_slot_taint(&self) -> &'static str {
        "rule-not-kernel-justified"
    }

    /// Returns `true` if the rule swaps out the currently considered database.
    #[inline]
    fn swaps_database(&self) -> bool {
        false
    }

    /// Get the new database to be swapped out.
    fn get_new_database(&mut self) -> (Database, PropagationEngine) {
        unreachable!()
    }

    /// Give the old database to the rule to handle it.
    fn handle_old_database(
        &mut self,
        _context: &mut Context,
        _database: Database,
        _prop_engine: PropagationEngine,
    ) {
        unreachable!()
    }
}

/// Generate enum for [`Checkable`] rules and provide function to cast a [`VeriPBRule`] to a [`CheckableRule`].
macro_rules! define_rule_checker {
    ($($variant:ident),* $(,)?) => {
        #[delegated_enum]
        #[derive(Debug)]
        pub enum CheckableRule {
            Deletion(DeletionChecker),
            Conclusion(ConclusionChecker),
            EndSubproof(EndSubproofChecker),
            LoadOrder(LoadOrderChecker),
            Solution(SolutionChecker),
            Proofgoal(ProofgoalChecker),
            $($variant($variant),)*
        }

        impl CheckableRule {
            /// The rule's variant name, for diagnostics.
            pub fn variant_name(&self) -> &'static str {
                match self {
                    CheckableRule::Deletion(_) => "Deletion",
                    CheckableRule::Conclusion(_) => "Conclusion",
                    CheckableRule::EndSubproof(_) => "EndSubproof",
                    CheckableRule::LoadOrder(_) => "LoadOrder",
                    CheckableRule::Solution(_) => "Solution",
                    CheckableRule::Proofgoal(_) => "Proofgoal",
                    $(CheckableRule::$variant(_) => stringify!($variant),)*
                }
            }
        }

        impl From<VeriPBRule> for CheckableRule {
            fn from(rule: VeriPBRule) -> Self {
                match rule {
                    VeriPBRule::Deletion(inner) => CheckableRule::Deletion(DeletionChecker::from(inner)),
                    VeriPBRule::ConclusionRule(inner) => CheckableRule::Conclusion(ConclusionChecker::from(inner)),
                    VeriPBRule::EndSubproof(inner) => CheckableRule::EndSubproof(EndSubproofChecker::from(inner)),
                    VeriPBRule::LoadOrderRule(inner) => CheckableRule::LoadOrder(LoadOrderChecker::from(inner)),
                    VeriPBRule::SolutionRule(inner) => CheckableRule::Solution(SolutionChecker::from(inner)),
                    VeriPBRule::ProofgoalRule(inner) => CheckableRule::Proofgoal(ProofgoalChecker::from(inner)),
                    $(VeriPBRule::$variant(inner) => CheckableRule::$variant(inner),)*
                }
            }
        }
    }
}

define_rule_checker! {
    AssertionRule,
    Comment,
    DefineOrderRule,
    DominanceBasedStrengtheningRule,
    EndProof,
    EndTimerRule,
    EqualsObjectiveRule,
    EqualsRule,
    FailRule,
    FormulaCheck,
    HeaderRule,
    ImpliesRule,
    IsDeletedCheck,
    MoveToCoreRule,
    ObjectiveUpdateRule,
    ObjectiveValueRule,
    OrderAuxVariablesRule,
    OrderDefConstraintRule,
    OrderDefRule,
    OrderFreshAux1Rule,
    OrderFreshAux2Rule,
    OrderFreshRightVariablesRule,
    OrderLeftVariablesRule,
    OrderProofRule,
    OrderReflexivityRule,
    OrderRightVariablesRule,
    OrderSpecificationRule,
    OrderTransitivityRule,
    OrderVariablesRule,
    OutputRule,
    PolRule,
    PreservedAddRule,
    PreservedEqualsRule,
    PreservedRemoveRule,
    ProofByContradiction,
    RUPRule,
    RedundanceBasedStrengtheningRule,
    ScopeRule,
    SetLevelRule,
    StartTimerRule,
    StrengtheningToCoreRule,
    UnimplementedRule,
}

/// Where a rule may run when an *order definition* is the innermost open
/// context.
///
/// The six [`Subcontext`](crate::context::Subcontext) variants split in two.
/// `Subproof` and `Proofgoal` keep the problem's constraint database
/// installed, and which rules may run in them is decided by
/// [`Checkable::is_subproof_friendly`]. The other four —
/// `Order`, `Specification`, `Transitivity`, `Reflexivity` — do not:
/// `def_order`/`pre_order` and `spec` swap in a *fresh, empty* database
/// ([`Checkable::swaps_database`]) and park the problem's in the
/// [`OrderContext`](crate::order_context::OrderContext), and
/// `transitivity`/`reflexivity` run their proofs inside that sub-database.
/// A rule whose effect is a claim about the problem being checked — a
/// verdict, the objective, core/derived membership, the active order, or a
/// logged solution — is therefore not merely useless there but unsound:
/// `sol` validates its assignment by iterating the installed database, so
/// against the empty order database every assignment passes vacuously; and
/// `strengthening_to_core` moves the empty order database to core while
/// setting the *global* flag that tells `red` it need no longer preserve the
/// derived set.
///
/// The version-3 parser rules this out with its `Scope` ladder
/// (`veripb_parser::pbp_parser::utils::Scope`), which refuses a rule whose
/// declared scope is shallower than the enclosing context. The version-2
/// parser has no scope state at all — `legacy_v2::parser::line_to_rule`
/// dispatches every line through one flat match — so in a version-2 proof
/// any rule whatsoever may be written between `pre_order` and its `end`.
/// This table restates the grammar's placement rule *in the checker*, where
/// it holds for every front end and cannot be bypassed by writing the proof
/// in the older dialect.
///
/// The mapping is exhaustive over [`CheckableRule`] rather than a
/// per-rule default, so a rule added later cannot be admitted here by
/// omission: the match in
/// [`CheckableRule::order_definition_placement`] fails to compile until its
/// placement is stated.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OrderDefinitionPlacement {
    /// Refused in all four contexts, and the default reading for anything
    /// whose effect reaches the problem rather than the order being defined.
    Never,
    /// Allowed inside a `spec` block, whose whole purpose is to derive over
    /// the order's own sub-database. These are the rules the version-3
    /// grammar places at `Scope::Proofgoal` (legal at every depth) together
    /// with `red`, which it places at `Scope::Specification`.
    Specification,
    /// A structural keyword of an order definition — `vars`, `def`, `aux`,
    /// `spec`, `transitivity`, `reflexivity`, `proof` and the freshness
    /// declarations. Legal only in the body of `def_order`/`transitivity`/
    /// `reflexivity`, never at the top level and never in a `spec` block.
    Structure,
    /// Bookkeeping that touches no database, plus the block terminator, which
    /// has to be reachable wherever a block can open.
    Always,
}

impl OrderDefinitionPlacement {
    /// Whether a rule with this placement may run with `subcontext` innermost.
    ///
    /// `subcontext` is [`None`] at the top level, where everything except a
    /// structural keyword is allowed — those keywords already report a
    /// specific error of their own (`VarsNotAllowedHere` and friends), and
    /// refusing them here as well costs nothing.
    pub fn permits(self, subcontext: Option<&Subcontext>) -> bool {
        match (self, subcontext) {
            (OrderDefinitionPlacement::Always, _) => true,
            (OrderDefinitionPlacement::Structure, None) => false,
            (_, None) => true,
            // Subproofs are governed by `is_subproof_friendly`, not by this
            // table; `permits` is never consulted for them.
            (_, Some(sc)) if sc.is_subproof() => true,
            (OrderDefinitionPlacement::Specification, Some(sc)) => {
                matches!(sc, Subcontext::Specification(_))
            }
            (OrderDefinitionPlacement::Structure, Some(sc)) => {
                !matches!(sc, Subcontext::Specification(_))
            }
            (OrderDefinitionPlacement::Never, Some(_)) => false,
        }
    }
}

impl CheckableRule {
    /// This rule's [`OrderDefinitionPlacement`].
    ///
    /// Written out variant by variant on purpose: see the type's
    /// documentation for why omission must not be a way in.
    pub fn order_definition_placement(&self) -> OrderDefinitionPlacement {
        use OrderDefinitionPlacement::*;
        match self {
            // Touches no database; must stay reachable everywhere.
            CheckableRule::Comment(_)
            | CheckableRule::UnimplementedRule(_)
            // The timer rules (upstream's `timer` feature) are instrumentation:
            // they read the clock and write a report, and touch no constraint
            // database at all. Upstream places them inside subproofs by design
            // ("Allow single letter timer and timer inside subproof"), so like
            // `Comment` they have to be legal in all four contexts. Anything
            // that DID touch a database would belong in `Specification` or
            // `Never` instead -- see this type's docs for why omission must not
            // be a way in.
            | CheckableRule::StartTimerRule(_)
            | CheckableRule::EndTimerRule(_)
            // The terminator of every block, including these four.
            | CheckableRule::EndSubproof(_) => Always,

            // The structural keywords of an order definition.
            CheckableRule::OrderAuxVariablesRule(_)
            | CheckableRule::OrderDefConstraintRule(_)
            | CheckableRule::OrderDefRule(_)
            | CheckableRule::OrderFreshAux1Rule(_)
            | CheckableRule::OrderFreshAux2Rule(_)
            | CheckableRule::OrderFreshRightVariablesRule(_)
            | CheckableRule::OrderLeftVariablesRule(_)
            | CheckableRule::OrderProofRule(_)
            | CheckableRule::OrderReflexivityRule(_)
            | CheckableRule::OrderRightVariablesRule(_)
            | CheckableRule::OrderSpecificationRule(_)
            | CheckableRule::OrderTransitivityRule(_)
            | CheckableRule::OrderVariablesRule(_) => Structure,

            // Derivation rules. Each adds only constraints entailed by, or
            // satisfiability-preserving over, the database it runs against,
            // so inside a `spec` block each speaks about the order being
            // defined and nothing else. `red` is the rule the specification
            // is written with; `rules::red_strengthening` separately confines
            // a specification `red` to the order's own variables.
            CheckableRule::AssertionRule(_)
            | CheckableRule::EqualsObjectiveRule(_)
            | CheckableRule::EqualsRule(_)
            | CheckableRule::FailRule(_)
            | CheckableRule::FormulaCheck(_)
            | CheckableRule::ImpliesRule(_)
            | CheckableRule::IsDeletedCheck(_)
            | CheckableRule::PolRule(_)
            | CheckableRule::ProofByContradiction(_)
            | CheckableRule::RUPRule(_)
            | CheckableRule::RedundanceBasedStrengtheningRule(_) => Specification,

            // Everything whose effect reaches past the order being defined:
            // the verdict and its footer, the objective, core/derived
            // membership, the preserved set, deletion, the active order, a
            // logged solution, a nested order definition, and the levels.
            CheckableRule::Conclusion(_)
            | CheckableRule::Deletion(_)
            | CheckableRule::DefineOrderRule(_)
            | CheckableRule::DominanceBasedStrengtheningRule(_)
            | CheckableRule::EndProof(_)
            | CheckableRule::HeaderRule(_)
            | CheckableRule::LoadOrder(_)
            | CheckableRule::MoveToCoreRule(_)
            | CheckableRule::ObjectiveUpdateRule(_)
            | CheckableRule::ObjectiveValueRule(_)
            | CheckableRule::OutputRule(_)
            | CheckableRule::PreservedAddRule(_)
            | CheckableRule::PreservedEqualsRule(_)
            | CheckableRule::PreservedRemoveRule(_)
            | CheckableRule::Proofgoal(_)
            | CheckableRule::ScopeRule(_)
            | CheckableRule::SetLevelRule(_)
            | CheckableRule::Solution(_)
            | CheckableRule::StrengtheningToCoreRule(_) => Never,
        }
    }
}

#[delegate_impl]
impl Elaboratable for CheckableRule {
    fn elaborate<
        C: veripb_rules::elaboration::ConstraintLookup,
        V: veripb_formula::prelude::VarNameLookup,
    >(
        &self,
        _elaborator: &mut veripb_rules::elaboration::Elaborator,
        _database: &C,
        _var_name_lookup: &V,
    ) -> Result<(), veripb_rules::elaboration::ElaborationError>;
}

#[delegate_impl]
impl Checkable for CheckableRule {
    fn compute(
        &mut self,
        context: &mut Context,
        database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError>;
    fn get_deleted<'a>(
        &'a self,
        database: &Database,
    ) -> Result<Option<DeletionSequenceEnum<'a>>, CheckingError>;
    fn get_returned_id(&self) -> Option<isize>;
    fn is_subproof_friendly(&self) -> bool;
    fn add_constraints_to_core(&self, context: &Context) -> bool;
    fn kernel_slot_taint(&self) -> &'static str;
    fn swaps_database(&self) -> bool;
    fn get_new_database(&mut self) -> (Database, PropagationEngine);
    fn handle_old_database(
        &mut self,
        context: &mut Context,
        database: Database,
        prop_engine: PropagationEngine,
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    use veripb_formula::prelude::{Cardinality, Lit, PBConstraintEnum, Substitution};
    use veripb_rules::{DominanceBasedStrengtheningRule, RedundanceBasedStrengtheningRule};

    fn any_constraint() -> PBConstraintEnum {
        Cardinality::from_lits(vec![Lit::from_var(0, false)], 1).into()
    }

    /// A rule that introduces a merely satisfiability-preserving constraint at top level must
    /// store it into the **core** set while strengthening-to-core is on, and into the derived set
    /// otherwise.
    ///
    /// This is not a stylistic preference. Both strengthening rules ask
    /// [`crate::database::Database::get_proofgoals`] for goals with
    /// `add_derived_goals = !context.is_strengthening_to_core`, so under the mode every derived
    /// constraint is dropped from the obligations of the next strengthening step. Dropping them
    /// is sound only while the derived set holds nothing but constraints entailed by the core
    /// set — which is exactly the invariant a rule breaks by storing a witnessed `red`/`dom`
    /// result there. `dom` carried the override from the start; `red` did not, and a bare `red`
    /// under the mode refuted satisfiable formulas until it got one. The taint each rule reports
    /// names the meta-step that makes its constraint non-entailed, so it is the right thing to
    /// key the requirement on.
    fn assert_stores_into_core_under_strengthening_to_core(rule: &impl Checkable) {
        let taint = rule.kernel_slot_taint();
        // Two shapes mark a rule whose stored constraint is not entailed:
        // `-unmodelled`, and `-premise` for the strengthening rules, whose
        // default taint now lands on the NEGATION they store while opening a
        // subproof (their own constraint is offered and justified separately).
        // Both are rules this test must cover; keying on `-unmodelled` alone
        // silently stopped covering `red` the moment it was routed.
        assert!(
            taint.ends_with("-unmodelled") || taint.ends_with("-premise"),
            "this test only covers rules whose constraint is not entailed; {taint} is not one"
        );

        let strengthening_to_core = Context {
            is_strengthening_to_core: true,
            ..Default::default()
        };
        assert!(
            rule.add_constraints_to_core(&strengthening_to_core),
            "{taint}: strengthening-to-core promises this constraint lands in the core set, and \
             the proofgoal shortcut of every later strengthening step rests on that promise"
        );
        assert!(
            !rule.add_constraints_to_core(&Context::default()),
            "{taint}: outside strengthening-to-core the constraint belongs in the derived set"
        );
    }

    #[test]
    fn redundance_based_strengthening_stores_into_core_under_strengthening_to_core() {
        for has_subproof in [false, true] {
            assert_stores_into_core_under_strengthening_to_core(
                &RedundanceBasedStrengtheningRule::new(
                    any_constraint(),
                    Substitution::default(),
                    has_subproof,
                ),
            );
        }
    }

    #[test]
    fn dominance_based_strengthening_stores_into_core_under_strengthening_to_core() {
        for has_subproof in [false, true] {
            assert_stores_into_core_under_strengthening_to_core(
                &DominanceBasedStrengtheningRule::new(
                    any_constraint(),
                    Substitution::default(),
                    has_subproof,
                ),
            );
        }
    }
}
