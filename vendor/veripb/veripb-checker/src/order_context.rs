//! [`Subcontext`] used by [`ForwardsChecker`] for checking the definition of an [`Order`].

use crate::{order::Order, prelude::*};
use ahash::AHashSet;
use itertools::izip;
use veripb_formula::prelude::*;
use veripb_propagator::propagation_engine::PropagationEngine;

/// Enum for deterimining if a variable is a left/right-hand side variable, an auxiliary variable, or neither (external).
#[derive(Debug, Clone, Copy)]
#[repr(u8)]
pub enum OrderVariableKind {
    /// Variable not used for this order.
    External = 0u8,
    /// Left-hand or right-hand side variable of order.
    Mapped = 1u8,
    /// Auxiliary variable of order.
    Auxiliary = 2u8,
}

impl OrderVariableKind {
    /// Check if this variable is external.
    pub fn is_external(self) -> bool {
        self as u8 == 0u8
    }

    /// Check if this variable is used for this order.
    pub fn is_mapped_or_auxiliary(self) -> bool {
        self as u8 >= 1u8
    }

    /// Check if this variables is auxiliary for this order.
    pub fn is_auxiliary(self) -> bool {
        self as u8 == 2u8
    }
}

/// How far through an order definition the checker has read.
///
/// `def_order`/`pre_order` is a *sequence*, not a bag of blocks: `vars`, then
/// an optional `spec`, then `def`, then an optional `transitivity`, then an
/// optional `reflexivity`, then `end`. Each block appears at most once and
/// only in that position. Version 3 gets this from its grammar —
/// `Parser::def_order_rule` reads the blocks in exactly that order and errors
/// on anything else — and the checker got it from nowhere at all, because the
/// version-2 parser dispatches every line through one flat match with no
/// sequencing.
///
/// The order is not decoration. Every side condition of an order is checked
/// against the *definition*, and the definition is built by `def`:
///
/// * `OrderProofRule` builds the transitivity obligations by iterating
///   `constructed_order.definition` at the moment `proof` runs, one proofgoal
///   per definition constraint. Written before `def`, that iteration is over
///   an empty list, so `proof` / `end` with nothing in between "proved"
///   transitivity for a relation that did not yet exist — and
///   `EndSubproofChecker` then skips the real check, because
///   `transitivity_proven` is already set. A `def` supplying a 3-cycle
///   afterwards was accepted as a preorder, and one `dom` chased the cycle to
///   the empty contradiction: an exactly-one-of-three formula satisfied by
///   `x1 = 1` verified as `s VERIFIED UNSATISFIABLE`.
/// * Reflexivity goes the same way, for the same reason.
/// * A `spec` written after `def` would enter the order without having been a
///   premise of the proofs that were supposed to hold under it.
/// * Re-opening `vars` after `def` would re-pair `left` and `right` with names
///   the definition constraints do not mention.
///
/// So the sequence is stated here, once, and enforced in the checker where
/// both front ends are held to it. This is the same lesson as
/// [`crate::rules::OrderDefinitionPlacement`], one level down: that pins
/// *which* rules may appear inside an order definition, this pins *when*.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum OrderPhase {
    /// After `def_order`/`pre_order`. Only `vars` may open.
    #[default]
    BeforeVars,
    /// `vars` has closed. `spec` or `def` may open.
    Variables,
    /// `spec` has closed. Only `def` may open.
    Specification,
    /// `def` has closed. `transitivity`, `reflexivity` or `end`.
    Definition,
    /// `transitivity` has closed. `reflexivity` or `end`.
    Transitivity,
    /// `reflexivity` has closed. Only `end`.
    Reflexivity,
}

impl OrderPhase {
    /// The keyword the version-3 grammar expects next, for diagnostics.
    pub fn expected_next(self) -> &'static str {
        match self {
            OrderPhase::BeforeVars => "`vars`",
            OrderPhase::Variables => "`spec` or `def`",
            OrderPhase::Specification => "`def`",
            OrderPhase::Definition => "`transitivity`, `reflexivity` or `end`",
            OrderPhase::Transitivity => "`reflexivity` or `end`",
            OrderPhase::Reflexivity => "`end`",
        }
    }
}

/// Context for the order definition subcontext.
#[derive(Debug, Default)]
pub struct OrderContext {
    /// Name of the order.
    pub name: String,
    /// The counted-skip total when this order's definition block opened.
    ///
    /// `VeriPbCore.dbOkF_dom_from_preorder` needs ONE property of the order:
    /// transitivity. It is established by a real subproof -- `autoprove_
    /// transitivity` always declines -- whose goals discharge through the
    /// ordinary path, so an unchanged census across the whole block is what
    /// says the kernel established it rather than the checker merely
    /// accepting it.
    pub kernel_skips_at_open: usize,
    /// How far through the definition's block sequence we are. See
    /// [`OrderPhase`].
    pub phase: OrderPhase,
    /// If inside the `vars` environment of the order definition.
    pub inside_vars: bool,
    /// If the left-hand side variables have been defined.
    pub left_vars_defined: bool,
    /// If the right-hand side variables have been defined.
    pub right_vars_defined: bool,
    /// If the auxiliary variables have been defined.
    pub aux_vars_defined: bool,
    /// If inside the `def` environment of the order definition.
    pub inside_def: bool,
    /// If reflexivity has been proven for this order.
    pub reflexivity_proven: bool,
    /// If transitivity has been proven for this order.
    pub transitivity_proven: bool,
    /// The constructed order.
    pub constructed_order: Order,
    /// Temporary storage of the main database.
    pub stored_database: Box<Database>,
    /// Temporary storage of the main propagation engine.
    pub stored_prop_engine: Box<PropagationEngine>,
    /// Temporary storage of the main elaborator constraint ID.
    pub stored_elaborator_id: usize,
    /// Temporary storage of the current active order.
    pub stored_active_order: Box<Option<ActiveOrder>>,
}

impl OrderContext {
    /// Open the block named `block`, which the sequence admits only at
    /// `required`. See [`OrderPhase`].
    pub fn open_block(
        &self,
        block: &'static str,
        required: &[OrderPhase],
    ) -> Result<(), CheckingError> {
        if required.contains(&self.phase) {
            Ok(())
        } else {
            Err(CheckingError::OrderBlockOutOfSequence {
                block,
                expected: self.phase.expected_next(),
            })
        }
    }

    /// Construct a new [`OrderContext`].
    #[inline]
    pub fn new(
        name: String,
        database: Database,
        prop_engine: PropagationEngine,
        active_order: Option<ActiveOrder>,
    ) -> Self {
        OrderContext {
            name,
            stored_database: Box::new(database),
            stored_prop_engine: Box::new(prop_engine),
            stored_active_order: Box::new(active_order),
            ..Default::default()
        }
    }

    /// Get the substitution for the reflexivity proofgoals.
    #[inline]
    pub fn get_reflexivity_substitution(&self) -> Substitution {
        let mut substitution = Substitution::with_size(self.constructed_order.left_vars.len());
        for (&left, &right) in izip!(
            self.constructed_order.left_vars.iter(),
            self.constructed_order.right_vars.iter(),
        ) {
            substitution.set(right, SubstitutionValue::lit(Lit::from_var(left, false)));
        }
        substitution
    }

    /// Check that the fresh variable lists of a `transitivity` block really are
    /// what [`Self::get_transitivity_substitution`] assumes them to be.
    ///
    /// The transitivity statement is `O(u,v) /\ O(v,w) -> O(u,w)`, and it is
    /// only *that* statement if `w` (`fresh_right`) is a vector of the same
    /// length as `u` and `v` consisting of variables distinct from every
    /// variable the order already uses; likewise for the two fresh auxiliary
    /// vectors, which stand for the auxiliary variables of the `(v,w)` and
    /// `(u,w)` instances respectively.
    ///
    /// Nothing downstream re-establishes this. `get_transitivity_substitution`
    /// builds both substitutions with `izip!`, which silently *truncates* to
    /// the shortest list, so a short (or empty) `fresh_right` collapses the
    /// substitutions towards the identity; `order_proof` then pushes each
    /// definition constraint as both a premise and its own proofgoal and the
    /// "transitivity proof" is discharged by `rup >= 1` for an arbitrary,
    /// possibly cyclic, relation. A non-fresh list is just as bad: with
    /// `fresh_right` equal to `right`, the goal degenerates to
    /// `O(u,v) /\ O(v,v) -> O(u,v)`.
    ///
    /// Freshness only has to be checked against the order's own variables:
    /// `def` constraints are restricted to `left`/`right`/`aux` by
    /// [`OrderDefConstraintRule`](crate::rules), and the transitivity proof runs
    /// in the order's own sub-database, so no other variable is in scope.
    pub fn check_transitivity_variables(
        &self,
        transitivity: &TransitivityContext,
        var_names: &VarNameManager,
    ) -> Result<(), CheckingError> {
        let order = &self.constructed_order;
        for (list_name, declared_name, fresh, declared) in [
            (
                veripb_rules::keywords::FRESH_RIGHT,
                "right",
                &transitivity.fresh_right,
                order.right_vars.len(),
            ),
            (
                veripb_rules::keywords::FRESH_AUX_1,
                "aux",
                &transitivity.fresh_aux_1,
                order.aux_vars.len(),
            ),
            (
                veripb_rules::keywords::FRESH_AUX_2,
                "aux",
                &transitivity.fresh_aux_2,
                order.aux_vars.len(),
            ),
        ] {
            if fresh.len() != declared {
                return Err(CheckingError::TransitivityFreshVarsWrongLength(
                    list_name,
                    declared,
                    fresh.len(),
                    declared_name,
                ));
            }
            for &var in fresh.iter() {
                if order.is_order_variable(var) {
                    return Err(CheckingError::TransitivityFreshVarNotFresh(
                        var.to_pretty_string(var_names),
                        list_name,
                    ));
                }
            }
        }

        // Pairwise distinctness across (and within) the three fresh lists. The
        // three vectors name three different instances of the order's
        // variables, so a variable shared between them conflates the
        // instances exactly as a non-fresh variable conflates them with the
        // declared ones.
        let mut seen = AHashSet::with_capacity(
            transitivity.fresh_right.len()
                + transitivity.fresh_aux_1.len()
                + transitivity.fresh_aux_2.len(),
        );
        for (list_name, fresh) in [
            (
                veripb_rules::keywords::FRESH_RIGHT,
                &transitivity.fresh_right,
            ),
            (
                veripb_rules::keywords::FRESH_AUX_1,
                &transitivity.fresh_aux_1,
            ),
            (
                veripb_rules::keywords::FRESH_AUX_2,
                &transitivity.fresh_aux_2,
            ),
        ] {
            for &var in fresh.iter() {
                if !seen.insert(var) {
                    return Err(CheckingError::TransitivityFreshVarNotFresh(
                        var.to_pretty_string(var_names),
                        list_name,
                    ));
                }
            }
        }

        Ok(())
    }

    /// Get the substitutions for the transitivity proofgoals.
    ///
    /// Returns a tuple of the 2 substitutions that are non-trivial. The first substitution maps from left variables to right variables and right variables to the fresh right variables (required for premise). The second substitution maps from left variables to left variables and right variables to the fresh right variables (required for proofgoal).
    ///
    /// So speaking in terms of x, y, z and x R y R z, then transitivity means that x R z. So the tuple is the substitutions for (y R z, x R z).
    ///
    /// The caller must have accepted the fresh variable lists with
    /// [`Self::check_transitivity_variables`] first: the `izip!`s below
    /// truncate to the shortest list and would otherwise happily build a
    /// partial — in the worst case identity — substitution.
    #[inline]
    pub fn get_transitivity_substitution(
        &self,
        transitivity: &TransitivityContext,
    ) -> (Substitution, Substitution) {
        let mut substitution_y_z = Substitution::with_size(
            2 * self.constructed_order.left_vars.len() + self.constructed_order.aux_vars.len(),
        );
        let mut substitution_x_z = Substitution::with_size(
            self.constructed_order.left_vars.len() + self.constructed_order.aux_vars.len(),
        );
        for (&left, &right, &fresh) in izip!(
            self.constructed_order.left_vars.iter(),
            self.constructed_order.right_vars.iter(),
            transitivity.fresh_right.iter(),
        ) {
            substitution_y_z.set(right, SubstitutionValue::lit(Lit::from_var(fresh, false)));
            substitution_y_z.set(left, SubstitutionValue::lit(Lit::from_var(right, false)));
            substitution_x_z.set(right, SubstitutionValue::lit(Lit::from_var(fresh, false)));
        }
        for (&aux, &fresh_aux_1, &fresh_aux_2) in izip!(
            self.constructed_order.aux_vars.iter(),
            transitivity.fresh_aux_1.iter(),
            transitivity.fresh_aux_2.iter()
        ) {
            substitution_y_z.set(
                aux,
                SubstitutionValue::lit(Lit::from_var(fresh_aux_1, false)),
            );
            substitution_x_z.set(
                aux,
                SubstitutionValue::lit(Lit::from_var(fresh_aux_2, false)),
            );
        }

        (substitution_y_z, substitution_x_z)
    }

    /// Try to autoprove the reflexivity of the order.
    ///
    /// Currently, autoproving of reflexivity only checks if all proofgoals
    /// are trivial. Under `--kernel-verify` each substituted definition
    /// constraint's triviality is re-judged by the proved kernel (the
    /// substitution itself remains live-trusted under the witness-modelling
    /// gap, the development design notes section 5, item 5); a live/kernel
    /// disagreement is a divergence error, so the result is now fallible.
    pub fn autoprove_reflexivity(&self, context: &mut Context) -> Result<bool, CheckingError> {
        let reflexivity_substitution = self.get_reflexivity_substitution();
        for constraint in self.constructed_order.definition.iter() {
            let substituted = constraint.substitute(&reflexivity_substitution);
            if !substituted.is_trivial() {
                return Ok(false);
            }
            crate::kernel_bridge::consume_trivial(context, &substituted.constraint)?;
        }
        if let Some(elaborator) = context.elaborator.as_mut() {
            elaborator.write_trivial_reflexivity_subproof(
                self.constructed_order.specification.len(),
                self.constructed_order.definition.len(),
            );
        }
        Ok(true)
    }

    /// Try to autoprove the transitivity of the order.
    ///
    /// Currently, autoproving of transitivity is not implemented, so this always
    /// reports failure and the caller rejects the order with
    /// [`CheckingError::TransitivityProofFailed`]. Transitivity is a side
    /// condition of `def_order`, and a `def_order` block without a
    /// `transitivity` block is grammatically legal (see the development design notes), so
    /// this is a proof that has to be *rejected*, not an internal error: it must
    /// never abort the process.
    pub fn autoprove_transitivity(&self) -> bool {
        false
    }
}

/// Context for the transitivity proof subcontext.
#[derive(Debug, Default)]
pub struct TransitivityContext {
    pub inside_vars: bool,
    pub is_proven: bool,
    pub fresh_right: Vec<VarIdx>,
    pub fresh_aux_1: Vec<VarIdx>,
    pub fresh_aux_2: Vec<VarIdx>,
}

/// Context for the transitivity proof subcontext.
#[derive(Debug, Default)]
pub struct ReflexivityContext {
    pub is_proven: bool,
}

/// Context for the specification derivation inside the `spec` environment of the order.
#[derive(Debug, Default)]
pub struct SpecificationContext {
    /// Temporary storage of the database for the order definition.
    pub stored_database: Box<Database>,
    /// Temporary storage of the propagation engine for the order definition.
    pub stored_prop_engine: Box<PropagationEngine>,
    /// Temporary storage of the current elaborator constraint ID for the order definition.
    pub stored_elaborator_id: usize,
}

impl SpecificationContext {
    /// Construct a new [`SpecificationContext`] for a give `database` and `prop_engine`.
    #[inline]
    pub fn new(database: Database, prop_engine: PropagationEngine) -> SpecificationContext {
        SpecificationContext {
            stored_database: Box::new(database),
            stored_prop_engine: Box::new(prop_engine),
            ..Default::default()
        }
    }
}
