//! Implementation of a reflexive and transitive [`Order`] defined over pseudo-Boolean constraints.
//!
//! The [`Order`] is used for defining an order over assignments to a subset of literals, which is used in VeriPB for redundance- and dominance-based strengthening.

use std::rc::Rc;

use ahash::{HashSet, RandomState};
use itertools::izip;
use veripb_formula::prelude::*;

use crate::{order_context::OrderVariableKind, prelude::*, rules::ScopeId};

/// Order to be stored in the list of defined orders.
#[derive(Debug, Default, Clone)]
pub struct Order {
    /// Left-hand side variables of the order.
    pub left_vars: Vec<VarIdx>,
    /// Right-hand side variables of the order.
    pub right_vars: Vec<VarIdx>,
    /// Additional variables used by the order.
    pub aux_vars: Vec<VarIdx>,
    /// Constraints that define the order. All of these constraints have to be true for the order to hold.
    pub definition: Vec<Rc<DBConstraint>>,
    /// Specification constraints of the order.
    pub specification: Vec<Rc<DBConstraint>>,
    /// A vector to keep track of auxiliary variables for this order.
    pub vars_table: Vec<OrderVariableKind>,
}

impl Order {
    /// Check that all variables in the left-hand and right-hand side variables are distinct.
    pub fn check_distinct_left_and_right_variables(&self) -> bool {
        let mut vars = {
            let mut vec = self.left_vars.clone();
            vec.extend_from_slice(self.right_vars.as_slice());
            vec
        };
        vars.sort();
        vars.as_slice()
            .windows(2usize)
            .all(|a| a[0usize] != a[1usize])
    }

    /// Check that there are the same number of left-hand and right-hand side variables.
    pub fn check_symmetric_left_and_right_variables(&self) -> bool {
        self.left_vars.len() == self.right_vars.len()
    }

    /// Check that all auxiliary variables are distinct.
    pub fn check_distinct_aux_variables(&self) -> bool {
        let mut vars = self.aux_vars.clone();
        vars.sort();
        vars.as_slice()
            .windows(2usize)
            .all(|a| a[0usize] != a[1usize])
    }

    /// Set the variables `vars` to the kind `kind` in the variables lookup table.
    ///
    /// Returns true if any of the variables was already set to either `Mapped` or `Auxiliary`,
    /// including duplicates in `vars`.
    ///
    /// Don't call this with `kind` == `External`, the semantics are then undefined but safe.
    pub fn set_variables(&mut self, kind: OrderVariableKind, vars: &[VarIdx]) -> bool {
        vars.iter().any(|var| {
            if var >= &self.vars_table.len() {
                self.vars_table.resize(*var, OrderVariableKind::External);
                self.vars_table.push(kind);
                false
            } else {
                let slot = self.vars_table.get_mut(*var).unwrap();
                if slot.is_external() {
                    *slot = kind;
                    false
                } else {
                    !kind.is_external()
                }
            }
        })
    }

    /// Check if the variable with index `var` is an auxiliary variable for this [`Order`].
    pub fn is_auxiliary_variable(&self, var: VarIdx) -> bool {
        self.vars_table
            .get(var)
            .is_some_and(|kind| kind.is_auxiliary())
    }

    /// Check if the variable with index `var` is a variable used in this [`Order`].
    pub fn is_order_variable(&self, var: VarIdx) -> bool {
        self.vars_table
            .get(var)
            .is_some_and(|kind| kind.is_mapped_or_auxiliary())
    }
}

/// The currently loaded [`Order`] with the set of literals the order is loaded over and some cached data.
#[derive(Debug)]
pub struct ActiveOrder {
    /// Cached substitution of left-hand side variables to the literals the order is loaded over.
    ///
    /// Scratch buffers for the two composed substitutions, reused across calls
    /// only to avoid reallocation — they carry no state between calls that a
    /// caller could observe. The witness-independent half of each (the order
    /// variables mapped to the target literals) is written once in
    /// [`ActiveOrder::new`]; the witness-dependent half is rewritten in full by
    /// [`ActiveOrder::compose_substitution_right`] /
    /// [`ActiveOrder::compose_substitution_left`] before every use, so each
    /// getter below is a function of the substitution it is handed.
    ///
    /// These buffers used to be memoised behind `substitution_left_set` /
    /// `substitution_right_set` flags that were reset on only one of the paths
    /// that finish a subproof, and the specification getters ignored the
    /// substitution they were handed once a flag was set. That was sound only
    /// by arguments about the callers: every caller that could reach a getter
    /// with a *different* substitution than the memo was built from — a `pbc`
    /// scope with an empty witness, or a witness that took the reification
    /// early return in [`ActiveOrder::get_proofgoals`] — happened to have its
    /// goals discharged for other reasons. Premises selected here and consumed
    /// in `rules/scope.rs` must not depend on which path ran first, so there
    /// is no memo to invalidate any more.
    substitution_left: Substitution,
    /// Cached substitution of right-hand side variables to the literals the order is loaded over.
    substitution_right: Substitution,
    /// The loaded order.
    pub order: Order,
    /// The literals the order is loaded over.
    lits: Vec<Lit>,
    /// Variables of the literals the order is loaded over.
    var_set: HashSet<VarIdx>,
}

impl ActiveOrder {
    /// Construct a new active order from a defined order.
    pub fn new(order: &Order, lits: Vec<Lit>) -> Self {
        let mut substitution_left = Substitution::default();
        let mut substitution_right = Substitution::default();
        let mut var_set = HashSet::with_hasher(RandomState::with_seeds(42, 42, 42, 42));
        for (&left_var, &right_var, &target_lit) in
            izip!(order.left_vars.iter(), order.right_vars.iter(), lits.iter())
        {
            substitution_left.set(left_var, SubstitutionValue::lit(target_lit));
            substitution_right.set(right_var, SubstitutionValue::lit(target_lit));
            var_set.insert(target_lit.get_var());
        }
        Self {
            substitution_left,
            substitution_right,
            order: order.clone(),
            lits,
            var_set,
        }
    }

    /// Rebuild the witness-dependent half of `substitution_right` from
    /// `substitution`: every left variable of the order is mapped to the image
    /// of its target literal under `substitution` (the target literal itself
    /// where the witness does not touch it). Together with the
    /// right-variables-to-target-literals half written in [`ActiveOrder::new`],
    /// applying the result to the order's definition or specification spells
    /// `witness(z) {} z` for the order relation `{}`.
    ///
    /// Every left-variable entry is overwritten on every call, so the buffer's
    /// previous contents cannot leak into the result.
    ///
    /// Returns whether `substitution` touched any order variable.
    fn compose_substitution_right(&mut self, substitution: &Substitution) -> bool {
        let mut witness_touching_order_vars = false;
        for (&left_var, &target_lit) in izip!(self.order.left_vars.iter(), self.lits.iter()) {
            match substitution.get(target_lit.get_var()) {
                Some(value) => {
                    witness_touching_order_vars = true;
                    if target_lit.is_negated() {
                        self.substitution_right.set(left_var, value.into_negation())
                    } else {
                        self.substitution_right.set(left_var, value)
                    }
                }
                None => self
                    .substitution_right
                    .set(left_var, SubstitutionValue::lit(target_lit)),
            };
        }
        witness_touching_order_vars
    }

    /// Rebuild the witness-dependent half of `substitution_left` from
    /// `substitution`: the mirror image of
    /// [`ActiveOrder::compose_substitution_right`], mapping every *right*
    /// variable of the order to the image of its target literal, so that
    /// applying the result spells `z {} witness(z)`.
    fn compose_substitution_left(&mut self, substitution: &Substitution) {
        for (&right_var, &target_lit) in izip!(self.order.right_vars.iter(), self.lits.iter()) {
            match substitution.get(target_lit.get_var()) {
                Some(value) => {
                    if target_lit.is_negated() {
                        self.substitution_left.set(right_var, value.into_negation())
                    } else {
                        self.substitution_left.set(right_var, value)
                    }
                }
                None => self
                    .substitution_left
                    .set(right_var, SubstitutionValue::lit(target_lit)),
            };
        }
    }

    /// Get the proofgoals that the active order is not worsening under the `substitution`. This is used for redundance-based strengthening.
    pub fn get_proofgoals(&mut self, substitution: &Substitution) -> Vec<Proofgoal> {
        let mut proofgoals = Vec::new();

        // Optimization: if the constraint introduced is a reification, and the witness hence only touches fresh variables,
        // then the order proofgoal follows directly from reflexivity. This is such a common case that in this case we do
        // not even want to go through the order variables, since this could be a major overhead.
        if substitution.len() == 1
            && !self
                .var_set
                .contains(substitution.syntactic_support().next().unwrap())
        {
            for constraint in self.order.definition.iter() {
                proofgoals.push(Proofgoal::mk_single_constraint(
                    constraint.clone(),
                    Some(ScopeId::LessEqual),
                    true,
                ));
            }
            return proofgoals;
        }

        let witness_touching_order_vars = self.compose_substitution_right(substitution);

        for constraint in self.order.definition.iter() {
            proofgoals.push(Proofgoal::mk_single_constraint(
                Rc::new(constraint.substitute(&self.substitution_right)),
                Some(ScopeId::LessEqual),
                !witness_touching_order_vars,
            ));
        }
        proofgoals
    }

    /// Get the proofgoals that the active order is strictly improving under the `substitution`. This is used for dominance-based strengthening.
    pub fn get_proofgoals_strict(&mut self, substitution: &Substitution) -> Vec<Proofgoal> {
        let mut proofgoals = self.get_proofgoals(substitution);
        self.compose_substitution_left(substitution);

        let mut constraints = Vec::new();
        for constraint in self.order.definition.iter() {
            constraints.push(Rc::new(constraint.substitute(&self.substitution_left)));
        }
        proofgoals.push(Proofgoal::mk_multi_constraint(
            constraints,
            Some(ScopeId::GreaterEqual),
        ));

        proofgoals
    }

    /// Get the premises that the active order is not worsening under the `substitution`. This is used for redundance-based and dominance-based strengthening.
    ///
    /// The result is the order's specification under exactly the
    /// `substitution` handed in — never under one a different call composed.
    pub fn get_specification_less_equal(
        &mut self,
        substitution: &Substitution,
    ) -> Vec<Rc<DBConstraint>> {
        self.compose_substitution_right(substitution);

        let mut premises = Vec::new();
        for constraint in self.order.specification.iter() {
            premises.push(Rc::new(constraint.substitute(&self.substitution_right)));
        }
        premises
    }

    /// Get the premises that the active order is not improving under the `substitution`. This is used for dominance-based strengthening.
    ///
    /// The result is the order's specification under exactly the
    /// `substitution` handed in — never under one a different call composed.
    pub fn get_specification_greater_equal(
        &mut self,
        substitution: &Substitution,
    ) -> Vec<Rc<DBConstraint>> {
        self.compose_substitution_left(substitution);

        let mut premises = Vec::new();
        for constraint in self.order.specification.iter() {
            premises.push(Rc::new(constraint.substitute(&self.substitution_left)));
        }
        premises
    }
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;

    use veripb_formula::prelude::{Cardinality, DBHeader};

    use super::*;

    /// `u0 <= v1` spelled as the single definition/specification constraint
    /// `~u0 + v1 >= 1`, over left variable 0 and right variable 1.
    fn constraint_over_order_vars() -> Rc<DBConstraint> {
        Rc::new(DBConstraint {
            header: RefCell::new(DBHeader::default()),
            constraint: Cardinality::from_lits(
                vec![Lit::from_var(0, true), Lit::from_var(1, false)],
                1,
            )
            .into(),
        })
    }

    /// An [`ActiveOrder`] for that order, loaded on the single target literal
    /// `x2`.
    fn active_order() -> ActiveOrder {
        let order = Order {
            left_vars: vec![0],
            right_vars: vec![1],
            definition: vec![constraint_over_order_vars()],
            specification: vec![constraint_over_order_vars()],
            ..Default::default()
        };
        ActiveOrder::new(&order, vec![Lit::from_var(2, false)])
    }

    /// A witness mapping the order's target variable `x2` to `x<var>`.
    fn witness_mapping_target_to(var: VarIdx) -> Substitution {
        let mut witness = Substitution::default();
        witness.set(2, SubstitutionValue::lit(Lit::from_var(var, false)));
        witness
    }

    /// The calls a strengthening rule makes before its scopes ask for the
    /// specification premises, each of which composes a substitution into the
    /// scratch buffers that the premises must *not* inherit.
    fn earlier_compositions() -> [fn(&mut ActiveOrder); 3] {
        [
            // A fresh order: nothing composed yet.
            |_| (),
            // `red`/`delc` proofgoal generation for a witness touching the
            // order's target variable.
            |active| drop(active.get_proofgoals(&witness_mapping_target_to(3))),
            // The same, for a reification witness that takes the early return
            // in `get_proofgoals` — the path that used to leave the buffers
            // entirely unrefreshed.
            |active| {
                let mut fresh_var_witness = Substitution::default();
                fresh_var_witness.set(5, SubstitutionValue::FALSE);
                drop(active.get_proofgoals(&fresh_var_witness));
            },
            // `get_proofgoals_strict` is exercised separately in the
            // greater-equal test below: it composes the left buffer too.
        ]
    }

    /// Observation A of the ninth red-team round: these premises used to be
    /// memoised behind never-invalidated flags, so a getter reached with a
    /// different substitution than the memo was built from — a `pbc` scope
    /// with an empty witness after an earlier `red`, say — served the earlier
    /// caller's premises instead of its own. The getters must be a function of
    /// the substitution they are handed, whatever ran on the order before.
    #[test]
    fn specification_less_equal_follows_the_handed_substitution() {
        for compose_earlier in earlier_compositions() {
            for scope_witness in [Substitution::default(), witness_mapping_target_to(4)] {
                let mut active = active_order();
                compose_earlier(&mut active);
                let premises = active.get_specification_less_equal(&scope_witness);
                let expected = active_order().get_specification_less_equal(&scope_witness);
                assert_eq!(premises.len(), expected.len());
                for (premise, expected) in izip!(premises.iter(), expected.iter()) {
                    assert_eq!(
                        premise.constraint, expected.constraint,
                        "a less-equal specification premise depended on an earlier call's \
                         substitution rather than the one handed in"
                    );
                }
            }
        }
    }

    /// The composed substitutions are not just *which* substitution was used
    /// but *how*: an order loaded on a negated literal maps its order
    /// variables to the negation-corrected witness images. Pinned against
    /// hand-built substitutions because the corpus exercises a negated-target
    /// order exactly once (`dominance_load_order_literal`), with goals easy
    /// enough that dropping the correction there still verifies.
    #[test]
    fn negated_target_literals_negate_the_witness_image() {
        // The same one-variable order, loaded on the NEGATED literal ~x2; the
        // witness maps x2 -> x3, so the witness image of the target ~x2 is ~x3.
        let order = Order {
            left_vars: vec![0],
            right_vars: vec![1],
            definition: vec![constraint_over_order_vars()],
            specification: vec![constraint_over_order_vars()],
            ..Default::default()
        };
        let mut active = ActiveOrder::new(&order, vec![Lit::from_var(2, true)]);
        let witness = witness_mapping_target_to(3);

        // Less-equal: the left variable stands for the witness image ~x3, the
        // right variable for the target ~x2 itself.
        let mut expected_leq = Substitution::default();
        expected_leq.set(0, SubstitutionValue::lit(Lit::from_var(3, true)));
        expected_leq.set(1, SubstitutionValue::lit(Lit::from_var(2, true)));
        let premises = active.get_specification_less_equal(&witness);
        let expected = constraint_over_order_vars().substitute(&expected_leq);
        assert_eq!(premises.len(), 1);
        assert_eq!(
            premises[0].constraint, expected.constraint,
            "the less-equal premise must negate the witness image of a negated target literal"
        );

        // Greater-equal: mirrored — the right variable becomes the witness
        // image ~x3, the left variable stays the target ~x2.
        let mut expected_geq = Substitution::default();
        expected_geq.set(0, SubstitutionValue::lit(Lit::from_var(2, true)));
        expected_geq.set(1, SubstitutionValue::lit(Lit::from_var(3, true)));
        let premises = active.get_specification_greater_equal(&witness);
        let expected = constraint_over_order_vars().substitute(&expected_geq);
        assert_eq!(premises.len(), 1);
        assert_eq!(
            premises[0].constraint, expected.constraint,
            "the greater-equal premise must negate the witness image of a negated target literal"
        );
    }

    /// The mirror of `specification_less_equal_follows_the_handed_substitution`
    /// for the strict (greater-equal) premises, whose buffer
    /// `get_proofgoals_strict` composes.
    #[test]
    fn specification_greater_equal_follows_the_handed_substitution() {
        for compose_earlier in [false, true] {
            for scope_witness in [Substitution::default(), witness_mapping_target_to(4)] {
                let mut active = active_order();
                if compose_earlier {
                    active.get_proofgoals_strict(&witness_mapping_target_to(3));
                }
                let premises = active.get_specification_greater_equal(&scope_witness);
                let expected = active_order().get_specification_greater_equal(&scope_witness);
                assert_eq!(premises.len(), expected.len());
                for (premise, expected) in izip!(premises.iter(), expected.iter()) {
                    assert_eq!(
                        premise.constraint, expected.constraint,
                        "a greater-equal specification premise depended on an earlier call's \
                         substitution rather than the one handed in"
                    );
                }
            }
        }
    }
}
