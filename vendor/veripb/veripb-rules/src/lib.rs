//! This crate provides data structures defining the VeriPB rules.
//!
//! The [`elaboration`] module provides the functionality to format rules to a file.

use std::{
    fmt::{Display, Formatter},
    rc::Rc,
};

use logos::Logos;
use malachite_bigint::BigInt;
use veripb_formula::{
    lit::Lit,
    prelude::{DBConstraint, PBConstraintEnum, PBObjective, Substitution, VarIdx},
};

pub mod elaboration;
pub mod keywords;
pub mod prelude;

/// Derive a `constraint` without any justification and optionally provide additional information.
///
/// A proof containing this rule is invalid (only valid under assertions).
#[derive(Debug)]
pub struct AssertionRule {
    /// Derived constraint.
    pub constraint: Rc<DBConstraint>,
    /// Optional list of antecedent constraint IDs.
    pub id_list: Option<Vec<isize>>,
    /// Optional name for "technique" used to derive constraint. For example, it could be possible to group assertions by their name.
    pub name: Option<String>,
    /// Optional free text hints that can be used by a justifier to elaborate an assertion.
    pub free_text: Option<String>,
}

impl AssertionRule {
    /// Construct an [`AssertionRule`] with additional information.
    pub fn new(
        constraint: PBConstraintEnum,
        id_list: Option<Vec<isize>>,
        name: Option<String>,
        free_text: Option<String>,
    ) -> Self {
        Self {
            constraint: Rc::new(DBConstraint::from(constraint)),
            id_list,
            name,
            free_text,
        }
    }

    /// Construct an [`AssertionRule`] without additional information.
    pub fn without_annotation(constraint: PBConstraintEnum) -> Self {
        Self {
            constraint: Rc::new(DBConstraint::from(constraint)),
            id_list: None,
            name: None,
            free_text: None,
        }
    }
}

/// A VeriPB comment.
#[derive(Debug)]
pub struct Comment;

/// Lower and upper bound type for `conclusion BOUNDS`.
#[derive(Debug, PartialEq, PartialOrd, Clone)]
pub enum Bound {
    /// Some integer bound.
    Bounded(BigInt),
    /// Infinity bound `INF`.
    Unbounded,
}

impl Bound {
    /// Unwrap the integer bound from a [`Bound`].
    #[inline]
    pub fn unwrap(self) -> BigInt {
        match self {
            Self::Bounded(bound) => bound,
            Self::Unbounded => {
                panic!("Cannot unwrap an unbounded bound to the value of the bound!")
            }
        }
    }
}

impl Display for Bound {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Bound::Unbounded => write!(f, "INF")?,
            Bound::Bounded(bound) => write!(f, "{bound}")?,
        }

        Ok(())
    }
}

/// Enum for different proof conclusions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Logos)]
#[logos(skip r"[ \t\r\n]")]
pub enum ConclusionResult {
    /// `conclusion SAT`
    #[token("SAT")]
    Satisfiable,

    /// `conclusion UNSAT`
    #[token("UNSAT")]
    Unsatisfiable,

    /// `conclusion BOUNDS`
    #[token("BOUNDS")]
    Bounds,

    /// `conclusion ENUMERATION_PARTIAL`
    #[token("ENUMERATION_PARTIAL")]
    EnumerationPartial,

    /// `conclusion ENUMERATION_COMPLETE`
    #[token("ENUMERATION_COMPLETE")]
    EnumerationComplete,

    /// `conclusion NONE`
    #[token("NONE")]
    None,
}

impl Display for ConclusionResult {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(
            f,
            "{}",
            match self {
                Self::Satisfiable => "SAT",
                Self::Unsatisfiable => "UNSAT",
                Self::Bounds => "BOUNDS",
                Self::EnumerationPartial => "ENUMERATION_PARTIAL",
                Self::EnumerationComplete => "ENUMERATION_COMPLETE",
                Self::None => "NONE",
            }
        )
    }
}

/// Proof conclusion footer rule.
#[derive(Debug)]
pub struct ConclusionRule {
    /// Concluding result of the proof.
    pub result: ConclusionResult,
    /// Objective lower bound or enumeration count. Only used for `conclusion BOUNDS` and the number of enumerated solutions in `conclusion ENUMERATION_*`.
    pub lower_bound_or_count: Option<Bound>,
    /// Objective upper bound. Only used for `conclusion BOUNDS`.
    pub upper_bound: Option<Bound>,
    /// Optional constraint ID hint. Used for indicating the contradicting or lower bounding constraint.
    pub constraint_id_hint: Option<isize>,
    /// Optional solution hint. Used for satisfying assignment or upper bounding solution.
    pub solution_hint: Option<Vec<Lit>>,
}

impl ConclusionRule {
    /// Construct a [`ConclusionRule`].
    #[inline]
    pub fn new(
        result: ConclusionResult,
        lower_bound_or_count: Option<Bound>,
        upper_bound: Option<Bound>,
        constraint_id_hint: Option<isize>,
        solution_hint: Option<Vec<Lit>>,
    ) -> Self {
        ConclusionRule {
            result,
            lower_bound_or_count,
            upper_bound,
            constraint_id_hint,
            solution_hint,
        }
    }
}

/// Start the environment to define an order.
#[derive(Debug)]
pub struct DefineOrderRule {
    /// The name of the order.
    pub name: String,
}

impl DefineOrderRule {
    /// Construct an [`DefineOrderRule`].
    pub fn new(name: String) -> Self {
        Self { name }
    }
}

/// Options for deleting a constraint.
#[derive(Debug, PartialEq)]
pub enum DeletionOption {
    /// Delete the constraint IDs in the given [`Vec`].
    Id(Vec<isize>),
    /// Delete all constraints with the first (inclusive) and second (exclusive) constraint ID.
    Range((isize, isize)),
    /// Delete the given constraint.
    Spec(Rc<DBConstraint>),
    /// Delete all constraints in the given level and above.
    Wipe(usize),
}

/// In which set the deleted constraints is expected to be in.
#[derive(Debug)]
pub enum DeletionOrigin {
    /// It is unknown in which set the deleted constraint is.
    Unknown,
    /// The deleted constraint should be in the core set.
    Core,
    /// The deleted constraint should be in the derived set.
    Derived,
}

/// Delete constraints from the database.
#[derive(Debug)]
pub struct Deletion {
    /// Specification of which constraints should be deleted.
    pub identifier: DeletionOption,
    /// Substitution witness for checked deletion.
    pub witness: Substitution,
    /// Start a subproof for a checked deletion.
    pub has_subproof: bool,
    /// Expected set in which the deleted constraints are.
    pub origin: DeletionOrigin,
}

impl Deletion {
    /// Construct a [`Deletion`].
    pub fn new(
        identifier: DeletionOption,
        witness: Substitution,
        has_subproof: bool,
        origin: DeletionOrigin,
    ) -> Self {
        Self {
            identifier,
            witness,
            has_subproof,
            origin,
        }
    }
}

/// Dominance-based strengthening rule.
///
/// For more details on the dominance-based strengthening rule, see [Bogaerts et. al. 2023](https://doi.org/10.1613/jair.1.14296) and [Anders et. al. 2026](https://doi.org/10.1609/aaai.v40i17.38426).
#[derive(Debug)]
pub struct DominanceBasedStrengtheningRule {
    /// Constraint to be derived by dominance-based strengthening.
    pub constraint: Rc<DBConstraint>,
    /// Substitution witness for the proofgoals.
    pub witness: Substitution,
    /// Start an explicit subproof for showing the required proofgoal.
    pub has_subproof: bool,
}

impl DominanceBasedStrengtheningRule {
    /// Construct a [`DominanceBasedStrengtheningRule`].
    pub fn new(constraint: PBConstraintEnum, witness: Substitution, has_subproof: bool) -> Self {
        Self {
            constraint: Rc::new(DBConstraint::from(constraint)),
            witness,
            has_subproof,
        }
    }
}

/// Footer rule to end the VeriPB proof.
#[derive(Debug)]
pub struct EndProof;

/// End a subcontext.
#[derive(Debug)]
pub struct EndSubproof {
    /// Optional constraint ID for a contradicting constraint.
    pub optional_hint: Option<isize>,
}

/// Construct an [`EndSubproof`].
impl EndSubproof {
    pub fn new(optional_hint: Option<isize>) -> Self {
        Self { optional_hint }
    }
}

/// Stop a used defined timer.
#[derive(Debug)]
pub struct EndTimerRule {
    /// The name of the timer.
    pub name: String,
}

impl EndTimerRule {
    /// Construct an [`EndTimerRule`].
    #[inline]
    pub fn new(name: String) -> Self {
        Self { name }
    }
}

/// Rule to check if the current objective equals the given objective.
#[derive(Debug)]
pub struct EqualsObjectiveRule {
    /// Expected objective.
    pub objective: PBObjective,
}

impl EqualsObjectiveRule {
    /// Construct an [`EqualsObjectiveRule`].
    pub fn new(objective: PBObjective) -> Self {
        Self { objective }
    }
}

/// Check that there is a constraint in the database that is equal to the expected constraint.
#[derive(Debug)]
pub struct EqualsRule {
    /// Expected constraint that should be in the database.
    pub constraint: Rc<DBConstraint>,
    /// Optional constraint ID to the constraint that should be equal to the expected constraint.
    pub hint: Option<isize>,
    /// Add the expected constraint to the database.
    pub add_result: bool,
}

impl EqualsRule {
    /// Construct an [`EqualsRule`].
    pub fn new(constraint: PBConstraintEnum, hint: Option<isize>, add_result: bool) -> Self {
        Self {
            constraint: Rc::new(DBConstraint::from(constraint)),
            hint,
            add_result,
        }
    }
}

/// Stop checking the proof.
#[derive(Debug)]
pub struct FailRule;

/// Check that the formula contains the expected number of constraints.
#[derive(Debug)]
pub struct FormulaCheck {
    // Expected number of constraints.
    pub size: usize,
}

impl FormulaCheck {
    /// Construct a [`FormulaCheck`].
    pub fn new(size: usize) -> Self {
        Self { size }
    }
}

/// Proof header.
#[derive(Debug)]
pub struct HeaderRule;

/// Check if a constraint is syntactically implied by another constraint in the database.
#[derive(Debug)]
pub struct ImpliesRule {
    /// Constraint that should be implied by another constraint in the database.
    pub constraint: Rc<DBConstraint>,
    /// Optional constraint ID to the constraint that should imply the implied constraint.
    pub hint: Option<isize>,
    /// Add the implied constraint to the database.
    pub add_result: bool,
}

impl ImpliesRule {
    /// Construct an [`ImpliesRule`].
    pub fn new(constraint: PBConstraintEnum, hint: Option<isize>, add_result: bool) -> Self {
        Self {
            constraint: Rc::new(DBConstraint::from(constraint)),
            hint,
            add_result,
        }
    }
}

/// Check if the constraint has been deleted.
#[derive(Debug)]
pub struct IsDeletedCheck {
    /// Constraint that should be deleted.
    pub constraint: Rc<DBConstraint>,
}

impl IsDeletedCheck {
    /// Construct an [`IsDeletedCheck`].
    pub fn new(constraint: PBConstraintEnum) -> Self {
        Self {
            constraint: Rc::new(DBConstraint::from(constraint)),
        }
    }
}

/// Load a previously defined order.
#[derive(Debug)]
pub struct LoadOrderRule {
    /// Name of the previously defined order.
    pub name: Option<String>,
    /// List of literals over which the order should be loaded.
    pub lits: Vec<Lit>,
}

impl LoadOrderRule {
    /// Construct a [`LoadOrderRule`].
    pub fn new(name: Option<String>, lits: Vec<Lit>) -> Self {
        Self { name, lits }
    }
}

/// Specification of how to interpret the constraint IDs.
#[derive(Debug, Logos, PartialEq, Eq)]
#[logos(skip r"[ \t\r\n]")]
pub enum IdentifierOption {
    /// Get constraints by a list of IDs.
    #[token("id")]
    Id,

    /// Get constraints in between two constraint ID including the first ID and not including the second ID.
    #[token("range")]
    Range,

    /// Get the constraint specified in OPB format.
    #[token("spec")]
    #[token("find")]
    Specification,
}

/// Move constraints to the core set.
#[derive(Debug)]
pub struct MoveToCoreRule {
    /// Specification of how to interpret the constraint IDs..
    pub identifier_option: IdentifierOption,
    /// Constraint IDs to be deleted interpreted by `identifier_option`.
    pub constraint_ids: Vec<isize>,
}

impl MoveToCoreRule {
    /// Construct a [`MoveToCoreRule`].
    #[inline]
    pub fn new(identifier_option: IdentifierOption, constraint_ids: Vec<isize>) -> Self {
        Self {
            identifier_option,
            constraint_ids,
        }
    }
}

/// Specification of how an objective is updated.
#[derive(Debug, Logos, PartialEq, Eq, Default, Copy, Clone)]
#[logos(skip r"[ \t\r\n]")]
pub enum ObjectiveUpdateType {
    /// Use specified objective as new objective.
    #[token("new")]
    #[default]
    New,

    /// Use specified objective as objective difference.
    #[token("diff")]
    Diff,
}

impl Display for ObjectiveUpdateType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ObjectiveUpdateType::New => write!(f, "new"),
            ObjectiveUpdateType::Diff => write!(f, "diff"),
        }
    }
}

/// Update the objective function.
#[derive(Debug)]
pub struct ObjectiveUpdateRule {
    /// How the objective in this rule should be applied to the current objective.
    pub update_type: ObjectiveUpdateType,
    /// New objective or objective change.
    pub objective: PBObjective,
    /// Start an explicit subproof for showing that the objective can be updated.
    pub has_subproof: bool,
}

impl ObjectiveUpdateRule {
    /// Construct an [`ObjectiveUpdateType`].
    #[inline]
    pub fn new(
        objective: PBObjective,
        update_type: ObjectiveUpdateType,
        has_subproof: bool,
    ) -> Self {
        Self {
            objective,
            update_type,
            has_subproof,
        }
    }
}

/// Introduce a solution-improving constraint that is not justified by a solution.
/// The solution-improving constraint is the constraint stating that the objective should be at smaller than the given objective value.
#[derive(Debug)]
pub struct ObjectiveValueRule {
    /// Objective value for which to introduce the solution improving constraint.
    pub value: BigInt,
}

impl ObjectiveValueRule {
    /// Construct an [`ObjectiveValueRule`].
    pub fn new(value: BigInt) -> Self {
        Self { value }
    }
}

/// Define the auxiliary variables of an order in an order definition environment.
#[derive(Debug)]
pub struct OrderAuxVariablesRule {
    /// List of auxiliary variable.
    pub vars: Vec<VarIdx>,
}

impl OrderAuxVariablesRule {
    /// Construct an [`OrderAuxVariablesRule`].
    #[inline]
    pub fn new(vars: Vec<VarIdx>) -> Self {
        Self { vars }
    }
}

/// Add constraint to the definition of an order inside an order definition environment.
#[derive(Debug)]
pub struct OrderDefConstraintRule {
    /// Constraint to be added to the order definition.
    pub constraint: Rc<DBConstraint>,
}

impl OrderDefConstraintRule {
    /// Construct an [`OrderDefConstraintRule`].
    pub fn new(constraint: PBConstraintEnum) -> Self {
        Self {
            constraint: Rc::new(DBConstraint::from(constraint)),
        }
    }
}

/// Start the order definition environment after which constraint can be added to the definition of the order.
#[derive(Debug)]
pub struct OrderDefRule;

/// Define the first additional auxiliary variables inside a transitivity proof environment for the definition of an order. The first auxiliary variables are the auxiliary variables for the order relating the right-hand side variables to the additional right-hand side variables.
#[derive(Debug)]
pub struct OrderFreshAux1Rule {
    /// List of first additional auxiliary variables.
    pub vars: Vec<VarIdx>,
}

impl OrderFreshAux1Rule {
    /// Construct an [`OrderFreshAux1Rule`].
    pub fn new(vars: Vec<VarIdx>) -> Self {
        Self { vars }
    }
}

/// Define the second additional auxiliary variables inside a transitivity proof environment for the definition of an order. The second auxiliary variables are the auxiliary variables for the order relating the left-hand side variables to the additional right-hand side variables.
#[derive(Debug)]
pub struct OrderFreshAux2Rule {
    /// List of second additional auxiliary variables.
    pub vars: Vec<VarIdx>,
}

impl OrderFreshAux2Rule {
    /// Construct an [`OrderFreshAux2Rule`].
    pub fn new(vars: Vec<VarIdx>) -> Self {
        Self { vars }
    }
}

/// Define the additional right-hand side variables inside a transitivity proof environment for the definition of an order.
#[derive(Debug)]
pub struct OrderFreshRightVariablesRule {
    /// List of additional right-hand side variables.
    pub vars: Vec<VarIdx>,
}

/// Construct an [`OrderFreshRightVariablesRule`].
impl OrderFreshRightVariablesRule {
    pub fn new(vars: Vec<VarIdx>) -> Self {
        Self { vars }
    }
}

/// Define the left-hand side variables of an order in an order definition environment.
#[derive(Debug)]
pub struct OrderLeftVariablesRule {
    /// List of left-hand side variables.
    pub vars: Vec<VarIdx>,
}

impl OrderLeftVariablesRule {
    /// Construct an [`OrderLeftVariablesRule`].
    pub fn new(vars: Vec<VarIdx>) -> Self {
        Self { vars }
    }
}

/// Start the proof inside a reflexivity or transitvity environment of an order definition.
#[derive(Debug)]
pub struct OrderProofRule;

#[cfg_attr(feature = "docs", katexit::katexit)]
/// Start the environment to show that the defined order is reflexive inside an order definition.
///
/// The actual proof to show reflexivity is initiated by using the [`OrderProofRule`].
/// To show that the order with order definition constraint $O(u, v, a)$ and auxiliary specification constraints $A(u, v, a)$ is reflexive, it has to be shown that the implication $A(u, u, a) \models O(u, u, a)$ holds. This shows that the order is satisfied when the same variables are on the left- and right-hand side. The variables $u$ are the left-hand side variables and $a$ are the normal auxiliary variables.
#[derive(Debug)]
pub struct OrderReflexivityRule;

/// Define the right-hand side variables of an order in an order definition environment.
#[derive(Debug)]
pub struct OrderRightVariablesRule {
    /// List of right-hand side variables.
    pub vars: Vec<VarIdx>,
}

impl OrderRightVariablesRule {
    /// Construct a [`OrderRightVariablesRule`].
    pub fn new(vars: Vec<VarIdx>) -> Self {
        Self { vars }
    }
}

/// Start the auxiliary specification derivation environment inside an order definition environment.
#[derive(Debug)]
pub struct OrderSpecificationRule;

#[cfg_attr(feature = "docs", katexit::katexit)]
/// Start the environment to show that the defined order is transitive inside an order definition.
///
/// The actual proof to show transitivity is initiated by using the [`OrderProofRule`].
/// To show that an order with definition constraints $O(u, v, a)$ and auxiliary specification constraints $A(u, v, a)$ is transitive, it has to be shown that the impliction $O(u, v, a) \wedge O(v, w, b) \wedge A(u, v, a) \wedge A(v, w, b) \wedge A(u, w, c) \models O(u, w, c)$ holds. The variables $u$, $v$, and $w$ are the left-hand side, right-hand side, and additional right-hand side variables, respectively. The variables $a$, $b$, and $c$ are the normal, first additional, and second additional auxiliary variables.
#[derive(Debug)]
pub struct OrderTransitivityRule;

/// Start the environment to define the variables of an order inside an order definition environment.
#[derive(Debug)]
pub struct OrderVariablesRule;

/// Proof output guarantee types.
#[derive(Debug, Clone, Copy, Logos, PartialEq, Eq)]
#[logos(skip r"[ \t\r\n]")]
pub enum OutputGuarantee {
    /// `output DERIVABLE ...`
    #[token("DERIVABLE")]
    Derivable,

    /// `output EQUISATISFIABLE ...`
    #[token("EQUISATISFIABLE")]
    Equisatisfiable,

    /// `output EQUIOPTIMAL ...`
    #[token("EQUIOPTIMAL")]
    Equioptimal,

    /// `output EQUIENUMERABLE ...`
    #[token("EQUIENUMERABLE")]
    Equienumerable,

    /// `output NONE`
    #[token("NONE")]
    None,
}

/// Proof output specification type. This is how the output is given.
#[derive(Debug, Clone, Copy, Logos, PartialEq, Eq)]
#[logos(skip r"[ \t\r\n]")]
pub enum OutputType {
    /// `output ... IMPLICIT`
    #[token("IMPLICIT")]
    Implicit,

    /// `output ... FILE`
    #[token("FILE")]
    File,

    /// `output ... PERMUTATION`
    #[token("PERMUTATION")]
    Permutation,

    /// No output.
    None,
}

/// Proof output rule.
#[derive(Debug)]
pub struct OutputRule {
    /// Proof output guarantee.
    pub guarantee: OutputGuarantee,
    /// Proof output specification type.
    pub output_type: OutputType,
}

impl OutputRule {
    /// Construct an [`OutputRule`].
    pub fn new(guarantee: OutputGuarantee, output_type: OutputType) -> Self {
        Self {
            guarantee,
            output_type,
        }
    }
}

/// Cutting planes derivation instructions used for reverse Polish (`pol`) notation lines.
#[derive(Debug, PartialEq, Eq)]
pub enum Instruction {
    /// Load a constraint with this ID.
    ConstraintId(isize),
    /// Load a literal axiom for this literal.
    LiteralAxiom(Lit),
    /// Apply cutting planes division to the constraint in normalized form.
    NormalizedFormDivide(BigInt),
    /// Apply Chvátal-Gomory cut division to the constraint in variable normal form.
    VariableFormDivide(BigInt),
    /// Apply a mixed integer rounding cut to the constraint in normalized form.
    NormalizedFormMIR(BigInt),
    /// Apply a mixed integer rounding cut to the constraint in variable normal form.
    VariableFormMIR(BigInt),
    /// Multiply the constraint by an integer.
    Multiply(BigInt),
    /// Weaken a variable in the constraint.
    Weaken(VarIdx),
    /// Lower the right-hand side of the constraint by an integer.
    LowerRHS(BigInt),
    /// Add two constraint together.
    Add,
    /// Saturate the constraint.
    Saturate,
}

/// Derive a constraint through a cutting planes derivation given in reverse Polish notation.
#[derive(Debug, PartialEq, Eq)]
pub struct PolRule {
    /// Cutting planes derivation in reverse Polish notation.
    pub instructions: Vec<Instruction>,
}

impl PolRule {
    /// Construct a [`PolRule`].
    pub fn new(instructions: Vec<Instruction>) -> Self {
        Self { instructions }
    }
}

/// Add a variable to the preserved set.
#[derive(Debug)]
pub struct PreservedAddRule {
    /// Variable to the preserved set.
    pub var: VarIdx,
    /// Constraint over other preserved variables defining the variable to be added.
    pub constraint: Rc<DBConstraint>,
    /// Start an explicit subproof for showing that the variable can be added to the preserved set.
    pub has_subproof: bool,
}

impl PreservedAddRule {
    /// Construct a [`PreservedAddRule`].
    pub fn new(var: VarIdx, constraint: PBConstraintEnum, has_subproof: bool) -> Self {
        Self {
            var,
            constraint: Rc::new(constraint.into()),
            has_subproof,
        }
    }
}

/// Check that the prserved set equals the expected set of variables.
#[derive(Debug)]
pub struct PreservedEqualsRule {
    /// Expected preserved set of variables.
    pub vars: Vec<VarIdx>,
}

impl PreservedEqualsRule {
    /// Construct a [`PreservedEqualsRule`].
    pub fn new(vars: Vec<VarIdx>) -> Self {
        Self { vars }
    }
}

/// Remove a variable from the preserved set.
#[derive(Debug)]
pub struct PreservedRemoveRule {
    /// Variable to be removed from the preserved set.
    pub var: VarIdx,
    /// Constraint over other preserved variables defining the variable to be removed.
    pub constraint: Rc<DBConstraint>,
    /// Start an explicit subproof for showing that the variable can be removed from the preserved set.
    pub has_subproof: bool,
}

impl PreservedRemoveRule {
    /// Construct a [`PreservedRemoveRule`].
    pub fn new(var: VarIdx, constraint: PBConstraintEnum, has_subproof: bool) -> Self {
        Self {
            var,
            constraint: Rc::new(constraint.into()),
            has_subproof,
        }
    }
}

/// Derive a constraint using a proof by contradiction.
#[derive(Debug)]
pub struct ProofByContradiction {
    /// Constraint to be derived by a proof by contradiction.
    pub constraint: Rc<DBConstraint>,
    /// Start an explicit subproof for showing the proof by contradiction.
    pub has_subproof: bool,
}

impl ProofByContradiction {
    /// Construct a [`ProofByContradiction`].
    pub fn new(constraint: PBConstraintEnum, has_subproof: bool) -> Self {
        Self {
            constraint: Rc::new(DBConstraint::from(constraint)),
            has_subproof,
        }
    }
}

/// Proofgoal identifier.
#[derive(Debug, Logos, PartialEq, Eq)]
#[logos(skip r"[ \t\r\n]")]
pub enum ProofgoalID {
    /// Internal proofgoal for the rule starting with `#` character.
    #[regex(r"#\d+", |lex| lex.slice()[1..].parse().ok())]
    Internal(usize),

    /// Proofgoal referring to a constraint in the database.
    #[regex(r"[+-]?\d+", |lex| lex.slice().parse().ok())]
    Database(isize),
}

impl Display for ProofgoalID {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ProofgoalID::Internal(id) => write!(f, "#{id}"),
            ProofgoalID::Database(id) => write!(f, "{id}"),
        }
    }
}

/// Start a proofgoal subproof.
#[derive(Debug)]
pub struct ProofgoalRule {
    /// Proofgoal identifier for which to start a subproof.
    pub proofgoal_id: ProofgoalID,
}

impl ProofgoalRule {
    /// Construct a [`ProofgoalRule`].
    pub fn new(proofgoal_id: ProofgoalID) -> Self {
        Self { proofgoal_id }
    }
}

/// Derive a constraint by reverse unit propagation (RUP).
#[derive(Debug)]
pub struct RUPRule {
    /// Constraint to be derived.
    pub constraint: Rc<DBConstraint>,
    /// Propagation hints for the RUP check.
    pub hint: Option<Vec<isize>>,
}

impl RUPRule {
    /// Construct a [`RUPRule`].
    #[inline]
    pub fn new(constraint: PBConstraintEnum, hint: Option<Vec<isize>>) -> Self {
        Self {
            constraint: Rc::new(DBConstraint::from(constraint)),
            hint,
        }
    }
}

/// Redundance-based strengthening rule.
///
/// More details about the redundance-based strengthening rule can be found in [Gocht and Nordström 2021]( https://doi.org/10.1609/aaai.v35i5.16494 ).
#[derive(Debug)]
pub struct RedundanceBasedStrengtheningRule {
    /// Constraint to be derived by redundance-based strengthening.
    pub constraint: Rc<DBConstraint>,
    /// Witness for the proofgoals.
    pub witness: Substitution,
    /// Start an explicit subproof for showing the redundance-based strengthening proofgoals.
    pub has_subproof: bool,
}

impl RedundanceBasedStrengtheningRule {
    /// Construct a [`RedundanceBasedStrengtheningRule`].
    #[inline]
    pub fn new(constraint: PBConstraintEnum, witness: Substitution, has_subproof: bool) -> Self {
        Self {
            constraint: Rc::new(DBConstraint::from(constraint)),
            witness,
            has_subproof,
        }
    }
}

/// Identifier for the scope.
#[derive(Debug, Clone, Copy, PartialEq)]
#[repr(u8)]
pub enum ScopeId {
    LessEqual = 0,
    GreaterEqual = 1,
}

impl Display for ScopeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ScopeId::LessEqual => write!(f, "leq"),
            ScopeId::GreaterEqual => write!(f, "geq"),
        }
    }
}

/// Start a scope inside a top-level subproof.
#[derive(Debug)]
pub struct ScopeRule {
    /// Identifier of the scope to start.
    pub id: ScopeId,
}

impl ScopeRule {
    /// Construct a [`ScopeRule`].
    #[inline]
    pub fn new(id: ScopeId) -> Self {
        Self { id }
    }
}

/// Set the current level for constraints derived after this rule.
#[derive(Debug)]
pub struct SetLevelRule {
    /// Specification of the level.
    pub level: usize,
}

impl SetLevelRule {
    /// Construct a [`SetLevelRule`].
    #[inline]
    pub fn new(level: usize) -> Self {
        SetLevelRule { level }
    }
}

/// Output type of a solution logging rule.
#[derive(Debug, PartialEq)]
pub enum SolutionRuleOutput {
    /// Add no constraint.
    None,
    /// Add a solution-improving constraint.
    Improving,
    /// Add a blocking (solution-excluding) constraint.
    Excluding,
}

/// Log a solution and derive a constraint depending on the solution.
#[derive(Debug)]
pub struct SolutionRule {
    /// Solution given as a list of literals that are satisfied.
    pub solution: Vec<Lit>,
    /// Specification of constraint that should be added to the database for the logged solution.
    pub rule_output: SolutionRuleOutput,
    /// Optional objective value achieved by the given solution.
    pub objective_value: Option<BigInt>,
}

impl SolutionRule {
    /// Construct a [`SolutionRule`].
    #[inline]
    pub fn new(
        solution: Vec<Lit>,
        rule_output: SolutionRuleOutput,
        objective_value: Option<BigInt>,
    ) -> Self {
        Self {
            solution,
            rule_output,
            objective_value,
        }
    }
}

/// Start a used defined timer.
#[derive(Debug)]
pub struct StartTimerRule {
    /// Name of the timer.
    pub name: String,
}

impl StartTimerRule {
    /// Construct a [`StartTimerRule`].
    #[inline]
    pub fn new(name: String) -> Self {
        Self { name }
    }
}

/// Enable or disable the strengthening-to-core mode.
#[derive(Debug)]
pub struct StrengtheningToCoreRule {
    /// If `true`, then enable the strengthening-to-core mode. If `false`, then disable the strengthening-to-core mode.
    pub enable: bool,
}

impl StrengtheningToCoreRule {
    /// Construct a [`StrengtheningToCoreRule`].
    #[inline]
    pub fn new(enable: bool) -> Self {
        Self { enable }
    }
}

/// Dummy rule for a rule that is currently not implemented, but might already exist in the parser.
#[derive(Debug)]
pub struct UnimplementedRule {
    /// Name of the rule.
    #[allow(dead_code)]
    pub feature: String,
}

impl UnimplementedRule {
    /// Construct an [`UnimplementedRule`].
    pub fn new(feature: String) -> Self {
        Self { feature }
    }
}

/// The parsed representation of a single proof rule. See the inner type of each rule for documentation about the rule.
pub enum VeriPBRule {
    AssertionRule(AssertionRule),
    Comment(Comment),
    ConclusionRule(ConclusionRule),
    DefineOrderRule(DefineOrderRule),
    Deletion(Deletion),
    DominanceBasedStrengtheningRule(DominanceBasedStrengtheningRule),
    EndProof(EndProof),
    EndSubproof(EndSubproof),
    EndTimerRule(EndTimerRule),
    EqualsObjectiveRule(EqualsObjectiveRule),
    EqualsRule(EqualsRule),
    FailRule(FailRule),
    FormulaCheck(FormulaCheck),
    HeaderRule(HeaderRule),
    ImpliesRule(ImpliesRule),
    IsDeletedCheck(IsDeletedCheck),
    LoadOrderRule(LoadOrderRule),
    MoveToCoreRule(MoveToCoreRule),
    ObjectiveUpdateRule(ObjectiveUpdateRule),
    ObjectiveValueRule(ObjectiveValueRule),
    OrderAuxVariablesRule(OrderAuxVariablesRule),
    OrderDefConstraintRule(OrderDefConstraintRule),
    OrderDefRule(OrderDefRule),
    OrderFreshAux1Rule(OrderFreshAux1Rule),
    OrderFreshAux2Rule(OrderFreshAux2Rule),
    OrderFreshRightVariablesRule(OrderFreshRightVariablesRule),
    OrderLeftVariablesRule(OrderLeftVariablesRule),
    OrderProofRule(OrderProofRule),
    OrderReflexivityRule(OrderReflexivityRule),
    OrderRightVariablesRule(OrderRightVariablesRule),
    OrderSpecificationRule(OrderSpecificationRule),
    OrderTransitivityRule(OrderTransitivityRule),
    OrderVariablesRule(OrderVariablesRule),
    OutputRule(OutputRule),
    PolRule(PolRule),
    PreservedAddRule(PreservedAddRule),
    PreservedEqualsRule(PreservedEqualsRule),
    PreservedRemoveRule(PreservedRemoveRule),
    ProofByContradiction(ProofByContradiction),
    ProofgoalRule(ProofgoalRule),
    RUPRule(RUPRule),
    RedundanceBasedStrengtheningRule(RedundanceBasedStrengtheningRule),
    ScopeRule(ScopeRule),
    SetLevelRule(SetLevelRule),
    SolutionRule(SolutionRule),
    StartTimerRule(StartTimerRule),
    StrengtheningToCoreRule(StrengtheningToCoreRule),
    UnimplementedRule(UnimplementedRule),
}
