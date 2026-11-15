//! Various error types for the forward checking process.

use std::{path::PathBuf, rc::Rc};

use colored::{ColoredString, Colorize};
use fragile::Sticky;
use malachite_bigint::BigInt;
use thiserror::Error;
use veripb_formula::prelude::DBConstraint;
use veripb_parser::error::ParserError;
use veripb_propagator::error::PropagatorError;

use veripb_rules::{ProofgoalID, elaboration::ElaborationError};

use crate::rules::ScopeId;

/// Error type for the [`ForwardsChecker`](crate::checker::ForwardsChecker). The specific error depends on which part of the [`ForwardsChecker`](crate::checker::ForwardsChecker) failed.
#[derive(Debug, Error)]
pub enum ForwardsCheckerError {
    #[error("Syntax error while parsing proof file!")]
    Parse(#[from] ParserError),

    // `transparent` so the reporter walks straight through to `CheckingLineError`.
    // Rendering `{0}` here *and* exposing it as the source made anyhow print the whole
    // checking error twice.
    // The conversion itself is the explicit `From` impl below, so no `#[from]` here.
    #[error(transparent)]
    Checking(CheckingLineError),

    #[error("Elaboration error: {0}")]
    Elaborator(#[from] ElaborationError),

    // Set-up I/O, before any proof line has been read: opening the elaboration
    // output. It has no proof line to name, which is why it is a variant here
    // rather than a `CheckingLineError`.
    #[error("{0}")]
    Io(#[from] std::io::Error),
}

/// Automatic conversion from [`CheckingLineError`] to [`ForwardsCheckerError`]
impl From<CheckingLineError> for ForwardsCheckerError {
    fn from(error: CheckingLineError) -> Self {
        Self::Checking(error)
    }
}

/// [`CheckingError`] with added context of file name and line number.
#[derive(Debug, Error)]
// Only the location belongs in this message. The underlying `CheckingError` is exposed as
// the error source so the reporter renders the `Caused by:` chain itself; building that
// chain by hand here as well produced a duplicated error report.
#[error("Checking error at {}:{}", file.to_string_lossy(), line)]
pub struct CheckingLineError {
    #[source]
    error: CheckingError,
    file: PathBuf,
    line: usize,
}

/// Error type returned if checking a [`Checkable`](crate::rules::Checkable) rules fails.
#[derive(Debug, Error)]
pub enum CheckingError {
    #[error("{0}")]
    FormulaParser(#[from] ParserError),

    #[error("Propagation engine error: {0}")]
    Propagator(#[from] PropagatorError),

    #[error("The compute function for the rule {rule} has not been implemented, yet!")]
    NotImplemented { rule: String },

    #[error(
        "Unable to delete the constraint with ID {} from the database, as {}.", .constraint_id.to_string(), .reason
    )]
    FailedDeletion {
        constraint_id: usize,
        reason: String,
    },

    #[error("Constraint not found in{which_database} database.")]
    NotFoundInDB {
        constraint: Sticky<Rc<DBConstraint>>,
        which_database: String,
    },

    #[error("Expected constraint is not equal to the constraint at the hint.")]
    NotEqual {
        expected_constraint: Sticky<Rc<DBConstraint>>,
        hint_constraint: Sticky<Rc<DBConstraint>>,
    },

    #[error(
        "Constraint not syntactically implied by any constraint in the{which_database} database."
    )]
    NotImpliedDB {
        constraint: Sticky<Rc<DBConstraint>>,
        which_database: String,
    },

    #[error("Expected constraint is not syntactically implied by the constraint at the hint.")]
    NotImplied {
        expected_constraint: Sticky<Rc<DBConstraint>>,
        hint_constraint: Sticky<Rc<DBConstraint>>,
    },

    #[error(
        "Constraint substituted with current unit propagations is not syntactically implied by any constraint in the{which_database} database substituted with current unit propagations."
    )]
    NotImpliedDBSubstituted {
        constraint: Sticky<Rc<DBConstraint>>,
        which_database: String,
    },

    #[error(
        "Expected constraint substituted with current unit propagations is not syntactically implied by the constraint at the hint substituted with current unit propagations."
    )]
    NotImpliedSubstituted {
        expected_constraint: Sticky<Rc<DBConstraint>>,
        hint_constraint: Sticky<Rc<DBConstraint>>,
    },

    #[error("Accessing the database out of bound with index {}. The index should be between {} and {}.", index.to_string(), lower, upper)]
    OutOfBoundsAccess {
        index: isize,
        lower: isize,
        upper: isize,
    },

    #[error("Trying to access constraint with ID {} that has already been deleted.", index.to_string())]
    AccessingDeleted { index: isize },

    #[error("This rule requires that no unchecked deletion was used to be activate.")]
    ExpectedStrongerGuarantees,

    #[error(
        "The formula contains {formula_size} constraints, but the rule expected that there are {expected_size} constraints."
    )]
    FormulaSizeMismatch {
        formula_size: usize,
        expected_size: usize,
    },

    #[error("The output section has already been given.")]
    DoubleOutput,

    #[error("The conclusion section has already been given.")]
    DoubleConclusion,

    #[error("The 'end pseudo-Boolean proof' has already been given.")]
    DoubleEnd,

    #[error("Unexpected '{}'. Maybe the proof footer has the wrong order. Expected order of the footer is 'output', 'conclusion', and finally 'end pseudo-Boolean proof'.", .0)]
    WrongFooterOrder(&'static str),

    #[error(
        "Cutting planes step ('pol') ended with constraint stack size {0}. The stack should only contain 1 constraint at the end of the step."
    )]
    StackNotOne(usize),

    #[error(
        "While checking the cutting planes step ('pol'), an instruction tried to access more constraints than there are constraints on the constraint stack."
    )]
    NotEnoughConstraintsOnStack,

    #[error("The constraint is not implied by reverse unit propagation (RUP) from {} database. Rerun with the option '--trace-failed' to see the propagations. A wrong cutting planes ('pol') derivation earlier in the proof can also cause this; add '--trace-pol' (with a trace option such as '--trace-lines') to trace pol derivations.", if *.0 {"only core"} else {"core and derived"})]
    NotRUP(bool),

    #[error("The constraint with ID {} is not contradicting, as specified by the hint.", .0.to_string())]
    HintNoContradiction(isize),

    #[error("There is no contradicting constraint in the database.")]
    NoContradicitionInDB,

    #[error(
        "Cannot wipe level {0}: no constraint has ever been assigned to a level that high (the highest level in use is {1}). A 'wipl' of an unused level is a no-op in principle, but accepting it silently would hide a proof that has lost track of its own level structure."
    )]
    WipeLevelOutOfRange(usize, usize),

    #[error(
        "Cannot set level {0}: the level bookkeeping is a dense array indexed by level, so this asks the checker to allocate {0} empty entries before any constraint is stored at them. The largest level supported is {1}."
    )]
    SetLevelOutOfRange(usize, usize),

    #[error(
        "Kernel verification divergence: {0}. The live checker and the proved kernel disagree on a soundness-critical step; one of them is wrong, so the proof is rejected. Report this."
    )]
    KernelDivergence(String),

    #[error(
        "Unable to verify 'conclusion UNSAT'. The input problem contains a contradiction, but 'conclusion UNSAT' can only be used without an objective. Use 'conclusion BOUNDS INF INF' for infeasible optimization problems."
    )]
    ConclusionUnsatObjective,

    #[error(
        "A solution has been logged in the proof using `sol`, `soli`, or `solx`. Hence, the conclusion `UNSAT` is wrong."
    )]
    ConclusionUnsatSolutionLogged,

    #[error("Unable to verify 'conclusion UNSAT'.")]
    ConclusionUnsat,

    #[error("The proof is missing the 'end pseudo-Boolean proof' line.")]
    EndProofMissing,

    #[error(
        "The solution logging rule that introduces a solution improving constraint ('soli') requires an objective, but no objective has been defined in the input problem."
    )]
    SolutionImprovingRequiresObjective,

    #[error(
        "Can not check optional objective value against objective value of solution, since no objective function is given."
    )]
    SolutionValueHintNoObjective,

    #[error("The logged solution was claimed to have value {0} but it has value {1}.")]
    SolutionIncorrectValue(BigInt, BigInt),

    #[error(
        "The objective value logging rule that introduces a solution improving constraint ('obji') requires an objective, but no objective has been defined in the input problem."
    )]
    ObjectiveImprovingRequiresObjective,

    #[error(
        "The given solution does not propagate to a complete assignment of all the currently used variables. The variable '{0}' is not assigned."
    )]
    SolutionNotComplete(String),

    #[error("The given assignment falsifies the constraint with ID {}.", .0.to_string())]
    SolutionFalsifyingConstraint(usize),

    #[error("The propagated assignment does not satisfy the constraint with ID {}.", .0.to_string())]
    SolutionNotSatisfiedConstraint(usize),

    #[error("The variable '{0}' in the objective function is unassigned by the solution.")]
    SolutionVarUnassignedImproving(String),

    #[error("The variable '{0}' in the preserved set is unassigned by the solution.")]
    SolutionVarUnassignedExcluding(String),

    #[error(
        "The 'conclusion SAT' can only be used for decision instances, but the input problem contains an objective."
    )]
    ConclusionSatWithObjective,

    #[error(
        "Unable to verify 'conclusion {0}'. No solution has been logged in the proof and no solution has been given in the conclusion."
    )]
    SolutionMissing(String),

    #[error(
        "The expected number of solutions ({0}) does not match the actuals number of solutions ({1})."
    )]
    MismatchEnumeratedSolutions(BigInt, BigInt),

    #[error(
        "Unable to verify conclusion. The solution given as hint for this conclusion does not satisfy a constraint in the input instance.\n\nHint: Note that the solution given for the conclusion is not propagated. If the solution should be propagated, then log the solution inside the proof using either 'sol', 'soli', or 'solx'."
    )]
    OriginalConstraintNotSatisfied,

    #[error(
        "The solution hint specified for the conclusion assigns the same variable to true and false. I.e., the solution contains both the literal and its negation."
    )]
    ConclusionSolutionConflicting,

    #[error(
        "Unable to verify 'conclusion BOUNDS'. The input problem does not contain an objective, which is required for 'conclusion BOUNDS'."
    )]
    ConclusionBoundsNoObjective,

    #[error(
        "Unable to verify 'conclusion BOUNDS'. The lower bounding constraint is not syntactically implied by any constraint in the database."
    )]
    ConclusionBoundsLBNotImpliedByDB,

    #[error(
        "Unable to verify 'conclusion BOUNDS'. The claimed upper bound of {0} mismatches the best recorded upper bound of {1}."
    )]
    ConclusionBoundsUpperBoundMismatchRecorded(BigInt, BigInt),

    #[error(
        "Unable to verify 'conclusion BOUNDS'. The claimed upper bound of {0} mismatches the objective value of the hint, which is {1}."
    )]
    ConclusionBoundsUpperBoundMismatchHint(BigInt, BigInt),

    #[error(
        "Unable to verify 'conclusion BOUNDS'. The problem is claimed to be infeasible and to have a upper bound at the same time. When the problem has a lower bound, then it is feasible."
    )]
    ConclusionBoundsInfeasibleAndUpper,

    #[error(
        "The 'conclusion BOUNDS' claims that the problem is infeaible, but at least one solution has been logged."
    )]
    ConclusionBoundsInfeasibleAndSolutionLogged,

    #[error(
        "The lower bound claimed for `conclusion BOUNDS` is larger than the best logged objective value."
    )]
    ConclusionBoundsLBLargerBestSolution,

    #[error(
        "The lower bound claimed for `conclusion BOUNDS` is larger than the objective value of a solution that solution logging removed from the database. `solx` excludes every assignment agreeing with the logged solution on the preserved variables, so the excluded class can contain solutions better than the one that was logged, and the lower bound proved from the remaining database does not hold for them."
    )]
    ConclusionBoundsLBLargerExcludedSolutions,

    #[error(
        "Unable to verify 'conclusion BOUNDS'. The claimed lower bound of {0} is larger than the claimed upper bound of {1}."
    )]
    ConclusionBoundsLowerGreaterUpper(BigInt, BigInt),

    #[error(
        "A variable in the objective is not assigned by the solution. Please explicitly specify a value for this variable."
    )]
    ObjectiveUnassigned,

    #[error(
        "Proofgoal {} could not be autoproven. Please add an explicit subproof for proofgoal {}.", .0.to_string(), .0.to_string()
    )]
    AutoprovingFailed(ProofgoalID),

    #[error("Proofgoal {} could not be autoproven for checked deletion. Please add an explicit subproof for proofgoal {}.", .0.to_string(), .0.to_string())]
    CheckedDeletionAutoprovingFailed(ProofgoalID, Option<usize>),

    #[error(
        "The end of the proofgoal subproof does not a constraint ID pointing to a constradiction and it was not possible to find the contradiction in the subproof."
    )]
    ProofgoalEndContradicitionNotObvious,

    #[error("There is no open subcontext to end here.")]
    NoOpenSubcontext,

    #[error(
        "The 'proofgoal' rule can only be used inside a subproof, but no subproof is activated."
    )]
    ProofgoalOutsideSubproof,

    #[error("The internal proofgoal with ID #{} does not exist.", .0.to_string())]
    InternalProofgoalNotExisting(usize),

    #[error("The internal proofgoal with ID #{} is already proven.", .0.to_string())]
    InternalProofgoalAlreadyProven(usize),

    #[error("The database proofgoal with ID {} does not exist or has already been proven.", .0.to_string())]
    DatabaseProofgoalNotExisting(usize),

    #[error(
        "There are still open subcontext at the end of the proof, which is started by the output rule."
    )]
    OutputWhileOpenSubcontext,

    #[error("The rule `{0}` cannot be used within a subproof.")]
    RuleNotSubproofFriendly(String),

    /// A rule was written inside an order definition, where the installed
    /// constraint database is the order's and not the problem's. See
    /// [`crate::rules::OrderDefinitionPlacement`].
    #[error(
        "The rule `{rule}` is not allowed in the {context} context. Between `def_order`/`pre_order` and its `end` the checker has the order's own constraint database installed, not the problem's, so a rule whose effect is a claim about the problem — a verdict, the objective, core membership, the loaded order, or a logged solution — has nothing to say there."
    )]
    RuleNotAllowedInOrderDefinition { rule: String, context: &'static str },

    #[error("Only pseudo-Boolean proofs of version 2.0 or greater are supported.")]
    UnsupportedProofVersion,

    #[error("Deletion of derived constraint ID {} using deletion from core set.", .0.to_string())]
    DeletionFromCoreDeletesDerived(usize),

    #[error("Deletion of core constraint ID {} using deletion from derived set.", .0.to_string())]
    DeletionFromDerivedDeletesCore(usize),

    #[error("Constraint is in database, but is expected to be deleted.")]
    DeletedConstraintInDB,

    #[error(
        "Usage of dominance-based strengthening without order an objective. Dominance-based strengthening can only be used when an order is loaded or the problem contains an objective."
    )]
    DominanceNoObjectiveOrOrder,

    #[error("The objective update rule cannot be used without an objective.")]
    ObjectiveUpdateNoObjective,

    #[error(
        "The keyword 'vars' to specify variables can only be used inside the 'def_order' or the 'transitivity'."
    )]
    VarsNotAllowedHere,

    #[error(
        "The keyword 'spec' for the order specification can only be used inside the 'def_order'."
    )]
    SpecNotAllowedHere,

    /// A block of an order definition appeared out of sequence. See
    /// [`crate::order_context::OrderPhase`].
    #[error(
        "The `{block}` block of an order definition is out of sequence: {expected} was expected here. An order definition is read as a sequence -- `vars`, an optional `spec`, `def`, an optional `transitivity`, an optional `reflexivity`, `end` -- and each block appears at most once. The order matters because every side condition of the order is checked against the definition that `def` supplies, and the blocks that check them read that definition as it stands when they run."
    )]
    OrderBlockOutOfSequence {
        block: &'static str,
        expected: &'static str,
    },

    #[error("The keyword 'def' to specify variables can only be used inside the 'def_order'.")]
    DefNotAllowedHere,

    #[error("It is not allowed to end this block with a constraint ID hint.")]
    EndNoHintAllowed,

    #[error(
        "The rules 'left', 'right', and 'aux' are only allowed in the variable definition of an order."
    )]
    RuleOnlyAllowedInOrderVars,

    #[error("Variables in 'left', 'right' and 'aux' must occur exactly once")]
    OrderVariablesNonDistinct,

    #[error("Variable lists in 'left' and 'right' must have the same length")]
    AsymmetricOrderVariables,

    #[error(
        "Constraints in 'def' and 'spec' are only allowed to contain variables from 'left', 'right' and 'aux'."
    )]
    UndeclaredVariablesInOrder,

    #[error("Witnesses inside 'spec' can only map variables in 'aux'")]
    SpecWitnessMapsNonAuxVariable,

    #[error(
        "The rules 'fresh_right' is only allowed in the variable definition of the transitivity proof of the order definition."
    )]
    RuleOnlyAllowedInTransitivityVars,

    #[error("The 'aux' vars for an order has to be empty in version 2.0 of the proof format.")]
    AuxVarsNonEmpty,

    #[error("Expected auxiliary variable valid for the current order.")]
    InvalidAuxVar,

    #[error(
        "The auxiliary variable {0} of this version 2.0 order is already in use outside the order, so it cannot be elaborated. Elaboration emits version 3.0, whose grammar spells auxiliary variables '${0}', but the elaborated proof up to this point (and the formula, which is not rewritten) already names it '{0}'; renaming it now would rename only some of its occurrences and change what the proof says. Give the auxiliary variable a name of its own, or check without '-e'."
    )]
    AuxVarNotFreshForElaboration(String),

    /// A `left`/`right`/`fresh_right` list names a variable an earlier `aux`
    /// list renamed for elaboration. See
    /// [`crate::checker::refuse_renamed_auxiliary_name`].
    #[error(
        "The variable '{0}' is an auxiliary variable of an earlier order in this version 2.0 proof, so elaboration has given it the version 3.0 auxiliary spelling. Version 3.0 does not admit that spelling in a 'left', 'right' or 'fresh_right' list, so the elaborated proof would not parse. Give this list a variable of its own, or check without '-e'."
    )]
    RenamedAuxVarInPlainList(String),

    #[error("Constraints without a rule are only allowed in the 'def' of the 'def_order'.")]
    OnlyAllowedInOrderDef,

    #[error(
        "The environment 'proof' is only allowed in the 'reflexivity' or 'transitivity' rules of the order definition."
    )]
    ProofOnlyInReflexivityOrTransitivity,

    #[error("Reflexivity has already been proven.")]
    ReflexivityAlreadyProven,

    #[error("Transitivity has already been proven.")]
    TransitivityAlreadyProven,

    #[error("There was no 'proof' for reflexivity presented inside 'reflexivity' environment.")]
    ReflexivityProofMissing,

    #[error("There was no 'proof' for transitivity presented inside 'transitivity' environment.")]
    TransitivityProofMissing,

    #[error("Reflexivity of the order could not be proven.")]
    ReflexivityProofFailed,

    #[error("Transitivity of the order could not be proven.")]
    TransitivityProofFailed,

    #[error(
        "The '{0}' variable list of the transitivity proof has {2} variables, but the order declares {1} '{3}' variables. The lists must have the same length."
    )]
    TransitivityFreshVarsWrongLength(&'static str, usize, usize, &'static str),

    #[error(
        "The variable {0} in the '{1}' list of the transitivity proof is not fresh: it already occurs in 'left', 'right', 'aux' or in another fresh variable list."
    )]
    TransitivityFreshVarNotFresh(String, &'static str),

    #[error("The order '{0}' can not be loaded, as it is not defined.")]
    OrderNotDefined(String),

    #[error(
        "The order is defined over {0} variables, but 'load_order' is trying to load it with {1} variables."
    )]
    OrderWrongNumberVariables(usize, usize),

    #[error("The 'scope' subcontext can only be used inside subproofs.")]
    ScopeOutsideSubproof,

    #[error("The scope named {0} does not exist.")]
    ScopeDoesNotExist(String),

    #[error("The previous scope has not ended. End the previous scope before opening a new scope.")]
    StartScopeWhileOtherScopeOpen,

    #[error("The proofgoal {0} can not be used in scope {1}.")]
    ProofgoalNotInScope(ProofgoalID, ScopeId),

    #[error(
        "The auxiliary variable {0} of the loaded order already occurs in the constraint database, so the specification constraints a 'scope' introduces are not a conservative extension and may contradict it. Auxiliary variables of an order must not be constrained outside the order's own 'spec'."
    )]
    ScopeAuxVarNotFresh(String),

    // Not a defect in the proof: a refusal to continue with a corrupted occurrence index, which
    // is how proofgoals are found. Silently dropping a constraint out of it would drop every
    // `red`/`dom` obligation that constraint should have produced, and the run would go on to
    // print a verdict. See `Database::update_unique_index`.
    #[error(
        "Internal invariant violated while merging duplicate constraint {0} into the unique index: the surviving constraint would have been dropped from the occurrence index, which no later indexing pass revisits. Every proof obligation that constraint should generate would be silently lost, so the run is stopped instead."
    )]
    OccurrenceIndexEviction(usize),

    #[error(
        "The 'left' variables of the order are undefined. Please add 'left' to the 'vars' definition of the order."
    )]
    LeftVarsUndefined,

    #[error(
        "The 'right' variables of the order are undefined. Please add 'right' to the 'vars' definition of the order."
    )]
    RightVarsUndefined,

    #[error(
        "The 'aux' variables of the order are undefined. Please add 'aux' to the 'vars' definition of the order."
    )]
    AuxVarsUndefined,

    #[error("Proof by contradiction should be able to show contradiction by RUP")]
    ProofByContradictionNotRUP,

    #[error("Checked deletion failed and `--force-checked-deletion` option used. Proofgoal with ID {} could not be autoproven.", .0.to_string())]
    ForceCheckedDeletionFailed(ProofgoalID),

    #[error("Unchecked deletion with a subproof is currently not allowed.")]
    UncheckedWithSubproof,

    #[error(
        "Unchecked deletions while strengthening-to-core is enabled or an order is loaded are disallowed if the derived set of constraints is not empty. Please add a subproof for the deletions or empty the derived set before deletion."
    )]
    UncheckedDeletionDangerous,

    #[error("Deletion with subproof can only be used if exactly one core constraint is deleted.")]
    DeletionSubproofNotOneCoreConstraint,

    #[error("Multiple core constraints can only be deleted at once if the witness is empty.")]
    DeletionMultipleCoreWithWitness,

    #[error(
        "Checked deletion with a witness cannot be used while strengthening to core is activated."
    )]
    DeletionWithWitnessWhileStrengtheningToCore,

    #[error("Subproof can only use core constraints, but ID {} is not a core constraint.", .0.to_string())]
    CoreSubproofUsingNonCoreConstraint(isize),

    #[error("Equals objective rule `eobj` can only be used if there is an objective.")]
    EqualObjectiveWithoutObjective,

    #[error("The specified objective is not equal to the current objective.")]
    ObjectivesNotEqual,

    #[error(
        "Output: No output formula file has been specified. The output type `FILE` expects that the third positional command line argument is the path to the output formula."
    )]
    NoOutputFormulaGiven,

    #[error(
        "Output: The constant of current objective in the proof is {0} and the constant of the output formula is {1}, which does not match."
    )]
    OutputObjectiveConstantMismatch(BigInt, BigInt),

    #[error("Output: The terms of the current objective in the proof do not match the terms of the output formula objective.
        \tAdditional terms in the current objective: {0}
        \tAdditional terms in the output objective: {1}")]
    OutputObjectiveMismatch(String, String),

    #[error(
        "Output: The output formula contains an objective, but the problem at the end of the proof does not contain an objective."
    )]
    OutputObjectiveButNoProofObjective,

    #[error(
        "Output: The problem at the end of the proof contains an objective, but the output formula does not contain an objective."
    )]
    OutputNoObjectiveButProofObjective,

    #[error(
        "Output: The following constraint is in the output formula but not in the database at the end of the proof: '{0}'"
    )]
    OutputConstraintNotInDatabase(String),

    #[error("Output: The constraint with ID {} is in the output formula, but in the database it is not a core constraint. The constraint {} should be moved to the core set, as the output section requires equivalence between the output formula and the core constraints.", .0.to_string(), .0.to_string())]
    OutputConstraintNotInCore(usize),

    #[error("Output: The core constraint with ID {} is not in the output formula.", .0.to_string())]
    OutputCoreConstraintNotInOutput(usize),

    #[error(
        "Output: The guarantee EQUIOPTIMAL can only be used if the proof contains an objective."
    )]
    OutputEquioptimalWithoutObjective,

    #[error(
        "Output: The guarantee EQUISATISFIABLE can only be used if the proof does not contain an objective."
    )]
    OutputEquisatisfiableWithObjective,

    #[error("Proof contains `fail` rule.")]
    FailProofUsed,

    #[error(
        "The given solution is conflicting in itself. A variable has been assigned to true and false in the same solution."
    )]
    SolutionIsConflicting,

    /// A stored formula constraint mentions a variable the name table does not cover.
    ///
    /// This is a backstop, not a diagnosable user error: every formula parser is required to
    /// hand the checker a variable-name table that covers every literal it stored, because the
    /// propagation path reads the assignment sized from that table with `get_unchecked`. A
    /// parser that comes up short is an out-of-bounds read on the accept/reject path, so the
    /// run is refused here rather than continued into undefined behaviour.
    #[error(
        "INTERNAL: the formula parser stored a constraint on variable index {index}, but the \
         variable-name table only covers {num_variables} variables. Refusing to check a formula \
         the checker cannot index. Please report this with the formula file."
    )]
    FormulaVariableNotInNameTable { index: usize, num_variables: usize },

    #[error("The preserved set has already been initialized. It can not be initalized again.")]
    PreservedSetAlreadyInitialized,

    #[error(
        "Preserved variables can only be initialized before the first witness is used in the proof."
    )]
    PreservedInitAfterWitnessUsed,

    #[error(
        "No preserved set is known. Hence, the given set of variables can not equal the current preserved set."
    )]
    PreservedEqualsNoPreservedSetKnown,

    #[error("The specified set of variables does not match the current set of preserved variables.{}{}", if !.0.is_empty() {format!(" The variable(s) {} are missing from the given set.", .0.bold())} else {String::from("")},if !.1.is_empty() {format!(" The variable(s) {} are additional in the given set.", .1.bold())} else {String::from("")})]
    PreservedEqualsSetMismatch(String, String),

    #[error(
        "No preserved set has been initialized. Hence, it is impossible to add a variable to the preserved set. Use `preserve_init` to initialize a preserved set."
    )]
    PreservedAddNoPreserved,

    #[error("The variable to be added to the preserved set is already in the preserved set.")]
    PreservedAddVariableAlreadyInSet,

    #[error("Constraint for adding preserved variable contains the variable to be added.")]
    PreservedAddVariableInConstraint,

    #[error(
        "Constraint for adding preserved variables contains variable {0}, which is not preserved."
    )]
    PreservedAddConstraintVariableNotPreserved(ColoredString),

    #[error(
        "No preserved set has been initialized. Hence, it is impossible to remove a variable to the preserved set. Use `preserve_init` to initialize a preserved set."
    )]
    PreservedRemoveNoPreserved,

    #[error("The variable to be removed from the preserved set is not in the preserved set.")]
    PreservedRemoveVariableNotInSet,

    #[error("Constraint for removing preserved variable contains the variable to be removed.")]
    PreservedRemoveVariableInConstraint,

    #[error(
        "Constraint for removing preserved variables contains variable {0}, which is not preserved."
    )]
    PreservedRemoveConstraintVariableNotPreserved(ColoredString),

    #[error("The witness contains the preserved variable {0}.")]
    WitnessContainsPreservedVar(ColoredString),

    #[error(
        "It can not be guaranteed that the output has the same number of solutions, as witnessing has been used without a preserved set being specified."
    )]
    OutputEquienumWitnessUsed,

    #[error(
        "It can not be guaranteed that the output has the same number of solutions, as a solution has been logged which introduced an excluding constraint."
    )]
    OutputEquienumSolutionLogged,

    #[error(
        "It can not be guaranteed that the output has the same number of solutions, as an objective-improving constraint (`soli`/`obji`) has been stored: it removes every solution that is not strictly better than the logged value, so the output's solution count over the preserved set can differ from the input's."
    )]
    OutputEquienumObjectiveRestricting,

    #[error(
        "It can not be guaranteed that the output is satisfiable exactly when the input is, as `solx` has been used: the excluding constraint it stores removes every assignment agreeing with the logged solution on the preserved variables, so the output can be unsatisfiable while the input is not."
    )]
    OutputEquisatSolutionExcluded,

    #[error(
        "It can not be guaranteed that the output is derivable from the input, as a constraint that is not entailed by the input has been stored: `sol`/`soli`/`solx` logging, `soli`/`obji` bounding the objective, or a witnessed `red`/`dom` strengthening. Each of those is satisfiability-preserving but NOT input-entailed, and `output DERIVABLE` claims every model of the input is a model of the output -- which one such constraint in the core set makes false."
    )]
    OutputDerivableSolutionRestricting,

    #[error(
        "The output formula has no preserved set of variables, but a current preserved set of variables is known."
    )]
    OutputFormulaHasNoPreservedVars,

    #[error(
        "A preserved set of variables is not known, but the output formula has a preserved set of variables."
    )]
    OutputCurrentHasNoPreservedVars,

    #[error("The preserved variables of the output formula do not match the current set of preserved variables.{}{}", if !.0.is_empty() {format!(" The variable(s) {} are missing from the output formula.", .0.bold())} else {String::from("")},if !.1.is_empty() {format!(" The variable(s) {} are additional in the output formula.", .1.bold())} else {String::from("")})]
    OutputPreservedVarsMismatch(String, String),

    #[error(
        "The preserved variable {0} is unassigned by the propagated solution when adding the solution excluding constraint."
    )]
    SolutionExcludingPreservedVarUnassigned(ColoredString),

    #[error("Can not log a solution after the set of preserved variables has been changed.")]
    SolutionExcludingPreservedVarChanged,

    #[error(
        "Logging and excluding a solution with 'solx' is only possible if a preserved set is specified."
    )]
    NoPreservedForSolutionExcluding,

    #[error(
        "A complete enumeration can not be concluded after an objective-improving solution logging rule (`soli`/`obji`) has been used: the constraint it stores removes solutions without counting them, so a contradiction in the database does not establish that no further solutions exist."
    )]
    ConclusionEnumerationObjectiveImproving,
}

impl CheckingError {
    /// Construct an error for checking a rule that has not been implemented.
    pub fn not_implemented(rule: &str) -> Self {
        CheckingError::NotImplemented {
            rule: rule.to_string(),
        }
    }

    /// Construct an error for a failed deletion for the given `reason`.
    pub fn deletion(constraint_id: usize, reason: &str) -> Self {
        CheckingError::FailedDeletion {
            constraint_id,
            reason: reason.to_string(),
        }
    }

    /// Construct an error where the `constraint` is not found in the database.
    pub fn not_found(constraint: &Rc<DBConstraint>, only_core: bool) -> Self {
        if only_core {
            CheckingError::NotFoundInDB {
                constraint: Sticky::new(constraint.clone()),
                which_database: " core".to_string(),
            }
        } else {
            CheckingError::NotFoundInDB {
                constraint: Sticky::new(constraint.clone()),
                which_database: String::new(),
            }
        }
    }

    /// Construct an error where the `expected_constraint` is not equal to the `hint_constraint`.
    pub fn not_equal(
        expected_constraint: &Rc<DBConstraint>,
        hint_constraint: &Rc<DBConstraint>,
    ) -> Self {
        CheckingError::NotEqual {
            expected_constraint: Sticky::new(expected_constraint.clone()),
            hint_constraint: Sticky::new(hint_constraint.clone()),
        }
    }

    /// Construct an error where the `constraint` is not syntactically implied by the database.
    pub fn not_implied_db(constraint: &Rc<DBConstraint>, only_core: bool) -> Self {
        if only_core {
            CheckingError::NotImpliedDB {
                constraint: Sticky::new(constraint.clone()),
                which_database: " core".to_string(),
            }
        } else {
            CheckingError::NotImpliedDB {
                constraint: Sticky::new(constraint.clone()),
                which_database: String::new(),
            }
        }
    }

    /// Construct an error where `expected_constraint` is not syntactically implied by `hint_constraint`.
    pub fn not_implied(
        expected_constraint: &Rc<DBConstraint>,
        hint_constraint: &Rc<DBConstraint>,
    ) -> Self {
        CheckingError::NotImplied {
            expected_constraint: Sticky::new(expected_constraint.clone()),
            hint_constraint: Sticky::new(hint_constraint.clone()),
        }
    }

    /// Construct an error where the `constraint` is not syntactically implied by any constraint in the database substituted with all unit propagations from the database.
    pub fn not_implied_substituted_db(constraint: &Rc<DBConstraint>, only_core: bool) -> Self {
        if only_core {
            CheckingError::NotImpliedDBSubstituted {
                constraint: Sticky::new(constraint.clone()),
                which_database: " core".to_string(),
            }
        } else {
            CheckingError::NotImpliedDBSubstituted {
                constraint: Sticky::new(constraint.clone()),
                which_database: String::new(),
            }
        }
    }

    /// Construct an error where the `expected_constraint` is not syntactically implied by the `hint_constraint` substituted with all unit propagations from the database.
    pub fn not_implied_substituted(
        expected_constraint: &Rc<DBConstraint>,
        hint_constraint: &Rc<DBConstraint>,
    ) -> Self {
        CheckingError::NotImpliedSubstituted {
            expected_constraint: Sticky::new(expected_constraint.clone()),
            hint_constraint: Sticky::new(hint_constraint.clone()),
        }
    }

    /// Construct an error for accessing a constraint ID that is out of bounds for the current database of constraints.
    pub fn out_of_bounds(index: isize, lower: isize, upper: isize) -> Self {
        CheckingError::OutOfBoundsAccess {
            index,
            lower,
            upper,
        }
    }

    /// Construct an error for accessing a deleted constraint.
    pub fn access_deleted(index: isize) -> Self {
        CheckingError::AccessingDeleted { index }
    }

    /// Construct an error for a mismatch between the actual `formula_size` and the `expected_size`.
    pub fn formula_size_mismatch(formula_size: usize, expected_size: usize) -> Self {
        CheckingError::FormulaSizeMismatch {
            formula_size,
            expected_size,
        }
    }

    /// Add the context of file name and line number to an checking error.
    pub fn add_context(self, file: PathBuf, line: usize) -> CheckingLineError {
        CheckingLineError {
            error: self,
            file,
            line: line + 1,
        }
    }
}
