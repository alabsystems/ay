---------------------------- MODULE kind_codegen ----------------------------
\* Codegen-compatible version of the K-Induction trace contract.
\*
\* This spec is semantically identical to kind_test.tla but removes the two
\* constructs that TLA2 codegen does not yet support:
\*   1. CONSTANTS -- replaced with concrete inline definitions
\*   2. Temporal operator ([][Next]_vars in Spec) -- removed entirely
\*
\* Use with tla2 codegen:
\*   tla2 codegen specs/kind_codegen.tla --kani -o /tmp/kind_gen.rs
\*   tla2 codegen specs/kind_codegen.tla --checker -o /tmp/kind_checker.rs
\*
\* MaxK is set to a small value (4) for tractable Kani verification.
\* The kind_test.cfg uses MaxK=100 for TLC, but Kani exhaustive exploration
\* at k=100 is infeasible.
\*
\* Part of #7914: make TLA2 codegen work for ay specs.

EXTENDS Naturals

\* Concrete constant (replacing CONSTANT declaration).
\* Small value for tractable Kani verification.
MaxK == 4

Results == {"Running", "Safe", "Unsafe", "Unknown", "NotApplicable"}
Phases == {"idle", "base", "forward", "backward"}

VARIABLES
    k,
    result,
    phase,
    baseCaseChecked

vars == <<k, result, phase, baseCaseChecked>>

Init ==
    /\ k = 0
    /\ result = "Running"
    /\ phase = "idle"
    /\ baseCaseChecked = FALSE

\* Check base case: Init AND Transitions AND Query at depth k.
CheckBaseCase ==
    /\ result = "Running"
    /\ k' = k
    /\ result' = "Running"
    /\ phase' = "base"
    /\ baseCaseChecked' = TRUE

\* Check forward induction: negated query is inductive.
CheckForwardInduction ==
    /\ result = "Running"
    /\ baseCaseChecked = TRUE
    /\ k' = k
    /\ result' = "Running"
    /\ phase' = "forward"
    /\ UNCHANGED baseCaseChecked

\* Check backward induction: init is k-inductive.
CheckBackwardInduction ==
    /\ result = "Running"
    /\ baseCaseChecked = TRUE
    /\ k' = k
    /\ result' = "Running"
    /\ phase' = "backward"
    /\ UNCHANGED baseCaseChecked

\* Increment k for next iteration of the k-induction loop.
IncrementK ==
    /\ result = "Running"
    /\ k < MaxK
    /\ baseCaseChecked = TRUE
    /\ k' = k + 1
    /\ result' = "Running"
    /\ phase' = "idle"
    /\ baseCaseChecked' = FALSE

\* Safety proven via trivial init or induction.
DeclareSafe ==
    /\ result = "Running"
    /\ \/ /\ phase = "idle"
       \/ /\ phase \in {"forward", "backward"}
          /\ baseCaseChecked = TRUE
    /\ result' = "Safe"
    /\ UNCHANGED <<k, phase, baseCaseChecked>>

\* Counterexample found: base case check was SAT.
DeclareUnsafe ==
    /\ result = "Running"
    /\ phase = "base"
    /\ result' = "Unsafe"
    /\ UNCHANGED <<k, phase, baseCaseChecked>>

\* Could not determine result.
DeclareUnknown ==
    /\ result = "Running"
    /\ result' = "Unknown"
    /\ UNCHANGED <<k, phase, baseCaseChecked>>

\* Problem structure not suitable for k-induction.
DeclareNotApplicable ==
    /\ result = "Running"
    /\ result' = "NotApplicable"
    /\ UNCHANGED <<k, phase, baseCaseChecked>>

\* Keep terminal states non-deadlocking.
TerminalStutter ==
    /\ result \in {"Safe", "Unsafe", "Unknown", "NotApplicable"}
    /\ UNCHANGED vars

Next ==
    \/ CheckBaseCase
    \/ CheckForwardInduction
    \/ CheckBackwardInduction
    \/ IncrementK
    \/ DeclareSafe
    \/ DeclareUnsafe
    \/ DeclareUnknown
    \/ DeclareNotApplicable
    \/ TerminalStutter

\* NOTE: Temporal Spec (Init /\ [][Next]_vars) is omitted because TLA2
\* codegen does not support temporal operators.

TypeInvariant ==
    /\ k \in 0..MaxK
    /\ result \in Results
    /\ phase \in Phases
    /\ baseCaseChecked \in BOOLEAN

\* Unsafe can only be declared after a base case check found a counterexample.
UnsafeFromBase ==
    result = "Unsafe" => phase = "base"

\* Safe cannot be declared immediately after a base case check.
SafeNotFromBase ==
    result = "Safe" => phase # "base"

\* Non-trivial safety requires base case verification at current k.
SafeFromInductionRequiresBaseCheck ==
    (result = "Safe" /\ phase \in {"forward", "backward"}) => baseCaseChecked = TRUE

=============================================================================
