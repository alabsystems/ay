---------------------------- MODULE kind_test ----------------------------
\* Finite-state K-Induction trace validation spec.
\*
\* This concrete instance is used by tla2 trace validate for runtime traces
\* emitted by AY's KIND solver.
\*
\* Variables:
\*   k                - current induction depth (0..MaxK)
\*   result           - solver result (Running/Safe/Unsafe/Unknown/NotApplicable)
\*   phase            - last check performed (idle/base/forward/backward)
\*   baseCaseChecked  - TRUE after CheckBaseCase at current k (reset on IncrementK)

EXTENDS Naturals

CONSTANTS
    MaxK

VARIABLES
    k,
    result,
    phase,
    baseCaseChecked

vars == <<k, result, phase, baseCaseChecked>>

Results == {"Running", "Safe", "Unsafe", "Unknown", "NotApplicable"}
Phases == {"idle", "base", "forward", "backward"}

Init ==
    /\ k = 0
    /\ result = "Running"
    /\ phase = "idle"
    /\ baseCaseChecked = FALSE

\* Check base case: Init AND Transitions AND Query at depth k.
\* If SAT, counterexample found (DeclareUnsafe follows separately).
\* Records that the base case was checked at this k value; the solver
\* performs the SMT query after emitting this trace step.
CheckBaseCase ==
    /\ result = "Running"
    /\ k' = k
    /\ result' = "Running"
    /\ phase' = "base"
    /\ baseCaseChecked' = TRUE

\* Check forward induction: negated query is inductive.
\* If UNSAT, property is k-inductive (DeclareSafe follows separately).
\* Requires base case to have been checked first at current k (#3022).
CheckForwardInduction ==
    /\ result = "Running"
    /\ baseCaseChecked = TRUE
    /\ k' = k
    /\ result' = "Running"
    /\ phase' = "forward"
    /\ UNCHANGED baseCaseChecked

\* Check backward induction: init is k-inductive.
\* If UNSAT, init region is invariant (DeclareSafe follows separately).
\* Requires base case to have been checked first at current k (#3022).
CheckBackwardInduction ==
    /\ result = "Running"
    /\ baseCaseChecked = TRUE
    /\ k' = k
    /\ result' = "Running"
    /\ phase' = "backward"
    /\ UNCHANGED baseCaseChecked

\* Increment k for next iteration of the k-induction loop.
\* Resets baseCaseChecked since the base case at the new k is unchecked.
IncrementK ==
    /\ result = "Running"
    /\ k < MaxK
    /\ baseCaseChecked = TRUE
    /\ k' = k + 1
    /\ result' = "Running"
    /\ phase' = "idle"
    /\ baseCaseChecked' = FALSE

\* Safety proven via one of two paths:
\* 1. Trivial: init is empty (phase = "idle", baseCaseChecked = FALSE)
\* 2. Induction: forward or backward step succeeded AND base case was
\*    checked at current k (baseCaseChecked = TRUE, #3022 soundness guard).
DeclareSafe ==
    /\ result = "Running"
    /\ \/ /\ phase = "idle"                                \* trivial init-empty
       \/ /\ phase \in {"forward", "backward"}             \* induction proof
          /\ baseCaseChecked = TRUE                        \* base verified (#3022)
    /\ result' = "Safe"
    /\ UNCHANGED <<k, phase, baseCaseChecked>>

\* Counterexample found: base case check was SAT.
DeclareUnsafe ==
    /\ result = "Running"
    /\ phase = "base"
    /\ result' = "Unsafe"
    /\ UNCHANGED <<k, phase, baseCaseChecked>>

\* Could not determine result (timeout, max k exceeded, etc.)
DeclareUnknown ==
    /\ result = "Running"
    /\ result' = "Unknown"
    /\ UNCHANGED <<k, phase, baseCaseChecked>>

\* Problem structure not suitable for k-induction.
DeclareNotApplicable ==
    /\ result = "Running"
    /\ result' = "NotApplicable"
    /\ UNCHANGED <<k, phase, baseCaseChecked>>

\* Keep terminal states non-deadlocking when TLC runs without -deadlock.
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

Spec == Init /\ [][Next]_vars

TypeInvariant ==
    /\ k \in 0..MaxK
    /\ result \in Results
    /\ phase \in Phases
    /\ baseCaseChecked \in BOOLEAN

\* Unsafe can only be declared after a base case check found a counterexample.
\* Forward/backward induction checks cannot produce counterexamples.
UnsafeFromBase ==
    result = "Unsafe" => phase = "base"

\* Safe cannot be declared immediately after a base case check.
\* Safety comes from induction (forward/backward) or trivial init emptiness (idle).
SafeNotFromBase ==
    result = "Safe" => phase # "base"

\* Non-trivial safety (from induction) requires that the base case was verified
\* at the current k.  This captures the k-induction soundness condition (#3022):
\* induction alone does not prove safety without also ruling out counterexamples
\* in the base case unrollings.
SafeFromInductionRequiresBaseCheck ==
    (result = "Safe" /\ phase \in {"forward", "backward"}) => baseCaseChecked = TRUE

=============================================================================
