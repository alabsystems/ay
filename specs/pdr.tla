---------------------------- MODULE pdr ----------------------------
\* TLA+ state-machine sketch for PDR trace validation.
\*
\* This module defines the core action vocabulary used by runtime traces.
\* Use pdr_test.tla for a concrete finite-state instance.

EXTENDS Naturals, Integers

VARIABLES
    frames,
    obligations,
    currentLevel,
    result,
    lemmaCount,
    activePredicate,
    activeLevel,
    obligationDepth

vars == <<frames, obligations, currentLevel, result, lemmaCount,
          activePredicate, activeLevel, obligationDepth>>

Init ==
    /\ frames = 2
    /\ obligations = 0
    /\ currentLevel = 1
    /\ result = "Running"
    /\ lemmaCount = 0
    /\ activePredicate = -1
    /\ activeLevel = -1
    /\ obligationDepth = 0

BlockObligation ==
    /\ result = "Running"
    /\ activePredicate' \in Nat              \* MUST have an active obligation
    /\ activeLevel' \in Nat                  \* at a valid frame level
    /\ activeLevel' < frames                 \* level < current frame count
    /\ obligationDepth' \in Nat
    /\ obligations' \in Nat
    /\ lemmaCount' \in Nat                   \* may decrease (lemma removal during refinement)
    /\ UNCHANGED <<frames, currentLevel, result>>

LearnLemma ==
    /\ result = "Running"
    /\ activePredicate' \in Nat              \* learned for a specific predicate
    /\ activeLevel' \in Nat                  \* at a specific level
    /\ activeLevel' < frames
    /\ obligationDepth' \in Nat
    /\ lemmaCount' > lemmaCount
    /\ obligations' \in Nat
    /\ UNCHANGED <<frames, currentLevel, result>>

ExpandLevel ==
    /\ result = "Running"
    /\ frames' = frames + 1
    /\ currentLevel' = currentLevel + 1
    /\ activePredicate' = -1                 \* no active obligation during expansion
    /\ activeLevel' = -1
    /\ obligationDepth' = 0
    /\ obligations' \in Nat
    /\ lemmaCount' >= lemmaCount
    /\ result' = "Running"

PropagateLemmas ==
    /\ result = "Running"
    /\ activePredicate' = -1                 \* no active obligation during propagation
    /\ activeLevel' = -1
    /\ obligationDepth' = 0
    /\ obligations' \in Nat
    /\ lemmaCount' >= lemmaCount
    /\ UNCHANGED <<frames, currentLevel, result>>

DeclareSafe ==
    /\ result = "Running"
    /\ result' = "Safe"
    /\ lemmaCount' >= lemmaCount
    /\ UNCHANGED <<frames, obligations, currentLevel,
                   activePredicate, activeLevel, obligationDepth>>

DeclareUnsafe ==
    /\ result = "Running"
    /\ result' = "Unsafe"
    /\ lemmaCount' >= lemmaCount
    /\ UNCHANGED <<frames, obligations, currentLevel,
                   activePredicate, activeLevel, obligationDepth>>

DeclareUnknown ==
    /\ result = "Running"
    /\ result' = "Unknown"
    /\ lemmaCount' >= lemmaCount
    /\ UNCHANGED <<frames, obligations, currentLevel,
                   activePredicate, activeLevel, obligationDepth>>

\* Keep terminal states non-deadlocking when TLC runs without -deadlock.
TerminalStutter ==
    /\ result \in {"Safe", "Unsafe", "Unknown"}
    /\ UNCHANGED vars

Next ==
    \/ BlockObligation
    \/ LearnLemma
    \/ ExpandLevel
    \/ PropagateLemmas
    \/ DeclareSafe
    \/ DeclareUnsafe
    \/ DeclareUnknown
    \/ TerminalStutter

Spec == Init /\ [][Next]_vars

TypeInvariant ==
    /\ frames \in Nat
    /\ frames >= 2
    /\ obligations \in Nat
    /\ currentLevel \in Nat
    /\ result \in {"Running", "Safe", "Unsafe", "Unknown"}
    /\ lemmaCount \in Nat
    /\ activePredicate \in Int
    /\ activeLevel \in Int
    /\ obligationDepth \in Nat

FrameMonotonicity ==
    /\ currentLevel = frames - 1
    /\ frames >= 2

\* Obligation-level must be within frame range when an obligation is active.
ObligationLevelBound ==
    activeLevel /= -1 => activeLevel < frames

\* A safety proof requires at least one learned lemma.
\* Replaces the original LemmaInductiveness (lemmaCount >= 0) which was vacuously
\* true for unsigned counts.
LemmaMonotonicity ==
    result = "Safe" => lemmaCount > 0

=============================================================================
