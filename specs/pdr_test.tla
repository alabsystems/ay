---------------------------- MODULE pdr_test ----------------------------
\* Finite-state PDR trace validation spec.
\*
\* This concrete instance is used by tla2 trace validate for runtime traces
\* emitted by AY's PDR solver.

EXTENDS Naturals, Integers

CONSTANTS
    MaxFrames,
    MaxLemmas,
    MaxObligations,
    MaxPredicates

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

Results == {"Running", "Safe", "Unsafe", "Unknown"}

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
    /\ activePredicate' \in 0..(MaxPredicates - 1)
    /\ activeLevel' \in 0..(MaxFrames - 1)
    /\ activeLevel' < frames
    /\ obligationDepth' \in 0..MaxObligations
    /\ obligations' \in 0..MaxObligations
    /\ lemmaCount' \in lemmaCount..MaxLemmas
    /\ UNCHANGED <<frames, currentLevel, result>>

LearnLemma ==
    /\ result = "Running"
    /\ activePredicate' \in 0..(MaxPredicates - 1)
    /\ activeLevel' \in 0..(MaxFrames - 1)
    /\ activeLevel' < frames
    /\ obligationDepth' \in 0..MaxObligations
    /\ lemmaCount' \in (lemmaCount + 1)..MaxLemmas
    /\ obligations' \in 0..MaxObligations
    /\ UNCHANGED <<frames, currentLevel, result>>

ExpandLevel ==
    /\ result = "Running"
    /\ frames < MaxFrames
    /\ frames' = frames + 1
    /\ currentLevel' = currentLevel + 1
    /\ activePredicate' = -1
    /\ activeLevel' = -1
    /\ obligationDepth' = 0
    /\ obligations' \in 0..MaxObligations
    /\ lemmaCount' \in lemmaCount..MaxLemmas
    /\ result' = "Running"

PropagateLemmas ==
    /\ result = "Running"
    /\ activePredicate' = -1
    /\ activeLevel' = -1
    /\ obligationDepth' = 0
    /\ obligations' \in 0..MaxObligations
    /\ lemmaCount' \in lemmaCount..MaxLemmas
    /\ UNCHANGED <<frames, currentLevel, result>>

DeclareSafe ==
    /\ result = "Running"
    /\ lemmaCount > 0
    /\ result' = "Safe"
    /\ lemmaCount' \in lemmaCount..MaxLemmas
    /\ UNCHANGED <<frames, obligations, currentLevel,
                   activePredicate, activeLevel, obligationDepth>>

DeclareUnsafe ==
    /\ result = "Running"
    /\ result' = "Unsafe"
    /\ lemmaCount' \in lemmaCount..MaxLemmas
    /\ UNCHANGED <<frames, obligations, currentLevel,
                   activePredicate, activeLevel, obligationDepth>>

DeclareUnknown ==
    /\ result = "Running"
    /\ result' = "Unknown"
    /\ lemmaCount' \in lemmaCount..MaxLemmas
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
    /\ frames \in 2..MaxFrames
    /\ obligations \in 0..MaxObligations
    /\ currentLevel \in 1..(MaxFrames - 1)
    /\ result \in Results
    /\ lemmaCount \in 0..MaxLemmas
    /\ activePredicate \in -1..(MaxPredicates - 1)
    /\ activeLevel \in -1..(MaxFrames - 1)
    /\ obligationDepth \in 0..MaxObligations

FrameMonotonicity ==
    /\ currentLevel = frames - 1
    /\ frames >= 2

\* Obligation-level must be within frame range when an obligation is active.
ObligationLevelBound ==
    activeLevel /= -1 => activeLevel < frames

\* A safety proof requires at least one learned lemma.
\* Replaces the original LemmaInductiveness (lemmaCount >= 0) which was vacuously
\* true for unsigned counts. This catches bugs where DeclareSafe fires without
\* any lemma being learned (i.e., an empty inductive invariant claim).
LemmaMonotonicity ==
    result = "Safe" => lemmaCount > 0

=============================================================================
