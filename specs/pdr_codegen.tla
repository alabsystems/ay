---------------------------- MODULE pdr_codegen ----------------------------
\* Codegen-compatible version of the PDR runtime trace contract.
\*
\* This spec is semantically identical to pdr_test.tla but removes the two
\* constructs that TLA2 codegen does not yet support:
\*   1. CONSTANTS -- replaced with concrete inline definitions
\*   2. Temporal operator ([][Next]_vars in Spec) -- removed entirely
\*
\* Use with tla2 codegen:
\*   tla2 codegen specs/pdr_codegen.tla --kani -o /tmp/pdr_gen.rs
\*   tla2 codegen specs/pdr_codegen.tla --checker -o /tmp/pdr_checker.rs
\*
\* The concrete values match pdr_test.cfg. Note: MaxFrames/MaxLemmas are
\* large (64/100) which may cause combinatorial blowup in exhaustive model
\* checking. For Kani harnesses, bounded unwinds keep it tractable.
\*
\* Part of #7914: make TLA2 codegen work for ay specs.

EXTENDS Naturals, Integers

\* Concrete constants (replacing CONSTANT declarations).
\* These values match pdr_test.cfg for consistency.
MaxFrames == 64
MaxLemmas == 100
MaxObligations == 10
MaxPredicates == 16

Results == {"Running", "Safe", "Unsafe", "Unknown"}

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

\* Keep terminal states non-deadlocking.
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

\* NOTE: Temporal Spec (Init /\ [][Next]_vars) is omitted because TLA2
\* codegen does not support temporal operators. The Init and Next operators
\* are individually available for codegen targets.

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
LemmaMonotonicity ==
    result = "Safe" => lemmaCount > 0

=============================================================================
