---------------------------- MODULE cdcl_codegen ----------------------------
\* Codegen-compatible version of the CDCL runtime trace contract.
\*
\* This spec is semantically identical to cdcl_test.tla but removes the two
\* constructs that TLA2 codegen does not yet support:
\*   1. CONSTANTS -- replaced with concrete inline definitions
\*   2. Temporal operator ([][Next]_vars in Spec) -- removed entirely
\*
\* Use with tla2 codegen:
\*   tla2 codegen specs/cdcl_codegen.tla --kani -o /tmp/cdcl_gen.rs
\*   tla2 codegen specs/cdcl_codegen.tla --checker -o /tmp/cdcl_checker.rs
\*
\* The concrete values (MaxNumVars=2, MaxLearnedClauses=4) match cdcl_test.cfg
\* and are sufficient for exhaustive state-space exploration of all CDCL
\* behavioral patterns: propagation, decision, conflict, learning, backtrack,
\* SAT, and UNSAT.
\*
\* Part of #7914: make TLA2 codegen work for ay specs.

EXTENDS Integers, Sequences, FiniteSets

\* Concrete constants (replacing CONSTANT declarations).
\* These values match cdcl_test.cfg for consistency.
MaxNumVars == 2
MaxLearnedClauses == 4

\* The concrete solver variable universe is carried by `assignment`.
VarIndices == DOMAIN assignment
NumVars == Cardinality(VarIndices)

\* A literal is <<varIndex, sign>> where sign is "pos" or "neg".
PosLit(v) == <<v, "pos">>
NegLit(v) == <<v, "neg">>
Literals == {<<v, s>> : v \in VarIndices, s \in {"pos", "neg"}}

\* Get the variable and sign of a literal.
Var(lit) == lit[1]
IsPositive(lit) == lit[2] = "pos"

\* Possible assignment values.
Values == {"TRUE", "FALSE", "UNDEF"}

\* Finite initial-state universe, matching Solver's dense zero-based domains.
BoundedAssignment(a) ==
    \E n \in 0..MaxNumVars : a \in [0..(n - 1) -> Values]

\* Finite set of all prefixes of a trail (including empty trail).
TrailPrefixes(s) ==
    { IF i = 0 THEN <<>> ELSE SubSeq(s, 1, i) : i \in 0..Len(s) }

\* Finite set of trails with bounded length.
BoundedTrails ==
    UNION { [1..k -> Literals] : k \in 0..NumVars }

\* A trail is duplicate-free if no variable appears more than once.
DuplicateFreeTrail(t) ==
    \A i, j \in 1..Len(t) : i # j => Var(t[i]) # Var(t[j])

\* Bounded trails that also satisfy the duplicate-free requirement.
DuplicateFreeTrails ==
    { t \in BoundedTrails : DuplicateFreeTrail(t) }

\* Any literal on trail must agree with assignment.
TrailAssignmentConsistent(a, t) ==
    /\ \A i \in 1..Len(t) :
        /\ t[i] \in Literals
        /\ LET lit == t[i] IN
            /\ a[Var(lit)] # "UNDEF"
            /\ IF IsPositive(lit)
                THEN a[Var(lit)] = "TRUE"
                ELSE a[Var(lit)] = "FALSE"

\* SAT-terminal consistency predicate reused by transition guards and invariants.
SatTerminalConsistent(a, t, d) ==
    /\ \A v \in VarIndices : a[v] # "UNDEF"
    /\ d \in 0..NumVars
    /\ d <= Len(t)
    /\ TrailAssignmentConsistent(a, t)

VARIABLES
    assignment,
    trail,
    state,
    decisionLevel,
    learnedClauses

vars == <<assignment, trail, state, decisionLevel, learnedClauses>>

Init ==
    /\ BoundedAssignment(assignment)
    /\ \A v \in DOMAIN assignment : assignment[v] = "UNDEF"
    /\ trail = <<>>
    /\ state = "PROPAGATING"
    /\ decisionLevel = 0
    /\ learnedClauses = 0

\* Propagation without immediate conflict.
Propagate ==
    /\ state = "PROPAGATING"
    /\ TrailAssignmentConsistent(assignment, trail)
    /\ assignment' \in [VarIndices -> Values]
    /\ Len(trail) < NumVars
    /\ \E lit \in Literals :
        /\ assignment[Var(lit)] = "UNDEF"
        /\ trail' = Append(trail, lit)
    /\ TrailAssignmentConsistent(assignment', trail')
    /\ decisionLevel' = decisionLevel
    /\ learnedClauses' = learnedClauses
    /\ state' = "PROPAGATING"

\* Detect conflict after propagation.
DetectConflict ==
    /\ state = "PROPAGATING"
    /\ TrailAssignmentConsistent(assignment, trail)
    /\ assignment' \in [VarIndices -> Values]
    /\ (
        trail' = trail
        \/ /\ Len(trail) < NumVars
           /\ \E lit \in Literals :
               /\ assignment[Var(lit)] = "UNDEF"
               /\ trail' = Append(trail, lit)
       )
    /\ TrailAssignmentConsistent(assignment', trail')
    /\ decisionLevel' = decisionLevel
    /\ learnedClauses' = learnedClauses
    /\ state' = "CONFLICTING"

\* Analyze conflict, learn a clause, and backtrack (combined solver action).
AnalyzeAndLearn ==
    /\ state = "CONFLICTING"
    /\ TrailAssignmentConsistent(assignment, trail)
    /\ decisionLevel > 0
    /\ \E newLevel \in 0..(decisionLevel - 1) :
        /\ decisionLevel' = newLevel
        /\ assignment' \in [VarIndices -> Values]
        \* CDCL backtrack keeps a trail prefix and may append one UIP literal.
        /\ \E prefix \in TrailPrefixes(trail) :
            /\ (
                trail' = prefix
                \/ /\ Len(prefix) < NumVars
                   /\ \E lit \in Literals :
                       /\ \A i \in 1..Len(prefix) : Var(prefix[i]) # Var(lit)
                       /\ trail' = Append(prefix, lit)
               )
        /\ TrailAssignmentConsistent(assignment', trail')
        /\ decisionLevel' <= Len(trail')
        \* Saturating bound keeps TLC state space finite without deadlocking.
        /\ learnedClauses' =
            IF learnedClauses < MaxLearnedClauses
                THEN learnedClauses + 1
                ELSE learnedClauses
        /\ state' = "PROPAGATING"

\* Make a decision (polarity may be positive or negative).
Decide ==
    /\ state = "PROPAGATING"
    /\ TrailAssignmentConsistent(assignment, trail)
    /\ decisionLevel < NumVars
    /\ Len(trail) < NumVars
    /\ \E v \in VarIndices :
        /\ assignment[v] = "UNDEF"
        /\ \E sign \in {"pos", "neg"} :
            /\ decisionLevel' = decisionLevel + 1
            /\ assignment' =
                [assignment EXCEPT ![v] = IF sign = "pos" THEN "TRUE" ELSE "FALSE"]
            /\ trail' = Append(trail, <<v, sign>>)
            /\ state' = "PROPAGATING"
            /\ UNCHANGED learnedClauses

\* All assigned - SAT.
DeclareSat ==
    /\ state = "PROPAGATING"
    /\ TrailAssignmentConsistent(assignment, trail)
    /\ assignment' \in [VarIndices -> Values]
    /\ trail' \in DuplicateFreeTrails
    /\ SatTerminalConsistent(assignment', trail', decisionLevel')
    /\ state' = "SAT"
    /\ learnedClauses' = learnedClauses

\* Conflict at level 0 - UNSAT.
DeclareUnsat ==
    /\ state \in {"PROPAGATING", "CONFLICTING"}
    /\ TrailAssignmentConsistent(assignment, trail)
    /\ decisionLevel = 0
    /\ assignment' \in [VarIndices -> Values]
    /\ trail' \in DuplicateFreeTrails
    /\ TrailAssignmentConsistent(assignment', trail')
    /\ decisionLevel' = 0
    /\ state' = "UNSAT"
    /\ learnedClauses' = learnedClauses

\* Keep terminal states non-deadlocking.
TerminalStutter ==
    /\ state \in {"SAT", "UNSAT"}
    /\ UNCHANGED vars

Next ==
    \/ Propagate
    \/ DetectConflict
    \/ AnalyzeAndLearn
    \/ Decide
    \/ DeclareSat
    \/ DeclareUnsat
    \/ TerminalStutter

\* NOTE: Temporal Spec (Init /\ [][Next]_vars) is omitted because TLA2
\* codegen does not support temporal operators. The Init and Next operators
\* are individually available for codegen targets (Kani harnesses, checker
\* adapters, proptest generators).

\* Invariants
TypeInvariant ==
    /\ BoundedAssignment(assignment)
    /\ trail \in Seq(Literals)
    /\ TrailAssignmentConsistent(assignment, trail)
    /\ state \in {"PROPAGATING", "CONFLICTING", "SAT", "UNSAT"}
    /\ decisionLevel \in 0..NumVars
    /\ decisionLevel <= Len(trail)
    /\ Len(trail) <= NumVars
    /\ learnedClauses \in 0..MaxLearnedClauses

\* No variable appears on the trail more than once.
NoTrailDuplicates ==
    \A i, j \in 1..Len(trail) :
        i # j => Var(trail[i]) # Var(trail[j])

\* SAT semantic correctness: terminal SAT must correspond to a total, consistent
\* assignment.
SatCorrect ==
    state = "SAT" =>
        SatTerminalConsistent(assignment, trail, decisionLevel)

\* UNSAT semantic correctness: UNSAT is only valid at root conflict level.
UnsatCorrect ==
    state = "UNSAT" =>
        /\ decisionLevel = 0
        /\ TrailAssignmentConsistent(assignment, trail)
        /\ NoTrailDuplicates

\* Combined semantic gate for runtime trace validation.
Soundness == SatCorrect /\ UnsatCorrect

\* Bound learned-clause growth for finite model checking.
LearnedClausesBound ==
    learnedClauses <= MaxLearnedClauses

=============================================================================
