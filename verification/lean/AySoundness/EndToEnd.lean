import AySoundness.Lrat
/-
  END-TO-END (T0-polish proof-of-concept): ay's REAL solver output, grounded in
  the VERIFIED checker.

  ay was run on PHP(3,2) (3 pigeons, 2 holes — unsatisfiable):
      target/debug/ay solve --proof php32.lean4 --proof-format lean4 php32.cnf
  and emitted the input clauses and the LRAT/RUP refutation below (transcribed
  verbatim from ay's `originalClauses` / `proofSteps`; ay's own emitted file
  closes with `lratCheck … = true := by native_decide`).

  Here we instead discharge `lratCheck … = true` by pure-kernel `decide` and feed
  it to the VERIFIED `lratCheck_sound` (AySoundness/Lrat.lean), obtaining a
  Lean-kernel-checked theorem that PHP(3,2) is genuinely unsatisfiable. The
  solver's search is never trusted — only its emitted certificate + the verified
  checker + Lean's kernel. `#print axioms` confirms the only axioms are
  [propext, Quot.sound] (no native_decide / Lean.ofReduceBool, so the native
  compiler is NOT in the trusted base — strictly stronger than ay's current
  emitter).
-/
namespace AySoundness.EndToEnd
open AySoundness

/-- ay's input clauses for PHP(3,2) (verbatim from the emitted `originalClauses`). -/
def php32_orig : List (Cid × Clause) :=
  [ (1, [1, 2]), (2, [3, 4]), (3, [5, 6]),
    (4, [-1, -3]), (5, [-1, -5]), (6, [-3, -5]),
    (7, [-2, -4]), (8, [-2, -6]), (9, [-4, -6]) ]

/-- ay's LRAT/RUP refutation (verbatim from the emitted `proofSteps`, each
    `{id, clause, hints}` rendered as `(id, clause, hints)`). -/
def php32_proof : List (Cid × Clause × List Int) :=
  [ (10, [-1], [4, 5, 2, 3, 9]),
    (11, [2],  [10, 1]),
    (12, [-4], [11, 7]),
    (13, [-6], [11, 8]),
    (14, [3],  [12, 2]),
    (15, [5],  [13, 3]),
    (16, [],   [10, 11, 12, 13, 14, 15, 6]) ]

/-- **ay's PHP(3,2) UNSAT verdict, verified by Lean's kernel.** The checker
    accepts ay's real proof (`by decide`, pure kernel reduction), and the verified
    `lratCheck_sound` turns acceptance into genuine unsatisfiability. -/
theorem php32_unsat : Unsat (clauses php32_orig) :=
  lratCheck_sound (original := php32_orig) (proof := php32_proof)
    (by decide) (by decide) (by decide)

#print axioms php32_unsat

end AySoundness.EndToEnd
