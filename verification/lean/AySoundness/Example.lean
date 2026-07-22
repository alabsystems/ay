import AySoundness.Lrat
/-
  End-to-end: a concrete formula + an ay-style LRAT certificate, composed with the
  verified `lratCheck_sound`, yields a Lean-kernel-checked `Unsat` theorem. The
  `lratCheck … = true` fact is discharged by `decide` (pure kernel reduction — no
  `native_decide`, so the native compiler is NOT in the TCB).
-/
namespace AySoundness.Example
open AySoundness

/-- Trivial UNSAT: `x ∧ ¬x`. -/
def triv_orig  : List (Cid × Clause) := [(1, [1]), (2, [-1])]
def triv_proof : List (Cid × Clause × List Int) := [(3, [], [1, 2])]

theorem triv_unsat : Unsat (clauses triv_orig) :=
  lratCheck_sound (original := triv_orig) (proof := triv_proof)
    (by decide) (by decide) (by decide)

/-- PHP(2,1): 2 pigeons, 1 hole — `(p1) ∧ (p2) ∧ (¬p1 ∨ ¬p2)`. -/
def php_orig  : List (Cid × Clause) := [(1, [1]), (2, [2]), (3, [-1, -2])]
def php_proof : List (Cid × Clause × List Int) := [(4, [], [1, 2, 3])]

theorem php21_unsat : Unsat (clauses php_orig) :=
  lratCheck_sound (original := php_orig) (proof := php_proof)
    (by decide) (by decide) (by decide)

#print axioms triv_unsat
#print axioms php21_unsat
end AySoundness.Example
