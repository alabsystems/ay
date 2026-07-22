import AySoundness.Firewall
/-
  NONLINEAR-INTEGER conflict that is LINEAR after constant folding — the target
  shape for the NIA (linear-after-pinning) emitter tier.

  For `x * y = 7 ∧ x = 2 ⊢ unsat`, ay treats `x * y` as nonlinear and refutes it
  eagerly (bare trust), so the structure is reconstructed from the frontend
  assertions; substituting the pinned `x = 2` makes the constraint LINEAR
  (`2 * y = 7`), which has no integer solution. The firewall lemma is the theory
  conflict `¬(2 * y = 7)`, valid in every model and discharged by `omega` — a
  Lean-CORE tactic (no Mathlib).

  `#print axioms no_model` ⊆ {propext, Quot.sound} (Int `DecidableEq` ⟹ computable
  `atomVal`); no `sorry`, no `native_decide`.
-/
namespace AySoundness.CombinedNiaLinear
open AySoundness

structure Val where
  y : Int

/-- Atom `1 ↦ 2 * y = 7` (the constraint after substituting `x = 2`). -/
def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide (2 * m.y = 7)
  | _ => false

def original : List (Cid × Clause) := [(1, [1])]
/-- The linear conflict: `2 * y = 7` is unsatisfiable over the integers. -/
def lemmas   : List (Cid × Clause) := [(2, [-1])]
def proof    : List (Cid × Clause × List Int) := [(3, [], [1, 2])]

/-- `2 * y ≠ 7` holds in every integer model — by `omega`. -/
theorem linear_lemma_valid (m : Val) : clauseSat (atomVal m) [-1] = true := by
  simp only [clauseSat, litSat, atomVal, List.any_cons, List.any_nil, Bool.or_false]
  -- goal reduces to `!decide (2 * m.y = 7) = true`, i.e. `2 * m.y ≠ 7`
  have : 2 * m.y ≠ 7 := by omega
  simp [this]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact linear_lemma_valid m

/-- No integer model satisfies `2 * y = 7` — via the verified firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.CombinedNiaLinear
