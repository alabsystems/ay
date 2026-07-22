import AySoundness.Firewall
/-
  STRING length-vs-literal conflict, refuted through the verified firewall — the
  target shape for the string emitter tier.

  For `s = "" ∧ str.len s = 3 ⊢ unsat`, ay's conflict lemma is surface-rewrite
  TRIVIALIZED before emit (the internal clause becomes `[¬false, ¬(t6=t6)]`, with
  the `str.len` structure visible only via printer overrides) — so unlike the
  array ROW2 case, the lemma's structure is NOT recoverable from the proof step.
  The structure IS still present in the ORIGINAL ASSERTIONS (`(= s "")`,
  `(= (str.len s) 3)`), so the string emitter must reconstruct from there
  (assertion-scanning), not from the proof lemma.

  The grounding itself is straightforward and verified here: model `Val = String`
  (Lean core has `String`), the tautology `¬(s = "") ∨ ¬(str.len s = 3)` holds
  because `s = "" ⟹ s.length = 0 ≠ 3`, discharged by `by_cases` on `s = ""` +
  `simp` (which computes `"".length = 0`). Generalizes to any literal `L` and
  length `K` with `L.length ≠ K`.

  `#print axioms no_model` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`,
  no `native_decide`. Pure Lean 4 core. This is the verified target the string
  emitter (assertion-scanning) will produce.
-/
namespace AySoundness.CombinedStringLength
open AySoundness

abbrev Val := String

/-- Atoms: `1 ↦ s = ""`, `2 ↦ str.len s = 3`. -/
def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide (m = "")
  | 2 => decide (m.length = 3)
  | _ => false

def original : List (Cid × Clause) := [(1, [1]), (2, [2])]
def lemmas   : List (Cid × Clause) := [(3, [-1, -2])]
def proof    : List (Cid × Clause × List Int) := [(4, [], [1, 2, 3])]

/-- `¬(s = "") ∨ ¬(str.len s = 3)` holds in every model: `s = "" ⟹ len = 0 ≠ 3`. -/
theorem length_lemma_valid (m : Val) : clauseSat (atomVal m) [-1, -2] = true := by
  simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]
  by_cases h : m = "" <;> simp [h]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact length_lemma_valid m

/-- No string is both `""` and of length 3 — via the verified firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.CombinedStringLength
