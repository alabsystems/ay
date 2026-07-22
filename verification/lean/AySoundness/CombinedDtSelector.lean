import AySoundness.Firewall
/-
  DATATYPE SELECTOR congruence refutation through the verified firewall — the
  target shape for the datatype-selector emitter tier.

  For `fst p = v ∧ p = q ∧ fst q ≠ v ⊢ unsat` (a selector applied to two equal
  datatype values must agree), ay's QF_DT pipeline refutes EAGERLY and emits only
  `(cl (or false false)) :rule trust` with the term structure folded away — and
  `self.ctx.assertions` is trivialized too — so there is no recoverable Alethe
  lemma. The structure IS still present in the ORIGINAL ASSERTIONS
  (`(= (fst p) v)`, `(= p q)`, `(not (= (fst q) v))`), so the emitter reconstructs
  the verified shape from there (assertion-scanning), like the string / BV / array
  ROW1 emitters.

  The grounding is congruence + transitivity: model the datatype values as an
  opaque carrier (`Nat`) and the selector as an arbitrary function `fst : Nat → Int`.
  The lemma `p = q ∧ fst p = v → fst q = v` holds in every model (`p = q` gives
  `fst p = fst q` by congruence, then transitivity with `fst p = v`). Pure Lean 4
  core — `Int`/`Nat` have `DecidableEq`, so `atomVal` is COMPUTABLE (no Classical).

  `#print axioms no_model` ⊆ {propext, Quot.sound}; no `sorry`, no `native_decide`.
  Generalizes to any unary selector, any value, and either argument position.
-/
namespace AySoundness.CombinedDtSelector
open AySoundness

/-- A model: two datatype values (opaque, as `Nat`), the selector `fst`, and the
    compared value `v`. -/
structure Val where
  p : Nat
  q : Nat
  fst : Nat → Int
  v : Int

/-- Atoms: `1 ↦ fst p = v`, `2 ↦ p = q`, `3 ↦ fst q = v`. -/
def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide (m.fst m.p = m.v)
  | 2 => decide (m.p = m.q)
  | 3 => decide (m.fst m.q = m.v)
  | _ => false

/-- `fst p = v` (1), `p = q` (2), `fst q ≠ v` (¬3). -/
def original : List (Cid × Clause) := [(1, [1]), (2, [2]), (3, [-3])]
/-- The selector-congruence lemma: `p = q ∧ fst p = v → fst q = v`. -/
def lemmas   : List (Cid × Clause) := [(4, [-2, -1, 3])]
/-- Unit-propagate `1, 2, -3` then conflict on the lemma → empty clause. -/
def proof    : List (Cid × Clause × List Int) := [(5, [], [1, 2, 3, 4])]

/-- `p = q ∧ fst p = v → fst q = v` holds in EVERY model (congruence on `fst`
    + transitivity). -/
theorem selector_lemma_valid (m : Val) : clauseSat (atomVal m) [-2, -1, 3] = true := by
  by_cases h2 : m.p = m.q
  · by_cases h1 : m.fst m.p = m.v
    · have h3 : m.fst m.q = m.v := by rw [← h2]; exact h1
      simp [clauseSat, litSat, atomVal, h3]
    · simp [clauseSat, litSat, atomVal, h1]
  · simp [clauseSat, litSat, atomVal, h2]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact selector_lemma_valid m

/-- No model satisfies `fst p = v ∧ p = q ∧ fst q ≠ v` — via the verified firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.CombinedDtSelector
