import AySoundness.Firewall
/-
  SET subset TRANSITIVITY refutation through the verified firewall — closing the
  set-transitivity half-(1) gap.

  For `A ⊆ B ∧ B ⊆ C ∧ ¬(A ⊆ C) ⊢ unsat`, ay's runtime decides it soundly (it
  injects a Skolem witness for the negated subset — see the set solver), but the
  emitted Alethe proof needs that Skolemization to be VALIDATOR-checkable. The
  Lean FIREWALL certificate, however, needs NO Skolemization: subset transitivity
  `A ⊆ B ∧ B ⊆ C → A ⊆ C` is a VALID lemma under the set interpretation (`X ⊆ Y`
  ≡ `∀ e, e∈X → e∈Y`), proved directly by composing the two implications. This is
  the half-(1) angle — independent of the half-(2) Skolem firewall extension
  (task #23).

  Sets are characteristic functions `Nat → Bool`; `⊆` is the ∀-implication. The
  `∀ e` over the infinite carrier makes the subset atoms' Bool value
  noncomputable via `Classical.propDecidable` (allowed axiom `Classical.choice`);
  `lratCheck`/`tableWf`/`proofWf` never touch `atomVal`, so the `by decide`
  obligations are unaffected.

  `#print axioms no_model` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`,
  no `native_decide`.
-/
namespace AySoundness.CombinedSetTransitivity
open AySoundness

attribute [local instance] Classical.propDecidable

structure Val where
  A : Nat → Bool
  B : Nat → Bool
  C : Nat → Bool

/-- `X ⊆ Y` ≡ `∀ e, e∈X → e∈Y`. -/
def sub (X Y : Nat → Bool) : Prop := ∀ e, X e = true → Y e = true

/-- Atoms: `1 ↦ A ⊆ B`, `2 ↦ B ⊆ C`, `3 ↦ A ⊆ C`. -/
noncomputable def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide (sub m.A m.B)
  | 2 => decide (sub m.B m.C)
  | 3 => decide (sub m.A m.C)
  | _ => false

/-- `A⊆B` (1), `B⊆C` (2), `¬(A⊆C)` (¬3). -/
def original : List (Cid × Clause) := [(1, [1]), (2, [2]), (3, [-3])]
/-- Transitivity: `A⊆B ∧ B⊆C → A⊆C`. -/
def lemmas   : List (Cid × Clause) := [(4, [-1, -2, 3])]
/-- Unit-propagate `1, 2, -3` then conflict on the lemma → empty clause. -/
def proof    : List (Cid × Clause × List Int) := [(5, [], [1, 2, 3, 4])]

/-- Subset transitivity holds in EVERY model: composing `A⊆B` and `B⊆C` gives
    `A⊆C`. -/
theorem trans_lemma_valid (m : Val) : clauseSat (atomVal m) [-1, -2, 3] = true := by
  by_cases h1 : sub m.A m.B
  · by_cases h2 : sub m.B m.C
    · have h3 : sub m.A m.C := fun e hae => h2 e (h1 e hae)
      simp [clauseSat, litSat, atomVal, h3]
    · simp [clauseSat, litSat, atomVal, h2]
  · simp [clauseSat, litSat, atomVal, h1]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact trans_lemma_valid m

/-- No set model satisfies `A⊆B ∧ B⊆C ∧ ¬(A⊆C)` — via the verified firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.CombinedSetTransitivity
