import AySoundness.Firewall
/-
  EUF congruence-over-a-transitive-chain refutation through the verified firewall
  — the target shape for the EUF fused congruence+transitivity emitter tier.

  For `a = b ∧ b = c ∧ f a ≠ f c ⊢ unsat`, the conflict combines transitivity
  (`a = b`, `b = c` ⟹ `a = c`) with congruence (`a = c` ⟹ `f a = f c`). ay's
  proof for this fuses the two into a single `:rule trust` step; the structured
  Alethe form (after the executor's split) is `eq_transitive` + `eq_congruent`
  STEPS (not `TheoryLemma` kinds), so the proof-step-driven firewall dispatch does
  not emit a certificate for it. The structure IS present in the original
  assertions (`(= a b)`, `(= b c)`, `(not (= (f a) (f c)))`), so the emitter
  reconstructs the verified shape from there (assertion-scanning), like the
  string / BV / array-ROW1 / datatype-selector / datatype-injectivity emitters.

  The grounding is the single fused lemma `a = b ∧ b = c → f a = f c`, valid in
  every model (transitivity then congruence), discharged through
  `firewall_combined_unsat`. Carriers are opaque (`Nat`), the function arbitrary
  (`Nat → Int`); fully computable `atomVal` (`DecidableEq`), no Classical.

  `#print axioms no_model` ⊆ {propext, Quot.sound}; no `sorry`, no `native_decide`.
-/
namespace AySoundness.CombinedEufCongTrans
open AySoundness

/-- A model: the three chain elements and the function. -/
structure Val where
  a : Nat
  b : Nat
  c : Nat
  f : Nat → Int

/-- Atoms: `1 ↦ a = b`, `2 ↦ b = c`, `3 ↦ f a = f c`. -/
def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide (m.a = m.b)
  | 2 => decide (m.b = m.c)
  | 3 => decide (m.f m.a = m.f m.c)
  | _ => false

/-- `a = b` (1), `b = c` (2), `f a ≠ f c` (¬3). -/
def original : List (Cid × Clause) := [(1, [1]), (2, [2]), (3, [-3])]
/-- The fused congruence-over-transitivity lemma: `a = b ∧ b = c → f a = f c`. -/
def lemmas   : List (Cid × Clause) := [(4, [-1, -2, 3])]
/-- Unit-propagate `1, 2, -3` then conflict on the lemma → empty clause. -/
def proof    : List (Cid × Clause × List Int) := [(5, [], [1, 2, 3, 4])]

/-- `a = b ∧ b = c → f a = f c` holds in EVERY model (transitivity + congruence). -/
theorem cong_trans_lemma_valid (m : Val) : clauseSat (atomVal m) [-1, -2, 3] = true := by
  by_cases h1 : m.a = m.b
  · by_cases h2 : m.b = m.c
    · have hfc : m.f m.a = m.f m.c := by rw [h1.trans h2]
      simp [clauseSat, litSat, atomVal, hfc]
    · simp [clauseSat, litSat, atomVal, h2]
  · simp [clauseSat, litSat, atomVal, h1]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact cong_trans_lemma_valid m

/-- No model satisfies `a = b ∧ b = c ∧ f a ≠ f c` — via the verified firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.CombinedEufCongTrans
