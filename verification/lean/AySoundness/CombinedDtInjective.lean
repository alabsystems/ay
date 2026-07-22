import AySoundness.Firewall
/-
  DATATYPE CONSTRUCTOR INJECTIVITY refutation through the verified firewall — the
  target shape for the datatype-injectivity emitter tier.

  For `mk a b = mk c d ∧ a ≠ c ⊢ unsat` (a constructor is injective, so equal
  applications have equal arguments), ay's QF_DT pipeline refutes eagerly and
  folds the structure away (bare `(cl …) :rule trust`), so the emitter
  reconstructs the verified shape from the ORIGINAL ASSERTIONS
  (`(= (mk a b) (mk c d))`, `(not (= a c))`), like the string / BV / array ROW1 /
  datatype-selector emitters.

  The grounding is constructor injectivity: model the datatype as an actual
  inductive `Pr` with a binary constructor `mk` (so `mk` IS injective — an
  arbitrary opaque function would not be), and discharge the lemma
  `mk a b = mk c d → a = c` by `injection`. Pure Lean 4 core — `Int` and the
  derived `DecidableEq Pr` make `atomVal` COMPUTABLE (no Classical).

  `#print axioms no_model` ⊆ {propext, Quot.sound}; no `sorry`, no `native_decide`.
  Generalizes to any constructor and any argument position.
-/
namespace AySoundness.CombinedDtInjective
open AySoundness

/-- A two-field datatype; `mk` is a genuine (injective) constructor. -/
inductive Pr where
  | mk : Int → Int → Pr
  deriving DecidableEq

/-- A model: the four constructor arguments. -/
structure Val where
  a : Int
  b : Int
  c : Int
  d : Int

/-- Atoms: `1 ↦ mk a b = mk c d`, `2 ↦ a = c`. -/
def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide (Pr.mk m.a m.b = Pr.mk m.c m.d)
  | 2 => decide (m.a = m.c)
  | _ => false

/-- `mk a b = mk c d` (1), `a ≠ c` (¬2). -/
def original : List (Cid × Clause) := [(1, [1]), (2, [-2])]
/-- The injectivity lemma: `mk a b = mk c d → a = c`. -/
def lemmas   : List (Cid × Clause) := [(3, [-1, 2])]
/-- Unit-propagate `1, -2` then conflict on the lemma → empty clause. -/
def proof    : List (Cid × Clause × List Int) := [(4, [], [1, 2, 3])]

/-- `mk a b = mk c d → a = c` holds in EVERY model (constructor injectivity). -/
theorem inj_lemma_valid (m : Val) : clauseSat (atomVal m) [-1, 2] = true := by
  by_cases h1 : m.a = m.c
  · simp [clauseSat, litSat, atomVal, h1]
  · -- a ≠ c ⟹ mk a b ≠ mk c d (constructor injectivity), so the `¬(mk=mk)`
    -- literal is satisfied.
    have hne : Pr.mk m.a m.b ≠ Pr.mk m.c m.d := fun he => h1 (Pr.mk.inj he).1
    simp [clauseSat, litSat, atomVal, hne, h1]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact inj_lemma_valid m

/-- No model satisfies `mk a b = mk c d ∧ a ≠ c` — via the verified firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.CombinedDtInjective
