import AySoundness.Firewall
/-
  EUF CONGRUENCE conflict, refuted through the verified firewall — the
  function-model proof-of-concept for the next automatic-emitter tier.

  ay emits, for `a = b ∧ f a ≠ f b ⊢ unsat`, the lemma

      (step t2 (cl (not (= a b)) (= (f a) (f b))) :rule eq_congruent)

  a mixed-polarity congruence tautology. Unlike the already-emitted theories
  (datatypes `cases`/`decide`, LIA/EUF-constants `omega` over a flat `Nat → _`
  valuation), congruence is NOT faithful under a flat valuation — equal
  arguments must map to equal results. So the model carries the uninterpreted
  function EXPLICITLY: `Val = (Nat → Nat) × (Nat → Nat)`, where `.1` is the
  constant valuation and `.2` is `f`. A constant `a` renders as `m.1 i`; an
  application `f a` as `m.2 (m.1 i)`. Lemma validity is then `by_cases` on the
  argument equality + `simp` (congruence by rewriting) — no `omega`.

  This is the verified target shape for `emit_euf_congruence_firewall_lean`
  (the function-model emitter tier: EUF-congruence, arrays, …), exactly as
  `CombinedDatatype` was the proof-of-concept that preceded the datatype emitter.
  `#print axioms no_model` is ⊆ {propext, Classical.choice, Quot.sound}; no
  `sorry`, no `native_decide`. Pure Lean 4 core.
-/
namespace AySoundness.CombinedEufCongruence
open AySoundness

/-- Model: a constant valuation `m.1` and the uninterpreted function `m.2 = f`.
    The explicit function is what makes congruence (`a = b → f a = f b`) hold —
    a flat valuation could assign `f a` and `f b` independently. -/
abbrev Val := (Nat → Nat) × (Nat → Nat)

/-- Atoms: `1 ↦ a = b` (constants), `2 ↦ f a = f b` (function applications). -/
def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide (m.1 0 = m.1 1)
  | 2 => decide (m.2 (m.1 0) = m.2 (m.1 1))
  | _ => false

/-- Input: `a = b` (asserted) and `f a ≠ f b` (asserted negation of the goal). -/
def original : List (Cid × Clause) := [(1, [1]), (2, [-2])]

/-- The `eq_congruent` lemma `¬(a = b) ∨ (f a = f b)` (mixed polarity). -/
def lemmas : List (Cid × Clause) := [(3, [-1, 2])]

/-- RUP refutation: `a=b` (1) and `f a ≠ f b` (-2) with the lemma close to ⊥. -/
def proof : List (Cid × Clause × List Int) := [(4, [], [1, 2, 3])]

/-- Congruence lemma validity — premise (b): `a = b → f a = f b` in every model.
    `by_cases` on the argument equality; when it holds, `simp` rewrites the
    argument and the conclusion is `rfl` (this is the congruence content). -/
theorem cong_lemma_valid (m : Val) : clauseSat (atomVal m) [-1, 2] = true := by
  simp only [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]
  by_cases h1 : m.1 0 = m.1 1 <;> simp [h1]

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact cong_lemma_valid m

/-- **EUF congruence through the verified firewall.** No model `(v, f)` satisfies
    `a = b ∧ f a ≠ f b`. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.CombinedEufCongruence
