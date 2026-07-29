/-
  REAL-FAITHFUL model abstraction for the SMT-LIB `Reals` theory.

  Lean core has no ℝ (and no Mathlib is vendored here — `lake-manifest.json` has
  zero packages), so a `no_model` theorem over `Int`/`Rat` would certify a
  STRICTLY WEAKER statement than a Real-sorted `unsat` verdict ("no rational
  model" does not entail "no real model": `x*x = 2` is rational-unsat and
  real-sat). Emitting one would be a §0 faithfulness violation.

  The faithful alternative implemented here: do NOT construct ℝ. Instead
  axiomatise a LINEARLY ORDERED FIELD with exactly the properties the SMT-LIB
  `Reals` theory declares, and state the refutation UNIVERSALLY over every such
  structure. "No model in ANY linearly ordered field" DOES entail "no model over
  ℝ", because ℝ is a linearly ordered field by the definition of the sort.

  NON-VACUITY (essential): a theorem quantified over an INCONSISTENT axiom set is
  vacuously true and certifies nothing. `ratOrdField` below exhibits `Rat` as a
  model of every axiom, so the class is inhabited and the quantification is
  meaningful. `Rat` is used ONLY as this consistency witness — it is never the
  model the refutation runs over.

  SCOPE NOTE (do not over-claim): this module does NOT generalise
  `AySoundness.Farkas`. `Farkas.lean` is `abbrev Model := Nat → Int` end to end,
  so `farkas_sound` would have to be RE-PROVED over an abstract ordered field,
  not merely extended with a rational embedding. Nothing here touches it.

  No imports: this module depends only on Lean 4 core, so `firewall_verify.rs`
  can embed it verbatim into a standalone artifact.
-/
namespace AySoundness

/-- A linearly ordered field, bundled (carrier + operations + axioms).

    Every axiom below is a theorem of ℝ, so ℝ is an instance; the axioms are
    exactly the ones SMT-LIB's `Reals` theory guarantees, minus completeness and
    Archimedeanness (deliberately omitted — they are not needed by the equational
    + congruence refutations this abstraction targets, and omitting them makes
    the resulting theorem STRONGER, hence still sound for ℝ). -/
structure OrdField where
  carrier : Type
  add : carrier → carrier → carrier
  mul : carrier → carrier → carrier
  neg : carrier → carrier
  inv : carrier → carrier
  zero : carrier
  one : carrier
  le : carrier → carrier → Prop
  -- additive abelian group
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  add_zero : ∀ a, add a zero = a
  add_neg : ∀ a, add a (neg a) = zero
  -- commutative ring
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b, mul a b = mul b a
  mul_one : ∀ a, mul a one = a
  mul_zero : ∀ a, mul a zero = zero
  mul_add : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  -- field
  one_ne_zero : one ≠ zero
  mul_inv_cancel : ∀ a, a ≠ zero → mul a (inv a) = one
  -- linear order
  le_refl : ∀ a, le a a
  le_trans : ∀ a b c, le a b → le b c → le a c
  le_antisymm : ∀ a b, le a b → le b a → a = b
  le_total : ∀ a b, le a b ∨ le b a
  -- order/field compatibility
  add_le_add_left : ∀ a b c, le a b → le (add c a) (add c b)
  mul_nonneg : ∀ a b, le zero a → le zero b → le zero (mul a b)
  zero_le_one : le zero one

namespace OrdField

variable (F : OrdField)

/-- Strict order, derived (SMT-LIB `<` on Reals). -/
def lt (a b : F.carrier) : Prop := F.le a b ∧ a ≠ b

theorem zero_add (a : F.carrier) : F.add F.zero a = a := by
  rw [F.add_comm]; exact F.add_zero a

theorem neg_add (a : F.carrier) : F.add (F.neg a) a = F.zero := by
  rw [F.add_comm]; exact F.add_neg a

/-- Additive left cancellation — the engine of numeral distinctness. -/
theorem add_left_cancel {a b c : F.carrier} (h : F.add c a = F.add c b) : a = b := by
  have h2 : F.add (F.neg c) (F.add c a) = F.add (F.neg c) (F.add c b) := by rw [h]
  rw [← F.add_assoc, ← F.add_assoc, F.neg_add, F.zero_add, F.zero_add] at h2
  exact h2

/-- **Strict-versus-weak incompatibility.** `a < b` and `b ≤ a` cannot both hold.
    This single lemma discharges every one-variable bound contradiction the
    QF_LRA emitter recognizes: irreflexivity (`x > 5 ∧ x < 5`), asymmetry
    (`x > 1 ∧ x < 1`) and crossed numeric bounds (`x ≥ 10 ∧ x ≤ 5`, after
    `le_trans` collapses the variable out). -/
theorem lt_le_absurd {a b : F.carrier} (h1 : F.lt a b) (h2 : F.le b a) : False :=
  h1.2 (F.le_antisymm _ _ h1.1 h2)

theorem lt_trans {a b c : F.carrier} (h1 : F.lt a b) (h2 : F.lt b c) : F.lt a c := by
  refine ⟨F.le_trans _ _ _ h1.1 h2.1, ?_⟩
  intro hac
  exact h1.2 (F.le_antisymm _ _ h1.1 (hac ▸ h2.1))

/-- The numeral embedding `Nat → carrier` (`n ↦ 1 + 1 + … + 1`). SMT-LIB
    integer-valued Real decimals (`5.0`, `10.0`, …) render through this. -/
def ofNat (G : OrdField) : Nat → G.carrier
  | 0 => G.zero
  | n + 1 => G.add (ofNat G n) G.one

/-- Deliberately NOT `@[simp]`: numerals must stay OPAQUE in the emitted
    branch-closing `simp` calls, otherwise `F.ofNat 20` unfolds to a 20-deep
    `F.add` chain and the polarity hypotheses no longer match syntactically. -/
theorem ofNat_succ (n : Nat) :
    F.ofNat (n + 1) = F.add (F.ofNat n) F.one := rfl

/-- `n < n+1` in the field: adding `1 > 0` strictly increases. -/
theorem ofNat_lt_succ (n : Nat) : F.lt (F.ofNat n) (F.ofNat (n + 1)) := by
  rw [F.ofNat_succ]
  refine ⟨?_, ?_⟩
  · have h := F.add_le_add_left F.zero F.one (F.ofNat n) F.zero_le_one
    rw [F.add_zero] at h
    exact h
  · intro hEq
    -- `x = x + 1` cancels to `0 = 1`, contradicting `one_ne_zero`.
    have h0 : F.add (F.ofNat n) F.zero = F.add (F.ofNat n) F.one := by
      rw [F.add_zero]; exact hEq
    exact F.one_ne_zero (F.add_left_cancel h0).symm

theorem ofNat_lt_of_lt {m n : Nat} (h : m < n) : F.lt (F.ofNat m) (F.ofNat n) := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hlt | heq
    · exact F.lt_trans (ih hlt) (F.ofNat_lt_succ k)
    · subst heq; exact F.ofNat_lt_succ m

/-- **Numeral distinctness.** Distinct naturals embed to distinct field
    elements — true in EVERY ordered field (characteristic 0 is forced by
    `0 ≤ 1` + `1 ≠ 0` + translation-invariance). This is what replaces the
    Int emitter's `omega`-discharged `10 ≠ 20`. -/
theorem ofNat_ne {m n : Nat} (h : m ≠ n) : F.ofNat m ≠ F.ofNat n := by
  rcases Nat.lt_or_ge m n with hlt | hge
  · exact (F.ofNat_lt_of_lt hlt).2
  · have hlt : n < m := by omega
    exact fun heq => (F.ofNat_lt_of_lt hlt).2 heq.symm

end OrdField

/-! ## Consistency witness: `Rat` is an `OrdField`.

    Without this, `∀ F : OrdField, …` could be vacuously true. `Rat` is a
    linearly ordered field constructible in Lean core, so the axiom set is
    consistent and every theorem quantified over `OrdField` has real content.
    NOTE: this instance is NOT the model used by any refutation — a refutation
    proved over all of `OrdField` holds for ℝ precisely because it does NOT
    depend on this or any other particular instance. -/
def ratOrdField : OrdField where
  carrier := Rat
  add := (· + ·)
  mul := (· * ·)
  neg := (- ·)
  inv := (·⁻¹)
  zero := 0
  one := 1
  le := (· ≤ ·)
  add_assoc := Rat.add_assoc
  add_comm := Rat.add_comm
  add_zero := Rat.add_zero
  add_neg := Rat.add_neg_cancel
  mul_assoc := Rat.mul_assoc
  mul_comm := Rat.mul_comm
  mul_one := Rat.mul_one
  mul_zero := by intro a; simp
  mul_add := Rat.mul_add
  one_ne_zero := by decide
  mul_inv_cancel := Rat.mul_inv_cancel
  le_refl := fun _ => Rat.le_refl
  le_trans := fun _ _ _ h1 h2 => Rat.le_trans h1 h2
  le_antisymm := fun _ _ h1 h2 => Rat.le_antisymm h1 h2
  le_total := fun _ _ => Rat.le_total
  add_le_add_left := fun _ _ _ h => Rat.add_le_add_left.mpr h
  mul_nonneg := fun _ _ h1 h2 => Rat.mul_nonneg h1 h2
  zero_le_one := by decide

/-- The class is inhabited, so `∀ F : OrdField, …` is not vacuous. -/
theorem ordField_nonvacuous : Nonempty OrdField := ⟨ratOrdField⟩

end AySoundness
