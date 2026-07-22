import AySoundness.Firewall
/-
  BIT-VECTOR (small-width) conflict, refuted through the verified firewall —
  CORRECTING the earlier "BV blocked in pure core" finding. ay bit-blasts BV
  eagerly, so its BV refutation is a bare `(cl) :rule trust` (no theory lemma to
  ground); but for SMALL widths the BV fact is decidable by finite enumeration,
  so the emitter reconstructs it from the parsed assertions (like strings).

  The earlier blocker was that `decide` over `∀ m : BitVec n × BitVec n` fails —
  the PRODUCT type lacks a decidable-∀ instance in pure Lean core. The fix:
  DESTRUCTURE then CURRY — `obtain ⟨x, y⟩ := m; revert x y; decide` — because
  `∀ (x y : BitVec n), …` IS decidable in core (no Mathlib `Fintype` needed).

  Example: `bvand x y = 0xF ∧ x ≠ 0xF ⊢ ⊥` over `BitVec 4` (`bvand x y = 0xF`
  forces every bit of x to 1). Model `Val = BitVec 4 × BitVec 4`; the tautology
  `¬(x &&& y = 0xF) ∨ (x = 0xF)` is discharged by curried `decide`.
  `#print axioms no_model` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`,
  no `native_decide`. Feasible for small widths/few vars (case count = ∏ 2^wᵢ);
  large widths need Mathlib `bv_decide` or SAT-level reconstruction.
-/
namespace AySoundness.CombinedBvBitwise
open AySoundness

abbrev Val := BitVec 4 × BitVec 4

/-- Atoms: `1 ↦ bvand x y = 0xF`, `2 ↦ x = 0xF`. -/
def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => decide (m.1 &&& m.2 = 0xF#4)
  | 2 => decide (m.1 = 0xF#4)
  | _ => false

def original : List (Cid × Clause) := [(1, [1]), (2, [-2])]
def lemmas   : List (Cid × Clause) := [(3, [-1, 2])]
def proof    : List (Cid × Clause × List Int) := [(4, [], [1, 2, 3])]

/-- `¬(x &&& y = 0xF) ∨ (x = 0xF)` holds for all 4-bit `x, y` — curried `decide`
    (destructure the product, then enumerate over each `BitVec 4` factor). -/
theorem bitwise_lemma_valid (m : Val) : clauseSat (atomVal m) [-1, 2] = true := by
  obtain ⟨x, y⟩ := m
  revert x y
  decide

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact bitwise_lemma_valid m

/-- No 4-bit `(x, y)` satisfies `bvand x y = 0xF ∧ x ≠ 0xF` — via the firewall. -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.CombinedBvBitwise
