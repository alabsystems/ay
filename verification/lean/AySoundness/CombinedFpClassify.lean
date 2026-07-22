import AySoundness.Firewall
import AySoundness.FpThy
/-
  FP CLASSIFICATION conflict through the verified firewall — the target shape for an
  FP classification emitter (the last theory without a firewall emitter).

  ay reduces floating point to bit-vectors (`FpToBv`) and reasons about the
  classification predicates is-zero / is-subnormal / is-inf / is-NaN / is-normal,
  which `AySoundness/FpThy.lean` proves are a genuine partition of every float's
  bitpattern (pairwise-exclusive + total, kernel-checked at width 5). A problem that
  asserts a float is BOTH infinity AND NaN is therefore UNSAT — no bitpattern is
  both (`FpThy.no_inf_and_nan`).

  Worked obligation: `(and (fp.isInfinite x) (fp.isNaN x))` over the concrete format
  `e=2, s=2` (width 5). Atoms: `1 ↦ isInf(x)`, `2 ↦ isNaN(x)`. The classification
  exclusivity `¬isInf ∨ ¬isNaN` is a VALID theory lemma (every FP bitpattern), and
  resolution closes `[1], [2], [-1,-2]` to the empty clause — so no float `x`
  satisfies `isInf(x) ∧ isNaN(x)`.

  `#print axioms no_model` ⊆ {propext, Quot.sound} (all Bool/BitVec, computable); no
  `sorry`, no `native_decide`. Mirrors the `FirewallExample` (LIA) shape with the FP
  classifier as the theory.
-/
namespace AySoundness.CombinedFpClassify
open AySoundness

/-- The theory model: a concrete-format float as its bit-vector encoding. -/
abbrev Val := BitVec FpThy.W

/-- Propositional valuation induced by a float bitpattern: atoms are the
    classification predicates `FpThy` proves consistent. -/
def atomVal (x : Val) : Nat → Bool
  | 1 => @FpThy.isInfBits 2 2 x
  | 2 => @FpThy.isNaNBits 2 2 x
  | _ => false

def original : List (Cid × Clause) := [(1, [1]), (2, [2])]
def lemmas : List (Cid × Clause) := [(3, [-1, -2])]
def proof : List (Cid × Clause × List Int) := [(4, [], [1, 2, 3])]

/-- The classification exclusivity `¬isInf(x) ∨ ¬isNaN(x)` holds for EVERY float
    bitpattern — exactly `FpThy.no_inf_and_nan`. -/
theorem lemma_valid :
    ∀ c ∈ clauses lemmas, ∀ x : Val, clauseSat (atomVal x) c = true := by
  intro c hc x
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  subst hc
  simp only [clauseSat, atomVal, AySoundness.litSat, List.any_cons, List.any_nil]
  have h := FpThy.no_inf_and_nan x
  cases hi : @FpThy.isInfBits 2 2 x <;> cases hn : @FpThy.isNaNBits 2 2 x <;>
    simp_all

/-- No concrete-format float is both infinity and NaN — via the verified firewall
    (FP classification exclusivity + `lratCheck`). -/
theorem no_model : ∀ x : Val, ¬ Sat (atomVal x) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemma_valid (by decide)

end AySoundness.CombinedFpClassify
