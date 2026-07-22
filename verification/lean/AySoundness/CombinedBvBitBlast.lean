import AySoundness.Firewall
/-
  BIT-BLASTING through the verified firewall — the PoC of the target shape for the
  BV-LARGE emitter tier (the grounding that scales past the brute-`decide` gate).

  The small-width BV emitter refutes by curried `decide` over the whole
  `(2^w)^vars` value space — which TIMES OUT the kernel beyond ~4096 cases (e.g.
  two free 8-bit vars = 65536). Bit-blasting sidesteps that entirely: introduce a
  Boolean variable per bit, a Tseitin auxiliary per gate output, assert the
  per-gate DEFINING clauses, and refute the resulting CNF by `lratCheck`
  (resolution). Crucially, in the firewall each gate clause is a VALID lemma whose
  validity is a TINY Boolean tautology over just that gate's input/output bits
  (a few `decide` cases), NOT a `(2^w)^vars` enumeration — so the cost is
  per-gate-constant + a short resolution proof, no matter the width.

  Worked example: `bvand x y = #b1 ∧ x = #b0` over `BitVec 1` is UNSAT (`x = 0` ⟹
  `x &&& y = 0 ≠ 1`). Bits: `1 ↦ x₀`, `2 ↦ y₀`, `3 ↦ (x &&& y)₀` (the AND gate
  output). The Tseitin defining clauses for `a₀ ↔ x₀ ∧ y₀` are valid (the model
  computes `a₀ = x₀ && y₀`); resolution closes
  `[a₀], [¬a₀ ∨ x₀], [¬x₀]` to the empty clause. This scales: more gates ⟶ more
  small per-gate lemmas + a longer LRAT, each piece still tiny.

  `#print axioms no_model` ⊆ {propext, Quot.sound} (Bool/BitVec are computable);
  no `sorry`, no `native_decide`. This is the verified target a bit-blasting BV
  emitter (ay's CNF + SAT-emitted LRAT + this computed `atomVal`) reproduces.
-/
namespace AySoundness.CombinedBvBitBlast
open AySoundness

/-- A model: the two 1-bit inputs. -/
structure Val where
  x : BitVec 1
  y : BitVec 1

/-- Atoms are BITS: `1 ↦ x₀`, `2 ↦ y₀`, `3 ↦ (AND gate output) = x₀ ∧ y₀`. The
    gate output is COMPUTED from the inputs (Tseitin auxiliary, not free). -/
def atomVal (m : Val) (n : Nat) : Bool :=
  match n with
  | 1 => m.x.getLsbD 0
  | 2 => m.y.getLsbD 0
  | 3 => m.x.getLsbD 0 && m.y.getLsbD 0
  | _ => false

/-- `(x &&& y)₀ = 1` (so `a₀`, clause `[3]`) and `x = 0` (so `x₀ = false`, clause
    `[-1]`). -/
def original : List (Cid × Clause) := [(1, [3]), (2, [-1])]
/-- Tseitin defining clauses for the AND gate `a₀ ↔ x₀ ∧ y₀`. -/
def lemmas : List (Cid × Clause) := [(3, [-3, 1]), (4, [-3, 2]), (5, [3, -1, -2])]
/-- Unit-propagate `a₀=true` (clause 1) and `x₀=false` (clause 2), then the gate
    clause `[-3,1]` (clause 3) is falsified ⟹ empty clause. -/
def proof : List (Cid × Clause × List Int) := [(6, [], [1, 2, 3])]

/-- Each AND-gate Tseitin clause is valid: with `a₀ = x₀ && y₀` the defining
    clauses are Boolean tautologies over the two bits. -/
theorem gate_clauses_valid (m : Val) (cl : Clause)
    (h : cl = [-3, 1] ∨ cl = [-3, 2] ∨ cl = [3, -1, -2]) :
    clauseSat (atomVal m) cl = true := by
  rcases h with h | h | h <;> subst h <;>
    simp only [clauseSat, litSat, atomVal, List.any_cons, List.any_nil] <;>
    cases m.x.getLsbD 0 <;> cases m.y.getLsbD 0 <;> rfl

theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) cl = true := by
  intro cl hcl m
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  exact gate_clauses_valid m cl hcl

/-- No 1-bit model satisfies `x &&& y = 1 ∧ x = 0` — via bit-blasting through the
    verified firewall (per-gate validity + `lratCheck`, no value enumeration). -/
theorem no_model : ∀ m : Val, ¬ Sat (atomVal m) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.CombinedBvBitBlast
