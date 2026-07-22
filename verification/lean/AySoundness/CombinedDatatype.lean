import AySoundness.Firewall
import AySoundness.Datatype
/-
  A datatype constructor-DISTINCTNESS conflict, refuted through the verified
  firewall (`AySoundness.firewall_combined_unsat`). This is the Lean grounding of
  ay's emitted `:rule dt_distinct` lemma (ay `30637b39d6`) — the datatype analog
  of `EndToEnd.lean` (SAT/PHP) and `CombinedExample.lean` (EUF+LIA): it takes
  ay's ACTUAL proof for

      (declare-datatype Color ((red) (green) (blue)))
      (declare-const c Color)
      (assert (= c red)) (assert (= c green))      ⊢  unsat

  whose certificate (verbatim from `ay --strict-proofs … (get-proof)`) is

      (step t2 (cl (not (= c red)) (not (= c green))) :rule dt_distinct)
      (step t3 (cl (not (= c green)))  :rule th_resolution :premises (t2 t0))
      (step t4 (cl)                    :rule th_resolution :premises (t3 t1))

  and discharges it through `firewall_combined_unsat`:
    * premise (a) — the resolution closes (`lratCheck … = true`, by `decide`);
    * premise (b) — the `dt_distinct` lemma `¬(c=red) ∨ ¬(c=green)` holds in
      EVERY model, because `red` and `green` are DISTINCT CONSTRUCTORS so no `c`
      is both. That is exactly the principle verified in `AySoundness.Datatype`
      (`dist_conflict_unsat : ¬(leaf = node a b)`); here the concrete instance
      over `Color` is `red ≠ green`, which the Lean kernel discharges from the
      constructor-distinctness of the `inductive` (its initial-model semantics).

  This is precisely the "import-the-verified-theorem" shape the per-theory
  emitter must target for the datatype theory. Pure Lean 4 core — `#print axioms`
  is ⊆ {propext, Classical.choice, Quot.sound}, no `sorry`, native compiler NOT
  in the TCB (`decide`, not `native_decide`).
-/
namespace AySoundness.CombinedDatatype
open AySoundness

/-- The datatype `Color` from the SMT problem: three nullary constructors.
    Its `inductive` declaration IS the initial/free model the SMT datatype
    theory specifies — constructors are distinct and injective by construction. -/
inductive Color where
  | red
  | green
  | blue
deriving DecidableEq

/-- Distinct constructors are unequal — the concrete `Color` instance of the
    datatype distinctness principle verified generally in `AySoundness.Datatype`
    (`dist_conflict_unsat`). The kernel proves it from the inductive's
    constructor-distinctness; no axioms beyond the kernel's. -/
theorem red_ne_green : (Color.red ≠ Color.green) := by decide

/-- Atom interpretation under a model (the value of `c`):
    `1 ↦ c = red`, `2 ↦ c = green`. -/
def atomVal (c : Color) (n : Nat) : Bool :=
  match n with
  | 1 => decide (c = Color.red)
  | 2 => decide (c = Color.green)
  | _ => false

/-- Input clauses: `c = red` (asserted), `c = green` (asserted). -/
def original : List (Cid × Clause) := [(1, [1]), (2, [2])]

/-- The single `dt_distinct` theory lemma `t2`: `¬(c = red) ∨ ¬(c = green)`. -/
def lemmas : List (Cid × Clause) := [(3, [-1, -2])]

/-- RUP/LRAT refutation: the unit clauses `1`, `2` and the distinctness lemma
    `3` propagate to the empty clause (ay's `t3`,`t4` resolution chain). -/
def proof : List (Cid × Clause × List Int) := [(4, [], [1, 2, 3])]

/-- **Distinctness lemma validity** — premise (b) of the firewall.
    `¬(c=red) ∨ ¬(c=green)` holds for every `c : Color`, because `red ≠ green`
    (distinct constructors), so no value of `c` satisfies both equalities. -/
theorem dt_distinct_lemma_valid (c : Color) :
    clauseSat (atomVal c) [-1, -2] = true := by
  cases c <;>
    simp [clauseSat, atomVal, litSat, List.any_cons, List.any_nil]

/-- Every theory lemma is valid in every model (the firewall's premise (b)). -/
theorem lemmas_valid :
    ∀ cl ∈ clauses lemmas, ∀ c : Color, clauseSat (atomVal c) cl = true := by
  intro cl hcl c
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  subst hcl
  exact dt_distinct_lemma_valid c

/-- **Datatype distinctness, demonstrated through the verified firewall.**
    No model assigns `c` both `red` and `green` — concluded from ay's resolution
    proof (premise (a)) and the `dt_distinct` lemma (premise (b)), each
    kernel-checked. The datatype analog of `Firewall`'s `no_x_gt5_lt3`. -/
theorem no_color_model : ∀ c : Color, ¬ Sat (atomVal c) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemmas_valid (by decide)

end AySoundness.CombinedDatatype
