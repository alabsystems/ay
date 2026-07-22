import AySoundness.Lrat
/-
  The soundness FIREWALL (capstone of the development design notes §2).

  ay decides a combined-theory UNSAT by: bit-blasting / abstracting atoms to
  propositional variables, learning THEORY-LEMMA clauses (each justified by a
  theory solver — Farkas for LIA/LRA, congruence for EUF, read-over-write for
  arrays, …), and driving the propositional core to the empty clause by
  resolution. The verdict is sound exactly when

    (a) the resolution derivation of the empty clause is valid       — `lratCheck_sound`
        (already verified: AySoundness/Lrat.lean), and
    (b) every learned theory-lemma clause holds in every model of the theory
        — supplied, per lemma, by the corresponding VERIFIED theory validator
        (Farkas/EUF/Array/BitVec/String/Set/Datatype/Multiset/Seq).

  This file proves the COMPOSITION: (a) + (b) ⟹ the original problem is
  theory-unsatisfiable. It is parameterised over an arbitrary model type `Val`
  and an interpretation `atomVal : Val → (propositional valuation)`, so it plugs
  into ANY theory whose validator can discharge premise (b). The result is that
  ay's combined UNSAT verdicts rest only on this proof + the theory validators +
  Lean's kernel — the unverified search (CDCL, theory propagation, heuristics,
  JIT) is never trusted.

  Pure Lean 4 core.
-/
namespace AySoundness


/-- Dropping clauses that hold in every model preserves unsatisfiability of the
    remainder: if `Fc ++ Lc` is unsatisfiable and every clause of `Lc` is true
    under every valuation, then `Fc` alone is unsatisfiable. -/
theorem unsat_drop_valid {Fc Lc : List Clause}
    (hvalid : ∀ c ∈ Lc, ∀ M : Nat → Bool, clauseSat M c = true)
    (h : Unsat (Fc ++ Lc)) : Unsat Fc := by
  rintro ⟨M, hM⟩
  exact h ⟨M, by
    intro c hc
    rcases List.mem_append.mp hc with h1 | h2
    · exact hM c h1
    · exact hvalid c h2 M⟩

/-- **The firewall: combined-theory UNSAT soundness.**

    `original` are the input clauses (atoms abstracted to propositional vars);
    `lemmas` are the learned theory-lemma clauses; `proof` is the LRAT/RUP
    derivation of the empty clause from `original ++ lemmas`.

    Premise (a) is `h` (the resolution checker accepts) — verified by
    `lratCheck_sound`. Premise (b) is `hvalid`: every theory-lemma clause holds
    under the propositional valuation induced by EVERY theory model `m : Val`
    (this is exactly what each verified theory validator establishes — e.g. a
    Farkas certificate gives that the LIA conflict clause holds in every LIA
    model). Conclusion: NO theory model `m` satisfies the original problem — it
    is theory-unsatisfiable. The CDCL/theory search is never trusted. -/
theorem firewall_combined_unsat {Val : Type} (atomVal : Val → Nat → Bool)
    {original lemmas : List (Cid × Clause)}
    {proof : List (Cid × Clause × List Int)}
    (hwf : tableWf (original ++ lemmas)) (hpw : proofWf proof)
    (hvalid : ∀ c ∈ clauses lemmas, ∀ m : Val, clauseSat (atomVal m) c = true)
    (h : lratCheck (original ++ lemmas) proof = true) :
    ∀ m : Val, ¬ Sat (atomVal m) (clauses original) := by
  have hu : Unsat (clauses (original ++ lemmas)) := lratCheck_sound hwf hpw h
  -- clauses distributes over append
  have hsplit : clauses (original ++ lemmas) = clauses original ++ clauses lemmas := by
    simp [clauses, List.map_append]
  rw [hsplit] at hu
  -- A theory model `m` satisfying `original` would, with the valid lemmas,
  -- satisfy `original ++ lemmas` — contradicting `hu`. (We cannot use
  -- `unsat_drop_valid`: the lemmas are valid only under theory-induced
  -- valuations `atomVal m`, not under every propositional valuation.)
  intro m hSat
  refine hu ⟨atomVal m, ?_⟩
  intro c hc
  rcases List.mem_append.mp hc with h1 | h2
  · exact hSat c h1
  · exact hvalid c h2 m

/-- **The firewall: SAT direction.** A theory model `m` whose induced valuation
    satisfies every input clause witnesses (theory-)satisfiability. ay emits a
    `Sat` verdict only after `verify_model_strict` DECIDABLY checks exactly this
    `Sat (atomVal m) (clauses original)` (every assertion evaluates to `true`
    under `m` via the verified per-theory evaluators), so the runtime model-check
    IS the satisfiability witness. Combined with `firewall_combined_unsat`, every
    definitive verdict is gated by a kernel-checkable certificate; the unverified
    search is never trusted in either direction. -/
theorem firewall_combined_sat {Val : Type} (atomVal : Val → Nat → Bool)
    {original : List (Cid × Clause)} (m : Val)
    (h : Sat (atomVal m) (clauses original)) :
    ∃ v : Nat → Bool, Sat v (clauses original) :=
  ⟨atomVal m, h⟩

/-- The runtime model-check is decidable, so ay can actually compute it before
    emitting `Sat` (this is the soundness content of `verify_model_strict`). -/
instance (M : Nat → Bool) (cs : List Clause) : Decidable (Sat M cs) := by
  unfold Sat; infer_instance

/-!
## Combination (Nelson–Oppen), soundness direction.

`firewall_combined_unsat` is ALREADY the combination-soundness theorem: its model
type `Val` is arbitrary, so for a multi-theory problem take `Val` to be the
product of the component theory models (e.g. `Int × (Nat → Int) × …`) and let
`atomVal` evaluate each abstracted atom in its own theory. Each theory's verified
validator (Farkas, EUF `der_conflict_unsat`, arrays, …) discharges its lemmas'
`hvalid` obligation under the shared combined model — including lemmas over the
shared equalities that connect theories. The resolution checker then closes the
propositional skeleton. Thus a combined UNSAT verdict is sound with no extra
trust. (Nelson–Oppen *completeness* — that a refutation is always FOUND via
purification + equality propagation — is a separate, search-side concern and not
needed for soundness.) `FirewallExample` below instantiates `Val := Int`.
-/

/-! ## Worked example: a LIA conflict closed by a Farkas-style theory lemma.

    Atoms: `1 ↦ (x > 5)`, `2 ↦ (x < 3)`. Theory model = the value of `x : Int`.
    Input problem `original = (x>5) ∧ (x<3)`. The theory lemma
    `lemmas = ¬(x>5) ∨ ¬(x<3)` holds in EVERY integer model (Farkas/`omega`).
    The LRAT proof resolves `[1]`, `[2]`, `[-1,-2]` to the empty clause, so the
    firewall concludes no `x : Int` satisfies `(x>5) ∧ (x<3)`. -/

namespace FirewallExample

/-- Propositional valuation induced by an integer model of `x`. -/
def atomVal (x : Int) : Nat → Bool
  | 1 => decide (x > 5)
  | 2 => decide (x < 3)
  | _ => false

def original : List (Cid × Clause) := [(1, [1]), (2, [2])]
def lemmas   : List (Cid × Clause) := [(3, [-1, -2])]
def proof    : List (Cid × Clause × List Int) := [(4, [], [1, 2, 3])]

/-- The theory lemma `¬(x>5) ∨ ¬(x<3)` holds for every integer `x`. -/
theorem lemma_valid :
    ∀ c ∈ clauses lemmas, ∀ x : Int, clauseSat (atomVal x) c = true := by
  intro c hc x
  simp only [clauses, lemmas, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  subst hc
  -- clauseSat (atomVal x) [-1,-2] = (atomVal x).litSat (-1) || (atomVal x).litSat (-2)
  simp only [clauseSat, atomVal, AySoundness.litSat, List.any_cons, List.any_nil]
  -- reduces to: ¬(x>5) || ¬(x<3) = true
  by_cases h : x > 5
  · simp [h]; omega
  · simp [h]

/-- The firewall verdict: no integer is both `> 5` and `< 3`. -/
theorem no_x_gt5_lt3 : ∀ x : Int, ¬ Sat (atomVal x) (clauses original) :=
  firewall_combined_unsat (original := original) (lemmas := lemmas) (proof := proof)
    atomVal (by decide) (by decide) lemma_valid (by decide)

end FirewallExample
end AySoundness
