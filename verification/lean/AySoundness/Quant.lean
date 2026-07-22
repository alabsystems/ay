/-
  Soundness of QUANTIFIER reasoning: universal instantiation, the (sound version
  of the) CEGQI conflict, and Skolemization — the theory whose *unsound* incarnation
  was ay's classA wrong-UNSAT bug, here formalized DONE RIGHT.

  ay handles quantifiers by INSTANTIATION: a universal `∀ x, P x` is sound to
  replace by any finite set of ground instances `P t₁, …, P tₙ` (each `tᵢ` a
  ground term in the model's domain), and these instance lemmas are fed to the
  combined-theory firewall just like any other theory lemma. For the firewall's
  premise (b) to hold, each emitted instance lemma must be ENTAILED by the
  universal it came from — i.e. true in every model of the universal. That is the
  content of this file.

  Three soundness facts, each a real entailment / (un)satisfiability statement —
  never `True`:

    * `forall_inst`        — universal instantiation: `(∀ x, P x) → P t`.
    * `cegqi_conflict_unsat` — the classA pattern done RIGHT: a universal together
                             with a ground counter-instance `¬ P c` is
                             UNSATISFIABLE. (The instance `P c` from the forall
                             contradicts the asserted `¬ P c`.) This is the SOUND
                             conflict; the bug was reporting this conflict when no
                             such ground counter-instance was actually entailed.
    * `not_exists_iff_forall_not` / `skolem_witness` — Skolemization soundness:
                             `¬ ∃ x, P x ↔ ∀ x, ¬ P x`, and an existential always
                             has a witness in a model where it holds.

  HEADLINE TIE-IN (`classA_correct`): the formula `¬ ∃ (x:Int), x ≤ 4 ∧ p` is
  SATISFIABLE exactly when `p` is false. Since `∃ x:Int, x ≤ 4` is trivially true
  (witness `x = 0`), the conjunction's satisfiability is governed *entirely* by
  `p`, so the formula is equivalent to `¬ p`. This pins classA's CORRECT answer —
  `sat` with `p := false` — the verdict ay used to get wrong by answering `unsat`.

  Pure Lean 4 core (no Mathlib).
-/
namespace AySoundness.Quant

/-! ## 1. Universal instantiation (the core entailment).

    `P : D → Prop` is an arbitrary body predicate over an arbitrary nonempty
    domain `D` (we never need nonemptiness here — instantiation is sound at any
    ground `t : D`). This is the lemma each emitted ground instance rests on: the
    instance `P t` is genuinely a logical consequence of `∀ x, P x`. -/

theorem forall_inst {D : Type} {P : D → Prop} (h : ∀ x, P x) (t : D) : P t :=
  h t

/-- Instantiating at SEVERAL ground terms at once: a finite instance set is
    entailed (the firewall is fed a list of ground instances per trigger). Every
    element of the instance list `P t` holds, so the whole conjunction of emitted
    instances is a consequence of the single universal. -/
theorem forall_inst_list {D : Type} {P : D → Prop} (h : ∀ x, P x) :
    ∀ ts : List D, ∀ t ∈ ts, P t :=
  fun _ t _ => h t

/-! ## 2. The classA conflict, done RIGHT (CEGQI soundness).

    The Counter-Example-Guided Quantifier Instantiation loop, when it has a
    universal `∀ x, P x` and a candidate counterexample `c` with `¬ P c`, reports
    a CONFLICT. That conflict is SOUND precisely because `∀ x, P x` entails `P c`,
    which contradicts `¬ P c`: no model can satisfy both. The classA wrong-UNSAT
    bug was reporting this conflict in a situation where the ground counter-instance
    was *not* actually entailed (CE-lemma over-constraint); here we certify the
    statement the conflict is allowed to make.

    We phrase it as genuine unsatisfiability: there is NO model `M` (an assignment
    of the body predicate `P` and the witness `c`) satisfying both the universal
    and its negated ground instance. -/

/-- A "model" for the conflict: a domain `D`, a body predicate `P` over it, and a
    distinguished ground term `c`. Satisfaction = the universal holds AND the
    counter-instance `¬ P c` holds. The conflict is sound = no such model exists. -/
structure ConflictModel where
  D : Type
  P : D → Prop
  c : D

def ConflictModel.sat (M : ConflictModel) : Prop :=
  (∀ x, M.P x) ∧ ¬ M.P M.c

/-- **CEGQI conflict soundness (classA done right).** A universal `∀ x, P x`
    together with a ground counter-instance `¬ P c` is UNSATISFIABLE: no model
    realizes both, because the forall entails `P c`. This is the precise verdict
    ay is licensed to emit — and only this; emitting it without a real `¬ P c`
    obligation is the unsoundness that was fixed. -/
theorem cegqi_conflict_unsat : ¬ ∃ M : ConflictModel, M.sat := by
  rintro ⟨M, hAll, hNot⟩
  exact hNot (forall_inst hAll M.c)

/-- The same fact stated directly over an arbitrary domain/predicate (no wrapper),
    so it composes with the firewall's per-lemma `hvalid` obligation: in EVERY
    interpretation of `P`, you cannot have both the universal and `¬ P c`. -/
theorem forall_and_neg_inst_unsat {D : Type} (P : D → Prop) (c : D) :
    ¬ ((∀ x, P x) ∧ ¬ P c) := by
  rintro ⟨hAll, hNot⟩
  exact hNot (hAll c)

/-! ## 3. Skolemization soundness.

    Negating a universal yields an existential and vice versa; and an existential
    that holds has a witness. These justify ay's Skolem step (replace `∃ x, P x`
    by `P sk` for a fresh constant `sk`) and the dual normalization of `¬ ∃`. -/

/-- `¬ ∃ x, P x ↔ ∀ x, ¬ P x` over an arbitrary domain. (The dual that justifies
    pushing negation through quantifiers during prenexing/Skolemization.) -/
theorem not_exists_iff_forall_not {D : Type} (P : D → Prop) :
    (¬ ∃ x, P x) ↔ ∀ x, ¬ P x := by
  constructor
  · intro h x hx; exact h ⟨x, hx⟩
  · rintro h ⟨x, hx⟩; exact h x hx

/-- `¬ ∀ x, P x ↔ ∃ x, ¬ P x` (classical; the existential-Skolem direction). -/
theorem not_forall_iff_exists_not {D : Type} (P : D → Prop) :
    (¬ ∀ x, P x) ↔ ∃ x, ¬ P x := by
  constructor
  · intro h
    by_cases hx : ∃ x, ¬ P x
    · exact hx
    · exact absurd (fun x => Classical.byContradiction (fun hnp => hx ⟨x, hnp⟩)) h
  · rintro ⟨x, hx⟩ hAll; exact hx (hAll x)

/-- **Skolem witness soundness.** If `∃ x, P x` holds in a model, then `P` holds
    at the chosen witness `Classical.choose h` — i.e. the Skolem constant really
    satisfies the matrix. (This is the only place we *need* classical choice, and
    it is in the approved axiom set.) -/
theorem skolem_witness {D : Type} {P : D → Prop} (h : ∃ x, P x) :
    P (Classical.choose h) :=
  Classical.choose_spec h

/-! ## 4. HEADLINE: classA, the formula whose UNSAT verdict was the bug.

    classA reduces (after the front end) to `∃ (x:Int), x ≤ 4 ∧ p` under a
    surrounding negation: the solver was asked whether `¬ ∃ x:Int, x ≤ 4 ∧ p` is
    satisfiable. ay used to answer UNSAT (claiming the negation is a contradiction
    for all `p`). The CORRECT semantics: `∃ x:Int, x ≤ 4` is trivially TRUE
    (witness `x = 0`), so `∃ x, x ≤ 4 ∧ p ↔ p`, hence `¬ ∃ x, x ≤ 4 ∧ p ↔ ¬ p`.
    The formula is therefore SATISFIABLE iff `p` is false — the answer ay now
    gives. -/

/-- **classA correctness.** `¬ ∃ x:Int, x ≤ 4 ∧ p` holds iff `¬ p`. Equivalently,
    the formula is satisfiable exactly when `p` is FALSE — formally certifying
    that classA's correct answer is `sat (p := false)`, the verdict ay used to
    get wrong (it answered `unsat`, i.e. it treated the LHS as outright false). -/
theorem classA_correct (p : Prop) : (¬ ∃ x : Int, x ≤ 4 ∧ p) ↔ ¬ p := by
  constructor
  · intro h hp
    exact h ⟨0, by omega, hp⟩
  · intro hnp ⟨_, _, hp⟩
    exact hnp hp

/-- The underlying existential pinned: `∃ x:Int, x ≤ 4 ∧ p ↔ p`. This is the
    non-vacuity heart of `classA_correct` — the quantifier genuinely collapses to
    `p` (it does NOT collapse to `True` or to `False`), because the constraint
    `x ≤ 4` is satisfiable in `Int`. -/
theorem classA_exists_iff (p : Prop) : (∃ x : Int, x ≤ 4 ∧ p) ↔ p := by
  constructor
  · rintro ⟨_, _, hp⟩; exact hp
  · intro hp; exact ⟨0, by omega, hp⟩

/-- The bound itself is genuinely satisfiable, so the collapse above is real and
    not by virtue of an empty constraint: `∃ x:Int, x ≤ 4` is TRUE. -/
theorem classA_bound_sat : ∃ x : Int, x ≤ 4 := ⟨0, by omega⟩

/-! ## 5. Concrete kernel-checked examples (non-vacuity witnesses). -/

namespace Example

/-- Universal instantiation on a concrete integer body: from `∀ n:Int, n + 0 = n`
    instantiate at `7`. Kernel-checked. -/
theorem inst_concrete : (∀ n : Int, n + 0 = n) → (7 : Int) + 0 = 7 :=
  fun h => forall_inst h 7

/-- A concrete SOUND conflict: `(∀ n:Int, n ≥ 0 ∨ n < 0)` together with the
    negated ground instance `¬ (5 ≥ 0 ∨ 5 < 0)` is unsatisfiable. Uses the general
    `forall_and_neg_inst_unsat`. -/
theorem conflict_concrete :
    ¬ ((∀ n : Int, n ≥ 0 ∨ n < 0) ∧ ¬ ((5 : Int) ≥ 0 ∨ (5 : Int) < 0)) :=
  forall_and_neg_inst_unsat (fun n : Int => n ≥ 0 ∨ n < 0) 5

/-- classA with `p := False` is SAT-side: `¬ ∃ x:Int, x ≤ 4 ∧ False` is TRUE
    (the negation holds), i.e. the original formula is satisfiable with `p` false.
    This is exactly the answer ay must give. Kernel-checked via `classA_correct`. -/
theorem classA_p_false : ¬ ∃ x : Int, x ≤ 4 ∧ False :=
  (classA_correct False).mpr (not_false)

/-- classA with `p := True` is UNSAT-side: `¬ ∃ x:Int, x ≤ 4 ∧ True` is FALSE
    (the existential holds, so its negation cannot). Shows the verdict really
    depends on `p` — the statement is non-vacuous. -/
theorem classA_p_true : ¬ (¬ ∃ x : Int, x ≤ 4 ∧ True) := by
  intro h
  exact (classA_correct True).mp h trivial

/-- Concrete Skolem witness: from `∃ n:Int, n > 10` we get a witness with the
    property. Kernel-checked (witness existence; the chosen value is opaque but
    provably satisfies the matrix). -/
theorem skolem_concrete : (10 : Int) < Classical.choose (⟨11, by omega⟩ : ∃ n : Int, n > 10) :=
  Classical.choose_spec (⟨11, by omega⟩ : ∃ n : Int, n > 10)

end Example
end AySoundness.Quant
