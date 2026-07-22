/-
  Soundness of ay's native finite-set theory (QF_SETLIA — ay's set extension),
  the development design notes

  ay reasons about finite sets of integers with the usual operations
  (`emptyset`, `singleton`, `insert`, `union`, `inter`, `setminus`,
  `member`, `subset`, set-equality) and emits a conflict whenever a literal set
  contradicts the set axioms.  This ties to REAL ay cases: ay correctly returns
  UNSAT for the negations below, where z3 — which lacks `set.*` semantics and
  treats those symbols as uninterpreted functions — wrongly reported `sat`:

      ¬ ({1} ⊆ {0,1})     ay: UNSAT   (the subset DOES hold; its negation is unsat)
        {0} = {1}         ay: UNSAT   (the sets are NOT equal)
        {0} ⊆ {1}         ay: UNSAT   (the subset does NOT hold)

  A set conflict that uses only instances of the set axioms (plus congruence /
  equality reasoning) is sound iff the axioms hold in the intended model.  We fix
  the *standard characteristic-function model* — a set over `Int` is its
  characteristic predicate `Int → Bool`, `member` is application, the operations
  are the pointwise boolean combinations, `subset`/`seteq` are the pointwise
  implications/biconditionals — and prove all the set axioms hold there
  (`set_axioms_sound`).  Hence any propositionally-derived conflict built from
  these axiom instances refutes a genuinely unsatisfiable constraint set: the
  model cannot exist, because the axioms are valid.

  We prove the soundness PRINCIPLE (`set_axioms_sound`): in EVERY characteristic
  model, the membership laws + extensionality hold simultaneously.  The
  per-problem grounding (which set term is which) is the solver's congruence
  closure; the theory content is exactly these membership/subset/equality facts.
  We then refute the three concrete conflicts ay reported UNSAT
  (`not_sub_0_1`, `sing_0_ne_1`, and the validity of `sub_1_01`), formally
  vindicating ay over z3, mirroring the `farkas_sound` (principle) +
  concrete-`Example` (decidable instance) split.

  Pure Lean 4 core (no Mathlib).  The model definitions mirror the standard set
  semantics used by ay's QF_SETLIA decision procedure.
-/
namespace AySoundness.SetThy

/-! ## The standard characteristic-function model.

A set of integers is its characteristic predicate `Int → Bool`.  `member` is
application; the constructors and operations are the pointwise boolean
combinations.  This is the canonical model the QF_SETLIA decision procedure is
proved sound against. -/

/-- A finite/cofinite set of integers, as a characteristic function. -/
abbrev St := Int → Bool

/-- `mem x s` : does `x` belong to set `s`. -/
def mem (x : Int) (s : St) : Bool := s x

/-- The empty set: nothing is a member. -/
def emptyS : St := fun _ => false

/-- The singleton `{a}`: exactly `a` is a member. -/
def singleton (a : Int) : St := fun x => decide (x = a)

/-- `insert a s = {a} ∪ s`. -/
def insert (a : Int) (s : St) : St := fun x => decide (x = a) || s x

/-- Pointwise union. -/
def union (s t : St) : St := fun x => s x || t x

/-- Pointwise intersection. -/
def inter (s t : St) : St := fun x => s x && t x

/-- Pointwise set difference `s \ t`. -/
def diff (s t : St) : St := fun x => s x && !(t x)

/-- `subset s t` : every member of `s` is a member of `t`. -/
def subset (s t : St) : Prop := ∀ x, mem x s = true → mem x t = true

/-- `seteq s t` : `s` and `t` have exactly the same members (extensional
    equality). -/
def seteq (s t : St) : Prop := ∀ x, mem x s = mem x t

/-! ## The set axioms, valid in the characteristic model. -/

/-- **Empty membership.**  Nothing is a member of `∅`. -/
theorem mem_empty (x : Int) : mem x emptyS = false := by
  simp [mem, emptyS]

/-- **Singleton membership.**  `x ∈ {a} ↔ x = a`. -/
theorem mem_singleton (x a : Int) : mem x (singleton a) = true ↔ x = a := by
  simp [mem, singleton]

/-- **Insert membership.**  `x ∈ insert a s ↔ x = a ∨ x ∈ s`. -/
theorem mem_insert (x a : Int) (s : St) :
    mem x (insert a s) = true ↔ x = a ∨ mem x s = true := by
  simp [mem, insert]

/-- **Union membership.**  `x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t`. -/
theorem mem_union (x : Int) (s t : St) :
    mem x (union s t) = true ↔ mem x s = true ∨ mem x t = true := by
  simp [mem, union]

/-- **Intersection membership.**  `x ∈ s ∩ t ↔ x ∈ s ∧ x ∈ t`. -/
theorem mem_inter (x : Int) (s t : St) :
    mem x (inter s t) = true ↔ mem x s = true ∧ mem x t = true := by
  simp [mem, inter]

/-- **Difference membership.**  `x ∈ s \ t ↔ x ∈ s ∧ x ∉ t`. -/
theorem mem_diff (x : Int) (s t : St) :
    mem x (diff s t) = true ↔ mem x s = true ∧ mem x t = false := by
  simp [mem, diff]

/-- **Subset definition.**  `subset s t` unfolds to the pointwise implication —
    the law ay's subset reasoning relies on. -/
theorem subset_def (s t : St) :
    subset s t ↔ ∀ x, mem x s = true → mem x t = true := Iff.rfl

/-- **Extensionality.**  Two sets with the same members are the *same* function.
    This is what licenses ay to treat set-equality as full congruence. -/
theorem seteq_ext (s t : St) (h : seteq s t) : s = t := by
  funext x
  have := h x
  simpa [mem] using this

/-- Converse: equal sets have the same members.  Together with `seteq_ext` this
    is the full set-equality characterization `seteq s t ↔ s = t`. -/
theorem seteq_iff (s t : St) : seteq s t ↔ s = t := by
  constructor
  · exact seteq_ext s t
  · intro h x; rw [h]

/-! ## The soundness principle.

`set_axioms_sound` packages the membership laws + extensionality as a single
validity statement: for the characteristic-function `mem`/constructors/ops, ALL
the laws hold for every set and element.  This is the theory content the
QF_SETLIA validator relies on, so any conflict built solely from these axiom
instances is sound. -/

/-- **Set theory soundness.**  In the standard characteristic-function model the
    set axioms (empty, singleton, insert, union, inter, diff membership laws,
    subset definition, and extensionality) hold simultaneously.  A conflict that
    uses only these axiom instances therefore refutes a genuinely unsatisfiable
    constraint set. -/
theorem set_axioms_sound :
    (∀ (x : Int), mem x emptyS = false) ∧
    (∀ (x a : Int), mem x (singleton a) = true ↔ x = a) ∧
    (∀ (x a : Int) (s : St), mem x (insert a s) = true ↔ x = a ∨ mem x s = true) ∧
    (∀ (x : Int) (s t : St), mem x (union s t) = true ↔ mem x s = true ∨ mem x t = true) ∧
    (∀ (x : Int) (s t : St), mem x (inter s t) = true ↔ mem x s = true ∧ mem x t = true) ∧
    (∀ (x : Int) (s t : St), mem x (diff s t) = true ↔ mem x s = true ∧ mem x t = false) ∧
    (∀ (s t : St), subset s t ↔ ∀ x, mem x s = true → mem x t = true) ∧
    (∀ (s t : St), seteq s t → s = t) :=
  ⟨mem_empty, mem_singleton, mem_insert, mem_union, mem_inter, mem_diff,
   subset_def, seteq_ext⟩

/-! ## The headline ay setlia conflicts (kernel-checked, NON-vacuous).

These are the three cases where ay correctly returned UNSAT and z3 wrongly said
sat.  We prove the three conflicts ay reported are genuinely unsatisfiable
(their negations hold), formally vindicating ay over z3.  The integer
(in)equalities are decidable and discharged by `decide`. -/

/-- **`{1} ⊆ {0,1}` is TRUE.**  Hence its negation (ay's input) is unsatisfiable:
    every member of `{1}` (namely `1`) is a member of `insert 0 {1} = {0,1}`. -/
theorem sub_1_01 : subset (singleton 1) (insert 0 (singleton 1)) := by
  intro x hx
  -- `x ∈ {1}` forces `x = 1`, which is in `{0,1}`.
  rw [mem_singleton] at hx
  rw [mem_insert]
  exact Or.inr (by rw [mem_singleton]; exact hx)

/-- **`{0} ⊆ {1}` is FALSE.**  This refutes ay's reported conflict input: `0` is a
    member of `{0}` but not of `{1}` (since `0 ≠ 1`). -/
theorem not_sub_0_1 : ¬ subset (singleton 0) (singleton 1) := by
  intro h
  -- `0 ∈ {0}` by membership, so subset would force `0 ∈ {1}`, i.e. `0 = 1`.
  have h0 : mem 0 (singleton 0) = true := by rw [mem_singleton]
  have h1 : mem 0 (singleton 1) = true := h 0 h0
  rw [mem_singleton] at h1
  exact absurd h1 (by decide)

/-- **`{0} = {1}` is FALSE.**  The sets are not extensionally equal: `0` belongs
    to `{0}` but not to `{1}`. -/
theorem sing_0_ne_1 : ¬ seteq (singleton 0) (singleton 1) := by
  intro h
  -- extensional equality at `x = 0` would force `0 ∈ {1}`, i.e. `0 = 1`.
  have h0 : mem 0 (singleton 0) = mem 0 (singleton 1) := h 0
  have hl : mem 0 (singleton 0) = true := by rw [mem_singleton]
  rw [hl] at h0
  have h1 : mem 0 (singleton 1) = true := h0.symm
  rw [mem_singleton] at h1
  exact absurd h1 (by decide)

/-! ## Fully decidable concrete witnesses (kernel `decide`), mirroring the
    `decide`-example split in `ArrayThy` / `Datatype`. -/

/-- `1 ∈ {0,1}` — the membership fact underlying `sub_1_01`, kernel-checked. -/
theorem one_mem_0_1 : mem 1 (insert 0 (singleton 1)) = true := by decide

/-- `0 ∉ {1}` — the membership fact underlying `not_sub_0_1`, kernel-checked. -/
theorem zero_notmem_1 : mem 0 (singleton 1) = false := by decide

/-- The set-equality conflict `{0} = {1}`, witnessed concretely at the point `0`:
    `mem 0 {0} ≠ mem 0 {1}` (`true ≠ false`), so the sets differ.  Kernel-checked
    by `decide`. -/
theorem sing_0_ne_1_witness : mem 0 (singleton 0) ≠ mem 0 (singleton 1) := by decide

/-- Non-vacuity of extensionality: two syntactically-different set expressions
    that agree everywhere are forced equal.  `inter s s = s` (intersecting a set
    with itself is a no-op), so `seteq_ext` is a real constraint, not vacuous. -/
theorem ext_nonvacuous (s : St) : inter s s = s := by
  apply seteq_ext
  intro x
  simp [mem, inter]

/-- A second non-vacuity witness: `union s emptyS = s` (the empty set is a unit
    for union), again forced by extensionality from a pointwise membership law. -/
theorem union_empty (s : St) : union s emptyS = s := by
  apply seteq_ext
  intro x
  simp [mem, union, emptyS]

end AySoundness.SetThy