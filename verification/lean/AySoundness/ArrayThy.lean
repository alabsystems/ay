/-
  Soundness of the theory of arrays (QF_AX): read-over-write + extensionality
  (Tn of the development design notes; the array theory validator).

  ay's array theory reasons with the McCarthy axioms over `select`/`store`:

      (RoW-1)  select (store a i v) i = v
      (RoW-2)  i ≠ j → select (store a i v) j = select a j
      (Ext)    (∀ i, select a i = select b i) → a = b

  A theory conflict that uses ONLY instances of these axioms (plus congruence /
  equality reasoning) is sound iff the axioms hold in the intended model. We fix
  the *standard functional model* — arrays are total functions `Idx → Val`,
  `select` is application, `store` is functional update — and prove all three
  axioms hold there. Hence any propositionally-derived conflict built from these
  axiom instances refutes a genuinely unsatisfiable constraint set: the model
  cannot exist, because the axioms are valid (`array_axioms_sound`).

  We prove the soundness PRINCIPLE (`array_axioms_sound`): in EVERY functional
  model, the three axioms are simultaneously valid. The per-problem grounding
  (which array term is which) is the solver's congruence closure; the theory
  content is exactly these three facts. We also refute two concrete conflicts
  (`select_store_same_conflict`, `select_store_other_conflict`) by `decide`,
  mirroring the `farkas_sound` + `decide`/`omega` example split.

  Pure Lean 4 core (no Mathlib). The model definitions mirror the standard
  read-over-write semantics used by ay's array decision procedure.
-/
namespace AySoundness.ArrayThy

/-! ## The standard functional model.

We generalize over an arbitrary index type `Idx` (with decidable equality, as a
real array index sort has) and value type `Val`. An array is a total function;
`select` is application and `store` is the pointwise functional update. This is
the canonical model the QF_AX decision procedure is proved sound against. -/

variable {Idx : Type} {Val : Type} [DecidableEq Idx]

/-- An array over index `Idx` and value `Val`: a total function. -/
abbrev Arr (Idx Val : Type) := Idx → Val

/-- `select a i` reads index `i` of array `a`. -/
def sel (a : Arr Idx Val) (i : Idx) : Val := a i

/-- `store a i v` updates array `a` at index `i` to value `v`. -/
def upd (a : Arr Idx Val) (i : Idx) (v : Val) : Arr Idx Val :=
  fun j => if j = i then v else a j

/-! ## The three array axioms, valid in the functional model. -/

/-- **RoW-1** (read-over-write, same index): reading the just-written index
    returns the written value. -/
theorem sel_upd_same (a : Arr Idx Val) (i : Idx) (v : Val) :
    sel (upd a i v) i = v := by
  simp [sel, upd]

/-- **RoW-2** (read-over-write, other index): reading a different index returns
    the original array's value there. -/
theorem sel_upd_other (a : Arr Idx Val) (i j : Idx) (v : Val) (h : i ≠ j) :
    sel (upd a i v) j = sel a j := by
  simp [sel, upd]
  intro hji
  exact absurd hji.symm h

omit [DecidableEq Idx] in
/-- **Extensionality**: arrays equal at every index are equal. -/
theorem ext (a b : Arr Idx Val)
    (h : ∀ i, sel a i = sel b i) : a = b := by
  funext i
  have := h i
  simpa [sel] using this

/-! ## The soundness principle.

`array_axioms_sound` packages the three axioms as a single validity statement:
for the functional `sel`/`upd`, ALL three hold for every array, index and value.
This is the full theory content the QF_AX validator relies on, so any conflict
built solely from these axiom instances is sound. -/

/-- **Array theory soundness.** In the standard functional model, the three
    McCarthy array axioms hold simultaneously. A conflict that uses only these
    axiom instances therefore refutes a genuinely unsatisfiable constraint set. -/
theorem array_axioms_sound :
    (∀ (a : Arr Idx Val) (i : Idx) (v : Val), sel (upd a i v) i = v) ∧
    (∀ (a : Arr Idx Val) (i j : Idx) (v : Val), i ≠ j → sel (upd a i v) j = sel a j) ∧
    (∀ (a b : Arr Idx Val), (∀ i, sel a i = sel b i) → a = b) :=
  ⟨sel_upd_same, sel_upd_other, ext⟩

/-! ## Concrete conflict refutations (kernel-checked, non-vacuous).

We instantiate at `Idx = Val = Int` (a decidable, inhabited carrier so the
examples are non-trivial) and refute two real QF_AX conflicts by `decide`. -/

/-- **Conflict 1**: it is impossible for `select (store a i v) i ≠ v`.
    For a concrete witness, with `a = id`, `i = 3`, `v = 7`:
    `select (store id 3 7) 3 = 7`, so the conflict `… ≠ 7` is refuted. -/
theorem select_store_same_conflict :
    ¬ (sel (upd (fun (x : Int) => x) 3 7) 3 ≠ 7) := by
  decide

/-- The same fact, stated as the satisfied equality (the value the conflict
    falsely denies). Kernel-checked by `decide`. -/
theorem select_store_same_value :
    sel (upd (fun (x : Int) => x) 3 7) 3 = 7 := by
  decide

/-- **Conflict 2**: with distinct indices `3 ≠ 5`, `select (store a 3 7) 5` must
    equal `select a 5`. With `a = id` that value is `5`; the conflict
    `select (store id 3 7) 5 ≠ select id 5` is refuted. -/
theorem select_store_other_conflict :
    ¬ (sel (upd (fun (x : Int) => x) 3 7) 5 ≠ sel (fun (x : Int) => x) 5) := by
  decide

/-- The same fact stated positively: reading the untouched index `5` returns the
    original `select id 5 = 5`. Kernel-checked by `decide`. -/
theorem select_store_other_value :
    sel (upd (fun (x : Int) => x) 3 7) 5 = sel (fun (x : Int) => x) 5 := by
  decide

/-- A non-vacuity witness for extensionality: two syntactically-different array
    expressions that agree everywhere are forced equal. `upd a i (sel a i) = a`
    (storing the value already present is a no-op), so `ext` is a real
    constraint, not a vacuous one. -/
theorem ext_nonvacuous (a : Arr Idx Val) (i : Idx) :
    upd a i (sel a i) = a := by
  apply ext
  intro j
  by_cases h : j = i
  · subst h; simp [sel, upd]
  · simp [sel, upd, h]

end AySoundness.ArrayThy