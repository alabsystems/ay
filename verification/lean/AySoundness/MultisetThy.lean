/-
  Soundness of ay's multiset / bag theory (QF_MULTISET): the count-function
  model + the multiset axioms (cf. the theory-validator family in
  the development design notes).

  ay reasons about finite multisets (bags) of integers with the usual
  operations (`empty`, `singleton`, bag `union` = count-addition, `inter` =
  count-min, `diff` = truncated count-subtraction, sub-multiset, and
  multiset-equality) and emits a conflict whenever a literal multiset constraint
  contradicts the multiset axioms.

  Unlike a *set*, a bag tracks the MULTIPLICITY of each element, so the right
  model is the *count function*: a multiset over `Int` is a map `Int → Nat`
  giving the count (multiplicity) of each element.  `union` adds counts (so
  `{a} ⊎ {a}` contains `a` twice, NOT once — this is the difference from sets),
  `inter` takes the pointwise minimum, `diff` is truncated `Nat` subtraction,
  sub-multiset is the pointwise `≤`, and multiset-equality is pointwise equality
  of counts.

  A multiset theory conflict that uses ONLY instances of these axioms (plus
  congruence / equality / linear-arithmetic reasoning over the counts) is sound
  iff the axioms hold in the intended model.  We fix the standard count-function
  model and prove all the multiset axioms hold there
  (`multiset_axioms_sound`).  Hence any propositionally / arithmetically derived
  conflict built from these axiom instances refutes a genuinely unsatisfiable
  constraint set: the model cannot exist, because the axioms are valid.

  We prove the soundness PRINCIPLE (`multiset_axioms_sound`): in EVERY
  count-function model, the count laws + the commutative-monoid laws for bag
  union + sub-multiset reflexivity + extensionality hold simultaneously.  The
  per-problem grounding (which bag term is which) is the solver's congruence
  closure; the theory content is exactly these count facts.  We then refute two
  concrete conflicts (`union_singleton_count_conflict`, the count-`2` fact that
  distinguishes bags from sets, and `sub_count_conflict`, a sub-multiset/count
  contradiction), mirroring the `farkas_sound` (principle) + concrete-decidable
  example split used by `ArrayThy` / `SetThy`.

  Pure Lean 4 core (no Mathlib).  The model definitions mirror the standard
  count-function semantics used by ay's QF_MULTISET decision procedure.
-/
namespace AySoundness.MultisetThy

/-! ## The standard count-function model.

A multiset of integers is its count function `Int → Nat`: `m x` is the
multiplicity of `x` in `m`.  This is the canonical model the QF_MULTISET
decision procedure is proved sound against.  Crucially, multiplicities can
exceed `1`, which is what distinguishes a bag from a set. -/

/-- A multiset (bag) of integers, as a count function. -/
abbrev MS := Int → Nat

/-- `count x m` : the multiplicity of `x` in the multiset `m`. -/
def count (x : Int) (m : MS) : Nat := m x

/-- The empty multiset: every element has count `0`. -/
def emptyMS : MS := fun _ => 0

/-- The singleton bag `{a}`: `a` has count `1`, everything else `0`. -/
def singletonMS (a : Int) : MS := fun x => if x = a then 1 else 0

/-- Bag union: counts ADD (so `{a} ⊎ {a}` has `a` with count `2`). -/
def unionMS (m n : MS) : MS := fun x => m x + n x

/-- Bag intersection: counts take the pointwise minimum. -/
def interMS (m n : MS) : MS := fun x => Nat.min (m x) (n x)

/-- Bag difference `m ∖ n`: truncated (`Nat`) count subtraction. -/
def diffMS (m n : MS) : MS := fun x => m x - n x

/-- `subMS m n` : `m` is a sub-multiset of `n` — pointwise `≤` on counts. -/
def subMS (m n : MS) : Prop := ∀ x, count x m ≤ count x n

/-- `eqMS m n` : `m` and `n` have the same count at every element (extensional
    multiset equality). -/
def eqMS (m n : MS) : Prop := ∀ x, count x m = count x n

/-! ## The multiset count axioms, valid in the count-function model. -/

/-- **Empty count.**  Every element has count `0` in `∅`. -/
theorem count_empty (x : Int) : count x emptyMS = 0 := by
  simp [count, emptyMS]

/-- **Singleton count.**  `count x {a} = 1` iff `x = a`, else `0`. -/
theorem count_singleton (x a : Int) :
    count x (singletonMS a) = if x = a then 1 else 0 := by
  simp [count, singletonMS]

/-- **Singleton self count.**  `count a {a} = 1`. -/
theorem count_singleton_self (a : Int) : count a (singletonMS a) = 1 := by
  simp [count, singletonMS]

/-- **Union count = addition.**  `count x (m ⊎ n) = count x m + count x n`. -/
theorem count_union (x : Int) (m n : MS) :
    count x (unionMS m n) = count x m + count x n := by
  simp [count, unionMS]

/-- **Intersection count = min.**  `count x (m ∩ n) = min (count x m) (count x n)`. -/
theorem count_inter (x : Int) (m n : MS) :
    count x (interMS m n) = Nat.min (count x m) (count x n) := by
  simp [count, interMS]

/-- **Difference count = truncated subtraction.**
    `count x (m ∖ n) = count x m - count x n` (`Nat` subtraction). -/
theorem count_diff (x : Int) (m n : MS) :
    count x (diffMS m n) = count x m - count x n := by
  simp [count, diffMS]

/-! ## Bag union is a commutative monoid with `emptyMS` as unit. -/

/-- **Union is commutative.** -/
theorem union_comm (m n : MS) : unionMS m n = unionMS n m := by
  funext x
  simp [unionMS]
  omega

/-- **Union is associative.** -/
theorem union_assoc (m n p : MS) :
    unionMS (unionMS m n) p = unionMS m (unionMS n p) := by
  funext x
  simp [unionMS]
  omega

/-- **Empty is a left unit for union.** -/
theorem union_empty_left (m : MS) : unionMS emptyMS m = m := by
  funext x
  simp [unionMS, emptyMS]

/-- **Empty is a right unit for union.** -/
theorem union_empty_right (m : MS) : unionMS m emptyMS = m := by
  funext x
  simp [unionMS, emptyMS]

/-! ## Sub-multiset and extensionality. -/

/-- **Sub-multiset is reflexive.**  Every bag is a sub-multiset of itself. -/
theorem sub_refl (m : MS) : subMS m m := by
  intro x
  exact Nat.le_refl (count x m)

/-- **Sub-multiset definition.**  `subMS m n` unfolds to the pointwise count
    inequality — the law ay's sub-multiset reasoning relies on. -/
theorem sub_def (m n : MS) : subMS m n ↔ ∀ x, count x m ≤ count x n := Iff.rfl

/-- **Extensionality.**  Two multisets with equal counts everywhere are the
    *same* function.  This is what licenses ay to treat multiset-equality as full
    congruence. -/
theorem eqMS_ext (m n : MS) (h : eqMS m n) : m = n := by
  funext x
  have := h x
  simpa [count] using this

/-- Converse: equal multisets have equal counts.  Together with `eqMS_ext` this
    is the full multiset-equality characterization `eqMS m n ↔ m = n`. -/
theorem eqMS_iff (m n : MS) : eqMS m n ↔ m = n := by
  constructor
  · exact eqMS_ext m n
  · intro h x; rw [h]

/-! ## The soundness principle.

`multiset_axioms_sound` packages the count laws + the commutative-monoid laws +
sub-multiset reflexivity + extensionality as a single validity statement: for
the count-function `count`/constructors/ops, ALL the laws hold for every bag and
element.  This is the theory content the QF_MULTISET validator relies on, so any
conflict built solely from these axiom instances is sound. -/

/-- **Multiset theory soundness.**  In the standard count-function model the
    multiset axioms (empty / singleton / union / inter / diff count laws, bag
    union as a commutative monoid with `emptyMS` as unit, sub-multiset
    reflexivity, and extensionality) hold simultaneously.  A conflict that uses
    only these axiom instances therefore refutes a genuinely unsatisfiable
    constraint set. -/
theorem multiset_axioms_sound :
    (∀ (x : Int), count x emptyMS = 0) ∧
    (∀ (x a : Int), count x (singletonMS a) = if x = a then 1 else 0) ∧
    (∀ (x : Int) (m n : MS), count x (unionMS m n) = count x m + count x n) ∧
    (∀ (x : Int) (m n : MS), count x (interMS m n) = Nat.min (count x m) (count x n)) ∧
    (∀ (x : Int) (m n : MS), count x (diffMS m n) = count x m - count x n) ∧
    (∀ (m n : MS), unionMS m n = unionMS n m) ∧
    (∀ (m n p : MS), unionMS (unionMS m n) p = unionMS m (unionMS n p)) ∧
    (∀ (m : MS), unionMS emptyMS m = m) ∧
    (∀ (m : MS), unionMS m emptyMS = m) ∧
    (∀ (m : MS), subMS m m) ∧
    (∀ (m n : MS), eqMS m n → m = n) :=
  ⟨count_empty, count_singleton, count_union, count_inter, count_diff,
   union_comm, union_assoc, union_empty_left, union_empty_right,
   sub_refl, eqMS_ext⟩

/-! ## Concrete conflict refutations (kernel-checked, NON-vacuous).

These instantiate at concrete integer elements and refute real QF_MULTISET
conflicts.  The first is the headline bag-vs-set distinction: `{a} ⊎ {a}` has
`a` with count `2`, not `1`. -/

/-- **The bag-vs-set count fact.**  `count a ({a} ⊎ {a}) = 2`.  This is THE
    multiplicity law that distinguishes a multiset from a set: in a set the
    union would still have `a` once.  Stated with `a = 5` it is kernel-checkable
    by `decide`; here we prove it for an arbitrary `a` via the count laws. -/
theorem union_singleton_self_count (a : Int) :
    count a (unionMS (singletonMS a) (singletonMS a)) = 2 := by
  rw [count_union, count_singleton_self]

/-- **Conflict 1.**  It is impossible that `count a ({a} ⊎ {a}) ≠ 2`; the bag
    union of two copies of `{a}` genuinely contains `a` twice.  Refutes ay's
    reported conflict input. -/
theorem union_singleton_count_conflict (a : Int) :
    ¬ (count a (unionMS (singletonMS a) (singletonMS a)) ≠ 2) := by
  intro h
  exact h (union_singleton_self_count a)

/-- The same fact as a fully concrete, kernel-checked witness at `a = 5`:
    `count 5 ({5} ⊎ {5}) = 2`.  Mirrors the `decide`-example split. -/
theorem union_singleton_count_witness :
    count 5 (unionMS (singletonMS 5) (singletonMS 5)) = 2 := by decide

/-- **Conflict 2** (sub-multiset / count contradiction).  If `m` is a
    sub-multiset of `n`, then `count x m ≤ count x n` at every `x`.  So the
    conflict input "`subMS m n` together with `count x m > count x n`" is
    unsatisfiable: `subMS` directly forbids it. -/
theorem sub_count_conflict (m n : MS) (x : Int)
    (hsub : subMS m n) (hgt : count x m > count x n) : False := by
  have hle : count x m ≤ count x n := hsub x
  omega

/-- A fully concrete instance of the sub-multiset conflict, kernel-checked.
    `{0}` is a sub-multiset of `{0} ⊎ {0}` (count `1 ≤ 2` at `0`), so any claim
    that `count 0 {0} > count 0 ({0} ⊎ {0})` is refuted: `1 > 2` is false. -/
theorem sub_count_witness :
    subMS (singletonMS 0) (unionMS (singletonMS 0) (singletonMS 0)) ∧
    count 0 (singletonMS 0) = 1 ∧
    count 0 (unionMS (singletonMS 0) (singletonMS 0)) = 2 := by
  refine ⟨?_, by decide, by decide⟩
  intro x
  simp only [count, singletonMS, unionMS]
  by_cases hx : x = 0
  · simp [hx]
  · simp [hx]

/-! ## Non-vacuity witnesses for the structural laws.

These show the commutative-monoid and extensionality laws are real constraints
on syntactically-distinct bag expressions, not vacuous identities. -/

/-- Non-vacuity of extensionality: `interMS m m = m` (intersecting a bag with
    itself is a no-op), forced by extensionality from the count `min` law. -/
theorem inter_self (m : MS) : interMS m m = m := by
  apply eqMS_ext
  intro x
  simp [count, interMS]

/-- A second non-vacuity witness: `diffMS m m = emptyMS` (a bag minus itself is
    empty), forced by extensionality from the truncated-subtraction count law. -/
theorem diff_self (m : MS) : diffMS m m = emptyMS := by
  apply eqMS_ext
  intro x
  simp [count, diffMS, emptyMS]

/-- A non-vacuity witness for the bag/set distinction at the function level:
    `unionMS (singletonMS a) (singletonMS a) ≠ singletonMS a`, i.e. the bag
    union of two copies of `{a}` is NOT `{a}` — concretely at `a = 0`, because
    their counts at `0` differ (`2 ≠ 1`).  This shows bag union really tracks
    multiplicity. -/
theorem union_singleton_ne_singleton :
    unionMS (singletonMS 0) (singletonMS 0) ≠ singletonMS 0 := by
  intro h
  have hc : count 0 (unionMS (singletonMS 0) (singletonMS 0))
            = count 0 (singletonMS 0) := by rw [h]
  rw [union_singleton_self_count, count_singleton_self] at hc
  exact absurd hc (by decide)

end AySoundness.MultisetThy
