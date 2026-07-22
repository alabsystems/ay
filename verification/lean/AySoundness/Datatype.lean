/-
  Soundness of ay's algebraic-datatype theory axioms (constructor injectivity,
  constructor distinctness, and acyclicity), the development design notes

  When ay solves a problem over an SMT datatype it treats the constructors as
  free term builders that satisfy three families of axioms, and it emits a
  conflict whenever a literal set contradicts them:

    * INJECTIVITY    `C(a₁…aₙ) = C(b₁…bₙ) → aᵢ = bᵢ`   (selectors are inverses);
    * DISTINCTNESS   `C(…) ≠ D(…)`  for distinct constructors `C ≠ D`;
    * ACYCLICITY     a term is never equal to a proper subterm of itself
                     (e.g. `t ≠ node t r`) — the term order is well-founded.

  A conflict that uses these axioms is sound exactly when the axioms hold in the
  intended (initial / free term) model. Lean's `inductive` type IS that initial
  model: its constructors are injective and disjoint by construction, and its
  terms are well-founded. So we discharge each axiom against a concrete `Tree`
  datatype and obtain kernel-checked soundness witnesses, mirroring the
  `farkas_sound` (principle) + concrete-`Example` (decidable instance) split.

  Pure Lean 4 core (no Mathlib).
-/
namespace AySoundness.Datatype

/-- A concrete two-constructor datatype: the standard binary tree.  `leaf` is a
    nullary constructor, `node` is binary — exactly the shape ay encodes for a
    user datatype `data Tree = leaf | node Tree Tree`. -/
inductive Tree where
  | leaf : Tree
  | node : Tree → Tree → Tree
  deriving DecidableEq

namespace Tree

/-! ## Axiom 1 — constructor injectivity.

    For ay this is the soundness of the selector axioms: from `node a b = node c d`
    the solver may derive `a = c` and `b = d`.  In the free term model this is the
    injectivity of the constructor, which Lean derives as `node.injEq`. -/

/-- **Injectivity of `node`.**  If two `node` terms are equal, their corresponding
    children are equal — the soundness of ay's selector/destructor reasoning. -/
theorem node_inj {a b c d : Tree} (h : node a b = node c d) : a = c ∧ b = d := by
  injection h with hl hr
  exact ⟨hl, hr⟩

/-- The converse direction, for completeness of the characterization: equal
    children give equal terms (constructors are congruent). -/
theorem node_congr {a b c d : Tree} (h : a = c ∧ b = d) : node a b = node c d := by
  obtain ⟨hl, hr⟩ := h; subst hl; subst hr; rfl

/-- Combined: `node a b = node c d ↔ a = c ∧ b = d` — the full selector
    characterization ay relies on. -/
theorem node_eq_iff {a b c d : Tree} : node a b = node c d ↔ a = c ∧ b = d :=
  ⟨node_inj, node_congr⟩

/-! ## Axiom 2 — constructor distinctness.

    Distinct constructors build distinct terms; ay emits a conflict from
    `leaf = node …`.  This is `Tree.noConfusion` in the free model. -/

/-- **Distinctness `leaf ≠ node`.**  A `leaf` term is never a `node` term — the
    soundness of ay's tester/`is-C` disjointness reasoning. -/
theorem leaf_ne_node {a b : Tree} : leaf ≠ node a b := by
  intro h; injection h

/-- Symmetric form. -/
theorem node_ne_leaf {a b : Tree} : node a b ≠ leaf := fun h => leaf_ne_node h.symm

/-! ## Axiom 3 — acyclicity.

    A datatype term is never equal to a proper subterm of itself; the subterm
    relation is well-founded, so ay's occurs-check conflict (`t = node t r`) is
    sound.  We prove it via a structural size measure (`depth`), which strictly
    decreases into children. -/

/-- Structural depth: the length of the longest root-to-leaf path. -/
def depth : Tree → Nat
  | leaf => 0
  | node l r => 1 + Nat.max (depth l) (depth r)

/-- `depth` strictly increases from a child to its parent `node` — the key
    well-foundedness fact behind the occurs check. -/
theorem depth_node_left (l r : Tree) : depth l < depth (node l r) := by
  have hnode : depth (node l r) = 1 + Nat.max (depth l) (depth r) := rfl
  have h : depth l ≤ Nat.max (depth l) (depth r) := Nat.le_max_left _ _
  omega

theorem depth_node_right (l r : Tree) : depth r < depth (node l r) := by
  have hnode : depth (node l r) = 1 + Nat.max (depth l) (depth r) := rfl
  have h : depth r ≤ Nat.max (depth l) (depth r) := Nat.le_max_right _ _
  omega

/-- **Acyclicity (left occurrence).**  A tree is never equal to a `node` having
    itself as the left child: `t ≠ node t r`.  This is the soundness of ay's
    acyclicity / occurs-check conflict. -/
theorem acyclic_l (t r : Tree) : t ≠ node t r := by
  intro h
  -- equal terms have equal depth, contradicting the strict decrease.
  have hlt : depth t < depth (node t r) := depth_node_left t r
  have heq : depth t = depth (node t r) := congrArg depth h
  omega

/-- **Acyclicity (right occurrence).**  Symmetric: `t ≠ node l t`. -/
theorem acyclic_r (t l : Tree) : t ≠ node l t := by
  intro h
  have hlt : depth t < depth (node l t) := depth_node_right l t
  have heq : depth t = depth (node l t) := congrArg depth h
  omega

end Tree

/-! ## SMT conflict abstraction.

    ay represents the result of a datatype decision as: a set of equality /
    disequality literals over constructor terms is UNSAT.  We give a small
    self-contained conflict principle and discharge it from the axioms above, so
    a kernel-checked `False` witnesses the soundness of the emitted conflict —
    mirroring the `farkas_sound` principle in `Farkas.lean`. -/

open Tree

/-- **Injectivity conflict (left selector).**  The literal set
    `{ node a b = node c d, a ≠ c }` is unsatisfiable: ay's left-selector
    conflict is sound. -/
theorem inj_conflict_unsat (a b c d : Tree) :
    ¬ (node a b = node c d ∧ a ≠ c) := by
  rintro ⟨heq, hne⟩
  exact hne (node_inj heq).1

/-- **Injectivity conflict (right selector).**  The literal set
    `{ node a b = node c d, b ≠ d }` is unsatisfiable. -/
theorem inj_conflict_unsat_snd (a b c d : Tree) :
    ¬ (node a b = node c d ∧ b ≠ d) := by
  rintro ⟨heq, hne⟩
  exact hne (node_inj heq).2

/-- **Distinctness conflict.**  The literal `leaf = node a b` is unsatisfiable. -/
theorem dist_conflict_unsat (a b : Tree) : ¬ (leaf = node a b) :=
  fun h => leaf_ne_node h

/-- **Acyclicity conflict.**  The literal `t = node t r` is unsatisfiable — ay's
    occurs-check conflict is sound. -/
theorem acyclic_conflict_unsat (t r : Tree) : ¬ (t = node t r) :=
  fun h => acyclic_l t r h

/-! ## Concrete, kernel-checked, NON-vacuous examples.

    Each refutes a *real* conflict over concrete ground terms; the contradiction
    is discharged by pure-kernel `decide` on `DecidableEq Tree`. -/

/-- Concrete injectivity conflict: `node leaf (node leaf leaf) = node leaf leaf`
    is false (the right children differ), so the selector conflict fires. -/
theorem ex_inj_conflict :
    ¬ (node leaf (node leaf leaf) = node leaf leaf) := by decide

/-- And it follows from the general principle too (not just `decide`): here the
    left children agree (`a = c = leaf`) but the right children differ
    (`b = node leaf leaf`, `d = leaf`), so the right-selector conflict fires. -/
theorem ex_inj_via_principle :
    ¬ (node leaf (node leaf leaf) = node leaf leaf ∧ node leaf leaf ≠ leaf) :=
  inj_conflict_unsat_snd leaf (node leaf leaf) leaf leaf

/-- Concrete distinctness conflict: `leaf = node leaf leaf` is false. -/
theorem ex_dist_conflict : ¬ (leaf = node leaf leaf) := by decide

/-- The same via the principle. -/
theorem ex_dist_via_principle : ¬ (leaf = node leaf leaf) :=
  dist_conflict_unsat leaf leaf

/-- Concrete acyclicity conflict on a ground term: `node leaf leaf = node (node leaf leaf) leaf`
    is false; the left child equals the whole term, which acyclicity forbids. -/
theorem ex_acyclic_conflict :
    ¬ (node leaf leaf = node (node leaf leaf) leaf) := by decide

/-- The same via the acyclicity principle, instantiated at `t = node leaf leaf`,
    `r = leaf`: a term cannot be the left child of a `node` headed by itself. -/
theorem ex_acyclic_via_principle :
    ¬ (node leaf leaf = node (node leaf leaf) leaf) :=
  acyclic_conflict_unsat (node leaf leaf) leaf

end AySoundness.Datatype
