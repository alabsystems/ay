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

/-! ## Generic acyclicity via the auto-derived `sizeOf` (theory-agnostic).

    The `depth`-based `acyclic_l`/`acyclic_r`/`acyclic_conflict_unsat` above are
    hard-specialised to `Tree` and its IMMEDIATE children.  ay's occurs-check,
    however, fires over ARBITRARY inductive datatypes and at ARBITRARY nesting
    depth — cons-lists (`x = h :: x`), depth-≥2 nesting (`x = a :: b :: x`),
    selector-mediated cycles (`v = tl v`), and any user datatype
    (`x = C(.., x, ..)`).  We discharge ALL of these uniformly with Lean's
    auto-derived structural `sizeOf`: every genuine constructor context `ctx`
    that contains `t` as a PROPER subterm strictly increases `sizeOf`, and equal
    terms have equal `sizeOf`, so `t = ctx t` is impossible.  No bespoke measure,
    no per-datatype boilerplate — the hypothesis `sizeOf t < sizeOf (ctx t)` is
    closed by `simp [C.sizeOf_spec]; omega` for the concrete `ctx` the emitter
    sees. -/

/-- **Generic acyclicity.**  If a unary context `ctx` strictly increases `sizeOf`
    at `t`, then `t ≠ ctx t`.  Every real datatype constructor application that
    contains `t` as a proper subterm satisfies the hypothesis, so this subsumes
    the `Tree`-specific `acyclic_l`/`acyclic_r` for ANY inductive `α`. -/
theorem acyclic_of_sizeOf_lt {α : Type u} [SizeOf α] {t : α} {ctx : α → α}
    (h : sizeOf t < sizeOf (ctx t)) : t ≠ ctx t := by
  intro heq
  have hz : sizeOf t = sizeOf (ctx t) := congrArg sizeOf heq
  omega

/-- **Generic acyclicity conflict** — the conflict-level corollary the firewall
    emitter grounds the occurs-check lemma in.  For the abstracted occurs-check
    atom `t = ctx t`, the literal set `{ t = ctx t }` is unsatisfiable in every
    model whenever `ctx` strictly increases `sizeOf` at `t`.  This is the generic
    analog of `acyclic_conflict_unsat`, usable through
    `AySoundness.firewall_combined_unsat` exactly as `dist_conflict_unsat` is used
    in `CombinedDatatype` (discharge the theory lemma's `hvalid`/`lemmas_valid`
    obligation `clauseSat _ [-k] = true` for the occurs-check atom `k` by this
    principle, since no model of the datatype satisfies `t = ctx t`). -/
theorem acyclic_conflict_generic {α : Type u} [SizeOf α] {t : α} {ctx : α → α}
    (h : sizeOf t < sizeOf (ctx t)) : ¬ (t = ctx t) :=
  fun heq => acyclic_of_sizeOf_lt h heq

/-! ### Coverage witnesses — the occurs-check shapes ay actually emits.

    Each closes the `sizeOf` hypothesis with `simp [C.sizeOf_spec]; omega`, the
    uniform recipe the emitter uses for a concrete constructor context `ctx`. -/

/-- Cons-list, immediate: `x ≠ h :: x`  (`ctx := (h :: ·)`). -/
example (h : Nat) (x : List Nat) : x ≠ h :: x :=
  acyclic_of_sizeOf_lt (ctx := (h :: ·))
    (by simp only [List.cons.sizeOf_spec]; omega)

/-- Cons-list, depth-≥2 nesting: `x ≠ a :: b :: x`  (`ctx := (a :: b :: ·)`). -/
example (a b : Nat) (x : List Nat) : x ≠ a :: b :: x :=
  acyclic_of_sizeOf_lt (ctx := (a :: b :: ·))
    (by simp only [List.cons.sizeOf_spec]; omega)

/-- Nested element type: `x ≠ ys :: x` over `List (List Nat)`. -/
example (x : List (List Nat)) (ys : List Nat) : x ≠ ys :: x :=
  acyclic_of_sizeOf_lt (ctx := (ys :: ·))
    (by simp only [List.cons.sizeOf_spec]; omega)

/-- ANY user inductive: a two-field record-like constructor. -/
inductive Wrap (β : Type) where
  | mk : β → Wrap β → Wrap β
  | nil : Wrap β

/-- `w ≠ .mk b w`  (`ctx := Wrap.mk b`) — arbitrary datatype occurs-check. -/
example (b : Nat) (w : Wrap Nat) : w ≠ Wrap.mk b w :=
  acyclic_of_sizeOf_lt (ctx := Wrap.mk b)
    (by simp only [Wrap.mk.sizeOf_spec]; omega)

/-- The `Tree` occurs-check, re-derived generically (no bespoke `depth`):
    `t ≠ node t r` via the auto-derived `sizeOf`, subsuming `acyclic_l`. -/
example (t r : Tree) : t ≠ node t r :=
  acyclic_of_sizeOf_lt (ctx := (node · r))
    (by simp only [Tree.node.sizeOf_spec]; omega)

/-- Selector-mediated occurs-check `v = tl v` also fits: model the selector's
    fixpoint as a constructor context.  `v ≠ hd v :: v` is the constraint the
    occurs check derives once `tl v = v` is oriented against `v = hd v :: tl v`. -/
example (v : List Nat) : v ≠ v.headD 0 :: v :=
  acyclic_of_sizeOf_lt (ctx := (v.headD 0 :: ·))
    (by simp only [List.cons.sizeOf_spec]; omega)

/-! ## Axiom 4 — tester / `is-C` mutual exclusion.

    ay's datatype solver reasons about the constructor TESTERS `((_ is C) x)`:
    every value is headed by exactly ONE constructor, so `((_ is C) x)` and
    `((_ is D) x)` are mutually exclusive for `C ≠ D`, and in particular
    `((_ is C) x) = true` together with `x = D(…)` (for `C ≠ D`) is a conflict.
    This is the ONE datatype reasoning primitive not covered by injectivity /
    distinctness / acyclicity, needed by the case-split firewall's tester branch
    (`benchmarks/…/qf_dt_acyclicity_casesplit_false_sat.smt2`): the disjunctive
    lemma clause `[-1, -4]` encodes `¬is-nd(x) ∨ ¬(lf = x)`.

    We model the tester as a `Bool`-valued match on `Tree` — exactly how ay
    lowers `((_ is node) ·)` — and prove that it cannot be `true` on a `leaf`. -/

/-- The `node` tester `((_ is node) ·)` as ay lowers it: `true` on `node`,
    `false` on `leaf`. -/
def isNode : Tree → Bool
  | node _ _ => true
  | leaf => false

/-- **Tester mutual-exclusion conflict.**  `((_ is node) x) = true` is
    incompatible with `x = leaf`: no value is simultaneously `node`-headed and a
    `leaf`.  This discharges the case-split firewall's tester disjunct `[-1,-4]`
    (`¬is-node(x) ∨ ¬(leaf = x)` holds in every model). -/
theorem tester_node_leaf_excl {x : Tree} (h1 : isNode x = true) (h2 : x = leaf) :
    False := by
  subst h2; simp [isNode] at h1

/-- Symmetric orientation (`leaf = x`), the form the emitter's abstracted atom
    `4 ↦ (leaf = x)` produces. -/
theorem tester_node_leaf_excl' {x : Tree} (h1 : isNode x = true) (h2 : leaf = x) :
    False := tester_node_leaf_excl h1 h2.symm

end AySoundness.Datatype
