/-
  Verified NONLINEAR-INTEGER product bridge.

  `omega` is a decision procedure for LINEAR integer arithmetic. Faced with a
  bilinear term such as `x * y` it *atomises* it: the product becomes an opaque
  fresh unknown with no connection whatsoever to `x` or `y`. Consequently
  `1 ≤ x ≤ 2 ∧ 1 ≤ y ≤ 2 ∧ x * y = 7` is NOT closed by `omega` alone — the
  atomised system is satisfiable.

  This module supplies the missing connection as LINEAR facts that `omega` can
  consume: the four corners of the McCormick envelope, the exact convex hull of a
  bilinear term over an interval box. Each corner is an instance of
  `Int.mul_nonneg` (Lean CORE — no Mathlib) applied to a product of two
  nonnegative slacks, expanded by pure `Int` ring rewrites.

  The four corners are exported SEPARATELY (not only as the bundled conjunction)
  because a query need not bound both factors on both sides: `sign_consistency`
  (`x > 0 ∧ y > 0 ∧ x * y < 0`) has LOWER bounds only, and only `mul_lb_ll` is
  derivable there. The emitter injects exactly the corners whose two bounds it
  actually found among the asserted atoms, so it never depends on a bound that
  the hypotheses do not carry.

  `#print axioms` ⊆ {propext, Quot.sound}; no `sorry`, no `native_decide`,
  no Mathlib.
-/
namespace AySoundness.NiaProduct

/-- **Lower-lower corner.** `a ≤ x` and `c ≤ y` give `0 ≤ (x - a) * (y - c)`,
    i.e. the LINEAR lower bound `a * y + c * x - a * c ≤ x * y`. -/
theorem mul_lb_ll {x y a c : Int} (hax : a ≤ x) (hcy : c ≤ y) :
    a * y + c * x - a * c ≤ x * y := by
  have n : 0 ≤ (x - a) * (y - c) := Int.mul_nonneg (by omega) (by omega)
  have e : (x - a) * (y - c) = x * y - x * c - (a * y - a * c) := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
  have c1 : x * c = c * x := Int.mul_comm x c
  omega

/-- **Upper-upper corner.** `x ≤ b` and `y ≤ d` give `0 ≤ (b - x) * (d - y)`,
    i.e. the LINEAR lower bound `b * y + d * x - b * d ≤ x * y`. -/
theorem mul_lb_uu {x y b d : Int} (hxb : x ≤ b) (hyd : y ≤ d) :
    b * y + d * x - b * d ≤ x * y := by
  have n : 0 ≤ (b - x) * (d - y) := Int.mul_nonneg (by omega) (by omega)
  have e : (b - x) * (d - y) = b * d - b * y - (x * d - x * y) := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
  have c1 : x * d = d * x := Int.mul_comm x d
  omega

/-- **Upper-lower corner.** `x ≤ b` and `c ≤ y` give `0 ≤ (b - x) * (y - c)`,
    i.e. the LINEAR upper bound `x * y ≤ b * y + c * x - b * c`. -/
theorem mul_ub_ul {x y b c : Int} (hxb : x ≤ b) (hcy : c ≤ y) :
    x * y ≤ b * y + c * x - b * c := by
  have n : 0 ≤ (b - x) * (y - c) := Int.mul_nonneg (by omega) (by omega)
  have e : (b - x) * (y - c) = b * y - b * c - (x * y - x * c) := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
  have c1 : x * c = c * x := Int.mul_comm x c
  omega

/-- **Lower-upper corner.** `a ≤ x` and `y ≤ d` give `0 ≤ (x - a) * (d - y)`,
    i.e. the LINEAR upper bound `x * y ≤ a * y + d * x - a * d`. -/
theorem mul_ub_lu {x y a d : Int} (hax : a ≤ x) (hyd : y ≤ d) :
    x * y ≤ a * y + d * x - a * d := by
  have n : 0 ≤ (x - a) * (d - y) := Int.mul_nonneg (by omega) (by omega)
  have e : (x - a) * (d - y) = x * d - x * y - (a * d - a * y) := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
  have c1 : x * d = d * x := Int.mul_comm x d
  omega

/-- **The full McCormick envelope** over the integers: under `a ≤ x ≤ b` and
    `c ≤ y ≤ d` the four corner products bound `x * y` LINEARLY. Bundled form of
    the four corner lemmas above. -/
theorem mccormick {x y a b c d : Int}
    (hax : a ≤ x) (hxb : x ≤ b) (hcy : c ≤ y) (hyd : y ≤ d) :
    a * y + c * x - a * c ≤ x * y ∧
    b * y + d * x - b * d ≤ x * y ∧
    x * y ≤ b * y + c * x - b * c ∧
    x * y ≤ a * y + d * x - a * d :=
  ⟨mul_lb_ll hax hcy, mul_lb_uu hxb hyd, mul_ub_ul hxb hcy, mul_ub_lu hax hyd⟩

/-! ### Worked instances (the shapes the emitter reconstructs at runtime) -/

/-- `benchmarks/smt/QF_NIA/simple_product_unsat.smt2`: `1 ≤ x,y ≤ 2` bounds
    `x * y ≤ 4`, so `x * y = 7` is infeasible. Only the UPPER corner is needed. -/
theorem simple_product_unsat_abstract {x y : Int}
    (h1 : x ≥ 1) (h2 : x ≤ 2) (h3 : y ≥ 1) (h4 : y ≤ 2) : x * y ≠ 7 := by
  have h := mul_ub_ul (x := x) (y := y) (b := (2 : Int)) (c := (1 : Int)) h2 (by omega)
  omega

/-- `benchmarks/smt/QF_NIA/sign_consistency.smt2`: with LOWER bounds only,
    `x, y ≥ 1` gives `x * y ≥ x + y - 1 ≥ 1`, refuting `x * y < 0`. -/
theorem sign_consistency_abstract {x y : Int} (hx : x > 0) (hy : y > 0) :
    ¬ (x * y < 0) := by
  have h := mul_lb_ll (x := x) (y := y) (a := (1 : Int)) (c := (1 : Int))
    (by omega) (by omega)
  omega

/-- The COMMUTED-DUPLICATE shape (`x * y + y * x = 14` under `1 ≤ x,y ≤ 2`).
    `omega` atomises `x * y` and `y * x` as DIFFERENT unknowns, so the emitter
    must render both occurrences with one canonical factor order; this is the
    canonicalised goal it must produce. -/
theorem commuted_duplicate_abstract {x y : Int}
    (h1 : x ≥ 1) (h2 : x ≤ 2) (h3 : y ≥ 1) (h4 : y ≤ 2) :
    x * y + x * y ≠ 14 := by
  have h := mul_ub_ul (x := x) (y := y) (b := (2 : Int)) (c := (1 : Int)) h2 (by omega)
  omega

/-- A MIXED-SIGN box, where a single corner is not enough: `x, y ∈ [-2, 3]`
    bounds `x * y ≤ 6`, refuting `x * y = 20`. -/
theorem mixed_bounds_abstract {x y : Int} (h1 : -2 ≤ x) (h2 : x ≤ 3)
    (h3 : -2 ≤ y) (h4 : y ≤ 3) : x * y ≠ 20 := by
  have h := mccormick (a := -2) (b := 3) (c := -2) (d := 3) h1 h2 h3 h4
  omega

/-- A SQUARE (`y := x`): `-5 ≤ x ≤ 5` bounds `x * x ≤ 25`, refuting `x * x = 30`.
    The corner lemmas specialise to `y := x` with no extra machinery. -/
theorem square_bound_abstract {x : Int} (h1 : -5 ≤ x) (h2 : x ≤ 5) :
    x * x ≠ 30 := by
  have h := mccormick (x := x) (y := x) (a := -5) (b := 5) (c := -5) (d := 5)
    h1 h2 h1 h2
  omega

end AySoundness.NiaProduct
