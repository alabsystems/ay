import AySoundness.Lrat
/-
  Boolean-formula evaluator soundness — the SAT-direction firewall's evaluator.

  In ay's SAT firewall, `verify_model_strict` does NOT trust the solver's claim
  that a model satisfies a formula: it independently EVALUATES the formula under
  the candidate model `M` and accepts only when the evaluation returns `true`.
  This file proves that this runtime evaluation is FAITHFUL to the propositional
  semantics:

      eval_sound : eval M f = true ↔ Holds M f

  i.e. the computable check `eval M f = true` is EXACTLY the proposition "`M`
  satisfies `f`". Hence a passing evaluation is a real satisfiability witness
  (`sat_witness`), and a formula whose negation always evaluates true is really
  unsatisfiable. We also tie a CNF-shaped `Form` to the LRAT-level `Sat` /
  `clauseSat` from `AySoundness.Lrat`, so the firewall's evaluator connects to
  the same `Sat` predicate the UNSAT-direction checker refutes.

  Pure Lean 4 core (no Mathlib). Every theorem here is kernel-checked and (per
  `#print axioms`) depends on at most `propext` — no `sorryAx`, no
  `native_decide`; the concrete examples reduce by `decide` in the kernel.
-/
namespace AySoundness

/-! ## Formula AST over propositional atoms (atoms indexed by `Nat`). -/

inductive Form where
  | atom (n : Nat) : Form
  | tt : Form
  | ff : Form
  | neg (a : Form) : Form
  | conj (a b : Form) : Form
  | disj (a b : Form) : Form
deriving DecidableEq, Repr

/-! ## The computable evaluator (what `verify_model_strict` runs). -/

def eval (M : Nat → Bool) : Form → Bool
  | .atom n => M n
  | .tt => true
  | .ff => false
  | .neg a => !(eval M a)
  | .conj a b => eval M a && eval M b
  | .disj a b => eval M a || eval M b

/-! ## The semantics: `Holds M f` is the propositional meaning of `f` under `M`. -/

def Holds (M : Nat → Bool) : Form → Prop
  | .atom n => M n = true
  | .tt => True
  | .ff => False
  | .neg a => ¬ Holds M a
  | .conj a b => Holds M a ∧ Holds M b
  | .disj a b => Holds M a ∨ Holds M b

/-! ## MAIN THEOREM: the evaluator is faithful to the semantics. -/

/-- `eval M f = true` is EXACTLY `Holds M f`. Proved by structural induction on
    `f`, both directions simultaneously via the `↔`. -/
theorem eval_sound (M : Nat → Bool) (f : Form) : eval M f = true ↔ Holds M f := by
  induction f with
  | atom n => simp [eval, Holds]
  | tt => simp [eval, Holds]
  | ff => simp [eval, Holds]
  | neg a ih =>
    simp only [eval, Holds]
    -- `!(eval M a) = true ↔ ¬ Holds M a`
    constructor
    · intro h hH
      have : eval M a = true := (ih).mpr hH
      rw [this] at h; simp at h
    · intro h
      cases hc : eval M a with
      | false => simp
      | true => exact absurd (ih.mp hc) h
  | conj a b iha ihb =>
    simp only [eval, Holds]
    rw [Bool.and_eq_true, iha, ihb]
  | disj a b iha ihb =>
    simp only [eval, Holds]
    rw [Bool.or_eq_true, iha, ihb]

/-! ## A clean negation corollary (the firewall's "this assignment fails" form). -/

/-- `eval M f = false` is EXACTLY `¬ Holds M f`. -/
theorem eval_false_iff (M : Nat → Bool) (f : Form) : eval M f = false ↔ ¬ Holds M f := by
  rw [← eval_sound M f]
  cases h : eval M f with
  | false => simp
  | true => simp

/-! ## SAT firewall corollary: a passing evaluation is a real model. -/

/-- If the evaluator accepts `M` on `f`, then `f` is satisfiable, witnessed by
    the very assignment `M` the firewall evaluated. This is the soundness of
    `verify_model_strict`: it never reports SAT without an actual model. -/
theorem sat_witness (M : Nat → Bool) (f : Form) (h : eval M f = true) :
    ∃ M', Holds M' f :=
  ⟨M, (eval_sound M f).mp h⟩

/-- Satisfiability of a formula (some assignment makes it hold). -/
def FormSat (f : Form) : Prop := ∃ M, Holds M f
/-- Unsatisfiability of a formula. -/
def FormUnsat (f : Form) : Prop := ¬ ∃ M, Holds M f

theorem sat_of_eval {M : Nat → Bool} {f : Form} (h : eval M f = true) : FormSat f :=
  sat_witness M f h

/-- An UNSAT firewall: if EVERY assignment makes `eval` reject `f`, then `f` is
    genuinely unsatisfiable. (Faithfulness in the refuting direction.) -/
theorem unsat_of_eval_all_false (f : Form) (h : ∀ M, eval M f = false) : FormUnsat f := by
  rintro ⟨M, hH⟩
  exact (eval_false_iff M f).mp (h M) hH

/-! ## Tie to the LRAT-level `Sat` / `clauseSat` used by the firewall.

A propositional literal `l : Int` (DIMACS-style: positive var, negative ¬var)
becomes a `Form`; a clause becomes a `disj`-tree; a CNF becomes a `conj`-tree.
We prove the `Form` semantics agree with `AySoundness.clauseSat` / `Sat`, so the
evaluator's `Holds` is the same satisfaction relation the LRAT checker refutes. -/

/-- Encode one DIMACS literal as a `Form` over atom `|l|`. -/
def litForm (l : Int) : Form :=
  if l > 0 then .atom l.toNat else .neg (.atom (-l).toNat)

/-- Encode a clause (disjunction of literals) as a `Form`; empty clause = `ff`. -/
def clauseForm : Clause → Form
  | [] => .ff
  | l :: rest => .disj (litForm l) (clauseForm rest)

/-- Encode a CNF (conjunction of clauses) as a `Form`; empty CNF = `tt`. -/
def cnfForm : List Clause → Form
  | [] => .tt
  | c :: rest => .conj (clauseForm c) (cnfForm rest)

/-- A single literal's `Form` evaluates exactly as `litSat`. -/
theorem eval_litForm (M : Nat → Bool) (l : Int) : eval M (litForm l) = litSat M l := by
  unfold litForm litSat
  by_cases h : l > 0 <;> simp [eval, h]

/-- A clause's `Form` evaluates exactly as `clauseSat`. -/
theorem eval_clauseForm (M : Nat → Bool) (c : Clause) :
    eval M (clauseForm c) = clauseSat M c := by
  induction c with
  | nil => simp [clauseForm, clauseSat, eval]
  | cons l rest ih =>
    simp only [clauseForm, eval, eval_litForm, ih, clauseSat, List.any_cons]

/-- The CNF `Form` HOLDS under `M` iff `M` is a `Sat` model of the clause list. -/
theorem holds_cnfForm_iff_Sat (M : Nat → Bool) (cs : List Clause) :
    Holds M (cnfForm cs) ↔ Sat M cs := by
  induction cs with
  | nil =>
    show Holds M Form.tt ↔ Sat M []
    simp only [Holds]
    constructor
    · intro _ c' hc'; exact absurd hc' (by simp)
    · intro _; trivial
  | cons c rest ih =>
    show Holds M (.conj (clauseForm c) (cnfForm rest)) ↔ Sat M (c :: rest)
    simp only [Holds]
    rw [ih]
    constructor
    · rintro ⟨hc, hrest⟩ c' hc'
      rcases List.mem_cons.mp hc' with e | e
      · subst e
        have : eval M (clauseForm c') = true := (eval_sound M (clauseForm c')).mpr hc
        rw [eval_clauseForm] at this; exact this
      · exact hrest c' e
    · intro h
      refine ⟨?_, ?_⟩
      · have hc : clauseSat M c = true := h c (by simp)
        exact (eval_sound M (clauseForm c)).mp (by rw [eval_clauseForm]; exact hc)
      · intro c' hc'; exact h c' (by simp [hc'])

/-- BRIDGE: the evaluator accepts a CNF `Form` under `M` iff `M` is an LRAT-level
    `Sat` model of the corresponding clause list. So the firewall's evaluator and
    the LRAT checker speak about the SAME satisfaction relation. -/
theorem eval_cnfForm_iff_Sat (M : Nat → Bool) (cs : List Clause) :
    eval M (cnfForm cs) = true ↔ Sat M cs := by
  rw [eval_sound]; exact holds_cnfForm_iff_Sat M cs

/-! ## CONCRETE kernel-checked examples (exercise BOTH directions). -/

/-- `f₀ = atom 0 ∧ (¬ atom 1 ∨ atom 0)`; model `M₀` sets atom 0 true, atom 1 false. -/
def M₀ : Nat → Bool := fun n => n == 0
def f₀ : Form := .conj (.atom 0) (.disj (.neg (.atom 1)) (.atom 0))

/-- Forward direction, kernel-checked: the evaluator accepts. -/
example : eval M₀ f₀ = true := by decide

/-- Backward direction, via the iff: a passing eval is a real `Holds`. -/
theorem f₀_holds : Holds M₀ f₀ := (eval_sound M₀ f₀).mp (by decide)

/-- And therefore `f₀` is satisfiable, witnessed by `M₀`. -/
theorem f₀_sat : FormSat f₀ := ⟨M₀, f₀_holds⟩

/-- Concrete UNSAT formula `g = atom 0 ∧ ¬ atom 0`: no assignment can satisfy it.
    Proved DIRECTLY from the semantics (not via the evaluator), so it certifies
    the `Holds` semantics is itself non-vacuous / contradiction-respecting. -/
def g : Form := .conj (.atom 0) (.neg (.atom 0))

theorem g_unsat : FormUnsat g := by
  rintro ⟨M, hpos, hneg⟩
  exact hneg hpos

/-- The same UNSAT fact obtained through the evaluator firewall: for EVERY model,
    `eval M g = false`, hence `FormUnsat g`. Connects the runtime check to the
    semantic impossibility. -/
theorem g_unsat_via_eval : FormUnsat g :=
  unsat_of_eval_all_false g (by
    intro M
    cases h : M 0 <;> simp [eval, g, h])

/-- LRAT bridge example: the CNF `[[1], [-1]]` (i.e. `x ∧ ¬x`) — its `Form`
    encoding is unsatisfiable, and via `eval_cnfForm_iff_Sat` this is the same as
    no `Sat` model existing (the fact the LRAT side refutes in `Example.lean`). -/
def triv_cnf : List Clause := [[1], [-1]]

theorem triv_cnf_no_sat : ¬ ∃ M, Sat M triv_cnf := by
  rintro ⟨M, hSat⟩
  have h1 : clauseSat M [1] = true := hSat [1] (by simp [triv_cnf])
  have h2 : clauseSat M [(-1 : Int)] = true := hSat [-1] (by simp [triv_cnf])
  simp [clauseSat, litSat] at h1 h2
  rw [h1] at h2; simp at h2

/-- And the evaluator agrees: no model makes the encoded CNF hold. -/
theorem triv_cnf_form_unsat : FormUnsat (cnfForm triv_cnf) := by
  rintro ⟨M, hH⟩
  exact triv_cnf_no_sat ⟨M, (holds_cnfForm_iff_Sat M triv_cnf).mp hH⟩

end AySoundness