//! The Trust two-language surface for the proved core.
//!
//! This module is compiled ONLY by `compiler_consumer` (the `trust-surface` cargo
//! feature is never enabled by a stock `cargo build`, and `#[cfg(feature)]`
//! on a `mod` declaration means stock rustc never even reads the file).
//!
//! It contains two things:
//!
//! 1. A `clean { ... }` **parser island** holding the entire proved kernel:
//!    the semantics (`Lit`, `Term`, `Constraint`, `litVal`, `evalTerms`,
//!    `Holds`, `HoldsAll`, `Entails`, `Unsat`) and every rule-soundness
//!    theorem, plus the machine-width `capCoeff` images the citations below
//!    name. `compiler_consumer` kernel-checks every declaration in it at compile time
//!    and reports the count; `scripts/verify-proofs.sh` gates on that count
//!    against the pin file, so it is deliberately not repeated here.
//!
//! 2. Rust functions whose `ensures` clauses are **discharged `by`** theorems
//!    from that island. Those are the places where the program and the proof
//!    are the same object.
//!
//! ## Why the island body is comment-free ASCII
//!
//! A `clean { ... }` island is delimited by *Rust token trees*, so its bytes
//! must lex as Rust tokens: no `->` written as `\u{2192}`, no backticks, no
//! em dashes, and no Lean block comments containing braces. The canonical,
//! fully commented source is `clean/veripb_kernel.lean`; the island body here
//! is that file with comments stripped and `\u{2192}`/`\u{2200}` rewritten to
//! `->`/`forall`. `tests/island_sync.rs` fails if the two ever drift.
//!
//! ## Verify it
//!
//! ```text
//! clean check clean/veripb_kernel.lean
//! compiler_consumer --edition 2021 --crate-type lib src/trust_surface.rs
//! ```

clean {
set_option autoImplicit false

namespace VeriPbCore

structure Lit where
  var : Nat
  negated : Bool

def litVal (a : Nat -> Bool) (l : Lit) : Bool :=
  match l.negated with
  | true  => Bool.not (a l.var)
  | false => a l.var

def negLit (l : Lit) : Lit := { var := l.var, negated := Bool.not l.negated }

structure Term where
  coeff : Int
  lit   : Lit

def evalTerms (a : Nat -> Bool) (ts : List Term) : Int :=
  match ts with
  | []      => 0
  | t :: rest =>
    match litVal a t.lit with
    | true  => t.coeff + evalTerms a rest
    | false => evalTerms a rest

structure Constraint where
  terms  : List Term
  degree : Int

def Holds (a : Nat -> Bool) (c : Constraint) : Prop :=
  Int.le c.degree (evalTerms a c.terms)

def HoldsAll (a : Nat -> Bool) (F : List Constraint) : Prop :=
  match F with
  | []        => True
  | c :: rest => And (Holds a c) (HoldsAll a rest)

def Entails (F : List Constraint) (c : Constraint) : Prop :=
  forall a : Nat -> Bool, HoldsAll a F -> Holds a c

def Unsat (F : List Constraint) : Prop :=
  forall a : Nat -> Bool, HoldsAll a F -> False

theorem evalTerms_nil (a : Nat -> Bool) : evalTerms a [] = 0 := rfl

theorem evalTerms_append_nil (a : Nat -> Bool) (ys : List Term) :
    evalTerms a (([] : List Term) ++ ys) = evalTerms a ([] : List Term) + evalTerms a ys :=
  (Int.zero_add (evalTerms a ys)).symm

theorem evalTerms_append_step (a : Nat -> Bool) (t : Term) (ts ys : List Term)
    (ih : evalTerms a (ts ++ ys) = evalTerms a ts + evalTerms a ys) :
    evalTerms a ((t :: ts) ++ ys) = evalTerms a (t :: ts) + evalTerms a ys :=
  @Bool.rec
    (fun b : Bool =>
      (match b with
        | true  => t.coeff + evalTerms a (ts ++ ys)
        | false => evalTerms a (ts ++ ys))
      = (match b with
        | true  => t.coeff + evalTerms a ts
        | false => evalTerms a ts) + evalTerms a ys)
    ih
    (Eq.trans
      (congrArg (fun z => t.coeff + z) ih)
      (Int.add_assoc t.coeff (evalTerms a ts) (evalTerms a ys)).symm)
    (litVal a t.lit)

theorem evalTerms_append (a : Nat -> Bool) (xs ys : List Term) :
    evalTerms a (xs ++ ys) = evalTerms a xs + evalTerms a ys :=
  @List.rec Term
    (fun xs => evalTerms a (xs ++ ys) = evalTerms a xs + evalTerms a ys)
    (evalTerms_append_nil a ys)
    (fun t ts ih => evalTerms_append_step a t ts ys ih)
    xs

theorem add_le_add (r1 r2 L1 L2 : Int) (h1 : Int.le r1 L1) (h2 : Int.le r2 L2) :
    Int.le (r1 + r2) (L1 + L2) :=
  Int.le_trans (r1 + r2) (L1 + r2) (L1 + L2)
    (Int.add_le_add_right r1 L1 h1 r2)
    (Int.add_le_add_left r2 L2 h2 L1)

theorem le_congr_left (x y z : Int) (heq : x = y) (h : Int.le x z) : Int.le y z :=
  @Eq.subst Int (fun w : Int => Int.le w z) x y heq h

theorem le_congr_right (x y z : Int) (heq : x = y) (h : Int.le z x) : Int.le z y :=
  @Eq.subst Int (fun w : Int => Int.le z w) x y heq h

theorem le_cancel_right (a b c : Int) (h : Int.le (a + b) (c + b)) : Int.le a c :=
  Eq.mpr (congrArg (fun z : Int => Int.NonNeg z) (Int.add_sub_add_right a c b).symm) h

def addC (c1 c2 : Constraint) : Constraint :=
  { terms := c1.terms ++ c2.terms, degree := c1.degree + c2.degree }

theorem entails_add (F : List Constraint) (c1 c2 : Constraint)
    (h1 : Entails F c1) (h2 : Entails F c2) : Entails F (addC c1 c2) :=
  fun a ha =>
    Eq.mpr
      (congrArg (Int.le (c1.degree + c2.degree)) (evalTerms_append a c1.terms c2.terms))
      (add_le_add c1.degree c2.degree (evalTerms a c1.terms) (evalTerms a c2.terms)
        (h1 a ha) (h2 a ha))

def weakenC (d : Int) (c : Constraint) : Constraint :=
  { terms := c.terms, degree := d }

theorem entails_weaken_degree (F : List Constraint) (c : Constraint) (d : Int)
    (hd : Int.le d c.degree) (h : Entails F c) : Entails F (weakenC d c) :=
  fun a ha => Int.le_trans d c.degree (evalTerms a c.terms) hd (h a ha)

def contradiction : Constraint := { terms := [], degree := 1 }

theorem int_lt_0_1 : Int.lt 0 1 := Int.le_refl 1

theorem unsat_of_entails_contradiction (F : List Constraint)
    (h : Entails F contradiction) : Unsat F :=
  fun a ha =>
    Int.lt_irrefl 1
      (Int.lt_of_le_of_lt 1 0 1 (h a ha) int_lt_0_1)

def scaleTerms (k : Int) (ts : List Term) : List Term :=
  match ts with
  | []        => []
  | t :: rest => ({ coeff := k * t.coeff, lit := t.lit } : Term) :: scaleTerms k rest

def scaleC (k : Int) (c : Constraint) : Constraint :=
  { terms := scaleTerms k c.terms, degree := k * c.degree }

theorem evalTerms_scale_nil (a : Nat -> Bool) (k : Int) :
    evalTerms a (scaleTerms k ([] : List Term)) = k * evalTerms a ([] : List Term) :=
  (Int.mul_zero k).symm

theorem evalTerms_scale_step (a : Nat -> Bool) (k : Int) (t : Term) (ts : List Term)
    (ih : evalTerms a (scaleTerms k ts) = k * evalTerms a ts) :
    evalTerms a (scaleTerms k (t :: ts)) = k * evalTerms a (t :: ts) :=
  @Bool.rec
    (fun b : Bool =>
      (match b with
        | true  => k * t.coeff + evalTerms a (scaleTerms k ts)
        | false => evalTerms a (scaleTerms k ts))
      = k * (match b with
        | true  => t.coeff + evalTerms a ts
        | false => evalTerms a ts))
    ih
    (Eq.trans
      (congrArg (fun z => k * t.coeff + z) ih)
      (Int.left_distrib k t.coeff (evalTerms a ts)).symm)
    (litVal a t.lit)

theorem evalTerms_scale (a : Nat -> Bool) (k : Int) (ts : List Term) :
    evalTerms a (scaleTerms k ts) = k * evalTerms a ts :=
  @List.rec Term
    (fun ts => evalTerms a (scaleTerms k ts) = k * evalTerms a ts)
    (evalTerms_scale_nil a k)
    (fun t ts ih => evalTerms_scale_step a k t ts ih)
    ts

theorem entails_multiply (F : List Constraint) (c : Constraint) (k : Int)
    (hk : Int.le 0 k) (h : Entails F c) : Entails F (scaleC k c) :=
  fun a ha =>
    Eq.mpr
      (congrArg (Int.le (k * c.degree)) (evalTerms_scale a k c.terms))
      (Int.mul_le_mul_of_nonneg_left c.degree (evalTerms a c.terms) k (h a ha) hk)

def litAxiom (l : Lit) : Constraint :=
  { terms := [({ coeff := 1, lit := l } : Term), ({ coeff := 1, lit := negLit l } : Term)],
    degree := 1 }

theorem litVal_negLit (a : Nat -> Bool) (l : Lit) :
    litVal a (negLit l) = Bool.not (litVal a l) :=
  @Bool.rec
    (fun b : Bool =>
      (match Bool.not b with
        | true  => Bool.not (a l.var)
        | false => a l.var)
      = Bool.not
        (match b with
          | true  => Bool.not (a l.var)
          | false => a l.var))
    rfl
    (Bool.not_not (a l.var)).symm
    l.negated

theorem evalTerms_litAxiom (a : Nat -> Bool) (l : Lit) :
    evalTerms a (litAxiom l).terms = 1 :=
  Eq.mpr
    (congrArg
      (fun z : Bool =>
        (match litVal a l with
          | true  => (1 : Int) + (match z with
                                  | true  => (1 : Int) + evalTerms a ([] : List Term)
                                  | false => evalTerms a ([] : List Term))
          | false => (match z with
                      | true  => (1 : Int) + evalTerms a ([] : List Term)
                      | false => evalTerms a ([] : List Term))) = 1)
      (litVal_negLit a l))
    (@Bool.rec
      (fun b : Bool =>
        (match b with
          | true  => (1 : Int) + (match Bool.not b with
                                  | true  => (1 : Int) + evalTerms a ([] : List Term)
                                  | false => evalTerms a ([] : List Term))
          | false => (match Bool.not b with
                      | true  => (1 : Int) + evalTerms a ([] : List Term)
                      | false => evalTerms a ([] : List Term))) = 1)
      rfl rfl (litVal a l))

theorem holds_litAxiom (a : Nat -> Bool) (l : Lit) :
    Int.le 1 (evalTerms a (litAxiom l).terms) :=
  Eq.mpr (congrArg (fun z : Int => Int.le 1 z) (evalTerms_litAxiom a l)) (Int.le_refl 1)

theorem entails_literal (F : List Constraint) (l : Lit) : Entails F (litAxiom l) :=
  fun a _ => holds_litAxiom a l

def mapCoeff (f : Int -> Int) (ts : List Term) : List Term :=
  match ts with
  | []        => []
  | t :: rest => ({ coeff := f t.coeff, lit := t.lit } : Term) :: mapCoeff f rest

def CoeffsDominated (k : Int) (f : Int -> Int) (ts : List Term) : Prop :=
  match ts with
  | []        => True
  | t :: rest => And (Int.le t.coeff (k * f t.coeff)) (CoeffsDominated k f rest)

def coeffsDominatedB (k : Int) (f : Int -> Int) (ts : List Term) : Bool :=
  match ts with
  | []        => true
  | t :: rest =>
    match Int.ble t.coeff (k * f t.coeff) with
    | true  => coeffsDominatedB k f rest
    | false => false

theorem coeffsDominated_of_check (k : Int) (f : Int -> Int) (ts : List Term) :
    coeffsDominatedB k f ts = true -> CoeffsDominated k f ts :=
  @List.rec Term
    (fun ts => coeffsDominatedB k f ts = true -> CoeffsDominated k f ts)
    (fun _ => True.intro)
    (fun t rest ih =>
      @Bool.rec
        (fun b : Bool =>
          (Int.ble t.coeff (k * f t.coeff) = b) ->
          (match b with
            | true  => coeffsDominatedB k f rest
            | false => false) = true ->
          And (Int.le t.coeff (k * f t.coeff)) (CoeffsDominated k f rest))
        (fun _ hh => Bool.noConfusion hh)
        (fun hb hh =>
          And.intro (Int.le_of_ble_eq_true t.coeff (k * f t.coeff) hb) (ih hh))
        (Int.ble t.coeff (k * f t.coeff))
        rfl)
    ts

theorem evalTerms_le_mul_map_nil (a : Nat -> Bool) (k : Int) (f : Int -> Int) :
    CoeffsDominated k f ([] : List Term) ->
    Int.le (evalTerms a ([] : List Term)) (k * evalTerms a (mapCoeff f ([] : List Term))) :=
  fun _ => Eq.mpr (congrArg (fun z : Int => Int.le 0 z) (Int.mul_zero k)) (Int.le_refl 0)

theorem evalTerms_le_mul_map_step (a : Nat -> Bool) (k : Int) (f : Int -> Int)
    (t : Term) (rest : List Term)
    (ih : CoeffsDominated k f rest ->
          Int.le (evalTerms a rest) (k * evalTerms a (mapCoeff f rest))) :
    CoeffsDominated k f (t :: rest) ->
    Int.le (evalTerms a (t :: rest)) (k * evalTerms a (mapCoeff f (t :: rest))) :=
  fun hd =>
    @Bool.rec
      (fun b : Bool =>
        Int.le
          (match b with
            | true  => t.coeff + evalTerms a rest
            | false => evalTerms a rest)
          (k * (match b with
            | true  => f t.coeff + evalTerms a (mapCoeff f rest)
            | false => evalTerms a (mapCoeff f rest))))
      (ih hd.right)
      (Eq.mpr
        (congrArg (fun z : Int => Int.le (t.coeff + evalTerms a rest) z)
          (Int.left_distrib k (f t.coeff) (evalTerms a (mapCoeff f rest))))
        (add_le_add t.coeff (evalTerms a rest)
          (k * f t.coeff) (k * evalTerms a (mapCoeff f rest))
          hd.left (ih hd.right)))
      (litVal a t.lit)

theorem evalTerms_le_mul_map (a : Nat -> Bool) (k : Int) (f : Int -> Int) (ts : List Term) :
    CoeffsDominated k f ts -> Int.le (evalTerms a ts) (k * evalTerms a (mapCoeff f ts)) :=
  @List.rec Term
    (fun ts => CoeffsDominated k f ts ->
      Int.le (evalTerms a ts) (k * evalTerms a (mapCoeff f ts)))
    (evalTerms_le_mul_map_nil a k f)
    (fun t rest ih => evalTerms_le_mul_map_step a k f t rest ih)
    ts

theorem le_of_mul_le_min (k Q q d : Int)
    (hk : Int.le 0 k)
    (hQ : Int.le d (k * Q))
    (hmin : Int.lt (k * q) (d + k)) :
    Int.le q Q :=
  @Or.rec (Int.lt q Q) (Or (Eq q Q) (Int.lt Q q)) (fun _ => Int.le q Q)
    (fun h => Int.le_of_lt q Q h)
    (fun h =>
      @Or.rec (Eq q Q) (Int.lt Q q) (fun _ => Int.le q Q)
        (fun heq => Eq.mpr (congrArg (fun z : Int => Int.le q z) heq.symm) (Int.le_refl q))
        (fun hlt =>
          False.elim
            (Int.lt_irrefl (k * q)
              (Int.lt_of_lt_of_le (k * q) (k * Q + k) (k * q)
                (Int.lt_of_lt_of_le (k * q) (d + k) (k * Q + k)
                  hmin
                  (Int.add_le_add_right d (k * Q) hQ k))
                (Eq.mpr
                  (congrArg (fun z : Int => Int.le z (k * q))
                    (Eq.trans (Int.left_distrib k Q 1)
                      (congrArg (fun z : Int => k * Q + z) (Int.mul_one k))).symm)
                  (Int.mul_le_mul_of_nonneg_left (Q + 1) q k hlt hk)))))
        h)
    (Int.lt_trichotomy q Q)

def divC (f : Int -> Int) (c : Constraint) : Constraint :=
  { terms := mapCoeff f c.terms, degree := f c.degree }

theorem entails_divide (F : List Constraint) (c : Constraint) (k : Int) (f : Int -> Int)
    (hk : Int.le 0 k)
    (hdom : CoeffsDominated k f c.terms)
    (hmin : Int.lt (k * f c.degree) (c.degree + k))
    (h : Entails F c) : Entails F (divC f c) :=
  fun a ha =>
    le_of_mul_le_min k (evalTerms a (mapCoeff f c.terms)) (f c.degree) c.degree hk
      (Int.le_trans c.degree (evalTerms a c.terms) (k * evalTerms a (mapCoeff f c.terms))
        (h a ha)
        (evalTerms_le_mul_map a k f c.terms hdom))
      hmin

theorem add_shuffle (x y z : Int) : x + (y + z) = y + (x + z) :=
  Eq.trans (Int.add_assoc x y z).symm
    (Eq.trans (congrArg (fun w : Int => w + z) (Int.add_comm x y))
      (Int.add_assoc y x z))

def negTerms (ts : List Term) : List Term :=
  match ts with
  | []        => []
  | t :: rest => ({ coeff := t.coeff, lit := negLit t.lit } : Term) :: negTerms rest

def coeffSum (ts : List Term) : Int :=
  match ts with
  | []        => 0
  | t :: rest => t.coeff + coeffSum rest

theorem evalTerms_negTerms_nil (a : Nat -> Bool) :
    evalTerms a (negTerms ([] : List Term)) + evalTerms a ([] : List Term)
      = coeffSum ([] : List Term) := rfl

theorem evalTerms_negTerms_step (a : Nat -> Bool) (t : Term) (rest : List Term)
    (ih : evalTerms a (negTerms rest) + evalTerms a rest = coeffSum rest) :
    evalTerms a (negTerms (t :: rest)) + evalTerms a (t :: rest) = coeffSum (t :: rest) :=
  Eq.mpr
    (congrArg
      (fun z : Bool =>
        ((match z with
            | true  => t.coeff + evalTerms a (negTerms rest)
            | false => evalTerms a (negTerms rest))
          + (match litVal a t.lit with
            | true  => t.coeff + evalTerms a rest
            | false => evalTerms a rest)) = t.coeff + coeffSum rest)
      (litVal_negLit a t.lit))
    (@Bool.rec
      (fun b : Bool =>
        ((match Bool.not b with
            | true  => t.coeff + evalTerms a (negTerms rest)
            | false => evalTerms a (negTerms rest))
          + (match b with
            | true  => t.coeff + evalTerms a rest
            | false => evalTerms a rest)) = t.coeff + coeffSum rest)
      (Eq.trans (Int.add_assoc t.coeff (evalTerms a (negTerms rest)) (evalTerms a rest))
        (congrArg (fun z : Int => t.coeff + z) ih))
      (Eq.trans (add_shuffle (evalTerms a (negTerms rest)) t.coeff (evalTerms a rest))
        (congrArg (fun z : Int => t.coeff + z) ih))
      (litVal a t.lit))

theorem evalTerms_negTerms (a : Nat -> Bool) (ts : List Term) :
    evalTerms a (negTerms ts) + evalTerms a ts = coeffSum ts :=
  @List.rec Term
    (fun ts => evalTerms a (negTerms ts) + evalTerms a ts = coeffSum ts)
    (evalTerms_negTerms_nil a)
    (fun t rest ih => evalTerms_negTerms_step a t rest ih)
    ts

def negC (c : Constraint) (nd : Int) : Constraint :=
  { terms := negTerms c.terms, degree := nd }

theorem le_of_neg_bound (nd D E N S : Int)
    (hnd : nd + D = S + 1) (hNE : N + E = S) (hlt : Int.le (E + 1) D) :
    Int.le nd N :=
  le_cancel_right nd E N
    (le_cancel_right (nd + E) 1 (N + E)
      (le_congr_left (nd + (E + 1)) ((nd + E) + 1) ((N + E) + 1)
        (Int.add_assoc nd E 1).symm
        (le_congr_right (nd + D) ((N + E) + 1) (nd + (E + 1))
          (Eq.trans hnd (congrArg (fun z : Int => z + 1) hNE.symm))
          (Int.add_le_add_left (E + 1) D hlt nd))))

theorem negC_holds_of_violated (a : Nat -> Bool) (c : Constraint) (nd : Int)
    (hnd : nd + c.degree = coeffSum c.terms + 1)
    (hlt : Int.lt (evalTerms a c.terms) c.degree) :
    Int.le nd (evalTerms a (negTerms c.terms)) :=
  le_of_neg_bound nd c.degree (evalTerms a c.terms)
    (evalTerms a (negTerms c.terms)) (coeffSum c.terms)
    hnd (evalTerms_negTerms a c.terms) hlt

theorem entails_of_negation_unsat (F : List Constraint) (c : Constraint) (nd : Int)
    (hnd : nd + c.degree = coeffSum c.terms + 1)
    (hU : Unsat (negC c nd :: F)) : Entails F c :=
  fun a ha =>
    @Or.rec (Int.lt c.degree (evalTerms a c.terms))
        (Or (Eq c.degree (evalTerms a c.terms)) (Int.lt (evalTerms a c.terms) c.degree))
        (fun _ => Int.le c.degree (evalTerms a c.terms))
      (fun h => Int.le_of_lt c.degree (evalTerms a c.terms) h)
      (fun h =>
        @Or.rec (Eq c.degree (evalTerms a c.terms)) (Int.lt (evalTerms a c.terms) c.degree)
            (fun _ => Int.le c.degree (evalTerms a c.terms))
          (fun heq =>
            Eq.mpr (congrArg (fun z : Int => Int.le c.degree z) heq.symm)
              (Int.le_refl c.degree))
          (fun hlt =>
            False.elim
              (hU a (And.intro (negC_holds_of_violated a c nd hnd hlt) ha)))
          h)
      (Int.lt_trichotomy c.degree (evalTerms a c.terms))

def i64Max : Int := 9223372036854775807
def i64Min : Int := Int.neg 9223372036854775808

def InI64 (x : Int) : Prop := And (Int.le i64Min x) (Int.le x i64Max)

def fitsI64 (x : Int) : Bool :=
  match Int.ble i64Min x with
  | true  => Int.ble x i64Max
  | false => false

theorem fitsI64_lower (x : Int) (h : fitsI64 x = true) : Int.le i64Min x :=
  @Bool.rec
    (fun b : Bool =>
      (Int.ble i64Min x = b) ->
      (match b with
        | true  => Int.ble x i64Max
        | false => false) = true ->
      Int.le i64Min x)
    (fun _ hh => Bool.noConfusion hh)
    (fun hb _ => Int.le_of_ble_eq_true i64Min x hb)
    (Int.ble i64Min x) rfl h

theorem fitsI64_upper (x : Int) (h : fitsI64 x = true) : Int.le x i64Max :=
  @Bool.rec
    (fun b : Bool =>
      (Int.ble i64Min x = b) ->
      (match b with
        | true  => Int.ble x i64Max
        | false => false) = true ->
      Int.le x i64Max)
    (fun _ hh => Bool.noConfusion hh)
    (fun _ hh => Int.le_of_ble_eq_true x i64Max hh)
    (Int.ble i64Min x) rfl h

theorem inI64_of_fitsI64 (x : Int) (h : fitsI64 x = true) : InI64 x :=
  And.intro (fitsI64_lower x h) (fitsI64_upper x h)

def eqOkB (x y : Int) : Bool :=
  match Int.ble x y with
  | true  => Int.ble y x
  | false => false

theorem eq_of_eqOkB (x y : Int) (h : eqOkB x y = true) : x = y :=
  @Bool.rec
    (fun b : Bool =>
      (Int.ble x y = b) ->
      (match b with
        | true  => Int.ble y x
        | false => false) = true ->
      x = y)
    (fun _ hh => Bool.noConfusion hh)
    (fun hb hh =>
      Int.le_antisymm x y (Int.le_of_ble_eq_true x y hb) (Int.le_of_ble_eq_true y x hh))
    (Int.ble x y) rfl h

theorem entails_add_checked (F : List Constraint) (c1 c2 : Constraint) (s : Int)
    (hs : eqOkB s (c1.degree + c2.degree) = true)
    (hfit : fitsI64 s = true)
    (h1 : Entails F c1) (h2 : Entails F c2) :
    And (InI64 s) (Entails F { terms := c1.terms ++ c2.terms, degree := s }) :=
  And.intro (inI64_of_fitsI64 s hfit)
    (Eq.mpr
      (congrArg
        (fun z : Int => Entails F ({ terms := c1.terms ++ c2.terms, degree := z } : Constraint))
        (eq_of_eqOkB s (c1.degree + c2.degree) hs))
      (entails_add F c1 c2 h1 h2))

theorem entails_weaken_checked (F : List Constraint) (c : Constraint) (w r : Int)
    (hr : eqOkB (r + w) c.degree = true)
    (hw : Int.le 0 w)
    (hfit : fitsI64 r = true)
    (h : Entails F c) : And (InI64 r) (Entails F (weakenC r c)) :=
  And.intro (inI64_of_fitsI64 r hfit)
    (entails_weaken_degree F c r
      (Eq.mpr
        (congrArg (fun z : Int => Int.le r z) (eq_of_eqOkB (r + w) c.degree hr).symm)
        (Eq.mpr
          (congrArg (fun z : Int => Int.le z (r + w)) (Int.add_zero r).symm)
          (Int.add_le_add_left 0 w hw r)))
      h)

theorem entails_multiply_checked (F : List Constraint) (c : Constraint) (k s : Int)
    (hk : Int.le 0 k)
    (hs : eqOkB s (k * c.degree) = true)
    (hfit : fitsI64 s = true)
    (h : Entails F c) :
    And (InI64 s) (Entails F { terms := scaleTerms k c.terms, degree := s }) :=
  And.intro (inI64_of_fitsI64 s hfit)
    (Eq.mpr
      (congrArg
        (fun z : Int => Entails F ({ terms := scaleTerms k c.terms, degree := z } : Constraint))
        (eq_of_eqOkB s (k * c.degree) hs))
      (entails_multiply F c k hk h))

theorem entails_divide_checked (F : List Constraint) (c : Constraint) (k : Int)
    (f : Int -> Int) (s : Int)
    (hk : Int.le 0 k)
    (hdom : CoeffsDominated k f c.terms)
    (hmin : Int.lt (k * f c.degree) (c.degree + k))
    (hs : eqOkB s (f c.degree) = true)
    (hfit : fitsI64 s = true)
    (h : Entails F c) :
    And (InI64 s) (Entails F { terms := mapCoeff f c.terms, degree := s }) :=
  And.intro (inI64_of_fitsI64 s hfit)
    (Eq.mpr
      (congrArg
        (fun z : Int => Entails F ({ terms := mapCoeff f c.terms, degree := z } : Constraint))
        (eq_of_eqOkB s (f c.degree) hs))
      (entails_divide F c k f hk hdom hmin h))

def AllNonneg (ts : List Term) : Prop :=
  match ts with
  | []        => True
  | t :: rest => And (Int.le 0 t.coeff) (AllNonneg rest)

def allNonnegB (ts : List Term) : Bool :=
  match ts with
  | []        => true
  | t :: rest =>
    match Int.ble 0 t.coeff with
    | true  => allNonnegB rest
    | false => false

theorem allNonneg_of_check (ts : List Term) : allNonnegB ts = true -> AllNonneg ts :=
  @List.rec Term
    (fun ts => allNonnegB ts = true -> AllNonneg ts)
    (fun _ => True.intro)
    (fun t rest ih =>
      @Bool.rec
        (fun b : Bool =>
          (Int.ble 0 t.coeff = b) ->
          (match b with
            | true  => allNonnegB rest
            | false => false) = true ->
          And (Int.le 0 t.coeff) (AllNonneg rest))
        (fun _ hh => Bool.noConfusion hh)
        (fun hb hh => And.intro (Int.le_of_ble_eq_true 0 t.coeff hb) (ih hh))
        (Int.ble 0 t.coeff)
        rfl)
    ts

theorem evalTerms_nonneg (a : Nat -> Bool) (ts : List Term) :
    AllNonneg ts -> Int.le 0 (evalTerms a ts) :=
  @List.rec Term
    (fun ts => AllNonneg ts -> Int.le 0 (evalTerms a ts))
    (fun _ => Int.le_refl 0)
    (fun t rest ih hn =>
      @Bool.rec
        (fun b : Bool =>
          Int.le 0 (match b with
            | true  => t.coeff + evalTerms a rest
            | false => evalTerms a rest))
        (ih hn.right)
        (le_congr_left (0 + 0) 0 (t.coeff + evalTerms a rest)
          (Int.add_zero 0)
          (add_le_add 0 0 t.coeff (evalTerms a rest) hn.left (ih hn.right)))
        (litVal a t.lit))
    ts

def capCoeff (d c : Int) : Int :=
  match Int.ble c d with
  | true  => c
  | false => d

theorem capCoeff_le_degree (d c : Int) : Int.le (capCoeff d c) d :=
  @Bool.rec
    (fun b : Bool =>
      (Int.ble c d = b) ->
      Int.le (match b with | true => c | false => d) d)
    (fun _ => Int.le_refl d)
    (fun hb => Int.le_of_ble_eq_true c d hb)
    (Int.ble c d)
    rfl

theorem capCoeff_nonneg (d c : Int) (hd : Int.le 0 d) (hc : Int.le 0 c) :
    Int.le 0 (capCoeff d c) :=
  @Bool.rec
    (fun b : Bool => Int.le 0 (match b with | true => c | false => d))
    hd hc
    (Int.ble c d)

theorem le_capCoeff (d x : Int) (h : Int.le d x) : Int.le d (capCoeff d x) :=
  @Bool.rec
    (fun b : Bool => Int.le d (match b with | true => x | false => d))
    (Int.le_refl d) h
    (Int.ble x d)

def satTerms (d : Int) (ts : List Term) : List Term :=
  match ts with
  | []        => []
  | t :: rest => ({ coeff := capCoeff d t.coeff, lit := t.lit } : Term) :: satTerms d rest

def satC (c : Constraint) : Constraint :=
  { terms := satTerms c.degree c.terms, degree := c.degree }

theorem satTerms_nonneg (d : Int) (hd : Int.le 0 d) (ts : List Term) :
    AllNonneg ts -> AllNonneg (satTerms d ts) :=
  @List.rec Term
    (fun ts => AllNonneg ts -> AllNonneg (satTerms d ts))
    (fun _ => True.intro)
    (fun t rest ih hn =>
      And.intro (capCoeff_nonneg d t.coeff hd hn.left) (ih hn.right))
    ts

def SaturateKey : Prop :=
  forall (a : Nat -> Bool) (d : Int) (ts : List Term),
    Int.le 0 d -> AllNonneg ts ->
    Int.le (capCoeff d (evalTerms a ts)) (evalTerms a (satTerms d ts))

theorem entails_saturate_of_key (hkey : SaturateKey)
    (F : List Constraint) (c : Constraint)
    (hd : Int.le 0 c.degree) (hn : AllNonneg c.terms) (h : Entails F c) :
    Entails F (satC c) :=
  fun a ha =>
    Int.le_trans c.degree (capCoeff c.degree (evalTerms a c.terms))
      (evalTerms a (satTerms c.degree c.terms))
      (le_capCoeff c.degree (evalTerms a c.terms) (h a ha))
      (hkey a c.degree c.terms hd hn)

theorem le_of_ble_eq_false (x d : Int) (hb : Int.ble x d = false) : Int.le d x :=
  @Or.rec (Int.le x d) (Int.le d x) (fun _ => Int.le d x)
    (fun h => @Bool.noConfusion (Int.le d x) false true
        (Eq.trans hb.symm (Int.ble_eq_true_of_le x d h)))
    (fun h => h)
    (Int.le_total x d)

theorem capCoeff_le_self (d x : Int) : Int.le (capCoeff d x) x :=
  @Bool.rec
    (fun b : Bool =>
      (Int.ble x d = b) -> Int.le (match b with | true => x | false => d) x)
    (fun hb => le_of_ble_eq_false x d hb)
    (fun _ => Int.le_refl x)
    (Int.ble x d)
    rfl

theorem capCoeff_of_le (d x : Int) (h : Int.le x d) : capCoeff d x = x :=
  @Bool.rec
    (fun b : Bool =>
      (Int.ble x d = b) -> (match b with | true => x | false => d) = x)
    (fun hb => Bool.noConfusion (Eq.trans hb.symm (Int.ble_eq_true_of_le x d h)))
    (fun _ => rfl)
    (Int.ble x d)
    rfl

theorem capCoeff_le_of_le_degree (d x P : Int) (h : Int.le d P) : Int.le (capCoeff d x) P :=
  Int.le_trans (capCoeff d x) d P (capCoeff_le_degree d x) h

theorem le_add_left_of_nonneg (c P : Int) (hc : Int.le 0 c) : Int.le P (c + P) :=
  le_congr_left (0 + P) P (c + P) (Int.zero_add P)
    (add_le_add 0 P c P hc (Int.le_refl P))

theorem le_add_right_of_nonneg (d Z : Int) (hz : Int.le 0 Z) : Int.le d (d + Z) :=
  le_congr_left (d + 0) d (d + Z) (Int.add_zero d)
    (add_le_add d 0 d Z (Int.le_refl d) hz)

theorem satKey_step (d c L Ls : Int)
    (hc : Int.le 0 c) (hLs : Int.le 0 Ls)
    (ih : Int.le (capCoeff d L) Ls) :
    Int.le (capCoeff d (c + L)) (capCoeff d c + Ls) :=
  @Bool.rec
    (fun b : Bool =>
      (Int.ble c d = b) ->
      Int.le (capCoeff d (c + L)) ((match b with | true => c | false => d) + Ls))
    (fun _ =>
      capCoeff_le_of_le_degree d (c + L) (d + Ls) (le_add_right_of_nonneg d Ls hLs))
    (fun _ =>
      @Bool.rec
        (fun b2 : Bool =>
          Int.le (match b2 with | true => L | false => d) Ls ->
          Int.le (capCoeff d (c + L)) (c + Ls))
        (fun hih =>
          capCoeff_le_of_le_degree d (c + L) (c + Ls)
            (Int.le_trans d Ls (c + Ls) hih (le_add_left_of_nonneg c Ls hc)))
        (fun hih =>
          Int.le_trans (capCoeff d (c + L)) (c + L) (c + Ls)
            (capCoeff_le_self d (c + L))
            (Int.add_le_add_left L Ls hih c))
        (Int.ble L d)
        ih)
    (Int.ble c d)
    rfl

theorem saturate_key : SaturateKey :=
  fun a d ts hd =>
    @List.rec Term
      (fun ts =>
        AllNonneg ts -> Int.le (capCoeff d (evalTerms a ts)) (evalTerms a (satTerms d ts)))
      (fun _ =>
        le_congr_left 0 (capCoeff d 0) 0 (capCoeff_of_le d 0 hd).symm (Int.le_refl 0))
      (fun t rest ih hn =>
        @Bool.rec
          (fun b : Bool =>
            Int.le
              (capCoeff d (match b with
                | true  => t.coeff + evalTerms a rest
                | false => evalTerms a rest))
              (match b with
                | true  => capCoeff d t.coeff + evalTerms a (satTerms d rest)
                | false => evalTerms a (satTerms d rest)))
          (ih hn.right)
          (satKey_step d t.coeff (evalTerms a rest) (evalTerms a (satTerms d rest))
            hn.left
            (evalTerms_nonneg a (satTerms d rest) (satTerms_nonneg d hd rest hn.right))
            (ih hn.right))
          (litVal a t.lit))
      ts

theorem entails_saturate (F : List Constraint) (c : Constraint)
    (hd : Int.le 0 c.degree) (hn : AllNonneg c.terms) (h : Entails F c) :
    Entails F (satC c) :=
  entails_saturate_of_key saturate_key F c hd hn h

def ctrlX : Lit := { var := 0, negated := false }
def ctrlNotX : Lit := negLit ctrlX
def ctrlAllTrue : Nat -> Bool := fun _ => true
def ctrlAllFalse : Nat -> Bool := fun _ => false

theorem ctrl_eval_true :
    evalTerms ctrlAllTrue [({ coeff := 3, lit := ctrlX } : Term)] = 3 := rfl
theorem ctrl_eval_false :
    evalTerms ctrlAllFalse [({ coeff := 3, lit := ctrlX } : Term)] = 0 := rfl

theorem ctrl_litAxiom_true : evalTerms ctrlAllTrue (litAxiom ctrlX).terms = 1 := rfl
theorem ctrl_litAxiom_false : evalTerms ctrlAllFalse (litAxiom ctrlX).terms = 1 := rfl

theorem ctrl_cap_hi : capCoeff 3 7 = 3 := rfl
theorem ctrl_cap_lo : capCoeff 3 2 = 2 := rfl

theorem ctrl_fits_max : fitsI64 9223372036854775807 = true := rfl
theorem ctrl_fits_overflow : fitsI64 9223372036854775808 = false := rfl
theorem ctrl_fits_min : fitsI64 (Int.neg 9223372036854775808) = true := rfl
theorem ctrl_fits_underflow : fitsI64 (Int.neg 9223372036854775809) = false := rfl

theorem ctrl_eq_guard_rejects_wrap :
    eqOkB 9223372036854775807 (Int.neg 9223372036854775809) = false := rfl
theorem ctrl_eq_guard_accepts : eqOkB 41 (40 + 1) = true := rfl

def boolEqB (b1 b2 : Bool) : Bool :=
  match b1 with
  | true  => b2
  | false => Bool.not b2

theorem boolEqB_sound (b1 b2 : Bool) (h : boolEqB b1 b2 = true) : b1 = b2 :=
  @Bool.rec
    (fun x : Bool =>
      (match x with
       | true  => b2
       | false => Bool.not b2) = true -> x = b2)
    (fun hh =>
      @Bool.rec (fun y : Bool => Bool.not y = true -> false = y)
        (fun _ => rfl)
        (fun hy => Bool.noConfusion hy)
        b2 hh)
    (fun hh =>
      @Bool.rec (fun y : Bool => y = true -> true = y)
        (fun hy => Bool.noConfusion hy)
        (fun _ => rfl)
        b2 hh)
    b1 h

def litEqB (l1 l2 : Lit) : Bool :=
  match Nat.beq l1.var l2.var with
  | true  => boolEqB l1.negated l2.negated
  | false => false

theorem mkLit_congr (v1 v2 : Nat) (b1 b2 : Bool) (hv : v1 = v2) (hb : b1 = b2) :
    ({ var := v1, negated := b1 } : Lit) = { var := v2, negated := b2 } :=
  Eq.trans
    (congrArg (fun v : Nat => ({ var := v, negated := b1 } : Lit)) hv)
    (congrArg (fun b : Bool => ({ var := v2, negated := b } : Lit)) hb)

theorem litEqB_sound (l1 l2 : Lit) (h : litEqB l1 l2 = true) : l1 = l2 :=
  @Bool.rec
    (fun x : Bool =>
      (Nat.beq l1.var l2.var = x) ->
      (match x with
       | true  => boolEqB l1.negated l2.negated
       | false => false) = true ->
      l1 = l2)
    (fun _ hh => Bool.noConfusion hh)
    (fun hbeq hh =>
      mkLit_congr l1.var l2.var l1.negated l2.negated
        (Nat.eq_of_beq_eq_true l1.var l2.var hbeq)
        (boolEqB_sound l1.negated l2.negated hh))
    (Nat.beq l1.var l2.var) rfl h

def memB (l : Lit) (tr : List Lit) : Bool :=
  match tr with
  | []        => false
  | x :: rest =>
    match litEqB l x with
    | true  => true
    | false => memB l rest

def Agrees (a : Nat -> Bool) (tr : List Lit) : Prop :=
  match tr with
  | []        => True
  | x :: rest => And (litVal a x = true) (Agrees a rest)

theorem agrees_mem (a : Nat -> Bool) (tr : List Lit) (l : Lit)
    (hA : Agrees a tr) (hm : memB l tr = true) : litVal a l = true :=
  @List.rec Lit
    (fun tr => Agrees a tr -> memB l tr = true -> litVal a l = true)
    (fun _ hm => Bool.noConfusion hm)
    (fun x rest ih hA hm =>
      @Bool.rec
        (fun b : Bool =>
          (litEqB l x = b) ->
          (match b with
           | true  => true
           | false => memB l rest) = true ->
          litVal a l = true)
        (fun _ hh => ih hA.right hh)
        (fun hb _ =>
          @Eq.subst Lit (fun w : Lit => litVal a w = true) x l
            (litEqB_sound l x hb).symm hA.left)
        (litEqB l x) rfl hm)
    tr hA hm

theorem eq_false_of_not_eq_true (x : Bool) (h : Bool.not x = true) : x = false :=
  @Bool.rec (fun y : Bool => Bool.not y = true -> y = false)
    (fun _ => rfl)
    (fun hy => Bool.noConfusion hy)
    x h

theorem litVal_false_of_neg_mem (a : Nat -> Bool) (tr : List Lit) (l : Lit)
    (hA : Agrees a tr) (hm : memB (negLit l) tr = true) : litVal a l = false :=
  eq_false_of_not_eq_true (litVal a l)
    (Eq.trans (litVal_negLit a l).symm (agrees_mem a tr (negLit l) hA hm))

def getO (DB : List (Option Constraint)) (i : Nat) : Option Constraint :=
  match DB with
  | []        => none
  | o :: rest =>
    match i with
    | Nat.zero   => o
    | Nat.succ j => getO rest j

def unwrapC (o : Option Constraint) : Constraint :=
  match o with
  | none   => contradiction
  | some c => c

theorem someC_inj (c1 c2 : Constraint) (h : some c1 = some c2) : c1 = c2 :=
  congrArg unwrapC h

def isSomeB (o : Option Constraint) : Bool :=
  match o with
  | none   => false
  | some _ => true

theorem false_ne_true (h : false = true) : False :=
  Bool.noConfusion h

theorem none_ne_someC (c : Constraint) (h : (none : Option Constraint) = some c) : False :=
  false_ne_true (congrArg isSomeB h)

def HoldsAllO (a : Nat -> Bool) (DB : List (Option Constraint)) : Prop :=
  match DB with
  | []        => True
  | o :: rest =>
    match o with
    | none   => HoldsAllO a rest
    | some c => And (Holds a c) (HoldsAllO a rest)

theorem holdsAllO_get (a : Nat -> Bool) (DB : List (Option Constraint)) :
    forall (i : Nat) (c : Constraint),
      HoldsAllO a DB -> getO DB i = some c -> Holds a c :=
  @List.rec (Option Constraint)
    (fun DB => forall (i : Nat) (c : Constraint),
      HoldsAllO a DB -> getO DB i = some c -> Holds a c)
    (fun _ c _ hg => False.elim (none_ne_someC c hg))
    (fun o rest ih =>
      @Option.rec Constraint
        (fun o => forall (i : Nat) (c : Constraint),
          HoldsAllO a (o :: rest) -> getO (o :: rest) i = some c -> Holds a c)
        (fun i =>
          @Nat.rec
            (fun i => forall (c : Constraint),
              HoldsAllO a (none :: rest) -> getO (none :: rest) i = some c -> Holds a c)
            (fun c _ hg => False.elim (none_ne_someC c hg))
            (fun j _ c hall hg => ih j c hall hg)
            i)
        (fun c' i =>
          @Nat.rec
            (fun i => forall (c : Constraint),
              HoldsAllO a (some c' :: rest) -> getO (some c' :: rest) i = some c -> Holds a c)
            (fun c hall hg =>
              @Eq.subst Constraint (fun w : Constraint => Holds a w) c' c
                (someC_inj c' c hg) hall.left)
            (fun j _ c hall hg => ih j c hall.right hg)
            i)
        o)
    DB

def slackTerms (tr : List Lit) (ts : List Term) : Int :=
  match ts with
  | []        => 0
  | t :: rest =>
    match memB (negLit t.lit) tr with
    | true  => slackTerms tr rest
    | false => t.coeff + slackTerms tr rest

def slackWithout (l : Lit) (tr : List Lit) (ts : List Term) : Int :=
  match ts with
  | []        => 0
  | t :: rest =>
    match litEqB t.lit l with
    | true  => slackWithout l tr rest
    | false =>
      match memB (negLit t.lit) tr with
      | true  => slackWithout l tr rest
      | false => t.coeff + slackWithout l tr rest

theorem evalTerms_le_slack (a : Nat -> Bool) (tr : List Lit) (hA : Agrees a tr)
    (ts : List Term) :
    AllNonneg ts -> Int.le (evalTerms a ts) (slackTerms tr ts) :=
  @List.rec Term
    (fun ts => AllNonneg ts -> Int.le (evalTerms a ts) (slackTerms tr ts))
    (fun _ => Int.le_refl 0)
    (fun t rest ih hn =>
      @Bool.rec
        (fun b : Bool =>
          (memB (negLit t.lit) tr = b) ->
          Int.le (match litVal a t.lit with
                  | true  => t.coeff + evalTerms a rest
                  | false => evalTerms a rest)
                 (match b with
                  | true  => slackTerms tr rest
                  | false => t.coeff + slackTerms tr rest))
        (fun _ =>
          @Bool.rec
            (fun z : Bool =>
              Int.le (match z with
                      | true  => t.coeff + evalTerms a rest
                      | false => evalTerms a rest)
                     (t.coeff + slackTerms tr rest))
            (Int.le_trans (evalTerms a rest) (slackTerms tr rest)
              (t.coeff + slackTerms tr rest)
              (ih hn.right)
              (le_add_left_of_nonneg t.coeff (slackTerms tr rest) hn.left))
            (Int.add_le_add_left (evalTerms a rest) (slackTerms tr rest)
              (ih hn.right) t.coeff)
            (litVal a t.lit))
        (fun hb =>
          Eq.mpr
            (congrArg
              (fun z : Bool =>
                Int.le (match z with
                        | true  => t.coeff + evalTerms a rest
                        | false => evalTerms a rest)
                       (slackTerms tr rest))
              (litVal_false_of_neg_mem a tr t.lit hA hb))
            (ih hn.right))
        (memB (negLit t.lit) tr) rfl)
    ts

theorem evalTerms_le_slackWithout (a : Nat -> Bool) (l : Lit) (tr : List Lit)
    (hA : Agrees a tr) (hl : litVal a l = false) (ts : List Term) :
    AllNonneg ts -> Int.le (evalTerms a ts) (slackWithout l tr ts) :=
  @List.rec Term
    (fun ts => AllNonneg ts -> Int.le (evalTerms a ts) (slackWithout l tr ts))
    (fun _ => Int.le_refl 0)
    (fun t rest ih hn =>
      @Bool.rec
        (fun b : Bool =>
          (litEqB t.lit l = b) ->
          Int.le (match litVal a t.lit with
                  | true  => t.coeff + evalTerms a rest
                  | false => evalTerms a rest)
                 (match b with
                  | true  => slackWithout l tr rest
                  | false =>
                    match memB (negLit t.lit) tr with
                    | true  => slackWithout l tr rest
                    | false => t.coeff + slackWithout l tr rest))
        (fun _ =>
          @Bool.rec
            (fun b2 : Bool =>
              (memB (negLit t.lit) tr = b2) ->
              Int.le (match litVal a t.lit with
                      | true  => t.coeff + evalTerms a rest
                      | false => evalTerms a rest)
                     (match b2 with
                      | true  => slackWithout l tr rest
                      | false => t.coeff + slackWithout l tr rest))
            (fun _ =>
              @Bool.rec
                (fun z : Bool =>
                  Int.le (match z with
                          | true  => t.coeff + evalTerms a rest
                          | false => evalTerms a rest)
                         (t.coeff + slackWithout l tr rest))
                (Int.le_trans (evalTerms a rest) (slackWithout l tr rest)
                  (t.coeff + slackWithout l tr rest)
                  (ih hn.right)
                  (le_add_left_of_nonneg t.coeff (slackWithout l tr rest) hn.left))
                (Int.add_le_add_left (evalTerms a rest) (slackWithout l tr rest)
                  (ih hn.right) t.coeff)
                (litVal a t.lit))
            (fun hb =>
              Eq.mpr
                (congrArg
                  (fun z : Bool =>
                    Int.le (match z with
                            | true  => t.coeff + evalTerms a rest
                            | false => evalTerms a rest)
                           (slackWithout l tr rest))
                  (litVal_false_of_neg_mem a tr t.lit hA hb))
                (ih hn.right))
            (memB (negLit t.lit) tr) rfl)
        (fun hb =>
          Eq.mpr
            (congrArg
              (fun z : Bool =>
                Int.le (match z with
                        | true  => t.coeff + evalTerms a rest
                        | false => evalTerms a rest)
                       (slackWithout l tr rest))
              (Eq.trans (congrArg (litVal a) (litEqB_sound t.lit l hb)) hl))
            (ih hn.right))
        (litEqB t.lit l) rfl)
    ts

theorem no_model_of_conflict (a : Nat -> Bool) (tr : List Lit) (c : Constraint)
    (hA : Agrees a tr) (hn : AllNonneg c.terms)
    (hconf : Int.lt (slackTerms tr c.terms) c.degree)
    (hH : Holds a c) : False :=
  Int.lt_irrefl (slackTerms tr c.terms)
    (Int.lt_of_lt_of_le (slackTerms tr c.terms) c.degree (slackTerms tr c.terms)
      hconf
      (Int.le_trans c.degree (evalTerms a c.terms) (slackTerms tr c.terms)
        hH
        (evalTerms_le_slack a tr hA c.terms hn)))

theorem propagated_lit_true (a : Nat -> Bool) (tr : List Lit) (c : Constraint) (l : Lit)
    (hA : Agrees a tr) (hn : AllNonneg c.terms)
    (hprop : Int.lt (slackWithout l tr c.terms) c.degree)
    (hH : Holds a c) : litVal a l = true :=
  @Bool.rec
    (fun z : Bool => (litVal a l = z) -> litVal a l = true)
    (fun hl =>
      False.elim
        (Int.lt_irrefl (slackWithout l tr c.terms)
          (Int.lt_of_lt_of_le (slackWithout l tr c.terms) c.degree
            (slackWithout l tr c.terms)
            hprop
            (Int.le_trans c.degree (evalTerms a c.terms) (slackWithout l tr c.terms)
              hH
              (evalTerms_le_slackWithout a l tr hA hl c.terms hn)))))
    (fun hl => hl)
    (litVal a l) rfl

def getG (neg : Constraint) (DB : List (Option Constraint)) (i : Nat) : Option Constraint :=
  match i with
  | Nat.zero   => some neg
  | Nat.succ j => getO DB j

theorem holdsG_get (a : Nat -> Bool) (neg : Constraint) (DB : List (Option Constraint))
    (hneg : Holds a neg) (hall : HoldsAllO a DB) (i : Nat) (c : Constraint)
    (hg : getG neg DB i = some c) : Holds a c :=
  @Nat.rec
    (fun i => getG neg DB i = some c -> Holds a c)
    (fun hg =>
      @Eq.subst Constraint (fun w : Constraint => Holds a w) neg c
        (someC_inj neg c hg) hneg)
    (fun j _ hg => holdsAllO_get a DB j c hall hg)
    i hg

inductive PropTrail (neg : Constraint) (DB : List (Option Constraint)) : List Lit -> Prop where
  | nil : PropTrail neg DB []
  | step : forall (tr : List Lit) (i : Nat) (c : Constraint) (l : Lit),
      PropTrail neg DB tr ->
      getG neg DB i = some c ->
      AllNonneg c.terms ->
      Int.lt (slackWithout l tr c.terms) c.degree ->
      PropTrail neg DB (l :: tr)

theorem trail_sound (neg : Constraint) (DB : List (Option Constraint)) (tr : List Lit)
    (ht : PropTrail neg DB tr) :
    forall a : Nat -> Bool, Holds a neg -> HoldsAllO a DB -> Agrees a tr :=
  @PropTrail.rec neg DB
    (fun tr _ => forall a : Nat -> Bool, Holds a neg -> HoldsAllO a DB -> Agrees a tr)
    (fun _ _ _ => True.intro)
    (fun tr i c l _ hg hnn hlt ih a hneg hall =>
      And.intro
        (propagated_lit_true a tr c l (ih a hneg hall) hnn hlt
          (holdsG_get a neg DB hneg hall i c hg))
        (ih a hneg hall))
    tr ht

theorem rup_conflict_unsat (neg : Constraint) (DB : List (Option Constraint))
    (tr : List Lit) (i : Nat) (cc : Constraint)
    (ht : PropTrail neg DB tr)
    (hg : getG neg DB i = some cc)
    (hnn : AllNonneg cc.terms)
    (hconf : Int.lt (slackTerms tr cc.terms) cc.degree) :
    forall a : Nat -> Bool, Holds a neg -> HoldsAllO a DB -> False :=
  fun a hneg hall =>
    no_model_of_conflict a tr cc (trail_sound neg DB tr ht a hneg hall) hnn hconf
      (holdsG_get a neg DB hneg hall i cc hg)

def DbEntailed (F : List Constraint) (DB : List (Option Constraint)) : Prop :=
  forall (i : Nat) (c : Constraint), getO DB i = some c -> Entails F c

theorem holdsAllO_of_entailed (F : List Constraint) (a : Nat -> Bool) (hF : HoldsAll a F)
    (DB : List (Option Constraint)) :
    DbEntailed F DB -> HoldsAllO a DB :=
  @List.rec (Option Constraint)
    (fun DB => DbEntailed F DB -> HoldsAllO a DB)
    (fun _ => True.intro)
    (fun o rest ih =>
      @Option.rec Constraint
        (fun o => DbEntailed F (o :: rest) -> HoldsAllO a (o :: rest))
        (fun hdb => ih (fun j c hg => hdb (Nat.succ j) c hg))
        (fun c' hdb =>
          And.intro (hdb Nat.zero c' rfl a hF)
            (ih (fun j c hg => hdb (Nat.succ j) c hg)))
        o)
    DB

theorem entails_of_rup (F : List Constraint) (DB : List (Option Constraint))
    (c : Constraint) (nd : Int) (tr : List Lit) (i : Nat) (cc : Constraint)
    (hdb : DbEntailed F DB)
    (hnd : nd + c.degree = coeffSum c.terms + 1)
    (ht : PropTrail (negC c nd) DB tr)
    (hg : getG (negC c nd) DB i = some cc)
    (hnn : AllNonneg cc.terms)
    (hconf : Int.lt (slackTerms tr cc.terms) cc.degree) :
    Entails F c :=
  fun a ha =>
    @Or.rec (Int.lt c.degree (evalTerms a c.terms))
        (Or (Eq c.degree (evalTerms a c.terms)) (Int.lt (evalTerms a c.terms) c.degree))
        (fun _ => Int.le c.degree (evalTerms a c.terms))
      (fun h => Int.le_of_lt c.degree (evalTerms a c.terms) h)
      (fun h =>
        @Or.rec (Eq c.degree (evalTerms a c.terms)) (Int.lt (evalTerms a c.terms) c.degree)
            (fun _ => Int.le c.degree (evalTerms a c.terms))
          (fun heq =>
            Eq.mpr (congrArg (fun z : Int => Int.le c.degree z) heq.symm)
              (Int.le_refl c.degree))
          (fun hlt =>
            False.elim
              (rup_conflict_unsat (negC c nd) DB tr i cc ht hg hnn hconf a
                (negC_holds_of_violated a c nd hnd hlt)
                (holdsAllO_of_entailed F a ha DB hdb)))
          h)
      (Int.lt_trichotomy c.degree (evalTerms a c.terms))

theorem lt_of_ble_succ (x d : Int) (h : Int.ble (x + 1) d = true) : Int.lt x d :=
  Int.le_of_ble_eq_true (x + 1) d h

theorem ctrl_slackWithout_unit :
    slackWithout ctrlX [] [({ coeff := 1, lit := ctrlX } : Term)] = 0 := rfl

theorem ctrl_slack_after_assign :
    slackTerms [ctrlX] [({ coeff := 1, lit := ctrlNotX } : Term)] = 0 := rfl

theorem ctrl_slack_no_assign :
    slackTerms [] [({ coeff := 1, lit := ctrlNotX } : Term)] = 1 := rfl

structure NormSt where
  ts : List Term
  delta : Int

def termVal (a : Nat -> Bool) (t : Term) : Int :=
  match litVal a t.lit with
  | true  => t.coeff
  | false => 0

def consSt (u : Term) (s : NormSt) : NormSt := { ts := u :: s.ts, delta := s.delta }

def insTerm (t : Term) (ts : List Term) : NormSt :=
  match ts with
  | [] => { ts := [t], delta := 0 }
  | u :: rest =>
    match Nat.beq u.lit.var t.lit.var with
    | true =>
      match boolEqB u.lit.negated t.lit.negated with
      | true  => { ts := ({ coeff := u.coeff + t.coeff, lit := u.lit } : Term) :: rest, delta := 0 }
      | false => { ts := ({ coeff := u.coeff - t.coeff, lit := u.lit } : Term) :: rest, delta := t.coeff }
    | false => consSt u (insTerm t rest)

def insSt (t : Term) (s : NormSt) : NormSt :=
  { ts := (insTerm t s.ts).ts, delta := s.delta + (insTerm t s.ts).delta }

def normIns (ts : List Term) : NormSt :=
  match ts with
  | [] => { ts := [], delta := 0 }
  | t :: rest => insSt t (normIns rest)

def flipDrop (ts : List Term) : NormSt :=
  match ts with
  | [] => { ts := [], delta := 0 }
  | t :: rest =>
    match Int.ble t.coeff 0 with
    | false => consSt t (flipDrop rest)
    | true =>
      match Int.ble 0 t.coeff with
      | true  => flipDrop rest
      | false =>
        { ts := ({ coeff := Int.neg t.coeff, lit := negLit t.lit } : Term) :: (flipDrop rest).ts,
          delta := t.coeff + (flipDrop rest).delta }

def normC (c : Constraint) : Constraint :=
  { terms := (flipDrop (normIns c.terms).ts).ts,
    degree := c.degree - ((normIns c.terms).delta + (flipDrop (normIns c.terms).ts).delta) }

def normF (F : List Constraint) : List Constraint :=
  match F with
  | [] => []
  | c :: rest => normC c :: normF rest

theorem eq_true_of_not_eq_false (x : Bool) (h : Bool.not x = false) : x = true :=
  @Bool.rec (fun y : Bool => Bool.not y = false -> y = true)
    (fun hy => Bool.noConfusion hy)
    (fun _ => rfl)
    x h

theorem boolEqB_false_not (b1 b2 : Bool) (h : boolEqB b1 b2 = false) : b2 = Bool.not b1 :=
  @Bool.rec
    (fun x : Bool =>
      (match x with
       | true  => b2
       | false => Bool.not b2) = false -> b2 = Bool.not x)
    (fun hh => eq_true_of_not_eq_false b2 hh)
    (fun hh => hh)
    b1 h

theorem neg_add_cancel (b : Int) : Int.neg b + b = 0 :=
  Eq.trans (Int.add_comm (Int.neg b) b) (Int.sub_self b)

theorem sub_add_cancel (x y : Int) : (x - y) + y = x :=
  Eq.trans (Int.add_assoc x (Int.neg y) y)
    (Eq.trans (congrArg (fun z : Int => x + z) (neg_add_cancel y)) (Int.add_zero x))

theorem neg_nonneg_of_nonpos (x : Int) (h : Int.le x 0) : Int.le 0 (Int.neg x) :=
  Eq.mpr
    (congrArg (fun z : Int => Int.NonNeg z)
      (Eq.trans (Int.add_zero (Int.neg x)) (Int.zero_add (Int.neg x)).symm))
    h

theorem add_swap_right (x y z : Int) : (x + y) + z = (x + z) + y :=
  Eq.trans (Int.add_assoc x y z)
    (Eq.trans (congrArg (fun w : Int => x + w) (Int.add_comm y z))
      (Int.add_assoc x z y).symm)

theorem add_mid_swap (x y z w : Int) : (x + y) + (z + w) = (x + z) + (y + w) :=
  Eq.trans (Int.add_assoc x y (z + w))
    (Eq.trans (congrArg (fun v : Int => x + v) (add_shuffle y z w))
      (Int.add_assoc x z (y + w)).symm)

theorem add_congr_left (x y z : Int) (h : x = y) : x + z = y + z :=
  congrArg (fun w : Int => w + z) h

theorem add_congr_right (x y z : Int) (h : x = y) : z + x = z + y :=
  congrArg (fun w : Int => z + w) h

theorem le_sub_of_le_add (d delta E2 : Int) (h : Int.le d (E2 + delta)) :
    Int.le (d - delta) E2 :=
  le_cancel_right (d - delta) delta E2
    (le_congr_left d ((d - delta) + delta) (E2 + delta) (sub_add_cancel d delta).symm h)

theorem le_add_of_sub_le (d delta E2 : Int) (h : Int.le (d - delta) E2) :
    Int.le d (E2 + delta) :=
  le_congr_left ((d - delta) + delta) d (E2 + delta) (sub_add_cancel d delta)
    (Int.add_le_add_right (d - delta) E2 h delta)

theorem evalTerms_cons (a : Nat -> Bool) (t : Term) (ts : List Term) :
    evalTerms a (t :: ts) = termVal a t + evalTerms a ts :=
  @Bool.rec
    (fun b : Bool =>
      (match b with
       | true  => t.coeff + evalTerms a ts
       | false => evalTerms a ts)
      = (match b with
         | true  => t.coeff
         | false => 0) + evalTerms a ts)
    (Int.zero_add (evalTerms a ts)).symm
    rfl
    (litVal a t.lit)

theorem termVal_zero (a : Nat -> Bool) (t : Term) (hc : t.coeff = 0) : termVal a t = 0 :=
  @Bool.rec
    (fun b : Bool =>
      (match b with
       | true  => t.coeff
       | false => 0) = 0)
    rfl
    hc
    (litVal a t.lit)

theorem termVal_pair (a : Nat -> Bool) (X Y : Int) (L : Lit) :
    termVal a ({ coeff := X + Y, lit := L } : Term)
      = termVal a ({ coeff := X, lit := L } : Term) + termVal a ({ coeff := Y, lit := L } : Term) :=
  @Bool.rec
    (fun b : Bool =>
      (match b with
       | true  => X + Y
       | false => 0)
      = (match b with
         | true  => X
         | false => 0) + (match b with
                          | true  => Y
                          | false => 0))
    (Int.add_zero 0).symm
    rfl
    (litVal a L)

theorem termVal_cancel (a : Nat -> Bool) (X Y : Int) (L : Lit) :
    termVal a ({ coeff := X - Y, lit := L } : Term) + Y
      = termVal a ({ coeff := X, lit := L } : Term)
        + termVal a ({ coeff := Y, lit := negLit L } : Term) :=
  Eq.mpr
    (congrArg
      (fun z : Bool =>
        (match litVal a L with
         | true  => X - Y
         | false => 0) + Y
        = (match litVal a L with
           | true  => X
           | false => 0) + (match z with
                            | true  => Y
                            | false => 0))
      (litVal_negLit a L))
    (@Bool.rec
      (fun b : Bool =>
        (match b with
         | true  => X - Y
         | false => 0) + Y
        = (match b with
           | true  => X
           | false => 0) + (match Bool.not b with
                            | true  => Y
                            | false => 0))
      rfl
      (Eq.trans (sub_add_cancel X Y) (Int.add_zero X).symm)
      (litVal a L))

theorem termVal_lit_congr (a : Nat -> Bool) (X : Int) (L1 L2 : Lit) (h : L1 = L2) :
    termVal a ({ coeff := X, lit := L1 } : Term)
      = termVal a ({ coeff := X, lit := L2 } : Term) :=
  congrArg (fun L : Lit => termVal a ({ coeff := X, lit := L } : Term)) h

theorem termVal_flip (a : Nat -> Bool) (Y : Int) (L : Lit) :
    termVal a ({ coeff := Int.neg Y, lit := negLit L } : Term) + Y
      = termVal a ({ coeff := Y, lit := L } : Term) :=
  Eq.mpr
    (congrArg
      (fun z : Bool =>
        (match z with
         | true  => Int.neg Y
         | false => 0) + Y
        = (match litVal a L with
           | true  => Y
           | false => 0))
      (litVal_negLit a L))
    (@Bool.rec
      (fun b : Bool =>
        (match Bool.not b with
         | true  => Int.neg Y
         | false => 0) + Y
        = (match b with
           | true  => Y
           | false => 0))
      (neg_add_cancel Y)
      (Int.zero_add Y)
      (litVal a L))

theorem insTerm_eval_mismatch (a : Nat -> Bool) (t u : Term) (rest : List Term)
    (ih : evalTerms a (insTerm t rest).ts + (insTerm t rest).delta
      = evalTerms a rest + termVal a t) :
    evalTerms a (u :: (insTerm t rest).ts) + (insTerm t rest).delta
      = evalTerms a (u :: rest) + termVal a t :=
  Eq.trans
    (congrArg (fun z : Int => z + (insTerm t rest).delta)
      (evalTerms_cons a u (insTerm t rest).ts))
    (Eq.trans
      (Int.add_assoc (termVal a u) (evalTerms a (insTerm t rest).ts) (insTerm t rest).delta)
      (Eq.trans
        (congrArg (fun z : Int => termVal a u + z) ih)
        (Eq.trans
          (Int.add_assoc (termVal a u) (evalTerms a rest) (termVal a t)).symm
          (congrArg (fun z : Int => z + termVal a t) (evalTerms_cons a u rest).symm))))

theorem insTerm_eval_merge (a : Nat -> Bool) (t u : Term) (rest : List Term)
    (hlit : u.lit = t.lit) :
    evalTerms a (({ coeff := u.coeff + t.coeff, lit := u.lit } : Term) :: rest) + 0
      = evalTerms a (u :: rest) + termVal a t :=
  Eq.trans
    (Int.add_zero (evalTerms a (({ coeff := u.coeff + t.coeff, lit := u.lit } : Term) :: rest)))
    (Eq.trans
      (evalTerms_cons a ({ coeff := u.coeff + t.coeff, lit := u.lit } : Term) rest)
      (Eq.trans
        (add_congr_left
          (termVal a ({ coeff := u.coeff + t.coeff, lit := u.lit } : Term))
          (termVal a ({ coeff := u.coeff, lit := u.lit } : Term)
            + termVal a ({ coeff := t.coeff, lit := t.lit } : Term))
          (evalTerms a rest)
          (Eq.trans
            (termVal_pair a u.coeff t.coeff u.lit)
            (add_congr_right
              (termVal a ({ coeff := t.coeff, lit := u.lit } : Term))
              (termVal a ({ coeff := t.coeff, lit := t.lit } : Term))
              (termVal a ({ coeff := u.coeff, lit := u.lit } : Term))
              (termVal_lit_congr a t.coeff u.lit t.lit hlit))))
        (Eq.trans
          (add_swap_right (termVal a u) (termVal a t) (evalTerms a rest))
          (add_congr_left (termVal a u + evalTerms a rest) (evalTerms a (u :: rest))
            (termVal a t) (evalTerms_cons a u rest).symm))))

theorem insTerm_eval_cancel (a : Nat -> Bool) (t u : Term) (rest : List Term)
    (hlit : t.lit = negLit u.lit) :
    evalTerms a (({ coeff := u.coeff - t.coeff, lit := u.lit } : Term) :: rest) + t.coeff
      = evalTerms a (u :: rest) + termVal a t :=
  Eq.trans
    (congrArg (fun z : Int => z + t.coeff)
      (evalTerms_cons a ({ coeff := u.coeff - t.coeff, lit := u.lit } : Term) rest))
    (Eq.trans
      (add_swap_right (termVal a ({ coeff := u.coeff - t.coeff, lit := u.lit } : Term))
        (evalTerms a rest) t.coeff)
      (Eq.trans
        (congrArg (fun z : Int => z + evalTerms a rest)
          (Eq.trans
            (termVal_cancel a u.coeff t.coeff u.lit)
            (congrArg
              (fun L : Lit =>
                termVal a ({ coeff := u.coeff, lit := u.lit } : Term)
                  + termVal a ({ coeff := t.coeff, lit := L } : Term))
              hlit.symm)))
        (Eq.trans
          (add_swap_right (termVal a u) (termVal a t) (evalTerms a rest))
          (congrArg (fun z : Int => z + termVal a t) (evalTerms_cons a u rest).symm))))

theorem insTerm_nil_arith (c e : Int) : (c + e) + 0 = e + c :=
  Eq.trans (Int.add_zero (c + e)) (Int.add_comm c e)

theorem insTerm_eval_nil (a : Nat -> Bool) (t : Term) :
    evalTerms a (insTerm t ([] : List Term)).ts + (insTerm t ([] : List Term)).delta
      = evalTerms a ([] : List Term) + termVal a t :=
  @Bool.rec
    (fun b : Bool =>
      (match b with
       | true  => t.coeff + evalTerms a ([] : List Term)
       | false => evalTerms a ([] : List Term)) + 0
      = evalTerms a ([] : List Term) + (match b with
                                        | true  => t.coeff
                                        | false => 0))
    rfl
    (insTerm_nil_arith t.coeff (evalTerms a ([] : List Term)))
    (litVal a t.lit)

theorem insTerm_eval_cons (a : Nat -> Bool) (t u : Term) (rest : List Term)
    (ih : evalTerms a (insTerm t rest).ts + (insTerm t rest).delta
      = evalTerms a rest + termVal a t) :
    evalTerms a (insTerm t (u :: rest)).ts + (insTerm t (u :: rest)).delta
      = evalTerms a (u :: rest) + termVal a t :=
  @Bool.rec
        (fun b : Bool => (Nat.beq u.lit.var t.lit.var = b) ->
          evalTerms a (NormSt.ts (match b with
            | true =>
              match boolEqB u.lit.negated t.lit.negated with
              | true  => ({ ts := ({ coeff := u.coeff + t.coeff, lit := u.lit } : Term) :: rest,
                            delta := 0 } : NormSt)
              | false => ({ ts := ({ coeff := u.coeff - t.coeff, lit := u.lit } : Term) :: rest,
                            delta := t.coeff } : NormSt)
            | false => consSt u (insTerm t rest)))
          + NormSt.delta (match b with
            | true =>
              match boolEqB u.lit.negated t.lit.negated with
              | true  => ({ ts := ({ coeff := u.coeff + t.coeff, lit := u.lit } : Term) :: rest,
                            delta := 0 } : NormSt)
              | false => ({ ts := ({ coeff := u.coeff - t.coeff, lit := u.lit } : Term) :: rest,
                            delta := t.coeff } : NormSt)
            | false => consSt u (insTerm t rest))
          = evalTerms a (u :: rest) + termVal a t)
        (fun _ => insTerm_eval_mismatch a t u rest ih)
        (fun hv =>
          @Bool.rec
            (fun b2 : Bool => (boolEqB u.lit.negated t.lit.negated = b2) ->
              evalTerms a (NormSt.ts (match b2 with
                | true  => ({ ts := ({ coeff := u.coeff + t.coeff, lit := u.lit } : Term) :: rest,
                              delta := 0 } : NormSt)
                | false => ({ ts := ({ coeff := u.coeff - t.coeff, lit := u.lit } : Term) :: rest,
                              delta := t.coeff } : NormSt)))
              + NormSt.delta (match b2 with
                | true  => ({ ts := ({ coeff := u.coeff + t.coeff, lit := u.lit } : Term) :: rest,
                              delta := 0 } : NormSt)
                | false => ({ ts := ({ coeff := u.coeff - t.coeff, lit := u.lit } : Term) :: rest,
                              delta := t.coeff } : NormSt))
              = evalTerms a (u :: rest) + termVal a t)
            (fun hb => insTerm_eval_cancel a t u rest
              (mkLit_congr t.lit.var u.lit.var t.lit.negated (Bool.not u.lit.negated)
                (Nat.eq_of_beq_eq_true u.lit.var t.lit.var hv).symm
                (boolEqB_false_not u.lit.negated t.lit.negated hb)))
            (fun hb => insTerm_eval_merge a t u rest
              (mkLit_congr u.lit.var t.lit.var u.lit.negated t.lit.negated
                (Nat.eq_of_beq_eq_true u.lit.var t.lit.var hv)
                (boolEqB_sound u.lit.negated t.lit.negated hb)))
            (boolEqB u.lit.negated t.lit.negated) rfl)
        (Nat.beq u.lit.var t.lit.var) rfl

theorem insTerm_eval (a : Nat -> Bool) (t : Term) (ts : List Term) :
    evalTerms a (insTerm t ts).ts + (insTerm t ts).delta = evalTerms a ts + termVal a t :=
  @List.rec Term
    (fun ts => evalTerms a (insTerm t ts).ts + (insTerm t ts).delta
      = evalTerms a ts + termVal a t)
    (insTerm_eval_nil a t)
    (fun u rest ih => insTerm_eval_cons a t u rest ih)
    ts

theorem normIns_step_arith (Ei di dn En E T : Int)
    (hIns : Ei + di = En + T) (ih : En + dn = E) :
    Ei + (dn + di) = T + E :=
  Eq.trans (add_congr_right (dn + di) (di + dn) Ei (Int.add_comm dn di))
    (Eq.trans (Int.add_assoc Ei di dn).symm
      (Eq.trans (add_congr_left (Ei + di) (En + T) dn hIns)
        (Eq.trans (add_swap_right En T dn)
          (Eq.trans (add_congr_left (En + dn) E T ih)
            (Int.add_comm E T)))))

theorem normIns_eval (a : Nat -> Bool) (ts : List Term) :
    evalTerms a (normIns ts).ts + (normIns ts).delta = evalTerms a ts :=
  @List.rec Term
    (fun ts => evalTerms a (normIns ts).ts + (normIns ts).delta = evalTerms a ts)
    (Int.add_zero 0)
    (fun t rest ih =>
      Eq.trans
        (normIns_step_arith
          (evalTerms a (insTerm t (normIns rest).ts).ts)
          (insTerm t (normIns rest).ts).delta
          (normIns rest).delta
          (evalTerms a (normIns rest).ts)
          (evalTerms a rest)
          (termVal a t)
          (insTerm_eval a t (normIns rest).ts)
          ih)
        (evalTerms_cons a t rest).symm)
    ts

theorem flipDrop_eval_keep (a : Nat -> Bool) (t : Term) (rest : List Term)
    (ih : evalTerms a (flipDrop rest).ts + (flipDrop rest).delta = evalTerms a rest) :
    evalTerms a (t :: (flipDrop rest).ts) + (flipDrop rest).delta = evalTerms a (t :: rest) :=
  Eq.trans
    (congrArg (fun z : Int => z + (flipDrop rest).delta) (evalTerms_cons a t (flipDrop rest).ts))
    (Eq.trans
      (Int.add_assoc (termVal a t) (evalTerms a (flipDrop rest).ts) (flipDrop rest).delta)
      (Eq.trans
        (congrArg (fun z : Int => termVal a t + z) ih)
        (evalTerms_cons a t rest).symm))

theorem flipDrop_eval_drop (a : Nat -> Bool) (t : Term) (rest : List Term)
    (hc : t.coeff = 0)
    (ih : evalTerms a (flipDrop rest).ts + (flipDrop rest).delta = evalTerms a rest) :
    evalTerms a (flipDrop rest).ts + (flipDrop rest).delta = evalTerms a (t :: rest) :=
  Eq.trans ih
    (Eq.trans (Int.zero_add (evalTerms a rest)).symm
      (Eq.trans
        (congrArg (fun z : Int => z + evalTerms a rest) (termVal_zero a t hc).symm)
        (evalTerms_cons a t rest).symm))

theorem flipDrop_eval_flip (a : Nat -> Bool) (t : Term) (rest : List Term)
    (ih : evalTerms a (flipDrop rest).ts + (flipDrop rest).delta = evalTerms a rest) :
    evalTerms a (({ coeff := Int.neg t.coeff, lit := negLit t.lit } : Term) :: (flipDrop rest).ts)
      + (t.coeff + (flipDrop rest).delta)
      = evalTerms a (t :: rest) :=
  Eq.trans
    (congrArg (fun z : Int => z + (t.coeff + (flipDrop rest).delta))
      (evalTerms_cons a ({ coeff := Int.neg t.coeff, lit := negLit t.lit } : Term)
        (flipDrop rest).ts))
    (Eq.trans
      (add_mid_swap (termVal a ({ coeff := Int.neg t.coeff, lit := negLit t.lit } : Term))
        (evalTerms a (flipDrop rest).ts) t.coeff (flipDrop rest).delta)
      (Eq.trans
        (congrArg (fun z : Int => z + (evalTerms a (flipDrop rest).ts + (flipDrop rest).delta))
          (termVal_flip a t.coeff t.lit))
        (Eq.trans
          (congrArg (fun z : Int => termVal a t + z) ih)
          (evalTerms_cons a t rest).symm)))

theorem flipDrop_eval (a : Nat -> Bool) (ts : List Term) :
    evalTerms a (flipDrop ts).ts + (flipDrop ts).delta = evalTerms a ts :=
  @List.rec Term
    (fun ts => evalTerms a (flipDrop ts).ts + (flipDrop ts).delta = evalTerms a ts)
    (Int.add_zero 0)
    (fun t rest ih =>
      @Bool.rec
        (fun b : Bool => (Int.ble t.coeff 0 = b) ->
          evalTerms a (NormSt.ts (match b with
            | false => consSt t (flipDrop rest)
            | true =>
              match Int.ble 0 t.coeff with
              | true  => flipDrop rest
              | false =>
                ({ ts := ({ coeff := Int.neg t.coeff, lit := negLit t.lit } : Term)
                            :: (flipDrop rest).ts,
                   delta := t.coeff + (flipDrop rest).delta } : NormSt)))
          + NormSt.delta (match b with
            | false => consSt t (flipDrop rest)
            | true =>
              match Int.ble 0 t.coeff with
              | true  => flipDrop rest
              | false =>
                ({ ts := ({ coeff := Int.neg t.coeff, lit := negLit t.lit } : Term)
                            :: (flipDrop rest).ts,
                   delta := t.coeff + (flipDrop rest).delta } : NormSt))
          = evalTerms a (t :: rest))
        (fun _ => flipDrop_eval_keep a t rest ih)
        (fun hb1 =>
          @Bool.rec
            (fun b2 : Bool => (Int.ble 0 t.coeff = b2) ->
              evalTerms a (NormSt.ts (match b2 with
                | true  => flipDrop rest
                | false =>
                  ({ ts := ({ coeff := Int.neg t.coeff, lit := negLit t.lit } : Term)
                              :: (flipDrop rest).ts,
                     delta := t.coeff + (flipDrop rest).delta } : NormSt)))
              + NormSt.delta (match b2 with
                | true  => flipDrop rest
                | false =>
                  ({ ts := ({ coeff := Int.neg t.coeff, lit := negLit t.lit } : Term)
                              :: (flipDrop rest).ts,
                     delta := t.coeff + (flipDrop rest).delta } : NormSt))
              = evalTerms a (t :: rest))
            (fun _ => flipDrop_eval_flip a t rest ih)
            (fun hb2 => flipDrop_eval_drop a t rest
              (Int.le_antisymm t.coeff 0
                (Int.le_of_ble_eq_true t.coeff 0 hb1)
                (Int.le_of_ble_eq_true 0 t.coeff hb2))
              ih)
            (Int.ble 0 t.coeff) rfl)
        (Int.ble t.coeff 0) rfl)
    ts

theorem flipDrop_nonneg (ts : List Term) : AllNonneg (flipDrop ts).ts :=
  @List.rec Term
    (fun ts => AllNonneg (flipDrop ts).ts)
    True.intro
    (fun t rest ih =>
      @Bool.rec
        (fun b : Bool => (Int.ble t.coeff 0 = b) ->
          AllNonneg (NormSt.ts (match b with
            | false => consSt t (flipDrop rest)
            | true =>
              match Int.ble 0 t.coeff with
              | true  => flipDrop rest
              | false =>
                ({ ts := ({ coeff := Int.neg t.coeff, lit := negLit t.lit } : Term)
                            :: (flipDrop rest).ts,
                   delta := t.coeff + (flipDrop rest).delta } : NormSt))))
        (fun hb1 => And.intro (le_of_ble_eq_false t.coeff 0 hb1) ih)
        (fun _ =>
          @Bool.rec
            (fun b2 : Bool => (Int.ble 0 t.coeff = b2) ->
              AllNonneg (NormSt.ts (match b2 with
                | true  => flipDrop rest
                | false =>
                  ({ ts := ({ coeff := Int.neg t.coeff, lit := negLit t.lit } : Term)
                              :: (flipDrop rest).ts,
                     delta := t.coeff + (flipDrop rest).delta } : NormSt))))
            (fun hb2 => And.intro
              (neg_nonneg_of_nonpos t.coeff (le_of_ble_eq_false 0 t.coeff hb2))
              ih)
            (fun _ => ih)
            (Int.ble 0 t.coeff) rfl)
        (Int.ble t.coeff 0) rfl)
    ts

theorem normC_nonneg (c : Constraint) : AllNonneg (normC c).terms :=
  flipDrop_nonneg (normIns c.terms).ts

theorem normFull_eval (a : Nat -> Bool) (ts : List Term) :
    evalTerms a (flipDrop (normIns ts).ts).ts
      + ((normIns ts).delta + (flipDrop (normIns ts).ts).delta)
      = evalTerms a ts :=
  Eq.trans
    (congrArg (fun z : Int => evalTerms a (flipDrop (normIns ts).ts).ts + z)
      (Int.add_comm (normIns ts).delta (flipDrop (normIns ts).ts).delta))
    (Eq.trans
      (Int.add_assoc (evalTerms a (flipDrop (normIns ts).ts).ts)
        (flipDrop (normIns ts).ts).delta (normIns ts).delta).symm
      (Eq.trans
        (congrArg (fun z : Int => z + (normIns ts).delta) (flipDrop_eval a (normIns ts).ts))
        (normIns_eval a ts)))

theorem holds_normC_of_holds (a : Nat -> Bool) (c : Constraint) (h : Holds a c) :
    Holds a (normC c) :=
  le_sub_of_le_add c.degree
    ((normIns c.terms).delta + (flipDrop (normIns c.terms).ts).delta)
    (evalTerms a (flipDrop (normIns c.terms).ts).ts)
    (le_congr_right (evalTerms a c.terms)
      (evalTerms a (flipDrop (normIns c.terms).ts).ts
        + ((normIns c.terms).delta + (flipDrop (normIns c.terms).ts).delta))
      c.degree
      (normFull_eval a c.terms).symm
      h)

theorem holds_of_holds_normC (a : Nat -> Bool) (c : Constraint) (h : Holds a (normC c)) :
    Holds a c :=
  le_congr_right
    (evalTerms a (flipDrop (normIns c.terms).ts).ts
      + ((normIns c.terms).delta + (flipDrop (normIns c.terms).ts).delta))
    (evalTerms a c.terms)
    c.degree
    (normFull_eval a c.terms)
    (le_add_of_sub_le c.degree
      ((normIns c.terms).delta + (flipDrop (normIns c.terms).ts).delta)
      (evalTerms a (flipDrop (normIns c.terms).ts).ts)
      h)

theorem entails_normC (F : List Constraint) (c : Constraint) (h : Entails F c) :
    Entails F (normC c) :=
  fun a ha => holds_normC_of_holds a c (h a ha)

theorem entails_of_normC (F : List Constraint) (c : Constraint) (h : Entails F (normC c)) :
    Entails F c :=
  fun a ha => holds_of_holds_normC a c (h a ha)

theorem holdsAll_normF_of_holdsAll (a : Nat -> Bool) (F : List Constraint)
    (h : HoldsAll a F) : HoldsAll a (normF F) :=
  @List.rec Constraint
    (fun F => HoldsAll a F -> HoldsAll a (normF F))
    (fun _ => True.intro)
    (fun c rest ih hh => And.intro (holds_normC_of_holds a c hh.left) (ih hh.right))
    F h

theorem holdsAll_of_holdsAll_normF (a : Nat -> Bool) (F : List Constraint)
    (h : HoldsAll a (normF F)) : HoldsAll a F :=
  @List.rec Constraint
    (fun F => HoldsAll a (normF F) -> HoldsAll a F)
    (fun _ => True.intro)
    (fun c rest ih hh => And.intro (holds_of_holds_normC a c hh.left) (ih hh.right))
    F h

theorem unsat_of_normF_unsat (F : List Constraint) (hU : Unsat (normF F)) : Unsat F :=
  fun a ha => hU a (holdsAll_normF_of_holdsAll a F ha)

theorem entails_of_normC_eq (F : List Constraint) (c1 c2 : Constraint)
    (heq : normC c1 = normC c2) (h : Entails F c1) : Entails F c2 :=
  entails_of_normC F c2
    (@Eq.subst Constraint (fun w : Constraint => Entails F w) (normC c1) (normC c2)
      heq (entails_normC F c1 h))

theorem ctrl_norm_merge_terms :
    (normC ({ terms := [({ coeff := 2, lit := ctrlX } : Term),
                        ({ coeff := 3, lit := ctrlX } : Term)],
              degree := 4 } : Constraint)).terms
      = [({ coeff := 5, lit := ctrlX } : Term)] := rfl

theorem ctrl_norm_merge_degree :
    (normC ({ terms := [({ coeff := 2, lit := ctrlX } : Term),
                        ({ coeff := 3, lit := ctrlX } : Term)],
              degree := 4 } : Constraint)).degree = 4 := rfl

theorem ctrl_norm_cancel_terms :
    (normC ({ terms := [({ coeff := 1, lit := ctrlX } : Term),
                        ({ coeff := 1, lit := ctrlNotX } : Term)],
              degree := 1 } : Constraint)).terms = ([] : List Term) := rfl

theorem ctrl_norm_cancel_degree :
    (normC ({ terms := [({ coeff := 1, lit := ctrlX } : Term),
                        ({ coeff := 1, lit := ctrlNotX } : Term)],
              degree := 1 } : Constraint)).degree = 0 := rfl

theorem ctrl_norm_flip_terms :
    (normC ({ terms := [({ coeff := Int.neg 2, lit := ctrlX } : Term)],
              degree := 1 } : Constraint)).terms
      = [({ coeff := 2, lit := ctrlNotX } : Term)] := rfl

theorem ctrl_norm_flip_degree :
    (normC ({ terms := [({ coeff := Int.neg 2, lit := ctrlX } : Term)],
              degree := 1 } : Constraint)).degree = 3 := rfl

structure NatDivMod where
  q : Nat
  r : Nat

def natDivModGo (fuel : Nat) (n : Nat) (k : Nat) : NatDivMod :=
  match fuel with
  | Nat.zero => { q := Nat.zero, r := n }
  | Nat.succ f =>
    match Nat.ble k n with
    | true  => { q := Nat.succ (natDivModGo f (Nat.sub n k) k).q,
                 r := (natDivModGo f (Nat.sub n k) k).r }
    | false => { q := Nat.zero, r := n }

def natDivMod (n k : Nat) : NatDivMod := natDivModGo n n k

def dmSpec (n k : Nat) (d : NatDivMod) : Prop :=
  And (Nat.add (Nat.mul d.q k) d.r = n) (Nat.lt d.r k)

theorem nat_eq_zero_of_le_zero (n : Nat) (h : Nat.le n Nat.zero) : n = Nat.zero :=
  Nat.le_antisymm n Nat.zero h (Nat.zero_le n)

theorem nat_lt_of_ble_eq_false (k n : Nat) (hb : Nat.ble k n = false) : Nat.lt n k :=
  Iff.mp (Nat.not_le k n) (Nat.not_le_of_ble_eq_false k n hb)

theorem divmod_step_arith (k n q r : Nat) (hkn : Nat.le k n)
    (heq : Nat.add (Nat.mul q k) r = Nat.sub n k) :
    Nat.add (Nat.mul (Nat.succ q) k) r = n :=
  Eq.trans (congrArg (fun w : Nat => Nat.add w r) (Nat.succ_mul q k))
    (Eq.trans (Nat.add_assoc k (Nat.mul q k) r)
      (Eq.trans (congrArg (fun w : Nat => Nat.add k w) heq)
        (Eq.trans (Nat.add_comm k (Nat.sub n k))
          (Nat.divmodAux.sub_add_cancel n k hkn))))

theorem natDivModGo_spec (k : Nat) (hk : Nat.le 1 k) (fuel : Nat) :
    forall (n : Nat), Nat.le n fuel -> dmSpec n k (natDivModGo fuel n k) :=
  @Nat.rec
    (fun fuel : Nat =>
      forall (n : Nat), Nat.le n fuel -> dmSpec n k (natDivModGo fuel n k))
    (fun n hn =>
      Eq.mpr
        (congrArg (fun z : Nat => dmSpec z k ({ q := Nat.zero, r := z } : NatDivMod))
          (nat_eq_zero_of_le_zero n hn))
        (And.intro (Nat.zero_mul k) hk))
    (fun f ih n hn =>
      @Bool.rec
        (fun b : Bool =>
          (Nat.ble k n = b) ->
          dmSpec n k (match b with
            | true  => ({ q := Nat.succ (natDivModGo f (Nat.sub n k) k).q,
                          r := (natDivModGo f (Nat.sub n k) k).r } : NatDivMod)
            | false => ({ q := Nat.zero, r := n } : NatDivMod)))
        (fun hb =>
          And.intro
            (Eq.trans (congrArg (fun w : Nat => Nat.add w n) (Nat.zero_mul k))
              (Nat.zero_add n))
            (nat_lt_of_ble_eq_false k n hb))
        (fun hb =>
          (fun (hkn : Nat.le k n) =>
            (fun (hsf : Nat.le (Nat.sub n k) f) =>
              (fun (ihr : dmSpec (Nat.sub n k) k (natDivModGo f (Nat.sub n k) k)) =>
                And.intro
                  (divmod_step_arith k n (natDivModGo f (Nat.sub n k) k).q
                    (natDivModGo f (Nat.sub n k) k).r hkn ihr.left)
                  ihr.right)
              (ih (Nat.sub n k) hsf))
            (Nat.le_of_succ_le_succ (Nat.sub n k) f
              (Nat.le_trans (Nat.sub_lt n k (Nat.le_trans hk hkn) hk) hn)))
          (Nat.le_of_ble_eq_true k n hb))
        (Nat.ble k n)
        rfl)
    fuel

theorem natDivMod_spec_eq (n k : Nat) (hk : Nat.le 1 k) :
    Nat.add (Nat.mul (natDivMod n k).q k) (natDivMod n k).r = n :=
  (natDivModGo_spec k hk n n (Nat.le_refl n)).left

theorem natDivMod_spec_lt (n k : Nat) (hk : Nat.le 1 k) :
    Nat.lt (natDivMod n k).r k :=
  (natDivModGo_spec k hk n n (Nat.le_refl n)).right

def natCeilDiv (n k : Nat) : Nat :=
  match Nat.beq (natDivMod n k).r Nat.zero with
  | true  => (natDivMod n k).q
  | false => Nat.succ (natDivMod n k).q

theorem nat_le_congr_left (x y z : Nat) (heq : x = y) (h : Nat.le x z) : Nat.le y z :=
  @Eq.subst Nat (fun w : Nat => Nat.le w z) x y heq h

theorem nat_le_congr_right (x y z : Nat) (heq : x = y) (h : Nat.le z x) : Nat.le z y :=
  @Eq.subst Nat (fun w : Nat => Nat.le z w) x y heq h

theorem nat_add_congr_left (x y z : Nat) (h : x = y) : Nat.add x z = Nat.add y z :=
  congrArg (fun w : Nat => Nat.add w z) h

theorem ceil_ge_exact (n k q r : Nat)
    (heq : Nat.add (Nat.mul q k) r = n) (hr0 : r = Nat.zero) :
    Nat.le n (Nat.mul q k) :=
  Eq.mpr
    (congrArg (fun w : Nat => Nat.le n w)
      (Eq.trans (congrArg (fun w : Nat => Nat.add (Nat.mul q k) w) hr0).symm heq))
    (Nat.le_refl n)

theorem ceil_ge_up (n k q r : Nat)
    (heq : Nat.add (Nat.mul q k) r = n) (hlt : Nat.lt r k) :
    Nat.le n (Nat.mul (Nat.succ q) k) :=
  nat_le_congr_right (Nat.add (Nat.mul q k) k) (Nat.mul (Nat.succ q) k) n
    (Eq.trans (Nat.add_comm (Nat.mul q k) k) (Nat.succ_mul q k).symm)
    (nat_le_congr_left (Nat.add (Nat.mul q k) r) n (Nat.add (Nat.mul q k) k) heq
      (Nat.add_le_add_left r k (Nat.le_of_lt hlt) (Nat.mul q k)))

theorem ceil_min_exact (n k q r : Nat) (hk : Nat.le 1 k)
    (heq : Nat.add (Nat.mul q k) r = n) (hr0 : r = Nat.zero) :
    Nat.lt (Nat.mul q k) (Nat.add n k) :=
  Eq.mpr
    (congrArg (fun w : Nat => Nat.lt w (Nat.add n k))
      (Eq.trans (congrArg (fun w : Nat => Nat.add (Nat.mul q k) w) hr0).symm heq))
    (Nat.add_le_add_left 1 k hk n)

theorem ceil_min_up (n k q r : Nat)
    (heq : Nat.add (Nat.mul q k) r = n) (h1r : Nat.le 1 r) :
    Nat.lt (Nat.mul (Nat.succ q) k) (Nat.add n k) :=
  nat_le_congr_left (Nat.succ (Nat.add k (Nat.mul q k)))
    (Nat.succ (Nat.mul (Nat.succ q) k)) (Nat.add n k)
    (congrArg Nat.succ (Nat.succ_mul q k).symm)
    (nat_le_congr_right (Nat.add (Nat.add (Nat.mul q k) r) k) (Nat.add n k)
      (Nat.succ (Nat.add k (Nat.mul q k)))
      (nat_add_congr_left (Nat.add (Nat.mul q k) r) n k heq)
      (nat_le_congr_left (Nat.add (Nat.add (Nat.mul q k) 1) k)
        (Nat.succ (Nat.add k (Nat.mul q k)))
        (Nat.add (Nat.add (Nat.mul q k) r) k)
        (Eq.trans (Nat.add_assoc (Nat.mul q k) 1 k)
          (Eq.trans (congrArg (fun w : Nat => Nat.add (Nat.mul q k) w) (Nat.add_comm 1 k))
            (Eq.trans (Nat.add_assoc (Nat.mul q k) k 1).symm
              (congrArg Nat.succ (Nat.add_comm (Nat.mul q k) k)))))
        (Nat.add_le_add_right (Nat.add (Nat.mul q k) 1) (Nat.add (Nat.mul q k) r)
          (Nat.add_le_add_left 1 r h1r (Nat.mul q k)) k)))

theorem one_le_of_beq_zero_false (m : Nat) (hb : Nat.beq m Nat.zero = false) :
    Nat.le 1 m :=
  @Nat.rec (fun m : Nat => Nat.beq m Nat.zero = false -> Nat.le 1 m)
    (fun hb => Bool.noConfusion hb)
    (fun m _ _ => Nat.succ_le_succ (Nat.zero_le m))
    m hb

theorem natCeilDiv_ge (n k : Nat) (hk : Nat.le 1 k) :
    Nat.le n (Nat.mul (natCeilDiv n k) k) :=
  @Bool.rec
    (fun b : Bool =>
      (Nat.beq (natDivMod n k).r Nat.zero = b) ->
      Nat.le n (Nat.mul (match b with
        | true  => (natDivMod n k).q
        | false => Nat.succ (natDivMod n k).q) k))
    (fun hb =>
      ceil_ge_up n k (natDivMod n k).q (natDivMod n k).r
        (natDivMod_spec_eq n k hk) (natDivMod_spec_lt n k hk))
    (fun hb =>
      ceil_ge_exact n k (natDivMod n k).q (natDivMod n k).r
        (natDivMod_spec_eq n k hk)
        (Nat.eq_of_beq_eq_true (natDivMod n k).r Nat.zero hb))
    (Nat.beq (natDivMod n k).r Nat.zero)
    rfl

theorem natCeilDiv_min (n k : Nat) (hk : Nat.le 1 k) :
    Nat.lt (Nat.mul (natCeilDiv n k) k) (Nat.add n k) :=
  @Bool.rec
    (fun b : Bool =>
      (Nat.beq (natDivMod n k).r Nat.zero = b) ->
      Nat.lt (Nat.mul (match b with
        | true  => (natDivMod n k).q
        | false => Nat.succ (natDivMod n k).q) k) (Nat.add n k))
    (fun hb =>
      ceil_min_up n k (natDivMod n k).q (natDivMod n k).r
        (natDivMod_spec_eq n k hk)
        (one_le_of_beq_zero_false (natDivMod n k).r hb))
    (fun hb =>
      ceil_min_exact n k (natDivMod n k).q (natDivMod n k).r hk
        (natDivMod_spec_eq n k hk)
        (Nat.eq_of_beq_eq_true (natDivMod n k).r Nat.zero hb))
    (Nat.beq (natDivMod n k).r Nat.zero)
    rfl

theorem int_zero_le_ofNat (n : Nat) : Int.le 0 (Int.ofNat n) :=
  Int.NonNeg.mk n

theorem int_ofNat_le_ofNat (a b : Nat) (h : Nat.le a b) :
    Int.le (Int.ofNat a) (Int.ofNat b) :=
  le_congr_right (Int.add (Int.ofNat (Nat.sub b a)) (Int.ofNat a)) (Int.ofNat b)
    (Int.ofNat a)
    (congrArg Int.ofNat (Nat.divmodAux.sub_add_cancel b a h))
    (le_add_left_of_nonneg (Int.ofNat (Nat.sub b a)) (Int.ofNat a)
      (int_zero_le_ofNat (Nat.sub b a)))

theorem int_ofNat_lt_ofNat (a b : Nat) (h : Nat.lt a b) :
    Int.lt (Int.ofNat a) (Int.ofNat b) :=
  int_ofNat_le_ofNat (Nat.succ a) b h

theorem int_neg_le_neg (A B : Int) (h : Int.le A B) :
    Int.le (Int.neg B) (Int.neg A) :=
  le_cancel_right (Int.neg B) (Int.add A B) (Int.neg A)
    (le_congr_right B (Int.add (Int.neg A) (Int.add A B)) (Int.add (Int.neg B) (Int.add A B))
      (Eq.trans (Int.add_assoc (Int.neg A) A B).symm
        (Eq.trans (congrArg (fun w : Int => Int.add w B) (neg_add_cancel A))
          (Int.zero_add B))).symm
      (le_congr_left A (Int.add (Int.neg B) (Int.add A B)) B
        (Eq.trans (congrArg (fun w : Int => Int.add (Int.neg B) w) (Int.add_comm A B))
          (Eq.trans (Int.add_assoc (Int.neg B) B A).symm
            (Eq.trans (congrArg (fun w : Int => Int.add w A) (neg_add_cancel B))
              (Int.zero_add A)))).symm
        h))

theorem int_neg_lt_of_lt_add (A B C : Int) (h : Int.lt A (Int.add B C)) :
    Int.lt (Int.neg B) (Int.add (Int.neg A) C) :=
  le_cancel_right (Int.add (Int.neg B) 1) (Int.add A B) (Int.add (Int.neg A) C)
    (le_congr_right (Int.add B C) (Int.add (Int.add (Int.neg A) C) (Int.add A B))
      (Int.add (Int.add (Int.neg B) 1) (Int.add A B))
      (Eq.trans (add_mid_swap (Int.neg A) C A B)
        (Eq.trans (congrArg (fun w : Int => Int.add w (Int.add C B)) (neg_add_cancel A))
          (Eq.trans (Int.zero_add (Int.add C B)) (Int.add_comm C B)))).symm
      (le_congr_left (Int.add A 1) (Int.add (Int.add (Int.neg B) 1) (Int.add A B))
        (Int.add B C)
        (Eq.trans
          (congrArg (fun w : Int => Int.add (Int.add (Int.neg B) 1) w) (Int.add_comm A B))
          (Eq.trans (add_mid_swap (Int.neg B) 1 B A)
            (Eq.trans (congrArg (fun w : Int => Int.add w (Int.add 1 A)) (neg_add_cancel B))
              (Eq.trans (Int.zero_add (Int.add 1 A)) (Int.add_comm 1 A))))).symm
        h))

theorem int_neg_ofNat_mul (k q : Nat) :
    Int.neg (Int.ofNat (Nat.mul q k)) = Int.mul (Int.ofNat k) (Int.neg (Int.ofNat q)) :=
  Eq.trans (congrArg (fun w : Nat => Int.neg (Int.ofNat w)) (Nat.mul_comm q k))
    (Int.neg_mul_right (Int.ofNat k) (Int.ofNat q))

def intCeilDiv (x : Int) (k : Nat) : Int :=
  match x with
  | Int.ofNat n   => Int.ofNat (natCeilDiv n k)
  | Int.negSucc m => Int.neg (Int.ofNat (natDivMod (Nat.succ m) k).q)

theorem intCeilDiv_ub (x : Int) (k : Nat) (hk : Nat.le 1 k) :
    Int.le x (Int.mul (Int.ofNat k) (intCeilDiv x k)) :=
  @Int.rec
    (fun x : Int => Int.le x (Int.mul (Int.ofNat k) (intCeilDiv x k)))
    (fun n =>
      int_ofNat_le_ofNat n (Nat.mul k (natCeilDiv n k))
        (nat_le_congr_right (Nat.mul (natCeilDiv n k) k) (Nat.mul k (natCeilDiv n k)) n
          (Nat.mul_comm (natCeilDiv n k) k)
          (natCeilDiv_ge n k hk)))
    (fun m =>
      le_congr_right
        (Int.neg (Int.ofNat (Nat.mul (natDivMod (Nat.succ m) k).q k)))
        (Int.mul (Int.ofNat k) (Int.neg (Int.ofNat (natDivMod (Nat.succ m) k).q)))
        (Int.negSucc m)
        (int_neg_ofNat_mul k (natDivMod (Nat.succ m) k).q)
        (int_neg_le_neg
          (Int.ofNat (Nat.mul (natDivMod (Nat.succ m) k).q k))
          (Int.ofNat (Nat.succ m))
          (int_ofNat_le_ofNat (Nat.mul (natDivMod (Nat.succ m) k).q k) (Nat.succ m)
            (nat_le_congr_right
              (Nat.add (Nat.mul (natDivMod (Nat.succ m) k).q k) (natDivMod (Nat.succ m) k).r)
              (Nat.succ m)
              (Nat.mul (natDivMod (Nat.succ m) k).q k)
              (natDivMod_spec_eq (Nat.succ m) k hk)
              (Nat.le_add_right (Nat.mul (natDivMod (Nat.succ m) k).q k)
                (natDivMod (Nat.succ m) k).r)))))
    x

theorem int_div_min_pos (n k : Nat) (hk : Nat.le 1 k) :
    Int.lt (Int.mul (Int.ofNat k) (Int.ofNat (natCeilDiv n k)))
      (Int.add (Int.ofNat n) (Int.ofNat k)) :=
  int_ofNat_lt_ofNat (Nat.mul k (natCeilDiv n k)) (Nat.add n k)
    (nat_le_congr_left (Nat.succ (Nat.mul (natCeilDiv n k) k))
      (Nat.succ (Nat.mul k (natCeilDiv n k)))
      (Nat.add n k)
      (congrArg Nat.succ (Nat.mul_comm (natCeilDiv n k) k))
      (natCeilDiv_min n k hk))

theorem int_div_min_neg (m k q r : Nat)
    (heq : Nat.add (Nat.mul q k) r = Nat.succ m)
    (hlt : Nat.lt r k) :
    Int.lt (Int.mul (Int.ofNat k) (Int.neg (Int.ofNat q)))
      (Int.add (Int.negSucc m) (Int.ofNat k)) :=
  le_congr_left
    (Int.add (Int.neg (Int.ofNat (Nat.mul q k))) 1)
    (Int.add (Int.mul (Int.ofNat k) (Int.neg (Int.ofNat q))) 1)
    (Int.add (Int.negSucc m) (Int.ofNat k))
    (congrArg (fun w : Int => Int.add w 1) (int_neg_ofNat_mul k q))
    (int_neg_lt_of_lt_add
      (Int.ofNat (Nat.succ m))
      (Int.ofNat (Nat.mul q k))
      (Int.ofNat k)
      (int_ofNat_lt_ofNat (Nat.succ m) (Nat.add (Nat.mul q k) k)
        (nat_le_congr_left
          (Nat.succ (Nat.add (Nat.mul q k) r))
          (Nat.succ (Nat.succ m))
          (Nat.add (Nat.mul q k) k)
          (congrArg Nat.succ heq)
          (Nat.add_lt_add_left r k hlt (Nat.mul q k)))))

theorem intCeilDiv_min (x : Int) (k : Nat) (hk : Nat.le 1 k) :
    Int.lt (Int.mul (Int.ofNat k) (intCeilDiv x k)) (Int.add x (Int.ofNat k)) :=
  @Int.rec
    (fun x : Int =>
      Int.lt (Int.mul (Int.ofNat k) (intCeilDiv x k)) (Int.add x (Int.ofNat k)))
    (fun n => int_div_min_pos n k hk)
    (fun m =>
      int_div_min_neg m k (natDivMod (Nat.succ m) k).q (natDivMod (Nat.succ m) k).r
        (natDivMod_spec_eq (Nat.succ m) k hk)
        (natDivMod_spec_lt (Nat.succ m) k hk))
    x

theorem coeffsDominated_intCeilDiv (k : Nat) (hk : Nat.le 1 k) (ts : List Term) :
    CoeffsDominated (Int.ofNat k) (fun x => intCeilDiv x k) ts :=
  @List.rec Term
    (fun ts : List Term => CoeffsDominated (Int.ofNat k) (fun x => intCeilDiv x k) ts)
    True.intro
    (fun t rest ih => And.intro (intCeilDiv_ub t.coeff k hk) ih)
    ts

theorem entails_divide_concrete (F : List Constraint) (c : Constraint) (k : Nat)
    (hk : Nat.le 1 k) (h : Entails F c) :
    Entails F (divC (fun x => intCeilDiv x k) c) :=
  entails_divide F c (Int.ofNat k) (fun x => intCeilDiv x k)
    (int_zero_le_ofNat k)
    (coeffsDominated_intCeilDiv k hk c.terms)
    (intCeilDiv_min c.degree k hk)
    h

theorem ceilQuotient_unique (x q : Int) (k : Nat) (hk : Nat.le 1 k)
    (hub : Int.le x (Int.mul (Int.ofNat k) q))
    (hmin : Int.lt (Int.mul (Int.ofNat k) q) (Int.add x (Int.ofNat k))) :
    q = intCeilDiv x k :=
  Int.le_antisymm q (intCeilDiv x k)
    (le_of_mul_le_min (Int.ofNat k) (intCeilDiv x k) q x
      (int_zero_le_ofNat k) (intCeilDiv_ub x k hk) hmin)
    (le_of_mul_le_min (Int.ofNat k) q (intCeilDiv x k) x
      (int_zero_le_ofNat k) hub (intCeilDiv_min x k hk))

theorem entails_divide_from_checks (F : List Constraint) (c : Constraint)
    (k : Nat) (q s : Int)
    (hk : Nat.le 1 k)
    (hub : Int.le c.degree (Int.mul (Int.ofNat k) q))
    (hmin : Int.lt (Int.mul (Int.ofNat k) q) (Int.add c.degree (Int.ofNat k)))
    (hs : eqOkB s q = true)
    (hfit : fitsI64 s = true)
    (h : Entails F c) :
    And (InI64 s)
        (Entails F { terms := mapCoeff (fun x => intCeilDiv x k) c.terms,
                     degree := s }) :=
  And.intro (inI64_of_fitsI64 s hfit)
    (Eq.mpr
      (congrArg
        (fun z : Int =>
          Entails F ({ terms := mapCoeff (fun x => intCeilDiv x k) c.terms,
                       degree := z } : Constraint))
        (Eq.trans (eq_of_eqOkB s q hs)
                  (ceilQuotient_unique c.degree q k hk hub hmin)))
      (entails_divide_concrete F c k hk h))

theorem ctrl_divmod_7_2_q : (natDivMod 7 2).q = 3 := rfl
theorem ctrl_divmod_7_2_r : (natDivMod 7 2).r = 1 := rfl
theorem ctrl_natceil_7_2 : natCeilDiv 7 2 = 4 := rfl
theorem ctrl_natceil_6_2 : natCeilDiv 6 2 = 3 := rfl

theorem ctrl_negSucc6_is_neg7 : Int.negSucc 6 = Int.neg (Int.ofNat 7) := rfl
theorem ctrl_ceildiv_7_2 : intCeilDiv 7 2 = 4 := rfl
theorem ctrl_ceildiv_neg7_2 : intCeilDiv (Int.negSucc 6) 2 = Int.negSucc 2 := rfl
theorem ctrl_ceildiv_6_2 : intCeilDiv 6 2 = 3 := rfl
theorem ctrl_ceildiv_0_5 : intCeilDiv 0 5 = 0 := rfl
theorem ctrl_ceildiv_neg6_2 : intCeilDiv (Int.negSucc 5) 2 = Int.negSucc 2 := rfl

theorem int_mul_comm (x y : Int) : Int.mul x y = Int.mul y x :=
  @Int.rec (fun x : Int => Int.mul x y = Int.mul y x)
    (fun a =>
      @Int.rec (fun y : Int => Int.mul (Int.ofNat a) y = Int.mul y (Int.ofNat a))
        (fun b => congrArg Int.ofNat (Nat.mul_comm a b))
        (fun b => congrArg Int.negOfNat (Nat.mul_comm a (Nat.succ b)))
        y)
    (fun a =>
      @Int.rec (fun y : Int => Int.mul (Int.negSucc a) y = Int.mul y (Int.negSucc a))
        (fun b => congrArg Int.negOfNat (Nat.mul_comm (Nat.succ a) b))
        (fun b => congrArg Int.ofNat (Nat.mul_comm (Nat.succ a) (Nat.succ b)))
        y)
    x

theorem int_zero_mul (a : Int) : Int.mul 0 a = 0 :=
  Eq.trans (int_mul_comm 0 a) (Int.mul_zero a)

theorem int_add_mul (a b c : Int) :
    Int.mul (Int.add a b) c = Int.add (Int.mul a c) (Int.mul b c) :=
  Eq.trans (int_mul_comm (Int.add a b) c)
    (Eq.trans (Int.left_distrib c a b)
      (Eq.trans
        (add_congr_left (Int.mul c a) (Int.mul a c) (Int.mul c b) (int_mul_comm c a))
        (add_congr_right (Int.mul c b) (Int.mul b c) (Int.mul a c) (int_mul_comm c b))))

theorem int_succ_mul (a b : Int) :
    Int.mul (Int.add a 1) b = Int.add (Int.mul a b) b :=
  Eq.trans (int_add_mul a 1 b)
    (add_congr_right (Int.mul 1 b) b (Int.mul a b) (Int.one_mul b))

theorem int_mul_le_mul_right (a b c : Int) (h : Int.le a b) (hc : Int.le 0 c) :
    Int.le (Int.mul a c) (Int.mul b c) :=
  le_congr_left (Int.mul c a) (Int.mul a c) (Int.mul b c) (int_mul_comm c a)
    (le_congr_right (Int.mul c b) (Int.mul b c) (Int.mul c a) (int_mul_comm c b)
      (Int.mul_le_mul_of_nonneg_left a b c h hc))

theorem int_le_of_eq (a b : Int) (h : a = b) : Int.le a b :=
  le_congr_right a b a h (Int.le_refl a)

theorem int_add_right_cancel (a b c : Int) (h : Int.add a c = Int.add b c) : a = b :=
  Int.le_antisymm a b
    (le_cancel_right a c b (int_le_of_eq (Int.add a c) (Int.add b c) h))
    (le_cancel_right b c a (int_le_of_eq (Int.add b c) (Int.add a c) h.symm))

theorem int_add_left_cancel (a b c : Int) (h : Int.add a b = Int.add a c) : b = c :=
  int_add_right_cancel b c a
    (Eq.trans (Int.add_comm b a) (Eq.trans h (Int.add_comm a c)))

theorem le_cancel_left (a b c : Int) (h : Int.le (Int.add a b) (Int.add a c)) :
    Int.le b c :=
  le_cancel_right b a c
    (le_congr_left (Int.add a b) (Int.add b a) (Int.add c a) (Int.add_comm a b)
      (le_congr_right (Int.add a c) (Int.add c a) (Int.add a b) (Int.add_comm a c) h))

theorem int_add_nonneg (a b : Int) (ha : Int.le 0 a) (hb : Int.le 0 b) :
    Int.le 0 (Int.add a b) :=
  le_congr_left (Int.add 0 0) 0 (Int.add a b) (Int.add_zero 0)
    (add_le_add 0 0 a b ha hb)

theorem int_le_0_1 : Int.le 0 1 := Int.le_of_lt 0 1 int_lt_0_1

theorem int_add_lt_add (a b c d : Int) (h1 : Int.lt a c) (h2 : Int.lt b d) :
    Int.lt (Int.add a b) (Int.add c d) :=
  Int.le_trans (Int.add (Int.add a b) 1) (Int.add (Int.add (Int.add a b) 1) 1)
    (Int.add c d)
    (le_add_right_of_nonneg (Int.add (Int.add a b) 1) 1 int_le_0_1)
    (le_congr_left (Int.add (Int.add a 1) (Int.add b 1))
      (Int.add (Int.add (Int.add a b) 1) 1) (Int.add c d)
      (Eq.trans (add_mid_swap a 1 b 1) (Int.add_assoc (Int.add a b) 1 1).symm)
      (add_le_add (Int.add a 1) (Int.add b 1) c d h1 h2))

def intFloorDiv (x : Int) (k : Nat) : Int :=
  match x with
  | Int.ofNat n   => Int.ofNat (natDivMod n k).q
  | Int.negSucc m => Int.neg (Int.ofNat (natCeilDiv (Nat.succ m) k))

def intFloorMod (x : Int) (k : Nat) : Int :=
  match x with
  | Int.ofNat n   => Int.ofNat (natDivMod n k).r
  | Int.negSucc m =>
    Int.ofNat (Nat.sub (Nat.mul (natCeilDiv (Nat.succ m) k) k) (Nat.succ m))

theorem int_ofNat_add (a b : Nat) :
    Int.add (Int.ofNat a) (Int.ofNat b) = Int.ofNat (Nat.add a b) := rfl

theorem int_ofNat_mul (a b : Nat) :
    Int.mul (Int.ofNat a) (Int.ofNat b) = Int.ofNat (Nat.mul a b) := rfl

theorem int_neg_succ (m : Nat) :
    Int.neg (Int.ofNat (Nat.succ m)) = Int.negSucc m := rfl

theorem int_dm_pos_eq (n k q r : Nat) (heq : Nat.add (Nat.mul q k) r = n) :
    Int.ofNat n = Int.add (Int.mul (Int.ofNat k) (Int.ofNat q)) (Int.ofNat r) :=
  (congrArg Int.ofNat
    (Eq.trans (nat_add_congr_left (Nat.mul k q) (Nat.mul q k) r (Nat.mul_comm k q))
      heq)).symm

theorem int_dm_neg_core (m N u : Nat) (hadd : Nat.add u (Nat.succ m) = N) :
    Int.negSucc m = Int.add (Int.neg (Int.ofNat N)) (Int.ofNat u) :=
  Eq.trans (int_neg_succ m).symm
    (int_add_right_cancel (Int.neg (Int.ofNat (Nat.succ m)))
      (Int.add (Int.neg (Int.ofNat N)) (Int.ofNat u))
      (Int.ofNat (Nat.succ m))
      (Eq.trans (neg_add_cancel (Int.ofNat (Nat.succ m)))
        (Eq.trans
          (Int.add_assoc (Int.neg (Int.ofNat N)) (Int.ofNat u)
            (Int.ofNat (Nat.succ m)))
          (Eq.trans
            (add_congr_right
              (Int.add (Int.ofNat u) (Int.ofNat (Nat.succ m)))
              (Int.ofNat N)
              (Int.neg (Int.ofNat N))
              (Eq.trans (int_ofNat_add u (Nat.succ m)) (congrArg Int.ofNat hadd)))
            (neg_add_cancel (Int.ofNat N)))).symm))

theorem int_dm_neg_eq (m k c : Nat) (hle : Nat.le (Nat.succ m) (Nat.mul c k)) :
    Int.negSucc m = Int.add (Int.mul (Int.ofNat k) (Int.neg (Int.ofNat c)))
                            (Int.ofNat (Nat.sub (Nat.mul c k) (Nat.succ m))) :=
  Eq.trans
    (int_dm_neg_core m (Nat.mul c k) (Nat.sub (Nat.mul c k) (Nat.succ m))
      (Nat.divmodAux.sub_add_cancel (Nat.mul c k) (Nat.succ m) hle))
    (add_congr_left (Int.neg (Int.ofNat (Nat.mul c k)))
      (Int.mul (Int.ofNat k) (Int.neg (Int.ofNat c)))
      (Int.ofNat (Nat.sub (Nat.mul c k) (Nat.succ m)))
      (int_neg_ofNat_mul k c))

theorem int_dm_neg_lt (k s N : Nat) (hsN : Nat.le s N) (hNk : Nat.lt N (Nat.add s k)) :
    Int.lt (Int.ofNat (Nat.sub N s)) (Int.ofNat k) :=
  le_cancel_right (Int.add (Int.ofNat (Nat.sub N s)) 1) (Int.ofNat s) (Int.ofNat k)
    (le_congr_right (Int.add (Int.ofNat s) (Int.ofNat k))
      (Int.add (Int.ofNat k) (Int.ofNat s))
      (Int.add (Int.add (Int.ofNat (Nat.sub N s)) 1) (Int.ofNat s))
      (Int.add_comm (Int.ofNat s) (Int.ofNat k))
      (le_congr_left (Int.add (Int.ofNat N) 1)
        (Int.add (Int.add (Int.ofNat (Nat.sub N s)) 1) (Int.ofNat s))
        (Int.add (Int.ofNat s) (Int.ofNat k))
        (Eq.trans
          (add_congr_left (Int.ofNat N)
            (Int.add (Int.ofNat (Nat.sub N s)) (Int.ofNat s)) 1
            ((congrArg Int.ofNat (Nat.divmodAux.sub_add_cancel N s hsN)).symm))
          (add_swap_right (Int.ofNat (Nat.sub N s)) (Int.ofNat s) 1))
        (int_ofNat_lt_ofNat N (Nat.add s k) hNk)))

theorem intFloor_spec (x : Int) (k : Nat) (hk : Nat.le 1 k) :
    x = Int.add (Int.mul (Int.ofNat k) (intFloorDiv x k)) (intFloorMod x k) :=
  @Int.rec
    (fun x : Int =>
      x = Int.add (Int.mul (Int.ofNat k) (intFloorDiv x k)) (intFloorMod x k))
    (fun n => int_dm_pos_eq n k (natDivMod n k).q (natDivMod n k).r
      (natDivMod_spec_eq n k hk))
    (fun m => int_dm_neg_eq m k (natCeilDiv (Nat.succ m) k)
      (natCeilDiv_ge (Nat.succ m) k hk))
    x

theorem intFloorMod_nonneg (x : Int) (k : Nat) : Int.le 0 (intFloorMod x k) :=
  @Int.rec (fun x : Int => Int.le 0 (intFloorMod x k))
    (fun n => int_zero_le_ofNat (natDivMod n k).r)
    (fun m => int_zero_le_ofNat
      (Nat.sub (Nat.mul (natCeilDiv (Nat.succ m) k) k) (Nat.succ m)))
    x

theorem intFloorMod_lt (x : Int) (k : Nat) (hk : Nat.le 1 k) :
    Int.lt (intFloorMod x k) (Int.ofNat k) :=
  @Int.rec (fun x : Int => Int.lt (intFloorMod x k) (Int.ofNat k))
    (fun n => int_ofNat_lt_ofNat (natDivMod n k).r k (natDivMod_spec_lt n k hk))
    (fun m => int_dm_neg_lt k (Nat.succ m) (Nat.mul (natCeilDiv (Nat.succ m) k) k)
      (natCeilDiv_ge (Nat.succ m) k hk) (natCeilDiv_min (Nat.succ m) k hk))
    x

theorem capCoeff_mono (d x y : Int) (h : Int.le x y) :
    Int.le (capCoeff d x) (capCoeff d y) :=
  @Bool.rec
    (fun b : Bool => Int.le (capCoeff d x) (match b with | true => y | false => d))
    (capCoeff_le_degree d x)
    (Int.le_trans (capCoeff d x) x y (capCoeff_le_self d x) h)
    (Int.ble y d)

theorem capCoeff_subadd (r x y : Int) (hx : Int.le 0 x) (hy : Int.le 0 y)
    (hr : Int.le 0 r) :
    Int.le (capCoeff r (Int.add x y)) (Int.add (capCoeff r x) (capCoeff r y)) :=
  satKey_step r x y (capCoeff r y) hx (capCoeff_nonneg r y hr hy)
    (Int.le_refl (capCoeff r y))

theorem fdiv_q_mono (K x1 q1 m1 x2 q2 m2 : Int)
    (hK0 : Int.le 0 K)
    (h1 : x1 = Int.add (Int.mul K q1) m1) (h1m : Int.le 0 m1)
    (h2 : x2 = Int.add (Int.mul K q2) m2) (h2lt : Int.lt m2 K)
    (hxy : Int.le x1 x2) : Int.le q1 q2 :=
  @Or.rec (Int.lt q1 q2) (Or (Eq q1 q2) (Int.lt q2 q1)) (fun _ => Int.le q1 q2)
    (fun hq => Int.le_of_lt q1 q2 hq)
    (fun hor =>
      @Or.rec (Eq q1 q2) (Int.lt q2 q1) (fun _ => Int.le q1 q2)
        (fun heq => int_le_of_eq q1 q2 heq)
        (fun hq =>
          False.elim
            (Int.lt_irrefl x2
              (Int.lt_of_lt_of_le x2 x1 x2
                (Int.lt_of_lt_of_le x2 (Int.add (Int.mul K q2) K) x1
                  (le_congr_left (Int.add (Int.add (Int.mul K q2) m2) 1)
                    (Int.add x2 1) (Int.add (Int.mul K q2) K)
                    (add_congr_left (Int.add (Int.mul K q2) m2) x2 1 h2.symm)
                    (le_congr_left
                      (Int.add (Int.mul K q2) (Int.add m2 1))
                      (Int.add (Int.add (Int.mul K q2) m2) 1)
                      (Int.add (Int.mul K q2) K)
                      (Int.add_assoc (Int.mul K q2) m2 1).symm
                      (Int.add_le_add_left (Int.add m2 1) K h2lt (Int.mul K q2))))
                  (Int.le_trans (Int.add (Int.mul K q2) K) (Int.mul K q1) x1
                    (le_congr_left (Int.mul K (Int.add q2 1))
                      (Int.add (Int.mul K q2) K) (Int.mul K q1)
                      (Eq.trans (Int.left_distrib K q2 1)
                        (add_congr_right (Int.mul K 1) K (Int.mul K q2)
                          (Int.mul_one K)))
                      (Int.mul_le_mul_of_nonneg_left (Int.add q2 1) q1 K hq hK0))
                    (le_congr_right (Int.add (Int.mul K q1) m1) x1 (Int.mul K q1)
                      h1.symm
                      (le_add_right_of_nonneg (Int.mul K q1) m1 h1m))))
                hxy)))
        hor)
    (Int.lt_trichotomy q1 q2)

theorem mir_mono_core (K r x1 q1 m1 x2 q2 m2 : Int)
    (hK0 : Int.le 0 K) (hr0 : Int.le 0 r)
    (h1 : x1 = Int.add (Int.mul K q1) m1) (h1m : Int.le 0 m1) (h1lt : Int.lt m1 K)
    (h2 : x2 = Int.add (Int.mul K q2) m2) (h2m : Int.le 0 m2) (h2lt : Int.lt m2 K)
    (hxy : Int.le x1 x2) :
    Int.le (Int.add (Int.mul q1 r) (capCoeff r m1))
           (Int.add (Int.mul q2 r) (capCoeff r m2)) :=
  @Or.rec (Int.lt q1 q2) (Or (Eq q1 q2) (Int.lt q2 q1))
    (fun _ => Int.le (Int.add (Int.mul q1 r) (capCoeff r m1))
                     (Int.add (Int.mul q2 r) (capCoeff r m2)))
    (fun hq =>
      Int.le_trans (Int.add (Int.mul q1 r) (capCoeff r m1))
        (Int.add (Int.mul q1 r) r)
        (Int.add (Int.mul q2 r) (capCoeff r m2))
        (Int.add_le_add_left (capCoeff r m1) r (capCoeff_le_degree r m1)
          (Int.mul q1 r))
        (Int.le_trans (Int.add (Int.mul q1 r) r) (Int.mul q2 r)
          (Int.add (Int.mul q2 r) (capCoeff r m2))
          (le_congr_left (Int.mul (Int.add q1 1) r) (Int.add (Int.mul q1 r) r)
            (Int.mul q2 r)
            (int_succ_mul q1 r)
            (int_mul_le_mul_right (Int.add q1 1) q2 r hq hr0))
          (le_add_right_of_nonneg (Int.mul q2 r) (capCoeff r m2)
            (capCoeff_nonneg r m2 hr0 h2m))))
    (fun hor =>
      @Or.rec (Eq q1 q2) (Int.lt q2 q1)
        (fun _ => Int.le (Int.add (Int.mul q1 r) (capCoeff r m1))
                         (Int.add (Int.mul q2 r) (capCoeff r m2)))
        (fun heq =>
          le_congr_right (Int.add (Int.mul q1 r) (capCoeff r m2))
            (Int.add (Int.mul q2 r) (capCoeff r m2))
            (Int.add (Int.mul q1 r) (capCoeff r m1))
            (add_congr_left (Int.mul q1 r) (Int.mul q2 r) (capCoeff r m2)
              (congrArg (fun w : Int => Int.mul w r) heq))
            (Int.add_le_add_left (capCoeff r m1) (capCoeff r m2)
              (capCoeff_mono r m1 m2
                (le_cancel_left (Int.mul K q1) m1 m2
                  (le_congr_right x2 (Int.add (Int.mul K q1) m2)
                    (Int.add (Int.mul K q1) m1)
                    (Eq.trans h2
                      (add_congr_left (Int.mul K q2) (Int.mul K q1) m2
                        (congrArg (fun w : Int => Int.mul K w) heq.symm)))
                    (le_congr_left x1 (Int.add (Int.mul K q1) m1) x2 h1 hxy))))
              (Int.mul q1 r)))
        (fun hq =>
          False.elim
            (Int.lt_irrefl q2
              (Int.lt_of_lt_of_le q2 q1 q2 hq
                (fdiv_q_mono K x1 q1 m1 x2 q2 m2 hK0 h1 h1m h2 h2lt hxy))))
        hor)
    (Int.lt_trichotomy q1 q2)

theorem mir_nonneg_core (K r x q m : Int)
    (hK0 : Int.le 0 K) (hr0 : Int.le 0 r) (hx : Int.le 0 x)
    (heq : x = Int.add (Int.mul K q) m) (hm0 : Int.le 0 m) (hmK : Int.lt m K) :
    Int.le 0 (Int.add (Int.mul q r) (capCoeff r m)) :=
  int_add_nonneg (Int.mul q r) (capCoeff r m)
    (le_congr_left (Int.mul 0 r) 0 (Int.mul q r) (int_zero_mul r)
      (int_mul_le_mul_right 0 q r
        (fdiv_q_mono K 0 0 0 x q m hK0
          (Eq.trans (add_congr_left (Int.mul K 0) 0 0 (Int.mul_zero K))
            (Int.add_zero 0)).symm
          (Int.le_refl 0) heq hmK hx)
        hr0))
    (capCoeff_nonneg r m hr0 hm0)

theorem carry_m_lt (K a b ms : Int) (haK : Int.lt a K)
    (heq : Int.add a b = Int.add K ms) : Int.lt ms b :=
  le_cancel_left K (Int.add ms 1) b
    (le_congr_left (Int.add (Int.add K ms) 1) (Int.add K (Int.add ms 1))
      (Int.add K b)
      (Int.add_assoc K ms 1)
      (le_congr_left (Int.add (Int.add a 1) b) (Int.add (Int.add K ms) 1)
        (Int.add K b)
        (Eq.trans (add_swap_right a 1 b)
          (add_congr_left (Int.add a b) (Int.add K ms) 1 heq))
        (Int.add_le_add_right (Int.add a 1) K haK b)))

theorem fdiv_carry_cases (K Q M qs ms : Int)
    (hK0 : Int.le 0 K)
    (hM0 : Int.le 0 M) (hM2 : Int.lt M (Int.add K K))
    (hms0 : Int.le 0 ms) (hmsK : Int.lt ms K)
    (heq : Int.add (Int.mul K Q) M = Int.add (Int.mul K qs) ms) :
    Or (qs = Q) (qs = Int.add Q 1) :=
  @Or.rec (Int.lt qs Q) (Or (Eq qs Q) (Int.lt Q qs))
    (fun _ => Or (qs = Q) (qs = Int.add Q 1))
    (fun hlt =>
      False.elim
        (Int.lt_irrefl ms
          (Int.lt_of_lt_of_le ms K ms hmsK
            (Int.le_trans K (Int.add K M) ms
              (le_add_right_of_nonneg K M hM0)
              (le_cancel_left (Int.mul K qs) (Int.add K M) ms
                (le_congr_right (Int.add (Int.mul K Q) M)
                  (Int.add (Int.mul K qs) ms)
                  (Int.add (Int.mul K qs) (Int.add K M))
                  heq
                  (le_congr_left (Int.add (Int.add (Int.mul K qs) K) M)
                    (Int.add (Int.mul K qs) (Int.add K M))
                    (Int.add (Int.mul K Q) M)
                    (Int.add_assoc (Int.mul K qs) K M)
                    (Int.add_le_add_right (Int.add (Int.mul K qs) K)
                      (Int.mul K Q)
                      (le_congr_left (Int.mul K (Int.add qs 1))
                        (Int.add (Int.mul K qs) K) (Int.mul K Q)
                        (Eq.trans (Int.left_distrib K qs 1)
                          (add_congr_right (Int.mul K 1) K (Int.mul K qs)
                            (Int.mul_one K)))
                        (Int.mul_le_mul_of_nonneg_left (Int.add qs 1) Q K
                          hlt hK0))
                      M))))))))
    (fun hor =>
      @Or.rec (Eq qs Q) (Int.lt Q qs)
        (fun _ => Or (qs = Q) (qs = Int.add Q 1))
        (fun heq2 => @Or.inl (qs = Q) (qs = Int.add Q 1) heq2)
        (fun hlt =>
          @Or.rec (Int.lt qs (Int.add Q 1))
            (Or (Eq qs (Int.add Q 1)) (Int.lt (Int.add Q 1) qs))
            (fun _ => Or (qs = Q) (qs = Int.add Q 1))
            (fun h1 =>
              False.elim
                (Int.lt_irrefl Q
                  (Int.le_trans (Int.add Q 1) qs Q hlt
                    (le_cancel_right qs 1 Q h1))))
            (fun hor2 =>
              @Or.rec (Eq qs (Int.add Q 1)) (Int.lt (Int.add Q 1) qs)
                (fun _ => Or (qs = Q) (qs = Int.add Q 1))
                (fun heq2 => @Or.inr (qs = Q) (qs = Int.add Q 1) heq2)
                (fun h1 =>
                  False.elim
                    (Int.lt_irrefl M
                      (Int.lt_of_lt_of_le M (Int.add K K) M hM2
                        (le_cancel_left (Int.mul K Q) (Int.add K K) M
                          (le_congr_right (Int.add (Int.mul K qs) ms)
                            (Int.add (Int.mul K Q) M)
                            (Int.add (Int.mul K Q) (Int.add K K))
                            heq.symm
                            (Int.le_trans
                              (Int.add (Int.mul K Q) (Int.add K K))
                              (Int.mul K qs)
                              (Int.add (Int.mul K qs) ms)
                              (le_congr_left
                                (Int.mul K (Int.add Q (Int.add 1 1)))
                                (Int.add (Int.mul K Q) (Int.add K K))
                                (Int.mul K qs)
                                (Eq.trans (Int.left_distrib K Q (Int.add 1 1))
                                  (add_congr_right
                                    (Int.mul K (Int.add 1 1)) (Int.add K K)
                                    (Int.mul K Q)
                                    (Eq.trans (Int.left_distrib K 1 1)
                                      (Eq.trans
                                        (add_congr_left (Int.mul K 1) K
                                          (Int.mul K 1) (Int.mul_one K))
                                        (add_congr_right (Int.mul K 1) K K
                                          (Int.mul_one K))))))
                                (Int.mul_le_mul_of_nonneg_left
                                  (Int.add Q (Int.add 1 1)) qs K
                                  (le_congr_left (Int.add (Int.add Q 1) 1)
                                    (Int.add Q (Int.add 1 1)) qs
                                    (Int.add_assoc Q 1 1)
                                    h1)
                                  hK0))
                              (le_add_right_of_nonneg (Int.mul K qs) ms
                                hms0)))))))
                hor2)
            (Int.lt_trichotomy qs (Int.add Q 1)))
        hor)
    (Int.lt_trichotomy qs Q)

theorem mir_carry_key (K r mx my ms : Int)
    (hrK : Int.lt r K) (hmxK : Int.lt mx K) (hmyK : Int.lt my K)
    (heq : Int.add mx my = Int.add K ms) :
    Int.le (Int.add r (capCoeff r ms)) (Int.add (capCoeff r mx) (capCoeff r my)) :=
  @Bool.rec
    (fun b : Bool =>
      Int.le (Int.add r (capCoeff r ms))
        (Int.add (match b with | true => mx | false => r) (capCoeff r my)))
    (@Bool.rec
      (fun b2 : Bool =>
        Int.le (Int.add r (capCoeff r ms))
          (Int.add r (match b2 with | true => my | false => r)))
      (Int.add_le_add_left (capCoeff r ms) r (capCoeff_le_degree r ms) r)
      (Int.add_le_add_left (capCoeff r ms) my
        (Int.le_trans (capCoeff r ms) ms my (capCoeff_le_self r ms)
          (Int.le_of_lt ms my (carry_m_lt K mx my ms hmxK heq)))
        r)
      (Int.ble my r))
    (@Bool.rec
      (fun b2 : Bool =>
        Int.le (Int.add r (capCoeff r ms))
          (Int.add mx (match b2 with | true => my | false => r)))
      (le_congr_right (Int.add r mx) (Int.add mx r) (Int.add r (capCoeff r ms))
        (Int.add_comm r mx)
        (Int.add_le_add_left (capCoeff r ms) mx
          (Int.le_trans (capCoeff r ms) ms mx (capCoeff_le_self r ms)
            (Int.le_of_lt ms mx
              (carry_m_lt K my mx ms hmyK
                (Eq.trans (Int.add_comm my mx) heq))))
          r))
      (le_congr_right (Int.add K ms) (Int.add mx my)
        (Int.add r (capCoeff r ms))
        heq.symm
        (add_le_add r (capCoeff r ms) K ms (Int.le_of_lt r K hrK)
          (capCoeff_le_self r ms)))
      (Int.ble my r))
    (Int.ble mx r)

theorem mir_subadd_nocarry (r qx mx qy my qs ms : Int)
    (hr0 : Int.le 0 r) (hmx0 : Int.le 0 mx) (hmy0 : Int.le 0 my)
    (hqs : qs = Int.add qx qy) (hms : Int.add mx my = ms) :
    Int.le (Int.add (Int.mul qs r) (capCoeff r ms))
           (Int.add (Int.add (Int.mul qx r) (capCoeff r mx))
                    (Int.add (Int.mul qy r) (capCoeff r my))) :=
  le_congr_left
    (Int.add (Int.mul (Int.add qx qy) r) (capCoeff r (Int.add mx my)))
    (Int.add (Int.mul qs r) (capCoeff r ms))
    (Int.add (Int.add (Int.mul qx r) (capCoeff r mx))
      (Int.add (Int.mul qy r) (capCoeff r my)))
    (Eq.trans
      (add_congr_left (Int.mul (Int.add qx qy) r) (Int.mul qs r)
        (capCoeff r (Int.add mx my))
        (congrArg (fun w : Int => Int.mul w r) hqs.symm))
      (add_congr_right (capCoeff r (Int.add mx my)) (capCoeff r ms)
        (Int.mul qs r)
        (congrArg (fun w : Int => capCoeff r w) hms)))
    (le_congr_right
      (Int.add (Int.add (Int.mul qx r) (Int.mul qy r))
        (Int.add (capCoeff r mx) (capCoeff r my)))
      (Int.add (Int.add (Int.mul qx r) (capCoeff r mx))
        (Int.add (Int.mul qy r) (capCoeff r my)))
      (Int.add (Int.mul (Int.add qx qy) r) (capCoeff r (Int.add mx my)))
      (add_mid_swap (Int.mul qx r) (capCoeff r mx) (Int.mul qy r)
        (capCoeff r my)).symm
      (le_congr_left
        (Int.add (Int.add (Int.mul qx r) (Int.mul qy r))
          (capCoeff r (Int.add mx my)))
        (Int.add (Int.mul (Int.add qx qy) r) (capCoeff r (Int.add mx my)))
        (Int.add (Int.add (Int.mul qx r) (Int.mul qy r))
          (Int.add (capCoeff r mx) (capCoeff r my)))
        (add_congr_left (Int.add (Int.mul qx r) (Int.mul qy r))
          (Int.mul (Int.add qx qy) r)
          (capCoeff r (Int.add mx my))
          (int_add_mul qx qy r).symm)
        (Int.add_le_add_left (capCoeff r (Int.add mx my))
          (Int.add (capCoeff r mx) (capCoeff r my))
          (capCoeff_subadd r mx my hmx0 hmy0 hr0)
          (Int.add (Int.mul qx r) (Int.mul qy r)))))

theorem mir_subadd_carry (K r qx mx qy my qs ms : Int)
    (hrK : Int.lt r K) (hmxK : Int.lt mx K) (hmyK : Int.lt my K)
    (hqs : qs = Int.add (Int.add qx qy) 1)
    (hM : Int.add mx my = Int.add K ms) :
    Int.le (Int.add (Int.mul qs r) (capCoeff r ms))
           (Int.add (Int.add (Int.mul qx r) (capCoeff r mx))
                    (Int.add (Int.mul qy r) (capCoeff r my))) :=
  le_congr_left
    (Int.add (Int.add (Int.mul qx r) (Int.mul qy r))
      (Int.add r (capCoeff r ms)))
    (Int.add (Int.mul qs r) (capCoeff r ms))
    (Int.add (Int.add (Int.mul qx r) (capCoeff r mx))
      (Int.add (Int.mul qy r) (capCoeff r my)))
    (Eq.trans
      (add_congr_left (Int.mul qs r)
        (Int.add (Int.add (Int.mul qx r) (Int.mul qy r)) r)
        (capCoeff r ms)
        (Eq.trans (congrArg (fun w : Int => Int.mul w r) hqs)
          (Eq.trans (int_succ_mul (Int.add qx qy) r)
            (add_congr_left (Int.mul (Int.add qx qy) r)
              (Int.add (Int.mul qx r) (Int.mul qy r)) r
              (int_add_mul qx qy r)))))
      (Int.add_assoc (Int.add (Int.mul qx r) (Int.mul qy r)) r
        (capCoeff r ms))).symm
    (le_congr_right
      (Int.add (Int.add (Int.mul qx r) (Int.mul qy r))
        (Int.add (capCoeff r mx) (capCoeff r my)))
      (Int.add (Int.add (Int.mul qx r) (capCoeff r mx))
        (Int.add (Int.mul qy r) (capCoeff r my)))
      (Int.add (Int.add (Int.mul qx r) (Int.mul qy r))
        (Int.add r (capCoeff r ms)))
      (add_mid_swap (Int.mul qx r) (capCoeff r mx) (Int.mul qy r)
        (capCoeff r my)).symm
      (Int.add_le_add_left (Int.add r (capCoeff r ms))
        (Int.add (capCoeff r mx) (capCoeff r my))
        (mir_carry_key K r mx my ms hrK hmxK hmyK hM)
        (Int.add (Int.mul qx r) (Int.mul qy r))))

theorem mir_subadd_core (K r qx mx qy my qs ms : Int)
    (hK0 : Int.le 0 K) (hr0 : Int.le 0 r) (hrK : Int.lt r K)
    (hmx0 : Int.le 0 mx) (hmxK : Int.lt mx K)
    (hmy0 : Int.le 0 my) (hmyK : Int.lt my K)
    (hms0 : Int.le 0 ms) (hmsK : Int.lt ms K)
    (heq : Int.add (Int.add (Int.mul K qx) mx) (Int.add (Int.mul K qy) my)
         = Int.add (Int.mul K qs) ms) :
    Int.le (Int.add (Int.mul qs r) (capCoeff r ms))
           (Int.add (Int.add (Int.mul qx r) (capCoeff r mx))
                    (Int.add (Int.mul qy r) (capCoeff r my))) :=
  @Or.rec (qs = Int.add qx qy) (qs = Int.add (Int.add qx qy) 1)
    (fun _ =>
      Int.le (Int.add (Int.mul qs r) (capCoeff r ms))
             (Int.add (Int.add (Int.mul qx r) (capCoeff r mx))
                      (Int.add (Int.mul qy r) (capCoeff r my))))
    (fun hqs =>
      mir_subadd_nocarry r qx mx qy my qs ms hr0 hmx0 hmy0 hqs
        (int_add_left_cancel (Int.mul K (Int.add qx qy)) (Int.add mx my) ms
          (Eq.trans
            (Eq.trans
              (add_congr_left (Int.mul K (Int.add qx qy))
                (Int.add (Int.mul K qx) (Int.mul K qy)) (Int.add mx my)
                (Int.left_distrib K qx qy))
              (Eq.trans
                (add_mid_swap (Int.mul K qx) (Int.mul K qy) mx my)
                heq))
            (add_congr_left (Int.mul K qs) (Int.mul K (Int.add qx qy)) ms
              (congrArg (fun w : Int => Int.mul K w) hqs)))))
    (fun hqs =>
      mir_subadd_carry K r qx mx qy my qs ms hrK hmxK hmyK hqs
        (int_add_left_cancel (Int.mul K (Int.add qx qy)) (Int.add mx my)
          (Int.add K ms)
          (Eq.trans
            (Eq.trans
              (add_congr_left (Int.mul K (Int.add qx qy))
                (Int.add (Int.mul K qx) (Int.mul K qy)) (Int.add mx my)
                (Int.left_distrib K qx qy))
              (Eq.trans
                (add_mid_swap (Int.mul K qx) (Int.mul K qy) mx my)
                heq))
            (Eq.trans
              (add_congr_left (Int.mul K qs)
                (Int.mul K (Int.add (Int.add qx qy) 1)) ms
                (congrArg (fun w : Int => Int.mul K w) hqs))
              (Eq.trans
                (add_congr_left (Int.mul K (Int.add (Int.add qx qy) 1))
                  (Int.add (Int.mul K (Int.add qx qy)) K) ms
                  (Eq.trans (Int.left_distrib K (Int.add qx qy) 1)
                    (add_congr_right (Int.mul K 1) K
                      (Int.mul K (Int.add qx qy)) (Int.mul_one K))))
                (Int.add_assoc (Int.mul K (Int.add qx qy)) K ms))))))
    (fdiv_carry_cases K (Int.add qx qy) (Int.add mx my) qs ms hK0
      (int_add_nonneg mx my hmx0 hmy0)
      (int_add_lt_add mx my K K hmxK hmyK)
      hms0 hmsK
      (Eq.trans
        (add_congr_left (Int.mul K (Int.add qx qy))
          (Int.add (Int.mul K qx) (Int.mul K qy)) (Int.add mx my)
          (Int.left_distrib K qx qy))
        (Eq.trans
          (add_mid_swap (Int.mul K qx) (Int.mul K qy) mx my)
          heq)))

def mirF (k : Nat) (r : Int) (x : Int) : Int :=
  Int.add (Int.mul (intFloorDiv x k) r) (capCoeff r (intFloorMod x k))

theorem mirF_nonneg (k : Nat) (r : Int) (hk : Nat.le 1 k) (hr0 : Int.le 0 r)
    (x : Int) (hx : Int.le 0 x) : Int.le 0 (mirF k r x) :=
  mir_nonneg_core (Int.ofNat k) r x (intFloorDiv x k) (intFloorMod x k)
    (int_zero_le_ofNat k) hr0 hx (intFloor_spec x k hk)
    (intFloorMod_nonneg x k) (intFloorMod_lt x k hk)

theorem mirF_mono (k : Nat) (r : Int) (hk : Nat.le 1 k) (hr0 : Int.le 0 r)
    (x y : Int) (hxy : Int.le x y) : Int.le (mirF k r x) (mirF k r y) :=
  mir_mono_core (Int.ofNat k) r x (intFloorDiv x k) (intFloorMod x k)
    y (intFloorDiv y k) (intFloorMod y k)
    (int_zero_le_ofNat k) hr0
    (intFloor_spec x k hk) (intFloorMod_nonneg x k) (intFloorMod_lt x k hk)
    (intFloor_spec y k hk) (intFloorMod_nonneg y k) (intFloorMod_lt y k hk)
    hxy

theorem mirF_subadd (k : Nat) (r : Int) (hk : Nat.le 1 k) (hr0 : Int.le 0 r)
    (hrk : Int.lt r (Int.ofNat k)) (x y : Int) :
    Int.le (mirF k r (Int.add x y)) (Int.add (mirF k r x) (mirF k r y)) :=
  mir_subadd_core (Int.ofNat k) r
    (intFloorDiv x k) (intFloorMod x k)
    (intFloorDiv y k) (intFloorMod y k)
    (intFloorDiv (Int.add x y) k) (intFloorMod (Int.add x y) k)
    (int_zero_le_ofNat k) hr0 hrk
    (intFloorMod_nonneg x k) (intFloorMod_lt x k hk)
    (intFloorMod_nonneg y k) (intFloorMod_lt y k hk)
    (intFloorMod_nonneg (Int.add x y) k) (intFloorMod_lt (Int.add x y) k hk)
    (Eq.trans
      (add_congr_left
        (Int.add (Int.mul (Int.ofNat k) (intFloorDiv x k)) (intFloorMod x k))
        x
        (Int.add (Int.mul (Int.ofNat k) (intFloorDiv y k)) (intFloorMod y k))
        (intFloor_spec x k hk).symm)
      (Eq.trans
        (add_congr_right
          (Int.add (Int.mul (Int.ofNat k) (intFloorDiv y k)) (intFloorMod y k))
          y x
          (intFloor_spec y k hk).symm)
        (intFloor_spec (Int.add x y) k hk)))

theorem mirF_eq_of_mod (k : Nat) (r A : Int) (hr : r = intFloorMod A k) :
    mirF k r A = Int.mul (Int.add (intFloorDiv A k) 1) r :=
  Eq.trans
    (add_congr_right (capCoeff r (intFloorMod A k)) (capCoeff r r)
      (Int.mul (intFloorDiv A k) r)
      (congrArg (fun w : Int => capCoeff r w) hr.symm))
    (Eq.trans
      (add_congr_right (capCoeff r r) r (Int.mul (intFloorDiv A k) r)
        (capCoeff_of_le r r (Int.le_refl r)))
      (int_succ_mul (intFloorDiv A k) r).symm)

theorem mirF_zero_le (k : Nat) (r : Int) (hr0 : Int.le 0 r) :
    Int.le (mirF k r 0) 0 :=
  int_le_of_eq (mirF k r 0) 0
    (Eq.trans
      (add_congr_left (Int.mul 0 r) 0 (capCoeff r 0) (int_zero_mul r))
      (Eq.trans
        (add_congr_right (capCoeff r 0) 0 0 (capCoeff_of_le r 0 hr0))
        (Int.add_zero 0)))

theorem evalTerms_mirF_ge (a : Nat -> Bool) (k : Nat) (r : Int)
    (hk : Nat.le 1 k) (hr0 : Int.le 0 r) (hrk : Int.lt r (Int.ofNat k))
    (ts : List Term) :
    AllNonneg ts ->
    Int.le (mirF k r (evalTerms a ts)) (evalTerms a (mapCoeff (mirF k r) ts)) :=
  @List.rec Term
    (fun ts =>
      AllNonneg ts ->
      Int.le (mirF k r (evalTerms a ts)) (evalTerms a (mapCoeff (mirF k r) ts)))
    (fun _ => mirF_zero_le k r hr0)
    (fun t rest ih hn =>
      @Bool.rec
        (fun b : Bool =>
          Int.le
            (mirF k r (match b with
              | true  => t.coeff + evalTerms a rest
              | false => evalTerms a rest))
            (match b with
              | true  => mirF k r t.coeff + evalTerms a (mapCoeff (mirF k r) rest)
              | false => evalTerms a (mapCoeff (mirF k r) rest)))
        (ih hn.right)
        (Int.le_trans (mirF k r (Int.add t.coeff (evalTerms a rest)))
          (Int.add (mirF k r t.coeff) (mirF k r (evalTerms a rest)))
          (Int.add (mirF k r t.coeff) (evalTerms a (mapCoeff (mirF k r) rest)))
          (mirF_subadd k r hk hr0 hrk t.coeff (evalTerms a rest))
          (Int.add_le_add_left (mirF k r (evalTerms a rest))
            (evalTerms a (mapCoeff (mirF k r) rest))
            (ih hn.right)
            (mirF k r t.coeff)))
        (litVal a t.lit))
    ts

theorem entails_mir (F : List Constraint) (c : Constraint) (k : Nat) (r : Int)
    (hk : Nat.le 1 k) (hn : AllNonneg c.terms)
    (hr : r = intFloorMod c.degree k) (hr0 : Int.lt 0 r)
    (h : Entails F c) :
    Entails F { terms := mapCoeff (mirF k r) c.terms,
                degree := Int.mul (Int.add (intFloorDiv c.degree k) 1) r } :=
  fun a ha =>
    le_congr_left (mirF k r c.degree)
      (Int.mul (Int.add (intFloorDiv c.degree k) 1) r)
      (evalTerms a (mapCoeff (mirF k r) c.terms))
      (mirF_eq_of_mod k r c.degree hr)
      (Int.le_trans (mirF k r c.degree) (mirF k r (evalTerms a c.terms))
        (evalTerms a (mapCoeff (mirF k r) c.terms))
        (mirF_mono k r hk (Int.le_of_lt 0 r hr0) c.degree (evalTerms a c.terms)
          (h a ha))
        (evalTerms_mirF_ge a k r hk (Int.le_of_lt 0 r hr0)
          (@Eq.subst Int (fun w : Int => Int.lt w (Int.ofNat k))
            (intFloorMod c.degree k) r hr.symm (intFloorMod_lt c.degree k hk))
          c.terms hn))

theorem ctrl_ifd_7_2 : intFloorDiv 7 2 = 3 := rfl
theorem ctrl_ifm_7_2 : intFloorMod 7 2 = 1 := rfl
theorem ctrl_ifd_neg7_2 : intFloorDiv (Int.negSucc 6) 2 = Int.negSucc 3 := rfl
theorem ctrl_ifm_neg7_2 : intFloorMod (Int.negSucc 6) 2 = 1 := rfl
theorem ctrl_ifd_0_5 : intFloorDiv 0 5 = 0 := rfl
theorem ctrl_ifm_0_5 : intFloorMod 0 5 = 0 := rfl
theorem ctrl_mirF_7_2_1 : mirF 2 1 7 = 4 := rfl
theorem ctrl_mirF_neg7_2_1 : mirF 2 1 (Int.negSucc 6) = Int.negSucc 2 := rfl

theorem ctrl_mir_5_3_r : intFloorMod 5 3 = 2 := rfl
theorem ctrl_mir_5_3_coeff : mirF 3 2 5 = 4 := rfl
theorem ctrl_mir_5_3_deg : Int.mul (Int.add (intFloorDiv 5 3) 1) 2 = 4 := rfl

theorem ctrl_mirF_3_2_1 : mirF 3 2 1 = 1 := rfl
theorem ctrl_mirF_3_2_2 : mirF 3 2 2 = 2 := rfl
theorem ctrl_mirF_3_2_3 : mirF 3 2 3 = 2 := rfl

theorem ctrl_mirF_not_superadd :
    Int.ble (Int.add (mirF 3 2 1) (mirF 3 2 2)) (mirF 3 2 (Int.add 1 2)) = false :=
  rfl

theorem ctrl_mirF_subadd_witness :
    Int.ble (mirF 3 2 (Int.add 1 2)) (Int.add (mirF 3 2 1) (mirF 3 2 2)) = true :=
  rfl

theorem nat_le_1_2 : Nat.le 1 2 := Nat.le.step Nat.le.refl
theorem nat_le_1_3 : Nat.le 1 3 := Nat.le.step nat_le_1_2
theorem int_lt_0_2 : Int.lt 0 2 := Int.le_of_lt 1 2 (Int.le_refl 2)

theorem evalTerms_mirF_signed (a : Nat -> Bool) (k : Nat) (r : Int)
    (hk : Nat.le 1 k) (hr0 : Int.le 0 r) (hrk : Int.lt r (Int.ofNat k))
    (ts : List Term) :
    Int.le (mirF k r (evalTerms a ts)) (evalTerms a (mapCoeff (mirF k r) ts)) :=
  @List.rec Term
    (fun ts =>
      Int.le (mirF k r (evalTerms a ts)) (evalTerms a (mapCoeff (mirF k r) ts)))
    (mirF_zero_le k r hr0)
    (fun t rest ih =>
      @Bool.rec
        (fun b : Bool =>
          Int.le
            (mirF k r (match b with
              | true  => t.coeff + evalTerms a rest
              | false => evalTerms a rest))
            (match b with
              | true  => mirF k r t.coeff + evalTerms a (mapCoeff (mirF k r) rest)
              | false => evalTerms a (mapCoeff (mirF k r) rest)))
        ih
        (Int.le_trans (mirF k r (Int.add t.coeff (evalTerms a rest)))
          (Int.add (mirF k r t.coeff) (mirF k r (evalTerms a rest)))
          (Int.add (mirF k r t.coeff) (evalTerms a (mapCoeff (mirF k r) rest)))
          (mirF_subadd k r hk hr0 hrk t.coeff (evalTerms a rest))
          (Int.add_le_add_left (mirF k r (evalTerms a rest))
            (evalTerms a (mapCoeff (mirF k r) rest))
            ih
            (mirF k r t.coeff)))
        (litVal a t.lit))
    ts

theorem entails_mir_signed (F : List Constraint) (c : Constraint) (k : Nat) (r : Int)
    (hk : Nat.le 1 k)
    (hr : r = intFloorMod c.degree k) (hr0 : Int.lt 0 r)
    (h : Entails F c) :
    Entails F { terms := mapCoeff (mirF k r) c.terms,
                degree := Int.mul (Int.add (intFloorDiv c.degree k) 1) r } :=
  fun a ha =>
    le_congr_left (mirF k r c.degree)
      (Int.mul (Int.add (intFloorDiv c.degree k) 1) r)
      (evalTerms a (mapCoeff (mirF k r) c.terms))
      (mirF_eq_of_mod k r c.degree hr)
      (Int.le_trans (mirF k r c.degree) (mirF k r (evalTerms a c.terms))
        (evalTerms a (mapCoeff (mirF k r) c.terms))
        (mirF_mono k r hk (Int.le_of_lt 0 r hr0) c.degree (evalTerms a c.terms)
          (h a ha))
        (evalTerms_mirF_signed a k r hk (Int.le_of_lt 0 r hr0)
          (@Eq.subst Int (fun w : Int => Int.lt w (Int.ofNat k))
            (intFloorMod c.degree k) r hr.symm (intFloorMod_lt c.degree k hk))
          c.terms))

def varCoeffB (b : Bool) (co : Int) : Int :=
  match b with
  | true  => Int.neg co
  | false => co

def varLitB (b : Bool) (l : Lit) : Lit :=
  match b with
  | true  => negLit l
  | false => l

def negPartB (b : Bool) (co : Int) : Int :=
  match b with
  | true  => co
  | false => 0

def varCoeff (t : Term) : Int := varCoeffB t.lit.negated t.coeff

def varLit (t : Term) : Lit := varLitB t.lit.negated t.lit

def varTerm (t : Term) : Term := { coeff := varCoeff t, lit := varLit t }

def varTerms (ts : List Term) : List Term :=
  match ts with
  | []        => []
  | t :: rest => varTerm t :: varTerms rest

def negPart (t : Term) : Int := negPartB t.lit.negated t.coeff

def negSum (ts : List Term) : Int :=
  match ts with
  | []        => 0
  | t :: rest => Int.add (negPart t) (negSum rest)

theorem termVal_varTerm (a : Nat -> Bool) (t : Term) :
    Int.add (termVal a (varTerm t)) (negPart t) = termVal a t :=
  @Bool.rec
    (fun b : Bool =>
      Int.add
        (termVal a ({ coeff := varCoeffB b t.coeff, lit := varLitB b t.lit } : Term))
        (negPartB b t.coeff)
      = termVal a t)
    (Int.add_zero (termVal a t))
    (termVal_flip a t.coeff t.lit)
    t.lit.negated

theorem evalTerms_varTerms (a : Nat -> Bool) (ts : List Term) :
    evalTerms a ts = Int.add (evalTerms a (varTerms ts)) (negSum ts) :=
  @List.rec Term
    (fun ts => evalTerms a ts = Int.add (evalTerms a (varTerms ts)) (negSum ts))
    rfl
    (fun t rest ih =>
      Eq.trans (evalTerms_cons a t rest)
        (Eq.trans
          (add_congr_left (termVal a t)
            (Int.add (termVal a (varTerm t)) (negPart t))
            (evalTerms a rest)
            (termVal_varTerm a t).symm)
          (Eq.trans
            (add_congr_right (evalTerms a rest)
              (Int.add (evalTerms a (varTerms rest)) (negSum rest))
              (Int.add (termVal a (varTerm t)) (negPart t))
              ih)
            (Eq.trans
              (add_mid_swap (termVal a (varTerm t)) (negPart t)
                (evalTerms a (varTerms rest)) (negSum rest))
              (add_congr_left
                (Int.add (termVal a (varTerm t)) (evalTerms a (varTerms rest)))
                (evalTerms a (varTerm t :: varTerms rest))
                (Int.add (negPart t) (negSum rest))
                (evalTerms_cons a (varTerm t) (varTerms rest)).symm)))))
    ts

def vfMapTerm (f : Int -> Int) (t : Term) : Term :=
  { coeff := varCoeffB t.lit.negated (f (varCoeff t)), lit := t.lit }

def vfMapTerms (f : Int -> Int) (ts : List Term) : List Term :=
  match ts with
  | []        => []
  | t :: rest => vfMapTerm f t :: vfMapTerms f rest

def vfMirTerms (k : Nat) (r : Int) (ts : List Term) : List Term :=
  vfMapTerms (mirF k r) ts

theorem varCoeffB_invol (b : Bool) (x : Int) : varCoeffB b (varCoeffB b x) = x :=
  @Bool.rec (fun b : Bool => varCoeffB b (varCoeffB b x) = x)
    rfl
    (Int.neg_neg x)
    b

theorem varCoeff_vfMapTerm (f : Int -> Int) (t : Term) :
    varCoeff (vfMapTerm f t) = f (varCoeff t) :=
  varCoeffB_invol t.lit.negated (f (varCoeff t))

theorem varTerm_vfMapTerm (f : Int -> Int) (t : Term) :
    varTerm (vfMapTerm f t)
      = ({ coeff := f (varTerm t).coeff, lit := (varTerm t).lit } : Term) :=
  congrArg (fun co : Int => ({ coeff := co, lit := varLit t } : Term))
    (varCoeff_vfMapTerm f t)

theorem term_cons_congr (x y : Term) (xs ys : List Term) (hx : x = y) (hxs : xs = ys) :
    List.cons x xs = List.cons y ys :=
  Eq.trans (congrArg (fun z : Term => List.cons z xs) hx)
    (congrArg (fun zs : List Term => List.cons y zs) hxs)

theorem varTerms_vfMapTerms (f : Int -> Int) (ts : List Term) :
    varTerms (vfMapTerms f ts) = mapCoeff f (varTerms ts) :=
  @List.rec Term
    (fun ts => varTerms (vfMapTerms f ts) = mapCoeff f (varTerms ts))
    rfl
    (fun t rest ih =>
      term_cons_congr (varTerm (vfMapTerm f t))
        ({ coeff := f (varTerm t).coeff, lit := (varTerm t).lit } : Term)
        (varTerms (vfMapTerms f rest))
        (mapCoeff f (varTerms rest))
        (varTerm_vfMapTerm f t)
        ih)
    ts

theorem entails_mir_variable (F : List Constraint) (c : Constraint) (k : Nat)
    (r A : Int)
    (hk : Nat.le 1 k)
    (hA : A = c.degree - negSum c.terms)
    (hr : r = intFloorMod A k) (hr0 : Int.lt 0 r)
    (h : Entails F c) :
    Entails F { terms := vfMirTerms k r c.terms,
                degree := Int.add (Int.mul (Int.add (intFloorDiv A k) 1) r)
                                  (negSum (vfMirTerms k r c.terms)) } :=
  fun a ha =>
    le_congr_right
      (Int.add (evalTerms a (varTerms (vfMirTerms k r c.terms)))
        (negSum (vfMirTerms k r c.terms)))
      (evalTerms a (vfMirTerms k r c.terms))
      (Int.add (Int.mul (Int.add (intFloorDiv A k) 1) r)
        (negSum (vfMirTerms k r c.terms)))
      (evalTerms_varTerms a (vfMirTerms k r c.terms)).symm
      (Int.add_le_add_right
        (Int.mul (Int.add (intFloorDiv A k) 1) r)
        (evalTerms a (varTerms (vfMirTerms k r c.terms)))
        (le_congr_left (mirF k r A)
          (Int.mul (Int.add (intFloorDiv A k) 1) r)
          (evalTerms a (varTerms (vfMirTerms k r c.terms)))
          (mirF_eq_of_mod k r A hr)
          (le_congr_right
            (evalTerms a (mapCoeff (mirF k r) (varTerms c.terms)))
            (evalTerms a (varTerms (vfMirTerms k r c.terms)))
            (mirF k r A)
            (congrArg (fun ws : List Term => evalTerms a ws)
              (varTerms_vfMapTerms (mirF k r) c.terms).symm)
            (Int.le_trans (mirF k r A)
              (mirF k r (evalTerms a (varTerms c.terms)))
              (evalTerms a (mapCoeff (mirF k r) (varTerms c.terms)))
              (mirF_mono k r hk (Int.le_of_lt 0 r hr0) A
                (evalTerms a (varTerms c.terms))
                (le_congr_left (c.degree - negSum c.terms) A
                  (evalTerms a (varTerms c.terms))
                  hA.symm
                  (le_sub_of_le_add c.degree (negSum c.terms)
                    (evalTerms a (varTerms c.terms))
                    (le_congr_right (evalTerms a c.terms)
                      (Int.add (evalTerms a (varTerms c.terms)) (negSum c.terms))
                      c.degree
                      (evalTerms_varTerms a c.terms)
                      (h a ha)))))
              (evalTerms_mirF_signed a k r hk (Int.le_of_lt 0 r hr0)
                (@Eq.subst Int (fun w : Int => Int.lt w (Int.ofNat k))
                  (intFloorMod A k) r hr.symm (intFloorMod_lt A k hk))
                (varTerms c.terms)))))
        (negSum (vfMirTerms k r c.terms)))

theorem mirF_nonpos (k : Nat) (r : Int) (hk : Nat.le 1 k) (hr0 : Int.le 0 r)
    (x : Int) (hx : Int.le x 0) : Int.le (mirF k r x) 0 :=
  Int.le_trans (mirF k r x) (mirF k r 0) 0
    (mirF_mono k r hk hr0 x 0 hx)
    (mirF_zero_le k r hr0)

theorem int_nonpos_neg_of_nonneg (x : Int) (h : Int.le 0 x) : Int.le (Int.neg x) 0 :=
  int_neg_le_neg 0 x h

theorem vfMirCoeff_nonneg (k : Nat) (r : Int) (hk : Nat.le 1 k) (hr0 : Int.le 0 r)
    (t : Term) (hc : Int.le 0 t.coeff) :
    Int.le 0 (vfMapTerm (mirF k r) t).coeff :=
  @Bool.rec
    (fun b : Bool => Int.le 0 (varCoeffB b (mirF k r (varCoeffB b t.coeff))))
    (mirF_nonneg k r hk hr0 t.coeff hc)
    (neg_nonneg_of_nonpos (mirF k r (Int.neg t.coeff))
      (mirF_nonpos k r hk hr0 (Int.neg t.coeff)
        (int_nonpos_neg_of_nonneg t.coeff hc)))
    t.lit.negated

theorem vfMirTerms_nonneg (k : Nat) (r : Int) (hk : Nat.le 1 k) (hr0 : Int.le 0 r)
    (ts : List Term) : AllNonneg ts -> AllNonneg (vfMirTerms k r ts) :=
  @List.rec Term
    (fun ts => AllNonneg ts -> AllNonneg (vfMirTerms k r ts))
    (fun _ => True.intro)
    (fun t rest ih hn =>
      And.intro (vfMirCoeff_nonneg k r hk hr0 t hn.left) (ih hn.right))
    ts

def ctrlVfNotY : Lit := { var := 1, negated := true }

def ctrlVfC : Constraint :=
  { terms := [({ coeff := 3, lit := ctrlX } : Term),
              ({ coeff := 2, lit := ctrlVfNotY } : Term)],
    degree := 4 }

def ctrlVfA : Nat -> Bool := fun v => Nat.beq v 0

theorem ctrl_vf_negSum : negSum ctrlVfC.terms = 2 := rfl
theorem ctrl_vf_degree_var : ctrlVfC.degree - negSum ctrlVfC.terms = 2 := rfl
theorem ctrl_vf_r : intFloorMod 2 3 = 2 := rfl

theorem ctrl_vf_varTerms :
    varTerms ctrlVfC.terms
      = [({ coeff := 3, lit := ctrlX } : Term),
         ({ coeff := Int.neg 2, lit := ({ var := 1, negated := false } : Lit) } : Term)] :=
  rfl

theorem ctrl_vf_mirF_pos : mirF 3 2 3 = 2 := rfl
theorem ctrl_vf_mirF_neg : mirF 3 2 (Int.neg 2) = Int.neg 1 := rfl

theorem ctrl_vf_terms :
    vfMirTerms 3 2 ctrlVfC.terms
      = [({ coeff := 2, lit := ctrlX } : Term),
         ({ coeff := 1, lit := ctrlVfNotY } : Term)] :=
  rfl

theorem ctrl_vf_new_negSum : negSum (vfMirTerms 3 2 ctrlVfC.terms) = 1 := rfl

theorem ctrl_vf_new_degree :
    Int.add (Int.mul (Int.add (intFloorDiv 2 3) 1) 2)
            (negSum (vfMirTerms 3 2 ctrlVfC.terms)) = 3 :=
  rfl

theorem ctrl_vf_eval_model_base : evalTerms ctrlVfA ctrlVfC.terms = 5 := rfl
theorem ctrl_vf_eval_model_cut :
    evalTerms ctrlVfA (vfMirTerms 3 2 ctrlVfC.terms) = 3 := rfl
theorem ctrl_vf_eval_all_true_base : evalTerms ctrlAllTrue ctrlVfC.terms = 3 := rfl
theorem ctrl_vf_eval_all_true_cut :
    evalTerms ctrlAllTrue (vfMirTerms 3 2 ctrlVfC.terms) = 2 := rfl

theorem ctrl_vf_entails :
    Entails [ctrlVfC]
      { terms := vfMirTerms 3 2 ctrlVfC.terms,
        degree := Int.add (Int.mul (Int.add (intFloorDiv 2 3) 1) 2)
                          (negSum (vfMirTerms 3 2 ctrlVfC.terms)) } :=
  entails_mir_variable [ctrlVfC] ctrlVfC 3 2 2
    nat_le_1_3 rfl rfl int_lt_0_2
    (fun a ha => ha.left)

theorem ctrl_vf_signed_terms :
    mapCoeff (mirF 3 2) (varTerms ctrlVfC.terms)
      = [({ coeff := 2, lit := ctrlX } : Term),
         ({ coeff := Int.neg 1, lit := ({ var := 1, negated := false } : Lit) } : Term)] :=
  rfl

def getC (F : List Constraint) (i : Nat) : Option Constraint :=
  match F with
  | []        => none
  | c :: rest =>
    match i with
    | Nat.zero   => some c
    | Nat.succ j => getC rest j

def liftDB (F : List Constraint) : List (Option Constraint) :=
  match F with
  | []        => []
  | c :: rest => some c :: liftDB rest

def setNoneGo (DB : List (Option Constraint)) (i : Nat) : List (Option Constraint) :=
  match DB with
  | []        => []
  | o :: rest =>
    match i with
    | Nat.zero   => none :: rest
    | Nat.succ j => o :: setNoneGo rest j

def setNone (i : Nat) (DB : List (Option Constraint)) : List (Option Constraint) :=
  setNoneGo DB i

theorem holdsAll_get (a : Nat -> Bool) (F : List Constraint) (i : Nat) (c : Constraint)
    (hall : HoldsAll a F) (hg : getC F i = some c) : Holds a c :=
  @List.rec Constraint
    (fun F => forall (i : Nat) (c : Constraint),
      HoldsAll a F -> getC F i = some c -> Holds a c)
    (fun _ c _ hg => False.elim (none_ne_someC c hg))
    (fun c' rest ih i =>
      @Nat.rec
        (fun i => forall (c : Constraint),
          HoldsAll a (c' :: rest) -> getC (c' :: rest) i = some c -> Holds a c)
        (fun c hall hg =>
          @Eq.subst Constraint (fun w : Constraint => Holds a w) c' c
            (someC_inj c' c hg) hall.left)
        (fun j _ c hall hg => ih j c hall.right hg)
        i)
    F i c hall hg

theorem entails_get (F : List Constraint) (i : Nat) (c : Constraint)
    (hg : getC F i = some c) : Entails F c :=
  fun a ha => holdsAll_get a F i c ha hg

theorem getO_liftDB (F : List Constraint) (i : Nat) (c : Constraint)
    (hg : getO (liftDB F) i = some c) : getC F i = some c :=
  @List.rec Constraint
    (fun F => forall (i : Nat) (c : Constraint),
      getO (liftDB F) i = some c -> getC F i = some c)
    (fun _ _ hg => hg)
    (fun c' rest ih i =>
      @Nat.rec
        (fun i => forall (c : Constraint),
          getO (liftDB (c' :: rest)) i = some c -> getC (c' :: rest) i = some c)
        (fun _ hg => hg)
        (fun j _ c hg => ih j c hg)
        i)
    F i c hg

theorem dbEntailed_init (F : List Constraint) : DbEntailed F (liftDB F) :=
  fun i c hg => entails_get F i c (getO_liftDB F i c hg)

theorem getO_append_of_get (DB : List (Option Constraint)) (x : Option Constraint)
    (i : Nat) (c : Constraint) (hg : getO DB i = some c) :
    getO (List.append DB [x]) i = some c :=
  @List.rec (Option Constraint)
    (fun DB => forall (i : Nat) (c : Constraint),
      getO DB i = some c -> getO (List.append DB [x]) i = some c)
    (fun _ c hg => False.elim (none_ne_someC c hg))
    (fun o rest ih i =>
      @Nat.rec
        (fun i => forall (c : Constraint),
          getO (o :: rest) i = some c ->
          getO (List.append (o :: rest) [x]) i = some c)
        (fun _ hg => hg)
        (fun j _ c hg => ih j c hg)
        i)
    DB i c hg

theorem getO_append_cases (DB : List (Option Constraint)) (x : Option Constraint)
    (i : Nat) (c : Constraint) (hg : getO (List.append DB [x]) i = some c) :
    Or (getO DB i = some c) (x = some c) :=
  @List.rec (Option Constraint)
    (fun DB => forall (i : Nat) (c : Constraint),
      getO (List.append DB [x]) i = some c ->
      Or (getO DB i = some c) (x = some c))
    (fun i =>
      @Nat.rec
        (fun i => forall (c : Constraint),
          getO (List.append ([] : List (Option Constraint)) [x]) i = some c ->
          Or (getO ([] : List (Option Constraint)) i = some c) (x = some c))
        (fun _ hg => Or.inr hg)
        (fun j _ c hg => False.elim (none_ne_someC c hg))
        i)
    (fun o rest ih i =>
      @Nat.rec
        (fun i => forall (c : Constraint),
          getO (List.append (o :: rest) [x]) i = some c ->
          Or (getO (o :: rest) i = some c) (x = some c))
        (fun _ hg => Or.inl hg)
        (fun j _ c hg => ih j c hg)
        i)
    DB i c hg

theorem getO_setNone (i j : Nat) (DB : List (Option Constraint)) (c : Constraint)
    (hg : getO (setNone i DB) j = some c) : getO DB j = some c :=
  @List.rec (Option Constraint)
    (fun DB => forall (i j : Nat) (c : Constraint),
      getO (setNone i DB) j = some c -> getO DB j = some c)
    (fun _ _ _ hg => hg)
    (fun o rest ih i =>
      @Nat.rec
        (fun i => forall (j : Nat) (c : Constraint),
          getO (setNone i (o :: rest)) j = some c -> getO (o :: rest) j = some c)
        (fun j =>
          @Nat.rec
            (fun j => forall (c : Constraint),
              getO (none :: rest) j = some c -> getO (o :: rest) j = some c)
            (fun c hg => False.elim (none_ne_someC c hg))
            (fun k _ _ hg => hg)
            j)
        (fun i' _ j =>
          @Nat.rec
            (fun j => forall (c : Constraint),
              getO (o :: setNoneGo rest i') j = some c -> getO (o :: rest) j = some c)
            (fun _ hg => hg)
            (fun k _ c hg => ih i' k c hg)
            j)
        i)
    DB i j c hg

theorem dbEntailed_extend (F : List Constraint) (DB : List (Option Constraint))
    (c : Constraint) (hdb : DbEntailed F DB) (hc : Entails F c) :
    DbEntailed F (List.append DB [some c]) :=
  fun i c' hg =>
    @Or.rec (getO DB i = some c') (some c = some c') (fun _ => Entails F c')
      (fun h => hdb i c' h)
      (fun h =>
        @Eq.subst Constraint (fun w : Constraint => Entails F w) c c'
          (someC_inj c c' h) hc)
      (getO_append_cases DB (some c) i c' hg)

theorem dbEntailed_delete (F : List Constraint) (DB : List (Option Constraint))
    (i : Nat) (hdb : DbEntailed F DB) : DbEntailed F (setNone i DB) :=
  fun j c hg => hdb j c (getO_setNone i j DB c hg)

theorem entails_trivial (F : List Constraint) (c : Constraint)
    (hn : AllNonneg c.terms) (hd : Int.le c.degree 0) : Entails F c :=
  fun a ha =>
    Int.le_trans c.degree 0 (evalTerms a c.terms) hd (evalTerms_nonneg a c.terms hn)

inductive DStep (DB : List (Option Constraint)) : Constraint -> Prop where
  | ax : forall (i : Nat) (c : Constraint), getO DB i = some c -> DStep DB c
  | lit : forall l : Lit, DStep DB (litAxiom l)
  | addS : forall c1 c2 : Constraint, DStep DB c1 -> DStep DB c2 -> DStep DB (addC c1 c2)
  | mulS : forall (k : Int) (c : Constraint), Int.le 0 k -> DStep DB c -> DStep DB (scaleC k c)
  | divS : forall (k : Int) (f : Int -> Int) (c : Constraint), Int.le 0 k ->
      CoeffsDominated k f c.terms -> Int.lt (k * f c.degree) (c.degree + k) ->
      DStep DB c -> DStep DB (divC f c)
  | satS : forall c : Constraint, Int.le 0 c.degree -> AllNonneg c.terms ->
      DStep DB c -> DStep DB (satC c)
  | wkS : forall (c : Constraint) (d : Int), Int.le d c.degree -> DStep DB c ->
      DStep DB (weakenC d c)
  | rupS : forall (c : Constraint) (nd : Int) (tr : List Lit) (i : Nat) (cc : Constraint),
      nd + c.degree = coeffSum c.terms + 1 ->
      PropTrail (negC c nd) DB tr ->
      getG (negC c nd) DB i = some cc ->
      AllNonneg cc.terms ->
      Int.lt (slackTerms tr cc.terms) cc.degree ->
      DStep DB c
  | trivS : forall c : Constraint, AllNonneg c.terms -> Int.le c.degree 0 -> DStep DB c
  | normS : forall c : Constraint, DStep DB c -> DStep DB (normC c)
  | mirS : forall (c : Constraint) (k : Nat) (r : Int), Nat.le 1 k ->
      r = intFloorMod c.degree k -> Int.lt 0 r ->
      DStep DB c ->
      DStep DB { terms := mapCoeff (mirF k r) c.terms,
                 degree := Int.mul (Int.add (intFloorDiv c.degree k) 1) r }
  | mirVarS : forall (c : Constraint) (k : Nat) (r A : Int), Nat.le 1 k ->
      A = c.degree - negSum c.terms ->
      r = intFloorMod A k -> Int.lt 0 r ->
      DStep DB c ->
      DStep DB { terms := vfMirTerms k r c.terms,
                 degree := Int.add (Int.mul (Int.add (intFloorDiv A k) 1) r)
                                   (negSum (vfMirTerms k r c.terms)) }

theorem dstep_entails (F : List Constraint) (DB : List (Option Constraint))
    (hdb : DbEntailed F DB) (c : Constraint) (hs : DStep DB c) : Entails F c :=
  @DStep.rec DB
    (fun c _ => Entails F c)
    (fun i c hg => hdb i c hg)
    (fun l => entails_literal F l)
    (fun c1 c2 _ _ ih1 ih2 => entails_add F c1 c2 ih1 ih2)
    (fun k c hk _ ih => entails_multiply F c k hk ih)
    (fun k f c hk hdom hmin _ ih => entails_divide F c k f hk hdom hmin ih)
    (fun c hd hn _ ih => entails_saturate F c hd hn ih)
    (fun c d hd _ ih => entails_weaken_degree F c d hd ih)
    (fun c nd tr i cc hnd ht hg hnn hconf =>
      entails_of_rup F DB c nd tr i cc hdb hnd ht hg hnn hconf)
    (fun c hn hd => entails_trivial F c hn hd)
    (fun c _ ih => entails_normC F c ih)
    (fun c k r hk hr hr0 _ ih => entails_mir_signed F c k r hk hr hr0 ih)
    (fun c k r A hk hA hr hr0 _ ih => entails_mir_variable F c k r A hk hA hr hr0 ih)
    c hs

theorem dstep_div_concrete (DB : List (Option Constraint)) (k : Nat)
    (hk : Nat.le 1 k) (c : Constraint) (h : DStep DB c) :
    DStep DB (divC (fun x => intCeilDiv x k) c) :=
  @DStep.divS DB (Int.ofNat k) (fun x => intCeilDiv x k) c
    (int_zero_le_ofNat k)
    (coeffsDominated_intCeilDiv k hk c.terms)
    (intCeilDiv_min c.degree k hk)
    h

inductive DbOk (F : List Constraint) : List (Option Constraint) -> Prop where
  | init : DbOk F (liftDB F)
  | derive : forall (DB : List (Option Constraint)) (c : Constraint),
      DbOk F DB -> DStep DB c -> DbOk F (List.append DB [some c])
  | delete : forall (DB : List (Option Constraint)) (i : Nat),
      DbOk F DB -> DbOk F (setNone i DB)

theorem dbOk_entailed (F : List Constraint) (DB : List (Option Constraint))
    (hok : DbOk F DB) : DbEntailed F DB :=
  @DbOk.rec F
    (fun DB _ => DbEntailed F DB)
    (dbEntailed_init F)
    (fun DB c _ hs ih => dbEntailed_extend F DB c ih (dstep_entails F DB ih c hs))
    (fun DB i _ ih => dbEntailed_delete F DB i ih)
    DB hok

theorem evalTerms_le_coeffSum (a : Nat -> Bool) (ts : List Term) :
    AllNonneg ts -> Int.le (evalTerms a ts) (coeffSum ts) :=
  @List.rec Term
    (fun ts => AllNonneg ts -> Int.le (evalTerms a ts) (coeffSum ts))
    (fun _ => Int.le_refl 0)
    (fun t rest ih hn =>
      @Bool.rec
        (fun b : Bool =>
          Int.le (match b with
                  | true  => t.coeff + evalTerms a rest
                  | false => evalTerms a rest)
                 (t.coeff + coeffSum rest))
        (Int.le_trans (evalTerms a rest) (coeffSum rest) (t.coeff + coeffSum rest)
          (ih hn.right)
          (le_add_left_of_nonneg t.coeff (coeffSum rest) hn.left))
        (Int.add_le_add_left (evalTerms a rest) (coeffSum rest) (ih hn.right) t.coeff)
        (litVal a t.lit))
    ts

theorem not_holds_of_degree_gt_coeffSum (a : Nat -> Bool) (c : Constraint)
    (hn : AllNonneg c.terms) (hgt : Int.lt (coeffSum c.terms) c.degree)
    (hH : Holds a c) : False :=
  Int.lt_irrefl (coeffSum c.terms)
    (Int.lt_of_lt_of_le (coeffSum c.terms) c.degree (coeffSum c.terms)
      hgt
      (Int.le_trans c.degree (evalTerms a c.terms) (coeffSum c.terms)
        hH
        (evalTerms_le_coeffSum a c.terms hn)))

theorem checker_sound (F : List Constraint) (DB : List (Option Constraint)) (i : Nat)
    (cc : Constraint) (hok : DbOk F DB) (hg : getO DB i = some cc)
    (hn : AllNonneg cc.terms) (hgt : Int.lt (coeffSum cc.terms) cc.degree) : Unsat F :=
  fun a ha =>
    not_holds_of_degree_gt_coeffSum a cc hn hgt
      (dbOk_entailed F DB hok i cc hg a ha)

theorem entails_anything_of_entails_contradicting (F : List Constraint)
    (s t : Constraint) (hs : Entails F s)
    (hn : AllNonneg s.terms) (hgt : Int.lt (coeffSum s.terms) s.degree) :
    Entails F t :=
  fun a ha =>
    False.elim (not_holds_of_degree_gt_coeffSum a s hn hgt (hs a ha))

def holdsB (a : Nat -> Bool) (c : Constraint) : Bool :=
  Int.ble c.degree (evalTerms a c.terms)

def holdsAllB (a : Nat -> Bool) (F : List Constraint) : Bool :=
  match F with
  | []        => true
  | c :: rest =>
    match holdsB a c with
    | true  => holdsAllB a rest
    | false => false

theorem holds_of_holdsB (a : Nat -> Bool) (c : Constraint) (h : holdsB a c = true) :
    Holds a c :=
  Int.le_of_ble_eq_true c.degree (evalTerms a c.terms) h

theorem holdsAll_of_holdsAllB (a : Nat -> Bool) (F : List Constraint)
    (h : holdsAllB a F = true) : HoldsAll a F :=
  @List.rec Constraint
    (fun F => holdsAllB a F = true -> HoldsAll a F)
    (fun _ => True.intro)
    (fun c rest ih =>
      @Bool.rec
        (fun b : Bool =>
          (holdsB a c = b) ->
          (match b with
           | true  => holdsAllB a rest
           | false => false) = true ->
          And (Holds a c) (HoldsAll a rest))
        (fun _ hh => Bool.noConfusion hh)
        (fun hb hh => And.intro (holds_of_holdsB a c hb) (ih hh))
        (holdsB a c) rfl)
    F h

theorem sat_of_witness (F : List Constraint) (a : Nat -> Bool)
    (h : holdsAllB a F = true) (hU : Unsat F) : False :=
  hU a (holdsAll_of_holdsAllB a F h)

theorem ctrl_le_0_1 : Int.le 0 1 := Int.le_of_lt 0 1 int_lt_0_1

def ctrlC1 : Constraint :=
  { terms := [({ coeff := 1, lit := ctrlX } : Term)], degree := 1 }

def ctrlC2 : Constraint :=
  { terms := [({ coeff := 1, lit := ctrlNotX } : Term)], degree := 1 }

def F0 : List Constraint := [ctrlC1, ctrlC2]

theorem ctrl_nonneg_c1 : AllNonneg ctrlC1.terms := And.intro ctrl_le_0_1 True.intro

theorem ctrl_nonneg_c2 : AllNonneg ctrlC2.terms := And.intro ctrl_le_0_1 True.intro

theorem ctrl_trail : PropTrail (negC contradiction 0) (liftDB F0) [ctrlX] :=
  @PropTrail.step (negC contradiction 0) (liftDB F0) [] 1 ctrlC1 ctrlX
    (@PropTrail.nil (negC contradiction 0) (liftDB F0))
    rfl ctrl_nonneg_c1 int_lt_0_1

theorem ctrl_dstep : DStep (liftDB F0) contradiction :=
  @DStep.rupS (liftDB F0) contradiction 0 [ctrlX] 2 ctrlC2
    rfl ctrl_trail rfl ctrl_nonneg_c2 int_lt_0_1

theorem ctrl_dbok : DbOk F0 (List.append (liftDB F0) [some contradiction]) :=
  @DbOk.derive F0 (liftDB F0) contradiction (@DbOk.init F0) ctrl_dstep

theorem ctrl_rup_refutation_end_to_end : Unsat F0 :=
  checker_sound F0 (List.append (liftDB F0) [some contradiction]) 2 contradiction
    ctrl_dbok rfl True.intro int_lt_0_1

def ctrlDivC : Constraint :=
  { terms := [({ coeff := 4, lit := ctrlX } : Term)], degree := 3 }

def ctrlDivCut : Constraint := divC (fun x => intCeilDiv x 2) ctrlDivC

theorem ctrl_div_cut_terms :
    ctrlDivCut.terms = [({ coeff := 2, lit := ctrlX } : Term)] := rfl
theorem ctrl_div_cut_degree : ctrlDivCut.degree = 2 := rfl
theorem ctrl_div_cut_eval_true : evalTerms ctrlAllTrue ctrlDivCut.terms = 2 := rfl
theorem ctrl_div_cut_eval_false : evalTerms ctrlAllFalse ctrlDivCut.terms = 0 := rfl

theorem ctrl_div_concrete_entails : Entails [ctrlDivC] ctrlDivCut :=
  entails_divide_concrete [ctrlDivC] ctrlDivC 2 nat_le_1_2 (fun a ha => ha.left)

theorem ctrl_dstep_div : DStep (liftDB [ctrlDivC]) ctrlDivCut :=
  dstep_div_concrete (liftDB [ctrlDivC]) 2 nat_le_1_2 ctrlDivC
    (@DStep.ax (liftDB [ctrlDivC]) 0 ctrlDivC rfl)

theorem ctrl_dbok_div :
    DbOk [ctrlDivC] (List.append (liftDB [ctrlDivC]) [some ctrlDivCut]) :=
  @DbOk.derive [ctrlDivC] (liftDB [ctrlDivC]) ctrlDivCut
    (@DbOk.init [ctrlDivC]) ctrl_dstep_div

def ctrlMirC : Constraint :=
  { terms := [({ coeff := 5, lit := ctrlX } : Term)], degree := 5 }

def ctrlMirCut : Constraint :=
  { terms := mapCoeff (mirF 3 2) ctrlMirC.terms,
    degree := Int.mul (Int.add (intFloorDiv ctrlMirC.degree 3) 1) 2 }

theorem ctrl_mir_cut_terms :
    ctrlMirCut.terms = [({ coeff := 4, lit := ctrlX } : Term)] := rfl
theorem ctrl_mir_cut_degree : ctrlMirCut.degree = 4 := rfl
theorem ctrl_mir_cut_eval_false : evalTerms ctrlAllFalse ctrlMirCut.terms = 0 := rfl

theorem ctrl_mir_entails : Entails [ctrlMirC] ctrlMirCut :=
  entails_mir [ctrlMirC] ctrlMirC 3 2 nat_le_1_3
    (And.intro (int_zero_le_ofNat 5) True.intro)
    rfl int_lt_0_2 (fun a ha => ha.left)

theorem ctrl_mir_signed_entails : Entails [ctrlMirC] ctrlMirCut :=
  entails_mir_signed [ctrlMirC] ctrlMirC 3 2 nat_le_1_3 rfl int_lt_0_2
    (fun a ha => ha.left)

theorem ctrl_dstep_mir : DStep (liftDB [ctrlMirC]) ctrlMirCut :=
  @DStep.mirS (liftDB [ctrlMirC]) ctrlMirC 3 2 nat_le_1_3 rfl int_lt_0_2
    (@DStep.ax (liftDB [ctrlMirC]) 0 ctrlMirC rfl)

theorem ctrl_dbok_mir :
    DbOk [ctrlMirC] (List.append (liftDB [ctrlMirC]) [some ctrlMirCut]) :=
  @DbOk.derive [ctrlMirC] (liftDB [ctrlMirC]) ctrlMirCut
    (@DbOk.init [ctrlMirC]) ctrl_dstep_mir

def ctrlVfCut : Constraint :=
  { terms := vfMirTerms 3 2 ctrlVfC.terms,
    degree := Int.add (Int.mul (Int.add (intFloorDiv 2 3) 1) 2)
                      (negSum (vfMirTerms 3 2 ctrlVfC.terms)) }

theorem ctrl_dstep_mir_var : DStep (liftDB [ctrlVfC]) ctrlVfCut :=
  @DStep.mirVarS (liftDB [ctrlVfC]) ctrlVfC 3 2 2 nat_le_1_3 rfl rfl int_lt_0_2
    (@DStep.ax (liftDB [ctrlVfC]) 0 ctrlVfC rfl)

theorem ctrl_dbok_mir_var :
    DbOk [ctrlVfC] (List.append (liftDB [ctrlVfC]) [some ctrlVfCut]) :=
  @DbOk.derive [ctrlVfC] (liftDB [ctrlVfC]) ctrlVfCut
    (@DbOk.init [ctrlVfC]) ctrl_dstep_mir_var

theorem ctrl_mir_entailed_through_composition : Entails [ctrlMirC] ctrlMirCut :=
  dbOk_entailed [ctrlMirC] (List.append (liftDB [ctrlMirC]) [some ctrlMirCut])
    ctrl_dbok_mir 1 ctrlMirCut rfl

inductive WitVal where
  | keep
  | isTrue
  | isFalse
  | toLit (m : Lit)

def Wit : Type := Nat -> WitVal

def applyA (w : Wit) (a : Nat -> Bool) : Nat -> Bool :=
  fun v =>
    match w v with
    | WitVal.keep    => a v
    | WitVal.isTrue  => true
    | WitVal.isFalse => false
    | WitVal.toLit m => litVal a m

inductive LitImage where
  | const (b : Bool)
  | lit (m : Lit)

def litImageVal (a : Nat -> Bool) (i : LitImage) : Bool :=
  match i with
  | LitImage.const b => b
  | LitImage.lit m   => litVal a m

def substVar (w : Wit) (v : Nat) : LitImage :=
  match w v with
  | WitVal.keep    => LitImage.lit ({ var := v, negated := false } : Lit)
  | WitVal.isTrue  => LitImage.const true
  | WitVal.isFalse => LitImage.const false
  | WitVal.toLit m => LitImage.lit m

def negImage (i : LitImage) : LitImage :=
  match i with
  | LitImage.const b => LitImage.const (Bool.not b)
  | LitImage.lit m   => LitImage.lit (negLit m)

def substLit (w : Wit) (l : Lit) : LitImage :=
  match l.negated with
  | true  => negImage (substVar w l.var)
  | false => substVar w l.var

theorem litImageVal_substVar (w : Wit) (a : Nat -> Bool) (v : Nat) :
    litImageVal a (substVar w v) = applyA w a v :=
  @WitVal.rec
    (fun wv =>
      litImageVal a
        (match wv with
         | WitVal.keep    => LitImage.lit ({ var := v, negated := false } : Lit)
         | WitVal.isTrue  => LitImage.const true
         | WitVal.isFalse => LitImage.const false
         | WitVal.toLit m => LitImage.lit m)
      =
      (match wv with
       | WitVal.keep    => a v
       | WitVal.isTrue  => true
       | WitVal.isFalse => false
       | WitVal.toLit m => litVal a m))
    rfl rfl rfl (fun _ => rfl)
    (w v)

theorem litImageVal_negImage (a : Nat -> Bool) (i : LitImage) :
    litImageVal a (negImage i) = Bool.not (litImageVal a i) :=
  @LitImage.rec
    (fun i => litImageVal a (negImage i) = Bool.not (litImageVal a i))
    (fun _ => rfl)
    (fun m => litVal_negLit a m)
    i

theorem litVal_applyA (w : Wit) (a : Nat -> Bool) (l : Lit) :
    litVal (applyA w a) l = litImageVal a (substLit w l) :=
  @Bool.rec
    (fun n =>
      (match n with
       | true  => Bool.not (applyA w a l.var)
       | false => applyA w a l.var)
      =
      litImageVal a
        (match n with
         | true  => negImage (substVar w l.var)
         | false => substVar w l.var))
    (Eq.symm (litImageVal_substVar w a l.var))
    (Eq.trans
      (congrArg Bool.not (Eq.symm (litImageVal_substVar w a l.var)))
      (Eq.symm (litImageVal_negImage a (substVar w l.var))))
    l.negated

def consImage (t : Term) (i : LitImage) (rest : List Term) : List Term :=
  match i with
  | LitImage.const _ => rest
  | LitImage.lit m   => ({ coeff := t.coeff, lit := m } : Term) :: rest

def shiftImage (t : Term) (i : LitImage) (rest : Int) : Int :=
  match i with
  | LitImage.const b =>
    (match b with
     | true  => t.coeff + rest
     | false => rest)
  | LitImage.lit _ => rest

def substTerms (w : Wit) (ts : List Term) : List Term :=
  match ts with
  | []        => []
  | t :: rest => consImage t (substLit w t.lit) (substTerms w rest)

def substShift (w : Wit) (ts : List Term) : Int :=
  match ts with
  | []        => 0
  | t :: rest => shiftImage t (substLit w t.lit) (substShift w rest)

theorem evalTerms_applyA_step (w : Wit) (a : Nat -> Bool) (t : Term) (rest : List Term)
    (ih : evalTerms (applyA w a) rest
            = evalTerms a (substTerms w rest) + substShift w rest)
    (im : LitImage)
    (him : litVal (applyA w a) t.lit = litImageVal a im) :
    (match litVal (applyA w a) t.lit with
     | true  => t.coeff + evalTerms (applyA w a) rest
     | false => evalTerms (applyA w a) rest)
    = evalTerms a (consImage t im (substTerms w rest))
        + shiftImage t im (substShift w rest) :=
  @Eq.subst Bool
    (fun b =>
      (match b with
       | true  => t.coeff + evalTerms (applyA w a) rest
       | false => evalTerms (applyA w a) rest)
      = evalTerms a (consImage t im (substTerms w rest))
          + shiftImage t im (substShift w rest))
    (litImageVal a im) (litVal (applyA w a) t.lit) (Eq.symm him)
    (@LitImage.rec
      (fun i =>
        (match litImageVal a i with
         | true  => t.coeff + evalTerms (applyA w a) rest
         | false => evalTerms (applyA w a) rest)
        = evalTerms a (consImage t i (substTerms w rest))
            + shiftImage t i (substShift w rest))
      (fun b =>
        @Bool.rec
          (fun b =>
            (match b with
             | true  => t.coeff + evalTerms (applyA w a) rest
             | false => evalTerms (applyA w a) rest)
            = evalTerms a (substTerms w rest)
                + (match b with
                   | true  => t.coeff + substShift w rest
                   | false => substShift w rest))
          ih
          (Eq.trans
            (congrArg (fun z : Int => t.coeff + z) ih)
            (add_shuffle t.coeff (evalTerms a (substTerms w rest)) (substShift w rest)))
          b)
      (fun m =>
        @Bool.rec
          (fun bv =>
            (match bv with
             | true  => t.coeff + evalTerms (applyA w a) rest
             | false => evalTerms (applyA w a) rest)
            = (match bv with
               | true  => t.coeff + evalTerms a (substTerms w rest)
               | false => evalTerms a (substTerms w rest))
              + substShift w rest)
          ih
          (Eq.trans
            (congrArg (fun z : Int => t.coeff + z) ih)
            (Eq.symm (Int.add_assoc t.coeff (evalTerms a (substTerms w rest))
                       (substShift w rest))))
          (litVal a m))
      im)

theorem evalTerms_applyA (w : Wit) (a : Nat -> Bool) (ts : List Term) :
    evalTerms (applyA w a) ts = evalTerms a (substTerms w ts) + substShift w ts :=
  @List.rec Term
    (fun ts => evalTerms (applyA w a) ts
                 = evalTerms a (substTerms w ts) + substShift w ts)
    rfl
    (fun t rest ih =>
      evalTerms_applyA_step w a t rest ih (substLit w t.lit) (litVal_applyA w a t.lit))
    ts

def substC (w : Wit) (c : Constraint) : Constraint :=
  { terms := substTerms w c.terms, degree := c.degree - substShift w c.terms }

theorem holds_substC (w : Wit) (a : Nat -> Bool) (c : Constraint)
    (h : Holds a (substC w c)) : Holds (applyA w a) c :=
  @Eq.subst Int (fun z : Int => Int.le c.degree z)
    (evalTerms a (substTerms w c.terms) + substShift w c.terms)
    (evalTerms (applyA w a) c.terms)
    (Eq.symm (evalTerms_applyA w a c.terms))
    (le_add_of_sub_le c.degree (substShift w c.terms)
      (evalTerms a (substTerms w c.terms)) h)

def flattenDB (DB : List (Option Constraint)) : List Constraint :=
  match DB with
  | []        => []
  | o :: rest =>
    match o with
    | none   => flattenDB rest
    | some c => c :: flattenDB rest

theorem holdsAll_flattenDB (b : Nat -> Bool) (DB : List (Option Constraint)) :
    HoldsAllO b DB -> HoldsAll b (flattenDB DB) :=
  @List.rec (Option Constraint)
    (fun DB => HoldsAllO b DB -> HoldsAll b (flattenDB DB))
    (fun _ => True.intro)
    (fun o rest ih =>
      @Option.rec Constraint
        (fun o => HoldsAllO b (o :: rest) -> HoldsAll b (flattenDB (o :: rest)))
        (fun hall => ih hall)
        (fun c hall => And.intro hall.left (ih hall.right))
        o)
    DB

theorem holdsAllO_of_flattenDB (b : Nat -> Bool) (DB : List (Option Constraint)) :
    HoldsAll b (flattenDB DB) -> HoldsAllO b DB :=
  @List.rec (Option Constraint)
    (fun DB => HoldsAll b (flattenDB DB) -> HoldsAllO b DB)
    (fun _ => True.intro)
    (fun o rest ih =>
      @Option.rec Constraint
        (fun o => HoldsAll b (flattenDB (o :: rest)) -> HoldsAllO b (o :: rest))
        (fun hall => ih hall)
        (fun c hall => And.intro hall.left (ih hall.right))
        o)
    DB

theorem dbEntailed_flattenDB (DB : List (Option Constraint)) :
    DbEntailed (flattenDB DB) DB :=
  fun i c hg a hF => holdsAllO_get a DB i c (holdsAllO_of_flattenDB a DB hF) hg

theorem dstep_holds (DB : List (Option Constraint)) (c : Constraint) (hs : DStep DB c)
    (b : Nat -> Bool) (hb : HoldsAllO b DB) : Holds b c :=
  dstep_entails (flattenDB DB) DB (dbEntailed_flattenDB DB) c hs b
    (holdsAll_flattenDB b DB hb)

theorem holdsAllO_setNone (b : Nat -> Bool) (DB : List (Option Constraint)) :
    forall i : Nat, HoldsAllO b DB -> HoldsAllO b (setNone i DB) :=
  @List.rec (Option Constraint)
    (fun DB => forall i : Nat, HoldsAllO b DB -> HoldsAllO b (setNone i DB))
    (fun _ _ => True.intro)
    (fun o rest ih =>
      @Option.rec Constraint
        (fun o => forall i : Nat,
          HoldsAllO b (o :: rest) -> HoldsAllO b (setNone i (o :: rest)))
        (fun i =>
          @Nat.rec
            (fun i => HoldsAllO b (none :: rest) -> HoldsAllO b (setNone i (none :: rest)))
            (fun hall => hall)
            (fun j _ hall => ih j hall)
            i)
        (fun c i =>
          @Nat.rec
            (fun i => HoldsAllO b (some c :: rest) ->
                      HoldsAllO b (setNone i (some c :: rest)))
            (fun hall => hall.right)
            (fun j _ hall => And.intro hall.left (ih j hall.right))
            i)
        o)
    DB

def DbSat (F : List Constraint) (DB : List (Option Constraint)) : Prop :=
  (forall b : Nat -> Bool, HoldsAllO b DB -> False) -> Unsat F

theorem dbSat_of_entailed (F : List Constraint) (DB : List (Option Constraint))
    (hdb : DbEntailed F DB) : DbSat F DB :=
  fun hno a hF => hno a (holdsAllO_of_entailed F a hF DB hdb)

theorem holdsAllO_append_some (b : Nat -> Bool) (c : Constraint)
    (DB : List (Option Constraint)) :
    HoldsAllO b DB -> Holds b c -> HoldsAllO b (List.append DB [some c]) :=
  @List.rec (Option Constraint)
    (fun DB => HoldsAllO b DB -> Holds b c -> HoldsAllO b (List.append DB [some c]))
    (fun _ hc => And.intro hc True.intro)
    (fun o rest ih =>
      @Option.rec Constraint
        (fun o => HoldsAllO b (o :: rest) -> Holds b c ->
                  HoldsAllO b (List.append (o :: rest) [some c]))
        (fun hall hc => ih hall hc)
        (fun c' hall hc => And.intro hall.left (ih hall.right hc))
        o)
    DB

theorem holds_cases (b : Nat -> Bool) (c : Constraint) (P : Prop)
    (hyes : Holds b c -> P) (hnot : (Holds b c -> False) -> P) : P :=
  @Bool.rec
    (fun bl => Int.ble c.degree (evalTerms b c.terms) = bl -> P)
    (fun heq =>
      hnot (fun hH =>
        @Bool.noConfusion False true false
          (Eq.trans
            (Eq.symm (Int.ble_eq_true_of_le c.degree (evalTerms b c.terms) hH))
            heq)))
    (fun heq => hyes (Int.le_of_ble_eq_true c.degree (evalTerms b c.terms) heq))
    (Int.ble c.degree (evalTerms b c.terms))
    rfl

theorem dbSat_red (F : List Constraint) (DB : List (Option Constraint))
    (c : Constraint) (w : Wit) (hdb : DbSat F DB)
    (hgoal : forall b : Nat -> Bool,
      HoldsAllO b DB -> (Holds b c -> False) ->
      And (HoldsAllO (applyA w b) DB) (Holds (applyA w b) c)) :
    DbSat F (List.append DB [some c]) :=
  fun hno =>
    hdb (fun b hb =>
      holds_cases b c False
        (fun hc => hno b (holdsAllO_append_some b c DB hb hc))
        (fun hnc =>
          @And.rec (HoldsAllO (applyA w b) DB) (Holds (applyA w b) c) (fun _ => False)
            (fun hDB' hc' =>
              hno (applyA w b) (holdsAllO_append_some (applyA w b) c DB hDB' hc'))
            (hgoal b hb hnc)))

theorem dbSat_red_of_substituted (F : List Constraint) (DB : List (Option Constraint))
    (c : Constraint) (w : Wit) (hdb : DbSat F DB)
    (hgoal : forall b : Nat -> Bool,
      HoldsAllO b DB -> (Holds b c -> False) ->
      And (HoldsAllO (applyA w b) DB) (Holds b (substC w c))) :
    DbSat F (List.append DB [some c]) :=
  dbSat_red F DB c w hdb
    (fun b hb hnc =>
      @And.rec (HoldsAllO (applyA w b) DB) (Holds b (substC w c))
        (fun _ => And (HoldsAllO (applyA w b) DB) (Holds (applyA w b) c))
        (fun hDB' hsub => And.intro hDB' (holds_substC w b c hsub))
        (hgoal b hb hnc))

inductive DbOkR (F : List Constraint) : List (Option Constraint) -> Prop where
  | init : DbOkR F (liftDB F)
  | derive : forall (DB : List (Option Constraint)) (c : Constraint),
      DbOkR F DB -> DStep DB c -> DbOkR F (List.append DB [some c])
  | delete : forall (DB : List (Option Constraint)) (i : Nat),
      DbOkR F DB -> DbOkR F (setNone i DB)
  | red : forall (DB : List (Option Constraint)) (c : Constraint) (w : Wit),
      DbOkR F DB ->
      (forall b : Nat -> Bool,
        HoldsAllO b DB -> (Holds b c -> False) ->
        And (HoldsAllO (applyA w b) DB) (Holds b (substC w c))) ->
      DbOkR F (List.append DB [some c])

theorem dbSat_delete (F : List Constraint) (DB : List (Option Constraint)) (i : Nat)
    (h : DbSat F DB) : DbSat F (setNone i DB) :=
  fun hno => h (fun b hb => hno b (holdsAllO_setNone b DB i hb))

theorem dbSat_derive (F : List Constraint) (DB : List (Option Constraint))
    (c : Constraint) (h : DbSat F DB) (hs : DStep DB c) :
    DbSat F (List.append DB [some c]) :=
  fun hno =>
    h (fun b hb =>
      hno b (holdsAllO_append_some b c DB hb (dstep_holds DB c hs b hb)))

theorem dbOkR_sat (F : List Constraint) (DB : List (Option Constraint))
    (hok : DbOkR F DB) : DbSat F DB :=
  @DbOkR.rec F
    (fun DB _ => DbSat F DB)
    (dbSat_of_entailed F (liftDB F) (dbEntailed_init F))
    (fun DB c _ hs ih => dbSat_derive F DB c ih hs)
    (fun DB i _ ih => dbSat_delete F DB i ih)
    (fun DB c w _ hg ih => dbSat_red_of_substituted F DB c w ih hg)
    DB hok

theorem checker_sound_red (F : List Constraint) (DB : List (Option Constraint)) (i : Nat)
    (cc : Constraint) (hok : DbOkR F DB) (hg : getO DB i = some cc)
    (hn : AllNonneg cc.terms) (hgt : Int.lt (coeffSum cc.terms) cc.degree) : Unsat F :=
  dbOkR_sat F DB hok
    (fun b hb =>
      not_holds_of_degree_gt_coeffSum b cc hn hgt (holdsAllO_get b DB i cc hb hg))

def substDB (w : Wit) (DB : List (Option Constraint)) : List (Option Constraint) :=
  match DB with
  | []        => []
  | o :: rest =>
    (match o with
     | none   => none
     | some c => some (substC w c)) :: substDB w rest

theorem holdsAllO_applyA_of_substDB (w : Wit) (b : Nat -> Bool)
    (DB : List (Option Constraint)) :
    HoldsAllO b (substDB w DB) -> HoldsAllO (applyA w b) DB :=
  @List.rec (Option Constraint)
    (fun DB => HoldsAllO b (substDB w DB) -> HoldsAllO (applyA w b) DB)
    (fun _ => True.intro)
    (fun o rest ih =>
      @Option.rec Constraint
        (fun o => HoldsAllO b (substDB w (o :: rest)) -> HoldsAllO (applyA w b) (o :: rest))
        (fun hall => ih hall)
        (fun c hall =>
          And.intro (holds_substC w b c hall.left) (ih hall.right))
        o)
    DB

theorem dbSat_red_of_goals (F : List Constraint) (DB : List (Option Constraint))
    (c : Constraint) (w : Wit) (hdb : DbSat F DB)
    (hgoal : forall b : Nat -> Bool,
      HoldsAllO b DB -> (Holds b c -> False) ->
      And (HoldsAllO b (substDB w DB)) (Holds b (substC w c))) :
    DbSat F (List.append DB [some c]) :=
  dbSat_red_of_substituted F DB c w hdb
    (fun b hb hnc =>
      @And.rec (HoldsAllO b (substDB w DB)) (Holds b (substC w c))
        (fun _ => And (HoldsAllO (applyA w b) DB) (Holds b (substC w c)))
        (fun hsub hc => And.intro (holdsAllO_applyA_of_substDB w b DB hsub) hc)
        (hgoal b hb hnc))

theorem dbOkR_red_of_goals (F : List Constraint) (DB : List (Option Constraint))
    (c : Constraint) (w : Wit) (hok : DbOkR F DB)
    (hgoal : forall b : Nat -> Bool,
      HoldsAllO b DB -> (Holds b c -> False) ->
      And (HoldsAllO b (substDB w DB)) (Holds b (substC w c))) :
    DbOkR F (List.append DB [some c]) :=
  @DbOkR.red F DB c w hok
    (fun b hb hnc =>
      @And.rec (HoldsAllO b (substDB w DB)) (Holds b (substC w c))
        (fun _ => And (HoldsAllO (applyA w b) DB) (Holds b (substC w c)))
        (fun hsub hc => And.intro (holdsAllO_applyA_of_substDB w b DB hsub) hc)
        (hgoal b hb hnc))

def blockLit (sigma : Nat -> Bool) (v : Nat) : Lit :=
  { var := v, negated := sigma v }

theorem eq_of_blockLit_false (sigma a : Nat -> Bool) (v : Nat)
    (h : Eq (litVal a (blockLit sigma v)) Bool.false) : Eq (a v) (sigma v) :=
  @Bool.rec
    (fun sv =>
      Eq (match sv with
          | true  => Bool.not (a v)
          | false => a v)
         Bool.false
      -> Eq (a v) sv)
    (fun hf => hf)
    (fun ht =>
      @Bool.rec
        (fun av => Eq (Bool.not av) Bool.false -> Eq av Bool.true)
        (fun hb => Bool.noConfusion hb)
        (fun _ => rfl)
        (a v)
        ht)
    (sigma v)
    h

def AgreesOn (a sigma : Nat -> Bool) (vars : List Nat) : Prop :=
  match vars with
  | []        => True
  | v :: rest => And (Eq (a v) (sigma v)) (AgreesOn a sigma rest)

def blockTerms (sigma : Nat -> Bool) (vars : List Nat) : List Term :=
  match vars with
  | []        => []
  | v :: rest =>
    ({ coeff := 1, lit := blockLit sigma v } : Term) :: blockTerms sigma rest

def blockC (sigma : Nat -> Bool) (vars : List Nat) : Constraint :=
  { terms := blockTerms sigma vars, degree := 1 }

theorem allNonneg_blockTerms (sigma : Nat -> Bool) (vars : List Nat) :
    AllNonneg (blockTerms sigma vars) :=
  @List.rec Nat
    (fun vars => AllNonneg (blockTerms sigma vars))
    True.intro
    (fun _ _ ih => And.intro int_le_0_1 ih)
    vars

theorem blockC_step (sigma a : Nat -> Bool) (v : Nat) (rest : List Nat)
    (hn : Holds a (blockC sigma (v :: rest)) -> False) :
    And (Eq (a v) (sigma v)) (Holds a (blockC sigma rest) -> False) :=
  @Bool.rec
    (fun b =>
      Eq (litVal a (blockLit sigma v)) b ->
      And (Eq (a v) (sigma v)) (Holds a (blockC sigma rest) -> False))
    (fun heq =>
      And.intro
        (eq_of_blockLit_false sigma a v heq)
        (fun hh =>
          hn
            (@Eq.subst Bool
              (fun b : Bool =>
                Int.le 1 (match b with
                          | true  => 1 + evalTerms a (blockTerms sigma rest)
                          | false => evalTerms a (blockTerms sigma rest)))
              Bool.false (litVal a (blockLit sigma v)) (Eq.symm heq) hh)))
    (fun heq =>
      False.elim
        (hn
          (@Eq.subst Bool
            (fun b : Bool =>
              Int.le 1 (match b with
                        | true  => 1 + evalTerms a (blockTerms sigma rest)
                        | false => evalTerms a (blockTerms sigma rest)))
            Bool.true (litVal a (blockLit sigma v)) (Eq.symm heq)
            (le_add_right_of_nonneg 1 (evalTerms a (blockTerms sigma rest))
              (evalTerms_nonneg a (blockTerms sigma rest)
                (allNonneg_blockTerms sigma rest))))))
    (litVal a (blockLit sigma v))
    rfl

theorem agrees_of_not_holds_blockC (sigma a : Nat -> Bool) (vars : List Nat) :
    (Holds a (blockC sigma vars) -> False) -> AgreesOn a sigma vars :=
  @List.rec Nat
    (fun vars => (Holds a (blockC sigma vars) -> False) -> AgreesOn a sigma vars)
    (fun _ => True.intro)
    (fun v rest ih hn =>
      @And.rec (Eq (a v) (sigma v)) (Holds a (blockC sigma rest) -> False)
        (fun _ => AgreesOn a sigma (v :: rest))
        (fun hv hrest => And.intro hv (ih hrest))
        (blockC_step sigma a v rest hn))
    vars

structure Excl where
  sol : Nat -> Bool
  vars : List Nat

def Excluded (a : Nat -> Bool) (excls : List Excl) : Prop :=
  match excls with
  | []        => False
  | e :: rest => Or (AgreesOn a e.sol e.vars) (Excluded a rest)

def DbEnum (F : List Constraint) (excls : List Excl)
    (DB : List (Option Constraint)) : Prop :=
  forall a : Nat -> Bool, HoldsAll a F -> Or (HoldsAllO a DB) (Excluded a excls)

inductive DbOkE (F : List Constraint) : List Excl -> List (Option Constraint) -> Prop where
  | init : DbOkE F [] (liftDB F)
  | derive : forall (excls : List Excl) (DB : List (Option Constraint)) (c : Constraint),
      DbOkE F excls DB -> DStep DB c -> DbOkE F excls (List.append DB [some c])
  | delete : forall (excls : List Excl) (DB : List (Option Constraint)) (i : Nat),
      DbOkE F excls DB -> DbOkE F excls (setNone i DB)
  | exclude : forall (excls : List Excl) (DB : List (Option Constraint))
      (sigma : Nat -> Bool) (vars : List Nat),
      DbOkE F excls DB ->
      DbOkE F ({ sol := sigma, vars := vars } :: excls)
        (List.append DB [some (blockC sigma vars)])

theorem dbEnum_init (F : List Constraint) : DbEnum F [] (liftDB F) :=
  fun a hF =>
    Or.inl (holdsAllO_of_entailed F a hF (liftDB F) (dbEntailed_init F))

theorem dbEnum_derive (F : List Constraint) (excls : List Excl)
    (DB : List (Option Constraint)) (c : Constraint)
    (ih : DbEnum F excls DB) (hs : DStep DB c) :
    DbEnum F excls (List.append DB [some c]) :=
  fun a hF =>
    @Or.rec (HoldsAllO a DB) (Excluded a excls)
      (fun _ => Or (HoldsAllO a (List.append DB [some c])) (Excluded a excls))
      (fun hDB =>
        Or.inl (holdsAllO_append_some a c DB hDB (dstep_holds DB c hs a hDB)))
      (fun he => Or.inr he)
      (ih a hF)

theorem dbEnum_delete (F : List Constraint) (excls : List Excl)
    (DB : List (Option Constraint)) (i : Nat) (ih : DbEnum F excls DB) :
    DbEnum F excls (setNone i DB) :=
  fun a hF =>
    @Or.rec (HoldsAllO a DB) (Excluded a excls)
      (fun _ => Or (HoldsAllO a (setNone i DB)) (Excluded a excls))
      (fun hDB => Or.inl (holdsAllO_setNone a DB i hDB))
      (fun he => Or.inr he)
      (ih a hF)

theorem dbEnum_exclude (F : List Constraint) (excls : List Excl)
    (DB : List (Option Constraint)) (sigma : Nat -> Bool) (vars : List Nat)
    (ih : DbEnum F excls DB) :
    DbEnum F ({ sol := sigma, vars := vars } :: excls)
      (List.append DB [some (blockC sigma vars)]) :=
  fun a hF =>
    @Or.rec (HoldsAllO a DB) (Excluded a excls)
      (fun _ =>
        Or (HoldsAllO a (List.append DB [some (blockC sigma vars)]))
           (Excluded a ({ sol := sigma, vars := vars } :: excls)))
      (fun hDB =>
        holds_cases a (blockC sigma vars)
          (Or (HoldsAllO a (List.append DB [some (blockC sigma vars)]))
              (Excluded a ({ sol := sigma, vars := vars } :: excls)))
          (fun hb =>
            Or.inl (holdsAllO_append_some a (blockC sigma vars) DB hDB hb))
          (fun hnb =>
            Or.inr (Or.inl (agrees_of_not_holds_blockC sigma a vars hnb))))
      (fun he => Or.inr (Or.inr he))
      (ih a hF)

theorem dbOkE_enum (F : List Constraint) (excls : List Excl)
    (DB : List (Option Constraint)) (hok : DbOkE F excls DB) : DbEnum F excls DB :=
  @DbOkE.rec F
    (fun excls DB _ => DbEnum F excls DB)
    (dbEnum_init F)
    (fun excls DB c _ hs ih => dbEnum_derive F excls DB c ih hs)
    (fun excls DB i _ ih => dbEnum_delete F excls DB i ih)
    (fun excls DB sigma vars _ ih => dbEnum_exclude F excls DB sigma vars ih)
    excls DB hok

theorem enumeration_complete (F : List Constraint) (excls : List Excl)
    (DB : List (Option Constraint)) (i : Nat) (cc : Constraint)
    (hok : DbOkE F excls DB) (hg : getO DB i = some cc)
    (hn : AllNonneg cc.terms) (hgt : Int.lt (coeffSum cc.terms) cc.degree)
    (a : Nat -> Bool) (hF : HoldsAll a F) : Excluded a excls :=
  @Or.rec (HoldsAllO a DB) (Excluded a excls) (fun _ => Excluded a excls)
    (fun hDB =>
      False.elim
        (not_holds_of_degree_gt_coeffSum a cc hn hgt
          (holdsAllO_get a DB i cc hDB hg)))
    (fun he => he)
    (dbOkE_enum F excls DB hok a hF)

theorem le_sub_of_add_le (v n k : Int) (h : Int.le (v + n) k) : Int.le v (k - n) :=
  le_cancel_right v n (k - n)
    (le_congr_right k ((k - n) + n) (v + n) (Eq.symm (sub_add_cancel k n)) h)

theorem add_le_of_le_sub (v n k : Int) (h : Int.le v (k - n)) : Int.le (v + n) k :=
  le_congr_right ((k - n) + n) k (v + n) (sub_add_cancel k n)
    (Int.add_le_add_right v (k - n) h n)

def objValNeg (negObj : List Term) (konst : Int) (a : Nat -> Bool) : Int :=
  konst - evalTerms a negObj

def improveC (negObj : List Term) (konst v : Int) : Constraint :=
  { terms := negObj, degree := 1 + konst - v }

theorem bound_of_not_holds_improveC (negObj : List Term) (konst v : Int)
    (a : Nat -> Bool) (hn : Holds a (improveC negObj konst v) -> False) :
    Int.le v (objValNeg negObj konst a) :=

  @Or.rec (Int.lt konst (v + evalTerms a negObj))
    (Or (Eq konst (v + evalTerms a negObj))
        (Int.lt (v + evalTerms a negObj) konst))
    (fun _ => Int.le v (objValNeg negObj konst a))
    (fun hlt =>
      False.elim
        (hn
          (le_sub_of_le_add (1 + konst) v (evalTerms a negObj)
            (le_congr_left (konst + 1) (1 + konst)
              (evalTerms a negObj + v)
              (Int.add_comm konst 1)
              (le_congr_right (v + evalTerms a negObj)
                (evalTerms a negObj + v) (konst + 1)
                (Int.add_comm v (evalTerms a negObj))
                hlt)))))
    (fun hrest =>
      @Or.rec (Eq konst (v + evalTerms a negObj))
        (Int.lt (v + evalTerms a negObj) konst)
        (fun _ => Int.le v (objValNeg negObj konst a))
        (fun heq =>
          le_sub_of_add_le v (evalTerms a negObj) konst
            (@Eq.subst Int (fun z : Int => Int.le (v + evalTerms a negObj) z)
              (v + evalTerms a negObj) konst (Eq.symm heq)
              (Int.le_refl (v + evalTerms a negObj))))
        (fun hgt =>
          le_sub_of_add_le v (evalTerms a negObj) konst
            (Int.le_of_lt (v + evalTerms a negObj) konst hgt))
        hrest)
    (Int.lt_trichotomy konst (v + evalTerms a negObj))

def DbBound (F : List Constraint) (negObj : List Term) (konst bound : Int)
    (DB : List (Option Constraint)) : Prop :=
  forall a : Nat -> Bool,
    HoldsAll a F -> Or (HoldsAllO a DB) (Int.le bound (objValNeg negObj konst a))

theorem dbBound_init (F : List Constraint) (negObj : List Term) (konst bound : Int) :
    DbBound F negObj konst bound (liftDB F) :=
  fun a hF =>
    Or.inl (holdsAllO_of_entailed F a hF (liftDB F) (dbEntailed_init F))

theorem dbBound_derive (F : List Constraint) (negObj : List Term) (konst bound : Int)
    (DB : List (Option Constraint)) (c : Constraint)
    (ih : DbBound F negObj konst bound DB) (hs : DStep DB c) :
    DbBound F negObj konst bound (List.append DB [some c]) :=
  fun a hF =>
    @Or.rec (HoldsAllO a DB) (Int.le bound (objValNeg negObj konst a))
      (fun _ =>
        Or (HoldsAllO a (List.append DB [some c]))
           (Int.le bound (objValNeg negObj konst a)))
      (fun hDB =>
        Or.inl (holdsAllO_append_some a c DB hDB (dstep_holds DB c hs a hDB)))
      (fun hb => Or.inr hb)
      (ih a hF)

theorem dbBound_delete (F : List Constraint) (negObj : List Term) (konst bound : Int)
    (DB : List (Option Constraint)) (i : Nat) (ih : DbBound F negObj konst bound DB) :
    DbBound F negObj konst bound (setNone i DB) :=
  fun a hF =>
    @Or.rec (HoldsAllO a DB) (Int.le bound (objValNeg negObj konst a))
      (fun _ =>
        Or (HoldsAllO a (setNone i DB)) (Int.le bound (objValNeg negObj konst a)))
      (fun hDB => Or.inl (holdsAllO_setNone a DB i hDB))
      (fun hb => Or.inr hb)
      (ih a hF)

theorem dbBound_improve (F : List Constraint) (negObj : List Term)
    (konst bound v : Int) (DB : List (Option Constraint))
    (hv : Int.le v bound) (ih : DbBound F negObj konst bound DB) :
    DbBound F negObj konst v (List.append DB [some (improveC negObj konst v)]) :=
  fun a hF =>
    @Or.rec (HoldsAllO a DB) (Int.le bound (objValNeg negObj konst a))
      (fun _ =>
        Or (HoldsAllO a (List.append DB [some (improveC negObj konst v)]))
           (Int.le v (objValNeg negObj konst a)))
      (fun hDB =>
        holds_cases a (improveC negObj konst v)
          (Or (HoldsAllO a (List.append DB [some (improveC negObj konst v)]))
              (Int.le v (objValNeg negObj konst a)))
          (fun hh =>
            Or.inl (holdsAllO_append_some a (improveC negObj konst v) DB hDB hh))
          (fun hnh =>
            Or.inr (bound_of_not_holds_improveC negObj konst v a hnh)))
      (fun hb =>
        Or.inr (Int.le_trans v bound (objValNeg negObj konst a) hv hb))
      (ih a hF)

inductive DbOkB (F : List Constraint) (negObj : List Term) (konst : Int) :
    Int -> List (Option Constraint) -> Prop where
  | init : forall bound : Int, DbOkB F negObj konst bound (liftDB F)
  | derive : forall (bound : Int) (DB : List (Option Constraint)) (c : Constraint),
      DbOkB F negObj konst bound DB -> DStep DB c ->
      DbOkB F negObj konst bound (List.append DB [some c])
  | delete : forall (bound : Int) (DB : List (Option Constraint)) (i : Nat),
      DbOkB F negObj konst bound DB -> DbOkB F negObj konst bound (setNone i DB)
  | improve : forall (bound v : Int) (DB : List (Option Constraint)),
      DbOkB F negObj konst bound DB -> Int.le v bound ->
      DbOkB F negObj konst v (List.append DB [some (improveC negObj konst v)])

theorem dbOkB_bound (F : List Constraint) (negObj : List Term) (konst : Int)
    (bound : Int) (DB : List (Option Constraint))
    (hok : DbOkB F negObj konst bound DB) : DbBound F negObj konst bound DB :=
  @DbOkB.rec F negObj konst
    (fun bound DB _ => DbBound F negObj konst bound DB)
    (fun bound => dbBound_init F negObj konst bound)
    (fun bound DB c _ hs ih => dbBound_derive F negObj konst bound DB c ih hs)
    (fun bound DB i _ ih => dbBound_delete F negObj konst bound DB i ih)
    (fun bound v DB _ hv ih => dbBound_improve F negObj konst bound v DB hv ih)
    bound DB hok

theorem bound_complete (F : List Constraint) (negObj : List Term)
    (konst bound : Int) (DB : List (Option Constraint)) (i : Nat) (cc : Constraint)
    (hok : DbOkB F negObj konst bound DB) (hg : getO DB i = some cc)
    (hn : AllNonneg cc.terms) (hgt : Int.lt (coeffSum cc.terms) cc.degree)
    (a : Nat -> Bool) (hF : HoldsAll a F) :
    Int.le bound (objValNeg negObj konst a) :=
  @Or.rec (HoldsAllO a DB) (Int.le bound (objValNeg negObj konst a))
    (fun _ => Int.le bound (objValNeg negObj konst a))
    (fun hDB =>
      False.elim
        (not_holds_of_degree_gt_coeffSum a cc hn hgt
          (holdsAllO_get a DB i cc hDB hg)))
    (fun hb => hb)
    (dbOkB_bound F negObj konst bound DB hok a hF)

def MemN (v : Nat) (vars : List Nat) : Prop :=
  match vars with
  | []        => False
  | w :: rest => Or (Eq v w) (MemN v rest)

def SubsetN (xs ys : List Nat) : Prop :=
  forall v : Nat, MemN v xs -> MemN v ys

theorem agreesOn_mem (a b : Nat -> Bool) (v : Nat) (vars : List Nat) :
    AgreesOn a b vars -> MemN v vars -> Eq (a v) (b v) :=
  @List.rec Nat
    (fun vars => AgreesOn a b vars -> MemN v vars -> Eq (a v) (b v))
    (fun _ hm => False.elim hm)
    (fun w rest ih hag hm =>
      @Or.rec (Eq v w) (MemN v rest) (fun _ => Eq (a v) (b v))
        (fun heq =>
          @Eq.subst Nat (fun z : Nat => Eq (a z) (b z)) w v (Eq.symm heq) hag.left)
        (fun hrest => ih hag.right hrest)
        hm)
    vars

theorem agreesOn_of_mem (a b : Nat -> Bool) (vars : List Nat) :
    (forall v : Nat, MemN v vars -> Eq (a v) (b v)) -> AgreesOn a b vars :=
  @List.rec Nat
    (fun vars =>
      (forall v : Nat, MemN v vars -> Eq (a v) (b v)) -> AgreesOn a b vars)
    (fun _ => True.intro)
    (fun w rest ih h =>
      And.intro
        (h w (Or.inl rfl))
        (ih (fun v hm => h v (Or.inr hm))))
    vars

theorem agreesOn_refl (a : Nat -> Bool) (vars : List Nat) : AgreesOn a a vars :=
  @List.rec Nat
    (fun vars => AgreesOn a a vars)
    True.intro
    (fun _ _ ih => And.intro rfl ih)
    vars

theorem agreesOn_symm (a b : Nat -> Bool) (vars : List Nat) :
    AgreesOn a b vars -> AgreesOn b a vars :=
  @List.rec Nat
    (fun vars => AgreesOn a b vars -> AgreesOn b a vars)
    (fun _ => True.intro)
    (fun _ _ ih h => And.intro (Eq.symm h.left) (ih h.right))
    vars

theorem agreesOn_trans (a b c : Nat -> Bool) (vars : List Nat) :
    AgreesOn a b vars -> AgreesOn b c vars -> AgreesOn a c vars :=
  @List.rec Nat
    (fun vars => AgreesOn a b vars -> AgreesOn b c vars -> AgreesOn a c vars)
    (fun _ _ => True.intro)
    (fun _ _ ih h1 h2 => And.intro (Eq.trans h1.left h2.left) (ih h1.right h2.right))
    vars

theorem agreesOn_of_subset (a b : Nat -> Bool) (xs ys : List Nat)
    (hsub : SubsetN xs ys) (hag : AgreesOn a b ys) : AgreesOn a b xs :=
  agreesOn_of_mem a b xs (fun v hm => agreesOn_mem a b v ys hag (hsub v hm))

def termVars (ts : List Term) : List Nat :=
  match ts with
  | []        => []
  | t :: rest => t.lit.var :: termVars rest

theorem litVal_congr (a b : Nat -> Bool) (l : Lit) (h : Eq (a l.var) (b l.var)) :
    Eq (litVal a l) (litVal b l) :=
  @Bool.rec
    (fun n =>
      Eq (match n with
          | true  => Bool.not (a l.var)
          | false => a l.var)
         (match n with
          | true  => Bool.not (b l.var)
          | false => b l.var))
    h
    (congrArg Bool.not h)
    l.negated

theorem evalTerms_congr_agrees (a b : Nat -> Bool) (ts : List Term) :
    AgreesOn a b (termVars ts) -> Eq (evalTerms a ts) (evalTerms b ts) :=
  @List.rec Term
    (fun ts => AgreesOn a b (termVars ts) -> Eq (evalTerms a ts) (evalTerms b ts))
    (fun _ => rfl)
    (fun t rest ih hag =>
      @Eq.subst Bool
        (fun bl =>
          Eq (match litVal a t.lit with
              | true  => t.coeff + evalTerms a rest
              | false => evalTerms a rest)
             (match bl with
              | true  => t.coeff + evalTerms b rest
              | false => evalTerms b rest))
        (litVal a t.lit) (litVal b t.lit) (litVal_congr a b t.lit hag.left)
        (@Bool.rec
          (fun bl =>
            Eq (match bl with
                | true  => t.coeff + evalTerms a rest
                | false => evalTerms a rest)
               (match bl with
                | true  => t.coeff + evalTerms b rest
                | false => evalTerms b rest))
          (ih hag.right)
          (congrArg (fun z : Int => t.coeff + z) (ih hag.right))
          (litVal a t.lit)))
    ts

def WitFixes (w : Wit) (vars : List Nat) : Prop :=
  match vars with
  | []        => True
  | v :: rest => And (Eq (w v) WitVal.keep) (WitFixes w rest)

theorem agrees_applyA_of_fixes (w : Wit) (a : Nat -> Bool) (vars : List Nat) :
    WitFixes w vars -> AgreesOn (applyA w a) a vars :=
  @List.rec Nat
    (fun vars => WitFixes w vars -> AgreesOn (applyA w a) a vars)
    (fun _ => True.intro)
    (fun v rest ih hf =>
      And.intro
        (@Eq.subst WitVal
          (fun wv : WitVal =>
            Eq (match wv with
                | WitVal.keep    => a v
                | WitVal.isTrue  => true
                | WitVal.isFalse => false
                | WitVal.toLit m => litVal a m)
               (a v))
          WitVal.keep (w v) (Eq.symm hf.left) rfl)
        (ih hf.right))
    vars

def BoundHolds (negObj : List Term) (konst : Int) (bound : Option Int)
    (a : Nat -> Bool) : Prop :=
  match bound with
  | none   => False
  | some b => Int.le b (objValNeg negObj konst a)

def BoundLe (v : Int) (bound : Option Int) : Prop :=
  match bound with
  | none   => True
  | some b => Int.le v b

theorem boundHolds_of_le (negObj : List Term) (konst v : Int) (bound : Option Int)
    (a : Nat -> Bool) (hle : BoundLe v bound)
    (h : BoundHolds negObj konst bound a) :
    BoundHolds negObj konst (some v) a :=
  @Option.rec Int
    (fun bnd =>
      BoundLe v bnd -> BoundHolds negObj konst bnd a ->
      BoundHolds negObj konst (some v) a)
    (fun _ hf => False.elim hf)
    (fun b0 hle0 h0 => Int.le_trans v b0 (objValNeg negObj konst a) hle0 h0)
    bound hle h

def Companion (P : List Nat) (DB : List (Option Constraint)) (a : Nat -> Bool) : Prop :=
  Exists (fun b : Nat -> Bool => And (HoldsAllO b DB) (AgreesOn b a P))

def DbFull (F : List Constraint) (P : List Nat) (excls : List Excl)
    (negObj : List Term) (konst : Int) (bound : Option Int)
    (DB : List (Option Constraint)) : Prop :=
  forall a : Nat -> Bool,
    HoldsAll a F ->
    Or (Companion P DB a)
       (Or (Excluded a excls) (BoundHolds negObj konst bound a))

theorem dbFull_init (F : List Constraint) (P : List Nat) (negObj : List Term)
    (konst : Int) : DbFull F P [] negObj konst none (liftDB F) :=
  fun a hF =>
    Or.inl
      (Exists.intro a
        (And.intro
          (holdsAllO_of_entailed F a hF (liftDB F) (dbEntailed_init F))
          (agreesOn_refl a P)))

theorem dbFull_derive (F : List Constraint) (P : List Nat) (excls : List Excl)
    (negObj : List Term) (konst : Int) (bound : Option Int)
    (DB : List (Option Constraint)) (c : Constraint)
    (ih : DbFull F P excls negObj konst bound DB) (hs : DStep DB c) :
    DbFull F P excls negObj konst bound (List.append DB [some c]) :=
  fun a hF =>
    @Or.rec (Companion P DB a)
      (Or (Excluded a excls) (BoundHolds negObj konst bound a))
      (fun _ =>
        Or (Companion P (List.append DB [some c]) a)
           (Or (Excluded a excls) (BoundHolds negObj konst bound a)))
      (fun hcomp =>
        @Exists.rec (Nat -> Bool)
          (fun b : Nat -> Bool => And (HoldsAllO b DB) (AgreesOn b a P))
          (fun _ =>
            Or (Companion P (List.append DB [some c]) a)
               (Or (Excluded a excls) (BoundHolds negObj konst bound a)))
          (fun b hb =>
            Or.inl
              (Exists.intro b
                (And.intro
                  (holdsAllO_append_some b c DB hb.left
                    (dstep_holds DB c hs b hb.left))
                  hb.right)))
          hcomp)
      (fun hrest => Or.inr hrest)
      (ih a hF)

theorem dbFull_delete (F : List Constraint) (P : List Nat) (excls : List Excl)
    (negObj : List Term) (konst : Int) (bound : Option Int)
    (DB : List (Option Constraint)) (i : Nat)
    (ih : DbFull F P excls negObj konst bound DB) :
    DbFull F P excls negObj konst bound (setNone i DB) :=
  fun a hF =>
    @Or.rec (Companion P DB a)
      (Or (Excluded a excls) (BoundHolds negObj konst bound a))
      (fun _ =>
        Or (Companion P (setNone i DB) a)
           (Or (Excluded a excls) (BoundHolds negObj konst bound a)))
      (fun hcomp =>
        @Exists.rec (Nat -> Bool)
          (fun b : Nat -> Bool => And (HoldsAllO b DB) (AgreesOn b a P))
          (fun _ =>
            Or (Companion P (setNone i DB) a)
               (Or (Excluded a excls) (BoundHolds negObj konst bound a)))
          (fun b hb =>
            Or.inl
              (Exists.intro b
                (And.intro (holdsAllO_setNone b DB i hb.left) hb.right)))
          hcomp)
      (fun hrest => Or.inr hrest)
      (ih a hF)

theorem dbFull_red (F : List Constraint) (P : List Nat) (excls : List Excl)
    (negObj : List Term) (konst : Int) (bound : Option Int)
    (DB : List (Option Constraint)) (c : Constraint) (w : Wit)
    (hfix : WitFixes w P)
    (hgoal : forall b : Nat -> Bool,
      HoldsAllO b DB -> (Holds b c -> False) ->
      And (HoldsAllO b (substDB w DB)) (Holds b (substC w c)))
    (ih : DbFull F P excls negObj konst bound DB) :
    DbFull F P excls negObj konst bound (List.append DB [some c]) :=
  fun a hF =>
    @Or.rec (Companion P DB a)
      (Or (Excluded a excls) (BoundHolds negObj konst bound a))
      (fun _ =>
        Or (Companion P (List.append DB [some c]) a)
           (Or (Excluded a excls) (BoundHolds negObj konst bound a)))
      (fun hcomp =>
        @Exists.rec (Nat -> Bool)
          (fun b : Nat -> Bool => And (HoldsAllO b DB) (AgreesOn b a P))
          (fun _ =>
            Or (Companion P (List.append DB [some c]) a)
               (Or (Excluded a excls) (BoundHolds negObj konst bound a)))
          (fun b hb =>
            holds_cases b c
              (Or (Companion P (List.append DB [some c]) a)
                  (Or (Excluded a excls) (BoundHolds negObj konst bound a)))
              (fun hc =>
                Or.inl
                  (Exists.intro b
                    (And.intro
                      (holdsAllO_append_some b c DB hb.left hc)
                      hb.right)))
              (fun hnc =>
                Or.inl
                  (Exists.intro (applyA w b)
                    (And.intro
                      (holdsAllO_append_some (applyA w b) c DB
                        (holdsAllO_applyA_of_substDB w b DB
                          (hgoal b hb.left hnc).left)
                        (holds_substC w b c (hgoal b hb.left hnc).right))
                      (agreesOn_trans (applyA w b) b a P
                        (agrees_applyA_of_fixes w b P hfix)
                        hb.right)))))
          hcomp)
      (fun hrest => Or.inr hrest)
      (ih a hF)

theorem dbFull_exclude (F : List Constraint) (P : List Nat) (excls : List Excl)
    (negObj : List Term) (konst : Int) (bound : Option Int)
    (DB : List (Option Constraint)) (sigma : Nat -> Bool) (vars : List Nat)
    (hsub : SubsetN vars P)
    (ih : DbFull F P excls negObj konst bound DB) :
    DbFull F P ({ sol := sigma, vars := vars } :: excls) negObj konst bound
      (List.append DB [some (blockC sigma vars)]) :=
  fun a hF =>
    @Or.rec (Companion P DB a)
      (Or (Excluded a excls) (BoundHolds negObj konst bound a))
      (fun _ =>
        Or (Companion P (List.append DB [some (blockC sigma vars)]) a)
           (Or (Excluded a ({ sol := sigma, vars := vars } :: excls))
               (BoundHolds negObj konst bound a)))
      (fun hcomp =>
        @Exists.rec (Nat -> Bool)
          (fun b : Nat -> Bool => And (HoldsAllO b DB) (AgreesOn b a P))
          (fun _ =>
            Or (Companion P (List.append DB [some (blockC sigma vars)]) a)
               (Or (Excluded a ({ sol := sigma, vars := vars } :: excls))
                   (BoundHolds negObj konst bound a)))
          (fun b hb =>
            holds_cases b (blockC sigma vars)
              (Or (Companion P (List.append DB [some (blockC sigma vars)]) a)
                  (Or (Excluded a ({ sol := sigma, vars := vars } :: excls))
                      (BoundHolds negObj konst bound a)))
              (fun hbl =>
                Or.inl
                  (Exists.intro b
                    (And.intro
                      (holdsAllO_append_some b (blockC sigma vars) DB hb.left hbl)
                      hb.right)))

              (fun hnbl =>
                Or.inr
                  (Or.inl
                    (Or.inl

                      (agreesOn_trans a b sigma vars
                        (agreesOn_symm b a vars
                          (agreesOn_of_subset b a vars P hsub hb.right))
                        (agrees_of_not_holds_blockC sigma b vars hnbl))))))
          hcomp)
      (fun hrest =>
        @Or.rec (Excluded a excls) (BoundHolds negObj konst bound a)
          (fun _ =>
            Or (Companion P (List.append DB [some (blockC sigma vars)]) a)
               (Or (Excluded a ({ sol := sigma, vars := vars } :: excls))
                   (BoundHolds negObj konst bound a)))
          (fun he => Or.inr (Or.inl (Or.inr he)))
          (fun hbd => Or.inr (Or.inr hbd))
          hrest)
      (ih a hF)

theorem dbFull_improve (F : List Constraint) (P : List Nat) (excls : List Excl)
    (refObj : List Term) (refKonst : Int) (bound : Option Int) (v : Int)
    (DB : List (Option Constraint)) (curObj : List Term) (curKonst : Int)
    (hle : BoundLe v bound) (hsub : SubsetN (termVars refObj) P)
    (hagree : forall b : Nat -> Bool,
      HoldsAllO b DB ->
      Eq (objValNeg curObj curKonst b) (objValNeg refObj refKonst b))
    (ih : DbFull F P excls refObj refKonst bound DB) :
    DbFull F P excls refObj refKonst (some v)
      (List.append DB [some (improveC curObj curKonst v)]) :=
  fun a hF =>
    @Or.rec (Companion P DB a)
      (Or (Excluded a excls) (BoundHolds refObj refKonst bound a))
      (fun _ =>
        Or (Companion P (List.append DB [some (improveC curObj curKonst v)]) a)
           (Or (Excluded a excls) (BoundHolds refObj refKonst (some v) a)))
      (fun hcomp =>
        @Exists.rec (Nat -> Bool)
          (fun b : Nat -> Bool => And (HoldsAllO b DB) (AgreesOn b a P))
          (fun _ =>
            Or (Companion P (List.append DB [some (improveC curObj curKonst v)]) a)
               (Or (Excluded a excls) (BoundHolds refObj refKonst (some v) a)))
          (fun b hb =>
            holds_cases b (improveC curObj curKonst v)
              (Or (Companion P (List.append DB [some (improveC curObj curKonst v)]) a)
                  (Or (Excluded a excls) (BoundHolds refObj refKonst (some v) a)))
              (fun hh =>
                Or.inl
                  (Exists.intro b
                    (And.intro
                      (holdsAllO_append_some b (improveC curObj curKonst v) DB
                        hb.left hh)
                      hb.right)))

              (fun hnh =>
                Or.inr
                  (Or.inr
                    (@Eq.subst Int
                      (fun z : Int => Int.le v (refKonst - z))
                      (evalTerms b refObj) (evalTerms a refObj)
                      (Eq.symm
                        (evalTerms_congr_agrees a b refObj
                          (agreesOn_of_subset a b (termVars refObj) P hsub
                            (agreesOn_symm b a P hb.right))))
                      (@Eq.subst Int
                        (fun z : Int => Int.le v z)
                        (objValNeg curObj curKonst b)
                        (objValNeg refObj refKonst b)
                        (hagree b hb.left)
                        (bound_of_not_holds_improveC curObj curKonst v b hnh))))))
          hcomp)
      (fun hrest =>
        @Or.rec (Excluded a excls) (BoundHolds refObj refKonst bound a)
          (fun _ =>
            Or (Companion P (List.append DB [some (improveC curObj curKonst v)]) a)
               (Or (Excluded a excls) (BoundHolds refObj refKonst (some v) a)))
          (fun he => Or.inr (Or.inl he))
          (fun hbd =>
            Or.inr (Or.inr (boundHolds_of_le refObj refKonst v bound a hle hbd)))
          hrest)
      (ih a hF)

theorem dom_companion (P : List Nat) (DB : List (Option Constraint)) (c : Constraint)
    (w : Wit) (mu : (Nat -> Bool) -> Nat) (a : Nat -> Bool)
    (hfix : WitFixes w P)
    (hgoal : forall b : Nat -> Bool,
      HoldsAllO b DB -> (Holds b c -> False) ->
      And (HoldsAllO b (substDB w DB)) (Nat.lt (mu (applyA w b)) (mu b)))
    (n : Nat) :
    forall b : Nat -> Bool,
      Nat.le (mu b) n -> HoldsAllO b DB -> AgreesOn b a P ->
      Companion P (List.append DB [some c]) a :=
  @Nat.rec
    (fun n =>
      forall b : Nat -> Bool,
        Nat.le (mu b) n -> HoldsAllO b DB -> AgreesOn b a P ->
        Companion P (List.append DB [some c]) a)

    (fun b hle hDB hag =>
      holds_cases b c (Companion P (List.append DB [some c]) a)
        (fun hc =>
          Exists.intro b
            (And.intro (holdsAllO_append_some b c DB hDB hc) hag))
        (fun hnc =>
          False.elim
            (Nat.noConfusion
              (nat_eq_zero_of_le_zero (Nat.succ (mu (applyA w b)))
                (@Eq.subst Nat (fun z : Nat => Nat.le (Nat.succ (mu (applyA w b))) z)
                  (mu b) Nat.zero
                  (nat_eq_zero_of_le_zero (mu b) hle)
                  (hgoal b hDB hnc).right)))))
    (fun n ih b hle hDB hag =>
      holds_cases b c (Companion P (List.append DB [some c]) a)
        (fun hc =>
          Exists.intro b
            (And.intro (holdsAllO_append_some b c DB hDB hc) hag))

        (fun hnc =>
          ih (applyA w b)
            (Nat.le_of_succ_le_succ (mu (applyA w b)) n
              (Nat.le_trans (Nat.succ (mu (applyA w b))) (mu b) (Nat.succ n)
                (hgoal b hDB hnc).right hle))
            (holdsAllO_applyA_of_substDB w b DB (hgoal b hDB hnc).left)
            (agreesOn_trans (applyA w b) b a P
              (agrees_applyA_of_fixes w b P hfix) hag)))
    n

theorem dbFull_dom (F : List Constraint) (P : List Nat) (excls : List Excl)
    (negObj : List Term) (konst : Int) (bound : Option Int)
    (DB : List (Option Constraint)) (c : Constraint) (w : Wit)
    (mu : (Nat -> Bool) -> Nat)
    (hfix : WitFixes w P)
    (hgoal : forall b : Nat -> Bool,
      HoldsAllO b DB -> (Holds b c -> False) ->
      And (HoldsAllO b (substDB w DB)) (Nat.lt (mu (applyA w b)) (mu b)))
    (ih : DbFull F P excls negObj konst bound DB) :
    DbFull F P excls negObj konst bound (List.append DB [some c]) :=
  fun a hF =>
    @Or.rec (Companion P DB a)
      (Or (Excluded a excls) (BoundHolds negObj konst bound a))
      (fun _ =>
        Or (Companion P (List.append DB [some c]) a)
           (Or (Excluded a excls) (BoundHolds negObj konst bound a)))
      (fun hcomp =>
        @Exists.rec (Nat -> Bool)
          (fun b : Nat -> Bool => And (HoldsAllO b DB) (AgreesOn b a P))
          (fun _ =>
            Or (Companion P (List.append DB [some c]) a)
               (Or (Excluded a excls) (BoundHolds negObj konst bound a)))
          (fun b hb =>
            Or.inl
              (dom_companion P DB c w mu a hfix hgoal (mu b) b
                (Nat.le_refl (mu b)) hb.left hb.right))
          hcomp)
      (fun hrest => Or.inr hrest)
      (ih a hF)

inductive DbOkF (F : List Constraint) (P : List Nat) (negObj : List Term)
    (konst : Int) : List Excl -> Option Int -> List (Option Constraint) -> Prop where
  | init : DbOkF F P negObj konst [] none (liftDB F)
  | derive : forall (excls : List Excl) (bound : Option Int)
      (DB : List (Option Constraint)) (c : Constraint),
      DbOkF F P negObj konst excls bound DB -> DStep DB c ->
      DbOkF F P negObj konst excls bound (List.append DB [some c])
  | delete : forall (excls : List Excl) (bound : Option Int)
      (DB : List (Option Constraint)) (i : Nat),
      DbOkF F P negObj konst excls bound DB ->
      DbOkF F P negObj konst excls bound (setNone i DB)
  | red : forall (excls : List Excl) (bound : Option Int)
      (DB : List (Option Constraint)) (c : Constraint) (w : Wit),
      DbOkF F P negObj konst excls bound DB ->
      WitFixes w P ->
      (forall b : Nat -> Bool,
        HoldsAllO b DB -> (Holds b c -> False) ->
        And (HoldsAllO b (substDB w DB)) (Holds b (substC w c))) ->
      DbOkF F P negObj konst excls bound (List.append DB [some c])
  | exclude : forall (excls : List Excl) (bound : Option Int)
      (DB : List (Option Constraint)) (sigma : Nat -> Bool) (vars : List Nat),
      DbOkF F P negObj konst excls bound DB -> SubsetN vars P ->
      DbOkF F P negObj konst ({ sol := sigma, vars := vars } :: excls) bound
        (List.append DB [some (blockC sigma vars)])
  | dom : forall (excls : List Excl) (bound : Option Int)
      (DB : List (Option Constraint)) (c : Constraint) (w : Wit)
      (mu : (Nat -> Bool) -> Nat),
      DbOkF F P negObj konst excls bound DB ->
      WitFixes w P ->
      (forall b : Nat -> Bool,
        HoldsAllO b DB -> (Holds b c -> False) ->
        And (HoldsAllO b (substDB w DB)) (Nat.lt (mu (applyA w b)) (mu b))) ->
      DbOkF F P negObj konst excls bound (List.append DB [some c])
  | improve : forall (excls : List Excl) (bound : Option Int) (v : Int)
      (DB : List (Option Constraint)) (curObj : List Term) (curKonst : Int),
      DbOkF F P negObj konst excls bound DB ->
      BoundLe v bound -> SubsetN (termVars negObj) P ->
      (forall b : Nat -> Bool,
        HoldsAllO b DB ->
        Eq (objValNeg curObj curKonst b) (objValNeg negObj konst b)) ->
      DbOkF F P negObj konst excls (some v)
        (List.append DB [some (improveC curObj curKonst v)])

theorem dbOkF_full (F : List Constraint) (P : List Nat) (negObj : List Term)
    (konst : Int) (excls : List Excl) (bound : Option Int)
    (DB : List (Option Constraint)) (hok : DbOkF F P negObj konst excls bound DB) :
    DbFull F P excls negObj konst bound DB :=
  @DbOkF.rec F P negObj konst
    (fun excls bound DB _ => DbFull F P excls negObj konst bound DB)
    (dbFull_init F P negObj konst)
    (fun excls bound DB c _ hs ih =>
      dbFull_derive F P excls negObj konst bound DB c ih hs)
    (fun excls bound DB i _ ih =>
      dbFull_delete F P excls negObj konst bound DB i ih)
    (fun excls bound DB c w _ hfix hgoal ih =>
      dbFull_red F P excls negObj konst bound DB c w hfix hgoal ih)
    (fun excls bound DB sigma vars _ hsub ih =>
      dbFull_exclude F P excls negObj konst bound DB sigma vars hsub ih)
    (fun excls bound DB c w mu _ hfix hgoal ih =>
      dbFull_dom F P excls negObj konst bound DB c w mu hfix hgoal ih)
    (fun excls bound v DB curObj curKonst _ hle hsub hagree ih =>
      dbFull_improve F P excls negObj konst bound v DB curObj curKonst
        hle hsub hagree ih)
    excls bound DB hok

theorem full_complete (F : List Constraint) (P : List Nat) (negObj : List Term)
    (konst : Int) (excls : List Excl) (bound : Option Int)
    (DB : List (Option Constraint)) (i : Nat) (cc : Constraint)
    (hok : DbOkF F P negObj konst excls bound DB) (hg : getO DB i = some cc)
    (hn : AllNonneg cc.terms) (hgt : Int.lt (coeffSum cc.terms) cc.degree)
    (a : Nat -> Bool) (hF : HoldsAll a F) :
    Or (Excluded a excls) (BoundHolds negObj konst bound a) :=
  @Or.rec (Companion P DB a)
    (Or (Excluded a excls) (BoundHolds negObj konst bound a))
    (fun _ => Or (Excluded a excls) (BoundHolds negObj konst bound a))
    (fun hcomp =>
      @Exists.rec (Nat -> Bool)
        (fun b : Nat -> Bool => And (HoldsAllO b DB) (AgreesOn b a P))
        (fun _ => Or (Excluded a excls) (BoundHolds negObj konst bound a))
        (fun b hb =>
          False.elim
            (not_holds_of_degree_gt_coeffSum b cc hn hgt
              (holdsAllO_get b DB i cc hb.left hg)))
        hcomp)
    (fun hrest => hrest)
    (dbOkF_full F P negObj konst excls bound DB hok a hF)

theorem full_unsat (F : List Constraint) (P : List Nat) (negObj : List Term)
    (konst : Int) (DB : List (Option Constraint)) (i : Nat) (cc : Constraint)
    (hok : DbOkF F P negObj konst [] none DB) (hg : getO DB i = some cc)
    (hn : AllNonneg cc.terms) (hgt : Int.lt (coeffSum cc.terms) cc.degree) :
    Unsat F :=
  fun a hF =>
    @Or.rec (Excluded a []) (BoundHolds negObj konst none a) (fun _ => False)
      (fun he => he)
      (fun hb => hb)
      (full_complete F P negObj konst [] none DB i cc hok hg hn hgt a hF)

def countLt (p : Nat -> Bool) (n : Nat) : Nat :=
  match n with
  | Nat.zero   => Nat.zero
  | Nat.succ m =>
    match p m with
    | true  => Nat.succ (countLt p m)
    | false => countLt p m

theorem nat_lt_succ_of_lt (j m : Nat) (h : Nat.lt j m) : Nat.lt j (Nat.succ m) :=
  Nat.le.step h

theorem countLt_mono (p q : Nat -> Bool) (n : Nat) :
    (forall j : Nat, Nat.lt j n -> Eq (p j) true -> Eq (q j) true) ->
    Nat.le (countLt p n) (countLt q n) :=
  @Nat.rec
    (fun n =>
      (forall j : Nat, Nat.lt j n -> Eq (p j) true -> Eq (q j) true) ->
      Nat.le (countLt p n) (countLt q n))
    (fun _ => Nat.le_refl Nat.zero)
    (fun m ih h =>
      @Bool.rec
        (fun pm =>
          Eq (p m) pm ->
          Nat.le (match pm with
                  | true  => Nat.succ (countLt p m)
                  | false => countLt p m)
                 (countLt q (Nat.succ m)))
        (fun _ =>
          Nat.le_trans (countLt p m) (countLt q m) (countLt q (Nat.succ m))
            (ih (fun j hj => h j (nat_lt_succ_of_lt j m hj)))
            (@Bool.rec
              (fun qm =>
                Nat.le (countLt q m)
                  (match qm with
                   | true  => Nat.succ (countLt q m)
                   | false => countLt q m))
              (Nat.le_refl (countLt q m))
              (Nat.le.step (Nat.le_refl (countLt q m)))
              (q m)))
        (fun hpm =>

          @Eq.subst Bool
            (fun qm : Bool =>
              Nat.le (Nat.succ (countLt p m))
                (match qm with
                 | true  => Nat.succ (countLt q m)
                 | false => countLt q m))
            true (q m)
            (Eq.symm (h m (Nat.le_refl (Nat.succ m)) hpm))
            (Nat.succ_le_succ (countLt p m) (countLt q m)
              (ih (fun j hj => h j (nat_lt_succ_of_lt j m hj)))))
        (p m)
        rfl)
    n

theorem countLt_lt (p q : Nat -> Bool) (j : Nat)
    (hpj : Eq (p j) false) (hqj : Eq (q j) true) (n : Nat) :
    (forall i : Nat, Nat.lt i n -> Eq (p i) true -> Eq (q i) true) ->
    Nat.lt j n ->
    Nat.lt (countLt p n) (countLt q n) :=
  @Nat.rec
    (fun n =>
      (forall i : Nat, Nat.lt i n -> Eq (p i) true -> Eq (q i) true) ->
      Nat.lt j n ->
      Nat.lt (countLt p n) (countLt q n))
    (fun _ hj => False.elim (Nat.noConfusion (nat_eq_zero_of_le_zero (Nat.succ j) hj)))
    (fun m ih h hj =>
      @Or.rec (Nat.lt j m) (Eq j m)
        (fun _ => Nat.lt (countLt p (Nat.succ m)) (countLt q (Nat.succ m)))

        (fun hlt =>
          @Bool.rec
            (fun pm =>
              Eq (p m) pm ->
              Nat.lt (match pm with
                      | true  => Nat.succ (countLt p m)
                      | false => countLt p m)
                     (countLt q (Nat.succ m)))
            (fun _ =>
              Nat.le_trans
                (Nat.succ (countLt p m)) (countLt q m) (countLt q (Nat.succ m))
                (ih (fun i hi => h i (nat_lt_succ_of_lt i m hi)) hlt)
                (@Bool.rec
                  (fun qm =>
                    Nat.le (countLt q m)
                      (match qm with
                       | true  => Nat.succ (countLt q m)
                       | false => countLt q m))
                  (Nat.le_refl (countLt q m))
                  (Nat.le.step (Nat.le_refl (countLt q m)))
                  (q m)))
            (fun hpm =>
              @Eq.subst Bool
                (fun qm : Bool =>
                  Nat.lt (Nat.succ (countLt p m))
                    (match qm with
                     | true  => Nat.succ (countLt q m)
                     | false => countLt q m))
                true (q m)
                (Eq.symm (h m (Nat.le_refl (Nat.succ m)) hpm))
                (Nat.succ_le_succ (Nat.succ (countLt p m)) (countLt q m)
                  (ih (fun i hi => h i (nat_lt_succ_of_lt i m hi)) hlt)))
            (p m)
            rfl)

        (fun heq =>
          @Eq.subst Nat
            (fun z : Nat =>
              Nat.lt (match p z with
                      | true  => Nat.succ (countLt p m)
                      | false => countLt p m)
                     (match q z with
                      | true  => Nat.succ (countLt q m)
                      | false => countLt q m))
            j m heq
            (@Eq.subst Bool
              (fun pj : Bool =>
                Nat.lt (match pj with
                        | true  => Nat.succ (countLt p m)
                        | false => countLt p m)
                       (match q j with
                        | true  => Nat.succ (countLt q m)
                        | false => countLt q m))
              false (p j) (Eq.symm hpj)
              (@Eq.subst Bool
                (fun qj : Bool =>
                  Nat.lt (countLt p m)
                    (match qj with
                     | true  => Nat.succ (countLt q m)
                     | false => countLt q m))
                true (q j) (Eq.symm hqj)
                (Nat.succ_le_succ (countLt p m) (countLt q m)
                  (countLt_mono p q m
                    (fun i hi => h i (nat_lt_succ_of_lt i m hi)))))))
        (Nat.lt_or_eq_of_le j m (Nat.le_of_succ_le_succ j m hj)))
    n

def rankOf (R : Nat -> Nat -> Bool) (N x : Nat) : Nat :=
  countLt (fun y => R y x) N

theorem rank_lt_of_rel (R : Nat -> Nat -> Bool) (N x y : Nat)
    (htrans : forall i j k : Nat,
      Eq (R i j) true -> Eq (R j k) true -> Eq (R i k) true)
    (hirr : forall i : Nat, Eq (R i i) false)
    (hyN : Nat.lt y N) (hxy : Eq (R y x) true) :
    Nat.lt (rankOf R N y) (rankOf R N x) :=
  countLt_lt (fun i => R i y) (fun i => R i x) y (hirr y) hxy N
    (fun i _ hiy => htrans i y x hiy hxy)
    hyN

theorem dbOkF_dom_from_order (F : List Constraint) (P : List Nat)
    (negObj : List Term) (konst : Int) (excls : List Excl) (bound : Option Int)
    (DB : List (Option Constraint)) (c : Constraint) (w : Wit)
    (R : Nat -> Nat -> Bool) (N : Nat) (idx : (Nat -> Bool) -> Nat)
    (hok : DbOkF F P negObj konst excls bound DB)
    (hfix : WitFixes w P)
    (htrans : forall i j k : Nat,
      Eq (R i j) true -> Eq (R j k) true -> Eq (R i k) true)
    (hirr : forall i : Nat, Eq (R i i) false)
    (hidx : forall b : Nat -> Bool, Nat.lt (idx b) N)
    (hgoal : forall b : Nat -> Bool,
      HoldsAllO b DB -> (Holds b c -> False) ->
      And (HoldsAllO b (substDB w DB))
          (Eq (R (idx (applyA w b)) (idx b)) true)) :
    DbOkF F P negObj konst excls bound (List.append DB [some c]) :=
  @DbOkF.dom F P negObj konst excls bound DB c w
    (fun b => rankOf R N (idx b))
    hok hfix
    (fun b hDB hnc =>
      And.intro
        (hgoal b hDB hnc).left
        (rank_lt_of_rel R N (idx b) (idx (applyA w b)) htrans hirr
          (hidx (applyA w b)) (hgoal b hDB hnc).right))

theorem and_true_left (a b : Bool) (h : Eq (Bool.and a b) true) : Eq a true :=
  @Bool.rec (fun x => Eq (Bool.and x b) true -> Eq x true)
    (fun hf => Bool.noConfusion hf)
    (fun _ => rfl)
    a h

theorem and_true_right (a b : Bool) (h : Eq (Bool.and a b) true) : Eq b true :=
  @Bool.rec (fun x => Eq (Bool.and x b) true -> Eq b true)
    (fun hf => Bool.noConfusion hf)
    (fun ht => ht)
    a h

theorem eq_false_of_not_true (b : Bool) (h : Eq (Bool.not b) true) : Eq b false :=
  @Bool.rec (fun x => Eq (Bool.not x) true -> Eq x false)
    (fun _ => rfl)
    (fun hf => Bool.noConfusion hf)
    b h

def strictOf (le : Nat -> Nat -> Bool) (x y : Nat) : Bool :=
  Bool.and (le x y) (Bool.not (le y x))

theorem strictOf_irrefl (le : Nat -> Nat -> Bool) (i : Nat) :
    Eq (strictOf le i i) false :=
  @Bool.rec
    (fun b => Eq (Bool.and b (Bool.not b)) false)
    rfl rfl
    (le i i)

theorem strictOf_trans (le : Nat -> Nat -> Bool)
    (htrans : forall i j k : Nat,
      Eq (le i j) true -> Eq (le j k) true -> Eq (le i k) true)
    (i j k : Nat)
    (hij : Eq (strictOf le i j) true) (hjk : Eq (strictOf le j k) true) :
    Eq (strictOf le i k) true :=
  @Eq.subst Bool (fun b : Bool => Eq (Bool.and b (Bool.not (le k i))) true)
    true (le i k)
    (Eq.symm
      (htrans i j k (and_true_left (le i j) (Bool.not (le j i)) hij)
        (and_true_left (le j k) (Bool.not (le k j)) hjk)))
    (@Eq.subst Bool (fun b : Bool => Eq (Bool.and true (Bool.not b)) true)
      false (le k i)
      (Eq.symm
        (@Bool.rec (fun b => Eq (le k i) b -> Eq (le k i) false)
          (fun hf => hf)
          (fun ht =>
            False.elim
              (Bool.noConfusion
                (Eq.trans
                  (Eq.symm
                    (htrans k i j ht (and_true_left (le i j) (Bool.not (le j i)) hij)))
                  (eq_false_of_not_true (le k j)
                    (and_true_right (le j k) (Bool.not (le k j)) hjk)))))
          (le k i)
          rfl))
      rfl)

theorem rank_lt_of_strict (le : Nat -> Nat -> Bool) (N x y : Nat)
    (htrans : forall i j k : Nat,
      Eq (le i j) true -> Eq (le j k) true -> Eq (le i k) true)
    (hyN : Nat.lt y N) (hxy : Eq (strictOf le y x) true) :
    Nat.lt (rankOf (strictOf le) N y) (rankOf (strictOf le) N x) :=
  rank_lt_of_rel (strictOf le) N x y
    (strictOf_trans le htrans) (strictOf_irrefl le) hyN hxy

theorem dbOkF_dom_from_preorder (F : List Constraint) (P : List Nat)
    (negObj : List Term) (konst : Int) (excls : List Excl) (bound : Option Int)
    (DB : List (Option Constraint)) (c : Constraint) (w : Wit)
    (le : Nat -> Nat -> Bool) (N : Nat) (idx : (Nat -> Bool) -> Nat)
    (hok : DbOkF F P negObj konst excls bound DB)
    (hfix : WitFixes w P)
    (htrans : forall i j k : Nat,
      Eq (le i j) true -> Eq (le j k) true -> Eq (le i k) true)
    (hidx : forall b : Nat -> Bool, Nat.lt (idx b) N)
    (hgoal : forall b : Nat -> Bool,
      HoldsAllO b DB -> (Holds b c -> False) ->
      And (HoldsAllO b (substDB w DB))
          (Eq (strictOf le (idx (applyA w b)) (idx b)) true)) :
    DbOkF F P negObj konst excls bound (List.append DB [some c]) :=
  dbOkF_dom_from_order F P negObj konst excls bound DB c w
    (strictOf le) N idx hok hfix
    (strictOf_trans le htrans) (strictOf_irrefl le) hidx hgoal

def DbBack (F : List Constraint) (CO : List (Option Constraint)) : Prop :=
  forall b : Nat -> Bool, HoldsAllO b CO -> HoldsAll b F

theorem holdsAllO_restore (b : Nat -> Bool) (DB : List (Option Constraint)) :
    forall (i : Nat) (c : Constraint),
      HoldsAllO b (setNone i DB) -> getO DB i = some c -> Holds b c ->
      HoldsAllO b DB :=
  @List.rec (Option Constraint)
    (fun DB => forall (i : Nat) (c : Constraint),
      HoldsAllO b (setNone i DB) -> getO DB i = some c -> Holds b c ->
      HoldsAllO b DB)
    (fun _ c _ hg _ => False.elim (none_ne_someC c hg))
    (fun o rest ih =>
      @Option.rec Constraint
        (fun o => forall (i : Nat) (c : Constraint),
          HoldsAllO b (setNone i (o :: rest)) -> getO (o :: rest) i = some c ->
          Holds b c -> HoldsAllO b (o :: rest))
        (fun i =>
          @Nat.rec
            (fun i => forall (c : Constraint),
              HoldsAllO b (setNone i (none :: rest)) ->
              getO (none :: rest) i = some c -> Holds b c ->
              HoldsAllO b (none :: rest))
            (fun c _ hg _ => False.elim (none_ne_someC c hg))
            (fun j _ c hall hg hc => ih j c hall hg hc)
            i)
        (fun c' i =>
          @Nat.rec
            (fun i => forall (c : Constraint),
              HoldsAllO b (setNone i (some c' :: rest)) ->
              getO (some c' :: rest) i = some c -> Holds b c ->
              HoldsAllO b (some c' :: rest))
            (fun c hall hg hc =>
              And.intro
                (@Eq.subst Constraint (fun w : Constraint => Holds b w) c c'
                  (Eq.symm (someC_inj c' c hg)) hc)
                hall)
            (fun j _ c hall hg hc =>
              And.intro hall.left (ih j c hall.right hg hc))
            i)
        o)
    DB

theorem holdsAllO_of_append (b : Nat -> Bool) (o : Option Constraint)
    (DB : List (Option Constraint)) :
    HoldsAllO b (List.append DB [o]) -> HoldsAllO b DB :=
  @List.rec (Option Constraint)
    (fun DB => HoldsAllO b (List.append DB [o]) -> HoldsAllO b DB)
    (fun _ => True.intro)
    (fun o' rest ih =>
      @Option.rec Constraint
        (fun o' => HoldsAllO b (List.append (o' :: rest) [o]) ->
                   HoldsAllO b (o' :: rest))
        (fun hall => ih hall)
        (fun c' hall => And.intro hall.left (ih hall.right))
        o')
    DB

theorem holdsAllO_of_slots (b : Nat -> Bool) (CO : List (Option Constraint)) :
    (forall (i : Nat) (c : Constraint), getO CO i = some c -> Holds b c) ->
    HoldsAllO b CO :=
  @List.rec (Option Constraint)
    (fun CO => (forall (i : Nat) (c : Constraint), getO CO i = some c -> Holds b c) ->
      HoldsAllO b CO)
    (fun _ => True.intro)
    (fun o rest ih =>
      @Option.rec Constraint
        (fun o => (forall (i : Nat) (c : Constraint),
            getO (o :: rest) i = some c -> Holds b c) ->
          HoldsAllO b (o :: rest))
        (fun h => ih (fun i c hg => h (Nat.succ i) c hg))
        (fun c' h =>
          And.intro
            (h Nat.zero c' (Eq.refl (some c')))
            (ih (fun i c hg => h (Nat.succ i) c hg)))
        o)
    CO

theorem dbBack_init (F : List Constraint) : DbBack F (liftDB F) :=
  fun b =>
    @List.rec Constraint
      (fun F => HoldsAllO b (liftDB F) -> HoldsAll b F)
      (fun _ => True.intro)
      (fun c rest ih hall => And.intro hall.left (ih hall.right))
      F

theorem dbBack_append (F : List Constraint) (CO : List (Option Constraint))
    (o : Option Constraint) (hback : DbBack F CO) :
    DbBack F (List.append CO [o]) :=
  fun b hb => hback b (holdsAllO_of_append b o CO hb)

theorem dbBack_delete_checked (F : List Constraint)
    (CO : List (Option Constraint)) (i : Nat) (c : Constraint)
    (hback : DbBack F CO)
    (hg : getO CO i = some c)
    (hchk : forall b : Nat -> Bool, HoldsAllO b (setNone i CO) -> Holds b c) :
    DbBack F (setNone i CO) :=
  fun b hb => hback b (holdsAllO_restore b CO i c hb hg (hchk b hb))

theorem output_unsat_of_unsat (F O : List Constraint)
    (CO : List (Option Constraint)) (idx : Nat -> Nat)
    (hback : DbBack F CO)
    (hpair : forall (i : Nat) (c : Constraint),
      getO CO i = some c -> getC O (idx i) = some c)
    (hF : Unsat F) : Unsat O :=
  fun b hO =>
    hF b
      (hback b
        (holdsAllO_of_slots b CO
          (fun i c hg => holdsAll_get b O (idx i) c hO (hpair i c hg))))

theorem holdsAll_of_slots (b : Nat -> Bool) (O : List Constraint) :
    (forall (j : Nat) (c : Constraint), getC O j = some c -> Holds b c) ->
    HoldsAll b O :=
  @List.rec Constraint
    (fun O => (forall (j : Nat) (c : Constraint), getC O j = some c -> Holds b c) ->
      HoldsAll b O)
    (fun _ => True.intro)
    (fun c' rest ih h =>
      And.intro
        (h Nat.zero c' (Eq.refl (some c')))
        (ih (fun j c hg => h (Nat.succ j) c hg)))
    O

theorem holdsAll_output_of_db (b : Nat -> Bool) (O : List Constraint)
    (DB : List (Option Constraint)) (src : Nat -> Nat)
    (hsub : forall (j : Nat) (c : Constraint),
      getC O j = some c -> getO DB (src j) = some c)
    (hDB : HoldsAllO b DB) : HoldsAll b O :=
  holdsAll_of_slots b O
    (fun j c hg => holdsAllO_get b DB (src j) c hDB (hsub j c hg))

theorem output_unsat_forward (F O : List Constraint)
    (DB : List (Option Constraint)) (src : Nat -> Nat)
    (hsub : forall (j : Nat) (c : Constraint),
      getC O j = some c -> getO DB (src j) = some c)
    (hcomp : forall a : Nat -> Bool, HoldsAll a F ->
      Exists (fun b : Nat -> Bool => HoldsAllO b DB))
    (hO : Unsat O) : Unsat F :=
  fun a hF =>
    @Exists.rec (Nat -> Bool) (fun b : Nat -> Bool => HoldsAllO b DB)
      (fun _ => False)
      (fun b hb => hO b (holdsAll_output_of_db b O DB src hsub hb))
      (hcomp a hF)

theorem output_equisat (F O : List Constraint) (DB CO : List (Option Constraint))
    (idx src : Nat -> Nat)
    (hback : DbBack F CO)
    (hpair : forall (i : Nat) (c : Constraint),
      getO CO i = some c -> getC O (idx i) = some c)
    (hsub : forall (j : Nat) (c : Constraint),
      getC O j = some c -> getO DB (src j) = some c)
    (hcomp : forall a : Nat -> Bool, HoldsAll a F ->
      Exists (fun b : Nat -> Bool => HoldsAllO b DB)) :
    And (Unsat F -> Unsat O) (Unsat O -> Unsat F) :=
  And.intro
    (output_unsat_of_unsat F O CO idx hback hpair)
    (output_unsat_forward F O DB src hsub hcomp)

theorem ctrl_dbBack_init_F0 : DbBack F0 (liftDB F0) := dbBack_init F0

theorem ctrl_holdsAllO_after_unchecked_delete :
    HoldsAllO ctrlAllTrue (setNone 1 (liftDB F0)) :=
  And.intro (Int.le_refl 1) True.intro

theorem ctrl_dbBack_fails_on_unchecked_delete :
    DbBack F0 (setNone 1 (liftDB F0)) -> False :=
  fun h =>
    Int.lt_irrefl 1
      (Int.lt_of_le_of_lt 1 0 1
        (h ctrlAllTrue ctrl_holdsAllO_after_unchecked_delete).right.left
        int_lt_0_1)

theorem dbOkF_companion (F : List Constraint) (P : List Nat) (negObj : List Term)
    (konst : Int) (DB : List (Option Constraint))
    (hok : DbOkF F P negObj konst [] none DB)
    (a : Nat -> Bool) (hF : HoldsAll a F) : Companion P DB a :=
  @Or.rec (Companion P DB a)
    (Or (Excluded a []) (BoundHolds negObj konst none a))
    (fun _ => Companion P DB a)
    (fun h => h)
    (fun h =>
      @Or.rec (Excluded a []) (BoundHolds negObj konst none a)
        (fun _ => Companion P DB a)
        (fun he => False.elim he)
        (fun hb => False.elim hb)
        h)
    (dbOkF_full F P negObj konst [] none DB hok a hF)

theorem output_unsat_forward_of_dbOkF (F O : List Constraint) (P : List Nat)
    (negObj : List Term) (konst : Int) (DB : List (Option Constraint))
    (src : Nat -> Nat)
    (hok : DbOkF F P negObj konst [] none DB)
    (hsub : forall (j : Nat) (c : Constraint),
      getC O j = some c -> getO DB (src j) = some c)
    (hO : Unsat O) : Unsat F :=
  output_unsat_forward F O DB src hsub
    (fun a hF =>
      @Exists.rec (Nat -> Bool)
        (fun b : Nat -> Bool => And (HoldsAllO b DB) (AgreesOn b a P))
        (fun _ => Exists (fun b : Nat -> Bool => HoldsAllO b DB))
        (fun b hb =>
          Exists.intro b hb.left)
        (dbOkF_companion F P negObj konst DB hok a hF))
    hO

def DbBackSat (F : List Constraint) (CO : List (Option Constraint)) : Prop :=
  Unsat F -> forall b : Nat -> Bool, HoldsAllO b CO -> False

theorem dbBackSat_of_dbBack (F : List Constraint) (CO : List (Option Constraint))
    (h : DbBack F CO) : DbBackSat F CO :=
  fun hF b hb => hF b (h b hb)

theorem dbBackSat_init (F : List Constraint) : DbBackSat F (liftDB F) :=
  dbBackSat_of_dbBack F (liftDB F) (dbBack_init F)

theorem dbBackSat_append (F : List Constraint) (CO : List (Option Constraint))
    (o : Option Constraint) (hback : DbBackSat F CO) :
    DbBackSat F (List.append CO [o]) :=
  fun hF b hb => hback hF b (holdsAllO_of_append b o CO hb)

theorem dbBackSat_delete_checked (F : List Constraint)
    (CO : List (Option Constraint)) (i : Nat) (c : Constraint)
    (hback : DbBackSat F CO)
    (hg : getO CO i = some c)
    (hchk : forall b : Nat -> Bool, HoldsAllO b (setNone i CO) -> Holds b c) :
    DbBackSat F (setNone i CO) :=
  fun hF b hb =>
    hback hF b (holdsAllO_restore b CO i c hb hg (hchk b hb))

theorem dbBackSat_delete_red (F : List Constraint)
    (CO : List (Option Constraint)) (i : Nat) (c : Constraint) (w : Wit)
    (hback : DbBackSat F CO)
    (hg : getO CO i = some c)
    (hgoal : forall b : Nat -> Bool,
      HoldsAllO b (setNone i CO) -> (Holds b c -> False) ->
      And (HoldsAllO (applyA w b) (setNone i CO)) (Holds (applyA w b) c)) :
    DbBackSat F (setNone i CO) :=
  fun hF b hb =>
    holds_cases b c False
      (fun hc => hback hF b (holdsAllO_restore b CO i c hb hg hc))
      (fun hnc =>
        hback hF (applyA w b)
          (holdsAllO_restore (applyA w b) CO i c
            (hgoal b hb hnc).left hg (hgoal b hb hnc).right))

theorem output_unsat_of_unsat_sat (F O : List Constraint)
    (CO : List (Option Constraint)) (idx : Nat -> Nat)
    (hback : DbBackSat F CO)
    (hpair : forall (i : Nat) (c : Constraint),
      getO CO i = some c -> getC O (idx i) = some c)
    (hF : Unsat F) : Unsat O :=
  fun b hO =>
    hback hF b
      (holdsAllO_of_slots b CO
        (fun i c hg => holdsAll_get b O (idx i) c hO (hpair i c hg)))

end VeriPbCore

theorem capcoeff_le_self : forall (c : UInt64) (d : UInt64),
    Nat.le (UInt64.toNat (if c < d then c else d)) (UInt64.toNat c) :=
    fun c d => Decidable.casesOn
        (motive := fun (h : Decidable (LT.lt c d)) =>
            Nat.le (UInt64.toNat (Decidable.casesOn (motive := fun _ => UInt64)
                h (fun _ => d) (fun _ => c))) (UInt64.toNat c))
        (instDecidableUInt64Lt c d)
        (fun h => Iff.mp (Nat.not_lt (UInt64.toNat c) (UInt64.toNat d)) h)
        (fun h => Nat.le.refl (UInt64.toNat c))

theorem u64_le_refl : forall (x : UInt64), Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
    fun x => Nat.le.refl (UInt64.toNat x)

theorem capcoeff_le_other : forall (c : UInt64) (d : UInt64),
    Nat.le (UInt64.toNat (if c < d then c else d)) (UInt64.toNat d) :=
    fun c d => Decidable.casesOn
        (motive := fun (h : Decidable (LT.lt c d)) =>
            Nat.le (UInt64.toNat (Decidable.casesOn (motive := fun _ => UInt64)
                h (fun _ => d) (fun _ => c))) (UInt64.toNat d))
        (instDecidableUInt64Lt c d)
        (fun h => Nat.le.refl (UInt64.toNat d))
        (fun h => Nat.le_of_lt (UInt64.toNat c) (UInt64.toNat d) h)

theorem capcoeff_min_bounds : forall (c : UInt64) (d : UInt64),
    And (Nat.le (UInt64.toNat (if c < d then c else d)) (UInt64.toNat c))
        (Nat.le (UInt64.toNat (if c < d then c else d)) (UInt64.toNat d)) :=
    fun c d => And.intro (capcoeff_le_self c d) (capcoeff_le_other c d)

theorem decide_le_exact : forall (a : Nat) (b : Nat),
    And (Or (Not (Eq (Decidable.decide (Nat.le a b) (Nat.decLe a b)) Bool.true)) (Nat.le a b))
        (Or (Eq (Decidable.decide (Nat.le a b) (Nat.decLe a b)) Bool.true) (Nat.lt b a)) :=
    fun a b => Decidable.casesOn
        (motive := fun (h : Decidable (Nat.le a b)) =>
            And (Or (Not (Eq (Decidable.decide (Nat.le a b) h) Bool.true)) (Nat.le a b))
                (Or (Eq (Decidable.decide (Nat.le a b) h) Bool.true) (Nat.lt b a)))
        (Nat.decLe a b)
        (fun hn => And.intro
            (@Or.inl (Not (Eq Bool.false Bool.true)) (Nat.le a b)
                     (fun he => Bool.noConfusion he))
            (@Or.inr (Eq Bool.false Bool.true) (Nat.lt b a)
                     (Iff.mp (Nat.not_le a b) hn)))
        (fun hp => And.intro
            (@Or.inr (Not (Eq Bool.true Bool.true)) (Nat.le a b) hp)
            (@Or.inl (Eq Bool.true Bool.true) (Nat.lt b a) rfl))

theorem decide_and_le_exact : forall (a : Nat) (b : Nat) (c : Nat) (d : Nat),
    And (Or (Not (Eq (Bool.and (Decidable.decide (Nat.le a b) (Nat.decLe a b))
                               (Decidable.decide (Nat.le c d) (Nat.decLe c d)))
                     Bool.true))
            (And (Nat.le a b) (Nat.le c d)))
        (Or (Eq (Bool.and (Decidable.decide (Nat.le a b) (Nat.decLe a b))
                          (Decidable.decide (Nat.le c d) (Nat.decLe c d)))
                Bool.true)
            (Or (Nat.lt b a) (Nat.lt d c))) :=
    fun a b c d => Decidable.casesOn
        (motive := fun (h1 : Decidable (Nat.le a b)) =>
            And (Or (Not (Eq (Bool.and (Decidable.decide (Nat.le a b) h1)
                                       (Decidable.decide (Nat.le c d) (Nat.decLe c d)))
                             Bool.true))
                    (And (Nat.le a b) (Nat.le c d)))
                (Or (Eq (Bool.and (Decidable.decide (Nat.le a b) h1)
                                  (Decidable.decide (Nat.le c d) (Nat.decLe c d)))
                        Bool.true)
                    (Or (Nat.lt b a) (Nat.lt d c))))
        (Nat.decLe a b)
        (fun hn1 => And.intro
            (@Or.inl (Not (Eq (Bool.and Bool.false
                                        (Decidable.decide (Nat.le c d) (Nat.decLe c d)))
                              Bool.true))
                     (And (Nat.le a b) (Nat.le c d))
                     (fun he => Bool.noConfusion he))
            (@Or.inr (Eq (Bool.and Bool.false
                                   (Decidable.decide (Nat.le c d) (Nat.decLe c d)))
                         Bool.true)
                     (Or (Nat.lt b a) (Nat.lt d c))
                     (@Or.inl (Nat.lt b a) (Nat.lt d c)
                              (Iff.mp (Nat.not_le a b) hn1))))
        (fun hp1 => Decidable.casesOn
            (motive := fun (h2 : Decidable (Nat.le c d)) =>
                And (Or (Not (Eq (Bool.and Bool.true (Decidable.decide (Nat.le c d) h2))
                                 Bool.true))
                        (And (Nat.le a b) (Nat.le c d)))
                    (Or (Eq (Bool.and Bool.true (Decidable.decide (Nat.le c d) h2))
                            Bool.true)
                        (Or (Nat.lt b a) (Nat.lt d c))))
            (Nat.decLe c d)
            (fun hn2 => And.intro
                (@Or.inl (Not (Eq Bool.false Bool.true))
                         (And (Nat.le a b) (Nat.le c d))
                         (fun he => Bool.noConfusion he))
                (@Or.inr (Eq Bool.false Bool.true)
                         (Or (Nat.lt b a) (Nat.lt d c))
                         (@Or.inr (Nat.lt b a) (Nat.lt d c)
                                  (Iff.mp (Nat.not_le c d) hn2))))
            (fun hp2 => And.intro
                (@Or.inr (Not (Eq Bool.true Bool.true))
                         (And (Nat.le a b) (Nat.le c d))
                         (And.intro hp1 hp2))
                (@Or.inl (Eq Bool.true Bool.true)
                         (Or (Nat.lt b a) (Nat.lt d c))
                         rfl)))

def key64 (v : BitVec 64) : Nat :=
    Nat.xor (BitVec.toNat v) 9223372036854775808

theorem capcoeff_i64_le_coeff : forall (degree : BitVec 64) (coeff : BitVec 64),
    Nat.le (key64 (if Nat.le (key64 coeff) (key64 degree) then coeff else degree))
           (key64 coeff) :=
    fun degree coeff => Decidable.casesOn
        (motive := fun (h : Decidable (Nat.le (key64 coeff) (key64 degree))) =>
            Nat.le (key64 (Decidable.casesOn (motive := fun _ => BitVec 64)
                h (fun _ => degree) (fun _ => coeff))) (key64 coeff))
        (Nat.decLe (key64 coeff) (key64 degree))
        (fun h => Nat.le_of_lt (Iff.mp (Nat.not_le (key64 coeff) (key64 degree)) h))
        (fun h => Nat.le.refl (key64 coeff))

theorem capcoeff_i64_le_degree : forall (degree : BitVec 64) (coeff : BitVec 64),
    Nat.le (key64 (if Nat.le (key64 coeff) (key64 degree) then coeff else degree))
           (key64 degree) :=
    fun degree coeff => Decidable.casesOn
        (motive := fun (h : Decidable (Nat.le (key64 coeff) (key64 degree))) =>
            Nat.le (key64 (Decidable.casesOn (motive := fun _ => BitVec 64)
                h (fun _ => degree) (fun _ => coeff))) (key64 degree))
        (Nat.decLe (key64 coeff) (key64 degree))
        (fun h => Nat.le.refl (key64 degree))
        (fun h => h)

theorem satterm_coeff_le_degree :
    forall (degree : BitVec 64) (coeff : BitVec 64) (litvar : UInt32) (litneg : Bool),
    Nat.le (key64 (if Nat.le (key64 coeff) (key64 degree) then coeff else degree))
           (key64 degree) :=
    fun degree coeff litvar litneg => capcoeff_i64_le_degree degree coeff

theorem litctor_var_preserved : forall (v : UInt32), Eq v v :=
    fun v => Eq.refl v

theorem litnegate_var_preserved : forall (v : UInt32) (n : Bool), Eq v v :=
    fun v n => Eq.refl v

theorem capcoeff_i64_min_full : forall (degree : BitVec 64) (coeff : BitVec 64),
    And (And (Nat.le (key64 (if Nat.le (key64 coeff) (key64 degree) then coeff else degree))
                     (key64 coeff))
             (Nat.le (key64 (if Nat.le (key64 coeff) (key64 degree) then coeff else degree))
                     (key64 degree)))
        (Or (Nat.le (key64 degree)
                    (key64 (if Nat.le (key64 coeff) (key64 degree) then coeff else degree)))
            (Nat.le (key64 coeff)
                    (key64 (if Nat.le (key64 coeff) (key64 degree) then coeff else degree)))) :=
    fun degree coeff => Decidable.casesOn
        (motive := fun (h : Decidable (Nat.le (key64 coeff) (key64 degree))) =>
            And (And (Nat.le (key64 (Decidable.casesOn (motive := fun _ => BitVec 64)
                        h (fun _ => degree) (fun _ => coeff))) (key64 coeff))
                     (Nat.le (key64 (Decidable.casesOn (motive := fun _ => BitVec 64)
                        h (fun _ => degree) (fun _ => coeff))) (key64 degree)))
                (Or (Nat.le (key64 degree) (key64 (Decidable.casesOn (motive := fun _ => BitVec 64)
                        h (fun _ => degree) (fun _ => coeff))))
                    (Nat.le (key64 coeff) (key64 (Decidable.casesOn (motive := fun _ => BitVec 64)
                        h (fun _ => degree) (fun _ => coeff))))))
        (Nat.decLe (key64 coeff) (key64 degree))
        (fun h => And.intro
            (And.intro (Nat.le_of_lt (Iff.mp (Nat.not_le (key64 coeff) (key64 degree)) h))
                       (Nat.le.refl (key64 degree)))
            (@Or.inl (Nat.le (key64 degree) (key64 degree))
                     (Nat.le (key64 coeff) (key64 degree)) (Nat.le.refl (key64 degree))))
        (fun h => And.intro
            (And.intro (Nat.le.refl (key64 coeff)) h)
            (@Or.inr (Nat.le (key64 degree) (key64 coeff))
                     (Nat.le (key64 coeff) (key64 coeff)) (Nat.le.refl (key64 coeff))))

theorem capcoeff_i64_le_capcoeff : forall (degree : BitVec 64) (coeff : BitVec 64),
    Or (Not (Nat.le (key64 degree) (key64 coeff)))
       (Nat.le (key64 degree)
               (key64 (if Nat.le (key64 coeff) (key64 degree) then coeff else degree))) :=
    fun degree coeff => Decidable.casesOn
        (motive := fun (h : Decidable (Nat.le (key64 coeff) (key64 degree))) =>
            Or (Not (Nat.le (key64 degree) (key64 coeff)))
               (Nat.le (key64 degree) (key64 (Decidable.casesOn (motive := fun _ => BitVec 64)
                   h (fun _ => degree) (fun _ => coeff)))))
        (Nat.decLe (key64 coeff) (key64 degree))
        (fun h => @Or.inr (Not (Nat.le (key64 degree) (key64 coeff)))
                          (Nat.le (key64 degree) (key64 degree))
                          (Nat.le.refl (key64 degree)))
        (fun h => Decidable.casesOn
            (motive := fun (_ : Decidable (Nat.le (key64 degree) (key64 coeff))) =>
                Or (Not (Nat.le (key64 degree) (key64 coeff)))
                   (Nat.le (key64 degree) (key64 coeff)))
            (Nat.decLe (key64 degree) (key64 coeff))
            (fun h2 => @Or.inl (Not (Nat.le (key64 degree) (key64 coeff)))
                               (Nat.le (key64 degree) (key64 coeff)) h2)
            (fun h2 => @Or.inr (Not (Nat.le (key64 degree) (key64 coeff)))
                               (Nat.le (key64 degree) (key64 coeff)) h2))

def key128 (v : BitVec 128) : Nat :=
    Nat.xor (BitVec.toNat v) 170141183460469231731687303715884105728

theorem weaken_factor_sign_exact : forall (w : BitVec 64),
    And (Or (Not (Eq (Decidable.decide
                        (Nat.le (key64 (BitVec.ofNat 64 Nat.zero)) (key64 w))
                        (Nat.decLe (key64 (BitVec.ofNat 64 Nat.zero)) (key64 w)))
                     Bool.true))
            (Nat.le (key64 (BitVec.ofNat 64 Nat.zero)) (key64 w)))
        (Or (Eq (Decidable.decide
                    (Nat.le (key64 (BitVec.ofNat 64 Nat.zero)) (key64 w))
                    (Nat.decLe (key64 (BitVec.ofNat 64 Nat.zero)) (key64 w)))
                Bool.true)
            (Nat.lt (key64 w) (key64 (BitVec.ofNat 64 Nat.zero)))) :=
    fun w => decide_le_exact (key64 (BitVec.ofNat 64 Nat.zero)) (key64 w)

theorem wide_sign_exact : forall (x : BitVec 128),
    And (Or (Not (Eq (Decidable.decide
                        (Nat.le (key128 (BitVec.ofNat 128 Nat.zero)) (key128 x))
                        (Nat.decLe (key128 (BitVec.ofNat 128 Nat.zero)) (key128 x)))
                     Bool.true))
            (Nat.le (key128 (BitVec.ofNat 128 Nat.zero)) (key128 x)))
        (Or (Eq (Decidable.decide
                    (Nat.le (key128 (BitVec.ofNat 128 Nat.zero)) (key128 x))
                    (Nat.decLe (key128 (BitVec.ofNat 128 Nat.zero)) (key128 x)))
                Bool.true)
            (Nat.lt (key128 x) (key128 (BitVec.ofNat 128 Nat.zero)))) :=
    fun x => decide_le_exact (key128 (BitVec.ofNat 128 Nat.zero)) (key128 x)

theorem wide_le_exact : forall (a : BitVec 128) (b : BitVec 128),
    And (Or (Not (Eq (Decidable.decide (Nat.le (key128 b) (key128 a))
                        (Nat.decLe (key128 b) (key128 a))) Bool.true))
            (Nat.le (key128 b) (key128 a)))
        (Or (Eq (Decidable.decide (Nat.le (key128 b) (key128 a))
                    (Nat.decLe (key128 b) (key128 a))) Bool.true)
            (Nat.lt (key128 a) (key128 b))) :=
    fun a b => decide_le_exact (key128 b) (key128 a)

theorem guard_fits_lower_exact : forall (x : BitVec 128),
    And (Or (Not (Eq (Decidable.decide
                        (Nat.le (key128 (BitVec.ofNat 128 340282366920938463454151235394913435648)) (key128 x))
                        (Nat.decLe (key128 (BitVec.ofNat 128 340282366920938463454151235394913435648)) (key128 x)))
                     Bool.true))
            (Nat.le (key128 (BitVec.ofNat 128 340282366920938463454151235394913435648)) (key128 x)))
        (Or (Eq (Decidable.decide
                    (Nat.le (key128 (BitVec.ofNat 128 340282366920938463454151235394913435648)) (key128 x))
                    (Nat.decLe (key128 (BitVec.ofNat 128 340282366920938463454151235394913435648)) (key128 x)))
                Bool.true)
            (Nat.lt (key128 x) (key128 (BitVec.ofNat 128 340282366920938463454151235394913435648)))) :=
    fun x => decide_le_exact (key128 (BitVec.ofNat 128 340282366920938463454151235394913435648)) (key128 x)

theorem guard_fits_upper_exact : forall (x : BitVec 128),
    And (Or (Not (Eq (Decidable.decide
                        (Nat.le (key128 x) (key128 (BitVec.ofNat 128 9223372036854775807)))
                        (Nat.decLe (key128 x) (key128 (BitVec.ofNat 128 9223372036854775807))))
                     Bool.true))
            (Nat.le (key128 x) (key128 (BitVec.ofNat 128 9223372036854775807))))
        (Or (Eq (Decidable.decide
                    (Nat.le (key128 x) (key128 (BitVec.ofNat 128 9223372036854775807)))
                    (Nat.decLe (key128 x) (key128 (BitVec.ofNat 128 9223372036854775807))))
                Bool.true)
            (Nat.lt (key128 (BitVec.ofNat 128 9223372036854775807)) (key128 x))) :=
    fun x => decide_le_exact (key128 x) (key128 (BitVec.ofNat 128 9223372036854775807))

theorem guard_fits_exact : forall (x : BitVec 128),
    And (Or (Not (Eq (Bool.and
                        (Decidable.decide
                            (Nat.le (key128 (BitVec.ofNat 128 340282366920938463454151235394913435648)) (key128 x))
                            (Nat.decLe (key128 (BitVec.ofNat 128 340282366920938463454151235394913435648)) (key128 x)))
                        (Decidable.decide
                            (Nat.le (key128 x) (key128 (BitVec.ofNat 128 9223372036854775807)))
                            (Nat.decLe (key128 x) (key128 (BitVec.ofNat 128 9223372036854775807)))))
                     Bool.true))
            (And (Nat.le (key128 (BitVec.ofNat 128 340282366920938463454151235394913435648)) (key128 x))
                 (Nat.le (key128 x) (key128 (BitVec.ofNat 128 9223372036854775807)))))
        (Or (Eq (Bool.and
                    (Decidable.decide
                        (Nat.le (key128 (BitVec.ofNat 128 340282366920938463454151235394913435648)) (key128 x))
                        (Nat.decLe (key128 (BitVec.ofNat 128 340282366920938463454151235394913435648)) (key128 x)))
                    (Decidable.decide
                        (Nat.le (key128 x) (key128 (BitVec.ofNat 128 9223372036854775807)))
                        (Nat.decLe (key128 x) (key128 (BitVec.ofNat 128 9223372036854775807)))))
                Bool.true)
            (Or (Nat.lt (key128 x) (key128 (BitVec.ofNat 128 340282366920938463454151235394913435648)))
                (Nat.lt (key128 (BitVec.ofNat 128 9223372036854775807)) (key128 x)))) :=
    fun x => decide_and_le_exact
        (key128 (BitVec.ofNat 128 340282366920938463454151235394913435648)) (key128 x)
        (key128 x) (key128 (BitVec.ofNat 128 9223372036854775807))

def toInt64 (v : BitVec 64) : Int :=
    match Nat.ble 9223372036854775808 (key64 v) with
    | true  => Int.ofNat (Nat.sub (key64 v) 9223372036854775808)
    | false => Int.negSucc (Nat.sub 9223372036854775807 (key64 v))

def toInt128 (v : BitVec 128) : Int :=
    match Nat.ble 170141183460469231731687303715884105728 (key128 v) with
    | true  => Int.ofNat (Nat.sub (key128 v) 170141183460469231731687303715884105728)
    | false => Int.negSucc (Nat.sub 170141183460469231731687303715884105727 (key128 v))

def ofInt64 (x : Int) : BitVec 64 :=
    match Int.ble (Int.ofNat 0) x with
    | true  => BitVec.ofNat 64 (Int.toNat x)
    | false => BitVec.ofNat 64 (Int.toNat (Int.add x (Int.ofNat 18446744073709551616)))

def ofInt128 (x : Int) : BitVec 128 :=
    match Int.ble (Int.ofNat 0) x with
    | true  => BitVec.ofNat 128 (Int.toNat x)
    | false => BitVec.ofNat 128 (Int.toNat (Int.add x (Int.ofNat 340282366920938463463374607431768211456)))

def i128Max : Int := 170141183460469231731687303715884105727

def i128Min : Int := Int.neg 170141183460469231731687303715884105728

def fitsI128 (x : Int) : Bool :=
    match Int.ble i128Min x with
    | true  => Int.ble x i128Max
    | false => false

def checkedAdd64 (a b : BitVec 64) : Option (BitVec 64) :=
    match VeriPbCore.fitsI64 (Int.add (toInt64 a) (toInt64 b)) with
    | true  => some (ofInt64 (Int.add (toInt64 a) (toInt64 b)))
    | false => none

def checkedSub64 (a b : BitVec 64) : Option (BitVec 64) :=
    match VeriPbCore.fitsI64 (Int.sub (toInt64 a) (toInt64 b)) with
    | true  => some (ofInt64 (Int.sub (toInt64 a) (toInt64 b)))
    | false => none

def checkedMul64 (a b : BitVec 64) : Option (BitVec 64) :=
    match VeriPbCore.fitsI64 (Int.mul (toInt64 a) (toInt64 b)) with
    | true  => some (ofInt64 (Int.mul (toInt64 a) (toInt64 b)))
    | false => none

theorem checkedAdd64_some : forall (a : BitVec 64) (b : BitVec 64),
    Eq (VeriPbCore.fitsI64 (Int.add (toInt64 a) (toInt64 b))) Bool.true ->
    Eq (checkedAdd64 a b) (some (ofInt64 (Int.add (toInt64 a) (toInt64 b)))) :=
    fun a b h =>
      congrArg
        (fun c : Bool =>
          match c with
          | true  => some (ofInt64 (Int.add (toInt64 a) (toInt64 b)))
          | false => (none : Option (BitVec 64)))
        h

theorem checkedAdd64_none : forall (a : BitVec 64) (b : BitVec 64),
    Eq (VeriPbCore.fitsI64 (Int.add (toInt64 a) (toInt64 b))) Bool.false ->
    Eq (checkedAdd64 a b) none :=
    fun a b h =>
      congrArg
        (fun c : Bool =>
          match c with
          | true  => some (ofInt64 (Int.add (toInt64 a) (toInt64 b)))
          | false => (none : Option (BitVec 64)))
        h

theorem checkedSub64_some : forall (a : BitVec 64) (b : BitVec 64),
    Eq (VeriPbCore.fitsI64 (Int.sub (toInt64 a) (toInt64 b))) Bool.true ->
    Eq (checkedSub64 a b) (some (ofInt64 (Int.sub (toInt64 a) (toInt64 b)))) :=
    fun a b h =>
      congrArg
        (fun c : Bool =>
          match c with
          | true  => some (ofInt64 (Int.sub (toInt64 a) (toInt64 b)))
          | false => (none : Option (BitVec 64)))
        h

theorem checkedSub64_none : forall (a : BitVec 64) (b : BitVec 64),
    Eq (VeriPbCore.fitsI64 (Int.sub (toInt64 a) (toInt64 b))) Bool.false ->
    Eq (checkedSub64 a b) none :=
    fun a b h =>
      congrArg
        (fun c : Bool =>
          match c with
          | true  => some (ofInt64 (Int.sub (toInt64 a) (toInt64 b)))
          | false => (none : Option (BitVec 64)))
        h

theorem checkedMul64_some : forall (a : BitVec 64) (b : BitVec 64),
    Eq (VeriPbCore.fitsI64 (Int.mul (toInt64 a) (toInt64 b))) Bool.true ->
    Eq (checkedMul64 a b) (some (ofInt64 (Int.mul (toInt64 a) (toInt64 b)))) :=
    fun a b h =>
      congrArg
        (fun c : Bool =>
          match c with
          | true  => some (ofInt64 (Int.mul (toInt64 a) (toInt64 b)))
          | false => (none : Option (BitVec 64)))
        h

theorem checkedMul64_none : forall (a : BitVec 64) (b : BitVec 64),
    Eq (VeriPbCore.fitsI64 (Int.mul (toInt64 a) (toInt64 b))) Bool.false ->
    Eq (checkedMul64 a b) none :=
    fun a b h =>
      congrArg
        (fun c : Bool =>
          match c with
          | true  => some (ofInt64 (Int.mul (toInt64 a) (toInt64 b)))
          | false => (none : Option (BitVec 64)))
        h

def checkedAdd128 (a b : BitVec 128) : Option (BitVec 128) :=
    match fitsI128 (Int.add (toInt128 a) (toInt128 b)) with
    | true  => some (ofInt128 (Int.add (toInt128 a) (toInt128 b)))
    | false => none

def checkedSub128 (a b : BitVec 128) : Option (BitVec 128) :=
    match fitsI128 (Int.sub (toInt128 a) (toInt128 b)) with
    | true  => some (ofInt128 (Int.sub (toInt128 a) (toInt128 b)))
    | false => none

def checkedMul128 (a b : BitVec 128) : Option (BitVec 128) :=
    match fitsI128 (Int.mul (toInt128 a) (toInt128 b)) with
    | true  => some (ofInt128 (Int.mul (toInt128 a) (toInt128 b)))
    | false => none

theorem checkedAdd128_some : forall (a : BitVec 128) (b : BitVec 128),
    Eq (fitsI128 (Int.add (toInt128 a) (toInt128 b))) Bool.true ->
    Eq (checkedAdd128 a b) (some (ofInt128 (Int.add (toInt128 a) (toInt128 b)))) :=
    fun a b h =>
      congrArg
        (fun c : Bool =>
          match c with
          | true  => some (ofInt128 (Int.add (toInt128 a) (toInt128 b)))
          | false => (none : Option (BitVec 128)))
        h

theorem checkedAdd128_none : forall (a : BitVec 128) (b : BitVec 128),
    Eq (fitsI128 (Int.add (toInt128 a) (toInt128 b))) Bool.false ->
    Eq (checkedAdd128 a b) none :=
    fun a b h =>
      congrArg
        (fun c : Bool =>
          match c with
          | true  => some (ofInt128 (Int.add (toInt128 a) (toInt128 b)))
          | false => (none : Option (BitVec 128)))
        h

theorem checkedSub128_some : forall (a : BitVec 128) (b : BitVec 128),
    Eq (fitsI128 (Int.sub (toInt128 a) (toInt128 b))) Bool.true ->
    Eq (checkedSub128 a b) (some (ofInt128 (Int.sub (toInt128 a) (toInt128 b)))) :=
    fun a b h =>
      congrArg
        (fun c : Bool =>
          match c with
          | true  => some (ofInt128 (Int.sub (toInt128 a) (toInt128 b)))
          | false => (none : Option (BitVec 128)))
        h

theorem checkedSub128_none : forall (a : BitVec 128) (b : BitVec 128),
    Eq (fitsI128 (Int.sub (toInt128 a) (toInt128 b))) Bool.false ->
    Eq (checkedSub128 a b) none :=
    fun a b h =>
      congrArg
        (fun c : Bool =>
          match c with
          | true  => some (ofInt128 (Int.sub (toInt128 a) (toInt128 b)))
          | false => (none : Option (BitVec 128)))
        h

theorem checkedMul128_some : forall (a : BitVec 128) (b : BitVec 128),
    Eq (fitsI128 (Int.mul (toInt128 a) (toInt128 b))) Bool.true ->
    Eq (checkedMul128 a b) (some (ofInt128 (Int.mul (toInt128 a) (toInt128 b)))) :=
    fun a b h =>
      congrArg
        (fun c : Bool =>
          match c with
          | true  => some (ofInt128 (Int.mul (toInt128 a) (toInt128 b)))
          | false => (none : Option (BitVec 128)))
        h

theorem checkedMul128_none : forall (a : BitVec 128) (b : BitVec 128),
    Eq (fitsI128 (Int.mul (toInt128 a) (toInt128 b))) Bool.false ->
    Eq (checkedMul128 a b) none :=
    fun a b h =>
      congrArg
        (fun c : Bool =>
          match c with
          | true  => some (ofInt128 (Int.mul (toInt128 a) (toInt128 b)))
          | false => (none : Option (BitVec 128)))
        h

theorem int_mul_comm : forall (x : Int) (y : Int), Eq (Int.mul x y) (Int.mul y x) :=
    fun x y =>
      @Int.rec (fun a : Int => Eq (Int.mul a y) (Int.mul y a))
        (fun m =>
          @Int.rec (fun b : Int => Eq (Int.mul (Int.ofNat m) b) (Int.mul b (Int.ofNat m)))
            (fun n => congrArg Int.ofNat (Nat.mul_comm m n))
            (fun n => congrArg Int.negOfNat (Nat.mul_comm m (Nat.succ n)))
            y)
        (fun m =>
          @Int.rec (fun b : Int => Eq (Int.mul (Int.negSucc m) b) (Int.mul b (Int.negSucc m)))
            (fun n => congrArg Int.negOfNat (Nat.mul_comm (Nat.succ m) n))
            (fun n => congrArg Int.ofNat (Nat.mul_comm (Nat.succ m) (Nat.succ n)))
            y)
        x

theorem fitsI128_zero : Eq (fitsI128 (Int.ofNat 0)) Bool.true := rfl

def isSomeB128 (o : Option (BitVec 128)) : Bool :=
    match o with
    | none   => false
    | some _ => true

theorem checkedAdd128_comm : forall (a : BitVec 128) (b : BitVec 128),
    Eq (checkedAdd128 a b) (checkedAdd128 b a) :=
    fun a b =>
      congrArg
        (fun z : Int =>
          match fitsI128 z with
          | true  => some (ofInt128 z)
          | false => (none : Option (BitVec 128)))
        (Int.add_comm (toInt128 a) (toInt128 b))

theorem checkedMul128_comm : forall (a : BitVec 128) (b : BitVec 128),
    Eq (checkedMul128 a b) (checkedMul128 b a) :=
    fun a b =>
      congrArg
        (fun z : Int =>
          match fitsI128 z with
          | true  => some (ofInt128 z)
          | false => (none : Option (BitVec 128)))
        (int_mul_comm (toInt128 a) (toInt128 b))

theorem checkedSub128_self_isSome : forall (a : BitVec 128),
    Not (Eq (checkedSub128 a a) none) :=
    fun a h =>
      Bool.noConfusion
        (congrArg isSomeB128
          (Eq.trans
            (Eq.symm (checkedSub128_some a a
              (Eq.trans (congrArg fitsI128 (Int.sub_self (toInt128 a))) fitsI128_zero)))
            h))

theorem ctrl_checkedAdd64_ok :
    Eq (checkedAdd64 (BitVec.ofNat 64 1) (BitVec.ofNat 64 2)) (some (BitVec.ofNat 64 3)) :=
    rfl

theorem ctrl_checkedAdd64_overflow :
    Eq (checkedAdd64 (BitVec.ofNat 64 9223372036854775807) (BitVec.ofNat 64 1)) none :=
    rfl

theorem ctrl_checkedSub64_underflow :
    Eq (checkedSub64 (BitVec.ofNat 64 9223372036854775808) (BitVec.ofNat 64 1)) none :=
    rfl

theorem ctrl_checkedMul64_min_neg1 :
    Eq (checkedMul64 (BitVec.ofNat 64 9223372036854775808) (BitVec.ofNat 64 18446744073709551615)) none :=
    rfl

theorem ctrl_checkedAdd128_ok :
    Eq (checkedAdd128 (BitVec.ofNat 128 1) (BitVec.ofNat 128 2)) (some (BitVec.ofNat 128 3)) :=
    rfl

theorem ctrl_checkedAdd128_neg :
    Eq (checkedAdd128 (BitVec.ofNat 128 1) (BitVec.ofNat 128 340282366920938463463374607431768211454))
       (some (BitVec.ofNat 128 340282366920938463463374607431768211455)) :=
    rfl

theorem ctrl_checkedMul128_min_neg1 :
    Eq (checkedMul128 (BitVec.ofNat 128 170141183460469231731687303715884105728) (BitVec.ofNat 128 340282366920938463463374607431768211455)) none :=
    rfl

theorem bool_xor_false : forall (t : Bool), Eq (Bool.xor t Bool.false) t :=
    fun t => @Bool.rec (fun b : Bool => Eq (Bool.xor b Bool.false) b) rfl rfl t

theorem bool_xor_xor_cancel_right : forall (t s : Bool),
    Eq (Bool.xor (Bool.xor t s) s) t :=
    fun t s =>
      @Bool.rec (fun b : Bool => Eq (Bool.xor (Bool.xor b s) s) b)
        (@Bool.rec (fun c : Bool => Eq (Bool.xor (Bool.xor Bool.false c) c) Bool.false)
          rfl rfl s)
        (@Bool.rec (fun c : Bool => Eq (Bool.xor (Bool.xor Bool.true c) c) Bool.true)
          rfl rfl s)
        t

theorem nat_lt_of_lt_of_le : forall (a : Nat) (b : Nat) (c : Nat),
    Nat.lt a b -> Nat.le b c -> Nat.lt a c :=
    fun a b c h1 h2 => Nat.le_trans h1 h2

theorem nat_lt_trans : forall (a : Nat) (b : Nat) (c : Nat),
    Nat.lt a b -> Nat.lt b c -> Nat.lt a c :=
    fun a b c h1 h2 => Nat.le_trans h1 (Nat.le_of_lt h2)

theorem nat_zero_lt_two_pow : forall (k : Nat), Nat.lt 0 (Nat.pow 2 k) :=
    fun k => Nat.pow_le_pow_right 2 0 k (Nat.le_of_ble_eq_true 1 2 rfl) (Nat.zero_le k)

theorem nat_two_pow_lt_two_pow : forall (i : Nat) (j : Nat), Nat.lt i j ->
    Nat.lt (Nat.pow 2 i) (Nat.pow 2 j) :=
    fun i j h =>
      nat_lt_of_lt_of_le (Nat.pow 2 i) (Nat.pow 2 (Nat.succ i)) (Nat.pow 2 j)
        (@Eq.subst Nat (fun w : Nat => Nat.lt (Nat.pow 2 i) w)
          (Nat.add (Nat.pow 2 i) (Nat.pow 2 i)) (Nat.pow 2 (Nat.succ i))
          (Eq.symm (Nat.pow_two_succ i))
          (Nat.add_lt_add_left 0 (Nat.pow 2 i) (nat_zero_lt_two_pow i) (Nat.pow 2 i)))
        (Nat.pow_le_pow_right 2 (Nat.succ i) j (Nat.le_of_ble_eq_true 1 2 rfl) h)

theorem nat_xor_xor_cancel_right : forall (a : Nat) (b : Nat),
    Eq (Nat.xor (Nat.xor a b) b) a :=
    fun a b =>
      Nat.eq_of_testBit_eq (Nat.xor (Nat.xor a b) b) a
        (fun i =>
          Eq.trans
            (Eq.trans
              (Nat.testBit_xor (Nat.xor a b) b i)
              (congrArg (fun w : Bool => Bool.xor w (Nat.testBit b i))
                (Nat.testBit_xor a b i)))
            (bool_xor_xor_cancel_right (Nat.testBit a i) (Nat.testBit b i)))

theorem nat_add_sub_cancel_left : forall (b : Nat) (x : Nat),
    Eq (Nat.sub (Nat.add b x) b) x :=
    fun b x =>
      Eq.trans
        (congrArg (fun w : Nat => Nat.sub w b) (Nat.add_comm b x))
        (Nat.add_sub_cancel x b)

theorem nat_add_sub_cancel_of_le : forall (p : Nat) (u : Nat), Nat.le p u ->
    Eq (Nat.add p (Nat.sub u p)) u :=
    fun p =>
      @Nat.rec (fun w : Nat => forall (u : Nat), Nat.le w u ->
          Eq (Nat.add w (Nat.sub u w)) u)
        (fun u _ => Nat.zero_add u)
        (fun p' ih u =>
          @Nat.rec (fun v : Nat => Nat.le (Nat.succ p') v ->
              Eq (Nat.add (Nat.succ p') (Nat.sub v (Nat.succ p'))) v)
            (fun hz => @False.elim
              (Eq (Nat.add (Nat.succ p') (Nat.sub Nat.zero (Nat.succ p'))) Nat.zero)
              (Nat.not_succ_le_zero p' hz))
            (fun u' _ h =>
              Eq.trans
                (Eq.trans
                  (congrArg (fun w : Nat => Nat.add (Nat.succ p') w)
                    (Nat.succ_sub_succ u' p'))
                  (Nat.succ_add p' (Nat.sub u' p')))
                (congrArg Nat.succ (ih u' (Nat.le_of_succ_le_succ p' u' h))))
            u)
        p

theorem nat_sub_lt_of_lt_add : forall (a : Nat) (b : Nat) (c : Nat),
    Nat.lt a (Nat.add b c) -> Nat.le b a -> Nat.lt (Nat.sub a b) c :=
    fun a b c h1 h2 =>
      @Eq.subst Nat (fun w : Nat => Nat.le (Nat.succ (Nat.sub a b)) w)
        (Nat.sub (Nat.add b c) b) c (nat_add_sub_cancel_left b c)
        (@Eq.subst Nat (fun w : Nat => Nat.le w (Nat.sub (Nat.add b c) b))
          (Nat.sub (Nat.add b (Nat.succ (Nat.sub a b))) b) (Nat.succ (Nat.sub a b))
          (nat_add_sub_cancel_left b (Nat.succ (Nat.sub a b)))
          (Nat.sub_le_sub_right (Nat.add b (Nat.succ (Nat.sub a b))) (Nat.add b c) b
            (@Eq.subst Nat (fun w : Nat => Nat.lt w (Nat.add b c))
              a (Nat.add b (Nat.sub a b))
              (Eq.symm (nat_add_sub_cancel_of_le b a h2))
              h1)))

theorem testbit_two_pow_below : forall (k : Nat) (i : Nat), Nat.lt i k ->
    Eq (Nat.testBit (Nat.pow 2 k) i) Bool.false :=
    fun k i hik =>
      Eq.trans
        (Nat.testBit_add_two_pow_lo k 0 (nat_zero_lt_two_pow k) i hik)
        (Nat.testBit_zero_eq_false i)

theorem testbit_two_pow_self : forall (k : Nat),
    Eq (Nat.testBit (Nat.pow 2 k) k) Bool.true :=
    fun k => Nat.testBit_add_two_pow_self k 0 (nat_zero_lt_two_pow k)

theorem xor_add_two_pow_bit_lo : forall (k : Nat) (u : Nat) (i : Nat),
    Nat.lt u (Nat.pow 2 k) -> Nat.lt i k ->
    Eq (Nat.testBit (Nat.xor (Nat.add (Nat.pow 2 k) u) (Nat.pow 2 k)) i)
       (Nat.testBit u i) :=
    fun k u i h hik =>
      Eq.trans
        (Eq.trans
          (Eq.trans
            (Nat.testBit_xor (Nat.add (Nat.pow 2 k) u) (Nat.pow 2 k) i)
            (congrArg (fun t : Bool => Bool.xor t (Nat.testBit (Nat.pow 2 k) i))
              (Nat.testBit_add_two_pow_lo k u h i hik)))
          (congrArg (fun s : Bool => Bool.xor (Nat.testBit u i) s)
            (testbit_two_pow_below k i hik)))
        (bool_xor_false (Nat.testBit u i))

theorem xor_add_two_pow_bit_self : forall (k : Nat) (u : Nat),
    Nat.lt u (Nat.pow 2 k) ->
    Eq (Nat.testBit (Nat.xor (Nat.add (Nat.pow 2 k) u) (Nat.pow 2 k)) k)
       (Nat.testBit u k) :=
    fun k u h =>
      Eq.trans
        (Eq.trans
          (Eq.trans
            (Nat.testBit_xor (Nat.add (Nat.pow 2 k) u) (Nat.pow 2 k) k)
            (congrArg (fun t : Bool => Bool.xor t (Nat.testBit (Nat.pow 2 k) k))
              (Nat.testBit_add_two_pow_self k u h)))
          (congrArg (fun s : Bool => Bool.xor Bool.true s)
            (testbit_two_pow_self k)))
        (Eq.symm (Nat.testBit_lt_pow k u h))

theorem xor_add_two_pow_bit_hi : forall (k : Nat) (u : Nat) (i : Nat),
    Nat.lt u (Nat.pow 2 k) -> Nat.lt k i ->
    Eq (Nat.testBit (Nat.xor (Nat.add (Nat.pow 2 k) u) (Nat.pow 2 k)) i)
       (Nat.testBit u i) :=
    fun k u i h hlt =>
      Eq.trans
        (Eq.trans
          (Eq.trans
            (Nat.testBit_xor (Nat.add (Nat.pow 2 k) u) (Nat.pow 2 k) i)
            (congrArg (fun t : Bool => Bool.xor t (Nat.testBit (Nat.pow 2 k) i))
              (Nat.testBit_lt_pow i (Nat.add (Nat.pow 2 k) u)
                (nat_lt_of_lt_of_le (Nat.add (Nat.pow 2 k) u)
                  (Nat.pow 2 (Nat.succ k)) (Nat.pow 2 i)
                  (@Eq.subst Nat
                    (fun w : Nat => Nat.lt (Nat.add (Nat.pow 2 k) u) w)
                    (Nat.add (Nat.pow 2 k) (Nat.pow 2 k)) (Nat.pow 2 (Nat.succ k))
                    (Eq.symm (Nat.pow_two_succ k))
                    (Nat.add_lt_add_left u (Nat.pow 2 k) h (Nat.pow 2 k)))
                  (Nat.pow_le_pow_right 2 (Nat.succ k) i
                    (Nat.le_of_ble_eq_true 1 2 rfl) hlt)))))
          (Nat.testBit_lt_pow i (Nat.pow 2 k) (nat_two_pow_lt_two_pow k i hlt)))
        (Eq.symm (Nat.testBit_lt_pow i u
          (nat_lt_trans u (Nat.pow 2 k) (Nat.pow 2 i) h
            (nat_two_pow_lt_two_pow k i hlt))))

theorem xor_two_pow_add_cancel : forall (k : Nat) (u : Nat),
    Nat.lt u (Nat.pow 2 k) ->
    Eq (Nat.xor (Nat.add (Nat.pow 2 k) u) (Nat.pow 2 k)) u :=
    fun k u h =>
      Nat.eq_of_testBit_eq (Nat.xor (Nat.add (Nat.pow 2 k) u) (Nat.pow 2 k)) u
        (fun i =>
          @Or.rec (Nat.le k i) (Nat.lt i k)
            (fun _ => Eq (Nat.testBit (Nat.xor (Nat.add (Nat.pow 2 k) u) (Nat.pow 2 k)) i)
                         (Nat.testBit u i))
            (fun hki =>
              @Or.rec (Nat.lt k i) (Eq k i)
                (fun _ => Eq (Nat.testBit (Nat.xor (Nat.add (Nat.pow 2 k) u) (Nat.pow 2 k)) i)
                             (Nat.testBit u i))
                (fun hlt => xor_add_two_pow_bit_hi k u i h hlt)
                (fun heq =>
                  @Eq.subst Nat
                    (fun w : Nat =>
                      Eq (Nat.testBit (Nat.xor (Nat.add (Nat.pow 2 k) u) (Nat.pow 2 k)) w)
                         (Nat.testBit u w))
                    k i heq (xor_add_two_pow_bit_self k u h))
                (Nat.lt_or_eq_of_le k i hki))
            (fun hik => xor_add_two_pow_bit_lo k u i h hik)
            (Nat.le_or_lt k i))

theorem xor_two_pow_of_lt : forall (k : Nat) (u : Nat),
    Nat.lt u (Nat.pow 2 k) ->
    Eq (Nat.xor u (Nat.pow 2 k)) (Nat.add u (Nat.pow 2 k)) :=
    fun k u h =>
      Eq.trans
        (Eq.trans
          (congrArg (fun w : Nat => Nat.xor w (Nat.pow 2 k))
            (Eq.symm (xor_two_pow_add_cancel k u h)))
          (nat_xor_xor_cancel_right (Nat.add (Nat.pow 2 k) u) (Nat.pow 2 k)))
        (Nat.add_comm (Nat.pow 2 k) u)

theorem xor_two_pow_of_ge : forall (k : Nat) (u : Nat),
    Nat.le (Nat.pow 2 k) u -> Nat.lt u (Nat.pow 2 (Nat.succ k)) ->
    Eq (Nat.xor u (Nat.pow 2 k)) (Nat.sub u (Nat.pow 2 k)) :=
    fun k u hle hlt =>
      Eq.trans
        (congrArg (fun w : Nat => Nat.xor w (Nat.pow 2 k))
          (Eq.symm (nat_add_sub_cancel_of_le (Nat.pow 2 k) u hle)))
        (xor_two_pow_add_cancel k (Nat.sub u (Nat.pow 2 k))
          (nat_sub_lt_of_lt_add u (Nat.pow 2 k) (Nat.pow 2 k)
            (@Eq.subst Nat (fun w : Nat => Nat.lt u w)
              (Nat.pow 2 (Nat.succ k)) (Nat.add (Nat.pow 2 k) (Nat.pow 2 k))
              (Nat.pow_two_succ k) hlt)
            hle))

theorem pow2_63_eq : Eq (Nat.pow 2 63) 9223372036854775808 := rfl
theorem pow2_64_eq : Eq (Nat.pow 2 64) 18446744073709551616 := rfl
theorem pow2_127_eq : Eq (Nat.pow 2 127) 170141183460469231731687303715884105728 := rfl
theorem pow2_128_eq : Eq (Nat.pow 2 128) 340282366920938463463374607431768211456 := rfl

theorem xor_pivot64_of_lt : forall (u : Nat), Nat.lt u 9223372036854775808 ->
    Eq (Nat.xor u 9223372036854775808) (Nat.add u 9223372036854775808) :=
    fun u h => xor_two_pow_of_lt 63 u h

theorem xor_pivot64_of_ge : forall (u : Nat),
    Nat.le 9223372036854775808 u -> Nat.lt u 18446744073709551616 ->
    Eq (Nat.xor u 9223372036854775808) (Nat.sub u 9223372036854775808) :=
    fun u h1 h2 => xor_two_pow_of_ge 63 u h1 h2

theorem xor_pivot128_of_lt : forall (u : Nat),
    Nat.lt u 170141183460469231731687303715884105728 ->
    Eq (Nat.xor u 170141183460469231731687303715884105728)
       (Nat.add u 170141183460469231731687303715884105728) :=
    fun u h => xor_two_pow_of_lt 127 u h

theorem xor_pivot128_of_ge : forall (u : Nat),
    Nat.le 170141183460469231731687303715884105728 u ->
    Nat.lt u 340282366920938463463374607431768211456 ->
    Eq (Nat.xor u 170141183460469231731687303715884105728)
       (Nat.sub u 170141183460469231731687303715884105728) :=
    fun u h1 h2 => xor_two_pow_of_ge 127 u h1 h2

def guardFitsW (x : BitVec 128) : Bool :=
    Bool.and
        (Decidable.decide
            (Nat.le (key128 (BitVec.ofNat 128 340282366920938463454151235394913435648)) (key128 x))
            (Nat.decLe (key128 (BitVec.ofNat 128 340282366920938463454151235394913435648)) (key128 x)))
        (Decidable.decide
            (Nat.le (key128 x) (key128 (BitVec.ofNat 128 9223372036854775807)))
            (Nat.decLe (key128 x) (key128 (BitVec.ofNat 128 9223372036854775807))))

theorem key128_min_pattern :
    Eq (key128 (BitVec.ofNat 128 340282366920938463454151235394913435648))
       170141183460469231722463931679029329920 := rfl

theorem key128_max_pattern :
    Eq (key128 (BitVec.ofNat 128 9223372036854775807))
       170141183460469231740910675752738881535 := rfl

theorem guardFitsW_bounds : forall (x : BitVec 128),
    Eq (guardFitsW x) Bool.true ->
    And (Nat.le (key128 (BitVec.ofNat 128 340282366920938463454151235394913435648)) (key128 x))
        (Nat.le (key128 x) (key128 (BitVec.ofNat 128 9223372036854775807))) :=
    fun x hg =>
      @Or.rec
        (Not (Eq (Bool.and
                    (Decidable.decide
                        (Nat.le (key128 (BitVec.ofNat 128 340282366920938463454151235394913435648)) (key128 x))
                        (Nat.decLe (key128 (BitVec.ofNat 128 340282366920938463454151235394913435648)) (key128 x)))
                    (Decidable.decide
                        (Nat.le (key128 x) (key128 (BitVec.ofNat 128 9223372036854775807)))
                        (Nat.decLe (key128 x) (key128 (BitVec.ofNat 128 9223372036854775807)))))
                 Bool.true))
        (And (Nat.le (key128 (BitVec.ofNat 128 340282366920938463454151235394913435648)) (key128 x))
             (Nat.le (key128 x) (key128 (BitVec.ofNat 128 9223372036854775807))))
        (fun _ =>
          And (Nat.le (key128 (BitVec.ofNat 128 340282366920938463454151235394913435648)) (key128 x))
              (Nat.le (key128 x) (key128 (BitVec.ofNat 128 9223372036854775807))))
        (fun hn => @False.elim
          (And (Nat.le (key128 (BitVec.ofNat 128 340282366920938463454151235394913435648)) (key128 x))
               (Nat.le (key128 x) (key128 (BitVec.ofNat 128 9223372036854775807))))
          (hn hg))
        (fun hand => hand)
        ((guard_fits_exact x).left)

theorem toInt128_in_i64_of_key_bounds : forall (x : BitVec 128),
    Nat.le 170141183460469231722463931679029329920 (key128 x) ->
    Nat.le (key128 x) 170141183460469231740910675752738881535 ->
    And (Int.le VeriPbCore.i64Min (toInt128 x)) (Int.le (toInt128 x) VeriPbCore.i64Max) :=
    fun x hlo hhi =>
      @Bool.rec
        (fun b : Bool =>
          (Eq (Nat.ble 170141183460469231731687303715884105728 (key128 x)) b) ->
          And (Int.le VeriPbCore.i64Min (match b with
                | true  => Int.ofNat (Nat.sub (key128 x) 170141183460469231731687303715884105728)
                | false => Int.negSucc (Nat.sub 170141183460469231731687303715884105727 (key128 x))))
              (Int.le (match b with
                | true  => Int.ofNat (Nat.sub (key128 x) 170141183460469231731687303715884105728)
                | false => Int.negSucc (Nat.sub 170141183460469231731687303715884105727 (key128 x)))
                VeriPbCore.i64Max))
        (fun _ => And.intro
          (VeriPbCore.int_neg_le_neg
            (Int.ofNat (Nat.succ (Nat.sub 170141183460469231731687303715884105727 (key128 x))))
            (Int.ofNat 9223372036854775808)
            (VeriPbCore.int_ofNat_le_ofNat
              (Nat.succ (Nat.sub 170141183460469231731687303715884105727 (key128 x)))
              9223372036854775808
              (Nat.succ_le_succ
                (Nat.sub_le_sub_left 170141183460469231731687303715884105727
                  170141183460469231722463931679029329920 (key128 x) hlo))))
          (Int.le_of_ble_eq_true
            (Int.negSucc (Nat.sub 170141183460469231731687303715884105727 (key128 x)))
            VeriPbCore.i64Max rfl))
        (fun _ => And.intro
          (Int.le_of_ble_eq_true VeriPbCore.i64Min
            (Int.ofNat (Nat.sub (key128 x) 170141183460469231731687303715884105728)) rfl)
          (VeriPbCore.int_ofNat_le_ofNat
            (Nat.sub (key128 x) 170141183460469231731687303715884105728)
            9223372036854775807
            (Nat.sub_le_sub_right (key128 x) 170141183460469231740910675752738881535
              170141183460469231731687303715884105728 hhi)))
        (Nat.ble 170141183460469231731687303715884105728 (key128 x))
        rfl

theorem toInt128_in_i64_of_guard : forall (x : BitVec 128),
    Eq (guardFitsW x) Bool.true ->
    And (Int.le VeriPbCore.i64Min (toInt128 x)) (Int.le (toInt128 x) VeriPbCore.i64Max) :=
    fun x hg =>
      toInt128_in_i64_of_key_bounds x
        (guardFitsW_bounds x hg).left
        (guardFitsW_bounds x hg).right

theorem fitsI128_sub_of_bounds : forall (A : Int) (B : Int),
    Int.le VeriPbCore.i64Min A -> Int.le A VeriPbCore.i64Max ->
    Int.le VeriPbCore.i64Min B -> Int.le B VeriPbCore.i64Max ->
    Eq (fitsI128 (Int.sub A B)) Bool.true :=
    fun A B hAlo hAhi hBlo hBhi =>
      Eq.trans
        (congrArg
          (fun c : Bool =>
            match c with
            | true  => Int.ble (Int.sub A B) i128Max
            | false => Bool.false)
          (Int.ble_eq_true_of_le i128Min (Int.sub A B)
            (Int.le_trans i128Min (Int.neg 18446744073709551615) (Int.sub A B)
              (Int.le_of_ble_eq_true i128Min (Int.neg 18446744073709551615) rfl)
              (VeriPbCore.le_congr_left
                (Int.add VeriPbCore.i64Min (Int.neg VeriPbCore.i64Max))
                (Int.neg 18446744073709551615)
                (Int.add A (Int.neg B))
                rfl
                (VeriPbCore.add_le_add VeriPbCore.i64Min (Int.neg VeriPbCore.i64Max) A (Int.neg B)
                  hAlo
                  (VeriPbCore.int_neg_le_neg B VeriPbCore.i64Max hBhi))))))
        (Int.ble_eq_true_of_le (Int.sub A B) i128Max
          (Int.le_trans (Int.sub A B) (Int.ofNat 18446744073709551615) i128Max
            (VeriPbCore.le_congr_right
              (Int.add VeriPbCore.i64Max (Int.neg VeriPbCore.i64Min))
              (Int.ofNat 18446744073709551615)
              (Int.sub A B)
              rfl
              (VeriPbCore.add_le_add A (Int.neg B) VeriPbCore.i64Max (Int.neg VeriPbCore.i64Min)
                hAhi
                (VeriPbCore.int_neg_le_neg VeriPbCore.i64Min B hBlo)))
            (Int.le_of_ble_eq_true (Int.ofNat 18446744073709551615) i128Max rfl)))

theorem fitsI128_add_of_bounds : forall (A : Int) (B : Int),
    Int.le VeriPbCore.i64Min A -> Int.le A VeriPbCore.i64Max ->
    Int.le VeriPbCore.i64Min B -> Int.le B VeriPbCore.i64Max ->
    Eq (fitsI128 (Int.add A B)) Bool.true :=
    fun A B hAlo hAhi hBlo hBhi =>
      Eq.trans
        (congrArg
          (fun c : Bool =>
            match c with
            | true  => Int.ble (Int.add A B) i128Max
            | false => Bool.false)
          (Int.ble_eq_true_of_le i128Min (Int.add A B)
            (Int.le_trans i128Min (Int.neg 18446744073709551616) (Int.add A B)
              (Int.le_of_ble_eq_true i128Min (Int.neg 18446744073709551616) rfl)
              (VeriPbCore.le_congr_left
                (Int.add VeriPbCore.i64Min VeriPbCore.i64Min)
                (Int.neg 18446744073709551616)
                (Int.add A B)
                rfl
                (VeriPbCore.add_le_add VeriPbCore.i64Min VeriPbCore.i64Min A B hAlo hBlo)))))
        (Int.ble_eq_true_of_le (Int.add A B) i128Max
          (Int.le_trans (Int.add A B) (Int.ofNat 18446744073709551614) i128Max
            (VeriPbCore.le_congr_right
              (Int.add VeriPbCore.i64Max VeriPbCore.i64Max)
              (Int.ofNat 18446744073709551614)
              (Int.add A B)
              rfl
              (VeriPbCore.add_le_add A B VeriPbCore.i64Max VeriPbCore.i64Max hAhi hBhi))
            (Int.le_of_ble_eq_true (Int.ofNat 18446744073709551614) i128Max rfl)))

theorem int_pow63_sq :
    Eq (Int.mul (Int.ofNat 9223372036854775808) (Int.ofNat 9223372036854775808))
       (Int.ofNat 85070591730234615865843651857942052864) := rfl

theorem int_mul_le_pp : forall (A : Int),
    Int.le (Int.ofNat 0) A -> Int.le A (Int.ofNat 9223372036854775808) ->
    Int.le (Int.mul A (Int.ofNat 9223372036854775808))
           (Int.ofNat 85070591730234615865843651857942052864) :=
    fun A h0A hAP =>
      VeriPbCore.le_congr_right
        (Int.mul (Int.ofNat 9223372036854775808) (Int.ofNat 9223372036854775808))
        (Int.ofNat 85070591730234615865843651857942052864)
        (Int.mul A (Int.ofNat 9223372036854775808))
        int_pow63_sq
        (VeriPbCore.le_congr_left
          (Int.mul (Int.ofNat 9223372036854775808) A)
          (Int.mul A (Int.ofNat 9223372036854775808))
          (Int.mul (Int.ofNat 9223372036854775808) (Int.ofNat 9223372036854775808))
          (int_mul_comm (Int.ofNat 9223372036854775808) A)
          (Int.mul_le_mul_of_nonneg_left A (Int.ofNat 9223372036854775808)
            (Int.ofNat 9223372036854775808)
            hAP
            (VeriPbCore.int_zero_le_ofNat 9223372036854775808)))

theorem int_mul_upper_nonneg : forall (A : Int) (B : Int),
    Int.le (Int.ofNat 0) A -> Int.le A (Int.ofNat 9223372036854775808) ->
    Int.le B (Int.ofNat 9223372036854775808) ->
    Int.le (Int.mul A B) (Int.ofNat 85070591730234615865843651857942052864) :=
    fun A B h0A hAP hBP =>
      Int.le_trans (Int.mul A B) (Int.mul A (Int.ofNat 9223372036854775808))
        (Int.ofNat 85070591730234615865843651857942052864)
        (Int.mul_le_mul_of_nonneg_left B (Int.ofNat 9223372036854775808) A hBP h0A)
        (int_mul_le_pp A h0A hAP)

theorem int_mul_lower_nonneg : forall (A : Int) (B : Int),
    Int.le (Int.ofNat 0) A -> Int.le A (Int.ofNat 9223372036854775808) ->
    Int.le (Int.neg (Int.ofNat 9223372036854775808)) B ->
    Int.le (Int.neg (Int.ofNat 85070591730234615865843651857942052864)) (Int.mul A B) :=
    fun A B h0A hAP hnB =>
      Int.le_trans (Int.neg (Int.ofNat 85070591730234615865843651857942052864))
        (Int.mul A (Int.neg (Int.ofNat 9223372036854775808)))
        (Int.mul A B)
        (VeriPbCore.le_congr_right
          (Int.neg (Int.mul A (Int.ofNat 9223372036854775808)))
          (Int.mul A (Int.neg (Int.ofNat 9223372036854775808)))
          (Int.neg (Int.ofNat 85070591730234615865843651857942052864))
          (Int.neg_mul_right A (Int.ofNat 9223372036854775808))
          (VeriPbCore.int_neg_le_neg
            (Int.mul A (Int.ofNat 9223372036854775808))
            (Int.ofNat 85070591730234615865843651857942052864)
            (int_mul_le_pp A h0A hAP)))
        (Int.mul_le_mul_of_nonneg_left (Int.neg (Int.ofNat 9223372036854775808)) B A hnB h0A)

theorem int_mul_bound_nonneg : forall (A : Int) (B : Int),
    Int.le (Int.ofNat 0) A -> Int.le A (Int.ofNat 9223372036854775808) ->
    Int.le (Int.neg (Int.ofNat 9223372036854775808)) B ->
    Int.le B (Int.ofNat 9223372036854775808) ->
    And (Int.le (Int.neg (Int.ofNat 85070591730234615865843651857942052864)) (Int.mul A B))
        (Int.le (Int.mul A B) (Int.ofNat 85070591730234615865843651857942052864)) :=
    fun A B h0A hAP hnB hBP =>
      And.intro (int_mul_lower_nonneg A B h0A hAP hnB)
                (int_mul_upper_nonneg A B h0A hAP hBP)

theorem int_mul_neg_flip : forall (A : Int) (B : Int),
    Eq (Int.mul (Int.neg A) B) (Int.neg (Int.mul A B)) :=
    fun A B =>
      Eq.trans (int_mul_comm (Int.neg A) B)
        (Eq.trans (Eq.symm (Int.neg_mul_right B A))
          (congrArg Int.neg (int_mul_comm B A)))

theorem int_neg_le_zero_of_le : forall (A : Int), Int.le A (Int.ofNat 0) ->
    Int.le (Int.ofNat 0) (Int.neg A) :=
    fun A hA0 => VeriPbCore.int_neg_le_neg A (Int.ofNat 0) hA0

theorem int_neg_le_p_of_neg_p_le : forall (A : Int),
    Int.le (Int.neg (Int.ofNat 9223372036854775808)) A ->
    Int.le (Int.neg A) (Int.ofNat 9223372036854775808) :=
    fun A hnA =>
      VeriPbCore.le_congr_right
        (Int.neg (Int.neg (Int.ofNat 9223372036854775808)))
        (Int.ofNat 9223372036854775808)
        (Int.neg A)
        (Int.neg_neg (Int.ofNat 9223372036854775808))
        (VeriPbCore.int_neg_le_neg (Int.neg (Int.ofNat 9223372036854775808)) A hnA)

theorem int_mul_lower_nonpos : forall (A : Int) (B : Int),
    Int.le A (Int.ofNat 0) ->
    Int.le (Int.neg (Int.ofNat 9223372036854775808)) A ->
    Int.le B (Int.ofNat 9223372036854775808) ->
    Int.le (Int.neg (Int.ofNat 85070591730234615865843651857942052864)) (Int.mul A B) :=
    fun A B hA0 hnA hBP =>
      VeriPbCore.le_congr_right
        (Int.neg (Int.mul (Int.neg A) B))
        (Int.mul A B)
        (Int.neg (Int.ofNat 85070591730234615865843651857942052864))
        (Eq.trans (congrArg Int.neg (int_mul_neg_flip A B)) (Int.neg_neg (Int.mul A B)))
        (VeriPbCore.int_neg_le_neg
          (Int.mul (Int.neg A) B)
          (Int.ofNat 85070591730234615865843651857942052864)
          (int_mul_upper_nonneg (Int.neg A) B
            (int_neg_le_zero_of_le A hA0)
            (int_neg_le_p_of_neg_p_le A hnA)
            hBP))

theorem int_mul_upper_nonpos : forall (A : Int) (B : Int),
    Int.le A (Int.ofNat 0) ->
    Int.le (Int.neg (Int.ofNat 9223372036854775808)) A ->
    Int.le (Int.neg (Int.ofNat 9223372036854775808)) B ->
    Int.le (Int.mul A B) (Int.ofNat 85070591730234615865843651857942052864) :=
    fun A B hA0 hnA hnB =>
      VeriPbCore.le_congr_right
        (Int.neg (Int.neg (Int.ofNat 85070591730234615865843651857942052864)))
        (Int.ofNat 85070591730234615865843651857942052864)
        (Int.mul A B)
        (Int.neg_neg (Int.ofNat 85070591730234615865843651857942052864))
        (VeriPbCore.le_congr_left
          (Int.neg (Int.mul (Int.neg A) B))
          (Int.mul A B)
          (Int.neg (Int.neg (Int.ofNat 85070591730234615865843651857942052864)))
          (Eq.trans (congrArg Int.neg (int_mul_neg_flip A B)) (Int.neg_neg (Int.mul A B)))
          (VeriPbCore.int_neg_le_neg
            (Int.neg (Int.ofNat 85070591730234615865843651857942052864))
            (Int.mul (Int.neg A) B)
            (int_mul_lower_nonneg (Int.neg A) B
              (int_neg_le_zero_of_le A hA0)
              (int_neg_le_p_of_neg_p_le A hnA)
              hnB)))

theorem int_mul_bound : forall (A : Int) (B : Int),
    Int.le (Int.neg (Int.ofNat 9223372036854775808)) A ->
    Int.le A (Int.ofNat 9223372036854775808) ->
    Int.le (Int.neg (Int.ofNat 9223372036854775808)) B ->
    Int.le B (Int.ofNat 9223372036854775808) ->
    And (Int.le (Int.neg (Int.ofNat 85070591730234615865843651857942052864)) (Int.mul A B))
        (Int.le (Int.mul A B) (Int.ofNat 85070591730234615865843651857942052864)) :=
    fun A B hnA hAP hnB hBP =>
      @Or.rec (Int.le (Int.ofNat 0) A) (Int.le A (Int.ofNat 0))
        (fun _ =>
          And (Int.le (Int.neg (Int.ofNat 85070591730234615865843651857942052864)) (Int.mul A B))
              (Int.le (Int.mul A B) (Int.ofNat 85070591730234615865843651857942052864)))
        (fun h0A => int_mul_bound_nonneg A B h0A hAP hnB hBP)
        (fun hA0 => And.intro
          (int_mul_lower_nonpos A B hA0 hnA hBP)
          (int_mul_upper_nonpos A B hA0 hnA hnB))
        (Int.le_total (Int.ofNat 0) A)

theorem int_in_p_of_in_i64_lo : forall (A : Int), Int.le VeriPbCore.i64Min A ->
    Int.le (Int.neg (Int.ofNat 9223372036854775808)) A :=
    fun A h => h

theorem int_in_p_of_in_i64_hi : forall (A : Int), Int.le A VeriPbCore.i64Max ->
    Int.le A (Int.ofNat 9223372036854775808) :=
    fun A h =>
      Int.le_trans A VeriPbCore.i64Max (Int.ofNat 9223372036854775808) h
        (Int.le_of_ble_eq_true VeriPbCore.i64Max (Int.ofNat 9223372036854775808) rfl)

theorem fitsI128_mul_of_bounds : forall (A : Int) (B : Int),
    Int.le VeriPbCore.i64Min A -> Int.le A VeriPbCore.i64Max ->
    Int.le VeriPbCore.i64Min B -> Int.le B VeriPbCore.i64Max ->
    Eq (fitsI128 (Int.mul A B)) Bool.true :=
    fun A B hAlo hAhi hBlo hBhi =>
      Eq.trans
        (congrArg
          (fun c : Bool =>
            match c with
            | true  => Int.ble (Int.mul A B) i128Max
            | false => Bool.false)
          (Int.ble_eq_true_of_le i128Min (Int.mul A B)
            (Int.le_trans i128Min
              (Int.neg (Int.ofNat 85070591730234615865843651857942052864))
              (Int.mul A B)
              (Int.le_of_ble_eq_true i128Min
                (Int.neg (Int.ofNat 85070591730234615865843651857942052864)) rfl)
              (int_mul_bound A B
                (int_in_p_of_in_i64_lo A hAlo) (int_in_p_of_in_i64_hi A hAhi)
                (int_in_p_of_in_i64_lo B hBlo) (int_in_p_of_in_i64_hi B hBhi)).left)))
        (Int.ble_eq_true_of_le (Int.mul A B) i128Max
          (Int.le_trans (Int.mul A B)
            (Int.ofNat 85070591730234615865843651857942052864)
            i128Max
            (int_mul_bound A B
              (int_in_p_of_in_i64_lo A hAlo) (int_in_p_of_in_i64_hi A hAhi)
              (int_in_p_of_in_i64_lo B hBlo) (int_in_p_of_in_i64_hi B hBhi)).right
            (Int.le_of_ble_eq_true
              (Int.ofNat 85070591730234615865843651857942052864) i128Max rfl)))

theorem checkedSub128_isSome_of_inI64 : forall (a : BitVec 128) (b : BitVec 128),
    Eq (guardFitsW a) Bool.true -> Eq (guardFitsW b) Bool.true ->
    Not (Eq (checkedSub128 a b) none) :=
    fun a b ha hb hn =>
      Bool.noConfusion
        (congrArg isSomeB128
          (Eq.trans
            (Eq.symm (checkedSub128_some a b
              (fitsI128_sub_of_bounds (toInt128 a) (toInt128 b)
                (toInt128_in_i64_of_guard a ha).left
                (toInt128_in_i64_of_guard a ha).right
                (toInt128_in_i64_of_guard b hb).left
                (toInt128_in_i64_of_guard b hb).right)))
            hn))

theorem checkedAdd128_isSome_of_inI64 : forall (a : BitVec 128) (b : BitVec 128),
    Eq (guardFitsW a) Bool.true -> Eq (guardFitsW b) Bool.true ->
    Not (Eq (checkedAdd128 a b) none) :=
    fun a b ha hb hn =>
      Bool.noConfusion
        (congrArg isSomeB128
          (Eq.trans
            (Eq.symm (checkedAdd128_some a b
              (fitsI128_add_of_bounds (toInt128 a) (toInt128 b)
                (toInt128_in_i64_of_guard a ha).left
                (toInt128_in_i64_of_guard a ha).right
                (toInt128_in_i64_of_guard b hb).left
                (toInt128_in_i64_of_guard b hb).right)))
            hn))

theorem checkedMul128_isSome_of_inI64 : forall (a : BitVec 128) (b : BitVec 128),
    Eq (guardFitsW a) Bool.true -> Eq (guardFitsW b) Bool.true ->
    Not (Eq (checkedMul128 a b) none) :=
    fun a b ha hb hn =>
      Bool.noConfusion
        (congrArg isSomeB128
          (Eq.trans
            (Eq.symm (checkedMul128_some a b
              (fitsI128_mul_of_bounds (toInt128 a) (toInt128 b)
                (toInt128_in_i64_of_guard a ha).left
                (toInt128_in_i64_of_guard a ha).right
                (toInt128_in_i64_of_guard b hb).left
                (toInt128_in_i64_of_guard b hb).right)))
            hn))

theorem nat_succ_sub_self : forall (n : Nat), Eq (Nat.sub (Nat.succ n) n) 1 :=
    fun n =>
      @Nat.rec (fun w : Nat => Eq (Nat.sub (Nat.succ w) w) 1)
        rfl
        (fun n' ih => Eq.trans (Nat.succ_sub_succ (Nat.succ n') n') ih)
        n

theorem nat_one_le_sub_of_lt : forall (a n : Nat), Nat.lt a n ->
    Nat.le 1 (Nat.sub n a) :=
    fun a n h =>
      @Eq.subst Nat (fun w : Nat => Nat.le w (Nat.sub n a))
        (Nat.sub (Nat.succ a) a) 1
        (nat_succ_sub_self a)
        (Nat.sub_le_sub_right (Nat.succ a) n a h)

theorem nat_sub_pos_absurd : forall (a n : Nat), Nat.lt a n ->
    Eq (Nat.sub n a) Nat.zero -> False :=
    fun a n h heq0 =>
      Nat.not_succ_le_zero 0
        (@Eq.subst Nat (fun w : Nat => Nat.le 1 w) (Nat.sub n a) Nat.zero heq0
          (nat_one_le_sub_of_lt a n h))

theorem modcore_succ_unfold : forall (f a n : Nat),
    Eq (Nat.modCore (Nat.succ f) a n)
       (@Nat.rec (fun _ : Nat => Nat)
          (Nat.modCore f (Nat.sub a n) n)
          (fun _ _ => a)
          (Nat.sub n a)) :=
    fun f a n => rfl

theorem nat_rec_const_succ_arm : forall (base a x s : Nat),
    Eq x (Nat.succ s) ->
    Eq (@Nat.rec (fun _ : Nat => Nat) base (fun _ _ => a) x) a :=
    fun base a x s heq =>
      congrArg
        (fun t : Nat => @Nat.rec (fun _ : Nat => Nat) base (fun _ _ => a) t)
        heq

theorem modcore_succ_eq_of_lt : forall (f a n : Nat), Nat.lt a n ->
    Eq (Nat.modCore (Nat.succ f) a n) a :=
    fun f a n h =>
      @Nat.rec (fun s : Nat => Eq (Nat.sub n a) s -> Eq (Nat.modCore (Nat.succ f) a n) a)
        (fun heq0 => @False.elim (Eq (Nat.modCore (Nat.succ f) a n) a)
          (nat_sub_pos_absurd a n h heq0))
        (fun s _ heqs =>
          Eq.trans
            (modcore_succ_unfold f a n)
            (nat_rec_const_succ_arm (Nat.modCore f (Nat.sub a n) n) a (Nat.sub n a) s heqs))
        (Nat.sub n a)
        rfl

theorem nat_modCore_eq_of_lt : forall (f a n : Nat), Nat.lt a n ->
    Eq (Nat.modCore f a n) a :=
    fun f a n h =>
      @Nat.rec (fun w : Nat => Eq (Nat.modCore w a n) a)
        rfl
        (fun f' _ => modcore_succ_eq_of_lt f' a n h)
        f

theorem nat_mod_eq_of_lt : forall (a n : Nat), Nat.lt a n -> Eq (Nat.mod a n) a :=
    fun a n h => nat_modCore_eq_of_lt a a n h

theorem nat_add_sub_assoc : forall (a b c : Nat), Nat.le c b ->
    Eq (Nat.sub (Nat.add a b) c) (Nat.add a (Nat.sub b c)) :=
    fun a b c h =>
      Eq.trans
        (congrArg (fun w : Nat => Nat.sub (Nat.add a w) c)
          (Eq.symm (nat_add_sub_cancel_of_le c b h)))
        (Eq.trans
          (congrArg (fun w : Nat => Nat.sub w c)
            (Eq.trans
              (Eq.symm (Nat.add_assoc a c (Nat.sub b c)))
              (Eq.trans
                (congrArg (fun w : Nat => Nat.add w (Nat.sub b c)) (Nat.add_comm a c))
                (Nat.add_assoc c a (Nat.sub b c)))))
          (nat_add_sub_cancel_left c (Nat.add a (Nat.sub b c))))

theorem nat_sub_sub_cancel : forall (b c : Nat), Nat.le c b ->
    Eq (Nat.sub b (Nat.sub b c)) c :=
    fun b c h =>
      Eq.trans
        (congrArg (fun w : Nat => Nat.sub w (Nat.sub b c))
          (Eq.symm (nat_add_sub_cancel_of_le c b h)))
        (Nat.add_sub_cancel c (Nat.sub b c))

theorem nat_ble_false_of_lt : forall (a b : Nat), Nat.lt a b ->
    Eq (Nat.ble b a) Bool.false :=
    fun a b h =>
      @Bool.rec (fun c : Bool => Eq (Nat.ble b a) c -> Eq (Nat.ble b a) Bool.false)
        (fun hb => hb)
        (fun hb => @False.elim (Eq (Nat.ble b a) Bool.false)
          (Nat.lt_irrefl a (Nat.le_trans h (Nat.le_of_ble_eq_true b a hb))))
        (Nat.ble b a)
        rfl

theorem int_nonneg_subNatNat_le : forall (m k : Nat),
    Int.NonNeg (Int.subNatNat k m) -> Nat.le m k :=
    fun m =>
      @Nat.rec (fun w : Nat => forall (k : Nat),
          Int.NonNeg (Int.subNatNat k w) -> Nat.le w k)
        (fun k _ => Nat.zero_le k)
        (fun m' ih k =>
          @Nat.rec (fun v : Nat =>
              Int.NonNeg (Int.subNatNat v (Nat.succ m')) -> Nat.le (Nat.succ m') v)
            (fun hnn => @False.elim (Nat.le (Nat.succ m') Nat.zero)
              (Int.not_nonneg_negSucc m'
                (@Eq.subst Int (fun z : Int => Int.NonNeg z)
                  (Int.subNatNat Nat.zero (Nat.succ m')) (Int.negSucc m')
                  (Int.subNatNat_zero_succ m')
                  hnn)))
            (fun k' _ hnn =>
              Nat.succ_le_succ
                (ih k'
                  (@Eq.subst Int (fun z : Int => Int.NonNeg z)
                    (Int.subNatNat (Nat.succ k') (Nat.succ m')) (Int.subNatNat k' m')
                    (Int.subNatNat_succ_succ k' m')
                    hnn)))
            k)
        m

theorem int_ofNat_le_inv : forall (m k : Nat),
    Int.le (Int.ofNat m) (Int.ofNat k) -> Nat.le m k :=
    fun m k h =>
      int_nonneg_subNatNat_le m k
        (@Eq.subst Int (fun z : Int => Int.NonNeg z)
          (Int.add (Int.ofNat k) (Int.negOfNat m))
          (Int.subNatNat k m)
          (Eq.symm (Int.subNatNat_eq_add k m))
          h)

theorem int_negSucc_le_inv : forall (m k : Nat),
    Int.le (Int.negSucc k) (Int.negSucc m) -> Nat.le m k :=
    fun m k h =>
      Nat.le_of_succ_le_succ m k
        (int_nonneg_subNatNat_le (Nat.succ m) (Nat.succ k) h)

theorem int_ble_zero_negSucc : forall (m : Nat),
    Eq (Int.ble (Int.ofNat 0) (Int.negSucc m)) Bool.false :=
    fun m => congrArg Int.isNonNeg (Int.subNatNat_zero_succ m)

theorem int_subNatNat_add_cancel : forall (u m : Nat),
    Eq (Int.subNatNat (Nat.add u m) m) (Int.ofNat u) :=
    fun u m =>
      Eq.trans
        (congrArg (Int.subNatNat (Nat.add u m)) (Eq.symm (Nat.zero_add m)))
        (Int.subNatNat_add_add u 0 m)

theorem int_subNatNat_of_le : forall (k m : Nat), Nat.le m k ->
    Eq (Int.subNatNat k m) (Int.ofNat (Nat.sub k m)) :=
    fun k m h =>
      Eq.trans
        (congrArg (fun w : Nat => Int.subNatNat w m)
          (Eq.symm
            (Eq.trans (Nat.add_comm (Nat.sub k m) m)
              (nat_add_sub_cancel_of_le m k h))))
        (int_subNatNat_add_cancel (Nat.sub k m) m)

theorem toNat64_ofNat : forall (n : Nat),
    Eq (BitVec.toNat (BitVec.ofNat 64 n)) (Nat.mod n 18446744073709551616) :=
    fun n => rfl

theorem toNat64_ofNat_of_lt : forall (n : Nat), Nat.lt n 18446744073709551616 ->
    Eq (BitVec.toNat (BitVec.ofNat 64 n)) n :=
    fun n h => Eq.trans (toNat64_ofNat n) (nat_mod_eq_of_lt n 18446744073709551616 h)

theorem lt64_of_lt63 : forall (n : Nat), Nat.lt n 9223372036854775808 ->
    Nat.lt n 18446744073709551616 :=
    fun n h =>
      nat_lt_of_lt_of_le n 9223372036854775808 18446744073709551616 h
        (Nat.le_of_ble_eq_true 9223372036854775808 18446744073709551616 rfl)

theorem key64_ofNat_lo : forall (u : Nat), Nat.lt u 9223372036854775808 ->
    Eq (key64 (BitVec.ofNat 64 u)) (Nat.add u 9223372036854775808) :=
    fun u h =>
      Eq.trans
        (congrArg (fun t : Nat => Nat.xor t 9223372036854775808)
          (toNat64_ofNat_of_lt u (lt64_of_lt63 u h)))
        (xor_pivot64_of_lt u h)

theorem key64_ofNat_hi : forall (u : Nat),
    Nat.le 9223372036854775808 u -> Nat.lt u 18446744073709551616 ->
    Eq (key64 (BitVec.ofNat 64 u)) (Nat.sub u 9223372036854775808) :=
    fun u hge hlt =>
      Eq.trans
        (congrArg (fun t : Nat => Nat.xor t 9223372036854775808)
          (toNat64_ofNat_of_lt u hlt))
        (xor_pivot64_of_ge u hge hlt)

theorem toInt64_of_key_true : forall (v : BitVec 64) (k : Nat),
    Eq (key64 v) k -> Eq (Nat.ble 9223372036854775808 k) Bool.true ->
    Eq (toInt64 v) (Int.ofNat (Nat.sub k 9223372036854775808)) :=
    fun v k hk hb =>
      Eq.trans
        (congrArg
          (fun kn : Nat =>
            match Nat.ble 9223372036854775808 kn with
            | true  => Int.ofNat (Nat.sub kn 9223372036854775808)
            | false => Int.negSucc (Nat.sub 9223372036854775807 kn))
          hk)
        (congrArg
          (fun c : Bool =>
            match c with
            | true  => Int.ofNat (Nat.sub k 9223372036854775808)
            | false => Int.negSucc (Nat.sub 9223372036854775807 k))
          hb)

theorem toInt64_of_key_false : forall (v : BitVec 64) (k : Nat),
    Eq (key64 v) k -> Eq (Nat.ble 9223372036854775808 k) Bool.false ->
    Eq (toInt64 v) (Int.negSucc (Nat.sub 9223372036854775807 k)) :=
    fun v k hk hb =>
      Eq.trans
        (congrArg
          (fun kn : Nat =>
            match Nat.ble 9223372036854775808 kn with
            | true  => Int.ofNat (Nat.sub kn 9223372036854775808)
            | false => Int.negSucc (Nat.sub 9223372036854775807 kn))
          hk)
        (congrArg
          (fun c : Bool =>
            match c with
            | true  => Int.ofNat (Nat.sub k 9223372036854775808)
            | false => Int.negSucc (Nat.sub 9223372036854775807 k))
          hb)

theorem rt64_le_lits : Nat.le 9223372036854775807 18446744073709551615 :=
    Nat.le_of_ble_eq_true 9223372036854775807 18446744073709551615 rfl

theorem rt64_sub_lits :
    Eq (Nat.sub 18446744073709551615 9223372036854775807) 9223372036854775808 := rfl

theorem rt64_add_lits :
    Eq (Nat.add 9223372036854775808 9223372036854775807) 18446744073709551615 := rfl

theorem lt_pivot64_of_le_max : forall (m : Nat), Nat.le m 9223372036854775807 ->
    Nat.lt m 9223372036854775808 :=
    fun m h => Nat.succ_le_succ h

theorem le_pivot64_add : forall (m : Nat),
    Nat.le 9223372036854775808 (Nat.add m 9223372036854775808) :=
    fun m =>
      @Eq.subst Nat (fun w : Nat => Nat.le 9223372036854775808 w)
        (Nat.add 9223372036854775808 m) (Nat.add m 9223372036854775808)
        (Nat.add_comm 9223372036854775808 m)
        (Nat.le_add_right 9223372036854775808 m)

theorem ofInt64_ofNat_eq : forall (m : Nat),
    Eq (ofInt64 (Int.ofNat m)) (BitVec.ofNat 64 m) :=
    fun m => rfl

theorem toInt64_ofInt64_ofNat : forall (m : Nat), Nat.le m 9223372036854775807 ->
    Eq (toInt64 (ofInt64 (Int.ofNat m))) (Int.ofNat m) :=
    fun m hm =>
      Eq.trans
        (toInt64_of_key_true (ofInt64 (Int.ofNat m)) (Nat.add m 9223372036854775808)
          (Eq.trans
            (congrArg key64 (ofInt64_ofNat_eq m))
            (key64_ofNat_lo m (lt_pivot64_of_le_max m hm)))
          (Nat.ble_eq_true_of_le 9223372036854775808 (Nat.add m 9223372036854775808)
            (le_pivot64_add m)))
        (congrArg Int.ofNat (Nat.add_sub_cancel m 9223372036854775808))

theorem ofInt64_negSucc_arm : forall (m : Nat),
    Eq (ofInt64 (Int.negSucc m))
       (BitVec.ofNat 64 (Int.toNat (Int.add (Int.negSucc m) (Int.ofNat 18446744073709551616)))) :=
    fun m =>
      congrArg
        (fun c : Bool =>
          match c with
          | true  => BitVec.ofNat 64 (Int.toNat (Int.negSucc m))
          | false => BitVec.ofNat 64 (Int.toNat (Int.add (Int.negSucc m) (Int.ofNat 18446744073709551616))))
        (int_ble_zero_negSucc m)

theorem int_add_negSucc_pow64 : forall (m : Nat), Nat.le m 9223372036854775807 ->
    Eq (Int.add (Int.negSucc m) (Int.ofNat 18446744073709551616))
       (Int.ofNat (Nat.sub 18446744073709551615 m)) :=
    fun m hm =>
      Eq.trans
        (Int.add_negSucc_ofNat_succ 18446744073709551615 m)
        (int_subNatNat_of_le 18446744073709551615 m (Nat.le_trans hm rt64_le_lits))

theorem ofInt64_negSucc_eq : forall (m : Nat), Nat.le m 9223372036854775807 ->
    Eq (ofInt64 (Int.negSucc m)) (BitVec.ofNat 64 (Nat.sub 18446744073709551615 m)) :=
    fun m hm =>
      Eq.trans
        (ofInt64_negSucc_arm m)
        (congrArg (fun z : Int => BitVec.ofNat 64 (Int.toNat z))
          (int_add_negSucc_pow64 m hm))

theorem rt64_u_ge : forall (m : Nat), Nat.le m 9223372036854775807 ->
    Nat.le 9223372036854775808 (Nat.sub 18446744073709551615 m) :=
    fun m hm =>
      @Eq.subst Nat (fun w : Nat => Nat.le w (Nat.sub 18446744073709551615 m))
        (Nat.sub 18446744073709551615 9223372036854775807) 9223372036854775808
        rt64_sub_lits
        (Nat.sub_le_sub_left 18446744073709551615 m 9223372036854775807 hm)

theorem rt64_u_lt : forall (m : Nat),
    Nat.lt (Nat.sub 18446744073709551615 m) 18446744073709551616 :=
    fun m => Nat.succ_le_succ (Nat.sub_le 18446744073709551615 m)

theorem rt64_shift : forall (m : Nat), Nat.le m 9223372036854775807 ->
    Eq (Nat.sub 18446744073709551615 m)
       (Nat.add 9223372036854775808 (Nat.sub 9223372036854775807 m)) :=
    fun m hm =>
      Eq.trans
        (congrArg (fun w : Nat => Nat.sub w m) (Eq.symm rt64_add_lits))
        (nat_add_sub_assoc 9223372036854775808 9223372036854775807 m hm)

theorem rt64_key_sub : forall (m : Nat), Nat.le m 9223372036854775807 ->
    Eq (Nat.sub (Nat.sub 18446744073709551615 m) 9223372036854775808)
       (Nat.sub 9223372036854775807 m) :=
    fun m hm =>
      Eq.trans
        (congrArg (fun w : Nat => Nat.sub w 9223372036854775808) (rt64_shift m hm))
        (nat_add_sub_cancel_left 9223372036854775808 (Nat.sub 9223372036854775807 m))

theorem rt64_key : forall (m : Nat), Nat.le m 9223372036854775807 ->
    Eq (key64 (ofInt64 (Int.negSucc m))) (Nat.sub 9223372036854775807 m) :=
    fun m hm =>
      Eq.trans
        (congrArg key64 (ofInt64_negSucc_eq m hm))
        (Eq.trans
          (key64_ofNat_hi (Nat.sub 18446744073709551615 m) (rt64_u_ge m hm) (rt64_u_lt m))
          (rt64_key_sub m hm))

theorem rt64_key_lt : forall (m : Nat),
    Nat.lt (Nat.sub 9223372036854775807 m) 9223372036854775808 :=
    fun m => Nat.succ_le_succ (Nat.sub_le 9223372036854775807 m)

theorem toInt64_ofInt64_negSucc : forall (m : Nat), Nat.le m 9223372036854775807 ->
    Eq (toInt64 (ofInt64 (Int.negSucc m))) (Int.negSucc m) :=
    fun m hm =>
      Eq.trans
        (toInt64_of_key_false (ofInt64 (Int.negSucc m)) (Nat.sub 9223372036854775807 m)
          (rt64_key m hm)
          (nat_ble_false_of_lt (Nat.sub 9223372036854775807 m) 9223372036854775808
            (rt64_key_lt m)))
        (congrArg Int.negSucc (nat_sub_sub_cancel 9223372036854775807 m hm))

theorem toInt64_ofInt64 : forall (x : Int),
    Eq (VeriPbCore.fitsI64 x) Bool.true -> Eq (toInt64 (ofInt64 x)) x :=
    fun x =>
      @Int.rec (fun z : Int => Eq (VeriPbCore.fitsI64 z) Bool.true -> Eq (toInt64 (ofInt64 z)) z)
        (fun m h => toInt64_ofInt64_ofNat m
          (int_ofNat_le_inv m 9223372036854775807 (VeriPbCore.fitsI64_upper (Int.ofNat m) h)))
        (fun m h => toInt64_ofInt64_negSucc m
          (int_negSucc_le_inv m 9223372036854775807 (VeriPbCore.fitsI64_lower (Int.negSucc m) h)))
        x

theorem fitsI128_lower : forall (x : Int),
    Eq (fitsI128 x) Bool.true -> Int.le i128Min x :=
    fun x h =>
      @Bool.rec
        (fun b : Bool =>
          Eq (Int.ble i128Min x) b ->
          Eq (match b with
              | true  => Int.ble x i128Max
              | false => Bool.false) Bool.true ->
          Int.le i128Min x)
        (fun _ hh => Bool.noConfusion hh)
        (fun hb _ => Int.le_of_ble_eq_true i128Min x hb)
        (Int.ble i128Min x) rfl h

theorem fitsI128_upper : forall (x : Int),
    Eq (fitsI128 x) Bool.true -> Int.le x i128Max :=
    fun x h =>
      @Bool.rec
        (fun b : Bool =>
          Eq (Int.ble i128Min x) b ->
          Eq (match b with
              | true  => Int.ble x i128Max
              | false => Bool.false) Bool.true ->
          Int.le x i128Max)
        (fun _ hh => Bool.noConfusion hh)
        (fun _ hh => Int.le_of_ble_eq_true x i128Max hh)
        (Int.ble i128Min x) rfl h

theorem toNat128_ofNat : forall (n : Nat),
    Eq (BitVec.toNat (BitVec.ofNat 128 n))
       (Nat.mod n 340282366920938463463374607431768211456) :=
    fun n => rfl

theorem toNat128_ofNat_of_lt : forall (n : Nat),
    Nat.lt n 340282366920938463463374607431768211456 ->
    Eq (BitVec.toNat (BitVec.ofNat 128 n)) n :=
    fun n h =>
      Eq.trans (toNat128_ofNat n)
        (nat_mod_eq_of_lt n 340282366920938463463374607431768211456 h)

theorem lt128_of_lt127 : forall (n : Nat),
    Nat.lt n 170141183460469231731687303715884105728 ->
    Nat.lt n 340282366920938463463374607431768211456 :=
    fun n h =>
      nat_lt_of_lt_of_le n 170141183460469231731687303715884105728
        340282366920938463463374607431768211456 h
        (Nat.le_of_ble_eq_true 170141183460469231731687303715884105728
          340282366920938463463374607431768211456 rfl)

theorem key128_ofNat_lo : forall (u : Nat),
    Nat.lt u 170141183460469231731687303715884105728 ->
    Eq (key128 (BitVec.ofNat 128 u))
       (Nat.add u 170141183460469231731687303715884105728) :=
    fun u h =>
      Eq.trans
        (congrArg (fun t : Nat => Nat.xor t 170141183460469231731687303715884105728)
          (toNat128_ofNat_of_lt u (lt128_of_lt127 u h)))
        (xor_pivot128_of_lt u h)

theorem key128_ofNat_hi : forall (u : Nat),
    Nat.le 170141183460469231731687303715884105728 u ->
    Nat.lt u 340282366920938463463374607431768211456 ->
    Eq (key128 (BitVec.ofNat 128 u))
       (Nat.sub u 170141183460469231731687303715884105728) :=
    fun u hge hlt =>
      Eq.trans
        (congrArg (fun t : Nat => Nat.xor t 170141183460469231731687303715884105728)
          (toNat128_ofNat_of_lt u hlt))
        (xor_pivot128_of_ge u hge hlt)

theorem toInt128_of_key_true : forall (v : BitVec 128) (k : Nat),
    Eq (key128 v) k ->
    Eq (Nat.ble 170141183460469231731687303715884105728 k) Bool.true ->
    Eq (toInt128 v) (Int.ofNat (Nat.sub k 170141183460469231731687303715884105728)) :=
    fun v k hk hb =>
      Eq.trans
        (congrArg
          (fun kn : Nat =>
            match Nat.ble 170141183460469231731687303715884105728 kn with
            | true  => Int.ofNat (Nat.sub kn 170141183460469231731687303715884105728)
            | false => Int.negSucc (Nat.sub 170141183460469231731687303715884105727 kn))
          hk)
        (congrArg
          (fun c : Bool =>
            match c with
            | true  => Int.ofNat (Nat.sub k 170141183460469231731687303715884105728)
            | false => Int.negSucc (Nat.sub 170141183460469231731687303715884105727 k))
          hb)

theorem toInt128_of_key_false : forall (v : BitVec 128) (k : Nat),
    Eq (key128 v) k ->
    Eq (Nat.ble 170141183460469231731687303715884105728 k) Bool.false ->
    Eq (toInt128 v) (Int.negSucc (Nat.sub 170141183460469231731687303715884105727 k)) :=
    fun v k hk hb =>
      Eq.trans
        (congrArg
          (fun kn : Nat =>
            match Nat.ble 170141183460469231731687303715884105728 kn with
            | true  => Int.ofNat (Nat.sub kn 170141183460469231731687303715884105728)
            | false => Int.negSucc (Nat.sub 170141183460469231731687303715884105727 kn))
          hk)
        (congrArg
          (fun c : Bool =>
            match c with
            | true  => Int.ofNat (Nat.sub k 170141183460469231731687303715884105728)
            | false => Int.negSucc (Nat.sub 170141183460469231731687303715884105727 k))
          hb)

theorem rt128_le_lits :
    Nat.le 170141183460469231731687303715884105727 340282366920938463463374607431768211455 :=
    Nat.le_of_ble_eq_true 170141183460469231731687303715884105727
      340282366920938463463374607431768211455 rfl

theorem rt128_sub_lits :
    Eq (Nat.sub 340282366920938463463374607431768211455 170141183460469231731687303715884105727)
       170141183460469231731687303715884105728 := rfl

theorem rt128_add_lits :
    Eq (Nat.add 170141183460469231731687303715884105728 170141183460469231731687303715884105727)
       340282366920938463463374607431768211455 := rfl

theorem lt_pivot128_of_le_max : forall (m : Nat),
    Nat.le m 170141183460469231731687303715884105727 ->
    Nat.lt m 170141183460469231731687303715884105728 :=
    fun m h => Nat.succ_le_succ h

theorem le_pivot128_add : forall (m : Nat),
    Nat.le 170141183460469231731687303715884105728
           (Nat.add m 170141183460469231731687303715884105728) :=
    fun m =>
      @Eq.subst Nat (fun w : Nat => Nat.le 170141183460469231731687303715884105728 w)
        (Nat.add 170141183460469231731687303715884105728 m)
        (Nat.add m 170141183460469231731687303715884105728)
        (Nat.add_comm 170141183460469231731687303715884105728 m)
        (Nat.le_add_right 170141183460469231731687303715884105728 m)

theorem ofInt128_ofNat_eq : forall (m : Nat),
    Eq (ofInt128 (Int.ofNat m)) (BitVec.ofNat 128 m) :=
    fun m => rfl

theorem toInt128_ofInt128_ofNat : forall (m : Nat),
    Nat.le m 170141183460469231731687303715884105727 ->
    Eq (toInt128 (ofInt128 (Int.ofNat m))) (Int.ofNat m) :=
    fun m hm =>
      Eq.trans
        (toInt128_of_key_true (ofInt128 (Int.ofNat m))
          (Nat.add m 170141183460469231731687303715884105728)
          (Eq.trans
            (congrArg key128 (ofInt128_ofNat_eq m))
            (key128_ofNat_lo m (lt_pivot128_of_le_max m hm)))
          (Nat.ble_eq_true_of_le 170141183460469231731687303715884105728
            (Nat.add m 170141183460469231731687303715884105728)
            (le_pivot128_add m)))
        (congrArg Int.ofNat
          (Nat.add_sub_cancel m 170141183460469231731687303715884105728))

theorem ofInt128_negSucc_arm : forall (m : Nat),
    Eq (ofInt128 (Int.negSucc m))
       (BitVec.ofNat 128 (Int.toNat (Int.add (Int.negSucc m)
          (Int.ofNat 340282366920938463463374607431768211456)))) :=
    fun m =>
      congrArg
        (fun c : Bool =>
          match c with
          | true  => BitVec.ofNat 128 (Int.toNat (Int.negSucc m))
          | false => BitVec.ofNat 128 (Int.toNat (Int.add (Int.negSucc m)
              (Int.ofNat 340282366920938463463374607431768211456))))
        (int_ble_zero_negSucc m)

theorem int_add_negSucc_pow128 : forall (m : Nat),
    Nat.le m 170141183460469231731687303715884105727 ->
    Eq (Int.add (Int.negSucc m) (Int.ofNat 340282366920938463463374607431768211456))
       (Int.ofNat (Nat.sub 340282366920938463463374607431768211455 m)) :=
    fun m hm =>
      Eq.trans
        (Int.add_negSucc_ofNat_succ 340282366920938463463374607431768211455 m)
        (int_subNatNat_of_le 340282366920938463463374607431768211455 m
          (Nat.le_trans hm rt128_le_lits))

theorem ofInt128_negSucc_eq : forall (m : Nat),
    Nat.le m 170141183460469231731687303715884105727 ->
    Eq (ofInt128 (Int.negSucc m))
       (BitVec.ofNat 128 (Nat.sub 340282366920938463463374607431768211455 m)) :=
    fun m hm =>
      Eq.trans
        (ofInt128_negSucc_arm m)
        (congrArg (fun z : Int => BitVec.ofNat 128 (Int.toNat z))
          (int_add_negSucc_pow128 m hm))

theorem rt128_u_ge : forall (m : Nat),
    Nat.le m 170141183460469231731687303715884105727 ->
    Nat.le 170141183460469231731687303715884105728
           (Nat.sub 340282366920938463463374607431768211455 m) :=
    fun m hm =>
      @Eq.subst Nat
        (fun w : Nat => Nat.le w (Nat.sub 340282366920938463463374607431768211455 m))
        (Nat.sub 340282366920938463463374607431768211455 170141183460469231731687303715884105727)
        170141183460469231731687303715884105728
        rt128_sub_lits
        (Nat.sub_le_sub_left 340282366920938463463374607431768211455 m
          170141183460469231731687303715884105727 hm)

theorem rt128_u_lt : forall (m : Nat),
    Nat.lt (Nat.sub 340282366920938463463374607431768211455 m)
           340282366920938463463374607431768211456 :=
    fun m => Nat.succ_le_succ (Nat.sub_le 340282366920938463463374607431768211455 m)

theorem rt128_shift : forall (m : Nat),
    Nat.le m 170141183460469231731687303715884105727 ->
    Eq (Nat.sub 340282366920938463463374607431768211455 m)
       (Nat.add 170141183460469231731687303715884105728
                (Nat.sub 170141183460469231731687303715884105727 m)) :=
    fun m hm =>
      Eq.trans
        (congrArg (fun w : Nat => Nat.sub w m) (Eq.symm rt128_add_lits))
        (nat_add_sub_assoc 170141183460469231731687303715884105728
          170141183460469231731687303715884105727 m hm)

theorem rt128_key_sub : forall (m : Nat),
    Nat.le m 170141183460469231731687303715884105727 ->
    Eq (Nat.sub (Nat.sub 340282366920938463463374607431768211455 m)
                170141183460469231731687303715884105728)
       (Nat.sub 170141183460469231731687303715884105727 m) :=
    fun m hm =>
      Eq.trans
        (congrArg (fun w : Nat => Nat.sub w 170141183460469231731687303715884105728)
          (rt128_shift m hm))
        (nat_add_sub_cancel_left 170141183460469231731687303715884105728
          (Nat.sub 170141183460469231731687303715884105727 m))

theorem rt128_key : forall (m : Nat),
    Nat.le m 170141183460469231731687303715884105727 ->
    Eq (key128 (ofInt128 (Int.negSucc m)))
       (Nat.sub 170141183460469231731687303715884105727 m) :=
    fun m hm =>
      Eq.trans
        (congrArg key128 (ofInt128_negSucc_eq m hm))
        (Eq.trans
          (key128_ofNat_hi (Nat.sub 340282366920938463463374607431768211455 m)
            (rt128_u_ge m hm) (rt128_u_lt m))
          (rt128_key_sub m hm))

theorem rt128_key_lt : forall (m : Nat),
    Nat.lt (Nat.sub 170141183460469231731687303715884105727 m)
           170141183460469231731687303715884105728 :=
    fun m => Nat.succ_le_succ (Nat.sub_le 170141183460469231731687303715884105727 m)

theorem toInt128_ofInt128_negSucc : forall (m : Nat),
    Nat.le m 170141183460469231731687303715884105727 ->
    Eq (toInt128 (ofInt128 (Int.negSucc m))) (Int.negSucc m) :=
    fun m hm =>
      Eq.trans
        (toInt128_of_key_false (ofInt128 (Int.negSucc m))
          (Nat.sub 170141183460469231731687303715884105727 m)
          (rt128_key m hm)
          (nat_ble_false_of_lt (Nat.sub 170141183460469231731687303715884105727 m)
            170141183460469231731687303715884105728 (rt128_key_lt m)))
        (congrArg Int.negSucc
          (nat_sub_sub_cancel 170141183460469231731687303715884105727 m hm))

theorem toInt128_ofInt128 : forall (x : Int),
    Eq (fitsI128 x) Bool.true -> Eq (toInt128 (ofInt128 x)) x :=
    fun x =>
      @Int.rec (fun z : Int => Eq (fitsI128 z) Bool.true -> Eq (toInt128 (ofInt128 z)) z)
        (fun m h => toInt128_ofInt128_ofNat m
          (int_ofNat_le_inv m 170141183460469231731687303715884105727
            (fitsI128_upper (Int.ofNat m) h)))
        (fun m h => toInt128_ofInt128_negSucc m
          (int_negSucc_le_inv m 170141183460469231731687303715884105727
            (fitsI128_lower (Int.negSucc m) h)))
        x

theorem bitvec_eq_of_toNat_eq : forall (w : Nat) (x y : BitVec w),
    Eq (BitVec.toNat x) (BitVec.toNat y) -> Eq x y :=
    fun w x y h =>
      congrArg (@BitVec.ofFin w)
        (Fin.eq_of_val_eq (Nat.pow 2 w) (BitVec.toFin x) (BitVec.toFin y) h)

theorem bitvec128_ofNat_congr : forall (x y : Nat),
    Eq (Nat.mod x 340282366920938463463374607431768211456)
       (Nat.mod y 340282366920938463463374607431768211456) ->
    Eq (BitVec.ofNat 128 x) (BitVec.ofNat 128 y) :=
    fun x y h =>
      bitvec_eq_of_toNat_eq 128 (BitVec.ofNat 128 x) (BitVec.ofNat 128 y) h

theorem bitvec64_ofNat_congr : forall (x y : Nat),
    Eq (Nat.mod x 18446744073709551616) (Nat.mod y 18446744073709551616) ->
    Eq (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) :=
    fun x y h =>
      bitvec_eq_of_toNat_eq 64 (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) h

theorem nat_sub_one : forall (n : Nat), Eq (Nat.sub n 1) (Nat.pred n) :=
    fun n => rfl

theorem nat_sub_eq_zero_of_le : forall (a b : Nat), Nat.le a b ->
    Eq (Nat.sub a b) Nat.zero :=
    fun a b h =>
      Nat.le_antisymm (Nat.sub a b) Nat.zero
        (@Eq.subst Nat (fun w : Nat => Nat.le (Nat.sub a b) w) (Nat.sub b b) Nat.zero
          (Nat.sub_self b)
          (Nat.sub_le_sub_right a b b h))
        (Nat.zero_le (Nat.sub a b))

theorem nat_rec_const_zero_arm : forall (base a x : Nat),
    Eq x Nat.zero ->
    Eq (@Nat.rec (fun _ : Nat => Nat) base (fun _ _ => a) x) base :=
    fun base a x heq =>
      congrArg
        (fun t : Nat => @Nat.rec (fun _ : Nat => Nat) base (fun _ _ => a) t)
        heq

theorem modcore_succ_step_of_le : forall (f a n : Nat), Nat.le n a ->
    Eq (Nat.modCore (Nat.succ f) a n) (Nat.modCore f (Nat.sub a n) n) :=
    fun f a n h =>
      Eq.trans
        (modcore_succ_unfold f a n)
        (nat_rec_const_zero_arm (Nat.modCore f (Nat.sub a n) n) a (Nat.sub n a)
          (nat_sub_eq_zero_of_le n a h))

theorem nat_strong_ind : forall (P : Nat -> Prop),
    (forall (k : Nat), (forall (m : Nat), Nat.lt m k -> P m) -> P k) ->
    forall (n : Nat), P n :=
    fun P ind n =>
      ind n
        (@Nat.rec (fun b : Nat => forall (m : Nat), Nat.lt m b -> P m)
          (fun m hm => @False.elim (P m) (Nat.not_succ_le_zero m hm))
          (fun bq ih m hm =>
            @Or.rec (Nat.lt m bq) (Eq m bq) (fun _ => P m)
              (fun hlt => ih m hlt)
              (fun heq => ind m
                (fun j hj => ih j (@Eq.subst Nat (fun w : Nat => Nat.lt j w) m bq heq hj)))
              (Nat.lt_or_eq_of_le m bq (Nat.le_of_succ_le_succ m bq hm)))
          n)

theorem nat_pred_le_pred : forall (a f : Nat), Nat.le a f ->
    Nat.le (Nat.pred a) (Nat.pred f) :=
    fun a f h =>
      @Eq.subst Nat (fun w : Nat => Nat.le (Nat.sub a 1) w) (Nat.sub f 1) (Nat.pred f)
        (nat_sub_one f)
        (@Eq.subst Nat (fun w : Nat => Nat.le w (Nat.sub f 1)) (Nat.sub a 1) (Nat.pred a)
          (nat_sub_one a)
          (Nat.sub_le_sub_right a f 1 h))

theorem nat_sub_le_pred : forall (a n : Nat), Nat.le 1 n ->
    Nat.le (Nat.sub a n) (Nat.pred a) :=
    fun a n h1 =>
      @Eq.subst Nat (fun w : Nat => Nat.le (Nat.sub a n) w) (Nat.sub a 1) (Nat.pred a)
        (nat_sub_one a)
        (Nat.sub_le_sub_left a 1 n h1)

theorem nat_le_pred_of_succ_le : forall (y s : Nat), Nat.le (Nat.succ y) s ->
    Nat.le y (Nat.pred s) :=
    fun y s h =>
      @Eq.subst Nat (fun w : Nat => Nat.le y w) (Nat.sub s 1) (Nat.pred s)
        (nat_sub_one s)
        (Nat.sub_le_sub_right (Nat.succ y) s 1 h)

theorem modcore_fuel_case_ge : forall (n a f : Nat),
    (forall (m : Nat), Nat.lt m a ->
        forall (g : Nat), Nat.le m g ->
        Eq (Nat.modCore g m n) (Nat.modCore m m n)) ->
    Nat.lt 0 n -> Nat.le n a -> Nat.le a f ->
    Eq (Nat.modCore f a n) (Nat.modCore a a n) :=
    fun n a f IH hn hna haf =>
      Eq.trans
        (Eq.trans
          (Eq.trans
            (congrArg (fun w : Nat => Nat.modCore w a n)
              (Eq.symm (Nat.succ_pred_of_pos f
                (Nat.le_trans (Nat.le_trans hn hna) haf))))
            (modcore_succ_step_of_le (Nat.pred f) a n hna))
          (IH (Nat.sub a n) (Nat.sub_lt a n (Nat.le_trans hn hna) hn) (Nat.pred f)
            (Nat.le_trans (nat_sub_le_pred a n hn) (nat_pred_le_pred a f haf))))
        (Eq.symm
          (Eq.trans
            (Eq.trans
              (congrArg (fun w : Nat => Nat.modCore w a n)
                (Eq.symm (Nat.succ_pred_of_pos a (Nat.le_trans hn hna))))
              (modcore_succ_step_of_le (Nat.pred a) a n hna))
            (IH (Nat.sub a n) (Nat.sub_lt a n (Nat.le_trans hn hna) hn) (Nat.pred a)
              (nat_sub_le_pred a n hn))))

theorem nat_modCore_fuel_eq : forall (n : Nat), Nat.lt 0 n -> forall (a f : Nat),
    Nat.le a f -> Eq (Nat.modCore f a n) (Nat.modCore a a n) :=
    fun n hn a =>
      nat_strong_ind
        (fun w : Nat => forall (f : Nat), Nat.le w f ->
            Eq (Nat.modCore f w n) (Nat.modCore w w n))
        (fun k IH f hkf =>
          @Or.rec (Nat.le n k) (Nat.lt k n)
            (fun _ => Eq (Nat.modCore f k n) (Nat.modCore k k n))
            (fun hnk => modcore_fuel_case_ge n k f IH hn hnk hkf)
            (fun hlt =>
              Eq.trans (nat_modCore_eq_of_lt f k n hlt)
                (Eq.symm (nat_modCore_eq_of_lt k k n hlt)))
            (Nat.le_or_lt n k))
        a

theorem nat_le_add_left_flip : forall (K y : Nat), Nat.le K (Nat.add y K) :=
    fun K y =>
      @Eq.subst Nat (fun w : Nat => Nat.le K w) (Nat.add K y) (Nat.add y K)
        (Nat.add_comm K y)
        (Nat.le_add_right K y)

theorem nat_succ_le_add_of_pos : forall (y K : Nat), Nat.lt 0 K ->
    Nat.le (Nat.succ y) (Nat.add y K) :=
    fun y K hK =>
      @Eq.subst Nat (fun w : Nat => Nat.le w (Nat.add y K)) (Nat.add y 1) (Nat.succ y)
        rfl
        (Nat.add_le_add_left 1 K hK y)

theorem nat_mod_shift : forall (y K : Nat), Nat.lt 0 K ->
    Eq (Nat.mod (Nat.add y K) K) (Nat.mod y K) :=
    fun y K hK =>
      Eq.trans
        (Eq.trans
          (Eq.trans
            (congrArg (fun w : Nat => Nat.modCore w (Nat.add y K) K)
              (Eq.symm (Nat.succ_pred_of_pos (Nat.add y K)
                (Nat.le_trans hK (nat_le_add_left_flip K y)))))
            (modcore_succ_step_of_le (Nat.pred (Nat.add y K)) (Nat.add y K) K
              (nat_le_add_left_flip K y)))
          (congrArg (fun w : Nat => Nat.modCore (Nat.pred (Nat.add y K)) w K)
            (Nat.add_sub_cancel y K)))
        (nat_modCore_fuel_eq K hK y (Nat.pred (Nat.add y K))
          (nat_le_pred_of_succ_le y (Nat.add y K) (nat_succ_le_add_of_pos y K hK)))

theorem nat_mod_mul_shift : forall (K : Nat), Nat.lt 0 K -> forall (t y : Nat),
    Eq (Nat.mod (Nat.add y (Nat.mul K t)) K) (Nat.mod y K) :=
    fun K hK t =>
      @Nat.rec
        (fun w : Nat => forall (y : Nat),
            Eq (Nat.mod (Nat.add y (Nat.mul K w)) K) (Nat.mod y K))
        (fun y => rfl)
        (fun t' ih y =>
          Eq.trans
            (Eq.trans
              (congrArg (fun w : Nat => Nat.mod w K)
                (Eq.symm (Nat.add_assoc y (Nat.mul K t') K)))
              (nat_mod_shift (Nat.add y (Nat.mul K t')) K hK))
            (ih y))
        t

theorem nat_succ_sub : forall (b a : Nat), Nat.le b a ->
    Eq (Nat.sub (Nat.succ a) b) (Nat.succ (Nat.sub a b)) :=
    fun b =>
      @Nat.rec (fun w : Nat => forall (a : Nat), Nat.le w a ->
          Eq (Nat.sub (Nat.succ a) w) (Nat.succ (Nat.sub a w)))
        (fun a _ => rfl)
        (fun bq ih a =>
          @Nat.rec (fun v : Nat => Nat.le (Nat.succ bq) v ->
              Eq (Nat.sub (Nat.succ v) (Nat.succ bq)) (Nat.succ (Nat.sub v (Nat.succ bq))))
            (fun hz => @False.elim
              (Eq (Nat.sub (Nat.succ Nat.zero) (Nat.succ bq))
                  (Nat.succ (Nat.sub Nat.zero (Nat.succ bq))))
              (Nat.not_succ_le_zero bq hz))
            (fun a' _ h =>
              Eq.trans (Nat.succ_sub_succ (Nat.succ a') bq)
                (Eq.trans (ih a' (Nat.le_of_succ_le_succ bq a' h))
                  (congrArg Nat.succ (Eq.symm (Nat.succ_sub_succ a' bq)))))
            a)
        b

theorem bitvec_toNat_lt128 : forall (v : BitVec 128),
    Nat.lt (BitVec.toNat v) 340282366920938463463374607431768211456 :=
    fun v => Fin.isLt (Nat.pow 2 128) (BitVec.toFin v)

theorem bitvec_toNat_le_max128 : forall (v : BitVec 128),
    Nat.le (BitVec.toNat v) 340282366920938463463374607431768211455 :=
    fun v =>
      nat_le_pred_of_succ_le (BitVec.toNat v) 340282366920938463463374607431768211456
        (bitvec_toNat_lt128 v)

theorem toInt128_toNat_lo : forall (v : BitVec 128),
    Nat.lt (BitVec.toNat v) 170141183460469231731687303715884105728 ->
    Eq (toInt128 v) (Int.ofNat (BitVec.toNat v)) :=
    fun v h =>
      Eq.trans
        (toInt128_of_key_true v
          (Nat.add (BitVec.toNat v) 170141183460469231731687303715884105728)
          (xor_pivot128_of_lt (BitVec.toNat v) h)
          (Nat.ble_eq_true_of_le 170141183460469231731687303715884105728
            (Nat.add (BitVec.toNat v) 170141183460469231731687303715884105728)
            (le_pivot128_add (BitVec.toNat v))))
        (congrArg Int.ofNat
          (Nat.add_sub_cancel (BitVec.toNat v) 170141183460469231731687303715884105728))

theorem toInt128_key_hi_raw : forall (v : BitVec 128),
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat v) ->
    Eq (toInt128 v)
       (Int.negSucc (Nat.sub 170141183460469231731687303715884105727
          (Nat.sub (BitVec.toNat v) 170141183460469231731687303715884105728))) :=
    fun v h =>
      toInt128_of_key_false v
        (Nat.sub (BitVec.toNat v) 170141183460469231731687303715884105728)
        (xor_pivot128_of_ge (BitVec.toNat v) h (bitvec_toNat_lt128 v))
        (nat_ble_false_of_lt
          (Nat.sub (BitVec.toNat v) 170141183460469231731687303715884105728)
          170141183460469231731687303715884105728
          (nat_sub_lt_of_lt_add (BitVec.toNat v)
            170141183460469231731687303715884105728
            170141183460469231731687303715884105728
            (bitvec_toNat_lt128 v) h))

theorem nat_add_sub_add_right : forall (b k c : Nat),
    Eq (Nat.sub (Nat.add b c) (Nat.add k c)) (Nat.sub b k) :=
    fun b k c =>
      @Nat.rec (fun w : Nat => Eq (Nat.sub (Nat.add b w) (Nat.add k w)) (Nat.sub b k))
        rfl
        (fun c' ih => Eq.trans (Nat.succ_sub_succ (Nat.add b c') (Nat.add k c')) ih)
        c

theorem wrap_add_lits : Eq
    (Nat.add 170141183460469231731687303715884105727 170141183460469231731687303715884105728)
    340282366920938463463374607431768211455 := rfl

theorem toNat_hi_payload : forall (v : BitVec 128),
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat v) ->
    Eq (Nat.sub 170141183460469231731687303715884105727
          (Nat.sub (BitVec.toNat v) 170141183460469231731687303715884105728))
       (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat v)) :=
    fun v h =>
      Eq.symm
        (Eq.trans
          (congrArg (fun w : Nat => Nat.sub 340282366920938463463374607431768211455 w)
            (Eq.symm
              (Eq.trans
                (Nat.add_comm (Nat.sub (BitVec.toNat v) 170141183460469231731687303715884105728)
                  170141183460469231731687303715884105728)
                (nat_add_sub_cancel_of_le 170141183460469231731687303715884105728
                  (BitVec.toNat v) h))))
          (Eq.trans
            (congrArg
              (fun w : Nat => Nat.sub w
                (Nat.add (Nat.sub (BitVec.toNat v) 170141183460469231731687303715884105728)
                  170141183460469231731687303715884105728))
              (Eq.symm wrap_add_lits))
            (nat_add_sub_add_right 170141183460469231731687303715884105727
              (Nat.sub (BitVec.toNat v) 170141183460469231731687303715884105728)
              170141183460469231731687303715884105728)))

theorem toInt128_toNat_hi : forall (v : BitVec 128),
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat v) ->
    Eq (toInt128 v)
       (Int.negSucc (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat v))) :=
    fun v h =>
      Eq.trans (toInt128_key_hi_raw v h)
        (congrArg Int.negSucc (toNat_hi_payload v h))

theorem toNat_hi_cancel : forall (v : BitVec 128),
    Eq (Nat.add (BitVec.toNat v)
          (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat v)))
       340282366920938463463374607431768211455 :=
    fun v =>
      nat_add_sub_cancel_of_le (BitVec.toNat v) 340282366920938463463374607431768211455
        (bitvec_toNat_le_max128 v)

theorem nat_succ_add_flip : forall (d k : Nat),
    Eq (Nat.add (Nat.succ d) k) (Nat.add (Nat.succ k) d) :=
    fun d k =>
      Eq.trans (Nat.succ_add d k)
        (Eq.trans (congrArg Nat.succ (Nat.add_comm d k))
          (Eq.symm (Nat.succ_add k d)))

theorem int_subNatNat_of_lt : forall (k m : Nat), Nat.lt k m ->
    Eq (Int.subNatNat k m) (Int.negSucc (Nat.sub m (Nat.succ k))) :=
    fun k m h =>
      Eq.trans
        (congrArg (Int.subNatNat k)
          (Eq.symm
            (Eq.trans (nat_succ_add_flip (Nat.sub m (Nat.succ k)) k)
              (nat_add_sub_cancel_of_le (Nat.succ k) m h))))
        (Eq.trans
          (congrArg
            (fun w : Nat => Int.subNatNat w (Nat.add (Nat.succ (Nat.sub m (Nat.succ k))) k))
            (Eq.symm (Nat.zero_add k)))
          (Eq.trans
            (Int.subNatNat_add_add 0 (Nat.succ (Nat.sub m (Nat.succ k))) k)
            (Int.subNatNat_zero_succ (Nat.sub m (Nat.succ k)))))

theorem nat_sub_sub_of_le : forall (a c b : Nat), Nat.le a c -> Nat.le c b ->
    Eq (Nat.sub b (Nat.sub c a)) (Nat.add (Nat.sub b c) a) :=
    fun a c b hac hcb =>
      Eq.trans
        (congrArg (fun w : Nat => Nat.sub w (Nat.sub c a))
          (Eq.symm
            (Eq.trans (Nat.add_assoc (Nat.sub b c) a (Nat.sub c a))
              (Eq.trans
                (congrArg (Nat.add (Nat.sub b c)) (nat_add_sub_cancel_of_le a c hac))
                (Eq.trans (Nat.add_comm (Nat.sub b c) c)
                  (nat_add_sub_cancel_of_le c b hcb))))))
        (Nat.add_sub_cancel (Nat.add (Nat.sub b c) a) (Nat.sub c a))

theorem posW128 : Nat.lt 0 340282366920938463463374607431768211456 :=
    Nat.le_of_ble_eq_true 1 340282366920938463463374607431768211456 rfl

theorem P_le_Wm1 : Nat.le 170141183460469231731687303715884105728
    340282366920938463463374607431768211455 :=
    Nat.le_of_ble_eq_true 170141183460469231731687303715884105728
      340282366920938463463374607431768211455 rfl

theorem wrap_sub_lits : Eq
    (Nat.sub 340282366920938463463374607431768211455 170141183460469231731687303715884105728)
    170141183460469231731687303715884105727 := rfl

theorem int_add_negSucc_pow128_wide : forall (m : Nat),
    Nat.le m 340282366920938463463374607431768211455 ->
    Eq (Int.add (Int.negSucc m) (Int.ofNat 340282366920938463463374607431768211456))
       (Int.ofNat (Nat.sub 340282366920938463463374607431768211455 m)) :=
    fun m hm =>
      Eq.trans
        (Int.add_negSucc_ofNat_succ 340282366920938463463374607431768211455 m)
        (int_subNatNat_of_le 340282366920938463463374607431768211455 m hm)

theorem ofInt128_negSucc_wide : forall (m : Nat),
    Nat.le m 340282366920938463463374607431768211455 ->
    Eq (ofInt128 (Int.negSucc m))
       (BitVec.ofNat 128 (Nat.sub 340282366920938463463374607431768211455 m)) :=
    fun m hm =>
      Eq.trans
        (ofInt128_negSucc_arm m)
        (congrArg (fun z : Int => BitVec.ofNat 128 (Int.toNat z))
          (int_add_negSucc_pow128_wide m hm))

theorem hi_j_le : forall (v : BitVec 128),
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat v) ->
    Nat.le (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat v))
           170141183460469231731687303715884105727 :=
    fun v h =>
      @Eq.subst Nat
        (fun w : Nat =>
          Nat.le (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat v)) w)
        (Nat.sub 340282366920938463463374607431768211455 170141183460469231731687303715884105728)
        170141183460469231731687303715884105727
        wrap_sub_lits
        (Nat.sub_le_sub_left 340282366920938463463374607431768211455
          170141183460469231731687303715884105728 (BitVec.toNat v) h)

theorem wrap_add_ll : forall (a b : BitVec 128),
    Nat.lt (BitVec.toNat a) 170141183460469231731687303715884105728 ->
    Nat.lt (BitVec.toNat b) 170141183460469231731687303715884105728 ->
    Eq (ofInt128 (Int.add (toInt128 a) (toInt128 b)))
       (BitVec.ofNat 128 (Nat.add (BitVec.toNat a) (BitVec.toNat b))) :=
    fun a b ha hb =>
      Eq.trans
        (congrArg (fun z : Int => ofInt128 (Int.add z (toInt128 b)))
          (toInt128_toNat_lo a ha))
        (Eq.trans
          (congrArg (fun z : Int => ofInt128 (Int.add (Int.ofNat (BitVec.toNat a)) z))
            (toInt128_toNat_lo b hb))
          (ofInt128_ofNat_eq (Nat.add (BitVec.toNat a) (BitVec.toNat b))))

theorem wrap_hh_j_le : forall (a b : BitVec 128),
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat a) ->
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat b) ->
    Nat.le (Nat.succ (Nat.add
             (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))
             (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))
           340282366920938463463374607431768211455 :=
    fun a b ha hb =>
      Nat.succ_le_succ
        (Nat.add_le_add
          (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))
          170141183460469231731687303715884105727
          (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))
          170141183460469231731687303715884105727
          (hi_j_le a ha) (hi_j_le b hb))

theorem wrap_hh_sum1 : forall (a b : BitVec 128),
    Eq (Nat.add (BitVec.toNat b)
          (Nat.add (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))
                   (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))
       (Nat.add 340282366920938463463374607431768211455
          (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))) :=
    fun a b =>
      Eq.trans
        (congrArg (Nat.add (BitVec.toNat b))
          (Nat.add_comm (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))
                        (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))
        (Eq.trans
          (Eq.symm (Nat.add_assoc (BitVec.toNat b)
            (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))
            (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))))
          (congrArg
            (fun w : Nat => Nat.add w (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)))
            (toNat_hi_cancel b)))

theorem wrap_hh_sum2 : forall (a : BitVec 128),
    Eq (Nat.add (BitVec.toNat a)
          (Nat.add 340282366920938463463374607431768211455
            (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))))
       680564733841876926926749214863536422910 :=
    fun a =>
      Eq.trans
        (congrArg (Nat.add (BitVec.toNat a))
          (Nat.add_comm 340282366920938463463374607431768211455
            (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))))
        (Eq.trans
          (Eq.symm (Nat.add_assoc (BitVec.toNat a)
            (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))
            340282366920938463463374607431768211455))
          (congrArg (fun w : Nat => Nat.add w 340282366920938463463374607431768211455)
            (toNat_hi_cancel a)))

theorem wrap_hh_lhs : forall (a b : BitVec 128),
    Eq (Nat.add (Nat.add (BitVec.toNat a) (BitVec.toNat b))
          (Nat.add (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))
                   (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))
       680564733841876926926749214863536422910 :=
    fun a b =>
      Eq.trans
        (Nat.add_assoc (BitVec.toNat a) (BitVec.toNat b)
          (Nat.add (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))
                   (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))
        (Eq.trans
          (congrArg (Nat.add (BitVec.toNat a)) (wrap_hh_sum1 a b))
          (wrap_hh_sum2 a))

theorem wrap_dq_generic : forall (q : Nat),
    Nat.le (Nat.succ q) 340282366920938463463374607431768211455 ->
    Eq (Nat.add (Nat.sub 340282366920938463463374607431768211455 (Nat.succ q)) q)
       340282366920938463463374607431768211454 :=
    fun q hq =>
      congrArg Nat.pred
        (Eq.trans
          (Nat.add_comm (Nat.sub 340282366920938463463374607431768211455 (Nat.succ q))
            (Nat.succ q))
          (nat_add_sub_cancel_of_le (Nat.succ q) 340282366920938463463374607431768211455 hq))

theorem wrap_rhs_generic : forall (q : Nat),
    Nat.le (Nat.succ q) 340282366920938463463374607431768211455 ->
    Eq (Nat.add
         (Nat.add (Nat.sub 340282366920938463463374607431768211455 (Nat.succ q))
                  340282366920938463463374607431768211456)
         q)
       680564733841876926926749214863536422910 :=
    fun q hq =>
      Eq.trans
        (Nat.add_assoc (Nat.sub 340282366920938463463374607431768211455 (Nat.succ q))
          340282366920938463463374607431768211456 q)
        (Eq.trans
          (congrArg (Nat.add (Nat.sub 340282366920938463463374607431768211455 (Nat.succ q)))
            (Nat.add_comm 340282366920938463463374607431768211456 q))
          (Eq.trans
            (Eq.symm (Nat.add_assoc (Nat.sub 340282366920938463463374607431768211455 (Nat.succ q))
              q 340282366920938463463374607431768211456))
            (congrArg (fun w : Nat => Nat.add w 340282366920938463463374607431768211456)
              (wrap_dq_generic q hq))))

theorem wrap_hh_sumEq : forall (a b : BitVec 128),
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat a) ->
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat b) ->
    Eq (Nat.add (BitVec.toNat a) (BitVec.toNat b))
       (Nat.add
         (Nat.sub 340282366920938463463374607431768211455
           (Nat.succ (Nat.add
             (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))
             (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))))
         340282366920938463463374607431768211456) :=
    fun a b ha hb =>
      Nat.add_right_cancel
        (Nat.add (BitVec.toNat a) (BitVec.toNat b))
        (Nat.add (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))
                 (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))
        (Nat.add
          (Nat.sub 340282366920938463463374607431768211455
            (Nat.succ (Nat.add
              (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))
              (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))))
          340282366920938463463374607431768211456)
        (Eq.trans (wrap_hh_lhs a b)
          (Eq.symm (wrap_rhs_generic
            (Nat.add (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))
                     (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))
            (wrap_hh_j_le a b ha hb))))

theorem wrap_add_hh : forall (a b : BitVec 128),
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat a) ->
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat b) ->
    Eq (ofInt128 (Int.add (toInt128 a) (toInt128 b)))
       (BitVec.ofNat 128 (Nat.add (BitVec.toNat a) (BitVec.toNat b))) :=
    fun a b ha hb =>
      Eq.trans
        (Eq.trans
          (congrArg (fun z : Int => ofInt128 (Int.add z (toInt128 b)))
            (toInt128_toNat_hi a ha))
          (congrArg
            (fun z : Int => ofInt128 (Int.add
              (Int.negSucc (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))) z))
            (toInt128_toNat_hi b hb)))
        (Eq.trans
          (ofInt128_negSucc_wide
            (Nat.succ (Nat.add
              (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))
              (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))
            (wrap_hh_j_le a b ha hb))
          (bitvec128_ofNat_congr
            (Nat.sub 340282366920938463463374607431768211455
              (Nat.succ (Nat.add
                (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))
                (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))))
            (Nat.add (BitVec.toNat a) (BitVec.toNat b))
            (Eq.symm
              (Eq.trans
                (congrArg (fun w : Nat => Nat.mod w 340282366920938463463374607431768211456)
                  (wrap_hh_sumEq a b ha hb))
                (nat_mod_shift
                  (Nat.sub 340282366920938463463374607431768211455
                    (Nat.succ (Nat.add
                      (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))
                      (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))))
                  340282366920938463463374607431768211456 posW128)))))

theorem wrap_lh_sEq : forall (b : BitVec 128),
    Eq (Nat.sub 340282366920938463463374607431768211456 (BitVec.toNat b))
       (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))) :=
    fun b =>
      nat_succ_sub (BitVec.toNat b) 340282366920938463463374607431768211455
        (bitvec_toNat_le_max128 b)

theorem wrap_lh_WEq : forall (b : BitVec 128),
    Eq (Nat.add (BitVec.toNat b)
          (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))
       340282366920938463463374607431768211456 :=
    fun b =>
      Eq.trans
        (congrArg (Nat.add (BitVec.toNat b)) (Eq.symm (wrap_lh_sEq b)))
        (nat_add_sub_cancel_of_le (BitVec.toNat b) 340282366920938463463374607431768211456
          (Nat.le_of_lt (bitvec_toNat_lt128 b)))

theorem wrap_lh_sumEq : forall (a b : BitVec 128),
    Nat.le (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))
           (BitVec.toNat a) ->
    Eq (Nat.add
         (Nat.sub (BitVec.toNat a)
           (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))
         340282366920938463463374607431768211456)
       (Nat.add (BitVec.toNat a) (BitVec.toNat b)) :=
    fun a b hle =>
      Eq.trans
        (congrArg
          (Nat.add (Nat.sub (BitVec.toNat a)
            (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))))
          (Eq.symm (wrap_lh_WEq b)))
        (Eq.trans
          (congrArg
            (Nat.add (Nat.sub (BitVec.toNat a)
              (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))))
            (Nat.add_comm (BitVec.toNat b)
              (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))))
          (Eq.trans
            (Eq.symm (Nat.add_assoc
              (Nat.sub (BitVec.toNat a)
                (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))
              (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))
              (BitVec.toNat b)))
            (Eq.trans
              (congrArg (fun w : Nat => Nat.add w (BitVec.toNat b))
                (Nat.add_comm
                  (Nat.sub (BitVec.toNat a)
                    (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))
                  (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))))
              (congrArg (fun w : Nat => Nat.add w (BitVec.toNat b))
                (nat_add_sub_cancel_of_le
                  (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))
                  (BitVec.toNat a) hle)))))

theorem wrap_add_lh_nonneg : forall (a b : BitVec 128),
    Nat.lt (BitVec.toNat a) 170141183460469231731687303715884105728 ->
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat b) ->
    Nat.le (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))
           (BitVec.toNat a) ->
    Eq (ofInt128 (Int.add (toInt128 a) (toInt128 b)))
       (BitVec.ofNat 128 (Nat.add (BitVec.toNat a) (BitVec.toNat b))) :=
    fun a b ha hb hle =>
      Eq.trans
        (Eq.trans
          (congrArg (fun z : Int => ofInt128 (Int.add z (toInt128 b)))
            (toInt128_toNat_lo a ha))
          (congrArg
            (fun z : Int => ofInt128 (Int.add (Int.ofNat (BitVec.toNat a)) z))
            (toInt128_toNat_hi b hb)))
        (Eq.trans
          (congrArg ofInt128
            (int_subNatNat_of_le (BitVec.toNat a)
              (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))
              hle))
          (Eq.trans
            (ofInt128_ofNat_eq
              (Nat.sub (BitVec.toNat a)
                (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))))
            (bitvec128_ofNat_congr
              (Nat.sub (BitVec.toNat a)
                (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))
              (Nat.add (BitVec.toNat a) (BitVec.toNat b))
              (Eq.symm
                (Eq.trans
                  (congrArg (fun w : Nat => Nat.mod w 340282366920938463463374607431768211456)
                    (Eq.symm (wrap_lh_sumEq a b hle)))
                  (nat_mod_shift
                    (Nat.sub (BitVec.toNat a)
                      (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))
                    340282366920938463463374607431768211456 posW128))))))

theorem wrap_lh_neg_m_le : forall (b : BitVec 128) (x : Nat),
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat b) ->
    Nat.le (Nat.sub
             (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))
             (Nat.succ x))
           340282366920938463463374607431768211455 :=
    fun b x hb =>
      Nat.le_trans
        (Nat.sub_le
          (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))
          (Nat.succ x))
        (Nat.le_trans (Nat.succ_le_succ (hi_j_le b hb)) P_le_Wm1)

theorem wrap_lh_neg_payload : forall (a b : BitVec 128),
    Nat.lt (BitVec.toNat a)
      (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))) ->
    Eq (Nat.sub 340282366920938463463374607431768211455
         (Nat.sub
           (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))
           (Nat.succ (BitVec.toNat a))))
       (Nat.add (BitVec.toNat a) (BitVec.toNat b)) :=
    fun a b hlt =>
      Eq.trans
        (congrArg (Nat.sub 340282366920938463463374607431768211455)
          (Nat.succ_sub_succ
            (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))
            (BitVec.toNat a)))
        (Eq.trans
          (nat_sub_sub_of_le (BitVec.toNat a)
            (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))
            340282366920938463463374607431768211455
            (Nat.le_of_succ_le_succ (BitVec.toNat a)
              (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)) hlt)
            (Nat.sub_le 340282366920938463463374607431768211455 (BitVec.toNat b)))
          (Eq.trans
            (congrArg (fun w : Nat => Nat.add w (BitVec.toNat a))
              (nat_sub_sub_cancel 340282366920938463463374607431768211455 (BitVec.toNat b)
                (bitvec_toNat_le_max128 b)))
            (Nat.add_comm (BitVec.toNat b) (BitVec.toNat a))))

theorem wrap_add_lh_neg : forall (a b : BitVec 128),
    Nat.lt (BitVec.toNat a) 170141183460469231731687303715884105728 ->
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat b) ->
    Nat.lt (BitVec.toNat a)
      (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))) ->
    Eq (ofInt128 (Int.add (toInt128 a) (toInt128 b)))
       (BitVec.ofNat 128 (Nat.add (BitVec.toNat a) (BitVec.toNat b))) :=
    fun a b ha hb hlt =>
      Eq.trans
        (Eq.trans
          (congrArg (fun z : Int => ofInt128 (Int.add z (toInt128 b)))
            (toInt128_toNat_lo a ha))
          (congrArg
            (fun z : Int => ofInt128 (Int.add (Int.ofNat (BitVec.toNat a)) z))
            (toInt128_toNat_hi b hb)))
        (Eq.trans
          (congrArg ofInt128
            (int_subNatNat_of_lt (BitVec.toNat a)
              (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))
              hlt))
          (Eq.trans
            (ofInt128_negSucc_wide
              (Nat.sub
                (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))
                (Nat.succ (BitVec.toNat a)))
              (wrap_lh_neg_m_le b (BitVec.toNat a) hb))
            (congrArg (fun w : Nat => BitVec.ofNat 128 w) (wrap_lh_neg_payload a b hlt))))

theorem wrap_add_lh : forall (a b : BitVec 128),
    Nat.lt (BitVec.toNat a) 170141183460469231731687303715884105728 ->
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat b) ->
    Eq (ofInt128 (Int.add (toInt128 a) (toInt128 b)))
       (BitVec.ofNat 128 (Nat.add (BitVec.toNat a) (BitVec.toNat b))) :=
    fun a b ha hb =>
      @Or.rec
        (Nat.le (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))
                (BitVec.toNat a))
        (Nat.lt (BitVec.toNat a)
                (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))
        (fun _ => Eq (ofInt128 (Int.add (toInt128 a) (toInt128 b)))
                     (BitVec.ofNat 128 (Nat.add (BitVec.toNat a) (BitVec.toNat b))))
        (fun hle => wrap_add_lh_nonneg a b ha hb hle)
        (fun hlt => wrap_add_lh_neg a b ha hb hlt)
        (Nat.le_or_lt
          (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))
          (BitVec.toNat a))

theorem wrap_add_hl : forall (a b : BitVec 128),
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat a) ->
    Nat.lt (BitVec.toNat b) 170141183460469231731687303715884105728 ->
    Eq (ofInt128 (Int.add (toInt128 a) (toInt128 b)))
       (BitVec.ofNat 128 (Nat.add (BitVec.toNat a) (BitVec.toNat b))) :=
    fun a b ha hb =>
      Eq.trans
        (congrArg ofInt128 (Int.add_comm (toInt128 a) (toInt128 b)))
        (Eq.trans
          (wrap_add_lh b a hb ha)
          (congrArg (fun w : Nat => BitVec.ofNat 128 w)
            (Nat.add_comm (BitVec.toNat b) (BitVec.toNat a))))

theorem ofInt128_add_wrap : forall (a b : BitVec 128),
    Eq (ofInt128 (Int.add (toInt128 a) (toInt128 b)))
       (BitVec.ofNat 128 (Nat.add (BitVec.toNat a) (BitVec.toNat b))) :=
    fun a b =>
      @Or.rec
        (Nat.le 170141183460469231731687303715884105728 (BitVec.toNat a))
        (Nat.lt (BitVec.toNat a) 170141183460469231731687303715884105728)
        (fun _ => Eq (ofInt128 (Int.add (toInt128 a) (toInt128 b)))
                     (BitVec.ofNat 128 (Nat.add (BitVec.toNat a) (BitVec.toNat b))))
        (fun ha =>
          @Or.rec
            (Nat.le 170141183460469231731687303715884105728 (BitVec.toNat b))
            (Nat.lt (BitVec.toNat b) 170141183460469231731687303715884105728)
            (fun _ => Eq (ofInt128 (Int.add (toInt128 a) (toInt128 b)))
                         (BitVec.ofNat 128 (Nat.add (BitVec.toNat a) (BitVec.toNat b))))
            (fun hb => wrap_add_hh a b ha hb)
            (fun hb => wrap_add_hl a b ha hb)
            (Nat.le_or_lt 170141183460469231731687303715884105728 (BitVec.toNat b)))
        (fun ha =>
          @Or.rec
            (Nat.le 170141183460469231731687303715884105728 (BitVec.toNat b))
            (Nat.lt (BitVec.toNat b) 170141183460469231731687303715884105728)
            (fun _ => Eq (ofInt128 (Int.add (toInt128 a) (toInt128 b)))
                         (BitVec.ofNat 128 (Nat.add (BitVec.toNat a) (BitVec.toNat b))))
            (fun hb => wrap_add_lh a b ha hb)
            (fun hb => wrap_add_ll a b ha hb)
            (Nat.le_or_lt 170141183460469231731687303715884105728 (BitVec.toNat b)))
        (Nat.le_or_lt 170141183460469231731687303715884105728 (BitVec.toNat a))

theorem checkedAdd128_some_wrap : forall (a : BitVec 128) (b : BitVec 128),
    Eq (fitsI128 (Int.add (toInt128 a) (toInt128 b))) Bool.true ->
    Eq (checkedAdd128 a b)
       (some (BitVec.ofNat 128 (Nat.add (BitVec.toNat a) (BitVec.toNat b)))) :=
    fun a b h =>
      Eq.trans (checkedAdd128_some a b h)
        (congrArg (fun v : BitVec 128 => some v) (ofInt128_add_wrap a b))

theorem wsub_sWEq : forall (n : Nat),
    Eq (Nat.sub 340282366920938463463374607431768211456 (Nat.succ n))
       (Nat.sub 340282366920938463463374607431768211455 n) :=
    fun n => Nat.succ_sub_succ 340282366920938463463374607431768211455 n

theorem wsub_TEq : forall (a b : BitVec 128),
    Eq (Nat.sub (Nat.add (BitVec.toNat a) 340282366920938463463374607431768211456)
                (BitVec.toNat b))
       (Nat.add (BitVec.toNat a)
                (Nat.sub 340282366920938463463374607431768211456 (BitVec.toNat b))) :=
    fun a b =>
      nat_add_sub_assoc (BitVec.toNat a) 340282366920938463463374607431768211456
        (BitVec.toNat b) (Nat.le_of_lt (bitvec_toNat_lt128 b))

theorem nat_add_swap_right : forall (x s j : Nat),
    Eq (Nat.add (Nat.add x s) j) (Nat.add (Nat.add x j) s) :=
    fun x s j =>
      Eq.trans (Nat.add_assoc x s j)
        (Eq.trans (congrArg (Nat.add x) (Nat.add_comm s j))
          (Eq.symm (Nat.add_assoc x j s)))

theorem wsub_n2_lhs : forall (a b : BitVec 128),
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat a) ->
    Eq (Nat.add
         (Nat.add (BitVec.toNat a)
           (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))
         (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)))
       (Nat.add 340282366920938463463374607431768211455
         (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))) :=
    fun a b ha =>
      Eq.trans
        (nat_add_swap_right (BitVec.toNat a)
          (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))
          (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)))
        (congrArg
          (fun w : Nat => Nat.add w
            (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))
          (toNat_hi_cancel a))

theorem wsub_n2_rhs : forall (a b : BitVec 128),
    Nat.le (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))
           (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)) ->
    Eq (Nat.add
         (Nat.add
           (Nat.sub (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))
                    (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)))
           340282366920938463463374607431768211456)
         (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)))
       (Nat.add (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))
                340282366920938463463374607431768211456) :=
    fun a b h =>
      Eq.trans
        (nat_add_swap_right
          (Nat.sub (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))
                   (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)))
          340282366920938463463374607431768211456
          (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)))
        (congrArg
          (fun w : Nat => Nat.add w 340282366920938463463374607431768211456)
          (Eq.trans
            (Nat.add_comm
              (Nat.sub (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))
                       (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)))
              (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)))
            (nat_add_sub_cancel_of_le
              (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))
              (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))
              h)))

theorem wsub_succ_bridge : forall (x : Nat),
    Eq (Nat.add 340282366920938463463374607431768211455 (Nat.succ x))
       (Nat.add x 340282366920938463463374607431768211456) :=
    fun x =>
      congrArg Nat.succ (Nat.add_comm 340282366920938463463374607431768211455 x)

theorem wsub_n2 : forall (a b : BitVec 128),
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat a) ->
    Nat.le (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))
           (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)) ->
    Eq (Nat.add (BitVec.toNat a)
          (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))
       (Nat.add
         (Nat.sub (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))
                  (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)))
         340282366920938463463374607431768211456) :=
    fun a b ha h =>
      Nat.add_right_cancel
        (Nat.add (BitVec.toNat a)
          (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))
        (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))
        (Nat.add
          (Nat.sub (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))
                   (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)))
          340282366920938463463374607431768211456)
        (Eq.trans (wsub_n2_lhs a b ha)
          (Eq.trans
            (wsub_succ_bridge (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))
            (Eq.symm (wsub_n2_rhs a b h))))

theorem wsub_n3 : forall (a b : BitVec 128),
    Nat.lt (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))
           (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)) ->
    Eq (Nat.sub 340282366920938463463374607431768211455
          (Nat.sub (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))
                   (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))))
       (Nat.add (BitVec.toNat a)
          (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))) :=
    fun a b hlt =>
      Eq.trans
        (nat_sub_sub_of_le
          (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))
          (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))
          340282366920938463463374607431768211455
          hlt
          (Nat.sub_le 340282366920938463463374607431768211455 (BitVec.toNat a)))
        (Eq.trans
          (congrArg
            (fun w : Nat => Nat.add w
              (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))
            (nat_sub_sub_cancel 340282366920938463463374607431768211455 (BitVec.toNat a)
              (bitvec_toNat_le_max128 a)))
          (Eq.refl (Nat.add (BitVec.toNat a)
            (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))))

theorem wsub_n5_lhs : forall (na nb' : Nat), Nat.le (Nat.succ nb') na ->
    Eq (Nat.add (Nat.add (Nat.sub na (Nat.succ nb')) 340282366920938463463374607431768211456)
                (Nat.succ nb'))
       (Nat.add na 340282366920938463463374607431768211456) :=
    fun na nb' h =>
      Eq.trans
        (nat_add_swap_right (Nat.sub na (Nat.succ nb'))
          340282366920938463463374607431768211456 (Nat.succ nb'))
        (congrArg (fun w : Nat => Nat.add w 340282366920938463463374607431768211456)
          (Eq.trans (Nat.add_comm (Nat.sub na (Nat.succ nb')) (Nat.succ nb'))
            (nat_add_sub_cancel_of_le (Nat.succ nb') na h)))

theorem wsub_n5_rhs : forall (na nb' : Nat),
    Nat.le nb' 340282366920938463463374607431768211455 ->
    Eq (Nat.add (Nat.add na (Nat.sub 340282366920938463463374607431768211455 nb'))
                (Nat.succ nb'))
       (Nat.add na 340282366920938463463374607431768211456) :=
    fun na nb' hb =>
      Eq.trans
        (Nat.add_assoc na (Nat.sub 340282366920938463463374607431768211455 nb') (Nat.succ nb'))
        (congrArg (Nat.add na)
          (congrArg Nat.succ
            (Eq.trans
              (Nat.add_comm (Nat.sub 340282366920938463463374607431768211455 nb') nb')
              (nat_add_sub_cancel_of_le nb' 340282366920938463463374607431768211455 hb))))

theorem L1_le_Wm1 : Nat.le 170141183460469231731687303715884105727
    340282366920938463463374607431768211455 :=
    Nat.le_of_ble_eq_true 170141183460469231731687303715884105727
      340282366920938463463374607431768211455 rfl

theorem wsub_T_bhi : forall (a b : BitVec 128),
    Eq (Nat.sub (Nat.add (BitVec.toNat a) 340282366920938463463374607431768211456)
                (BitVec.toNat b))
       (Nat.add (BitVec.toNat a)
                (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))) :=
    fun a b =>
      Eq.trans (wsub_TEq a b)
        (congrArg (Nat.add (BitVec.toNat a)) (wrap_lh_sEq b))

theorem wsub_T_bs : forall (a b : BitVec 128) (nb' : Nat),
    Eq (BitVec.toNat b) (Nat.succ nb') ->
    Eq (Nat.sub (Nat.add (BitVec.toNat a) 340282366920938463463374607431768211456)
                (BitVec.toNat b))
       (Nat.add (BitVec.toNat a)
                (Nat.sub 340282366920938463463374607431768211455 nb')) :=
    fun a b nb' hs =>
      Eq.trans (wsub_TEq a b)
        (Eq.trans
          (congrArg (Nat.add (BitVec.toNat a))
            (congrArg (Nat.sub 340282366920938463463374607431768211456) hs))
          (congrArg (Nat.add (BitVec.toNat a)) (wsub_sWEq nb')))

theorem wsub_n5 : forall (na nb' : Nat),
    Nat.le (Nat.succ nb') na -> Nat.le nb' 340282366920938463463374607431768211455 ->
    Eq (Nat.add (Nat.sub na (Nat.succ nb')) 340282366920938463463374607431768211456)
       (Nat.add na (Nat.sub 340282366920938463463374607431768211455 nb')) :=
    fun na nb' hle hb =>
      Nat.add_right_cancel
        (Nat.add (Nat.sub na (Nat.succ nb')) 340282366920938463463374607431768211456)
        (Nat.succ nb')
        (Nat.add na (Nat.sub 340282366920938463463374607431768211455 nb'))
        (Eq.trans (wsub_n5_lhs na nb' hle) (Eq.symm (wsub_n5_rhs na nb' hb)))

theorem wsub_n6 : forall (na nb' : Nat),
    Nat.lt na (Nat.succ nb') -> Nat.le nb' 340282366920938463463374607431768211455 ->
    Eq (Nat.sub 340282366920938463463374607431768211455 (Nat.sub (Nat.succ nb') (Nat.succ na)))
       (Nat.add na (Nat.sub 340282366920938463463374607431768211455 nb')) :=
    fun na nb' hlt hb =>
      Eq.trans
        (congrArg (Nat.sub 340282366920938463463374607431768211455)
          (Nat.succ_sub_succ nb' na))
        (Eq.trans
          (nat_sub_sub_of_le na nb' 340282366920938463463374607431768211455
            (Nat.le_of_succ_le_succ na nb' hlt) hb)
          (Nat.add_comm (Nat.sub 340282366920938463463374607431768211455 nb') na))

theorem wsub_n7_lhs : forall (q : Nat),
    Nat.le (Nat.succ q) 340282366920938463463374607431768211455 ->
    Eq (Nat.add
         (Nat.add (Nat.sub 340282366920938463463374607431768211455 (Nat.succ q))
                  340282366920938463463374607431768211456)
         (Nat.succ q))
       680564733841876926926749214863536422911 :=
    fun q hq =>
      Eq.trans
        (nat_add_swap_right (Nat.sub 340282366920938463463374607431768211455 (Nat.succ q))
          340282366920938463463374607431768211456 (Nat.succ q))
        (congrArg (fun w : Nat => Nat.add w 340282366920938463463374607431768211456)
          (Eq.trans
            (Nat.add_comm (Nat.sub 340282366920938463463374607431768211455 (Nat.succ q))
              (Nat.succ q))
            (nat_add_sub_cancel_of_le (Nat.succ q) 340282366920938463463374607431768211455 hq)))

theorem wsub_n7_rhs_inner : forall (a : BitVec 128) (nb' : Nat),
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat a) ->
    Nat.le nb' 340282366920938463463374607431768211455 ->
    Eq (Nat.add
         (Nat.add (BitVec.toNat a) (Nat.sub 340282366920938463463374607431768211455 nb'))
         (Nat.add (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)) nb'))
       680564733841876926926749214863536422910 :=
    fun a nb' ha hb =>
      Eq.trans
        (Nat.add_assoc (BitVec.toNat a)
          (Nat.sub 340282366920938463463374607431768211455 nb')
          (Nat.add (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)) nb'))
        (Eq.trans
          (congrArg (Nat.add (BitVec.toNat a))
            (Eq.trans
              (congrArg (Nat.add (Nat.sub 340282366920938463463374607431768211455 nb'))
                (Nat.add_comm (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))
                  nb'))
              (Eq.trans
                (Eq.symm (Nat.add_assoc (Nat.sub 340282366920938463463374607431768211455 nb')
                  nb' (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))))
                (congrArg
                  (fun w : Nat => Nat.add w
                    (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)))
                  (Eq.trans
                    (Nat.add_comm (Nat.sub 340282366920938463463374607431768211455 nb') nb')
                    (nat_add_sub_cancel_of_le nb' 340282366920938463463374607431768211455 hb))))))
          (Eq.trans
            (congrArg (Nat.add (BitVec.toNat a))
              (Nat.add_comm 340282366920938463463374607431768211455
                (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))))
            (Eq.trans
              (Eq.symm (Nat.add_assoc (BitVec.toNat a)
                (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))
                340282366920938463463374607431768211455))
              (congrArg (fun w : Nat => Nat.add w 340282366920938463463374607431768211455)
                (toNat_hi_cancel a)))))

theorem wsub_n7 : forall (a : BitVec 128) (nb' : Nat),
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat a) ->
    Nat.le nb' 340282366920938463463374607431768211455 ->
    Nat.le (Nat.succ (Nat.add (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)) nb'))
           340282366920938463463374607431768211455 ->
    Eq (Nat.add
         (Nat.sub 340282366920938463463374607431768211455
           (Nat.succ (Nat.add (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)) nb')))
         340282366920938463463374607431768211456)
       (Nat.add (BitVec.toNat a) (Nat.sub 340282366920938463463374607431768211455 nb')) :=
    fun a nb' ha hb hq =>
      Nat.add_right_cancel
        (Nat.add
          (Nat.sub 340282366920938463463374607431768211455
            (Nat.succ (Nat.add (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)) nb')))
          340282366920938463463374607431768211456)
        (Nat.succ (Nat.add (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)) nb'))
        (Nat.add (BitVec.toNat a) (Nat.sub 340282366920938463463374607431768211455 nb'))
        (Eq.trans
          (wsub_n7_lhs
            (Nat.add (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)) nb')
            hq)
          (Eq.symm
            (congrArg Nat.succ (wsub_n7_rhs_inner a nb' ha hb))))

theorem wsub_hsWm1 : forall (b : BitVec 128) (nb' : Nat),
    Eq (BitVec.toNat b) (Nat.succ nb') ->
    Nat.le (Nat.succ nb') 340282366920938463463374607431768211455 :=
    fun b nb' hs =>
      @Eq.subst Nat (fun w : Nat => Nat.le w 340282366920938463463374607431768211455)
        (BitVec.toNat b) (Nat.succ nb') hs (bitvec_toNat_le_max128 b)

theorem wsub_nbWm1 : forall (b : BitVec 128) (nb' : Nat),
    Eq (BitVec.toNat b) (Nat.succ nb') ->
    Nat.le nb' 340282366920938463463374607431768211455 :=
    fun b nb' hs =>
      Nat.le_trans (Nat.le.step nb' nb' (Nat.le.refl nb')) (wsub_hsWm1 b nb' hs)

theorem wsub_J_le : forall (a b : BitVec 128) (nb' : Nat),
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat a) ->
    Nat.lt (BitVec.toNat b) 170141183460469231731687303715884105728 ->
    Eq (BitVec.toNat b) (Nat.succ nb') ->
    Nat.le (Nat.succ (Nat.add
             (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)) nb'))
           340282366920938463463374607431768211455 :=
    fun a b nb' ha hb hs =>
      Nat.le_trans
        (Nat.succ_le_succ
          (Nat.add_le_add
            (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))
            170141183460469231731687303715884105727
            nb'
            170141183460469231731687303715884105726
            (hi_j_le a ha)
            (nat_le_pred_of_succ_le nb' 170141183460469231731687303715884105727
              (Nat.le_of_succ_le_succ (Nat.succ nb') 170141183460469231731687303715884105727
                (@Eq.subst Nat
                  (fun w : Nat => Nat.lt w 170141183460469231731687303715884105728)
                  (BitVec.toNat b) (Nat.succ nb') hs hb)))))
        (Nat.le_of_ble_eq_true 340282366920938463463374607431768211454
          340282366920938463463374607431768211455 rfl)

theorem int_sub_ofNat_negSucc : forall (m n : Nat),
    Eq (Int.sub (Int.ofNat m) (Int.negSucc n))
       (Int.ofNat (Nat.add m (Nat.succ n))) :=
    fun m n => rfl

theorem int_sub_negSucc_negSucc : forall (m n : Nat),
    Eq (Int.sub (Int.negSucc m) (Int.negSucc n))
       (Int.subNatNat (Nat.succ n) (Nat.succ m)) :=
    fun m n => rfl

theorem int_sub_ofNat_ofNat_succ : forall (m n : Nat),
    Eq (Int.sub (Int.ofNat m) (Int.ofNat (Nat.succ n)))
       (Int.subNatNat m (Nat.succ n)) :=
    fun m n => rfl

theorem int_sub_negSucc_ofNat_succ : forall (m n : Nat),
    Eq (Int.sub (Int.negSucc m) (Int.ofNat (Nat.succ n)))
       (Int.negSucc (Nat.succ (Nat.add m n))) :=
    fun m n => rfl

theorem int_sub_zero_eq : forall (z : Int),
    Eq (Int.sub z (Int.ofNat 0)) z :=
    fun z => Int.add_zero z

theorem wsub_int_bhi_alo : forall (a b : BitVec 128),
    Nat.lt (BitVec.toNat a) 170141183460469231731687303715884105728 ->
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat b) ->
    Eq (Int.sub (toInt128 a) (toInt128 b))
       (Int.ofNat (Nat.add (BitVec.toNat a)
         (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))) :=
    fun a b ha hb =>
      Eq.trans
        (congrArg (fun z : Int => Int.sub z (toInt128 b)) (toInt128_toNat_lo a ha))
        (Eq.trans
          (congrArg (fun z : Int => Int.sub (Int.ofNat (BitVec.toNat a)) z)
            (toInt128_toNat_hi b hb))
          (int_sub_ofNat_negSucc (BitVec.toNat a)
            (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))

theorem wsub_int_bhi_ahi : forall (a b : BitVec 128),
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat a) ->
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat b) ->
    Eq (Int.sub (toInt128 a) (toInt128 b))
       (Int.subNatNat (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))
                      (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))) :=
    fun a b ha hb =>
      Eq.trans
        (congrArg (fun z : Int => Int.sub z (toInt128 b)) (toInt128_toNat_hi a ha))
        (Eq.trans
          (congrArg
            (fun z : Int => Int.sub
              (Int.negSucc (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))) z)
            (toInt128_toNat_hi b hb))
          (Eq.trans
            (int_sub_negSucc_negSucc
              (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))
              (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))
            (Int.subNatNat_succ_succ
              (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))
              (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)))))

theorem wsub_int_b0 : forall (a b : BitVec 128),
    Nat.lt (BitVec.toNat b) 170141183460469231731687303715884105728 ->
    Eq (BitVec.toNat b) Nat.zero ->
    Eq (Int.sub (toInt128 a) (toInt128 b)) (toInt128 a) :=
    fun a b hb hz =>
      Eq.trans
        (congrArg (Int.sub (toInt128 a)) (toInt128_toNat_lo b hb))
        (Eq.trans
          (congrArg (fun w : Nat => Int.sub (toInt128 a) (Int.ofNat w)) hz)
          (int_sub_zero_eq (toInt128 a)))

theorem wsub_int_bs_alo : forall (a b : BitVec 128) (nb' : Nat),
    Nat.lt (BitVec.toNat a) 170141183460469231731687303715884105728 ->
    Nat.lt (BitVec.toNat b) 170141183460469231731687303715884105728 ->
    Eq (BitVec.toNat b) (Nat.succ nb') ->
    Eq (Int.sub (toInt128 a) (toInt128 b))
       (Int.subNatNat (BitVec.toNat a) (Nat.succ nb')) :=
    fun a b nb' ha hb hs =>
      Eq.trans
        (congrArg (fun z : Int => Int.sub z (toInt128 b)) (toInt128_toNat_lo a ha))
        (Eq.trans
          (congrArg (fun z : Int => Int.sub (Int.ofNat (BitVec.toNat a)) z)
            (toInt128_toNat_lo b hb))
          (Eq.trans
            (congrArg
              (fun w : Nat => Int.sub (Int.ofNat (BitVec.toNat a)) (Int.ofNat w)) hs)
            (int_sub_ofNat_ofNat_succ (BitVec.toNat a) nb')))

theorem wsub_int_bs_ahi : forall (a b : BitVec 128) (nb' : Nat),
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat a) ->
    Nat.lt (BitVec.toNat b) 170141183460469231731687303715884105728 ->
    Eq (BitVec.toNat b) (Nat.succ nb') ->
    Eq (Int.sub (toInt128 a) (toInt128 b))
       (Int.negSucc (Nat.succ (Nat.add
         (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)) nb'))) :=
    fun a b nb' ha hb hs =>
      Eq.trans
        (congrArg (fun z : Int => Int.sub z (toInt128 b)) (toInt128_toNat_hi a ha))
        (Eq.trans
          (congrArg
            (fun z : Int => Int.sub
              (Int.negSucc (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))) z)
            (toInt128_toNat_lo b hb))
          (Eq.trans
            (congrArg
              (fun w : Nat => Int.sub
                (Int.negSucc (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)))
                (Int.ofNat w)) hs)
            (int_sub_negSucc_ofNat_succ
              (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)) nb')))

theorem wsub_bhi_alo : forall (a b : BitVec 128),
    Nat.lt (BitVec.toNat a) 170141183460469231731687303715884105728 ->
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat b) ->
    Eq (ofInt128 (Int.sub (toInt128 a) (toInt128 b)))
       (BitVec.ofNat 128 (Nat.sub (Nat.add (BitVec.toNat a) 340282366920938463463374607431768211456)
                                  (BitVec.toNat b))) :=
    fun a b ha hb =>
      Eq.trans
        (congrArg ofInt128 (wsub_int_bhi_alo a b ha hb))
        (Eq.trans
          (ofInt128_ofNat_eq (Nat.add (BitVec.toNat a)
            (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))))
          (bitvec128_ofNat_congr
            (Nat.add (BitVec.toNat a)
              (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))
            (Nat.sub (Nat.add (BitVec.toNat a) 340282366920938463463374607431768211456)
                     (BitVec.toNat b))
            (Eq.symm
              (congrArg (fun w : Nat => Nat.mod w 340282366920938463463374607431768211456)
                (wsub_T_bhi a b)))))

theorem wsub_bhi_ahi_le : forall (a b : BitVec 128),
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat a) ->
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat b) ->
    Nat.le (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))
           (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)) ->
    Eq (ofInt128 (Int.sub (toInt128 a) (toInt128 b)))
       (BitVec.ofNat 128 (Nat.sub (Nat.add (BitVec.toNat a) 340282366920938463463374607431768211456)
                                  (BitVec.toNat b))) :=
    fun a b ha hb hle =>
      Eq.trans
        (congrArg ofInt128 (wsub_int_bhi_ahi a b ha hb))
        (Eq.trans
          (congrArg ofInt128
            (int_subNatNat_of_le
              (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))
              (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))
              hle))
          (Eq.trans
            (ofInt128_ofNat_eq
              (Nat.sub (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))
                       (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))))
            (bitvec128_ofNat_congr
              (Nat.sub (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))
                       (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)))
              (Nat.sub (Nat.add (BitVec.toNat a) 340282366920938463463374607431768211456)
                       (BitVec.toNat b))
              (Eq.symm
                (Eq.trans
                  (congrArg (fun w : Nat => Nat.mod w 340282366920938463463374607431768211456)
                    (Eq.trans (wsub_T_bhi a b) (wsub_n2 a b ha hle)))
                  (nat_mod_shift
                    (Nat.sub (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))
                             (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)))
                    340282366920938463463374607431768211456 posW128))))))

theorem wsub_bhi_ahi_lt : forall (a b : BitVec 128),
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat a) ->
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat b) ->
    Nat.lt (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))
           (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)) ->
    Eq (ofInt128 (Int.sub (toInt128 a) (toInt128 b)))
       (BitVec.ofNat 128 (Nat.sub (Nat.add (BitVec.toNat a) 340282366920938463463374607431768211456)
                                  (BitVec.toNat b))) :=
    fun a b ha hb hlt =>
      Eq.trans
        (congrArg ofInt128 (wsub_int_bhi_ahi a b ha hb))
        (Eq.trans
          (congrArg ofInt128
            (int_subNatNat_of_lt
              (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))
              (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))
              hlt))
          (Eq.trans
            (ofInt128_negSucc_wide
              (Nat.sub (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))
                       (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))
              (Nat.le_trans
                (Nat.sub_le
                  (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))
                  (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))
                (Nat.le_trans (hi_j_le a ha) L1_le_Wm1)))
            (congrArg (fun w : Nat => BitVec.ofNat 128 w)
              (Eq.trans (wsub_n3 a b hlt) (Eq.symm (wsub_T_bhi a b))))))

theorem wsub_b0_alo : forall (a b : BitVec 128),
    Nat.lt (BitVec.toNat a) 170141183460469231731687303715884105728 ->
    Nat.lt (BitVec.toNat b) 170141183460469231731687303715884105728 ->
    Eq (BitVec.toNat b) Nat.zero ->
    Eq (ofInt128 (Int.sub (toInt128 a) (toInt128 b)))
       (BitVec.ofNat 128 (Nat.sub (Nat.add (BitVec.toNat a) 340282366920938463463374607431768211456)
                                  (BitVec.toNat b))) :=
    fun a b ha hb hz =>
      Eq.trans
        (congrArg ofInt128 (wsub_int_b0 a b hb hz))
        (Eq.trans
          (congrArg ofInt128 (toInt128_toNat_lo a ha))
          (Eq.trans
            (ofInt128_ofNat_eq (BitVec.toNat a))
            (bitvec128_ofNat_congr (BitVec.toNat a)
              (Nat.sub (Nat.add (BitVec.toNat a) 340282366920938463463374607431768211456)
                       (BitVec.toNat b))
              (Eq.symm
                (Eq.trans
                  (congrArg
                    (fun w : Nat => Nat.mod
                      (Nat.sub (Nat.add (BitVec.toNat a) 340282366920938463463374607431768211456) w)
                      340282366920938463463374607431768211456)
                    hz)
                  (nat_mod_shift (BitVec.toNat a) 340282366920938463463374607431768211456
                    posW128))))))

theorem wsub_b0_ahi : forall (a b : BitVec 128),
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat a) ->
    Nat.lt (BitVec.toNat b) 170141183460469231731687303715884105728 ->
    Eq (BitVec.toNat b) Nat.zero ->
    Eq (ofInt128 (Int.sub (toInt128 a) (toInt128 b)))
       (BitVec.ofNat 128 (Nat.sub (Nat.add (BitVec.toNat a) 340282366920938463463374607431768211456)
                                  (BitVec.toNat b))) :=
    fun a b ha hb hz =>
      Eq.trans
        (congrArg ofInt128 (wsub_int_b0 a b hb hz))
        (Eq.trans
          (congrArg ofInt128 (toInt128_toNat_hi a ha))
          (Eq.trans
            (ofInt128_negSucc_wide
              (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))
              (Nat.le_trans (hi_j_le a ha) L1_le_Wm1))
            (Eq.trans
              (congrArg (fun w : Nat => BitVec.ofNat 128 w)
                (nat_sub_sub_cancel 340282366920938463463374607431768211455 (BitVec.toNat a)
                  (bitvec_toNat_le_max128 a)))
              (bitvec128_ofNat_congr (BitVec.toNat a)
                (Nat.sub (Nat.add (BitVec.toNat a) 340282366920938463463374607431768211456)
                         (BitVec.toNat b))
                (Eq.symm
                  (Eq.trans
                    (congrArg
                      (fun w : Nat => Nat.mod
                        (Nat.sub (Nat.add (BitVec.toNat a) 340282366920938463463374607431768211456) w)
                        340282366920938463463374607431768211456)
                      hz)
                    (nat_mod_shift (BitVec.toNat a) 340282366920938463463374607431768211456
                      posW128)))))))

theorem wsub_bs_alo_le : forall (a b : BitVec 128) (nb' : Nat),
    Nat.lt (BitVec.toNat a) 170141183460469231731687303715884105728 ->
    Nat.lt (BitVec.toNat b) 170141183460469231731687303715884105728 ->
    Eq (BitVec.toNat b) (Nat.succ nb') ->
    Nat.le (Nat.succ nb') (BitVec.toNat a) ->
    Eq (ofInt128 (Int.sub (toInt128 a) (toInt128 b)))
       (BitVec.ofNat 128 (Nat.sub (Nat.add (BitVec.toNat a) 340282366920938463463374607431768211456)
                                  (BitVec.toNat b))) :=
    fun a b nb' ha hb hs hle =>
      Eq.trans
        (congrArg ofInt128 (wsub_int_bs_alo a b nb' ha hb hs))
        (Eq.trans
          (congrArg ofInt128 (int_subNatNat_of_le (BitVec.toNat a) (Nat.succ nb') hle))
          (Eq.trans
            (ofInt128_ofNat_eq (Nat.sub (BitVec.toNat a) (Nat.succ nb')))
            (bitvec128_ofNat_congr
              (Nat.sub (BitVec.toNat a) (Nat.succ nb'))
              (Nat.sub (Nat.add (BitVec.toNat a) 340282366920938463463374607431768211456)
                       (BitVec.toNat b))
              (Eq.symm
                (Eq.trans
                  (congrArg (fun w : Nat => Nat.mod w 340282366920938463463374607431768211456)
                    (Eq.trans (wsub_T_bs a b nb' hs)
                      (Eq.symm (wsub_n5 (BitVec.toNat a) nb' hle (wsub_nbWm1 b nb' hs)))))
                  (nat_mod_shift (Nat.sub (BitVec.toNat a) (Nat.succ nb'))
                    340282366920938463463374607431768211456 posW128))))))

theorem wsub_bs_alo_lt : forall (a b : BitVec 128) (nb' : Nat),
    Nat.lt (BitVec.toNat a) 170141183460469231731687303715884105728 ->
    Nat.lt (BitVec.toNat b) 170141183460469231731687303715884105728 ->
    Eq (BitVec.toNat b) (Nat.succ nb') ->
    Nat.lt (BitVec.toNat a) (Nat.succ nb') ->
    Eq (ofInt128 (Int.sub (toInt128 a) (toInt128 b)))
       (BitVec.ofNat 128 (Nat.sub (Nat.add (BitVec.toNat a) 340282366920938463463374607431768211456)
                                  (BitVec.toNat b))) :=
    fun a b nb' ha hb hs hlt =>
      Eq.trans
        (congrArg ofInt128 (wsub_int_bs_alo a b nb' ha hb hs))
        (Eq.trans
          (congrArg ofInt128 (int_subNatNat_of_lt (BitVec.toNat a) (Nat.succ nb') hlt))
          (Eq.trans
            (ofInt128_negSucc_wide
              (Nat.sub (Nat.succ nb') (Nat.succ (BitVec.toNat a)))
              (Nat.le_trans
                (Nat.sub_le (Nat.succ nb') (Nat.succ (BitVec.toNat a)))
                (wsub_hsWm1 b nb' hs)))
            (congrArg (fun w : Nat => BitVec.ofNat 128 w)
              (Eq.trans (wsub_n6 (BitVec.toNat a) nb' hlt (wsub_nbWm1 b nb' hs))
                (Eq.symm (wsub_T_bs a b nb' hs))))))

theorem wsub_bs_ahi : forall (a b : BitVec 128) (nb' : Nat),
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat a) ->
    Nat.lt (BitVec.toNat b) 170141183460469231731687303715884105728 ->
    Eq (BitVec.toNat b) (Nat.succ nb') ->
    Eq (ofInt128 (Int.sub (toInt128 a) (toInt128 b)))
       (BitVec.ofNat 128 (Nat.sub (Nat.add (BitVec.toNat a) 340282366920938463463374607431768211456)
                                  (BitVec.toNat b))) :=
    fun a b nb' ha hb hs =>
      Eq.trans
        (congrArg ofInt128 (wsub_int_bs_ahi a b nb' ha hb hs))
        (Eq.trans
          (ofInt128_negSucc_wide
            (Nat.succ (Nat.add
              (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)) nb'))
            (wsub_J_le a b nb' ha hb hs))
          (bitvec128_ofNat_congr
            (Nat.sub 340282366920938463463374607431768211455
              (Nat.succ (Nat.add
                (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)) nb')))
            (Nat.sub (Nat.add (BitVec.toNat a) 340282366920938463463374607431768211456)
                     (BitVec.toNat b))
            (Eq.symm
              (Eq.trans
                (congrArg (fun w : Nat => Nat.mod w 340282366920938463463374607431768211456)
                  (Eq.trans (wsub_T_bs a b nb' hs)
                    (Eq.symm (wsub_n7 a nb' ha (wsub_nbWm1 b nb' hs)
                      (wsub_J_le a b nb' ha hb hs)))))
                (nat_mod_shift
                  (Nat.sub 340282366920938463463374607431768211455
                    (Nat.succ (Nat.add
                      (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)) nb')))
                  340282366920938463463374607431768211456 posW128)))))

theorem ofInt128_sub_wrap : forall (a b : BitVec 128),
    Eq (ofInt128 (Int.sub (toInt128 a) (toInt128 b)))
       (BitVec.ofNat 128 (Nat.sub (Nat.add (BitVec.toNat a) 340282366920938463463374607431768211456)
                                  (BitVec.toNat b))) :=
    fun a b =>
      @Or.rec
        (Nat.le 170141183460469231731687303715884105728 (BitVec.toNat b))
        (Nat.lt (BitVec.toNat b) 170141183460469231731687303715884105728)
        (fun _ => Eq (ofInt128 (Int.sub (toInt128 a) (toInt128 b)))
                     (BitVec.ofNat 128 (Nat.sub (Nat.add (BitVec.toNat a) 340282366920938463463374607431768211456)
                                                (BitVec.toNat b))))
        (fun hb =>
          @Or.rec
            (Nat.le 170141183460469231731687303715884105728 (BitVec.toNat a))
            (Nat.lt (BitVec.toNat a) 170141183460469231731687303715884105728)
            (fun _ => Eq (ofInt128 (Int.sub (toInt128 a) (toInt128 b)))
                         (BitVec.ofNat 128 (Nat.sub (Nat.add (BitVec.toNat a) 340282366920938463463374607431768211456)
                                                    (BitVec.toNat b))))
            (fun ha =>
              @Or.rec
                (Nat.le (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))
                        (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))
                (Nat.lt (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))
                        (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)))
                (fun _ => Eq (ofInt128 (Int.sub (toInt128 a) (toInt128 b)))
                             (BitVec.ofNat 128 (Nat.sub (Nat.add (BitVec.toNat a) 340282366920938463463374607431768211456)
                                                        (BitVec.toNat b))))
                (fun hle => wsub_bhi_ahi_le a b ha hb hle)
                (fun hlt => wsub_bhi_ahi_lt a b ha hb hlt)
                (Nat.le_or_lt
                  (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))
                  (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))
            (fun ha => wsub_bhi_alo a b ha hb)
            (Nat.le_or_lt 170141183460469231731687303715884105728 (BitVec.toNat a)))
        (fun hb =>
          @Nat.rec
            (fun v : Nat => Eq (BitVec.toNat b) v ->
              Eq (ofInt128 (Int.sub (toInt128 a) (toInt128 b)))
                 (BitVec.ofNat 128 (Nat.sub (Nat.add (BitVec.toNat a) 340282366920938463463374607431768211456)
                                            (BitVec.toNat b))))
            (fun hz =>
              @Or.rec
                (Nat.le 170141183460469231731687303715884105728 (BitVec.toNat a))
                (Nat.lt (BitVec.toNat a) 170141183460469231731687303715884105728)
                (fun _ => Eq (ofInt128 (Int.sub (toInt128 a) (toInt128 b)))
                             (BitVec.ofNat 128 (Nat.sub (Nat.add (BitVec.toNat a) 340282366920938463463374607431768211456)
                                                        (BitVec.toNat b))))
                (fun ha => wsub_b0_ahi a b ha hb hz)
                (fun ha => wsub_b0_alo a b ha hb hz)
                (Nat.le_or_lt 170141183460469231731687303715884105728 (BitVec.toNat a)))
            (fun nb' _ hs =>
              @Or.rec
                (Nat.le 170141183460469231731687303715884105728 (BitVec.toNat a))
                (Nat.lt (BitVec.toNat a) 170141183460469231731687303715884105728)
                (fun _ => Eq (ofInt128 (Int.sub (toInt128 a) (toInt128 b)))
                             (BitVec.ofNat 128 (Nat.sub (Nat.add (BitVec.toNat a) 340282366920938463463374607431768211456)
                                                        (BitVec.toNat b))))
                (fun ha => wsub_bs_ahi a b nb' ha hb hs)
                (fun ha =>
                  @Or.rec
                    (Nat.le (Nat.succ nb') (BitVec.toNat a))
                    (Nat.lt (BitVec.toNat a) (Nat.succ nb'))
                    (fun _ => Eq (ofInt128 (Int.sub (toInt128 a) (toInt128 b)))
                                 (BitVec.ofNat 128 (Nat.sub (Nat.add (BitVec.toNat a) 340282366920938463463374607431768211456)
                                                            (BitVec.toNat b))))
                    (fun hle => wsub_bs_alo_le a b nb' ha hb hs hle)
                    (fun hlt => wsub_bs_alo_lt a b nb' ha hb hs hlt)
                    (Nat.le_or_lt (Nat.succ nb') (BitVec.toNat a)))
                (Nat.le_or_lt 170141183460469231731687303715884105728 (BitVec.toNat a)))
            (BitVec.toNat b)
            rfl)
        (Nat.le_or_lt 170141183460469231731687303715884105728 (BitVec.toNat b))

theorem int_mul_ofNat_ofNat : forall (m n : Nat),
    Eq (Int.mul (Int.ofNat m) (Int.ofNat n)) (Int.ofNat (Nat.mul m n)) :=
    fun m n => rfl

theorem int_mul_negSucc_negSucc : forall (m n : Nat),
    Eq (Int.mul (Int.negSucc m) (Int.negSucc n))
       (Int.ofNat (Nat.mul (Nat.succ m) (Nat.succ n))) :=
    fun m n => rfl

theorem int_mul_ofNat_succ_negSucc : forall (p q : Nat),
    Eq (Int.mul (Int.ofNat (Nat.succ p)) (Int.negSucc q))
       (Int.negSucc (Nat.add (Nat.mul (Nat.succ p) q) p)) :=
    fun p q => rfl

theorem int_mul_zero_negSucc : forall (q : Nat),
    Eq (Int.mul (Int.ofNat 0) (Int.negSucc q)) (Int.ofNat 0) :=
    fun q => congrArg Int.negOfNat (Nat.zero_mul (Nat.succ q))

theorem nat_add_left_swap : forall (a b c : Nat),
    Eq (Nat.add a (Nat.add b c)) (Nat.add b (Nat.add a c)) :=
    fun a b c =>
      Eq.trans (Eq.symm (Nat.add_assoc a b c))
        (Eq.trans (congrArg (fun w : Nat => Nat.add w c) (Nat.add_comm a b))
          (Nat.add_assoc b a c))

theorem wmul_cancelA : forall (v : BitVec 128),
    Eq (Nat.add (BitVec.toNat v)
         (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat v))))
       340282366920938463463374607431768211456 :=
    fun v => congrArg Nat.succ (toNat_hi_cancel v)

theorem wmul_hh_p1 : forall (a b : BitVec 128),
    Eq (Nat.add (Nat.mul (BitVec.toNat a) (BitVec.toNat b))
         (Nat.mul 340282366920938463463374607431768211456
           (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))))
       (Nat.add
         (Nat.mul (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)))
                  (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))
         (Nat.mul 340282366920938463463374607431768211456 (BitVec.toNat a))) :=
    fun a b =>
      Eq.trans
        (congrArg (Nat.add (Nat.mul (BitVec.toNat a) (BitVec.toNat b)))
          (congrArg
            (fun w : Nat => Nat.mul w
              (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))
            (Eq.symm (wmul_cancelA a))))
        (Eq.trans
          (congrArg (Nat.add (Nat.mul (BitVec.toNat a) (BitVec.toNat b)))
            (Nat.right_distrib (BitVec.toNat a)
              (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)))
              (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))))
          (Eq.trans
            (Eq.symm (Nat.add_assoc
              (Nat.mul (BitVec.toNat a) (BitVec.toNat b))
              (Nat.mul (BitVec.toNat a)
                (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))
              (Nat.mul (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)))
                (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))))
            (Eq.trans
              (congrArg
                (fun w : Nat => Nat.add w
                  (Nat.mul (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)))
                    (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))))
                (Eq.symm (Nat.left_distrib (BitVec.toNat a) (BitVec.toNat b)
                  (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))))
              (Eq.trans
                (congrArg
                  (fun w : Nat => Nat.add w
                    (Nat.mul (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)))
                      (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))))
                  (congrArg (Nat.mul (BitVec.toNat a)) (wmul_cancelA b)))
                (Eq.trans
                  (congrArg
                    (fun w : Nat => Nat.add w
                      (Nat.mul (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)))
                        (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))))
                    (Nat.mul_comm (BitVec.toNat a) 340282366920938463463374607431768211456))
                  (Nat.add_comm
                    (Nat.mul 340282366920938463463374607431768211456 (BitVec.toNat a))
                    (Nat.mul (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)))
                      (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))))))))

theorem wmul_p2_left : forall (p : Nat) (b : BitVec 128),
    Eq (Nat.add (Nat.mul (Nat.succ p) (BitVec.toNat b))
         (Nat.succ (Nat.add
           (Nat.mul (Nat.succ p) (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))
           p)))
       (Nat.add (Nat.mul 340282366920938463463374607431768211456 p)
                340282366920938463463374607431768211456) :=
    fun p b =>
      Eq.trans
        (Eq.symm (Nat.left_distrib (Nat.succ p) (BitVec.toNat b)
          (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))))
        (Eq.trans
          (congrArg (Nat.mul (Nat.succ p)) (wrap_lh_WEq b))
          (Nat.mul_comm (Nat.succ p) 340282366920938463463374607431768211456))

theorem wmul_p2_right : forall (p D : Nat),
    Nat.le D 340282366920938463463374607431768211455 ->
    Eq (Nat.add
         (Nat.add (Nat.sub 340282366920938463463374607431768211455 D)
                  (Nat.mul 340282366920938463463374607431768211456 p))
         (Nat.succ D))
       (Nat.add (Nat.mul 340282366920938463463374607431768211456 p)
                340282366920938463463374607431768211456) :=
    fun p D hD =>
      Eq.trans
        (nat_add_swap_right (Nat.sub 340282366920938463463374607431768211455 D)
          (Nat.mul 340282366920938463463374607431768211456 p) (Nat.succ D))
        (Eq.trans
          (congrArg
            (fun w : Nat => Nat.add w (Nat.mul 340282366920938463463374607431768211456 p))
            (congrArg Nat.succ
              (Eq.trans (Nat.add_comm (Nat.sub 340282366920938463463374607431768211455 D) D)
                (nat_add_sub_cancel_of_le D 340282366920938463463374607431768211455 hD))))
          (Nat.add_comm 340282366920938463463374607431768211456
            (Nat.mul 340282366920938463463374607431768211456 p)))

theorem wmul_p2 : forall (p : Nat) (b : BitVec 128),
    Nat.le (Nat.add
             (Nat.mul (Nat.succ p) (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))
             p)
           340282366920938463463374607431768211455 ->
    Eq (Nat.mul (Nat.succ p) (BitVec.toNat b))
       (Nat.add
         (Nat.sub 340282366920938463463374607431768211455
           (Nat.add
             (Nat.mul (Nat.succ p) (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))
             p))
         (Nat.mul 340282366920938463463374607431768211456 p)) :=
    fun p b hD =>
      Nat.add_right_cancel
        (Nat.mul (Nat.succ p) (BitVec.toNat b))
        (Nat.succ (Nat.add
          (Nat.mul (Nat.succ p) (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))
          p))
        (Nat.add
          (Nat.sub 340282366920938463463374607431768211455
            (Nat.add
              (Nat.mul (Nat.succ p) (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))
              p))
          (Nat.mul 340282366920938463463374607431768211456 p))
        (Eq.trans (wmul_p2_left p b)
          (Eq.symm (wmul_p2_right p
            (Nat.add
              (Nat.mul (Nat.succ p) (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))
              p)
            hD)))

theorem wmul_int_ll : forall (a b : BitVec 128),
    Nat.lt (BitVec.toNat a) 170141183460469231731687303715884105728 ->
    Nat.lt (BitVec.toNat b) 170141183460469231731687303715884105728 ->
    Eq (Int.mul (toInt128 a) (toInt128 b))
       (Int.ofNat (Nat.mul (BitVec.toNat a) (BitVec.toNat b))) :=
    fun a b ha hb =>
      Eq.trans
        (congrArg (fun z : Int => Int.mul z (toInt128 b)) (toInt128_toNat_lo a ha))
        (Eq.trans
          (congrArg (fun z : Int => Int.mul (Int.ofNat (BitVec.toNat a)) z)
            (toInt128_toNat_lo b hb))
          (int_mul_ofNat_ofNat (BitVec.toNat a) (BitVec.toNat b)))

theorem wmul_int_hh : forall (a b : BitVec 128),
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat a) ->
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat b) ->
    Eq (Int.mul (toInt128 a) (toInt128 b))
       (Int.ofNat (Nat.mul
         (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)))
         (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))) :=
    fun a b ha hb =>
      Eq.trans
        (congrArg (fun z : Int => Int.mul z (toInt128 b)) (toInt128_toNat_hi a ha))
        (Eq.trans
          (congrArg
            (fun z : Int => Int.mul
              (Int.negSucc (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))) z)
            (toInt128_toNat_hi b hb))
          (int_mul_negSucc_negSucc
            (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a))
            (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))

theorem wmul_int_lh0 : forall (a b : BitVec 128),
    Nat.lt (BitVec.toNat a) 170141183460469231731687303715884105728 ->
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat b) ->
    Eq (BitVec.toNat a) Nat.zero ->
    Eq (Int.mul (toInt128 a) (toInt128 b)) (Int.ofNat 0) :=
    fun a b ha hb hz =>
      Eq.trans
        (congrArg (fun z : Int => Int.mul z (toInt128 b)) (toInt128_toNat_lo a ha))
        (Eq.trans
          (congrArg (fun w : Nat => Int.mul (Int.ofNat w) (toInt128 b)) hz)
          (Eq.trans
            (congrArg (fun z : Int => Int.mul (Int.ofNat 0) z) (toInt128_toNat_hi b hb))
            (int_mul_zero_negSucc
              (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))))

theorem wmul_int_lhs : forall (a b : BitVec 128) (p : Nat),
    Nat.lt (BitVec.toNat a) 170141183460469231731687303715884105728 ->
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat b) ->
    Eq (BitVec.toNat a) (Nat.succ p) ->
    Eq (Int.mul (toInt128 a) (toInt128 b))
       (Int.negSucc (Nat.add
         (Nat.mul (Nat.succ p) (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))
         p)) :=
    fun a b p ha hb hs =>
      Eq.trans
        (congrArg (fun z : Int => Int.mul z (toInt128 b)) (toInt128_toNat_lo a ha))
        (Eq.trans
          (congrArg (fun w : Nat => Int.mul (Int.ofNat w) (toInt128 b)) hs)
          (Eq.trans
            (congrArg (fun z : Int => Int.mul (Int.ofNat (Nat.succ p)) z)
              (toInt128_toNat_hi b hb))
            (int_mul_ofNat_succ_negSucc p
              (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))))

theorem wmul_ll : forall (a b : BitVec 128),
    Nat.lt (BitVec.toNat a) 170141183460469231731687303715884105728 ->
    Nat.lt (BitVec.toNat b) 170141183460469231731687303715884105728 ->
    Eq (ofInt128 (Int.mul (toInt128 a) (toInt128 b)))
       (BitVec.ofNat 128 (Nat.mul (BitVec.toNat a) (BitVec.toNat b))) :=
    fun a b ha hb =>
      Eq.trans
        (congrArg ofInt128 (wmul_int_ll a b ha hb))
        (ofInt128_ofNat_eq (Nat.mul (BitVec.toNat a) (BitVec.toNat b)))

theorem wmul_hh : forall (a b : BitVec 128),
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat a) ->
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat b) ->
    Eq (ofInt128 (Int.mul (toInt128 a) (toInt128 b)))
       (BitVec.ofNat 128 (Nat.mul (BitVec.toNat a) (BitVec.toNat b))) :=
    fun a b ha hb =>
      Eq.trans
        (congrArg ofInt128 (wmul_int_hh a b ha hb))
        (Eq.trans
          (ofInt128_ofNat_eq (Nat.mul
            (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)))
            (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))))
          (bitvec128_ofNat_congr
            (Nat.mul
              (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)))
              (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))
            (Nat.mul (BitVec.toNat a) (BitVec.toNat b))
            (Eq.symm
              (Eq.trans
                (Eq.symm (nat_mod_mul_shift 340282366920938463463374607431768211456 posW128
                  (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))
                  (Nat.mul (BitVec.toNat a) (BitVec.toNat b))))
                (Eq.trans
                  (congrArg (fun w : Nat => Nat.mod w 340282366920938463463374607431768211456)
                    (wmul_hh_p1 a b))
                  (nat_mod_mul_shift 340282366920938463463374607431768211456 posW128
                    (BitVec.toNat a)
                    (Nat.mul
                      (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat a)))
                      (Nat.succ (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b))))))))))

theorem wmul_lh_zero : forall (a b : BitVec 128),
    Nat.lt (BitVec.toNat a) 170141183460469231731687303715884105728 ->
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat b) ->
    Eq (BitVec.toNat a) Nat.zero ->
    Eq (ofInt128 (Int.mul (toInt128 a) (toInt128 b)))
       (BitVec.ofNat 128 (Nat.mul (BitVec.toNat a) (BitVec.toNat b))) :=
    fun a b ha hb hz =>
      Eq.trans
        (congrArg ofInt128 (wmul_int_lh0 a b ha hb hz))
        (Eq.trans
          (ofInt128_ofNat_eq 0)
          (bitvec128_ofNat_congr 0 (Nat.mul (BitVec.toNat a) (BitVec.toNat b))
            (Eq.symm
              (congrArg (fun w : Nat => Nat.mod w 340282366920938463463374607431768211456)
                (Eq.trans
                  (congrArg (fun w : Nat => Nat.mul w (BitVec.toNat b)) hz)
                  (Nat.zero_mul (BitVec.toNat b)))))))

theorem wmul_lh_succ : forall (a b : BitVec 128) (p : Nat),
    Nat.lt (BitVec.toNat a) 170141183460469231731687303715884105728 ->
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat b) ->
    Eq (BitVec.toNat a) (Nat.succ p) ->
    Eq (fitsI128 (Int.mul (toInt128 a) (toInt128 b))) Bool.true ->
    Eq (ofInt128 (Int.mul (toInt128 a) (toInt128 b)))
       (BitVec.ofNat 128 (Nat.mul (BitVec.toNat a) (BitVec.toNat b))) :=
    fun a b p ha hb hs hfit =>
      Eq.trans
        (congrArg ofInt128 (wmul_int_lhs a b p ha hb hs))
        (Eq.trans
          (ofInt128_negSucc_wide
            (Nat.add
              (Nat.mul (Nat.succ p) (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))
              p)
            (Nat.le_trans
              (int_negSucc_le_inv
                (Nat.add
                  (Nat.mul (Nat.succ p) (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))
                  p)
                170141183460469231731687303715884105727
                (@Eq.subst Int (fun z : Int => Int.le i128Min z)
                  (Int.mul (toInt128 a) (toInt128 b))
                  (Int.negSucc (Nat.add
                    (Nat.mul (Nat.succ p) (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))
                    p))
                  (wmul_int_lhs a b p ha hb hs)
                  (fitsI128_lower (Int.mul (toInt128 a) (toInt128 b)) hfit)))
              L1_le_Wm1))
          (bitvec128_ofNat_congr
            (Nat.sub 340282366920938463463374607431768211455
              (Nat.add
                (Nat.mul (Nat.succ p) (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))
                p))
            (Nat.mul (BitVec.toNat a) (BitVec.toNat b))
            (Eq.symm
              (Eq.trans
                (congrArg (fun w : Nat => Nat.mod w 340282366920938463463374607431768211456)
                  (Eq.trans
                    (congrArg (fun w : Nat => Nat.mul w (BitVec.toNat b)) hs)
                    (wmul_p2 p b
                      (Nat.le_trans
                        (int_negSucc_le_inv
                          (Nat.add
                            (Nat.mul (Nat.succ p) (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))
                            p)
                          170141183460469231731687303715884105727
                          (@Eq.subst Int (fun z : Int => Int.le i128Min z)
                            (Int.mul (toInt128 a) (toInt128 b))
                            (Int.negSucc (Nat.add
                              (Nat.mul (Nat.succ p) (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))
                              p))
                            (wmul_int_lhs a b p ha hb hs)
                            (fitsI128_lower (Int.mul (toInt128 a) (toInt128 b)) hfit)))
                        L1_le_Wm1))))
                (nat_mod_mul_shift 340282366920938463463374607431768211456 posW128 p
                  (Nat.sub 340282366920938463463374607431768211455
                    (Nat.add
                      (Nat.mul (Nat.succ p) (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat b)))
                      p)))))))

theorem wmul_lh : forall (a b : BitVec 128),
    Nat.lt (BitVec.toNat a) 170141183460469231731687303715884105728 ->
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat b) ->
    Eq (fitsI128 (Int.mul (toInt128 a) (toInt128 b))) Bool.true ->
    Eq (ofInt128 (Int.mul (toInt128 a) (toInt128 b)))
       (BitVec.ofNat 128 (Nat.mul (BitVec.toNat a) (BitVec.toNat b))) :=
    fun a b ha hb hfit =>
      @Nat.rec
        (fun v : Nat => Eq (BitVec.toNat a) v ->
          Eq (ofInt128 (Int.mul (toInt128 a) (toInt128 b)))
             (BitVec.ofNat 128 (Nat.mul (BitVec.toNat a) (BitVec.toNat b))))
        (fun hz => wmul_lh_zero a b ha hb hz)
        (fun p _ hs => wmul_lh_succ a b p ha hb hs hfit)
        (BitVec.toNat a)
        rfl

theorem wmul_hl : forall (a b : BitVec 128),
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat a) ->
    Nat.lt (BitVec.toNat b) 170141183460469231731687303715884105728 ->
    Eq (fitsI128 (Int.mul (toInt128 a) (toInt128 b))) Bool.true ->
    Eq (ofInt128 (Int.mul (toInt128 a) (toInt128 b)))
       (BitVec.ofNat 128 (Nat.mul (BitVec.toNat a) (BitVec.toNat b))) :=
    fun a b ha hb hfit =>
      Eq.trans
        (congrArg ofInt128 (int_mul_comm (toInt128 a) (toInt128 b)))
        (Eq.trans
          (wmul_lh b a hb ha
            (Eq.trans
              (congrArg fitsI128 (int_mul_comm (toInt128 b) (toInt128 a)))
              hfit))
          (congrArg (fun w : Nat => BitVec.ofNat 128 w)
            (Nat.mul_comm (BitVec.toNat b) (BitVec.toNat a))))

theorem ofInt128_mul_wrap_of_fits : forall (a b : BitVec 128),
    Eq (fitsI128 (Int.mul (toInt128 a) (toInt128 b))) Bool.true ->
    Eq (ofInt128 (Int.mul (toInt128 a) (toInt128 b)))
       (BitVec.ofNat 128 (Nat.mul (BitVec.toNat a) (BitVec.toNat b))) :=
    fun a b hfit =>
      @Or.rec
        (Nat.le 170141183460469231731687303715884105728 (BitVec.toNat a))
        (Nat.lt (BitVec.toNat a) 170141183460469231731687303715884105728)
        (fun _ => Eq (ofInt128 (Int.mul (toInt128 a) (toInt128 b)))
                     (BitVec.ofNat 128 (Nat.mul (BitVec.toNat a) (BitVec.toNat b))))
        (fun ha =>
          @Or.rec
            (Nat.le 170141183460469231731687303715884105728 (BitVec.toNat b))
            (Nat.lt (BitVec.toNat b) 170141183460469231731687303715884105728)
            (fun _ => Eq (ofInt128 (Int.mul (toInt128 a) (toInt128 b)))
                         (BitVec.ofNat 128 (Nat.mul (BitVec.toNat a) (BitVec.toNat b))))
            (fun hb => wmul_hh a b ha hb)
            (fun hb => wmul_hl a b ha hb hfit)
            (Nat.le_or_lt 170141183460469231731687303715884105728 (BitVec.toNat b)))
        (fun ha =>
          @Or.rec
            (Nat.le 170141183460469231731687303715884105728 (BitVec.toNat b))
            (Nat.lt (BitVec.toNat b) 170141183460469231731687303715884105728)
            (fun _ => Eq (ofInt128 (Int.mul (toInt128 a) (toInt128 b)))
                         (BitVec.ofNat 128 (Nat.mul (BitVec.toNat a) (BitVec.toNat b))))
            (fun hb => wmul_lh a b ha hb hfit)
            (fun hb => wmul_ll a b ha hb)
            (Nat.le_or_lt 170141183460469231731687303715884105728 (BitVec.toNat b)))
        (Nat.le_or_lt 170141183460469231731687303715884105728 (BitVec.toNat a))

theorem checkedSub128_some_wrap : forall (a : BitVec 128) (b : BitVec 128),
    Eq (fitsI128 (Int.sub (toInt128 a) (toInt128 b))) Bool.true ->
    Eq (checkedSub128 a b)
       (some (BitVec.ofNat 128
         (Nat.sub (Nat.add (BitVec.toNat a) 340282366920938463463374607431768211456)
                  (BitVec.toNat b)))) :=
    fun a b h =>
      Eq.trans (checkedSub128_some a b h)
        (congrArg (fun v : BitVec 128 => some v) (ofInt128_sub_wrap a b))

theorem checkedMul128_some_wrap : forall (a : BitVec 128) (b : BitVec 128),
    Eq (fitsI128 (Int.mul (toInt128 a) (toInt128 b))) Bool.true ->
    Eq (checkedMul128 a b)
       (some (BitVec.ofNat 128 (Nat.mul (BitVec.toNat a) (BitVec.toNat b)))) :=
    fun a b h =>
      Eq.trans (checkedMul128_some a b h)
        (congrArg (fun v : BitVec 128 => some v) (ofInt128_mul_wrap_of_fits a b h))

def truncTo64 (v : BitVec 128) : BitVec 64 :=
    BitVec.ofNat 64 (BitVec.toNat v)

def narrowW (x : BitVec 128) : Option (BitVec 64) :=
    match guardFitsW x with
    | true  => some (truncTo64 x)
    | false => none

theorem narrowW_some_of_guard : forall (x : BitVec 128),
    Eq (guardFitsW x) Bool.true -> Eq (narrowW x) (some (truncTo64 x)) :=
    fun x h =>
      congrArg
        (fun c : Bool =>
          match c with
          | true  => some (truncTo64 x)
          | false => (none : Option (BitVec 64)))
        h

theorem narrowW_none_of_guard_false : forall (x : BitVec 128),
    Eq (guardFitsW x) Bool.false -> Eq (narrowW x) none :=
    fun x h =>
      congrArg
        (fun c : Bool =>
          match c with
          | true  => some (truncTo64 x)
          | false => (none : Option (BitVec 64)))
        h

theorem narrow_sub_lits :
    Eq (Nat.sub 340282366920938463463374607431768211455
                340282366920938463454151235394913435648)
       9223372036854775807 := rfl

theorem narrow_add_lits :
    Eq (Nat.add 340282366920938463444927863358058659840 18446744073709551615)
       340282366920938463463374607431768211455 := rfl

theorem narrow_mul_lits :
    Eq (Nat.mul 18446744073709551616 18446744073709551615)
       340282366920938463444927863358058659840 := rfl

theorem narrow_key_lo_lits :
    Eq (Nat.add 170141183460469231722463931679029329920
                170141183460469231731687303715884105728)
       340282366920938463454151235394913435648 := rfl

theorem narrow_pos64 : Nat.lt 0 18446744073709551616 :=
    Nat.le_of_ble_eq_true 1 18446744073709551616 rfl

theorem fitsI64_of_bounds : forall (A : Int),
    Int.le VeriPbCore.i64Min A -> Int.le A VeriPbCore.i64Max ->
    Eq (VeriPbCore.fitsI64 A) Bool.true :=
    fun A hlo hhi =>
      @Bool.rec
        (fun b : Bool =>
          Eq (Int.ble VeriPbCore.i64Min A) b ->
          Eq (match b with
              | true  => Int.ble A VeriPbCore.i64Max
              | false => Bool.false)
             Bool.true)
        (fun hb => @Bool.noConfusion
          (Eq (match Bool.false with
               | true  => Int.ble A VeriPbCore.i64Max
               | false => Bool.false)
              Bool.true)
          Bool.false Bool.true
          (Eq.trans (Eq.symm hb) (Int.ble_eq_true_of_le VeriPbCore.i64Min A hlo)))
        (fun _ => Int.ble_eq_true_of_le A VeriPbCore.i64Max hhi)
        (Int.ble VeriPbCore.i64Min A)
        rfl

theorem fitsI64_toInt128_of_guard : forall (x : BitVec 128),
    Eq (guardFitsW x) Bool.true ->
    Eq (VeriPbCore.fitsI64 (toInt128 x)) Bool.true :=
    fun x hg =>
      fitsI64_of_bounds (toInt128 x)
        (toInt128_in_i64_of_guard x hg).left
        (toInt128_in_i64_of_guard x hg).right

theorem narrow_key_lo_bound : forall (x : BitVec 128),
    Eq (guardFitsW x) Bool.true ->
    Nat.le 170141183460469231722463931679029329920 (key128 x) :=
    fun x hg =>
      @Eq.subst Nat (fun w : Nat => Nat.le w (key128 x))
        (key128 (BitVec.ofNat 128 340282366920938463454151235394913435648))
        170141183460469231722463931679029329920
        key128_min_pattern
        (guardFitsW_bounds x hg).left

theorem narrow_hi_sub_bound : forall (x : BitVec 128),
    Eq (guardFitsW x) Bool.true ->
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat x) ->
    Nat.le 170141183460469231722463931679029329920
           (Nat.sub (BitVec.toNat x) 170141183460469231731687303715884105728) :=
    fun x hg hp =>
      @Eq.subst Nat
        (fun w : Nat => Nat.le 170141183460469231722463931679029329920 w)
        (key128 x)
        (Nat.sub (BitVec.toNat x) 170141183460469231731687303715884105728)
        (xor_pivot128_of_ge (BitVec.toNat x) hp (bitvec_toNat_lt128 x))
        (narrow_key_lo_bound x hg)

theorem narrow_hi_toNat_ge : forall (x : BitVec 128),
    Eq (guardFitsW x) Bool.true ->
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat x) ->
    Nat.le 340282366920938463454151235394913435648 (BitVec.toNat x) :=
    fun x hg hp =>
      @Eq.subst Nat
        (fun w : Nat => Nat.le 340282366920938463454151235394913435648 w)
        (Nat.add (Nat.sub (BitVec.toNat x) 170141183460469231731687303715884105728)
                 170141183460469231731687303715884105728)
        (BitVec.toNat x)
        (Eq.trans
          (Nat.add_comm
            (Nat.sub (BitVec.toNat x) 170141183460469231731687303715884105728)
            170141183460469231731687303715884105728)
          (nat_add_sub_cancel_of_le 170141183460469231731687303715884105728
            (BitVec.toNat x) hp))
        (@Eq.subst Nat
          (fun w : Nat =>
            Nat.le w
              (Nat.add (Nat.sub (BitVec.toNat x) 170141183460469231731687303715884105728)
                       170141183460469231731687303715884105728))
          (Nat.add 170141183460469231722463931679029329920
                   170141183460469231731687303715884105728)
          340282366920938463454151235394913435648
          narrow_key_lo_lits
          (Nat.add_le_add_right 170141183460469231722463931679029329920
            (Nat.sub (BitVec.toNat x) 170141183460469231731687303715884105728)
            (narrow_hi_sub_bound x hg hp)
            170141183460469231731687303715884105728))

theorem narrow_hi_j_le : forall (x : BitVec 128),
    Nat.le 340282366920938463454151235394913435648 (BitVec.toNat x) ->
    Nat.le (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat x))
           9223372036854775807 :=
    fun x h =>
      @Eq.subst Nat
        (fun w : Nat =>
          Nat.le (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat x)) w)
        (Nat.sub 340282366920938463463374607431768211455
                 340282366920938463454151235394913435648)
        9223372036854775807
        narrow_sub_lits
        (Nat.sub_le_sub_left 340282366920938463463374607431768211455
          340282366920938463454151235394913435648 (BitVec.toNat x) h)

theorem narrow_hi_j_le64 : forall (x : BitVec 128),
    Nat.le 340282366920938463454151235394913435648 (BitVec.toNat x) ->
    Nat.le (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat x))
           18446744073709551615 :=
    fun x h =>
      Nat.le_trans
        (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat x))
        9223372036854775807 18446744073709551615
        (narrow_hi_j_le x h) rt64_le_lits

theorem narrow_hi_payload : forall (x : BitVec 128),
    Nat.le 340282366920938463454151235394913435648 (BitVec.toNat x) ->
    Eq (Nat.add
          (Nat.sub 18446744073709551615
            (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat x)))
          340282366920938463444927863358058659840)
       (BitVec.toNat x) :=
    fun x h =>
      Eq.trans
        (Nat.add_comm
          (Nat.sub 18446744073709551615
            (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat x)))
          340282366920938463444927863358058659840)
        (Eq.trans
          (Eq.symm
            (nat_add_sub_assoc 340282366920938463444927863358058659840
              18446744073709551615
              (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat x))
              (narrow_hi_j_le64 x h)))
          (Eq.trans
            (congrArg
              (fun w : Nat =>
                Nat.sub w (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat x)))
              narrow_add_lits)
            (nat_sub_sub_cancel 340282366920938463463374607431768211455 (BitVec.toNat x)
              (bitvec_toNat_le_max128 x))))

theorem narrow_hi_mod : forall (x : BitVec 128),
    Nat.le 340282366920938463454151235394913435648 (BitVec.toNat x) ->
    Eq (Nat.mod
          (Nat.sub 18446744073709551615
            (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat x)))
          18446744073709551616)
       (Nat.mod (BitVec.toNat x) 18446744073709551616) :=
    fun x h =>
      Eq.symm
        (Eq.trans
          (congrArg (fun w : Nat => Nat.mod w 18446744073709551616)
            (Eq.symm (narrow_hi_payload x h)))
          (Eq.trans
            (congrArg
              (fun w : Nat =>
                Nat.mod
                  (Nat.add
                    (Nat.sub 18446744073709551615
                      (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat x)))
                    w)
                  18446744073709551616)
              (Eq.symm narrow_mul_lits))
            (nat_mod_mul_shift 18446744073709551616 narrow_pos64 18446744073709551615
              (Nat.sub 18446744073709551615
                (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat x))))))

theorem ofInt64_toInt128_lo : forall (x : BitVec 128),
    Nat.lt (BitVec.toNat x) 170141183460469231731687303715884105728 ->
    Eq (ofInt64 (toInt128 x)) (truncTo64 x) :=
    fun x h =>
      Eq.trans
        (congrArg ofInt64 (toInt128_toNat_lo x h))
        (ofInt64_ofNat_eq (BitVec.toNat x))

theorem ofInt64_toInt128_hi : forall (x : BitVec 128),
    Eq (guardFitsW x) Bool.true ->
    Nat.le 170141183460469231731687303715884105728 (BitVec.toNat x) ->
    Eq (ofInt64 (toInt128 x)) (truncTo64 x) :=
    fun x hg hp =>
      Eq.trans
        (congrArg ofInt64 (toInt128_toNat_hi x hp))
        (Eq.trans
          (ofInt64_negSucc_eq
            (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat x))
            (narrow_hi_j_le x (narrow_hi_toNat_ge x hg hp)))
          (bitvec64_ofNat_congr
            (Nat.sub 18446744073709551615
              (Nat.sub 340282366920938463463374607431768211455 (BitVec.toNat x)))
            (BitVec.toNat x)
            (narrow_hi_mod x (narrow_hi_toNat_ge x hg hp))))

theorem ofInt64_toInt128_eq_trunc : forall (x : BitVec 128),
    Eq (guardFitsW x) Bool.true ->
    Eq (ofInt64 (toInt128 x)) (truncTo64 x) :=
    fun x hg =>
      @Or.rec
        (Nat.le 170141183460469231731687303715884105728 (BitVec.toNat x))
        (Nat.lt (BitVec.toNat x) 170141183460469231731687303715884105728)
        (fun _ => Eq (ofInt64 (toInt128 x)) (truncTo64 x))
        (fun hp => ofInt64_toInt128_hi x hg hp)
        (fun hp => ofInt64_toInt128_lo x hp)
        (Nat.le_or_lt 170141183460469231731687303715884105728 (BitVec.toNat x))

theorem narrowW_value_preserving : forall (x : BitVec 128),
    Eq (guardFitsW x) Bool.true ->
    Eq (toInt64 (truncTo64 x)) (toInt128 x) :=
    fun x hg =>
      Eq.trans
        (congrArg toInt64 (Eq.symm (ofInt64_toInt128_eq_trunc x hg)))
        (toInt64_ofInt64 (toInt128 x) (fitsI64_toInt128_of_guard x hg))

theorem narrowW_some_value : forall (x : BitVec 128),
    Eq (guardFitsW x) Bool.true ->
    Eq (narrowW x) (some (ofInt64 (toInt128 x))) :=
    fun x hg =>
      Eq.trans
        (narrowW_some_of_guard x hg)
        (congrArg (fun v : BitVec 64 => some v)
          (Eq.symm (ofInt64_toInt128_eq_trunc x hg)))

def narrowWide (x : BitVec 128) : Option (BitVec 64) :=
    match VeriPbCore.fitsI64 (toInt128 x) with
    | true  => some (truncTo64 x)
    | false => none

theorem narrowWide_char : forall (x : BitVec 128),
    Eq (narrowWide x)
       (match VeriPbCore.fitsI64 (toInt128 x) with
        | true  => some (truncTo64 x)
        | false => none) :=
    fun x => rfl

def isSomeB64 (o : Option (BitVec 64)) : Bool :=
    match o with
    | none   => false
    | some _ => true

theorem narrowWide_some_of_fits : forall (x : BitVec 128),
    Eq (VeriPbCore.fitsI64 (toInt128 x)) Bool.true ->
    Eq (narrowWide x) (some (truncTo64 x)) :=
    fun x h =>
      congrArg
        (fun c : Bool =>
          match c with
          | true  => some (truncTo64 x)
          | false => (none : Option (BitVec 64)))
        h

theorem narrowWide_none_of_fits_false : forall (x : BitVec 128),
    Eq (VeriPbCore.fitsI64 (toInt128 x)) Bool.false ->
    Eq (narrowWide x) none :=
    fun x h =>
      congrArg
        (fun c : Bool =>
          match c with
          | true  => some (truncTo64 x)
          | false => (none : Option (BitVec 64)))
        h

theorem narrowWide_some_of_guard : forall (x : BitVec 128),
    Eq (guardFitsW x) Bool.true ->
    Eq (narrowWide x) (some (truncTo64 x)) :=
    fun x hg =>
      narrowWide_some_of_fits x (fitsI64_toInt128_of_guard x hg)

theorem narrowWide_isSome_of_fits : forall (x : BitVec 128),
    Eq (guardFitsW x) Bool.true -> Not (Eq (narrowWide x) none) :=
    fun x hg hn =>
      Bool.noConfusion
        (congrArg isSomeB64
          (Eq.trans (Eq.symm (narrowWide_some_of_guard x hg)) hn))

theorem narrowWide_some_value : forall (x : BitVec 128),
    Eq (guardFitsW x) Bool.true ->
    Eq (narrowWide x) (some (ofInt64 (toInt128 x))) :=
    fun x hg =>
      Eq.trans
        (narrowWide_some_of_guard x hg)
        (congrArg (fun v : BitVec 64 => some v)
          (Eq.symm (ofInt64_toInt128_eq_trunc x hg)))

theorem narrowWide_value_preserving : forall (x : BitVec 128),
    Eq (guardFitsW x) Bool.true ->
    Eq (toInt64 (truncTo64 x)) (toInt128 x) :=
    narrowW_value_preserving

theorem capcoeff_i128_min_full : forall (degree : BitVec 128) (coeff : BitVec 128),
    And (And (Nat.le (key128 (if Nat.le (key128 coeff) (key128 degree) then coeff else degree))
                     (key128 coeff))
             (Nat.le (key128 (if Nat.le (key128 coeff) (key128 degree) then coeff else degree))
                     (key128 degree)))
        (Or (Nat.le (key128 degree)
                    (key128 (if Nat.le (key128 coeff) (key128 degree) then coeff else degree)))
            (Nat.le (key128 coeff)
                    (key128 (if Nat.le (key128 coeff) (key128 degree) then coeff else degree)))) :=
    fun degree coeff => Decidable.casesOn
        (motive := fun (h : Decidable (Nat.le (key128 coeff) (key128 degree))) =>
            And (And (Nat.le (key128 (Decidable.casesOn (motive := fun _ => BitVec 128)
                        h (fun _ => degree) (fun _ => coeff))) (key128 coeff))
                     (Nat.le (key128 (Decidable.casesOn (motive := fun _ => BitVec 128)
                        h (fun _ => degree) (fun _ => coeff))) (key128 degree)))
                (Or (Nat.le (key128 degree) (key128 (Decidable.casesOn (motive := fun _ => BitVec 128)
                        h (fun _ => degree) (fun _ => coeff))))
                    (Nat.le (key128 coeff) (key128 (Decidable.casesOn (motive := fun _ => BitVec 128)
                        h (fun _ => degree) (fun _ => coeff))))))
        (Nat.decLe (key128 coeff) (key128 degree))
        (fun h => And.intro
            (And.intro (Nat.le_of_lt (Iff.mp (Nat.not_le (key128 coeff) (key128 degree)) h))
                       (Nat.le.refl (key128 degree)))
            (@Or.inl (Nat.le (key128 degree) (key128 degree))
                     (Nat.le (key128 coeff) (key128 degree)) (Nat.le.refl (key128 degree))))
        (fun h => And.intro
            (And.intro (Nat.le.refl (key128 coeff)) h)
            (@Or.inr (Nat.le (key128 degree) (key128 coeff))
                     (Nat.le (key128 coeff) (key128 coeff)) (Nat.le.refl (key128 coeff))))

theorem bitvec_toNat_lt64 : forall (v : BitVec 64),
    Nat.lt (BitVec.toNat v) 18446744073709551616 :=
    fun v => Fin.isLt (Nat.pow 2 64) (BitVec.toFin v)

theorem key64_raw_lo : forall (v : BitVec 64),
    Nat.lt (BitVec.toNat v) 9223372036854775808 ->
    Eq (key64 v) (Nat.add (BitVec.toNat v) 9223372036854775808) :=
    fun v h => xor_pivot64_of_lt (BitVec.toNat v) h

theorem key64_raw_hi : forall (v : BitVec 64),
    Nat.le 9223372036854775808 (BitVec.toNat v) ->
    Eq (key64 v) (Nat.sub (BitVec.toNat v) 9223372036854775808) :=
    fun v h => xor_pivot64_of_ge (BitVec.toNat v) h (bitvec_toNat_lt64 v)

theorem key64_lt64 : forall (v : BitVec 64),
    Nat.lt (key64 v) 18446744073709551616 :=
    fun v => Decidable.casesOn
        (motive := fun (_ : Decidable (Nat.le 9223372036854775808 (BitVec.toNat v))) =>
            Nat.lt (key64 v) 18446744073709551616)
        (Nat.decLe 9223372036854775808 (BitVec.toNat v))
        (fun hn =>
          @Eq.subst Nat (fun w : Nat => Nat.lt w 18446744073709551616)
            (Nat.add (BitVec.toNat v) 9223372036854775808) (key64 v)
            (Eq.symm (key64_raw_lo v
              (Iff.mp (Nat.not_le 9223372036854775808 (BitVec.toNat v)) hn)))
            (Nat.add_lt_add_right (BitVec.toNat v) 9223372036854775808
              (Iff.mp (Nat.not_le 9223372036854775808 (BitVec.toNat v)) hn)
              9223372036854775808))
        (fun hp =>
          @Eq.subst Nat (fun w : Nat => Nat.lt w 18446744073709551616)
            (Nat.sub (BitVec.toNat v) 9223372036854775808) (key64 v)
            (Eq.symm (key64_raw_hi v hp))
            (lt64_of_lt63 (Nat.sub (BitVec.toNat v) 9223372036854775808)
              (nat_sub_lt_of_lt_add (BitVec.toNat v)
                9223372036854775808 9223372036854775808
                (bitvec_toNat_lt64 v) hp)))

theorem key64_le_max64 : forall (v : BitVec 64),
    Nat.le (key64 v) 18446744073709551615 :=
    fun v => nat_le_pred_of_succ_le (key64 v) 18446744073709551616 (key64_lt64 v)

theorem toInt64_in_i64 : forall (v : BitVec 64),
    And (Int.le VeriPbCore.i64Min (toInt64 v)) (Int.le (toInt64 v) VeriPbCore.i64Max) :=
    fun v =>
      @Bool.rec
        (fun b : Bool =>
          (Eq (Nat.ble 9223372036854775808 (key64 v)) b) ->
          And (Int.le VeriPbCore.i64Min (match b with
                | true  => Int.ofNat (Nat.sub (key64 v) 9223372036854775808)
                | false => Int.negSucc (Nat.sub 9223372036854775807 (key64 v))))
              (Int.le (match b with
                | true  => Int.ofNat (Nat.sub (key64 v) 9223372036854775808)
                | false => Int.negSucc (Nat.sub 9223372036854775807 (key64 v)))
                VeriPbCore.i64Max))
        (fun _ => And.intro
          (VeriPbCore.int_neg_le_neg
            (Int.ofNat (Nat.succ (Nat.sub 9223372036854775807 (key64 v))))
            (Int.ofNat 9223372036854775808)
            (VeriPbCore.int_ofNat_le_ofNat
              (Nat.succ (Nat.sub 9223372036854775807 (key64 v)))
              9223372036854775808
              (Nat.succ_le_succ (Nat.sub_le 9223372036854775807 (key64 v)))))
          (Int.le_of_ble_eq_true
            (Int.negSucc (Nat.sub 9223372036854775807 (key64 v)))
            VeriPbCore.i64Max rfl))
        (fun _ => And.intro
          (Int.le_of_ble_eq_true VeriPbCore.i64Min
            (Int.ofNat (Nat.sub (key64 v) 9223372036854775808)) rfl)
          (VeriPbCore.int_ofNat_le_ofNat
            (Nat.sub (key64 v) 9223372036854775808)
            9223372036854775807
            (Nat.sub_le_sub_right (key64 v) 18446744073709551615
              9223372036854775808 (key64_le_max64 v))))
        (Nat.ble 9223372036854775808 (key64 v))
        rfl

theorem int_i64Min_le_zero : Int.le VeriPbCore.i64Min (Int.ofNat 0) :=
    VeriPbCore.int_neg_le_neg (Int.ofNat 0) (Int.ofNat 9223372036854775808)
      (VeriPbCore.int_ofNat_le_ofNat 0 9223372036854775808
        (Nat.zero_le 9223372036854775808))

theorem int_zero_le_i64Max : Int.le (Int.ofNat 0) VeriPbCore.i64Max :=
    VeriPbCore.int_ofNat_le_ofNat 0 9223372036854775807
      (Nat.zero_le 9223372036854775807)

theorem fitsI128_toInt64 : forall (m : BitVec 64),
    Eq (fitsI128 (toInt64 m)) Bool.true :=
    fun m =>
      @Eq.subst Int (fun z : Int => Eq (fitsI128 z) Bool.true)
        (Int.add (toInt64 m) (Int.ofNat 0)) (toInt64 m)
        (Int.add_zero (toInt64 m))
        (fitsI128_add_of_bounds (toInt64 m) (Int.ofNat 0)
          (toInt64_in_i64 m).left (toInt64_in_i64 m).right
          int_i64Min_le_zero int_zero_le_i64Max)

def sextWide (v : BitVec 64) : BitVec 128 := ofInt128 (toInt64 v)

def eqOkW (m : BitVec 64) (t : BitVec 128) : Bool :=
    Decidable.decide (Eq (BitVec.toNat (sextWide m)) (BitVec.toNat t))
                     (Nat.decEq (BitVec.toNat (sextWide m)) (BitVec.toNat t))

theorem nat_eq_of_decEq_true : forall (a : Nat) (bq : Nat),
    Eq (Decidable.decide (Eq a bq) (Nat.decEq a bq)) Bool.true -> Eq a bq :=
    fun a bq h => Decidable.casesOn
        (motive := fun (d : Decidable (Eq a bq)) =>
            Eq (Decidable.decide (Eq a bq) d) Bool.true -> Eq a bq)
        (Nat.decEq a bq)
        (fun _ => fun hh => @Bool.noConfusion (Eq a bq) Bool.false Bool.true hh)
        (fun hp => fun _ => hp)
        h

theorem eqOkW_toNat_eq : forall (m : BitVec 64) (t : BitVec 128),
    Eq (eqOkW m t) Bool.true ->
    Eq (BitVec.toNat (sextWide m)) (BitVec.toNat t) :=
    fun m t h =>
      nat_eq_of_decEq_true (BitVec.toNat (sextWide m)) (BitVec.toNat t) h

theorem sextWide_eq_of_eqOkW : forall (m : BitVec 64) (t : BitVec 128),
    Eq (eqOkW m t) Bool.true -> Eq (sextWide m) t :=
    fun m t h =>
      bitvec_eq_of_toNat_eq 128 (sextWide m) t (eqOkW_toNat_eq m t h)

theorem toInt128_sextWide : forall (m : BitVec 64),
    Eq (toInt128 (sextWide m)) (toInt64 m) :=
    fun m => toInt128_ofInt128 (toInt64 m) (fitsI128_toInt64 m)

theorem eq_of_eqOkW : forall (m : BitVec 64) (t : BitVec 128),
    Eq (eqOkW m t) Bool.true -> Eq (toInt64 m) (toInt128 t) :=
    fun m t h =>
      Eq.trans
        (Eq.symm (toInt128_sextWide m))
        (congrArg toInt128 (sextWide_eq_of_eqOkW m t h))

theorem eqOkB_self : forall (x : Int), Eq (VeriPbCore.eqOkB x x) Bool.true :=
    fun x =>
      @Bool.rec
        (fun b : Bool =>
          Eq (Int.ble x x) b ->
          Eq (match b with
              | true  => Int.ble x x
              | false => Bool.false)
             Bool.true)
        (fun hb => @Bool.noConfusion
          (Eq (match Bool.false with
               | true  => Int.ble x x
               | false => Bool.false)
              Bool.true)
          Bool.false Bool.true
          (Eq.trans (Eq.symm hb) (Int.ble_eq_true_of_le x x (Int.le_refl x))))
        (fun _ => Int.ble_eq_true_of_le x x (Int.le_refl x))
        (Int.ble x x)
        rfl

theorem eqOkB_of_eq : forall (x y : Int),
    Eq x y -> Eq (VeriPbCore.eqOkB x y) Bool.true :=
    fun x y h =>
      @Eq.rec Int x (fun z _ => Eq (VeriPbCore.eqOkB x z) Bool.true)
        (eqOkB_self x) y h

theorem entails_add_machine :
    forall (F : List VeriPbCore.Constraint) (c1 c2 : VeriPbCore.Constraint)
           (m : BitVec 64) (t : BitVec 128),
    Eq (toInt128 t) (c1.degree + c2.degree) ->
    Eq (eqOkW m t) Bool.true ->
    Eq (guardFitsW t) Bool.true ->
    VeriPbCore.Entails F c1 -> VeriPbCore.Entails F c2 ->
    And (VeriPbCore.InI64 (toInt64 m))
        (VeriPbCore.Entails F
          { terms := c1.terms ++ c2.terms, degree := toInt64 m }) :=
    fun F c1 c2 m t hsum hs hfit h1 h2 =>
      VeriPbCore.entails_add_checked F c1 c2 (toInt64 m)
        (eqOkB_of_eq (toInt64 m) (c1.degree + c2.degree)
          (Eq.trans (eq_of_eqOkW m t hs) hsum))
        (Eq.trans (congrArg VeriPbCore.fitsI64 (eq_of_eqOkW m t hs))
                  (fitsI64_toInt128_of_guard t hfit))
        h1 h2

theorem entails_add_narrowed :
    forall (F : List VeriPbCore.Constraint) (c1 c2 : VeriPbCore.Constraint)
           (t : BitVec 128),
    Eq (toInt128 t) (c1.degree + c2.degree) ->
    Eq (guardFitsW t) Bool.true ->
    VeriPbCore.Entails F c1 -> VeriPbCore.Entails F c2 ->
    And (VeriPbCore.InI64 (toInt64 (truncTo64 t)))
        (VeriPbCore.Entails F
          { terms := c1.terms ++ c2.terms, degree := toInt64 (truncTo64 t) }) :=
    fun F c1 c2 t hsum hfit h1 h2 =>
      VeriPbCore.entails_add_checked F c1 c2 (toInt64 (truncTo64 t))
        (eqOkB_of_eq (toInt64 (truncTo64 t)) (c1.degree + c2.degree)
          (Eq.trans (narrowWide_value_preserving t hfit) hsum))
        (Eq.trans (congrArg VeriPbCore.fitsI64
                    (narrowWide_value_preserving t hfit))
                  (fitsI64_toInt128_of_guard t hfit))
        h1 h2

theorem entails_weaken_narrowed :
    forall (F : List VeriPbCore.Constraint) (c : VeriPbCore.Constraint)
           (w : Int) (rt : BitVec 128),
    Eq (toInt128 rt + w) c.degree ->
    Int.le 0 w ->
    Eq (guardFitsW rt) Bool.true ->
    VeriPbCore.Entails F c ->
    And (VeriPbCore.InI64 (toInt64 (truncTo64 rt)))
        (VeriPbCore.Entails F
          (VeriPbCore.weakenC (toInt64 (truncTo64 rt)) c)) :=
    fun F c w rt hsum hw hfit h =>
      VeriPbCore.entails_weaken_checked F c w (toInt64 (truncTo64 rt))
        (eqOkB_of_eq (toInt64 (truncTo64 rt) + w) c.degree
          (Eq.trans
            (congrArg (fun z : Int => z + w)
              (narrowWide_value_preserving rt hfit))
            hsum))
        hw
        (Eq.trans (congrArg VeriPbCore.fitsI64
                    (narrowWide_value_preserving rt hfit))
                  (fitsI64_toInt128_of_guard rt hfit))
        h

theorem wideAdd_denotes_exact_sum : forall (a : BitVec 128) (b : BitVec 128),
    Eq (guardFitsW a) Bool.true -> Eq (guardFitsW b) Bool.true ->
    Eq (toInt128 (BitVec.ofNat 128 (Nat.add (BitVec.toNat a) (BitVec.toNat b))))
       (Int.add (toInt128 a) (toInt128 b)) :=
    fun a b hga hgb =>
      Eq.trans
        (Eq.symm
          (congrArg toInt128 (ofInt128_add_wrap a b)))
        (toInt128_ofInt128 (Int.add (toInt128 a) (toInt128 b))
          (fitsI128_add_of_bounds (toInt128 a) (toInt128 b)
            (toInt128_in_i64_of_guard a hga).left
            (toInt128_in_i64_of_guard a hga).right
            (toInt128_in_i64_of_guard b hgb).left
            (toInt128_in_i64_of_guard b hgb).right))

theorem entails_add_from_guards :
    forall (F : List VeriPbCore.Constraint) (c1 c2 : VeriPbCore.Constraint)
           (a : BitVec 128) (b : BitVec 128),
    Eq (toInt128 a) c1.degree ->
    Eq (toInt128 b) c2.degree ->
    Eq (guardFitsW a) Bool.true ->
    Eq (guardFitsW b) Bool.true ->
    Eq (guardFitsW (BitVec.ofNat 128 (Nat.add (BitVec.toNat a) (BitVec.toNat b))))
       Bool.true ->
    VeriPbCore.Entails F c1 -> VeriPbCore.Entails F c2 ->
    And (VeriPbCore.InI64
          (toInt64 (truncTo64
            (BitVec.ofNat 128 (Nat.add (BitVec.toNat a) (BitVec.toNat b))))))
        (VeriPbCore.Entails F
          { terms := c1.terms ++ c2.terms,
            degree := toInt64 (truncTo64
              (BitVec.ofNat 128 (Nat.add (BitVec.toNat a) (BitVec.toNat b)))) }) :=
    fun F c1 c2 a b hda hdb hga hgb hgt h1 h2 =>
      entails_add_narrowed F c1 c2
        (BitVec.ofNat 128 (Nat.add (BitVec.toNat a) (BitVec.toNat b)))
        (Eq.trans
          (wideAdd_denotes_exact_sum a b hga hgb)
          (Eq.trans
            (congrArg (fun z : Int => Int.add z (toInt128 b)) hda)
            (congrArg (fun z : Int => Int.add c1.degree z) hdb)))
        hgt h1 h2

theorem wideSub_denotes_exact_difference : forall (a : BitVec 128) (b : BitVec 128),
    Eq (guardFitsW a) Bool.true -> Eq (guardFitsW b) Bool.true ->
    Eq (toInt128 (BitVec.ofNat 128
          (Nat.sub (Nat.add (BitVec.toNat a) 340282366920938463463374607431768211456)
                   (BitVec.toNat b))))
       (Int.sub (toInt128 a) (toInt128 b)) :=
    fun a b hga hgb =>
      Eq.trans
        (Eq.symm (congrArg toInt128 (ofInt128_sub_wrap a b)))
        (toInt128_ofInt128 (Int.sub (toInt128 a) (toInt128 b))
          (fitsI128_sub_of_bounds (toInt128 a) (toInt128 b)
            (toInt128_in_i64_of_guard a hga).left
            (toInt128_in_i64_of_guard a hga).right
            (toInt128_in_i64_of_guard b hgb).left
            (toInt128_in_i64_of_guard b hgb).right))

theorem entails_weaken_from_guards :
    forall (F : List VeriPbCore.Constraint) (c : VeriPbCore.Constraint)
           (d : BitVec 128) (wv : BitVec 128),
    Eq (toInt128 d) c.degree ->
    Int.le 0 (toInt128 wv) ->
    Eq (guardFitsW d) Bool.true ->
    Eq (guardFitsW wv) Bool.true ->
    Eq (guardFitsW (BitVec.ofNat 128
          (Nat.sub (Nat.add (BitVec.toNat d) 340282366920938463463374607431768211456)
                   (BitVec.toNat wv)))) Bool.true ->
    VeriPbCore.Entails F c ->
    And (VeriPbCore.InI64 (toInt64 (truncTo64 (BitVec.ofNat 128
          (Nat.sub (Nat.add (BitVec.toNat d) 340282366920938463463374607431768211456)
                   (BitVec.toNat wv))))))
        (VeriPbCore.Entails F
          (VeriPbCore.weakenC (toInt64 (truncTo64 (BitVec.ofNat 128
            (Nat.sub (Nat.add (BitVec.toNat d) 340282366920938463463374607431768211456)
                     (BitVec.toNat wv))))) c)) :=
    fun F c d wv hdd hw hgd hgw hgt h =>
      entails_weaken_narrowed F c (toInt128 wv)
        (BitVec.ofNat 128
          (Nat.sub (Nat.add (BitVec.toNat d) 340282366920938463463374607431768211456)
                   (BitVec.toNat wv)))
        (Eq.trans
          (congrArg (fun z : Int => z + toInt128 wv)
            (Eq.trans (wideSub_denotes_exact_difference d wv hgd hgw)
                      (congrArg (fun z : Int => Int.sub z (toInt128 wv)) hdd)))
          (VeriPbCore.sub_add_cancel c.degree (toInt128 wv)))
        hw hgt h

theorem entails_multiply_narrowed :
    forall (F : List VeriPbCore.Constraint) (c : VeriPbCore.Constraint)
           (k : Int) (t : BitVec 128),
    Int.le 0 k ->
    Eq (toInt128 t) (k * c.degree) ->
    Eq (guardFitsW t) Bool.true ->
    VeriPbCore.Entails F c ->
    And (VeriPbCore.InI64 (toInt64 (truncTo64 t)))
        (VeriPbCore.Entails F
          { terms := VeriPbCore.scaleTerms k c.terms,
            degree := toInt64 (truncTo64 t) }) :=
    fun F c k t hk hprod hfit h =>
      VeriPbCore.entails_multiply_checked F c k (toInt64 (truncTo64 t)) hk
        (eqOkB_of_eq (toInt64 (truncTo64 t)) (k * c.degree)
          (Eq.trans (narrowWide_value_preserving t hfit) hprod))
        (Eq.trans (congrArg VeriPbCore.fitsI64
                    (narrowWide_value_preserving t hfit))
                  (fitsI64_toInt128_of_guard t hfit))
        h

theorem entails_divide_narrowed :
    forall (F : List VeriPbCore.Constraint) (c : VeriPbCore.Constraint)
           (k : Int) (f : Int -> Int) (t : BitVec 128),
    Int.le 0 k ->
    VeriPbCore.CoeffsDominated k f c.terms ->
    Int.lt (k * f c.degree) (c.degree + k) ->
    Eq (toInt128 t) (f c.degree) ->
    Eq (guardFitsW t) Bool.true ->
    VeriPbCore.Entails F c ->
    And (VeriPbCore.InI64 (toInt64 (truncTo64 t)))
        (VeriPbCore.Entails F
          { terms := VeriPbCore.mapCoeff f c.terms,
            degree := toInt64 (truncTo64 t) }) :=
    fun F c k f t hk hdom hmin hq hfit h =>
      VeriPbCore.entails_divide_checked F c k f (toInt64 (truncTo64 t)) hk hdom hmin
        (eqOkB_of_eq (toInt64 (truncTo64 t)) (f c.degree)
          (Eq.trans (narrowWide_value_preserving t hfit) hq))
        (Eq.trans (congrArg VeriPbCore.fitsI64
                    (narrowWide_value_preserving t hfit))
                  (fitsI64_toInt128_of_guard t hfit))
        h

theorem wideMul_denotes_exact_product : forall (a : BitVec 128) (b : BitVec 128),
    Eq (guardFitsW a) Bool.true -> Eq (guardFitsW b) Bool.true ->
    Eq (toInt128 (BitVec.ofNat 128 (Nat.mul (BitVec.toNat a) (BitVec.toNat b))))
       (Int.mul (toInt128 a) (toInt128 b)) :=
    fun a b hga hgb =>
      Eq.trans
        (Eq.symm
          (congrArg toInt128
            (ofInt128_mul_wrap_of_fits a b
              (fitsI128_mul_of_bounds (toInt128 a) (toInt128 b)
                (toInt128_in_i64_of_guard a hga).left
                (toInt128_in_i64_of_guard a hga).right
                (toInt128_in_i64_of_guard b hgb).left
                (toInt128_in_i64_of_guard b hgb).right))))
        (toInt128_ofInt128 (Int.mul (toInt128 a) (toInt128 b))
          (fitsI128_mul_of_bounds (toInt128 a) (toInt128 b)
            (toInt128_in_i64_of_guard a hga).left
            (toInt128_in_i64_of_guard a hga).right
            (toInt128_in_i64_of_guard b hgb).left
            (toInt128_in_i64_of_guard b hgb).right))

theorem entails_multiply_from_guards :
    forall (F : List VeriPbCore.Constraint) (c : VeriPbCore.Constraint)
           (kv : BitVec 128) (d : BitVec 128),
    Int.le 0 (toInt128 kv) ->
    Eq (toInt128 d) c.degree ->
    Eq (guardFitsW kv) Bool.true ->
    Eq (guardFitsW d) Bool.true ->
    Eq (guardFitsW (BitVec.ofNat 128
         (Nat.mul (BitVec.toNat kv) (BitVec.toNat d)))) Bool.true ->
    VeriPbCore.Entails F c ->
    And (VeriPbCore.InI64
          (toInt64 (truncTo64 (BitVec.ofNat 128
            (Nat.mul (BitVec.toNat kv) (BitVec.toNat d))))))
        (VeriPbCore.Entails F
          { terms := VeriPbCore.scaleTerms (toInt128 kv) c.terms,
            degree := toInt64 (truncTo64 (BitVec.ofNat 128
              (Nat.mul (BitVec.toNat kv) (BitVec.toNat d)))) }) :=
    fun F c kv d hk hdd hgk hgd hgp h =>
      entails_multiply_narrowed F c (toInt128 kv)
        (BitVec.ofNat 128 (Nat.mul (BitVec.toNat kv) (BitVec.toNat d)))
        hk
        (Eq.trans (wideMul_denotes_exact_product kv d hgk hgd)
                  (congrArg (fun z : Int => Int.mul (toInt128 kv) z) hdd))
        hgp h

theorem capCoeff_inI64 : forall (d : Int) (x : Int),
    VeriPbCore.InI64 d -> VeriPbCore.InI64 x ->
    VeriPbCore.InI64 (VeriPbCore.capCoeff d x) :=
    fun d x hd hx =>
      @Bool.rec
        (fun bb : Bool =>
          VeriPbCore.InI64 (match bb with | Bool.true => x | Bool.false => d))
        hd hx (Int.ble x d)
}

/// `min(c, d)` on machine words. This is the machine image of
/// `VeriPbCore.capCoeff`, which SATURATE caps coefficients with.
pub fn cap_coeff_u64(c: u64, d: u64) -> u64 {
    if c < d { c } else { d }
}

/// Saturation never raises a coefficient.
///
/// The clause is proved by the island theorem `capcoeff_le_self`, with
/// `result` bound to the E6 kernel import of this function -- the machine
/// image of `VeriPbCore.capCoeff_le_self`. The theorem is stated over
/// `if c < d then c else d`, which is exactly the `ite`/`Decidable` term the
/// Select mint produces (compiler_consumer >= 2026-07-26); the import is delta-reducible,
/// so one theorem discharges both the `result` form and the call-site form.
pub fn cap_coeff_le_self_u64(c: u64, d: u64) -> u64
    ensures result <= c by capcoeff_le_self
{
    if c < d { c } else { d }
}

/// The same fact stated over the call, rather than over `result`: the spec
/// mentions `cap_coeff_u64` DEFINITIONALLY, so the clause is about the
/// function the binary actually runs.
pub fn cap_coeff_call_site(c: u64, d: u64) -> u64
    ensures cap_coeff_u64(c, d) <= c by capcoeff_le_self
{
    cap_coeff_u64(c, d)
}

/// The other defining bound of min: saturation caps at the degree.
pub fn cap_coeff_le_other_u64(c: u64, d: u64) -> u64
    ensures result <= d by capcoeff_le_other
{
    if c < d { c } else { d }
}

/// Both defining bounds of min in one conjunctive clause -- exercises the
/// conjunction-splitting discharge lane of the E9 citation audit.
pub fn cap_coeff_bounds_u64(c: u64, d: u64) -> u64
    ensures result <= c && result <= d by capcoeff_min_bounds
{
    if c < d { c } else { d }
}

/// **The saturation cap at its real width.** Byte-identical to
/// [`veripb_core_proved::cap_coeff`] — the function the checker actually
/// runs, over `i64` coefficients, not a `u64` stand-in. Its postcondition is
/// discharged by an island theorem, so this is the first place where a
/// *soundness-critical kernel function of the real crate* carries a
/// compiler-checked contract.
///
/// The signed encoding is two's-complement `BitVec 64` with the order key
/// `key64 v = Nat.xor (BitVec.toNat v) 2^63`, which maps signed order
/// bijectively onto `Nat` order — deliberately *not* Clean's unsigned
/// `BitVec` order, which would give the program's signed `<=` an unsigned
/// meaning at `i64::MIN`. `capCoeff_le_self` is the `Int`-level image of the
/// same fact (`VeriPbCore.capCoeff_le_self`).
///
/// The clause is a **complete characterisation**, not two upper bounds. Both
/// `result <= coeff` and `result <= degree` are satisfied by a `cap_coeff`
/// that returns `i64::MIN` unconditionally, and that implementation makes
/// SATURATE unsound (from `Σ cᵢ·lᵢ ≥ d` it derives `0 ≥ d`). The third
/// conjunct — the result is at least one of its two arguments — is what rules
/// that out: together the three pin `result == min(coeff, degree)` exactly.
pub fn cap_coeff_i64(degree: i64, coeff: i64) -> i64
    ensures result <= coeff && result <= degree && (result >= degree || result >= coeff)
    by capcoeff_i64_min_full
{
    if coeff <= degree { coeff } else { degree }
}

/// The first upper bound on its own (`VeriPbCore.capCoeff_le_self` at `i64`
/// width). Kept as its own function so the single-clause discharge lane stays
/// exercised alongside the conjunctive one above.
pub fn cap_coeff_i64_le_coeff(degree: i64, coeff: i64) -> i64
    ensures result <= coeff by capcoeff_i64_le_coeff
{
    if coeff <= degree { coeff } else { degree }
}

/// The other upper bound at the real width: saturation never exceeds the
/// degree (`VeriPbCore.capCoeff_le_degree`).
pub fn cap_coeff_i64_le_degree(degree: i64, coeff: i64) -> i64
    ensures result <= degree by capcoeff_i64_le_degree
{
    if coeff <= degree { coeff } else { degree }
}

/// **The direction SATURATE's soundness actually consumes**, at the real
/// width: the image of `VeriPbCore.le_capCoeff` (`veripb_kernel.lean:664`,
/// used by `entails_saturate_of_key` at :703). When the degree does not
/// exceed the coefficient, the cap does not fall *below* the degree — an
/// under-capping `cap_coeff` would let SATURATE derive a strictly stronger
/// constraint than the one it was given. Body token-identical to
/// [`veripb_core_proved::cap_coeff`], pinned by
/// `the_i64_cap_functions_have_the_body_of_the_real_cap_coeff`.
pub fn cap_coeff_i64_le_capcoeff(degree: i64, coeff: i64) -> i64
    ensures !(degree <= coeff) || result >= degree by capcoeff_i64_le_capcoeff
{
    if coeff <= degree { coeff } else { degree }
}

/// **A reflexivity control, not a soundness property — read the headline
/// count as eight substantive citations plus this one.** The obligation is
/// `d <= d` on the identity function, so discharging it says nothing whatever
/// about the checker.
///
/// It does NOT state "SATURATE leaves the degree alone" — that is
/// `(satC c).degree = c.degree`, an equality the clause fragment cannot state
/// today. The per-citation ledger in the development design notes §4.1 says which
/// citations carry weight and which, like this one, do not.
///
/// ## What it is actually for
///
/// It is the **coverage row for the non-`if` discharge lane**. Every other
/// citation here sits on a `min`-shaped body, so `result` is imported as the
/// `ite`/`Decidable` term the E6 Select mint produces; this one is the only
/// site where `result` is definitionally a *parameter*. If that import lane
/// ever broke, no other row in the file would notice.
///
/// It is also the citation `scripts/verify-proofs.sh --self-test` deletes
/// from a synthetic island log, to show that the island gate rejects a log
/// with a citation missing. The self-test looks *this function* up in
/// `island_citation_sites` (in `clean/proved-core-expected.txt`) rather than
/// hardcoding a name, so the fixture is this row and not a stand-in — and if
/// this row is ever removed, that lookup comes back empty and the self-test
/// fails, which is the prompt to rewrite this paragraph and the ledger row in
/// the development design notes §4.1 instead of leaving them claiming a fixture that
/// no longer exists.
///
/// ## What it is NOT, and what a previous version of this comment claimed
///
/// It is not evidence that a *disappearing* citation is otherwise visible,
/// and the count of proved obligations is no evidence of that either.
/// Measured 2026-08-24 against the stage2 compiler_consumer of the day: deleting the
/// `by u64_le_refl` here, or the `by capcoeff_i64_min_full` on the
/// soundness-carrying `cap_coeff_i64` above, leaves compiler_consumer at exit 0 with the
/// obligation total *unchanged* in both cases — the solver re-proves the
/// postcondition unaided and only the citation *name and site lists* move.
/// That is why those two lists are pinned, and why the obligation total is
/// documented as carrying no information about whether the citations are
/// present. The total itself is not written out here; it lives in
/// `island_proved_obligations` in `clean/proved-core-expected.txt`, and it has
/// moved once already since this note was taken (the two rule-guard citations
/// added later in the same day raised it), which is exactly why restating it
/// in prose is a mistake.
pub fn saturated_degree(degree: u64) -> u64
    ensures result <= degree by u64_le_refl
{
    degree
}

/// **The sign side condition WEAKEN and MULTIPLY are gated on**, at the real
/// coefficient width.
///
/// This is the first compiler-checked contract in this file that is not about
/// `min`. It is about a *rule's own side condition*: `entails_weaken_checked`
/// requires `Int.le 0 w` and `entails_multiply` requires `Int.le 0 k`, and in
/// the Rust kernel that hypothesis is discharged by one machine comparison
/// against zero. A negative factor is not a rounding matter: WEAKEN with
/// `w < 0` *raises* the degree, deriving a constraint strictly stronger than
/// the premise entails.
///
/// The body is exactly [`veripb_core_proved::weaken_degree`]'s acceptance
/// test, negated: that rule rejects `w < 0` with
/// `GuardError::NonPositiveFactor`, so it proceeds on precisely the set this
/// function returns `true` for. [`multiply`](veripb_core_proved::multiply)
/// rejects `k <= 0`, which is *stricter* than the kernel needs -- its
/// hypothesis is `Int.le 0 k`, and `k > 0` is required only so the rule is
/// non-degenerate. So this contract is `weaken_degree`'s test exactly, and
/// for `multiply` it is the kernel hypothesis its stricter check implies, not
/// the check itself.
///
/// ## What the clause claims
///
/// A **complete characterisation** of the test, not a one-way implication:
///
/// * `!result || w >= 0` — the test never accepts a negative factor. This is
///   the direction the kernel consumes.
/// * `result || w < 0` — and never rejects a non-negative one, so the test
///   cannot be satisfied by a constant `false`.
///
/// Each conjunct alone is satisfied by a wrong body (`w >= 1` never accepts a
/// negative factor either); only the two together force the comparison to
/// change sense at exactly zero. The theorem is the island's
/// `weaken_factor_sign_exact`, an instance of the shared decision lemma
/// `decide_le_exact` at the `i64` sign-flip order key `key64` — the signed
/// order, deliberately not Clean's unsigned `BitVec` order, which is the
/// whole question for a *sign* test.
///
/// ## What it does NOT claim
///
/// Nothing about `weaken_degree` or `multiply` themselves: their bodies (a
/// `Vec` clone, a `Result` return, exact-width arithmetic) are far outside the
/// E6 admission fragment, so no `ensures` can reach them. It claims that
/// *this* comparison decides the side condition exactly; that `weaken_degree`
/// performs this comparison is pinned by text, not by the compiler
/// (`the_rule_guard_twins_have_the_predicate_of_the_real_guards` in
/// `tests/island_sync.rs`), and the step from the side condition to soundness
/// is `entails_weaken_checked`, proved in the kernel.
pub fn weaken_factor_nonneg(w: i64) -> bool
    ensures (!result || w >= 0) && (result || w < 0) by weaken_factor_sign_exact
{
    w >= 0
}

/// **The width guard's lower bound, at the exact-arithmetic width the checker
/// computes it in.**
///
/// the development design notes §1.1 names the guard as the one place a width can be
/// got wrong: the rule lemmas are stated over unbounded `Int`, and every
/// machine value crossing into them is admitted by
/// [`veripb_core_proved::guard::fits_i64`] and nothing else. That function is
///
/// ```text
/// pub fn fits_i64(x: Wide) -> bool {
///     x >= Wide::from(Coeff::MIN) && x <= Wide::from(Coeff::MAX)
/// }
/// ```
///
/// — two literal-bounded comparisons over `Wide = i128`. This is its lower
/// half, at that same carrier, and it is the half bug C runs through:
/// `weaken_degree` decrements a degree, and the value that must be caught is
/// `i64::MIN - 1`, which as `i64` arithmetic wraps to `i64::MAX` and so passes
/// any *upper* bound. At `i128` the un-wrapped value is still visible, and
/// this clause says the comparison that sees it changes sense at exactly
/// `i64::MIN`:
///
/// * `!result || x >= i64::MIN` — never accepts an underflowed value
///   (the direction `inI64_of_fitsI64` supplies to `entails_add_checked` and
///   `entails_weaken_checked`);
/// * `result || x < i64::MIN` — and never rejects a representable one.
///
/// The theorem is the island's `guard_fits_lower_exact`, `decide_le_exact` at
/// the `i128` sign-flip key `key128`.
///
/// ## The upper half, and the threshold that used to keep it out
///
/// For most of this file's life the sibling below ([`fits_i64_upper_wide`])
/// could not exist: measured 2026-08-24 against the stage2 compiler_consumer of the day,
/// a numeral written in a `clean { }` island was definitionally equal to the
/// literal compiler_consumer mints only when its value was at least `2^64`, or was
/// spelled `Nat.zero`. `i64::MIN` at 128 bits is `2^128 - 2^63` and cleared
/// that threshold; `i64::MAX` is `9223372036854775807` and did not, so
/// `BitVec.ofNat 128 9223372036854775807` was refused as not definitionally
/// equal to the mint's literal and no theorem over it could discharge
/// anything — the *value*, not the spelling, decided. The cause was the Clean
/// kernel's `BitVec.ofNat` reducer reading its operand through a u64-capped
/// bare-literal reader: it fired on the mint's small bare literal, parked on
/// the island's `OfNat`-wrapped spelling, and the two normal forms diverged
/// exactly below `2^64`. Lifted 2026-08-25 (first-party/clean `05f6b0b3d`:
/// multi-limb read, `OfNat` numeral peel, multi-limb emit — pure evaluation
/// of `ofNat`'s own `mod 2^w` semantics). Both halves are compiler-cited
/// now, and [`fits_i64_wide`] below carries the conjunction the real guard
/// computes as a single contract. The compiler_consumer probe pair `f43`/`f44` pins
/// that the magnitude no longer decides.
///
/// ## What it does NOT claim
///
/// Nothing about `add`, `multiply`, `divide`, `weaken_degree`, `negate` or
/// `mir`: their bodies are outside the admission fragment. It claims that one
/// of the two comparisons `guard::fits_i64` is made of accepts exactly the
/// values at or above `i64::MIN`. The step to rule soundness is
/// `entails_add_checked` / `entails_weaken_checked`, proved in the kernel; the
/// step from this function to the one `add` actually calls is
/// `the_rule_guard_twins_have_the_predicate_of_the_real_guards`, which pins
/// the real guard's source text *and* runs it against the two literal
/// comparisons at every boundary — a test, not a compiler check.
///
/// ## It is load-bearing, unlike the citations above it
///
/// Deleting `by capcoeff_i64_min_full` from `cap_coeff_i64` leaves compiler_consumer at
/// exit 0 with the same obligation total, because the solver re-proves that
/// postcondition unaided. Deleting `by guard_fits_lower_exact` here does not:
/// the native verifier reports this clause `Unknown` at `i128`, so the
/// obligations are proved by the kernel discharge or not at all, and removing
/// the citation turns the build red.
pub fn fits_i64_lower_wide(x: i128) -> bool
    ensures (!result || x >= -9223372036854775808) && (result || x < -9223372036854775808)
    by guard_fits_lower_exact
{
    x >= -9223372036854775808
}

/// The width guard's OTHER half — the direction the overflow family runs in:
/// a degree grown past `i64::MAX` must be caught by the upper comparison, at
/// `i128`, where the un-wrapped value is still visible.
///
/// * `!result || x <= i64::MAX` — never accepts an overflowed value;
/// * `result || x > i64::MAX` — and never rejects a representable one.
///
/// The theorem is the island's `guard_fits_upper_exact` — `decide_le_exact`
/// at `key128`, the exact mirror of the lower half's. This was the first
/// citation in this crate whose bound sits below `2^64`; see the threshold
/// note on [`fits_i64_lower_wide`] for why that was impossible before the
/// `BitVec.ofNat` reducer lift, and it is load-bearing the same way its
/// sibling is: the native verifier reports the clause `Unknown` at `i128`,
/// so the kernel discharge is the only proof and dropping the `by` turns the
/// build red.
pub fn fits_i64_upper_wide(x: i128) -> bool
    ensures (!result || x <= 9223372036854775807) && (result || x > 9223372036854775807)
    by guard_fits_upper_exact
{
    x <= 9223372036854775807
}

/// The COMPLETE width guard, one body, both bounds -- the exact shape of
/// `guard::fits_i64` after `Wide::from(Coeff::MIN)`/`Wide::from(Coeff::MAX)`
/// const-fold (measured: the real guard compiles to this conjunction of two
/// literal-bounded comparisons with `calls=[]`, `admissible=true`).  The
/// clause is the two-sided characterization: `true` never accepts a value
/// outside `[i64::MIN, i64::MAX]`, `false` never rejects one inside it.
///
/// The theorem is the island's `guard_fits_exact` -- `decide_and_le_exact`
/// (the `Bool.and` lift of `decide_le_exact`) at the `i128` sign-flip key
/// `key128`.  Unlike the two half-twins above, this contract speaks about
/// the conjunction the body actually computes, so the step from here to the
/// real `guard::fits_i64` is body-shape identity, not a pair of halves glued
/// by a test.
pub fn fits_i64_wide(x: i128) -> bool
    ensures (!result || (x >= -9223372036854775808 && x <= 9223372036854775807))
        && (result || (x < -9223372036854775808 || x > 9223372036854775807))
    by guard_fits_exact
{
    x >= -9223372036854775808 && x <= 9223372036854775807
}

/// **Overflow-checked wide addition** -- the checker's exact-arithmetic add at
/// `Wide = i128`, as a leaf: the body is exactly `a.checked_add(b)`, the shape
/// [`veripb_core_proved::add`]'s degree core computes before `guard::fits_i64`
/// narrows the sum back to `i64`. The kernel model is the island's
/// `checkedAdd128`: the EXACT sum over unbounded `Int` (through the `key128`
/// sign-flip bridge `toInt128`), guarded by `fitsI128` -- `some` exactly when
/// the true sum is representable, `none` exactly on true overflow, with
/// `i128::MIN` edges falling out of the unbounded arithmetic.
///
/// ## What the clause claims
///
/// Argument-order symmetry: `checked_add(a, b) == checked_add(b, a)`, the
/// island's `checkedAdd128_comm`. This is a genuine functional postcondition
/// of the OPERATION (guard and payload both commute because `Int.add`
/// commutes), and it is op-discriminating: `checked_sub` is NOT commutative,
/// so a mint that mis-recognized the op fails to match the cited statement --
/// the same NEG-probe discipline as `admit_select_function`.
///
/// ## What it does NOT claim, and the staged full contract
///
/// Nothing about WHICH `Some`/`None` comes back. The full functional pairing
///
/// ```text
/// requires  fits_i128(a + b)   ensures result == Some(a + b)   // _some
/// requires !fits_i128(a + b)   ensures result == None          // _none
/// ```
///
/// is authored and proved in the island (`checkedAdd128_some`/`_none`) but is
/// NOT citable yet -- staged, awaiting THREE named capabilities, any one of
/// which is insufficient alone:
/// 1. a hypothesis lane: `requires` clauses are never folded into the E9
///    citation goal (the goal is built from the ensures clause alone), and no
///    `==>`-fragment hypothesis elaborates to the theorems'
///    `fitsI128 (exact sum) = true` -- clause hypotheses are `key128`-order
///    comparisons or admitted-bool-call facts, neither of which reaches the
///    exact-`Int` guard without (2) and (3);
/// 2. the `BitVec.toNat`/`Nat.xor` round-trip inventory (the two
///    `NOT YET PROVABLE` blocks at the end of `veripb_kernel.lean`), needed to
///    restate the `Some` payload in the clause fragment's WRAPPING-add
///    spelling (`checkedAdd128_some_wrap`, statement recorded there);
/// 3. the structural `ofNat`-peel in the vendored `reduce_bitvec_to_nat`
///    (successor increment to first-party/clean 05f6b0b3d), without which the
///    island cannot evaluate `key128` of any literal bound.
pub fn cadd_wide(a: i128, b: i128) -> Option<i128>
    ensures result == cadd_wide(b, a) by checkedAdd128_comm
    ensures fits_i64_wide(a) ==> fits_i64_wide(b) ==> cadd_wide(a, b) != None
    by checkedAdd128_isSome_of_inI64
{
    a.checked_add(b)
}

/// **Overflow-checked wide subtraction** -- `a.checked_sub(b)` at `Wide =
/// i128`, the leaf shape of [`veripb_core_proved::weaken_degree`]'s decrement,
/// the site of bug C: `i64::MIN - 1` wraps to `i64::MAX` at `i64` width and
/// passes every upper bound, while at `i128` the un-wrapped value is still
/// visible and `checked_sub` cannot even wrap. Kernel model: the island's
/// `checkedSub128` (exact `Int` difference + `fitsI128`).
///
/// ## What the clause claims
///
/// The diagonal never overflows: `checked_sub(a, a)` is `Some(_)`, never
/// `None` -- the island's `checkedSub128_self_isSome` (`Int.sub_self` maps the
/// guard onto `fitsI128 0 = true`). A deliberately SUB-specific fact:
/// `checked_add(a, a)` and `checked_mul(a, a)` genuinely can return `None`,
/// so a mint that swapped the op fails to match the cited statement. The
/// clause names the function directly (the [`cap_coeff_call_site`] precedent)
/// because the claim is about the diagonal, not about the general `result`.
///
/// ## What it does NOT claim, and the staged full contract
///
/// Nothing about `checked_sub(a, b)` for `a != b`, and nothing about the
/// payload. The full functional pairing (`requires fits ==> Some(a - b)` /
/// `requires !fits ==> None`, by `checkedSub128_some`/`_none`) is staged
/// behind the same three named capabilities listed on [`cadd_wide`].
pub fn csub_wide(a: i128, b: i128) -> Option<i128>
    ensures csub_wide(a, a) != None by checkedSub128_self_isSome
    ensures fits_i64_wide(a) ==> fits_i64_wide(b) ==> csub_wide(a, b) != None
    by checkedSub128_isSome_of_inI64
{
    a.checked_sub(b)
}

/// **Overflow-checked wide multiplication** -- `a.checked_mul(b)` at `Wide =
/// i128`, the leaf shape of `Exact::checked_mul` (used by `divide_with`'s
/// check). Kernel model: the island's `checkedMul128` -- the exact product can
/// reach ~2^254, but `Int.mul` is unbounded, so the model needs no 256-bit
/// carrier, and `MIN * -1` is just a non-fitting exact product: `none` with no
/// special-casing.
///
/// ## What the clause claims
///
/// Argument-order symmetry, by `checkedMul128_comm`. `Int.mul_comm` is not in
/// the Clean default environment; the island derives it (`int_mul_comm`, a
/// double `Int.rec` constructor split over `Nat.mul_comm`) and the checked
/// statement follows by the same scrutinee-and-payload rewrite as the add
/// twin. Op-discriminating against `checked_sub` exactly as on [`cadd_wide`].
///
/// ## What it does NOT claim, and the staged full contract
///
/// Nothing about which `Some`/`None` comes back; the full
/// `checkedMul128_some`/`_none` pairing is staged behind the same three named
/// capabilities listed on [`cadd_wide`].
pub fn cmul_wide(a: i128, b: i128) -> Option<i128>
    ensures result == cmul_wide(b, a) by checkedMul128_comm
    ensures fits_i64_wide(a) ==> fits_i64_wide(b) ==> cmul_wide(a, b) != None
    by checkedMul128_isSome_of_inI64
{
    a.checked_mul(b)
}

/// **The width guard's NARROWING half** -- the twin of
/// [`veripb_core_proved::guard::narrow`], the one function every rule's
/// widened arithmetic must pass through before a value may be stored as a
/// machine coefficient. Sixteen sites on the soundness path consume its
/// result (add, multiply, divide_with, weaken_degree, negate, normalize's
/// four, mir's four); this body is that function token-for-token under the
/// single pinned substitution `fits_i64` -> [`fits_i64_wide`], and
/// `the_narrow_twin_has_the_body_of_the_real_narrow` pins the two together.
///
/// This is the first CONSUMER shape to carry a contract: earlier citations
/// sit on bodies that compute a value, this one destructures the guard into
/// an `Option`. compiler_consumer admits it through the GuardedNarrow lane, whose mint
/// models the `x as i64` cast as what it is -- two's-complement TRUNCATION,
/// `BitVec.ofNat 64 (BitVec.toNat x)` -- UNCONDITIONALLY, so the defining
/// equation is exact on every input including the ones the guard rejects.
/// No part of the model rests on the guard being right.
///
/// ## What the two clauses claim
///
/// * `result == narrowWide(x)` -- the FULL functional equation, uncited
///   (it closes by delta-defeq against the island definition, the f49
///   mechanism). Both halves are pinned by it: `Some` of the truncation
///   exactly when the guard holds, `None` exactly when it does not.
/// * `fits_i64_wide(x) ==> narrow_wide(x) != None`, by
///   `narrowWide_isSome_of_fits` -- the hypothesis-guarded guarantee that a
///   value already known to be in range is never rejected, over the same
///   `guardFitsW` spelling the checked-arithmetic contracts use.
///
/// ## The theorem behind it that no earlier citation could state
///
/// `narrowW_value_preserving` (island): under a true guard,
/// `toInt64 (truncTo64 x) = toInt128 x` -- the `i64` admitted into storage
/// DENOTES THE SAME INTEGER as the `i128` it came from. That is the silent
/// truncation-corruption class, and until the narrowing body itself became
/// admissible nothing in this crate could speak about it: the fits twins
/// pin the boolean guard, not the value it admits.
pub fn narrow_wide(x: i128) -> Option<i64>
    ensures result == narrowWide(x)
{
    if fits_i64_wide(x) {
        Some(x as i64)
    } else {
        None
    }
}

/// The same body, carrying the HYPOTHESIS-GUARDED half of the claim.
///
/// Two functions rather than two clauses on one, and the reason is a
/// measured property of the toolchain rather than a preference: a function
/// that carries one CITED clause must cite them all, because the citation
/// discharge covers a clause's fail-closed sentinels only for clauses it was
/// given a theorem for — and the functional equation above cannot be cited,
/// since a cited clause must type its `result` (or name a Rust call, which
/// an island definition is not). Each lane discharges what it can express:
/// the equation closes by delta-defeq against `narrowWide`, and this one
/// closes by kernel citation. Both bodies are pinned to the real
/// `guard::narrow` by `the_narrow_twin_has_the_body_of_the_real_narrow`.
///
/// Logically the equation above subsumes this claim; it is kept because it
/// is the one that exercises the CITATION path on a consumer shape, and
/// because `narrowWide_isSome_of_fits` states it over the same `guardFitsW`
/// hypothesis spelling the checked-arithmetic contracts use — so a reader
/// comparing the two families is comparing like with like.
pub fn narrow_wide_in_range(x: i128) -> Option<i64>
    ensures fits_i64_wide(x) ==> narrow_wide_in_range(x) != None
    by narrowWide_isSome_of_fits
{
    if fits_i64_wide(x) {
        Some(x as i64)
    } else {
        None
    }
}
