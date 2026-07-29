import AySoundness.StringThy
/-
  Soundness of the LENGTH-INVARIANT tier of QF_S / QF_SLIA regular-expression
  membership (`str.in_re` over a SYMBOLIC string).

  `AySoundness.StringThy` / `AySoundness.SeqThy` cover len/cat/charAt/str.at/
  indexof only — nothing there mentions regex membership, so before this module
  every `str.in_re` conflict was declined by the firewall.

  This file supplies the missing invariants:

      `mem_len_dvd : kdvd k r = true → Mem r s → k ∣ len s`

  a MODULAR-LENGTH invariant of regular-expression membership, computed by a
  purely structural `Bool` predicate `kdvd`.  It subsumes the "re.*/re.+
  commutation" and "interval collapse" lemmas the accounting doc predicted:
  because the invariant is proved by induction on the membership derivation and
  `kdvd` recurses structurally, ARBITRARY nestings such as
  `(re.+ (re.* (str.to_re w)))` or `(re.* (re.++ (re.+ R) (str.to_re "")))` are
  handled directly, with no normalisation/commutation step needed.

  Companion invariants `mem_minLen_le` (structural lower bound) and
  `mem_maxLen_ge` (structural upper bound for finite languages) close the
  complementary "too short" / "too long" conflicts, and the two of them are what
  the INEQUALITY firing conditions (`<`, `<=`, `>`, `>=` on `str.len`) are proved
  from — see `regex_len_min_conflict_le` / `regex_len_max_conflict_ge`.  The
  modular invariant has no inequality form and the emitter must not fire it on
  one.

  Model: `Str = List Nat` — exactly `AySoundness.StringThy.Str`, so the emitter
  can reuse the existing `StringThy.len` / `StringThy.cat` grounding and the
  already-verified `StringThy.len_cat`.

  SCOPE OF THE COMMITMENT.  The only semantic commitment made here is that `Mem`
  is the textbook membership relation for the `Re` syntax below.  Every soundness
  obligation OUTSIDE that — that the emitter renders the SMT-LIB regex faithfully
  into `Re`, that the string literals were decoded with SMT-LIB 2.6 semantics,
  that the rendered assertions are in scope at the certified `check-sat` — lives
  in the emitter and is NOT discharged by any theorem in this file.  In
  particular, the one-sided (over-approximating) treatment of `Re.inter` and of
  `re.range` says nothing about the front end: a front-end misclassification
  still produces a file that kernel-checks while certifying the wrong query.

  Pure Lean 4 core (no Mathlib).  Axioms must be ⊆ {propext, Quot.sound}.
-/

namespace AySoundness.RegexThy

open AySoundness.StringThy

/-! ## Syntax of the SMT-LIB regular expressions AY actually sees.

Only the constructors whose length behaviour is soundly abstractable are
modelled.  `re.comp` (complement) and `re.diff` are deliberately ABSENT: their
length sets are not bounded by any structural rule over the operand, so an
emitter must DECLINE on them rather than guess.  `re.inter` IS modelled,
because `L(inter a b) ⊆ L(a)` gives a sound one-sided rule. -/

/-- A regular expression over codepoints (`Nat`). -/
inductive Re where
  /-- `re.none` — the empty language. -/
  | none : Re
  /-- `str.to_re w` — the singleton language `{w}` (also models `re.to_re ""`). -/
  | lit : Str → Re
  /-- `re.allchar` / `re.range a b` — any single character. -/
  | anyChar : Re
  /-- `re.++` — concatenation. -/
  | cat : Re → Re → Re
  /-- `re.union` — union. -/
  | union : Re → Re → Re
  /-- `re.inter` — intersection. -/
  | inter : Re → Re → Re
  /-- `re.*` — Kleene star. -/
  | star : Re → Re
  deriving Repr

/-- `re.+ r` is derived: `r ++ r*`. -/
def plus (r : Re) : Re := .cat r (.star r)

/-- `re.opt r` is derived: `ε ∪ r`. -/
def opt (r : Re) : Re := .union (.lit []) r

/-! ## Semantics: the membership relation.

`Mem r s` is the standard inductive characterisation of `s ∈ L(r)`.  It is the
ONLY semantic commitment this file makes, and it is the textbook one, so the
emitter's obligation is just to render the SMT regex syntax faithfully into
`Re`. -/

/-- `Mem r s` : the string `s` is in the language of `r`. -/
inductive Mem : Re → Str → Prop where
  | lit (w : Str) : Mem (.lit w) w
  | anyChar (c : Nat) : Mem .anyChar [c]
  | cat {a b : Re} {s t : Str} : Mem a s → Mem b t → Mem (.cat a b) (s ++ t)
  | unionL {a b : Re} {s : Str} : Mem a s → Mem (.union a b) s
  | unionR {a b : Re} {s : Str} : Mem b s → Mem (.union a b) s
  | inter {a b : Re} {s : Str} : Mem a s → Mem b s → Mem (.inter a b) s
  | starNil {a : Re} : Mem (.star a) []
  | starCat {a : Re} {s t : Str} : Mem a s → Mem (.star a) t → Mem (.star a) (s ++ t)

/-- The firewall's `atomVal` is `Bool`-valued, so an emitter that renders a
    `str.in_re` assertion as an atom needs SOME decision procedure for `Mem`.
    We supply the classical one.

    Why not a Boolean regex matcher: a matcher would need its own soundness
    proof (`matches r s = true ↔ Mem r s`), and a bug in it would silently
    change WHICH proposition the emitted atom denotes.  The classical instance
    is definitionally opaque — nothing ever computes with it — so the emitted
    atom is EXACTLY the membership proposition.  The only cost is that
    `Classical.choice` appears in the emitted artifact's axiom audit, which is
    inside the allowed set {propext, Classical.choice, Quot.sound}. -/
noncomputable instance instDecidableMem (r : Re) (s : Str) : Decidable (Mem r s) :=
  Classical.propDecidable _

/-! ## The modular-length abstraction.

`kdvd k r` is a decidable, purely structural sufficient condition for
"every member of `r` has length divisible by `k`". -/

/-- Structural check: does every string in `L r` have length divisible by `k`? -/
def kdvd (k : Nat) : Re → Bool
  | .none      => true                       -- vacuous: no members
  | .lit w     => decide (k ∣ w.length)
  | .anyChar   => decide (k ∣ 1)
  | .cat a b   => kdvd k a && kdvd k b
  | .union a b => kdvd k a && kdvd k b
  | .inter a b => kdvd k a || kdvd k b       -- one-sided: L(inter) ⊆ L(a) and ⊆ L(b)
  | .star a    => kdvd k a

/-- **Modular-length invariant of regex membership.**  If every literal leaf of
    `r` (along the branches the abstraction inspects) has length divisible by
    `k`, then so does every string in `L(r)`.

    This is the missing symbolic-regex lemma: `s` is an arbitrary (SYMBOLIC)
    string, and the conclusion is a pure arithmetic fact about `len s` that the
    LIA core can then contradict against an asserted `str.len` value. -/
theorem mem_len_dvd {k : Nat} : ∀ {r : Re} {s : Str},
    kdvd k r = true → Mem r s → k ∣ len s := by
  intro r s hk hm
  induction hm with
  | lit w =>
      simpa [len, kdvd] using (of_decide_eq_true hk)
  | anyChar c =>
      have : k ∣ 1 := by simpa [kdvd] using (of_decide_eq_true hk)
      simpa [len] using this
  | @cat a b s t _ha _hb iha ihb =>
      simp only [kdvd, Bool.and_eq_true] at hk
      have h1 := iha hk.1
      have h2 := ihb hk.2
      simp only [len, List.length_append]
      exact Nat.dvd_add h1 h2
  | @unionL a b s _h ih =>
      simp only [kdvd, Bool.and_eq_true] at hk
      exact ih hk.1
  | @unionR a b s _h ih =>
      simp only [kdvd, Bool.and_eq_true] at hk
      exact ih hk.2
  | @inter a b s _ha _hb iha ihb =>
      simp only [kdvd, Bool.or_eq_true] at hk
      cases hk with
      | inl h => exact iha h
      | inr h => exact ihb h
  | @starNil a =>
      simp [len]
  | @starCat a s t _ha _ht iha iht =>
      simp only [kdvd] at hk
      have h1 := iha hk
      have h2 := iht (by simp only [kdvd]; exact hk)
      simp only [len, List.length_append]
      exact Nat.dvd_add h1 h2

/-! ## The complementary minimum-length abstraction. -/

/-- Structural lower bound on the length of any member of `r`. -/
def minLen : Re → Nat
  | .none      => 0                          -- vacuous
  | .lit w     => w.length
  | .anyChar   => 1
  | .cat a b   => minLen a + minLen b
  | .union a b => Nat.min (minLen a) (minLen b)
  | .inter a b => Nat.max (minLen a) (minLen b)
  | .star _    => 0

/-- **Minimum-length invariant.**  Every member of `r` is at least `minLen r`
    characters long. -/
theorem mem_minLen_le : ∀ {r : Re} {s : Str}, Mem r s → minLen r ≤ len s := by
  intro r s hm
  induction hm with
  | lit w => simp [minLen, len]
  | anyChar c => simp [minLen, len]
  | @cat a b s t _ha _hb iha ihb =>
      simp only [minLen, len, List.length_append]
      simp only [len] at iha ihb
      omega
  | @unionL a b s _h ih =>
      simp only [minLen, Nat.min_def]
      simp only [len] at ih ⊢
      split <;> omega
  | @unionR a b s _h ih =>
      simp only [minLen, Nat.min_def]
      simp only [len] at ih ⊢
      split <;> omega
  | @inter a b s _ha _hb iha ihb =>
      simp only [minLen, Nat.max_def]
      simp only [len] at iha ihb ⊢
      split <;> omega
  | @starNil a => simp [minLen]
  | @starCat a s t _ha _ht _iha _iht => simp [minLen]

/-! ## The maximum-length (finite-language) abstraction.

`maxLen r = some n` certifies that `L(r)` is length-bounded by `n`; `none`
means the structural check found an unbounded star and gives up (fail-closed). -/

/-- Structural upper bound on the length of any member of `r`, when one exists. -/
def maxLen : Re → Option Nat
  | .none      => some 0                     -- vacuous
  | .lit w     => some w.length
  | .anyChar   => some 1
  | .cat a b   =>
      match maxLen a, maxLen b with
      | some x, some y => some (x + y)
      | _, _ => Option.none
  | .union a b =>
      match maxLen a, maxLen b with
      | some x, some y => some (Nat.max x y)
      | _, _ => Option.none
  | .inter a b =>                            -- one-sided: L(inter) ⊆ L(a), ⊆ L(b)
      match maxLen a, maxLen b with
      | some x, some y => some (Nat.min x y)
      | some x, Option.none => some x
      | Option.none, some y => some y
      | Option.none, Option.none => Option.none
  | .star a    =>
      match maxLen a with
      | some 0 => some 0                     -- only ε iterates ⇒ language = {ε}
      | _ => Option.none

/-- **Maximum-length invariant.**  If the structural check certifies a bound
    `n`, every member of `r` is at most `n` characters long.  This closes the
    "regex pins a FINITE language, the asserted length overshoots it" conflicts
    (e.g. a bare `str.to_re w` with an asserted `str.len ≠ |w|`). -/
theorem mem_maxLen_ge : ∀ {r : Re} {s : Str} {n : Nat},
    maxLen r = some n → Mem r s → len s ≤ n := by
  intro r s n hn hm
  induction hm generalizing n with
  | lit w => simp only [maxLen, Option.some.injEq] at hn; simp [len, ← hn]
  | anyChar c => simp only [maxLen, Option.some.injEq] at hn; simp [len, ← hn]
  | @cat a b s t _ha _hb iha ihb =>
      simp only [maxLen] at hn
      cases hx : maxLen a with
      | none => rw [hx] at hn; cases hy : maxLen b <;> rw [hy] at hn <;> simp at hn
      | some x =>
        cases hy : maxLen b with
        | none => rw [hx, hy] at hn; simp at hn
        | some y =>
          rw [hx, hy] at hn
          simp only [Option.some.injEq] at hn
          have h1 := iha hx
          have h2 := ihb hy
          simp only [len, List.length_append] at *
          omega
  | @unionL a b s _h ih =>
      simp only [maxLen] at hn
      cases hx : maxLen a with
      | none => rw [hx] at hn; cases hy : maxLen b <;> rw [hy] at hn <;> simp at hn
      | some x =>
        cases hy : maxLen b with
        | none => rw [hx, hy] at hn; simp at hn
        | some y =>
          rw [hx, hy] at hn
          simp only [Option.some.injEq] at hn
          have h1 := ih hx
          simp only [len, Nat.max_def] at *
          split at hn <;> omega
  | @unionR a b s _h ih =>
      simp only [maxLen] at hn
      cases hx : maxLen a with
      | none => rw [hx] at hn; cases hy : maxLen b <;> rw [hy] at hn <;> simp at hn
      | some x =>
        cases hy : maxLen b with
        | none => rw [hx, hy] at hn; simp at hn
        | some y =>
          rw [hx, hy] at hn
          simp only [Option.some.injEq] at hn
          have h2 := ih hy
          simp only [len, Nat.max_def] at *
          split at hn <;> omega
  | @inter a b s _ha _hb iha ihb =>
      simp only [maxLen] at hn
      cases hx : maxLen a with
      | none =>
        cases hy : maxLen b with
        | none => rw [hx, hy] at hn; simp at hn
        | some y =>
          rw [hx, hy] at hn; simp only [Option.some.injEq] at hn
          have h2 := ihb hy; omega
      | some x =>
        cases hy : maxLen b with
        | none =>
          rw [hx, hy] at hn; simp only [Option.some.injEq] at hn
          have h1 := iha hx; omega
        | some y =>
          rw [hx, hy] at hn; simp only [Option.some.injEq] at hn
          have h1 := iha hx
          have h2 := ihb hy
          simp only [Nat.min_def] at hn
          split at hn <;> omega
  | @starNil a =>
      simp only [maxLen] at hn
      cases hx : maxLen a with
      | none => rw [hx] at hn; simp at hn
      | some x =>
        cases x with
        | zero => rw [hx] at hn; simp only [Option.some.injEq] at hn; simp [len, ← hn]
        | succ k => rw [hx] at hn; simp at hn
  | @starCat a s t _ha _ht iha iht =>
      simp only [maxLen] at hn
      cases hx : maxLen a with
      | none => rw [hx] at hn; simp at hn
      | some x =>
        cases x with
        | zero =>
          have hstar : maxLen (Re.star a) = some 0 := by
            simp only [maxLen, hx]
          rw [hx] at hn; simp only [Option.some.injEq] at hn
          have h1 := iha hx
          have h2 := iht hstar
          simp only [len, List.length_append] at *
          omega
        | succ k => rw [hx] at hn; simp at hn

/-! ## Emitter-facing conflict corollaries.

These are the exact `False`-shaped obligations a firewall emitter would
discharge.  Each takes the SYMBOLIC membership hypothesis plus an asserted
`str.len` value and derives `False` by pure decidable arithmetic. -/

/-- **Symbolic regex-membership length conflict (modular).**  If `s ∈ L(r)`,
    the structural modulus check `kdvd k r` succeeds, and `len s` is asserted
    to be `c` with `k ∤ c`, then the assertion set is unsatisfiable. -/
theorem regex_len_mod_conflict {k c : Nat} {r : Re} {s : Str}
    (hk : kdvd k r = true) (hm : Mem r s) (hlen : len s = c)
    (hnd : ¬ (k ∣ c)) : False :=
  hnd (hlen ▸ mem_len_dvd hk hm)

/-- **Symbolic regex-membership length conflict (too short).**  If `s ∈ L(r)`
    but `len s` is asserted below `minLen r`, the assertion set is
    unsatisfiable. -/
theorem regex_len_min_conflict {c : Nat} {r : Re} {s : Str}
    (hm : Mem r s) (hlen : len s = c) (hlt : c < minLen r) : False := by
  have := mem_minLen_le hm
  omega

/-- **Symbolic regex-membership length conflict (too long / finite language).**
    If `s ∈ L(r)`, the structural bound check yields `maxLen r = some n`, and
    `len s` is asserted above `n`, the assertion set is unsatisfiable. -/
theorem regex_len_max_conflict {c n : Nat} {r : Re} {s : Str}
    (hn : maxLen r = some n) (hm : Mem r s) (hlen : len s = c)
    (hgt : n < c) : False := by
  have := mem_maxLen_ge hn hm
  omega

/-! ### INEQUALITY firing conditions.

The four corollaries above all require an EQUALITY pin `len s = c`.  An emitter
that fires on `<` / `<=` / `>` / `>=` needs these two, which are the only
inequality-shaped conflicts the invariants support.  There is deliberately NO
inequality form of the modular conflict: `k ∣ len s` is compatible with every
open length interval that contains a multiple of `k`, so an emitter must never
fire `kdvd` on an inequality. -/

/-- **Too short, inequality form.**  `s ∈ L(r)` and an asserted UPPER bound on
    `len s` that falls strictly below the structural minimum. Covers `(<= (str.len
    s) b)` directly, and `(< (str.len s) b')` after the emitter's `b = b' - 1`
    normalisation (`b' ≥ 1`). -/
theorem regex_len_min_conflict_le {b : Nat} {r : Re} {s : Str}
    (hm : Mem r s) (hlen : len s ≤ b) (hlt : b < minLen r) : False := by
  have := mem_minLen_le hm
  omega

/-- **Too long, inequality form.**  `s ∈ L(r)`, the structural bound check yields
    `maxLen r = some n`, and an asserted LOWER bound on `len s` exceeds `n`.
    Covers `(>= (str.len s) b)` directly, and `(> (str.len s) b')` after the
    emitter's `b = b' + 1` normalisation. -/
theorem regex_len_max_conflict_ge {b n : Nat} {r : Re} {s : Str}
    (hn : maxLen r = some n) (hm : Mem r s) (hlen : b ≤ len s) (hgt : n < b) :
    False := by
  have := mem_maxLen_ge hn hm
  omega

/-- **Two-membership modular conflict.**  `s ∈ L(r₁) ∧ s ∈ L(r₂)` with moduli
    `k₁`, `k₂` and any `c` that is not a common multiple.  (Instantiates
    `regex_len_mod_conflict` on whichever side fails; stated separately because
    the emitter sees the two `str.in_re` assertions independently.) -/
theorem regex_two_mem_len_conflict {k₁ k₂ c : Nat} {r₁ r₂ : Re} {s : Str}
    (h₁ : kdvd k₁ r₁ = true) (h₂ : kdvd k₂ r₂ = true)
    (m₁ : Mem r₁ s) (m₂ : Mem r₂ s) (hlen : len s = c)
    (hnd : ¬ (k₁ ∣ c) ∨ ¬ (k₂ ∣ c)) : False := by
  cases hnd with
  | inl h => exact regex_len_mod_conflict h₁ m₁ hlen h
  | inr h => exact regex_len_mod_conflict h₂ m₂ hlen h

/-! ## Concrete, kernel-checked, NON-vacuous witnesses.

Instantiated on the ACTUAL residual benchmark
`benchmarks/smtcomp/QF_SLIA/non-incremental/QF_SLIA/20230327-stringfuzz-lu/
transformed/z3str2/regex-011-unsat-fuzz-graft-reverse.smt2`:

    (assert (str.in_re x (re.+ (re.* (str.to_re ":{'hAa")))))
    (assert (= 4 (str.len x)))

`":{'hAa"` is 6 codepoints (58 123 39 104 65 97).  The regex is
`re.+ (re.* (str.to_re w))` — the DOUBLY-nested star/plus shape the accounting
doc called out as needing a commutation lemma.  `kdvd 6` sees straight through
it structurally.  6 ∤ 4, so the assertion set is refuted, for EVERY `x`. -/

/-- `":{'hAa"` as codepoints — 6 characters. -/
def w011 : Str := [58, 123, 39, 104, 65, 97]

/-- The regex of `regex-011-unsat-fuzz-graft-reverse.smt2`:
    `re.+ (re.* (str.to_re ":{'hAa"))`. -/
def r011 : Re := plus (.star (.lit w011))

/-- The structural modulus check succeeds with `k = 6` — kernel-decidable. -/
theorem r011_kdvd6 : kdvd 6 r011 = true := by decide

/-- **`regex-011-unsat-fuzz-graft-reverse` conflict, for EVERY symbolic `x`.**
    No string of length 4 lies in `re.+ (re.* (str.to_re ":{'hAa"))`. -/
theorem regex011_no_model (x : Str) (hm : Mem r011 x) (hlen : len x = 4) : False :=
  regex_len_mod_conflict r011_kdvd6 hm hlen (by decide)

/-- Non-vacuity: the language is genuinely inhabited — `w011 ++ w011` (length
    12) IS a member, so `regex011_no_model` is not refuting an empty language. -/
theorem r011_inhabited : Mem r011 (w011 ++ w011) := by
  have h1 : Mem (.star (.lit w011)) (w011 ++ w011) :=
    .starCat (.lit w011) (by
      have : Mem (Re.star (.lit w011)) (w011 ++ ([] : Str)) :=
        .starCat (.lit w011) .starNil
      simpa using this)
  have h2 : Mem (.cat (.star (.lit w011)) (.star (.star (.lit w011))))
      ((w011 ++ w011) ++ ([] : Str)) := .cat h1 .starNil
  simpa [plus, r011] using h2

/-- And that inhabitant has length 12, which IS divisible by 6 — confirming the
    invariant is tight, not trivially true. -/
theorem r011_inhabitant_len : len (w011 ++ w011) = 12 := by decide

/-- The `regex-002-unsat-fuzz.smt2` shape (`x = "sRZQaaEFa"` (9 chars),
    `x ∈ re.+ (str.to_re "ed")`), reduced to its length projection: 2 ∤ 9. -/
def wEd : Str := [101, 100]

/-- `re.+ (str.to_re "ed")` has modulus 2. -/
theorem red_kdvd2 : kdvd 2 (plus (.lit wEd)) = true := by decide

/-- **`regex-002-unsat-fuzz` conflict**: no member of `re.+ (str.to_re "ed")`
    has length 9. -/
theorem regex002_no_model (x : Str) (hm : Mem (plus (.lit wEd)) x)
    (hlen : len x = 9) : False :=
  regex_len_mod_conflict red_kdvd2 hm hlen (by decide)

/-- A "too short" witness for the complementary lemma:
    `re.++ (str.to_re "abc") (re.+ (str.to_re "de"))` has `minLen = 3 + 2 = 5`,
    so no member has length 4. -/
def rShort : Re := .cat (.lit [97, 98, 99]) (plus (.lit [100, 101]))

theorem rShort_minLen : minLen rShort = 5 := by decide

theorem rShort_no_model (x : Str) (hm : Mem rShort x) (hlen : len x = 4) : False :=
  regex_len_min_conflict hm hlen (by decide)

/-! ### `regex-019-unsat-multiply-multiply-graft` — the finite-language shape.

    (assert (str.in_re x (str.to_re "....")))
    (assert (= (str.len x) 20))

`str.to_re "...."` is the singleton `{"...."}`, so `maxLen = some 4 < 20`.
The modular check alone does NOT close this (4 ∣ 20); the max-length invariant
is what refutes it. -/

/-- `"...."` as codepoints — 4 characters. -/
def wDots : Str := [46, 46, 46, 46]

theorem rDots_maxLen : maxLen (.lit wDots) = some 4 := by decide

/-- **`regex-019-unsat-multiply-multiply-graft` conflict** for every symbolic
    `x`: no member of `str.to_re "...."` has length 20. -/
theorem regex019_no_model (x : Str) (hm : Mem (.lit wDots) x)
    (hlen : len x = 20) : False :=
  regex_len_max_conflict rDots_maxLen hm hlen (by decide)

/-! ### Inequality witnesses (the `regex_len_min_conflict_le` /
`regex_len_max_conflict_ge` firing conditions, instantiated). -/

/-- `re.++ (str.to_re "abc") (re.+ (str.to_re "de"))` has `minLen = 5`, so
    `(< (str.len x) 5)` — normalised to `len x ≤ 4` — is refuted. -/
theorem rShort_no_model_lt (x : Str) (hm : Mem rShort x) (hlen : len x < 5) :
    False :=
  regex_len_min_conflict_le hm (b := 4) (by omega) (by decide)

/-- `str.to_re "...."` has `maxLen = some 4`, so `(> (str.len x) 4)` —
    normalised to `5 ≤ len x` — is refuted. -/
theorem regex019_no_model_gt (x : Str) (hm : Mem (.lit wDots) x)
    (hlen : 4 < len x) : False :=
  regex_len_max_conflict_ge rDots_maxLen hm (b := 5) (by omega) (by decide)

/-! ## `re.loop` / `re.^` are DELIBERATELY ABSENT.

The SMT-LIB indexed identifiers `(_ re.loop n m)` and `(_ re.^ n)` have no
constructor here and no `kdvd`/`minLen`/`maxLen` extension is proved for them
(their `n > m` case denotes the EMPTY language, which the `minLen` rule for a
bounded repetition would get wrong).  An emitter must DECLINE on them rather
than desugar them into `cat`/`star`; see the `re.loop` decline test in
`crates/ay-dpll/src/executor/lean_firewall_tests.rs`.  `re.comp` and `re.diff`
are absent for the same reason (no sound one-sided length rule). -/

/-! ## Axiom audit — REQUIRED to be ⊆ {propext, Classical.choice, Quot.sound}.

Deliberately not run here: this module is EMBEDDED verbatim into the standalone
sources the runtime firewall gate kernel-checks, and that gate parses the LAST
`#print axioms` report before its sentinel.  The audit for each theorem is run
by `verification/lean/AySoundness/Audit.lean` and by the emitted artifacts
themselves. -/

end AySoundness.RegexThy
