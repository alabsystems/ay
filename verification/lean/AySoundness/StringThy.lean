/-
  Soundness of the theory of strings / sequences (QF_S): length and content
  axioms (the development design notes; the string-theory validator).

  ay reasons about strings (and, more generally, sequences) through a small core
  of axioms over the length and concatenation operators plus positional access:

    * LEN-CAT      `len (s ++ t) = len s + len t`           (length is a monoid hom);
    * LEN-ZERO     `len s = 0 ↔ s = ε`                       (empty-string charact.);
    * CAT-NIL      `s ++ ε = s`  and  CAT-ASSOC  `(s ++ t) ++ u = s ++ (t ++ u)`
                                                            (concatenation is a monoid);
    * CHARAT-CAT   for `i < len s`, `(s ++ t)[i] = s[i]`     (content / positional axiom).

  A theory conflict that uses ONLY instances of these axioms (plus congruence /
  equality reasoning) is sound iff the axioms hold in the intended model. We fix
  the *standard sequence model* — a string is the free monoid `List Nat` of
  character codepoints, `len` is `List.length`, `++` (`cat`) is list append, and
  positional read is `getElem?` — and prove every axiom holds there. Hence any
  propositionally-derived conflict built from these axiom instances refutes a
  genuinely unsatisfiable constraint set: the model is forced, and the axioms are
  valid (`string_axioms_sound`).

  We prove the soundness PRINCIPLE (`string_axioms_sound`): in the standard model
  the axioms are simultaneously valid; the per-problem grounding (which string is
  which) is the solver's congruence closure. We also refute two concrete
  conflicts (`len_zero_nonnil_conflict`, `len_cat_conflict`) and exhibit a
  decidable positional witness, mirroring the `farkas_sound` (principle) +
  concrete-`decide` example split of `Farkas.lean` / `ArrayThy.lean`.

  Pure Lean 4 core (no Mathlib). The model definitions mirror the standard list
  semantics used by ay's string / sequence decision procedure.
-/
namespace AySoundness.StringThy

/-! ## The standard sequence model.

A string is the free monoid of character codepoints. We take codepoints to be
`Nat` (any decidable, infinite alphabet works the same way); a string is a
`List Nat`, so the empty string is `[]`, concatenation is `++`, and length is
`List.length`. This is the canonical model ay's QF_S decision procedure is proved
sound against. -/

/-- A string: a finite sequence of character codepoints. -/
abbrev Str := List Nat

/-- `len s` is the number of characters in `s`. -/
def len (s : Str) : Nat := s.length

/-- `cat s t` concatenates `s` and `t` (the monoid operation). -/
def cat (s t : Str) : Str := s ++ t

/-- The empty string `ε`. -/
def empty : Str := []

/-- `charAt s i` reads the codepoint at position `i`, `none` when out of range —
    the standard partial positional access (`s[i]?`). -/
def charAt (s : Str) (i : Nat) : Option Nat := s[i]?

/-! ## The length axioms. -/

/-- **LEN-CAT.** Length is additive over concatenation:
    `len (s ++ t) = len s + len t`. The core arithmetic link ay uses to relate a
    string's length to the lengths of its parts. -/
theorem len_cat (s t : Str) : len (cat s t) = len s + len t := by
  simp [len, cat, List.length_append]

/-- **LEN-ZERO.** A string has length zero iff it is the empty string. This is
    the empty-string characterization the solver uses to discharge
    `len s = 0`-style literals. -/
theorem len_zero_iff (s : Str) : len s = 0 ↔ s = empty := by
  simp [len, empty, List.length_eq_zero_iff]

/-! ## The monoid axioms for concatenation. -/

/-- **CAT-NIL (right unit).** `ε` is a right identity: `s ++ ε = s`. -/
theorem cat_nil (s : Str) : cat s empty = s := by
  simp [cat, empty]

/-- **CAT-NIL (left unit).** `ε` is a left identity: `ε ++ s = s`. -/
theorem nil_cat (s : Str) : cat empty s = s := by
  simp [cat, empty]

/-- **CAT-ASSOC.** Concatenation is associative:
    `(s ++ t) ++ u = s ++ (t ++ u)`. -/
theorem cat_assoc (s t u : Str) : cat (cat s t) u = cat s (cat t u) := by
  simp [cat, List.append_assoc]

/-! ## The content / positional axiom. -/

/-- **CHARAT-CAT (left).** Reading a position inside the left operand of a
    concatenation ignores the right operand: for `i < len s`,
    `(s ++ t)[i]? = s[i]?`. This is ay's content axiom that propagates a known
    character of `s` to the same position of `s ++ t`. -/
theorem charAt_cat_left (s t : Str) (i : Nat) (h : i < len s) :
    charAt (cat s t) i = charAt s i := by
  simp only [charAt, cat]
  exact List.getElem?_append_left (by simpa [len] using h)

/-- **CHARAT-CAT (right).** The dual: reading past the left operand reads the
    right operand at the shifted index: for `len s ≤ i`,
    `(s ++ t)[i]? = t[i - len s]?`. Stated for completeness of the positional
    characterization. -/
theorem charAt_cat_right (s t : Str) (i : Nat) (h : len s ≤ i) :
    charAt (cat s t) i = charAt t (i - len s) := by
  simp only [charAt, cat]
  exact List.getElem?_append_right (by simpa [len] using h)

/-! ## The soundness principle.

`string_axioms_sound` packages the core string axioms as a single validity
statement: for the standard `len` / `cat` / `charAt`, every axiom holds for all
strings, positions and characters. This is the theory content the QF_S validator
relies on, so any conflict built solely from these axiom instances is sound. -/

/-- **String theory soundness.** In the standard sequence model the core QF_S
    axioms — length-additivity, the empty-string characterization, the
    concatenation monoid laws, and the left content axiom — hold simultaneously.
    A conflict that uses only these axiom instances therefore refutes a genuinely
    unsatisfiable constraint set. -/
theorem string_axioms_sound :
    (∀ s t : Str, len (cat s t) = len s + len t) ∧
    (∀ s : Str, len s = 0 ↔ s = empty) ∧
    (∀ s : Str, cat s empty = s) ∧
    (∀ s : Str, cat empty s = s) ∧
    (∀ s t u : Str, cat (cat s t) u = cat s (cat t u)) ∧
    (∀ (s t : Str) (i : Nat), i < len s → charAt (cat s t) i = charAt s i) :=
  ⟨len_cat, len_zero_iff, cat_nil, nil_cat, cat_assoc, charAt_cat_left⟩

/-! ## Conflict abstraction.

ay represents the result of a string decision as: a set of length / content
literals is UNSAT. We discharge each conflict shape from the axioms above so a
kernel-checked `False` witnesses the soundness of the emitted conflict — mirroring
the `farkas_sound` / `array_axioms_sound` principles. -/

/-- **Empty-string conflict.** The literal set `{ len s = 0, s ≠ ε }` is
    unsatisfiable: from `len s = 0` the empty-string characterization forces
    `s = ε`, contradicting `s ≠ ε`. -/
theorem len_zero_nonnil_conflict (s : Str) : ¬ (len s = 0 ∧ s ≠ empty) := by
  rintro ⟨hlen, hne⟩
  exact hne ((len_zero_iff s).mp hlen)

/-- **Length-additivity conflict.** The literal `len (s ++ t) ≠ len s + len t`
    is unsatisfiable: ay's length-arithmetic conflict over a concatenation is
    sound. -/
theorem len_cat_conflict (s t : Str) : ¬ (len (cat s t) ≠ len s + len t) :=
  fun h => h (len_cat s t)

/-- **Content conflict.** With `i < len s`, the literal
    `(s ++ t)[i]? ≠ s[i]?` is unsatisfiable: ay's character-propagation conflict
    is sound. -/
theorem charAt_cat_conflict (s t : Str) (i : Nat) (h : i < len s) :
    ¬ (charAt (cat s t) i ≠ charAt s i) :=
  fun hne => hne (charAt_cat_left s t i h)

/-! ## Concrete, kernel-checked, NON-vacuous examples.

Each refutes a *real* conflict over concrete ground strings; the contradictions
are discharged by pure-kernel `decide` on the decidable `List`/`Option`
equalities. The strings are non-empty over a non-trivial alphabet so the
witnesses are not vacuous. -/

/-- The string `"AB"` encoded as codepoints `[65, 66]`. -/
def sAB : Str := [65, 66]
/-- The string `"C"` encoded as the codepoint `[67]`. -/
def sC : Str := [67]

/-- Concrete empty-string conflict: `[65, 66]` has length `2 ≠ 0`, so the literal
    `len sAB = 0` is itself refutable, hence the conflict `len sAB = 0 ∧ sAB ≠ ε`
    cannot hold. -/
theorem ex_len_zero_conflict : ¬ (len sAB = 0) := by decide

/-- The same via the general principle: `sAB ≠ ε` is decidably true, so the pair
    `{ len sAB = 0, sAB ≠ ε }` is refuted by `len_zero_nonnil_conflict`. -/
theorem ex_len_zero_via_principle : ¬ (len sAB = 0 ∧ sAB ≠ empty) :=
  len_zero_nonnil_conflict sAB

/-- Concrete length-additivity fact: `len (sAB ++ sC) = 3 = 2 + 1 = len sAB + len sC`.
    Kernel-checked, so the conflict `len (cat sAB sC) ≠ len sAB + len sC` is refuted. -/
theorem ex_len_cat_value : len (cat sAB sC) = len sAB + len sC := by decide

/-- Concrete content fact: position `1 < len sAB` reads `66` ("B") in both
    `sAB` and `sAB ++ sC`, so the content conflict `(sAB ++ sC)[1]? ≠ sAB[1]?`
    is refuted. The read value `some 66` is non-trivial. -/
theorem ex_charAt_cat_value : charAt (cat sAB sC) 1 = charAt sAB 1 := by decide

/-- And the same content fact follows from the general principle (not just
    `decide`): with the side condition `1 < len sAB` discharged by `decide`. -/
theorem ex_charAt_cat_via_principle : charAt (cat sAB sC) 1 = charAt sAB 1 :=
  charAt_cat_left sAB sC 1 (by decide)

/-- Non-vacuity witness for the read: the character actually read is `some 66`,
    a concrete codepoint, confirming `charAt` is not constantly `none`. -/
theorem ex_charAt_value : charAt (cat sAB sC) 1 = some 66 := by decide

end AySoundness.StringThy