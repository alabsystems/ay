// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Finite-domain datatype → SAT lane (E13, milestone 1).
//!
//! Eager reduction of list-shaped QF_DT problems (the SMT-LIB
//! `20230720-blocksworld` family: enum blocks, a `Tower = stack(top, rest) |
//! empty` list, records of towers, BMC step relations over selectors and
//! testers) to ONE propositional CNF decided by `ay-sat`. Background: Shah,
//! Mora, Seshia, "An Eager Satisfiability Modulo Theories Solver for
//! Algebraic Datatypes", AAAI'24 (Algaroba); the design and its critique live
//! in the campaign notes (E13 DESIGN.md §4–§8 and the critic's F1–F4/S1–S8).
//!
//! # Fragment (precondition P1, checked by [`scan`] and [`signature`])
//!
//! Sorts are `Bool`, `Enum` (all constructors nullary), `Record` (one
//! constructor, fields of admitted sorts, non-recursive) and `List` (one cons
//! with exactly one recursive field whose other fields are enums, plus ONE
//! NULLARY nil). Terms are Boolean connectives, `=`, `distinct`, `ite`,
//! declared nullary constants, constructors, selectors and testers. Anything
//! else — sums with fields, several nils or nils with fields (critique F3/F4),
//! non-enum cell fields, mutual recursion, trees, UF with arguments,
//! arithmetic, quantifiers — declines the lane, and so do assumptions carried
//! apart from the assertions, and the absence of any list-sorted term.
//!
//! # Encoding
//!
//! Fix a cell count `D >= 1`. Every admitted term `t` gets a value whose
//! bits are NAMED BY THEIR CONTENT, a Boolean property of `t` in a model:
//! * an enum value is a one-hot row, bit `C` := "`t = C`";
//! * a list value is `D` cells; `s_i(t)` := "`t` has more than `i` cons
//!   cells" (`AND_{j<=i} is-cons(rest^j t)`), and the row bit `v_{i,f,C}(t)`
//!   := "`s_i(t)` and `f(rest^i t) = C`";
//! * a record value is the tuple of its fields' values;
//! * gate (Tseitin) and equality variables are named by their defining
//!   formula.
//!
//! Every value is CANONICAL (critique F1): absent cells carry all-false
//! bits, present cells exactly one bit per row, enum values exactly one bit;
//! cell rows are only ever enum rows, so no equality ever compares an
//! inactive-constructor encoding with an active one.
//!
//! # Theorem 1 (soundness of every UNSAT; no condition on `D`)
//!
//! *For every query φ admitted by the gate and every `D >= 1`: if the
//! emitted CNF `E_D(φ)` is propositionally unsatisfiable, then φ is
//! unsatisfiable in the SMT-LIB 2.6 theory of datatypes (selectors are total
//! functions; a selector applied to the wrong constructor denotes an
//! arbitrary but fixed value).*
//!
//! *Proof.* Let `M ⊨ φ`. Assign every variable of `E_D(φ)` the truth value
//! of its content in `M`. Every emitted clause is an instance of one of the
//! following schemas, each of which is TRUE IN EVERY MODEL OF φ under that
//! reading (most are true in every datatype model):
//! 1. *monotone cells* `s_i(t) -> s_{i-1}(t)` (more than `i` cells implies
//!    more than `i-1`); for a beyond-window cell `L` of `rest(x)`,
//!    `s(L) -> s_{D-1}(x)` is the same fact at index `D`;
//! 2. *cell well-formedness* `v -> s_i`, `s_i -> exactly-one(row)`: a
//!    present cell's field has exactly one value, an absent cell none;
//! 3. *constructor shift* `cons(e,u)`: cell 0 is `(TRUE, e)`, cell `i+1` is
//!    cell `i` of `u` (selector-of-constructor); the nil constant has no cell;
//! 4. *selectors*: under `is-cons(x)` the cells of `rest(x)` are the cells of
//!    `x` shifted by one and `f(x)` is cell 0's row; under `not is-cons(x)`,
//!    `x = nil` (exhaustiveness, ONE nullary nil), so `rest(x)` and `f(x)`
//!    equal the ONE shared value of `rest(nil)` / `f(nil)` (functionality);
//!    two applications of one selector to the same encoded value share one
//!    value, and two `rest` values of one kind whose arguments are both
//!    nil are equal, `s_0(x) | s_0(y) | e` (functionality again);
//!    record selectors are projections (one constructor);
//! 5. *list equality*, only `e -> ce_i` (equal lists have equal cells) and
//!    `(AND_i ce_i) & not s_{D-1}(a) -> e` (lists with fewer than `D` cells
//!    that agree cell by cell are the same finite term, by injectivity and
//!    distinctness); a deep/deep agreement leaves `e` FREE — this is the
//!    over-approximation;
//! 6. *finite equality, testers, one-hot rows*: `e <-> OR_C (a=C & b=C)`
//!    for enums, conjunction of fields for records, `is-C(x)` is a row bit
//!    or `s_0`;
//! 7. *Tseitin definitions* and the unit clauses of the asserted roots (true
//!    in `M` because `M ⊨ φ`); a root that is an enum domain closure
//!    `(or (= t C_1) .. (= t C_k))` over every constructor is valid, so it is
//!    left unasserted (φ minus a valid conjunct is equivalent to φ);
//! 8. *substitution* of an asserted top-level equality between two declared
//!    constants (they share one value; true in `M` because asserted);
//! 9. *muxes*: `ite(c,a,b)` and the wrong-constructor selector forms are
//!    bitwise if-then-else of canonical values (semantics of `ite`).
//! So the content assignment satisfies `E_D(φ)`, contradicting
//! unsatisfiability. ∎
//!
//! The theorem involves NO depth bound and NO completeness claim: `D` only
//! decides how often the lane answers, never whether an UNSAT is right. The
//! lane emits no acyclicity, bound, symmetry-breaking or invariant clause.
//! (A cyclic constraint such as `x = cons(A, x)` simply forces `x` deep at
//! every `D`; it is never refuted here.)
//!
//! *Why no bounded-completeness theorem is needed.* A depth-bounded
//! encoding that ASSERTS "every term has at most `D` cells" may answer UNSAT
//! only under a small-model theorem. This encoding never asserts it: a value
//! with more than `D` cells is represented by its first `D` cells with
//! `s_{D-1}` true, nothing constrains what lies beyond the window (the one
//! beyond-window cell of `rest(x)` is fresh, schema 1), and an equality
//! between two such deep values is left free (schema 5). Truncation
//! therefore only forgets facts, so every model of φ, of ANY depth, maps to
//! a model of `E_D(φ)` — which is exactly the proof above. The condition
//! "UNSAT is sound" thus holds for every `D >= 1` with no bound check; the
//! conditions that ARE checked are P1–P3 below, and `D` matters only for
//! SAT answers, which Lemma 3 re-checks against the original roots. (The
//! design's optional Theorem 2 "every term is shallow" mode is not part of
//! milestone 1, so no code path makes an UNSAT depend on `D`.)
//!
//! *Preconditions checked in code.* (P1) the gate admits every root, term and
//! sort before any clause is emitted ([`scan`], [`signature`]); (P2) the emitter produces
//! only schemas 1–9: one function per schema in [`values`] and [`encode`],
//! every shape mismatch declines instead of emitting, and the unit tests
//! carry a clause-validity oracle that checks every emitted clause under
//! the content reading of brute-forced models of small queries; (P3) the
//! verdict is a genuine `ay-sat` refutation of exactly that CNF.
//!
//! *What φ is.* φ is the solver-facing assertion vector `ctx.assertions`
//! of the command, i.e. the authored assertions after the executor's
//! preprocessing. The theorem makes the lane's UNSAT exactly as sound as
//! that vector is equisatisfiable with the authored script; the lane adds
//! no further assumption. A preprocessing pass that injects a root false in
//! some model of the script breaks this for EVERY lane, and is fixed at that
//! pass. The LNH symmetry pass did so (#dt-fd-lnh-ctor and the E13 audit's
//! l01..l06: it took nullary constructors and compound terms such as
//! `(hd l_i)` for interchangeable constants); on main it is off in every
//! posture (`lnh_symmetry::lnh_enabled()` is false). The pending domain
//! repair (fix/lnh-symmetry-domain) re-enables it only over declared free
//! constants (never a constructor or compound term) and only in a
//! non-incremental check, where its clauses are a symmetry reduction of that
//! one check's φ and so keep it equisatisfiable; this lane needs no LNH
//! refusal of its own under either, and no pass this lane runs after
//! injects such a root today.
//!
//! # Lemma 4 (guarded selectors; justifies compaction O2)
//!
//! *Let `u = sel(x)` be a selector of the cons constructor, and suppose
//! every occurrence of `u` in φ lies (i) in the then-branch of an `ite`
//! whose condition has `is-cons(x)` (or `not is-nil(x)`) as a top-level
//! conjunct, (ii) in an argument of an `and` another argument of which has
//! it, (iii) in an argument of an `or` another argument of which is the
//! negation of such a formula, or (iv) in the conclusion of an implication a
//! premise of which has it. Then replacing
//! every occurrence of `u` by `u' = ite(is-cons(x), u, d)` for a fixed
//! WELL-FORMED ground `d` (nil for `rest`, the first enum constructor for a
//! field) yields an equivalent φ'.* Proof: in (i), if the condition holds
//! then `u = u'`, otherwise the branch does not contribute; in (ii), if the
//! sibling is false both conjunctions are false, otherwise `u = u'`; in
//! (iii) and (iv), if the guard is false both disjunctions (implications)
//! are true, otherwise `u = u'`; the
//! equivalence of the guarding subformula propagates to the root through
//! any context. Applying the lemma to several selectors one at a time is
//! sound because the replacement maps contexts homomorphically (guards
//! become guards of the replaced terms). ∎ Theorem 1 is applied to φ'. The
//! guard analysis ([`guards`]) is syntactic over the exact roots; any
//! unguarded path, or exhausting its visit budget, keeps the general form.
//!
//! # Lemma 3 (SAT answers)
//!
//! A CNF model is decoded per declared constant (a deep list — all `D`
//! cells present — is completed with nil), the wrong-constructor
//! applications take the decoded shared values (or `d`), and the ORIGINAL
//! roots are evaluated with exact SMT-LIB semantics ([`decode`]). Only a
//! model that evaluates every root to true is handed to the executor's
//! validation pipeline and the independent gate. If no list value is deep,
//! every schema is exact and the decoded model satisfies φ, so a rejection
//! there is a lane defect: it fails closed (`dt_fd_lane=rejected-shallow`).
//! A rejection with a deep value is a spurious over-approximate model: `D`
//! doubles (at most [`MAX_ROUNDS`] times) or the lane gives up.
//!
//! A confirmed model is a TOTAL model of the admitted signature — the
//! constants' values plus the committed `rest(nil)` / `field_j(nil)` — and
//! is published whole (`model/lane_ground_model.rs`), so `(get-value)` of a
//! term the query never mentions, and the printed selector tables, read the
//! same model the evaluator accepted.
//!
//! # Postures
//!
//! The lane publishes its UNSAT as an unevidenced `competition-raw` verdict
//! exactly when `competition_shedding_active()` holds and no unsat core is
//! requested: `--z3-mode`, and also `--no-proof` and `--rigor fast` (the
//! "just the answer, like z3" rung). Every other posture (default,
//! `--proof`, `--strict-proofs`, `--self-check`, cores) uses the lane for SAT
//! only: its SEARCH runs under a small time cap (the cap never covers
//! publication, whose deadline polls are sticky), it falls through on
//! CNF-UNSAT (an UNSAT without checkable evidence would otherwise become a
//! final `unknown`), and it does not run at all in a certification re-solve
//! (`new_derived_query_executor`, which only reads UNSAT); it does run in the
//! forged-UNSAT guard's re-solve, which asks for SAT.
//!
//! The lane reads only `ctx.assertions`, so it declines while assumptions
//! are carried apart from them. A `check-sat-assuming` over a query its gate
//! admits runs it on the scoped window that merges the assumptions into the
//! assertions, BEFORE the direct DT assumption engine ([`assuming`]); that
//! window is an ordinary query, so the same theorems apply. A push/pop
//! session is no reason to decline: `ctx.assertions` is the whole scoped
//! stack at every check, and the lane keeps no state between commands
//! (#dt-fd-session).
//!
//! # Resources
//!
//! Each round's clause count is capped from the room left under the process
//! memory ceiling, the encoding polls memory as a backstop, the solver is
//! loaded only when its estimated arena fits, and its search stops short of
//! the ceiling ([`memory`]). Each is a decline, so the fallback lanes run
//! instead of the whole check-sat ending in `memout`.

mod assuming;
mod cnf;
mod decode;
mod driver;
mod encode;
mod export;
mod guards;
mod memory;
mod scan;
mod signature;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_regress;
#[cfg(test)]
mod tests_round3;
#[cfg(test)]
mod tests_round6;
mod values;

/// Deepening rounds after the first encoding.
const MAX_ROUNDS: usize = 4;
