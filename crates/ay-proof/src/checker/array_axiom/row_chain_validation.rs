// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Walk the maximal leading `store` spine of `term`, DEBITING one unit of work
/// per spine node so the measurement itself is bounded and fails closed.
///
/// This is the closure of the prepass under-charge hole. A free-walking
/// `store_chain_len` let `L` literals sharing ONE length-`N` chain perform
/// Θ(L·N) real spine walks while the structural formula priced only the MAXIMUM
/// spine length (`n_max = N`) — admitting unbounded work under a fixed envelope,
/// a DoS hole in a fail-closed resource bound. Charging per node makes the SUM
/// of all spine walks debit through the meter: the prepass's own walk of every
/// literal's sides, and — with the same-or-larger constant — [`matches_row_chain`]'s
/// single parse/eval re-walk of each of those same nodes (its sub-schema-(B)
/// cross-product MULTIPLICITY is priced separately by the caller).
/// `parse_store_chain` follows the same `args[0]` base spine, so this
/// upper-bounds the nodes any single parse visits; the interned term DAG is
/// acyclic, so the walk terminates.
fn metered_store_chain_len(
    terms: &TermStore,
    term: TermId,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<usize, ProofCheckError> {
    let mut len = 0usize;
    let mut current = term;
    while let TermData::App(sym, args) = terms.get(current) {
        if !matches!(sym, Symbol::Named(name) if name == "store") || args.len() != 3 {
            break;
        }
        // Debit THIS node before descending. 64 covers the prepass's own visit
        // plus `matches_row_chain`'s single parse+eval re-walk of the same node.
        if !progress(64, 0) {
            return Err(ProofCheckError::ResourceLimit);
        }
        len += 1;
        current = args[0];
    }
    Ok(len)
}

/// Debit the strict-check meter for the ACTUAL work
/// [`validate_array_row_chain`] is about to perform on `literals`, failing
/// closed if the caller's envelope cannot absorb it.
///
/// This is the row-chain half of the `ArrayClauseSchema` fix: instead of the
/// former up-front `~8 * unfolded_work^2` precharge (quadratic in chain length,
/// which withheld correctly-decided UNSATs on long but genuinely-linear chains),
/// the row-chain validator now charges a TIGHT upper bound on
/// [`matches_row_chain`]'s real cost — AND on the prepass's own measurement work
/// — through the same progress callback that `ResolutionRoute`/`Generic` lemmas
/// debit.
///
/// SOUNDNESS OF THE BOUND (it must never UNDER-charge — an unbounded check is a
/// DoS hole as severe as a wrong verdict). Let `L = literals.len()`.
///  * `64*L` up front covers `PositiveEqPairs::collect`, premise collection, the
///    per-literal classification, and the exact sub-schemas (C)-(I) — each gated
///    to `L ∈ {2,3,4}`.
///  * EVERY store spine any sub-schema could parse is walked here through
///    [`metered_store_chain_len`], which debits PER NODE. The SUM of those walks
///    — including `L` shared copies of one length-`N` chain, i.e. Θ(L·N) — is
///    therefore charged as it happens, and the same per-node walk also covers
///    `matches_row_chain`'s single parse/eval of each of those chains (sub-schema
///    (A) `matches_row_chain_eval` and the single premise parses).
///  * Sub-schema (B) `matches_row_chain_under_array_eq` re-walks each premise
///    chain candidates × orientations × 2 times PER select-bearing positive
///    equality — a multiplicity on top of the single per-node walk — plus a
///    cheap premise-loop pass per positive equality: `64*(pos_eq_all*premises +
///    pos_eq_with_select*premises*n_max)`.
///
/// `n_max` is the maximum store-spine length over every array term any parse
/// could reach, so no single premise re-walk in the (B) cross product exceeds it.
///
/// A genuine O(n) row-chain reduction has few literals, one chain, and
/// `premises` O(1), so the whole bound is O(n) and certifies cheaply. Both an
/// adversarial (B) cross product AND an adversarial shared-chain spine fan-out
/// are priced in full and refused.
fn charge_row_chain_validation(
    terms: &TermStore,
    literals: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    let mul = |a: usize, b: usize| a.checked_mul(b).ok_or(ProofCheckError::ResourceLimit);
    let add = |a: usize, b: usize| a.checked_add(b).ok_or(ProofCheckError::ResourceLimit);

    let l = literals.len();
    // Charge the linear per-literal scan BEFORE the spine walks, so an oversized
    // literal count fails closed up front.
    if !progress(mul(l, 64)?, mul(l, 4 * size_of::<TermId>())?) {
        return Err(ProofCheckError::ResourceLimit);
    }

    let mut pos_eq_all = 0usize;
    let mut pos_eq_with_select = 0usize;
    let mut premises = 0usize;
    let mut n_max = 0usize;

    // Classify each literal and measure every store spine any sub-schema could
    // parse. `metered_store_chain_len` debits PER NODE, so the SUM of all spine
    // walks — Θ(L·N) for `L` literals sharing one length-`N` chain — is charged
    // as it happens and fails closed, instead of being walked for free while the
    // formula prices only the maximum spine length.
    for &lit in literals {
        if let Some((lhs, rhs)) = equality_sides(terms, lit) {
            pos_eq_all += 1;
            let mut has_select = false;
            for side in [lhs, rhs] {
                n_max = n_max.max(metered_store_chain_len(terms, side, progress)?);
                if let Some((array, _)) = well_sorted_select_parts(terms, side) {
                    has_select = true;
                    n_max = n_max.max(metered_store_chain_len(terms, array, progress)?);
                }
            }
            if has_select {
                pos_eq_with_select += 1;
            }
        } else if let Some((left, right)) = negated_equality_sides(terms, lit) {
            for side in [left, right] {
                n_max = n_max.max(metered_store_chain_len(terms, side, progress)?);
                if let Some((array, _)) = well_sorted_select_parts(terms, side) {
                    n_max = n_max.max(metered_store_chain_len(terms, array, progress)?);
                }
            }
            if matches!(terms.sort(left), Sort::Array(_)) && terms.sort(left) == terms.sort(right) {
                premises += 1;
            }
        }
    }

    // Sub-schema (B): cheap premise-loop overhead per positive equality, plus the
    // expensive cross-product re-walks of premise chains. This multiplicity is
    // ON TOP of the single per-node spine walks already charged above.
    let cheap_b = mul(pos_eq_all, premises)?;
    let expensive_b = mul(mul(pos_eq_with_select, premises)?, n_max)?;
    let cross = mul(add(cheap_b, expensive_b)?, 64)?;
    // Peak transient scratch: the premise vector and positive-equality pair set
    // are O(L); one parsed store chain of ≤ n_max entries is live at a time.
    let bytes = mul(add(l, n_max)?, 4 * size_of::<(TermId, TermId)>())?;
    if !progress(cross, bytes) {
        return Err(ProofCheckError::ResourceLimit);
    }
    Ok(())
}

/// Validate an `ArrayRowChain` lemma in strict mode.
///
/// SCHEMA. Write `eval(C, x)` for the partial read-over-write evaluation of an
/// array term `C` at index `x`: walk `C`'s `store` chain OUTERMOST-FIRST; on an
/// entry `(i, v)` return `v` when `i` IS syntactically `x`, otherwise the
/// clause must carry a POSITIVE literal `(= x i)` (else `eval` FAILS and the
/// lemma is rejected) and the walk continues inward; when the chain is
/// exhausted the result is the term `(select base x)`. Every `store` node and
/// the final `select` must be well-sorted array operations.
///
/// The clause is accepted when either sub-schema holds:
///
/// (A) CHAIN EVALUATION. A POSITIVE literal `(= P Q)` where `P` is a well-
///     sorted `(select C x)` and `eval(C, x)` denotes exactly `Q` (or the
///     mirror image), and `sort(P) == sort(Q)`.
///
/// (B) UNDER AN ARRAY EQUALITY. A NEGATIVE literal `(not (= L R))` with
///     `sort(L) == sort(R) == Array(as)`, plus a POSITIVE literal `(= U W)`
///     with `sort(U) == sort(W) == as.element_sort`, and an index term `x` of
///     sort `as.index_sort` such that `eval(L, x)` denotes `U` and
///     `eval(R, x)` denotes `W` (or the mirror image). `x` is taken from a
///     top-level `(select _ x)` on either side of the conclusion literal; a
///     conclusion with no such select is REJECTED (the checker will not guess a
///     witness index).
///
/// (C) EQUAL STORES FORCE THE BASE ALIAS. Exactly four literals spell
///     `¬(A = store(B,i,v)) ∨ ¬(A = store(B,j,v)) ∨ i=j ∨ B=A`, modulo
///     equality orientation and literal order. The two store terms are exact
///     depth-one, well-sorted stores over the same `B` with the same `v`.
///
/// (D) EXACT SELECT CONGRUENCE. Exactly two literals spell
///     `not (= A B) OR (= (select A i) (select B i))`, modulo equality and
///     literal orientation. Both reads use the exact premise roots and the
///     same exact, well-sorted index. This is intentionally disjoint from (B):
///     it does not relax (B)'s requirement that at least one side perform a
///     genuine ROW reduction.
///
/// (E) EXACT CONST-ARRAY READ UNDER EQUALITY. Exactly two literals spell
///     `not (= A (const-array fill)) OR (= (select A i) fill)`, modulo equality
///     and literal orientation, with exactly one const-array side and an exact,
///     well-sorted read of the other premise root.
///
/// (F) EXACT STORE CONGRUENCE. Exactly two literals spell
///     `not (= A B) OR (= (store A i v) (store B i v))`, modulo equality and
///     literal orientation. The roots, index, and value are exact shared terms;
///     no chain peeling or equality side condition is consulted.
///
/// (G) EXACT STORE IDEMPOTENCE UNDER EQUALITY. Exactly two literals spell
///     `not (= A S) OR (= S (store A i v))`, where `S` is exactly the
///     depth-one, well-sorted term `(store B i v)`. All occurrences of `A`,
///     `S`, `i`, and `v` are exact shared terms.
///
/// (H) GUARDED MATCHING-OUTER-STORE READ. Exactly three literals spell
///     `i=k OR not (= (store A i v) (store C i v)) OR (= (select X k)
///     (select Y k))`.  `X` must be either the left outer store or its exact
///     base `A`, and `Y` must independently be either the right outer store or
///     its exact base `C` (modulo equality orientation).  The endpoints must
///     remain cross-side: two terms from the same store/base family are not
///     accepted by this sub-schema.
///
/// (I) EXACT SAME-INDEX STORE VALUE EQUALITY. Exactly two literals spell
///     `not (= (store X i v) (store Y i w)) OR (= v w)`, modulo equality and
///     literal orientation. Only the outermost `store` of each side is peeled,
///     both sides must write at the same exact index term `i`, and the two
///     bases `X`, `Y` are arbitrary and never inspected.
///
/// SOUNDNESS. Assume the clause false. Then every `(= x i)` literal consumed by
/// `eval` is false, i.e. `x != i`, so each skipped `store` is transparent at
/// `x` by the read-over-write-negative axiom and each taken entry gives its
/// value by read-over-write-positive: `select(C, x) = eval(C, x)`.
/// For (A) that already contradicts the assumed-false conclusion.
/// For (B) the negative literal being false gives `L = R`, so by congruence
/// `select(L, x) = select(R, x)`, i.e. `U = W` — again contradicting the
/// assumed-false conclusion. For (C), assuming both store equalities and
/// `i != j`, equality of the stores at `i` and `j` forces `B[i] = v` and
/// `B[j] = v`; therefore either write leaves `B` unchanged and `A = B`,
/// contradicting the final assumed-false equality. (D) is ordinary equality
/// congruence. In (E), the false negative premise identifies `A` with the
/// constant array, whose read is `fill`. (F) is ordinary congruence of the
/// well-sorted `store(_, i, v)` function. For (G), substituting `A=S` and the
/// same-index overwrite law give `store(A,i,v)=store(S,i,v)=S`. Extra literals
/// are harmless in (A)/(B). For (H), falsity of `i=k` gives `i != k`, so ROW
/// makes each outer store read equal to its base read at `k`; the false
/// negative premise and congruence make the two side families equal at `k`.
/// For (I), the false negative premise gives `store(X,i,v) = store(Y,i,w)`;
/// reading both sides at `i` and applying read-over-write-positive twice gives
/// `v = select(store(X,i,v), i) = select(store(Y,i,w), i) = w`, contradicting
/// the assumed-false conclusion. That derivation never mentions `X` or `Y`,
/// which is why they are unconstrained.
/// (C)/(D)/(E)/(F)/(G)/(H)/(I) are intentionally exact.
pub(crate) fn validate_array_row_chain(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    if clause.is_empty() {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "array axiom clause must be non-empty".to_string(),
        });
    }
    reject_non_bool_literals(terms, step_id, clause, "array read-over-write chain")?;

    let literals = flatten_clause_literals(terms, clause);
    reject_non_bool_literals(terms, step_id, &literals, "array read-over-write chain")?;
    // Debit the metered work bound (see [`charge_row_chain_validation`]) before
    // the schema search runs: a genuine O(n) row chain is cheap, an adversarial
    // clause that would drive the quadratic (B) cross product fails closed here.
    charge_row_chain_validation(terms, &literals, progress)?;
    if matches_row_chain(terms, &literals) {
        return Ok(());
    }
    Err(ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: "array read-over-write-chain clause does not match the exact schema: every \
                 store skipped while evaluating the chain at the read index must be justified \
                 by a positive `(= x i)` literal in the same clause, and the conclusion must be \
                 the evaluated equality (optionally under a `(not (= L R))` array-equality \
                 premise whose conclusion carries a top-level select at the read index)"
            .to_string(),
    })
}
