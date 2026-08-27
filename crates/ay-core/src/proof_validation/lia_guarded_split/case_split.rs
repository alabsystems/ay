// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// The guarded-split rule's CASE-ANALYSIS arms, `include!`d into
// `lia_guarded_split.rs` so both files stay inside the quality gate's
// per-file size limit. Every item here is private to that module and shares
// its soundness argument verbatim; nothing is re-exported.

/// Whether the base rows ALONE are already infeasible over ℤ — the zero-split
/// case of the same argument.
///
/// `¬C` entails every base row, so refuting the base rows refutes `¬C` and the
/// clause is valid; no case analysis is involved and none is claimed. The arm
/// is guarded on the presence of an EQUALITY row because that is the only
/// thing [`branch_refuted`] brings over the cheaper
/// [`super::lia_cut_lattice`] rule every caller has already asked: both
/// lattice rules skip equality literals entirely (`parse_int_bound` returns
/// `None` for `=`), so a clause whose parity lives in its equalities has no
/// other route. Without an equality row this degenerates to that rule and is
/// declined here rather than recomputed.
fn equality_substitution_refutes(base: &Base) -> bool {
    // Equality literals do not pass through `parse_base`'s row cap (they
    // `continue` before it), so the substitution round count is bounded here
    // instead. Declined OUTRIGHT rather than truncated: a truncated row set
    // would make acceptance depend on literal order.
    if base.rows.eqs.is_empty() || base.rows.len() > MAX_GUARDED_ROWS {
        return false;
    }
    branch_refuted(base.rows.clone())
}

/// Whether some POSITIVE integer `=` literal's two ℤ branches are BOTH
/// refuted by the base rows.
///
/// `¬C` contains `A ≠ B`, i.e. `form ≠ bound`, which over ℤ holds exactly when
/// `form ≥ bound+1` or `form ≤ bound−1`. If the base rows refute both, `¬C` is
/// unsatisfiable and `C` is valid — the same contrapositive the `or` arm uses,
/// with a two-branch split that needs no disjunction in the clause.
fn disequality_split_refutes(base: &Base) -> bool {
    // Work bound, order-independent: a clause carrying more disequality
    // candidates than the `or` arm's disjunct cap declines this arm OUTRIGHT
    // rather than trying a prefix, so acceptance can never depend on literal
    // order. The `or` arm is unaffected.
    if base.diseq_splits.len() > MAX_SPLIT_DISJUNCTS {
        return false;
    }
    'candidate: for eq in &base.diseq_splits {
        for branch in disequality_branches(eq) {
            let mut rows = base.rows.clone();
            rows.eqs.extend(branch.eqs);
            rows.ges.extend(branch.ges);
            if rows.len() > MAX_GUARDED_ROWS {
                continue 'candidate;
            }
            if !branch_refuted(rows) {
                continue 'candidate;
            }
        }
        return true;
    }
    false
}

/// The two ℤ branches of `form ≠ bound`, each of which must be refuted.
fn disequality_branches(eq: &EqRow) -> Vec<Rows> {
    let one = BigInt::from(1);
    let above = GeRow {
        form: eq.form.clone(),
        bound: &eq.bound + &one,
    };
    let below = GeRow {
        form: eq.form.iter().map(|(v, c)| (*v, -c)).collect(),
        bound: -&eq.bound + &one,
    };
    vec![
        Rows {
            eqs: Vec::new(),
            ges: vec![above],
        },
        Rows {
            eqs: Vec::new(),
            ges: vec![below],
        },
    ]
}

/// The row sets under which one disjunct HOLDS; every returned branch must be
/// refuted. `None` fails the whole candidate `or` (the disjunct cannot be
/// modelled exactly, so nothing about the split may be concluded).
fn disjunct_branches(terms: &TermStore, disjunct: TermId) -> Option<Vec<Rows>> {
    match terms.get(disjunct) {
        // A `false` disjunct has no satisfying assignment: vacuously refuted.
        TermData::Const(crate::term::Constant::Bool(false)) => Some(Vec::new()),
        TermData::Not(inner) => {
            let inner = *inner;
            match terms.get(inner) {
                TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
                    // Disequality over ℤ: exactly `F ≥ b+1` or `F ≤ b−1`.
                    let (a, b) = (args[0], args[1]);
                    let eq = int_equality_row(terms, a, b)?;
                    Some(disequality_branches(&eq))
                }
                _ => {
                    // `(not cmp)` holds ⟺ `cmp` is FALSE.
                    let (coeffs, is_upper, value) =
                        super::lia::parse_int_comparison_row(terms, inner, false)?;
                    Some(vec![Rows {
                        eqs: Vec::new(),
                        ges: vec![ge_row(coeffs, is_upper, value)],
                    }])
                }
            }
        }
        TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
            let eq = int_equality_row(terms, args[0], args[1])?;
            Some(vec![Rows {
                eqs: vec![eq],
                ges: Vec::new(),
            }])
        }
        _ => {
            // A positive comparison holds ⟺ it is TRUE.
            let (coeffs, is_upper, value) =
                super::lia::parse_int_comparison_row(terms, disjunct, true)?;
            Some(vec![Rows {
                eqs: Vec::new(),
                ges: vec![ge_row(coeffs, is_upper, value)],
            }])
        }
    }
}

/// `a = b` over all-`Int` operands as an [`EqRow`], or `None`.
fn int_equality_row(terms: &TermStore, a: TermId, b: TermId) -> Option<EqRow> {
    let (form, constant) = super::lia::int_linear_diff(terms, a, b)?;
    // a − b = form + constant, so a = b ⟺ form = −constant.
    Some(EqRow {
        form,
        bound: -constant,
    })
}
