// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl ExactLp {
    /// Algebraic pivot: `entering` (nonbasic, in row `ri`) becomes basic,
    /// the row's current basic leaves. Values are not touched.
    ///
    /// Dispatches on the representation in force and, under [`Form::Reduced`],
    /// closes the census window that may switch it.
    pub(super) fn pivot(&mut self, ri: usize, entering: u32) {
        #[cfg(test)]
        probe::tick();
        match self.form {
            Form::Reduced => {
                self.pivot_reduced(ri, entering);
                if !self.poisoned {
                    self.close_window();
                }
            }
            Form::FractionFree => self.pivot_fraction_free(ri, entering),
        }
    }

    /// The REDUCED pivot: one fully reduced [`Rational`] per entry, exactly as
    /// the rim has always done it. `den` is 1 on every row here, so the stored
    /// values are the coefficients and nothing reads a divisor.
    fn pivot_reduced(&mut self, ri: usize, entering: u32) {
        let row = &self.rows[ri];
        let leaving = row.basic;
        let Some(c_e) = row.numer_of(entering).cloned() else {
            debug_assert!(false, "pivot: entering not in row");
            self.poisoned = true;
            return;
        };
        // `det B' = det B · c_re`: the pivot swaps one column of the basis, and
        // the determinant scales by the entering column's coefficient in the
        // pivot row. Carried so the switch has a divisor to convert to.
        if self.convertible {
            self.det = self.det.clone() * c_e.clone().abs();
        }
        let row = &self.rows[ri];
        // x_e = (1/c_e)·x_leaving − Σ_{k≠e} (c_k/c_e)·x_k
        let inv = Rational::new(1, 1) / c_e;
        let mut new_terms: Vec<(u32, Rational)> = Vec::with_capacity(row.terms.len());
        for (v, c) in &row.terms {
            if *v == entering {
                continue;
            }
            new_terms.push((*v, -(c.clone() * inv.clone())));
        }
        new_terms.push((leaving, inv));
        new_terms.sort_unstable_by_key(|&(v, _)| v);
        let new_row = TabRow {
            basic: entering,
            terms: new_terms,
            den: Rational::new(1, 1),
        };
        // Substitute x_e in every other row.
        for rj in 0..self.rows.len() {
            if rj == ri {
                continue;
            }
            let d = match self.rows[rj].numer_of(entering) {
                Some(d) => d.clone(),
                None => continue,
            };
            let substituted = substitute(&self.rows[rj].terms, entering, &d, &new_row.terms);
            #[cfg(test)]
            probe::census(&substituted);
            self.census(&substituted);
            self.rows[rj].terms = substituted;
        }
        self.basic_of[leaving as usize] = None;
        self.basic_of[entering as usize] = Some(ri as u32);
        #[cfg(test)]
        probe::census(&new_row.terms);
        self.census(&new_row.terms);
        self.rows[ri] = new_row;
    }

    /// Census a row a pivot just rewrote: how many of its entries stayed on the
    /// inline `i64` path. THE SWITCH'S ONLY INPUT.
    ///
    /// SAMPLED, one row in [`SWITCH_SAMPLE_STRIDE`], because the signal is a
    /// SHARE and a share does not need every entry — it needs enough of them,
    /// and one window is thousands even at a stride of eight. MEASURED, and
    /// the reason the stride exists: counting EVERY entry cost the reduced
    /// class 1-2.5%, and the cost tracked entries rather than pivots (`qiu`,
    /// 2.09 BILLION entries over 9,189 pivots, 2.5%; `qnet1`, 406M entries
    /// over 40,000 pivots, 0.6%) — which is what says the census was paying
    /// per entry and could stop.
    ///
    /// The counter is NOT reset per pivot, so the sampled rows drift with the
    /// number of rows each pivot happens to touch rather than landing on the
    /// same eight-row lattice every time. It is still exactly reproducible:
    /// the same solve samples the same rows.
    #[inline]
    fn census(&mut self, terms: &[(u32, Rational)]) {
        if !self.convertible {
            return;
        }
        self.census_seq += 1;
        if !self.census_seq.is_multiple_of(SWITCH_SAMPLE_STRIDE) {
            return;
        }
        let inline = terms.iter().filter(|(_, c)| c.is_small()).count() as u64;
        self.window_entries += terms.len() as u64;
        self.window_inline += inline;
    }

    /// End of a census window: decide, in integer arithmetic, whether the
    /// tableau has left the inline path for good.
    ///
    /// DETERMINISTIC — the inputs are a pivot count and two entry counts, all
    /// of them functions of the tableau alone. No wall clock, no allocator
    /// state, no thread. Two runs of the same solve switch at the same pivot,
    /// which is what a certification path requires: the verdict must not
    /// depend on the machine that produced it.
    fn close_window(&mut self) {
        if !self.convertible {
            return;
        }
        // A/B override, test builds only: the shipped policy has no input but
        // the census below.
        #[cfg(test)]
        match probe::force() {
            1 => return,
            2 => {
                self.convert_to_fraction_free();
                return;
            }
            _ => {}
        }
        let (window, percent, sustain) = switch_params();
        self.window_pivots += 1;
        if self.window_pivots < window {
            return;
        }
        // `inline·100 < entries·PERCENT` — the share test without a division
        // and without a float.
        let cold =
            self.window_entries > 0 && self.window_inline * 100 < self.window_entries * percent;
        self.window_pivots = 0;
        self.window_entries = 0;
        self.window_inline = 0;
        if cold {
            self.cold_windows += 1;
            if self.cold_windows >= sustain {
                self.convert_to_fraction_free();
            }
        } else {
            self.cold_windows = 0;
        }
    }

    /// THE CONVERSION: rewrite every row as integers over the shared divisor
    /// `Δ = |det B|`. One pass, one multiply per entry — a single pivot's worth
    /// of work, paid once.
    ///
    /// WHY IT IS VERDICT-NEUTRAL BY CONSTRUCTION. The stored pair `(t, den)`
    /// denotes `t/den`, and every entry is rewritten to `(Δ·c, Δ)`, which
    /// denotes `Δ·c/Δ = c`: the tableau's COEFFICIENTS are not touched, only
    /// how they are spelled. Nothing else in the rim is touched at all —
    /// `values`, `lower`, `upper`, `basic_of` and the basis are untouched, and
    /// the objective row `d` holds true coefficients in both forms. Every
    /// decision downstream (Bland's index scan, the sign tests, the ratio
    /// test, the certificate multipliers) reads coefficients through
    /// [`coefficient`], so it sees the same exact rationals it would have seen
    /// had the conversion not happened, and the solve continues along the same
    /// pivot sequence to the same optimum.
    ///
    /// WHY THE ARITHMETIC AFTER IT IS EXACT. `Δ = |det B|` for the current
    /// basis of the INTEGER matrix `[ΛA | −I]`, so `Δ·c = ±adj(B)·[ΛA | −I]`
    /// is integral — the entries this writes really are integers, and the
    /// identity `t' = ±(t_ik·p − t_ie·t_rk)/den_i` that
    /// [`Self::pivot_fraction_free`] runs afterwards divides exactly for the
    /// same reason (see [`fraction_free`]). Both facts are CHECKED anyway:
    /// integrality here and every later division by `div_rem`, each with the
    /// same poison — the rim withholds the verdict rather than report one it
    /// has just caught its own arithmetic failing to justify. Rewriting IN
    /// PLACE (rather than into a second copy of the tableau that could be
    /// thrown away) is what that choice buys: no instance pays a doubled peak
    /// for a branch that cannot be taken.
    fn convert_to_fraction_free(&mut self) {
        debug_assert!(self.convertible);
        let delta = self.det.clone();
        if is_unit(&delta) {
            // Nothing to gain: `Δ = 1` means the tableau is ALREADY integral
            // (`1·c = ±adj(B)·[ΛA | −I]`), and integers over 1 is the reduced
            // form. There is no rewrite to do, only a name to change.
            return;
        }
        for row in &mut self.rows {
            for (_, c) in &mut row.terms {
                let t = c.clone() * delta.clone();
                if !is_integral(&t) {
                    debug_assert!(false, "det B · tableau entry must be integral");
                    self.poisoned = true;
                    return;
                }
                *c = t;
            }
            row.den = delta.clone();
        }
        self.form = Form::FractionFree;
        #[cfg(test)]
        probe::switched();
    }

    /// The FRACTION-FREE pivot (Bareiss). The pivot row is first brought to the
    /// current divisor `Δ` (a no-op unless it is stale), which makes
    /// `p = Δ·t_re` and lets the whole step be written with ONE division per
    /// entry, by the divisor the row being rewritten already carries:
    ///
    /// ```text
    ///   s = sign(p),  Δ' = |p|
    ///   t'_ik        = s·(t_ik·p − t_ie·t_rk) / den_i     (i ≠ r, t_ie ≠ 0)
    ///   t'_i,leaving = s·t_ie
    ///   t'_rk        = −s·t_rk,   t'_r,leaving = s·Δ
    /// ```
    ///
    /// and every rewritten row takes `den = Δ'`. WHY THE DIVISION IS EXACT: the
    /// numerator equals `den_i·Δ'·t'_ik`, and `Δ'·t'` is `±adj(B')·[ΛA | −I]`
    /// for the new basis — integral. A remainder therefore cannot happen, is
    /// checked for anyway, and poisons the solve rather than rounding.
    ///
    /// A row with `t_ie = 0` keeps its value, so it keeps its numerators and
    /// its (now older) divisor and is not visited at all.
    fn pivot_fraction_free(&mut self, ri: usize, entering: u32) {
        let leaving = self.rows[ri].basic;
        // Bring the pivot row to the current divisor. `Δ·t_r` is integral, so
        // this rescale is exact; it is skipped outright when the row is already
        // current, which is the common case.
        if self.rows[ri].den != self.det {
            let delta = self.det.clone();
            let stale = self.rows[ri].den.clone();
            for index in 0..self.rows[ri].terms.len() {
                let t = self.rows[ri].terms[index].1.clone();
                let Some(scaled) =
                    fraction_free::fused(&t, &delta, &Rational::zero(), &Rational::zero(), &stale)
                else {
                    self.poisoned = true;
                    return;
                };
                self.rows[ri].terms[index].1 = scaled;
            }
            self.rows[ri].den = delta;
            self.rows[ri].terms.retain(|(_, t)| !t.is_zero());
        }
        let Some(p) = self.rows[ri].numer_of(entering).cloned() else {
            debug_assert!(false, "pivot: entering not in row");
            self.poisoned = true;
            return;
        };
        let negative = p < Rational::zero();
        let delta = self.det.clone();
        let new_den = fraction_free::abs(&p);
        let pivot_terms = std::mem::take(&mut self.rows[ri].terms);
        let mut scratch: Vec<(u32, Rational)> = Vec::new();
        for rj in 0..self.rows.len() {
            if rj == ri {
                continue;
            }
            let Some(b) = self.rows[rj].numer_of(entering).cloned() else {
                continue;
            };
            scratch.clear();
            scratch.reserve(self.rows[rj].terms.len() + pivot_terms.len() + 1);
            let args = FuseRowArgs {
                row: &self.rows[rj].terms,
                pivot_row: &pivot_terms,
                entering,
                leaving,
                entering_coefficient: &b,
                pivot: &p,
                row_denominator: &self.rows[rj].den,
                current_denominator: &delta,
                negative,
            };
            if !fuse_row(args, &mut scratch) {
                self.poisoned = true;
                return;
            }
            #[cfg(test)]
            probe::census(&scratch);
            std::mem::swap(&mut self.rows[rj].terms, &mut scratch);
            self.rows[rj].den = new_den.clone();
        }
        // The pivot row itself: no division, only a sign and the old divisor in
        // the leaving column.
        let mut new_terms: Vec<(u32, Rational)> = Vec::with_capacity(pivot_terms.len());
        let mut placed = false;
        for (v, t) in &pivot_terms {
            if *v == entering {
                continue;
            }
            if !placed && *v > leaving {
                new_terms.push((leaving, signed_int(&delta, negative)));
                placed = true;
            }
            new_terms.push((*v, signed_int(t, !negative)));
        }
        if !placed {
            new_terms.push((leaving, signed_int(&delta, negative)));
        }
        #[cfg(test)]
        probe::census(&new_terms);
        self.rows[ri] = TabRow {
            basic: entering,
            terms: new_terms,
            den: new_den.clone(),
        };
        self.det = new_den;
        self.basic_of[leaving as usize] = None;
        self.basic_of[entering as usize] = Some(ri as u32);
    }

    /// Which tableau representation the solve ended in — measurement only.
    #[cfg(test)]
    pub(super) fn form_label(&self) -> &'static str {
        match (self.form, self.convertible) {
            (Form::Reduced, true) => "reduced",
            (Form::Reduced, false) => "reduced-locked",
            (Form::FractionFree, _) => "fraction-free",
        }
    }
}

/// `x` or `−x`.
#[inline]
fn signed_int(x: &Rational, negate: bool) -> Rational {
    if negate {
        -x.clone()
    } else {
        x.clone()
    }
}

/// One row of the fraction-free pivot: `out ← s·(row·p − b·prow)/delta` over
/// the union of the two rows' variables, minus the entering column, plus
/// `s·b` in the leaving column, where `delta` is THE ROW'S OWN divisor.
/// Sorted, zero-free, and integral throughout.
///
/// Returns `false` if any division left a remainder — the one thing that
/// cannot happen if the tableau is what the identity says it is, and the one
/// thing that must never be papered over.
struct FuseRowArgs<'a> {
    row: &'a [(u32, Rational)],
    pivot_row: &'a [(u32, Rational)],
    entering: u32,
    leaving: u32,
    entering_coefficient: &'a Rational,
    pivot: &'a Rational,
    row_denominator: &'a Rational,
    current_denominator: &'a Rational,
    negative: bool,
}

fn fuse_row(args: FuseRowArgs<'_>, out: &mut Vec<(u32, Rational)>) -> bool {
    let FuseRowArgs {
        row,
        pivot_row,
        entering,
        leaving,
        entering_coefficient: b,
        pivot: p,
        row_denominator: delta,
        current_denominator: current,
        negative,
    } = args;
    debug_assert!(
        !b.is_zero(),
        "fuse_row: row does not contain the entering column"
    );
    let zero = Rational::zero();
    // WHEN THE DIVISOR DOES NOT MOVE. `s·p = |p|`, so if `|p| = den_i` the
    // rescale factor `s·p/den_i` is exactly 1 and every entry OUTSIDE the
    // pivot row's support is unchanged: `t'_ik = s·(t_ik·p − 0)/den_i = t_ik`.
    // Those entries are then copied, not recomputed, which is what the reduced
    // form did for every row it touched.
    //
    // This is not a corner case. It is every pivot of a unimodular basis
    // (`|p| = den_i = 1`), which is what the network-shaped members of the
    // corpus are made of, and it is where a divisor that always moved cost
    // `dcmulti` 5.9x and `qnet1` 2.4x against the reduced form.
    let divisor_holds = fraction_free::abs(p) == *delta;
    // `t'_i,leaving = t_ie/t_re`, which at the new divisor `Δ' = |p|` is
    // `s·t_ie·Δ` — so the stored numerator is `s·b·Δ/den_i`, and it is `s·b`
    // only for a row already at `Δ`. (`b·Δ/den_i = Δ·t_ie` is integral, so the
    // division is exact, and it is checked like every other.)
    let leaving_coeff = if delta == current {
        signed_int(b, negative)
    } else {
        let Some(scaled) = fraction_free::fused(b, current, &zero, &zero, delta) else {
            return false;
        };
        signed_int(&scaled, negative)
    };
    let mut placed = false;
    let (mut i, mut j) = (0usize, 0usize);
    while i < row.len() || j < pivot_row.len() {
        let v = match (row.get(i), pivot_row.get(j)) {
            (Some(&(vi, _)), Some(&(vj, _))) => vi.min(vj),
            (Some(&(vi, _)), None) => vi,
            (None, Some(&(vj, _))) => vj,
            (None, None) => break,
        };
        let ti = match row.get(i) {
            Some((vi, t)) if *vi == v => {
                i += 1;
                t
            }
            _ => &zero,
        };
        let tj = match pivot_row.get(j) {
            Some((vj, t)) if *vj == v => {
                j += 1;
                t
            }
            _ => &zero,
        };
        if v == entering {
            continue;
        }
        if divisor_holds && tj.is_zero() {
            if !placed && leaving < v {
                out.push((leaving, leaving_coeff.clone()));
                placed = true;
            }
            out.push((v, ti.clone()));
            continue;
        }
        let Some(n) = fraction_free::fused(ti, p, b, tj, delta) else {
            return false;
        };
        if n.is_zero() {
            continue;
        }
        if !placed && leaving < v {
            out.push((leaving, leaving_coeff.clone()));
            placed = true;
        }
        out.push((v, signed_int(&n, negative)));
    }
    if !placed {
        out.push((leaving, leaving_coeff));
    }
    true
}
