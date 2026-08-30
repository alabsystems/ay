// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An independent cutting-planes interpreter with VeriPB's own semantics, used
//! by the structural OPT-LIN certifiers to PARSE THEIR OWN EMITTED BYTES BACK
//! and replay them before anything is returned.
//!
//! WHY THIS IS ONE MODULE AND NOT ONE PER CERTIFIER. The whole value of a
//! self-check is that it models what the CHECKER computes, not what the emitter
//! meant. `s`, `d` and `w` are defined on the NORMALIZED LITERAL form, and the
//! variable-form shortcut for them is a different (sound, but different)
//! operation — so a second, independently written copy of these rules is a
//! second chance to model the wrong semantics, in a file nobody diffs against
//! the first. `clique_coloring` and `frustrated_cycle` share this one
//! definition; if it is wrong, both self-checks fail loudly rather than one
//! quietly disagreeing with the other.
//!
//! Nothing here trusts the emitter: every row is rebuilt from the proof text
//! and the instance, and the arithmetic is exact `i128` with checked overflow
//! throughout (a wrapped coefficient is precisely how a "more trivially true
//! than its operands" row becomes an empty contradiction — see defects 9, 10
//! and 12 in `ci/veripb.pin`).

use std::collections::BTreeMap;

// ---------------------------------------------------------------------------
// Layer 4: an independent cutting-planes interpreter with VeriPB semantics.
// ---------------------------------------------------------------------------

/// `ceil(a / d)` for `d >= 1`, exact over `i128`.
pub(super) fn ceil_div(a: i128, d: i128) -> Option<i128> {
    if d < 1 {
        return None;
    }
    let q = a.checked_div_euclid(d)?;
    if a.checked_rem_euclid(d)? == 0 {
        Some(q)
    } else {
        q.checked_add(1)
    }
}

/// A `>=` constraint stored in VARIABLE form: `Σ coeff[v] * x_v >= rhs`, with
/// `x_v ∈ {0,1}` and zero coefficients never stored.
///
/// Addition and scaling are exact in this form. Saturation, division and
/// weakening are NOT — VeriPB defines those on the NORMALIZED LITERAL form (all
/// coefficients positive, `~x = 1 - x` folded into the degree), and the two
/// disagree on rows with negative coefficients. Each of those three operations
/// therefore converts to the normalized view, acts there, and converts back, so
/// this interpreter reproduces what the checker actually computes rather than a
/// merely-sound approximation of it. A self-check that modelled a *different*
/// (even if sound) semantics would not be evidence about the emitted bytes.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct CpRow {
    pub(super) coeff: BTreeMap<u32, i128>,
    pub(super) rhs: i128,
}

impl CpRow {
    pub(super) fn add_coeff(&mut self, var: u32, delta: i128) -> Option<()> {
        let slot = self.coeff.entry(var).or_insert(0);
        *slot = slot.checked_add(delta)?;
        if *slot == 0 {
            self.coeff.remove(&var);
        }
        Some(())
    }

    /// The degree of the normalized-literal view: `rhs + Σ_{c<0} |c|`.
    pub(super) fn norm_degree(&self) -> Option<i128> {
        let mut degree = self.rhs;
        for &c in self.coeff.values() {
            if c < 0 {
                degree = degree.checked_sub(c)?;
            }
        }
        Some(degree)
    }

    /// Rebuilds the variable form from normalized coefficients keyed by the sign
    /// pattern this row already has: `rhs = degree - Σ_{c<0} a_v`.
    pub(super) fn from_normalized(
        signs: &BTreeMap<u32, bool>,
        mags: BTreeMap<u32, i128>,
        degree: i128,
    ) -> Option<Self> {
        let mut out = CpRow {
            coeff: BTreeMap::new(),
            rhs: degree,
        };
        for (&var, &mag) in &mags {
            if mag == 0 {
                continue;
            }
            let negative = *signs.get(&var)?;
            if negative {
                out.coeff.insert(var, mag.checked_neg()?);
                out.rhs = out.rhs.checked_sub(mag)?;
            } else {
                out.coeff.insert(var, mag);
            }
        }
        Some(out)
    }

    pub(super) fn signs_and_mags(&self) -> Option<(BTreeMap<u32, bool>, BTreeMap<u32, i128>)> {
        let mut signs = BTreeMap::new();
        let mut mags = BTreeMap::new();
        for (&var, &c) in &self.coeff {
            signs.insert(var, c < 0);
            mags.insert(var, c.checked_abs()?);
        }
        Some((signs, mags))
    }

    pub(super) fn add(&self, other: &Self) -> Option<Self> {
        let mut out = self.clone();
        for (&var, &delta) in &other.coeff {
            out.add_coeff(var, delta)?;
        }
        out.rhs = out.rhs.checked_add(other.rhs)?;
        Some(out)
    }

    pub(super) fn scale(&self, k: i128) -> Option<Self> {
        if k < 1 {
            return None;
        }
        let mut out = CpRow {
            coeff: BTreeMap::new(),
            rhs: self.rhs.checked_mul(k)?,
        };
        for (&var, &c) in &self.coeff {
            out.coeff.insert(var, c.checked_mul(k)?);
        }
        Some(out)
    }

    /// VeriPB `s`: cap every NORMALIZED coefficient at the NORMALIZED degree.
    /// Fails closed on a negative degree, where the cap is not sound.
    pub(super) fn saturate(&self) -> Option<Self> {
        let degree = self.norm_degree()?;
        if degree < 0 {
            return None;
        }
        let (signs, mags) = self.signs_and_mags()?;
        let capped = mags.into_iter().map(|(v, m)| (v, m.min(degree))).collect();
        Self::from_normalized(&signs, capped, degree)
    }

    /// VeriPB `d`: ceil-divide every NORMALIZED coefficient and the NORMALIZED
    /// degree.
    pub(super) fn divide(&self, d: i128) -> Option<Self> {
        if d < 1 {
            return None;
        }
        let degree = self.norm_degree()?;
        let (signs, mags) = self.signs_and_mags()?;
        let mut divided = BTreeMap::new();
        for (var, mag) in mags {
            divided.insert(var, ceil_div(mag, d)?);
        }
        Self::from_normalized(&signs, divided, ceil_div(degree, d)?)
    }

    /// VeriPB `w`: drop the variable and lower the NORMALIZED degree by the
    /// coefficient dropped. A variable that does not occur is a no-op.
    pub(super) fn weaken(&self, var: u32) -> Option<Self> {
        let Some(&c) = self.coeff.get(&var) else {
            return Some(self.clone());
        };
        let degree = self.norm_degree()?.checked_sub(c.checked_abs()?)?;
        let (mut signs, mut mags) = self.signs_and_mags()?;
        signs.remove(&var);
        mags.remove(&var);
        Self::from_normalized(&signs, mags, degree)
    }

    /// The literal axiom `l >= 0`.
    pub(super) fn literal_axiom(var: u32, negated: bool) -> Self {
        let mut out = CpRow::default();
        if negated {
            out.coeff.insert(var, -1);
            out.rhs = -1;
        } else {
            out.coeff.insert(var, 1);
        }
        out
    }

    pub(super) fn is_contradiction(&self) -> bool {
        self.coeff.is_empty() && self.rhs >= 1
    }

    /// `true` iff this row holds under `values` (indexed by `var - 1`).
    pub(super) fn holds(&self, values: &[bool]) -> bool {
        let mut acc: i128 = 0;
        for (&var, &c) in &self.coeff {
            match values.get((var as usize).wrapping_sub(1)) {
                Some(true) => acc += c,
                Some(false) => {}
                // A row over a variable outside the extension cannot be checked;
                // treat as a failure so the caller declines.
                None => return false,
            }
        }
        acc >= self.rhs
    }
}

/// One entry on the `pol` evaluation stack. A bare integer is ambiguous in
/// VeriPB's reverse-polish `pol` — it is a constraint id when consumed by `+`
/// and a scalar when consumed by `*` or `d` — so resolution is deferred to the
/// operator, exactly as the checker does it.
pub(super) enum Item {
    Num(i128),
    Lit(u32, bool),
    Row(CpRow),
}

/// Parses an OPB term list (`+1 x3 +1 ~x7 ...`) into variable form.
pub(super) fn parse_terms(tokens: &[&str]) -> Option<CpRow> {
    let mut row = CpRow::default();
    let mut chunks = tokens.chunks_exact(2);
    for chunk in &mut chunks {
        let coeff: i128 = chunk[0].parse().ok()?;
        let (var, negated) = parse_lit(chunk[1])?;
        if negated {
            row.add_coeff(var, coeff.checked_neg()?)?;
            row.rhs = row.rhs.checked_sub(coeff)?;
        } else {
            row.add_coeff(var, coeff)?;
        }
    }
    if !chunks.remainder().is_empty() {
        return None;
    }
    Some(row)
}

pub(super) fn parse_lit(token: &str) -> Option<(u32, bool)> {
    let (negated, rest) = match token.strip_prefix('~') {
        Some(rest) => (true, rest),
        None => (false, token),
    };
    let digits = rest.strip_prefix('x')?;
    Some((digits.parse().ok()?, negated))
}

/// Replays a `pol` expression against the database, also reporting every id it
/// CONSUMED as a constraint (as opposed to as a scalar). The caller uses that to
/// propagate the `soli` taint — see [`self_check_inner`].
pub(super) fn eval_pol(expr: &str, db: &BTreeMap<u64, CpRow>) -> Option<(CpRow, Vec<u64>)> {
    let mut stack: Vec<Item> = Vec::new();
    let mut used: Vec<u64> = Vec::new();
    let as_row = |item: Item, db: &BTreeMap<u64, CpRow>, used: &mut Vec<u64>| -> Option<CpRow> {
        match item {
            Item::Row(row) => Some(row),
            Item::Lit(var, negated) => Some(CpRow::literal_axiom(var, negated)),
            Item::Num(id) => {
                let id = u64::try_from(id).ok()?;
                used.push(id);
                db.get(&id).cloned()
            }
        }
    };
    for token in expr.split_whitespace() {
        match token {
            "+" => {
                let b = as_row(stack.pop()?, db, &mut used)?;
                let a = as_row(stack.pop()?, db, &mut used)?;
                stack.push(Item::Row(a.add(&b)?));
            }
            "*" => {
                let Item::Num(k) = stack.pop()? else {
                    return None;
                };
                let a = as_row(stack.pop()?, db, &mut used)?;
                stack.push(Item::Row(a.scale(k)?));
            }
            "d" => {
                let Item::Num(k) = stack.pop()? else {
                    return None;
                };
                let a = as_row(stack.pop()?, db, &mut used)?;
                stack.push(Item::Row(a.divide(k)?));
            }
            "s" => {
                let a = as_row(stack.pop()?, db, &mut used)?;
                stack.push(Item::Row(a.saturate()?));
            }
            "w" => {
                let Item::Lit(var, _) = stack.pop()? else {
                    return None;
                };
                let a = as_row(stack.pop()?, db, &mut used)?;
                stack.push(Item::Row(a.weaken(var)?));
            }
            _ => {
                if let Some((var, negated)) = parse_lit(token) {
                    stack.push(Item::Lit(var, negated));
                } else {
                    stack.push(Item::Num(token.parse().ok()?));
                }
            }
        }
    }
    if stack.len() != 1 {
        return None;
    }
    let row = as_row(stack.pop()?, db, &mut used)?;
    Some((row, used))
}
