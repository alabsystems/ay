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
//! the first. `clique_coloring`, `frustrated_cycle` and `odd_cycle_cover` share
//! this one definition; if it is wrong, every self-check fails loudly rather
//! than one quietly disagreeing with the others.
//!
//! The same argument applies one level up, to the WHOLE self-check, which is
//! why [`self_check_pol_only_objective_floor`] lives here too. Two structural
//! certifiers — `frustrated_cycle` and `odd_cycle_cover` — emit proofs with
//! byte-for-byte the same CONTRACT (a `pol`-only derivation, ending at
//! `Σ_obj x_v >= optimum`, published by a hinted `conclusion BOUNDS`), and they
//! reached it by different mathematics. A per-certifier copy of that check
//! would be a second chance to get the id arithmetic, the `f`-count or the
//! conclusion grammar subtly wrong in a file nobody diffs against the first —
//! and the id arithmetic is precisely where this repository has already shipped
//! four uncheckable proofs (see `veripb_input_row_ids`).
//!
//! Nothing here trusts the emitter: every row is rebuilt from the proof text
//! and the instance, and the arithmetic is exact `i128` with checked overflow
//! throughout (a wrapped coefficient is precisely how a "more trivially true
//! than its operands" row becomes an empty contradiction — see defects 9, 10
//! and 12 in `ci/veripb.pin`).

use std::collections::BTreeMap;

use super::format_assignment;
use crate::proof::veripb::{veripb_input_constraint_count, veripb_input_row_ids};
use crate::types::{PbInstance, PbRel};

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

// ---------------------------------------------------------------------------
// Layer 4: parse a certifier's emitted bytes back and replay them.
// ---------------------------------------------------------------------------

// `DECLINE` records the first refusal site under test so a failure is
// diagnosable instead of a bare `false`; production reads only success/failure.
#[cfg(test)]
thread_local! {
    static DECLINE: std::cell::RefCell<Option<&'static str>> =
        const { std::cell::RefCell::new(None) };
}

fn decline<T>(_site: &'static str) -> Option<T> {
    #[cfg(test)]
    DECLINE.with(|slot| {
        let mut slot = slot.borrow_mut();
        if slot.is_none() {
            *slot = Some(_site);
        }
    });
    None
}

/// Replays a certifier's emitted proof text and returns `true` only if those
/// BYTES establish `Σ_obj x_v >= optimum` for THIS instance.
///
/// The contract enforced here, and the reason it is worth sharing:
///
/// * the header's `f` count is the one [`veripb_input_constraint_count`] gives,
///   so an `=` row cannot silently shift what the checker imported;
/// * the database is seeded at the ids [`veripb_input_row_ids`] gives, so a
///   `pol` step citing `idx + 1` past an equality is caught here rather than at
///   `conclusion BOUNDS` (which is how four uncheckable proofs shipped);
/// * EVERY rule line is `pol`, so the derivation contains no extension
///   variable, no assumption and no `rup`/`red`/`soli` to model;
/// * every replayed row must hold at the (independently re-verified feasible)
///   incumbent, because a feasible point falsifying a derived row would mean the
///   derivation is unsound; and
/// * the row the conclusion HINTS AT must be exactly the objective floor —
///   unit on every objective variable, nothing else, degree `optimum`.
pub(super) fn self_check_pol_only_objective_floor(
    text: &str,
    instance: &PbInstance,
    incumbent: &[bool],
    optimum: i128,
    floor_id: u64,
) -> bool {
    self_check_inner(
        text,
        instance,
        incumbent,
        optimum,
        floor_id,
        FloorContract::UnitObjectiveGeInputs,
    )
    .is_some()
}

/// The same interpreter and the same conclusion grammar, for certifiers whose
/// INPUT rows include `=` constraints (seeded at VeriPB's two-id split: the
/// `>=` half at the row's id, the negated `<=` half at `id + 1` — see
/// `veripb_input_row_ids`) and whose objective carries general positive
/// weights; the cited floor must be EXACTLY the weighted objective row at
/// degree `optimum`. One implementation serves both entry points for the
/// reason this module exists at all: a second copy of the seeding or the
/// conclusion grammar would be a second chance to model the wrong semantics.
/// The unit entry point keeps its original, stricter behaviour byte-for-byte —
/// loosening it in place would have WEAKENED the redundancy for the three
/// certifiers already relying on it.
pub(super) fn self_check_pol_only_weighted_objective_floor(
    text: &str,
    instance: &PbInstance,
    incumbent: &[bool],
    optimum: i128,
    floor_id: u64,
) -> bool {
    self_check_inner(
        text,
        instance,
        incumbent,
        optimum,
        floor_id,
        FloorContract::WeightedObjectiveEqInputs,
    )
    .is_some()
}

/// Replays a `certified_bb` OPT-LIN proof and returns `true` only if THOSE
/// BYTES refute `obj <= optimum - 1` for THIS instance.
///
/// # Why a third contract exists rather than a third copy of the interpreter
///
/// The two contracts above both check that the derivation ENDS AT AN OBJECTIVE
/// FLOOR: a row whose coefficients are the objective's and whose degree is
/// `optimum`. That is the wrong shape for a branch-and-bound refutation, which
/// never derives the floor at all. It installs the objective-improving row with
/// `soli`, closes every leaf of the search tree AGAINST that row, resolves the
/// leaves back to the empty clause, and cites the CONTRADICTION. Forcing that
/// shape through `UnitObjectiveGeInputs` was not possible; writing a second
/// interpreter for it would have been a second chance to model `d`, `s` and the
/// `=` split differently from the file every other certifier is checked by —
/// which is the whole reason this module is shared (see the module docs).
///
/// # What this contract adds, and why each part is load-bearing
///
/// * ONE `soli` line is permitted, before any `pol`, and its assignment must be
///   exactly the incumbent's. It installs the objective-improving row
///   `-Σ g_v x_v >= 1 + offset - optimum` at the id after the inputs — modelled
///   here from the INSTANCE's objective, not from anything the emitter says, so
///   an emitter that misremembers VeriPB's normalization is caught rather than
///   believed.
/// * SOLI TAINT. The incumbent FALSIFIES the objective-improving row, so a row
///   derived from it must not be checked against the incumbent — but a row
///   derived WITHOUT it must, exactly as before. [`eval_pol`] already reports
///   which ids each step consumed AS A CONSTRAINT; this is the consumer that
///   docstring was written for. Untainted rows keep the original check.
/// * The cited row must be a CONTRADICTION (empty support, degree >= 1) AND
///   tainted. Both halves matter: an untainted contradiction would say the
///   formula itself is unsatisfiable, which cannot be true of an instance we
///   have just re-verified a feasible incumbent for — so it is evidence of a
///   modelling error in the replay or a forged input row, and is refused.
pub(super) fn self_check_soli_refutation(
    text: &str,
    instance: &PbInstance,
    incumbent: &[bool],
    optimum: i128,
    contradiction_id: u64,
) -> bool {
    self_check_inner(
        text,
        instance,
        incumbent,
        optimum,
        contradiction_id,
        FloorContract::SoliRefutedContradiction,
    )
    .is_some()
}

/// Which input-row and floor shape [`self_check_inner`] enforces.
#[derive(Clone, Copy, PartialEq, Eq)]
enum FloorContract {
    /// `>=`-only inputs, unit objective, unit floor coefficients.
    UnitObjectiveGeInputs,
    /// `=` inputs allowed (two-id split), positive-weight objective, floor
    /// coefficients equal to the objective's own.
    WeightedObjectiveEqInputs,
    /// `>=`-only inputs, one leading `soli`, and a cited row that is a
    /// soli-tainted CONTRADICTION rather than an objective floor.
    SoliRefutedContradiction,
}

/// The row VeriPB's `soli` installs: the OBJECTIVE-IMPROVING constraint
/// `obj <= optimum - 1`, in `>=` form, rebuilt from the INSTANCE.
///
/// Modelled here rather than parsed from the emitter's text, because the whole
/// point of the replay is to be a second opinion about what the checker will
/// hold in its database. `min: Σ c_v x_v` bounded above by `optimum - 1` is
/// `-Σ c_v x_v >= 1 - optimum`.
///
/// Restricted, fail-closed, to objectives of PLAIN NON-NEGATED single literals.
/// A negated objective literal contributes a constant that VeriPB folds into the
/// degree, and a replay that models that fold WRONGLY would be a self-check that
/// silently agrees with a broken emitter. The one route using this contract
/// emits only over this shape, so the restriction costs nothing today and
/// removes the untested case entirely.
fn objective_improving_row(instance: &PbInstance, optimum: i128) -> Option<CpRow> {
    let objective = instance.objective.as_ref()?;
    let mut row = CpRow {
        coeff: BTreeMap::new(),
        rhs: 1_i128.checked_sub(optimum)?,
    };
    for term in &objective.terms {
        let [lit] = term.lits.as_slice() else {
            return decline("soli-objective-nonlinear");
        };
        if lit.negated || lit.var == 0 {
            return decline("soli-objective-negated-literal");
        }
        row.add_coeff(lit.var, term.coeff.checked_neg()?)?;
    }
    if row.coeff.is_empty() {
        return decline("soli-objective-empty");
    }
    Some(row)
}

#[allow(clippy::too_many_lines)]
fn self_check_inner(
    text: &str,
    instance: &PbInstance,
    incumbent: &[bool],
    optimum: i128,
    floor_id: u64,
    contract: FloorContract,
) -> Option<()> {
    let mut lines = text.lines();
    if lines.next()? != "pseudo-Boolean proof version 3.0" {
        return decline("header");
    }
    let f_line: Vec<&str> = lines.next()?.split_whitespace().collect();
    if f_line.first()? != &"f" {
        return decline("f-line");
    }
    let declared: u64 = f_line.get(1)?.parse().ok()?;
    if declared != veripb_input_constraint_count(instance).ok()? {
        return decline("f-count");
    }

    // Seed the database with the input rows at the ids VeriPB gives them. Every
    // row of this family is a `>=` row, so the `=` split cannot arise; refuse
    // rather than assume if one ever does.
    let ids = veripb_input_row_ids(instance).ok()?;
    let mut db: BTreeMap<u64, CpRow> = BTreeMap::new();
    for (index, constraint) in instance.constraints.iter().enumerate() {
        match (constraint.rel, contract) {
            (PbRel::Ge, _) | (PbRel::Eq, FloorContract::WeightedObjectiveEqInputs) => {}
            _ => return decline("input-row-not-ge"),
        }
        let mut row = CpRow {
            coeff: BTreeMap::new(),
            rhs: constraint.rhs,
        };
        for term in &constraint.terms {
            let [lit] = term.lits.as_slice() else {
                return decline("input-row-nonlinear");
            };
            if lit.negated {
                row.add_coeff(lit.var, term.coeff.checked_neg()?)?;
                row.rhs = row.rhs.checked_sub(term.coeff)?;
            } else {
                row.add_coeff(lit.var, term.coeff)?;
            }
        }
        let id = ids.get(index)?.get();
        if constraint.rel == PbRel::Eq {
            // VeriPB's `=` split: the `<=` half, negated into `>=` form, lives
            // at the id after the `>=` half.
            let mut le = CpRow {
                coeff: BTreeMap::new(),
                rhs: row.rhs.checked_neg()?,
            };
            for (&var, &coeff) in &row.coeff {
                le.add_coeff(var, coeff.checked_neg()?)?;
            }
            db.insert(id.checked_add(1)?, le);
        }
        db.insert(id, row);
    }

    let mut next_id = declared.checked_add(1)?;
    let mut conclusion: Option<String> = None;
    let mut saw_end = false;
    // Ids whose row depends — transitively — on the objective-improving row the
    // `soli` line installs. The incumbent falsifies that row by construction, so
    // these are the rows, and the ONLY rows, exempt from the incumbent check.
    let mut soli_tainted: std::collections::BTreeSet<u64> = std::collections::BTreeSet::new();
    for line in lines {
        let line = line.trim_end();
        if line == "output NONE;" {
            continue;
        }
        if line == "end pseudo-Boolean proof;" {
            saw_end = true;
            break;
        }
        if let Some(rest) = line.strip_prefix("conclusion ") {
            if conclusion.is_some() {
                return decline("second-conclusion");
            }
            conclusion = Some(rest.to_string());
            continue;
        }
        if let Some(rest) = line.strip_prefix("soli ") {
            // Only the refutation contract may log a solution, only once, and
            // only before any derivation — a `soli` in the middle of a `pol`
            // chain would shift every later id.
            if contract != FloorContract::SoliRefutedContradiction {
                return decline("soli-in-pol-only-contract");
            }
            if !soli_tainted.is_empty() || next_id != declared.checked_add(1)? {
                return decline("soli-not-first");
            }
            if rest.strip_suffix(';')?.trim_end() != format_assignment(incumbent) {
                return decline("soli-assignment-is-not-the-incumbent");
            }
            db.insert(next_id, objective_improving_row(instance, optimum)?);
            soli_tainted.insert(next_id);
            next_id = next_id.checked_add(1)?;
            continue;
        }
        // `pol` ONLY (plus the one `soli` above). No `red`, no `rup`, no `del`:
        // every derived row is then a checked cutting-planes inference from the
        // instance's own rows and the one logged solution, there is no extension
        // variable anywhere, and nothing in the proof is an assumption. Anything
        // else is refused rather than modelled.
        let Some(expression) = line.strip_prefix("pol ") else {
            return decline("non-pol-rule");
        };
        if conclusion.is_some() {
            return decline("rule-after-conclusion");
        }
        let body = expression.strip_suffix(';')?.trim_end();
        let (row, used) = eval_pol(body, &db)?;
        if used.iter().any(|id| soli_tainted.contains(id)) {
            soli_tainted.insert(next_id);
        } else if !row.holds(incumbent) {
            // A feasible point must satisfy every row a sound derivation
            // produces FROM THE FORMULA ALONE. Rows that cite the
            // objective-improving assumption are refuting it, so the incumbent
            // is expected to falsify them and this check does not apply.
            return decline("derived-row-false-at-incumbent");
        }
        db.insert(next_id, row);
        next_id = next_id.checked_add(1)?;
    }
    if !saw_end {
        return decline("missing-end");
    }

    if contract == FloorContract::SoliRefutedContradiction {
        // The cited row must be an EMPTY CONTRADICTION reached THROUGH the
        // objective-improving row: that, and only that, is what licenses
        // `conclusion BOUNDS optimum ...` for a branch-and-bound refutation.
        if soli_tainted.is_empty() {
            return decline("refutation-without-soli");
        }
        let cited = db.get(&floor_id)?;
        if !cited.is_contradiction() {
            return decline("cited-row-is-not-a-contradiction");
        }
        if !soli_tainted.contains(&floor_id) {
            return decline("contradiction-does-not-cite-soli");
        }
    } else {
        // The row the conclusion cites must be the objective floor itself: unit
        // coefficient on every objective variable, nothing else, degree
        // `optimum`.
        let floor = db.get(&floor_id)?;
        if floor.rhs != optimum {
            return decline("floor-degree");
        }
        let objective = instance.objective.as_ref()?;
        if floor.coeff.len() != objective.terms.len() {
            return decline("floor-support");
        }
        for term in &objective.terms {
            let [lit] = term.lits.as_slice() else {
                return decline("objective-nonlinear");
            };
            let expected = match contract {
                FloorContract::UnitObjectiveGeInputs => {
                    if lit.negated || term.coeff != 1 {
                        return decline("objective-not-unit");
                    }
                    1
                }
                FloorContract::WeightedObjectiveEqInputs => {
                    if lit.negated || term.coeff < 1 {
                        return decline("objective-not-positive");
                    }
                    term.coeff
                }
                FloorContract::SoliRefutedContradiction => unreachable!("handled above"),
            };
            if floor.coeff.get(&lit.var) != Some(&expected) {
                return decline("floor-coefficient");
            }
        }
    }

    // `BOUNDS <lb> : <id> <ub> : <witness>;`
    let conclusion = conclusion?;
    let rest = conclusion.strip_prefix("BOUNDS ")?;
    let body = rest.strip_suffix(';')?;
    let (lower_part, upper_part) = body.split_once(" : ")?;
    let lower: i128 = lower_part.trim().parse().ok()?;
    if lower != optimum {
        return decline("conclusion-lower");
    }
    let (hint, upper_rest) = upper_part.split_once(' ')?;
    if hint.trim().parse::<u64>().ok()? != floor_id {
        return decline("conclusion-hint");
    }
    let (upper, witness) = upper_rest.split_once(" : ")?;
    if upper.trim().parse::<i128>().ok()? != optimum {
        return decline("conclusion-upper");
    }
    if witness.trim() != format_assignment(incumbent) {
        return decline("conclusion-witness");
    }
    Some(())
}
