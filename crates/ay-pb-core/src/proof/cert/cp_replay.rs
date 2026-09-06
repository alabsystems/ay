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

    /// The NEGATION of this `>=` row, as the `>=` row a checker adds when it
    /// starts a `rup` check: `Σ c_v x_v <= rhs - 1`, i.e.
    /// `Σ (-c_v) x_v >= 1 - rhs`.
    ///
    /// Over 0/1 variables and integer coefficients this is EXACTLY the
    /// complement — there is no rounding to get wrong — which is what makes
    /// "propagate the database together with this row" the definition of RUP
    /// rather than an approximation of it.
    pub(super) fn negate(&self) -> Option<Self> {
        let mut out = CpRow {
            coeff: BTreeMap::new(),
            rhs: 1_i128.checked_sub(self.rhs)?,
        };
        for (&var, &c) in &self.coeff {
            out.coeff.insert(var, c.checked_neg()?);
        }
        Some(out)
    }

    /// The NORMALIZED slack of this row under a partial assignment: the most
    /// its unfalsified literals can still contribute, minus its degree.
    ///
    /// `slack < 0` is the checker's conflict test, and a literal whose weight
    /// EXCEEDS the slack is the checker's propagation test — both are defined on
    /// the normalized literal view (`x_v` when `c > 0`, `~x_v` when `c < 0`,
    /// degree `rhs + Σ_{c<0}|c|`), which is why this is computed there and not
    /// in the variable form. Fails closed on overflow: defect 10 in
    /// `ci/veripb.pin` is a propagation slack computed in a width that wrapped.
    fn norm_slack(&self, assign: &Assignment) -> Option<i128> {
        let mut slack = self.norm_degree()?.checked_neg()?;
        for (&var, &c) in &self.coeff {
            let falsified = match assign.get(&var) {
                // The literal is `x_v` when `c > 0` and `~x_v` when `c < 0`.
                Some(&(value, _)) => (c > 0) != value,
                None => false,
            };
            if !falsified {
                slack = slack.checked_add(c.checked_abs()?)?;
            }
        }
        Some(slack)
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

/// A partial assignment during a RUP check: `var -> (value, the row that
/// forced it)`. `None` as the reason means the target's own negation forced it,
/// which is an assumption of the check rather than a database row.
type Assignment = BTreeMap<u32, (bool, Option<u64>)>;

/// The largest number of ROW VISITS one [`rup_refutes`] call may spend.
///
/// A deterministic COUNT, never a clock: the same proof text against the same
/// instance costs the same number of visits on every machine and under every
/// load, so a self-check that declines on this budget declines reproducibly.
/// Propagation assigns each variable at most once and each assignment queues
/// only the rows mentioning that variable, so the natural bound is
/// `seeds + nnz(database)`; this cap is the guard for a database far larger
/// than anything measured, not the thing that normally stops the loop.
const MAX_RUP_ROW_VISITS: u64 = 1 << 24;

/// The replay database together with the two indices a RUP check needs, so that
/// one check costs the rows it TOUCHES rather than the whole database.
///
/// Kept as one type because the indices are an invariant of the map: an
/// `insert` that updated `rows` and forgot `occ` would silently make every later
/// RUP check miss a propagation, and a check that misses propagations FAILS
/// CLOSED (it declines) — which is safe, but it would also make the guard
/// quietly weaker than it reads. One insertion path, no way to skip it.
struct CpDb {
    rows: BTreeMap<u64, CpRow>,
    /// `var -> ids of the rows mentioning it`.
    occ: BTreeMap<u32, Vec<u64>>,
    /// The rows that can conflict OR propagate under the EMPTY assignment, and
    /// therefore have to be examined by every check even before it assigns
    /// anything. Every other row is reached through [`CpDb::occ`] when one of
    /// its variables is assigned, and cannot do anything before that: with no
    /// assignment its slack is `Σ|c_v| - degree >= 0` and every literal weight
    /// is `<= that slack`, which is exactly the condition tested here.
    seeds: Vec<u64>,
}

impl CpDb {
    fn new() -> Self {
        CpDb {
            rows: BTreeMap::new(),
            occ: BTreeMap::new(),
            seeds: Vec::new(),
        }
    }

    fn insert(&mut self, id: u64, row: CpRow) -> Option<()> {
        let empty = Assignment::new();
        let slack = row.norm_slack(&empty)?;
        if slack < 0
            || row
                .coeff
                .values()
                .any(|c| c.checked_abs().is_none_or(|w| w > slack))
        {
            self.seeds.push(id);
        }
        for &var in row.coeff.keys() {
            self.occ.entry(var).or_default().push(id);
        }
        self.rows.insert(id, row);
        Some(())
    }

    fn get(&self, id: u64) -> Option<&CpRow> {
        self.rows.get(&id)
    }
}

/// VeriPB's `rup` rule, modelled rather than trusted: unit-propagate the
/// database together with the NEGATION of `target` and report whether that
/// reaches a conflict.
///
/// Returns the ids of the database rows the refutation USED — the transitive
/// reasons of the conflict, in the same currency [`eval_pol`] reports for `pol`
/// — so the caller can propagate the `soli` taint through a `rup` exactly as it
/// does through a `pol`. Returns `None`, which is a REFUSAL and never an
/// acceptance, when propagation reaches a fixed point with no conflict, when the
/// visit budget is spent, or when any arithmetic would overflow.
///
/// WHY THIS IS THE WHOLE POINT. A `rup` line is an ASSUMPTION until something
/// checks it. If this function answered "yes" for anything shaped like a clause,
/// the route's self-check would be a rubber stamp on its own leaves: the one
/// layer that reads the emitted bytes cold would have stopped reading them. So
/// the propagation here is the real one — normalized slack, weight-versus-slack
/// propagation, conflict on negative slack — and a target that is merely TRUE,
/// or merely implied by something that needs a cut to see, is refused.
fn rup_refutes(db: &CpDb, target: &CpRow) -> Option<Vec<u64>> {
    // Not a database id: the negation is the check's assumption, not a row.
    const NEGATION: u64 = u64::MAX;
    let negation = target.negate()?;
    let mut assign = Assignment::new();
    let mut queue: Vec<u64> = db.seeds.clone();
    queue.push(NEGATION);
    let mut visits: u64 = 0;
    let mut conflict: Option<u64> = None;

    while let Some(id) = queue.pop() {
        visits = visits.checked_add(1)?;
        if visits > MAX_RUP_ROW_VISITS {
            return decline("rup-visit-budget");
        }
        let row = if id == NEGATION {
            &negation
        } else {
            db.get(id)?
        };
        let slack = row.norm_slack(&assign)?;
        if slack < 0 {
            conflict = Some(id);
            break;
        }
        // A literal whose weight exceeds the slack must be TRUE, or the row
        // cannot be satisfied. Assigning it does not change THIS row's slack (a
        // true literal is not falsified), so the remaining tests in this loop
        // stay valid; the rows that DO change are queued through `occ`.
        for (&var, &c) in &row.coeff {
            if assign.contains_key(&var) {
                continue;
            }
            if c.checked_abs()? > slack {
                let reason = if id == NEGATION { None } else { Some(id) };
                assign.insert(var, (c > 0, reason));
                if let Some(ids) = db.occ.get(&var) {
                    queue.extend_from_slice(ids);
                }
            }
        }
    }

    // No conflict is not a soft failure: the target is not RUP-implied, and the
    // proof line claiming it is unsupported.
    let Some(conflict) = conflict else {
        return decline("rup-not-implied");
    };
    // The conflict's transitive reasons. An over-approximation would only make
    // the taint wider (and the incumbent check weaker); this walk is the exact
    // set the propagation actually leaned on.
    let mut used: std::collections::BTreeSet<u64> = std::collections::BTreeSet::new();
    let mut stack = vec![conflict];
    while let Some(id) = stack.pop() {
        if id == NEGATION || !used.insert(id) {
            continue;
        }
        for var in db.get(id)?.coeff.keys() {
            if let Some(&(_, Some(reason))) = assign.get(var) {
                if !used.contains(&reason) {
                    stack.push(reason);
                }
            }
        }
    }
    Some(used.into_iter().collect())
}

/// Parses a `rup` line's inline constraint body (`1 x3 1 ~x7 >= 1`, without the
/// trailing `;`) into variable form.
///
/// `>=` only. VeriPB accepts other relations in this position; modelling one
/// this route never emits would be an untested branch in the one place that is
/// supposed to be the second opinion, so anything else is refused.
fn parse_rup_constraint(body: &str) -> Option<CpRow> {
    let tokens: Vec<&str> = body.split_whitespace().collect();
    let at = tokens.iter().position(|token| *token == ">=")?;
    if tokens.len() != at.checked_add(2)? {
        return decline("rup-constraint-tail");
    }
    let degree: i128 = tokens.get(at.checked_add(1)?)?.parse().ok()?;
    let mut row = parse_terms(tokens.get(..at)?)?;
    row.rhs = row.rhs.checked_add(degree)?;
    Some(row)
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
    let mut db = CpDb::new();
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
            db.insert(id.checked_add(1)?, le)?;
        }
        db.insert(id, row)?;
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
            db.insert(next_id, objective_improving_row(instance, optimum)?)?;
            soli_tainted.insert(next_id);
            next_id = next_id.checked_add(1)?;
            continue;
        }
        if let Some(rest) = line.strip_prefix("rup ") {
            // `rup` is REPLAYED, not believed. The other two contracts promise a
            // `pol`-only derivation, and loosening them here would weaken three
            // certifiers that never asked for it.
            if contract != FloorContract::SoliRefutedContradiction {
                return decline("rup-in-pol-only-contract");
            }
            if conclusion.is_some() {
                return decline("rule-after-conclusion");
            }
            let body = rest.strip_suffix(';')?.trim_end();
            let row = parse_rup_constraint(body)?;
            let used = rup_refutes(&db, &row)?;
            if used.iter().any(|id| soli_tainted.contains(id)) {
                soli_tainted.insert(next_id);
            } else if !row.holds(incumbent) {
                // Same rule as `pol`, for the same reason, and it is not
                // vacuous here: an untainted RUP-implied row is a consequence of
                // the FORMULA, so the re-verified feasible incumbent has to
                // satisfy it. The `soli`-tainted ones are refuting the
                // objective-improving assumption and are expected to fail it.
                return decline("rup-row-false-at-incumbent");
            }
            db.insert(next_id, row)?;
            next_id = next_id.checked_add(1)?;
            continue;
        }
        // `pol` (plus the one `soli` above, and `rup` for the refutation
        // contract). No `red`, no `del`: every derived row is then either a
        // checked cutting-planes inference or a checked reverse unit
        // propagation from the instance's own rows and the one logged solution,
        // there is no extension variable anywhere, and nothing in the proof is
        // an unchecked assumption. Anything else is refused rather than
        // modelled.
        let Some(expression) = line.strip_prefix("pol ") else {
            return decline("non-pol-rule");
        };
        if conclusion.is_some() {
            return decline("rule-after-conclusion");
        }
        let body = expression.strip_suffix(';')?.trim_end();
        let (row, used) = eval_pol(body, &db.rows)?;
        if used.iter().any(|id| soli_tainted.contains(id)) {
            soli_tainted.insert(next_id);
        } else if !row.holds(incumbent) {
            // A feasible point must satisfy every row a sound derivation
            // produces FROM THE FORMULA ALONE. Rows that cite the
            // objective-improving assumption are refuting it, so the incumbent
            // is expected to falsify them and this check does not apply.
            return decline("derived-row-false-at-incumbent");
        }
        db.insert(next_id, row)?;
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
        let cited = db.get(floor_id)?;
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
        let floor = db.get(floor_id)?;
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

#[cfg(test)]
mod tests {
    use super::{parse_rup_constraint, rup_refutes, CpDb, CpRow};
    use std::collections::BTreeMap;

    /// `Σ coeff·x >= rhs` in variable form.
    fn row(coeff: &[(u32, i128)], rhs: i128) -> CpRow {
        CpRow {
            coeff: coeff.iter().copied().collect::<BTreeMap<_, _>>(),
            rhs,
        }
    }

    fn db_of(rows: &[(u64, CpRow)]) -> CpDb {
        let mut db = CpDb::new();
        for (id, r) in rows {
            db.insert(*id, r.clone()).expect("insert");
        }
        db
    }

    /// THE CHAIN. Certifier #9's own leaves conflict on the FIRST row visited —
    /// the aggregate row the leaf just derived — so nothing in the shipped
    /// corpus exercises propagation past one step. That is exactly why it is
    /// pinned here: a propagation loop that silently never re-examined a row
    /// would pass every instance we have and be wrong the first time a leaf
    /// needed it.
    ///
    /// `x1` is unit; `x2 >= x1` and `x3 >= x2` only become unit AFTER the
    /// assignment before them; `x1 + x2 + x3 <= 2` only conflicts after all
    /// three. Only the first row can act under the empty assignment, so a
    /// refutation here requires three chained propagations.
    #[test]
    fn unit_propagation_chains_and_reports_every_row_it_leaned_on() {
        let db = db_of(&[
            (1, row(&[(1, 1)], 1)),                     // x1 >= 1
            (2, row(&[(1, -1), (2, 1)], 0)),            // x2 >= x1
            (3, row(&[(2, -1), (3, 1)], 0)),            // x3 >= x2
            (4, row(&[(1, -1), (2, -1), (3, -1)], -2)), // x1 + x2 + x3 <= 2
        ]);
        // Only row 1 can act before anything is assigned.
        assert_eq!(
            db.seeds,
            vec![1],
            "rows 2-4 must not be reachable at the start"
        );
        let used = rup_refutes(&db, &row(&[], 1)).expect("the database is contradictory");
        assert_eq!(
            used,
            vec![1, 2, 3, 4],
            "the reasons are the whole chain, so the `soli` taint cannot leak"
        );
    }

    /// TRUE IS NOT THE TEST. A triangle needs two of its three vertices covered,
    /// so `x1 + x2 + x3 >= 2` is a THEOREM of these rows — and it is not
    /// reachable by unit propagation (negating it leaves every row with slack 1
    /// and every weight at 1, a fixed point). A guard that checked the claim
    /// rather than the RULE would accept it.
    #[test]
    fn a_true_clause_that_needs_a_cut_is_not_rup() {
        let db = db_of(&[
            (1, row(&[(1, 1), (2, 1)], 1)),
            (2, row(&[(2, 1), (3, 1)], 1)),
            (3, row(&[(1, 1), (3, 1)], 1)),
        ]);
        assert!(rup_refutes(&db, &row(&[(1, 1), (2, 1), (3, 1)], 2)).is_none());
        // The same database DOES imply each edge by RUP: it holds one verbatim.
        assert!(rup_refutes(&db, &row(&[(1, 1), (2, 1)], 1)).is_some());
    }

    /// THE SLACK IS THE PB ONE, NOT THE CLAUSAL ONE. `3x1 + 2x2 + 2x3 >= 5`
    /// forces `x1`: without it the most the row can reach is 4. Read as a
    /// CLAUSE ("at least one literal true") it would force nothing, and a
    /// self-check that made that mistake would decline every leaf whose
    /// aggregate row has coefficients above 1 — which is all of them.
    #[test]
    fn propagation_uses_the_coefficients_not_just_the_literals() {
        let db = db_of(&[(1, row(&[(1, 3), (2, 2), (3, 2)], 5))]);
        assert!(
            rup_refutes(&db, &row(&[(1, 1)], 1)).is_some(),
            "dropping x1 leaves 4 < 5"
        );
        // Weakening the row by one unit removes exactly that: 4 >= 4 now.
        let weaker = db_of(&[(1, row(&[(1, 3), (2, 2), (3, 2)], 4))]);
        assert!(rup_refutes(&weaker, &row(&[(1, 1)], 1)).is_none());
    }

    /// The inline constraint body a `rup` line carries, including the empty
    /// clause, which is how a leaf claims the contradiction.
    #[test]
    fn the_rup_body_parses_to_the_clause_it_spells() {
        assert_eq!(
            parse_rup_constraint("1 x3 1 ~x7 >= 1"),
            Some(row(&[(3, 1), (7, -1)], 0)),
            "`~x7` is `1 - x7`, so the degree drops by one"
        );
        let empty = parse_rup_constraint(">= 1").expect("the empty clause");
        assert!(empty.is_contradiction());
        // Anything that is not `<terms> >= <degree>` is refused, not guessed.
        assert!(parse_rup_constraint("1 x3 >= 1 extra").is_none());
        assert!(parse_rup_constraint("1 x3 <= 1").is_none());
        assert!(parse_rup_constraint("1 x3").is_none());
    }
}
