// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Judge a PREMISE-BEARING rule over the text the document actually ships.
//!
//! Every earlier guard in this printer judges a *premise-free* step: it
//! instantiates the rule's spec template over the step's own printed operands.
//! `resolution` / `th_resolution` cannot be judged that way — its validity is a
//! function of its PREMISES' printed clauses and the pivot, not of any source
//! term it carries. So the existing machinery never reached it, and the third
//! false green of this campaign lived exactly there:
//!
//! ```text
//! (assume t1 (not (<= 0 (- C 1))))
//! (step t3 (cl (<= 0 (+ C (- 1)))) :rule th_resolution :premises (t2 t0))
//! (step t4 (cl) :rule th_resolution :premises (t3 t1))
//! ```
//!
//! Internally `t3` and `t1` are exact complements — one `TermId` and its
//! `Not`. On the wire they are two different atoms, because the authored
//! spelling `(- C 1)` survives only in the surface-override ledger and that
//! ledger is restored at assume ROOTS only (see
//! `purge_surface_overrides_for_certified_proof` +
//! `restore_reachable_authored_assume_surface_overrides` in the executor),
//! while `TermStore::mk_sub` normalises `(- C 1)` to `(+ C (- 1))` at term
//! construction so the canonical rendering is the only one a derived literal
//! can get. Carcara answers *"pivot was not eliminated"* and the whole document
//! is `invalid` while AY prints `unproved_steps=0 ay_self_checkable=yes`.
//!
//! # The check
//!
//! [`AlethePrinter::judge_printed_resolution`] replays the step against the
//! printed clauses of its already-emitted premises, with every literal treated
//! as an opaque string modulo the parity of its `not` shells — which is how
//! the external checker treats them (it resolves `(not a)` against
//! `(not (not a))` and answers `valid`). The model is **reverse unit propagation**:
//! assert the negation of the printed conclusion, unit-propagate the printed
//! premises, and demand a conflict.
//!
//! RUP is the right model because it is WEAKER than everything the pinned
//! checker accepts here — measured, not assumed. Four hand probes written
//! against pinned carcara 1.1.0 for this module: from premises `(cl a)` and
//! `(cl b)` it accepts the conclusions `(cl a b)` (eliminates nothing),
//! `(cl a b c)` (invents a conclusion literal) and `(cl a)` (drops a premise
//! entirely), and from `(cl a b)` / `(cl (not a) c)` it accepts `(cl b c)`.
//! RUP accepts all four. The one shape carcara refuses is the one where a
//! literal must be eliminated and its complement is not present, which is the
//! shape above and the only one RUP refuses too. So a RUP failure is evidence
//! the external checker will refuse the step, not merely evidence that this
//! module is stricter than the spec.
//!
//! # The repair
//!
//! When the two printed literals are an arithmetic comparison and its
//! complement in a DIFFERENT spelling, the missing link is an ordinary linear
//! tautology and the checker has a rule for it. The bridge states it:
//!
//! ```text
//! (step t4.p (cl (not (<= 0 (+ C (- 1)))) (<= 0 (- C 1))) :rule la_generic :args (1 1))
//! (step t4 (cl) :rule resolution :premises (t3 t4.p t1))
//! ```
//!
//! The bridge clause is admitted by
//! [`crate::printed_la_generic_unit_implication_is_supported`], which reparses
//! the PRINTED text and runs the same Farkas admission the emitted `la_generic`
//! steps get. So the added step is a claim AY verifies over the bytes it ships,
//! not a claim inherited from a term identity the checker cannot see. The same
//! predicate already gates the shipped authored-assume linear bridge.
//!
//! Anything the bridge cannot reach is an export DECLINE. That turns a false
//! green into an honest `no`, which is the campaign's stated floor.

#[cfg(test)]
use super::printed_command::{printed_commands, PrintedCommandRead};
#[cfg(test)]
use super::split_application;
use super::{parse_printed_bitvec_literal, split_smt_terms, AlethePrintError, AlethePrinter};
use ay_core::kani_compat::{
    det_hash_map_with_capacity, DetHashMap, DetHashMap as HashMap, DetHashSet,
};
use ay_core::{ProofId, TermId};
use std::rc::Rc;

mod wire_text;
pub(super) use wire_text::ScratchScope;
pub(super) use wire_text::{ChargeState, OwnedText, TextBudget, WireLiteral, COUNTER_BYTES};
use wire_text::{ScratchVec, Tracked, WireParts};

/// Every repair a diverged printed pivot can reach, behind one entry point.
mod pivot_bridge;

/// Work bound on one step's printed-text replay. A step wider than this is
/// not replayed; it declines to the honest hole (see [`PrintedClause`]) — the
/// guard must never become the reason a large document fails to EMIT, and a
/// hole is a published step.
const MAX_JUDGED_LITERALS: usize = 4096;

/// Ceiling on the recorded printed-clause ledger, in bytes of RESIDENT memory.
///
/// The ledger holds part of the document a second time, so it has to be
/// bounded: a 31.8 MB certificate is a measured shape in this campaign. Past
/// the ceiling a demanded id is recorded as [`PrintedClause::Unbounded`], and
/// every later judgement that cites it declines to the honest hole over its
/// own clause. Until 2026-09-16 it read "not judged" and the step shipped
/// UNCHANGED — the same silent approval the line-scanning ledger gave a
/// command it could not read, which is the tenth false green reopened by a
/// newline. A bound may cost evidence; it may not manufacture it.
///
/// **What it counts, and why that is the whole story on the big documents.**
/// Until 2026-09-18 the charge was the literal text of every clause, counted
/// once per OCCURRENCE. A printed clause names the same atom over and over, so
/// that over-charged the ledger by the sharing factor, and the bound fired on
/// exactly the documents whose evidence is worth most. MEASURED on today's
/// main over the nine worst documents of
/// `2026-09-17-printed-judgement-hole-cost.jsonl`: **4,838 of 4,883**
/// judgement-caused holes were `premise … is past the ledger's bounds`, and
/// every other decline class was ZERO. On QF_UF
/// `QG-classification/qg5/iso_icl1279` the by-occurrence charge is 8,433,005
/// bytes against this 8 MiB ceiling — a 0.53% overshoot that cost 1,357 holes
/// — while the SAME ledger's real residency is 1,133 distinct literals,
/// 298,851 bytes of text, 35,692 occurrences: about 0.83 MiB. The charge below
/// counts that residency, so the ceiling caps what the ledger costs rather
/// than how often a document repeats itself.
const MAX_RECORDED_PRINTED_BYTES: usize = 8 * 1024 * 1024;

/// An interned printed literal, as the ledger stores it: an index into
/// `AlethePrinter::printed_clause_atom_texts`.
///
/// The ledger holds ONE of these per literal occurrence, so its width is the
/// per-occurrence price of the whole mechanism. MEASURED 2026-09-18 on QF_AX
/// `storecomm_t2_np_sf_ai_00060_009`: 679,190 occurrences drawn from 2,808
/// distinct literals averaging 12.3 bytes. At `Rc<str>`'s 16 bytes that clause
/// ledger costs 11.1 MB and blows the 8 MiB ceiling EARLIER than charging the
/// text per occurrence did (8.36 MB) — measured as 1,460 holes against the
/// base's 1,335. At four bytes it costs 2.97 MB and fits. A ledger of short
/// literals is dominated by its per-occurrence word, not by its text.
pub(super) type PrintedAtomId = u32;

// The occurrence stays four bytes. Generation bits make a retired slot's old
// ids unreadable even after the slot is reused; generations never wrap.
const ATOM_SLOT_BITS: u32 = 18;
const ATOM_SLOT_MASK: u32 = (1 << ATOM_SLOT_BITS) - 1;
const MAX_ATOM_GENERATION: u16 = (u32::MAX >> ATOM_SLOT_BITS) as u16;
const NO_FREE_ATOM: u32 = u32::MAX;
const RC_TEXT_HEADER: usize = 2 * size_of::<usize>();

#[derive(Debug)]
pub(super) struct PrintedAtomSlot {
    text: Option<WireLiteral>,
    references: usize,
    next_free: u32,
    generation: u16,
}

fn rc_text_bytes(text: &str) -> usize {
    // Include the allocation header and its maximum trailing alignment padding.
    text.len()
        .saturating_add(RC_TEXT_HEADER + align_of::<usize>() - 1)
}

fn atom_id(slot: usize, generation: u16) -> PrintedAtomId {
    ((generation as u32) << ATOM_SLOT_BITS) | slot as u32
}

/// Depth and size bounds on the spelling normalisation below.
const MAX_NORMALISED_DEPTH: usize = 64;
const MAX_NORMALISED_NODES: usize = 4096;

/// One printed literal as the replay needs it: the atom its `not` shells
/// enclose, the parity of those shells, and the atom's NORMALISED spelling —
/// the string two literals share exactly when the checker's parser collapses
/// them.
///
/// Every field is an `Rc` into `AlethePrinter::printed_literal_identities`, so
/// a premise clause twenty steps cite is decoded and normalised ONCE. It used
/// to be decoded and re-parsed on every citation, and the printer charged the
/// emission work budget that premise's full text every time. MEASURED
/// 2026-09-18, in the same pass that made the judgement able to read those
/// premises at all: on QF_UF `QG-classification/qg5/iso_icl1279` the
/// per-citation charge alone exhausted the synthesized-default budget after
/// 3,178 of 3,859 steps and discarded an 18.9 MB document the base publishes.
/// The work being charged was never done twice; only the charge was.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PrintedLiteral {
    /// The atom inside the `not` shells, exactly as it is printed.
    atom: OwnedText,
    /// [`normalise_printed_spelling`] of that atom.
    spelling: OwnedText,
    /// How many `not` shells enclosed it.
    depth: usize,
}

impl PrintedLiteral {
    /// Whether the literal asserts its atom (an even number of `not` shells).
    fn positive(&self) -> bool {
        self.depth % 2 == 0
    }
}

/// What the ledger holds for an id some judged step will cite.
///
/// Every id in `printed_clause_demand` gets exactly one entry when its step
/// is rendered, so a judgement can tell the three cases apart and NONE of
/// them is silently "approved":
///
/// * [`Literals`](Self::Literals) — the clause the command binding the id
///   put on the wire, its literals interned into
///   `AlethePrinter::printed_clause_atoms`; the judgement replays over it.
/// * [`Unreadable`](Self::Unreadable) — the rendering had no command binding
///   the id, or that command's clause could not be read. The judgement cannot
///   read the object the checker will read, so the citing step declines to
///   the honest hole.
/// * [`Unbounded`](Self::Unbounded) — readable, but past
///   [`MAX_JUDGED_LITERALS`] or [`MAX_RECORDED_PRINTED_BYTES`]. Same floor.
///
/// An id with NO entry while the ledger is active (`plan_printed_clause_demand`
/// ran) was never rendered through `format_step`, and is the same floor. With
/// the ledger inactive — an isolated helper or a unit test rendering one step
/// — there is nothing recorded and nothing to judge, and behaviour is
/// unchanged.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum PrintedClause {
    Literals(Vec<PrintedAtomId>),
    Unreadable,
    Unbounded,
}

/// Rewrite a printed term into a form where two spellings the external
/// checker's PARSER collapses become one string.
///
/// This is the difference between a real divergence and a cosmetic one, and
/// getting it wrong in either direction is expensive. MEASURED: AY's
/// `bv_identity_collapse` refutation assumes `(not (= (bvult x (_ bv1 4)) (= x
/// (_ bv0 4))))` — the problem's own spelling — and derives
/// `(= (bvult x (_ bv1 4)) (= x #b0000))`, then resolves the two. Those
/// literals are not byte-identical, and pinned carcara answers **`valid`**,
/// because `#b0000` and `(_ bv0 4)` parse to one `Constant::BitVec(0, 4)`. A
/// byte-wise judgement declines that document and destroys evidence the
/// campaign already has.
///
/// Only the bit-vector literal family is normalised, because that is the only
/// parser-level collapse this session measured. Everything else stays
/// byte-wise, which is the conservative direction for a rule that only ever
/// REFUSES.
pub(super) fn normalise_printed_spelling(text: &str, depth: usize, nodes: &mut usize) -> String {
    let text = text.trim();
    if depth > MAX_NORMALISED_DEPTH || *nodes >= MAX_NORMALISED_NODES {
        return text.to_string();
    }
    *nodes += 1;
    if let Some((value, width)) = parse_printed_bitvec_literal(text) {
        return format!("#bv{value}:{width}");
    }
    let Some(inner) = text.strip_prefix('(').and_then(|t| t.strip_suffix(')')) else {
        return text.to_string();
    };
    let Some(parts) = split_smt_terms(inner) else {
        return text.to_string();
    };
    let parts: Vec<String> = parts
        .iter()
        .map(|part| normalise_printed_spelling(part, depth + 1, nodes))
        .collect();
    format!("({})", parts.join(" "))
}

/// Strip the printed `not` shells from a rendered literal.
///
/// Purely textual, because that is all the external checker has. `(not (not
/// p))` decodes as `("p", 2)` and is therefore the complement of `(not p)`,
/// which matches carcara's own `not` handling (probe `p6a`: it resolves
/// `(not a)` against `(not (not a))` to `(cl)` and answers `valid`).
#[cfg(test)]
fn decode_printed_literal(printed: &str) -> Option<(String, usize)> {
    let mut current = printed.trim().to_string();
    let mut depth = 0usize;
    loop {
        let Some(parts) = split_application(&current, "not") else {
            return Some((current, depth));
        };
        let [inner] = parts.as_slice() else {
            return Some((current, depth));
        };
        depth = depth.checked_add(1)?;
        current = inner.trim().to_string();
    }
}

fn printed_clauses_rup_entail_with_budget(
    premises: &[Vec<PrintedLiteral>],
    conclusion: &[PrintedLiteral],
    budget: &TextBudget,
) -> Option<bool> {
    let count = premises
        .iter()
        .try_fold(conclusion.len(), |n, row| n.checked_add(row.len()))?;
    let bound = count
        .checked_mul(256)?
        .checked_add(premises.len().checked_mul(128)?)?
        .checked_add(4096)?;
    let mut metadata = budget.reserve(bound)?;
    // Intern each distinct spelling once; the propagation itself then runs on
    // integers, so a 1,000-literal `th_resolution` costs one hash per literal
    // rather than a quadratic pile of string comparisons. The spelling is
    // already computed — see [`PrintedLiteral`] — so this reads it, never
    // reparses it.
    let mut atoms: DetHashMap<OwnedText, usize> = DetHashMap::default();
    let mut intern = |literal: &PrintedLiteral| -> (usize, bool) {
        let next = atoms.len();
        let atom = *atoms.entry(literal.spelling.clone()).or_insert(next);
        (atom, literal.positive())
    };

    // Deduplicate as we intern. A printed clause may repeat a literal, and a
    // repeated literal would otherwise leave two "unassigned" slots in a clause
    // that in fact has one, so unit propagation would never fire on it and a
    // checkable step would be declined.
    let clauses: Vec<Vec<(usize, bool)>> = premises
        .iter()
        .map(|clause| {
            let mut literals: Vec<(usize, bool)> = clause.iter().map(&mut intern).collect();
            literals.sort_unstable();
            literals.dedup();
            literals
        })
        .collect();
    let negated_conclusion: Vec<(usize, bool)> = conclusion.iter().map(&mut intern).collect();

    // `assignment[atom]`: `Some(true)` asserted positive, `Some(false)`
    // asserted negative, `None` unassigned.
    let mut assignment: Vec<Option<bool>> = vec![None; atoms.len()];
    let actual = atoms
        .allocation_size()
        .checked_add(
            clauses
                .capacity()
                .checked_mul(size_of::<Vec<(usize, bool)>>())?,
        )?
        .checked_add(clauses.iter().try_fold(0usize, |n, row| {
            n.checked_add(row.capacity().checked_mul(size_of::<(usize, bool)>())?)
        })?)?
        .checked_add(
            negated_conclusion
                .capacity()
                .checked_mul(size_of::<(usize, bool)>())?,
        )?
        .checked_add(
            assignment
                .capacity()
                .checked_mul(size_of::<Option<bool>>())?,
        )?;
    metadata.resize(actual, budget.limit)?;
    for (atom, polarity) in &negated_conclusion {
        match assignment[*atom] {
            // The negated conclusion is itself contradictory, so the clause is
            // a tautology and any premise set entails it.
            Some(existing) if existing == *polarity => return Some(true),
            _ => assignment[*atom] = Some(!*polarity),
        }
    }

    // Ordinary unit propagation to fixpoint. Bounded by the literal count, so
    // it terminates in at most `clauses.len()` sweeps.
    loop {
        let mut progressed = false;
        for clause in &clauses {
            let mut unassigned: Option<(usize, bool)> = None;
            let mut satisfied = false;
            let mut unassigned_count = 0usize;
            for &(atom, polarity) in clause {
                match assignment[atom] {
                    Some(value) if value == polarity => {
                        satisfied = true;
                        break;
                    }
                    Some(_) => {}
                    None => {
                        unassigned_count += 1;
                        unassigned = Some((atom, polarity));
                    }
                }
            }
            if satisfied {
                continue;
            }
            match unassigned_count {
                0 => return Some(true),
                1 => {
                    let (atom, polarity) = unassigned.expect("counted one unassigned literal");
                    assignment[atom] = Some(polarity);
                    progressed = true;
                }
                _ => {}
            }
        }
        if !progressed {
            return Some(false);
        }
    }
}

/// Extract the clause an external checker will bind to `id` from the text this
/// printer just emitted for it.
///
/// A step may render as several commands; the one that BINDS the id is the
/// command whose own name is `id`, and every bridge in this printer ends with
/// exactly that command. Anything else (an `anchor`, a comment) records
/// nothing, which the judge reads as "unreadable" rather than as approval.
///
/// Read through the command reader, never line by line: a command spanning
/// lines (a quoted symbol `|g\nh|`, a multi-line string literal) is one
/// command to the checker and must be one command here.
#[cfg(test)]
pub(super) fn printed_conclusion_of(id: ProofId, rendered: &str) -> Option<Vec<String>> {
    let commands = printed_commands(rendered).ok()?;
    let name = id.to_string();
    let binding = commands.iter().rev().find_map(|read| match read {
        PrintedCommandRead::Command(command) if command.name() == Some(name.as_str()) => {
            Some(command)
        }
        _ => None,
    })?;
    Some(
        binding
            .conclusion()?
            .into_iter()
            .map(str::to_string)
            .collect(),
    )
}

fn replay_clause_slices<'a>(text: &'a str, budget: &TextBudget) -> Option<ScratchVec<&'a str>> {
    use super::surface_tokens::next_smt_term_slice;
    let inner = text.strip_prefix("(cl")?.strip_suffix(')')?;
    if !inner.is_empty() && !inner.starts_with(char::is_whitespace) {
        return None;
    }
    let mut cursor = 0;
    let mut count = 0usize;
    while next_smt_term_slice(inner, &mut cursor).ok()?.is_some() {
        count = count.checked_add(1)?;
        if count > MAX_JUDGED_LITERALS {
            return None;
        }
    }
    let mut out = budget.vector(count)?;
    cursor = 0;
    while let Some(term) = next_smt_term_slice(inner, &mut cursor).ok()? {
        out.push(term);
    }
    Some(out)
}

enum WireConclusion {
    Literals(ScratchVec<OwnedText>),
    TooWide,
}

fn read_wire_conclusion(
    id: ProofId,
    rendered: &str,
    budget: &TextBudget,
) -> Option<WireConclusion> {
    use super::surface_tokens::{next_alethe_command_slice, next_smt_term_slice};
    if rendered.len() > super::printed_command::MAX_STEP_BYTES {
        return None;
    }
    let mut name_lease = budget.reserve(16)?;
    let name = id.to_string();
    name_lease.resize(name.capacity(), budget.limit)?;
    let mut position = 0;
    let mut binding = None;
    while let Some(command) = next_alethe_command_slice(rendered, &mut position).ok()? {
        let inner = command.strip_prefix('(')?.strip_suffix(')')?;
        let mut cursor = 0;
        let mut count = 0;
        let mut head = None;
        let mut command_name = None;
        let mut conclusion = None;
        let mut readable = true;
        loop {
            match next_smt_term_slice(inner, &mut cursor) {
                Ok(Some(field)) => {
                    match count {
                        0 => head = Some(field),
                        1 => command_name = Some(field),
                        2 => conclusion = Some(field),
                        _ => (),
                    }
                    count += 1;
                }
                Ok(None) => break,
                Err(_) => {
                    readable = false;
                    break;
                }
            }
        }
        if readable
            && command_name == Some(name.as_str())
            && matches!(head, Some("step" | "assume"))
        {
            binding = Some((head?, count, conclusion));
        }
    }
    let (head, count, conclusion) = binding?;
    let conclusion = conclusion?;
    if head == "assume" {
        if count != 3 {
            return None;
        }
        let mut out = budget.vector(1)?;
        out.push(budget.copy(conclusion)?);
        return Some(WireConclusion::Literals(out));
    }
    let inner = conclusion.strip_prefix("(cl")?.strip_suffix(')')?;
    if !inner.is_empty() && !inner.starts_with(char::is_whitespace) {
        return None;
    }
    let mut cursor = 0;
    let mut count = 0usize;
    while next_smt_term_slice(inner, &mut cursor).ok()?.is_some() {
        count = count.checked_add(1)?;
        if count > MAX_JUDGED_LITERALS {
            return Some(WireConclusion::TooWide);
        }
    }
    let mut out = budget.vector(count)?;
    cursor = 0;
    while let Some(literal) = next_smt_term_slice(inner, &mut cursor).ok()? {
        out.push(budget.copy(literal)?);
    }
    Some(WireConclusion::Literals(out))
}

impl AlethePrinter<'_> {
    /// Plan retention from every native premise edge, not just judged rules.
    /// Synthetic helpers bind their own local ids; the only nonlocal implicit
    /// sources are printed assumptions, which remain pinned for this export.
    pub(super) fn plan_printed_clause_demand(&self, proof: &ay_core::Proof) {
        *self.printed_step_clauses.borrow_mut() = HashMap::default();
        *self.printed_clause_atom_texts.borrow_mut() = Vec::new();
        *self.printed_clause_atom_index.borrow_mut() = HashMap::default();
        *self.printed_clause_bodies.borrow_mut() = HashMap::default();
        let old_overhead = self.printed_clause_overhead_bytes.replace(0);
        let surviving = match self.printed_clause_bytes.get().checked_sub(old_overhead) {
            Some(n) => n,
            None => {
                self.printed_clause_bytes.poison();
                self.printed_clause_bytes.get()
            }
        };
        *self.printed_literal_identities.borrow_mut() = HashMap::default();
        *self.printed_wire_identities.borrow_mut() = HashMap::default();
        self.printed_literal_identity_bytes.set(0);
        self.printed_clause_free_atom.set(NO_FREE_ATOM);
        self.printed_clause_free_atoms.set(0);
        self.printed_clause_retirement_cursor.set(0);
        self.printed_clause_ledger_active.set(true);
        *self.native_zero_cong_scopes.borrow_mut() = HashMap::default();
        let mut demand = HashMap::default();
        let mut zero_scopes = HashMap::default();
        // Bound the plan itself. An oversized plan records no text, so every
        // active-ledger judgement that needs it still refuses missing evidence.
        const MAX_DEMAND: usize = MAX_RECORDED_PRINTED_BYTES / 128;
        let mut oversized = false;
        'plan: for (idx, step) in proof.steps.iter().enumerate() {
            let zero_cong = matches!(step,
                ay_core::ProofStep::Step { rule: ay_core::AletheRule::Cong, clause, premises, args }
                    if premises.len() == 1 && args.is_empty()
                        && self.is_zero_extend_zero_cong_candidate(clause));
            let max_demand = MAX_DEMAND.saturating_sub(zero_scopes.len() + usize::from(zero_cong));
            let mut insert = |premise| {
                if demand.len() >= max_demand && !demand.contains_key(&premise) {
                    return false;
                }
                demand.insert(premise, ProofId(idx as u32));
                true
            };
            let premises: &[ProofId] = match step {
                ay_core::ProofStep::Resolution {
                    clause1, clause2, ..
                } => {
                    for premise in [*clause1, *clause2] {
                        if !insert(premise) {
                            oversized = true;
                            break 'plan;
                        }
                    }
                    &[]
                }
                ay_core::ProofStep::Step { rule, premises, .. }
                    if super::resolution_args::is_generic_resolution(rule)
                        || super::printed_or::is_judged_premise_rule(rule)
                        || zero_cong =>
                {
                    premises
                }
                _ => &[],
            };
            for premise in premises {
                if !insert(*premise) {
                    oversized = true;
                    break 'plan;
                }
                if zero_cong {
                    if !self.admit_emission_work(128) {
                        oversized = true;
                        break 'plan;
                    }
                    zero_scopes.insert(*premise, ProofId(0));
                }
            }
        }
        // Only this narrow native bridge needs scope metadata. Reuse the
        // ledger's residency allowance, and precharge its extra source walk.
        // Invalid/missing scope evidence never enables the bridge.
        let mut scope_stack = Vec::<ProofId>::new();
        if !oversized && !zero_scopes.is_empty() {
            if !self.admit_emission_work((proof.steps.len() as u64).saturating_mul(4)) {
                oversized = true;
            } else {
                for (idx, step) in proof.steps.iter().enumerate() {
                    let id = ProofId(idx as u32);
                    while scope_stack.last() == Some(&id) {
                        scope_stack.pop();
                    }
                    if scope_stack.last().is_some_and(|end| *end < id) {
                        oversized = true;
                        break;
                    }
                    if let Some(end) = zero_scopes.get_mut(&id) {
                        *end = scope_stack.last().copied().unwrap_or(ProofId(u32::MAX));
                    }
                    if let ay_core::ProofStep::Anchor { end_step, .. } = step {
                        if *end_step <= id
                            || end_step.0 as usize >= proof.steps.len()
                            || scope_stack.last().is_some_and(|outer| end_step >= outer)
                            || scope_stack
                                .len()
                                .saturating_add(demand.len())
                                .saturating_add(zero_scopes.len())
                                >= MAX_DEMAND
                        {
                            oversized = true;
                            break;
                        }
                        if !self.admit_emission_work(scope_stack.len() as u64 + 1) {
                            oversized = true;
                            break;
                        }
                        scope_stack.reserve_exact(1);
                        scope_stack.push(*end_step);
                    }
                }
            }
        }
        if !oversized {
            for (idx, step) in proof.steps.iter().enumerate() {
                let mut cite = |premise: ProofId| {
                    if let Some(last) = demand.get_mut(&premise) {
                        *last = (*last).max(ProofId(idx as u32));
                    }
                };
                match step {
                    ay_core::ProofStep::Resolution {
                        clause1, clause2, ..
                    } => {
                        cite(*clause1);
                        cite(*clause2);
                    }
                    ay_core::ProofStep::Step { premises, .. } => {
                        for premise in premises {
                            cite(*premise);
                        }
                    }
                    _ => {}
                }
            }
            for (idx, step) in proof.steps.iter().enumerate() {
                if matches!(step, ay_core::ProofStep::Assume(_)) {
                    if let Some(last) = demand.get_mut(&ProofId(idx as u32)) {
                        *last = ProofId(u32::MAX);
                    }
                }
            }
        } else {
            demand = HashMap::default();
            zero_scopes = HashMap::default();
        }
        let mut retirement: Vec<_> = demand
            .iter()
            .filter(|(_, last)| last.0 != u32::MAX)
            .map(|(id, last)| (*last, *id))
            .collect();
        retirement.sort_unstable();
        let mut clauses = det_hash_map_with_capacity(demand.len());
        let mut bytes = demand
            .allocation_size()
            .saturating_add(zero_scopes.allocation_size())
            .saturating_add(scope_stack.capacity().saturating_mul(size_of::<ProofId>()))
            .saturating_add(clauses.allocation_size())
            .saturating_add(
                retirement
                    .capacity()
                    .saturating_mul(size_of::<(ProofId, ProofId)>()),
            );
        if surviving.saturating_add(bytes) > MAX_RECORDED_PRINTED_BYTES {
            demand = HashMap::default();
            retirement = Vec::new();
            clauses = HashMap::default();
            zero_scopes = HashMap::default();
            bytes = 0;
        }
        *self.printed_clause_demand.borrow_mut() = demand;
        *self.native_zero_cong_scopes.borrow_mut() = zero_scopes;
        *self.printed_clause_retirement.borrow_mut() = retirement;
        *self.printed_step_clauses.borrow_mut() = clauses;
        self.printed_clause_overhead_bytes.set(bytes);
        self.printed_clause_bytes
            .set(surviving.saturating_add(bytes));
    }

    /// Complete one sequential export write. Isolated `format_step` callers
    /// retain their repeatable behavior and never retire premises implicitly.
    pub(crate) fn finish_exported_step(&self, id: ProofId) {
        let retirement = self.printed_clause_retirement.borrow();
        let mut cursor = self.printed_clause_retirement_cursor.get();
        while let Some((last, premise)) = retirement.get(cursor) {
            if *last > id {
                break;
            }
            let clause = self.printed_step_clauses.borrow_mut().remove(premise);
            if let Some(PrintedClause::Literals(ids)) = clause {
                self.release_printed_atoms(ids);
            }
            cursor += 1;
        }
        self.printed_clause_retirement_cursor.set(cursor);
    }

    pub(super) fn record_printed_conclusion(&self, id: ProofId, rendered: &str) {
        if !self.printed_clause_demand.borrow().contains_key(&id) {
            return;
        }
        let _scratch_scope = ScratchScope::enter(
            &self.printed_replay_scratch,
            super::printed_command::MAX_STEP_BYTES,
            &self.printed_clause_bytes,
        );
        let entry = match read_wire_conclusion(id, rendered, &self.printed_replay_budget()) {
            None => PrintedClause::Unreadable,
            Some(WireConclusion::TooWide) => PrintedClause::Unbounded,
            Some(WireConclusion::Literals(literals)) => {
                match self.record_interned_clause(&literals) {
                    Some(interned) => PrintedClause::Literals(interned),
                    None => PrintedClause::Unbounded,
                }
            }
        };
        if matches!(entry, PrintedClause::Unreadable | PrintedClause::Unbounded)
            && ay_core::misc_cli_flags().debug_cert
        {
            ay_core::safe_eprintln!("c !! printed clause ledger at {id}: {entry:?}");
        }
        let previous = self.printed_step_clauses.borrow_mut().insert(id, entry);
        if let Some(PrintedClause::Literals(ids)) = previous {
            self.release_printed_atoms(ids);
        }
    }

    /// Admit all actual body/table/vector capacities before persistent mutation.
    fn record_interned_clause<T: AsRef<str>>(&self, literals: &[T]) -> Option<Vec<PrintedAtomId>> {
        if self.printed_clause_bytes.is_poisoned() {
            return None;
        }
        let _scratch_scope = ScratchScope::enter(
            &self.printed_replay_scratch,
            super::printed_command::MAX_STEP_BYTES,
            &self.printed_clause_bytes,
        );
        let scratch = self.printed_replay_budget();
        let mut parts = scratch.vector::<WireParts<'_>>(literals.len())?;
        let bodies = self.printed_clause_bodies.borrow();
        let index = self.printed_clause_atom_index.borrow();
        let mut fresh_bodies: DetHashMap<&str, ()> = det_hash_map_with_capacity(literals.len());
        let mut fresh_literals: DetHashMap<WireParts<'_>, ()> =
            det_hash_map_with_capacity(literals.len());
        let _fresh_maps = scratch.reserve(
            fresh_bodies
                .allocation_size()
                .checked_add(fresh_literals.allocation_size())?,
        )?;
        let mut fresh_bytes = 0usize;
        for literal in literals {
            let literal = literal.as_ref();
            if !self.admit_emission_work(literal.len() as u64) {
                return None;
            }
            let part = WireParts::read(literal);
            let known = bodies.get_key_value(part.body).and_then(|(body, _)| {
                index.get(&WireLiteral {
                    body: body.clone(),
                    shells: part.shells,
                })
            });
            if known.is_none() {
                fresh_literals.insert(part, ());
            }
            if !bodies.contains_key(part.body) && fresh_bodies.insert(part.body, ()).is_none() {
                fresh_bytes = fresh_bytes.checked_add(OwnedText::cost(part.body.len())?)?;
            }
            parts.push(part);
        }
        let slots = self.printed_clause_atom_texts.borrow();
        let needed_slots = slots.len().checked_add(
            fresh_literals
                .len()
                .saturating_sub(self.printed_clause_free_atoms.get()),
        )?;
        if needed_slots > ATOM_SLOT_MASK as usize + 1 {
            return None;
        }
        let mut grown_slots = (needed_slots > slots.capacity()).then(|| {
            Vec::with_capacity(needed_slots.max(slots.capacity().saturating_mul(2)).max(4))
        });
        let needed_index = index.len().checked_add(fresh_literals.len())?;
        let mut grown_index = (needed_index > index.capacity()).then(|| {
            det_hash_map_with_capacity(needed_index.max(index.capacity().saturating_mul(2)))
        });
        let needed_bodies = bodies.len().checked_add(fresh_bodies.len())?;
        let mut grown_bodies = (needed_bodies > bodies.capacity()).then(|| {
            det_hash_map_with_capacity(needed_bodies.max(bodies.capacity().saturating_mul(2)))
        });
        let slot_growth = grown_slots
            .as_ref()
            .map_or(0, |new: &Vec<PrintedAtomSlot>| {
                (new.capacity() - slots.capacity()).saturating_mul(size_of::<PrintedAtomSlot>())
            });
        let index_growth =
            grown_index
                .as_ref()
                .map_or(0, |new: &HashMap<WireLiteral, PrintedAtomId>| {
                    new.allocation_size()
                        .saturating_sub(index.allocation_size())
                });
        let body_growth = grown_bodies
            .as_ref()
            .map_or(0, |new: &HashMap<OwnedText, usize>| {
                new.allocation_size()
                    .saturating_sub(bodies.allocation_size())
            });
        let mut recorded = Vec::with_capacity(literals.len());
        let overhead = slot_growth
            .checked_add(index_growth)?
            .checked_add(body_growth)?
            .checked_add(
                recorded
                    .capacity()
                    .checked_mul(size_of::<PrintedAtomId>())?,
            )?;
        let _growth_scratch = scratch.reserve(
            grown_slots
                .as_ref()
                .map_or(0, |v| {
                    v.capacity().saturating_mul(size_of::<PrintedAtomSlot>())
                })
                .saturating_add(grown_index.as_ref().map_or(0, HashMap::allocation_size))
                .saturating_add(grown_bodies.as_ref().map_or(0, HashMap::allocation_size))
                .saturating_add(
                    recorded
                        .capacity()
                        .saturating_mul(size_of::<PrintedAtomId>()),
                ),
        )?;
        let total = self
            .printed_clause_bytes
            .get()
            .checked_add(fresh_bytes)?
            .checked_add(overhead)?;
        if total > MAX_RECORDED_PRINTED_BYTES {
            return None;
        }
        drop(slots);
        drop(index);
        drop(bodies);
        self.printed_clause_bytes.set(total);
        self.printed_clause_overhead_bytes.set(
            self.printed_clause_overhead_bytes
                .get()
                .saturating_add(overhead),
        );
        let mut index = self.printed_clause_atom_index.borrow_mut();
        let mut slots = self.printed_clause_atom_texts.borrow_mut();
        let mut bodies = self.printed_clause_bodies.borrow_mut();
        if let Some(mut new) = grown_slots.take() {
            new.append(&mut slots);
            *slots = new;
        }
        if let Some(mut new) = grown_index.take() {
            new.extend(index.drain());
            *index = new;
        }
        if let Some(mut new) = grown_bodies.take() {
            new.extend(bodies.drain());
            *bodies = new;
        }
        for part in parts.iter() {
            let body = if let Some((body, _)) = bodies.get_key_value(part.body) {
                body.clone()
            } else {
                let body = OwnedText::precharged(part.body, Rc::clone(&self.printed_clause_bytes));
                bodies.insert(body.clone(), 0);
                body
            };
            let key = WireLiteral {
                body,
                shells: part.shells,
            };
            let id = if let Some(id) = index.get(&key) {
                *id
            } else {
                let free = self.printed_clause_free_atom.get();
                let slot = if free == NO_FREE_ATOM {
                    slots.push(PrintedAtomSlot {
                        text: None,
                        references: 0,
                        next_free: NO_FREE_ATOM,
                        generation: 0,
                    });
                    slots.len() - 1
                } else {
                    self.printed_clause_free_atom
                        .set(slots[free as usize].next_free);
                    self.printed_clause_free_atoms
                        .set(self.printed_clause_free_atoms.get() - 1);
                    free as usize
                };
                *bodies.entry(key.body.clone()).or_insert(0) += 1;
                slots[slot].text = Some(key.clone());
                let id = atom_id(slot, slots[slot].generation);
                index.insert(key, id);
                id
            };
            slots[(id & ATOM_SLOT_MASK) as usize].references += 1;
            recorded.push(id);
        }
        Some(recorded)
    }

    fn release_printed_atoms(&self, ids: Vec<PrintedAtomId>) {
        let released = ids.capacity().saturating_mul(size_of::<PrintedAtomId>());
        let mut index = self.printed_clause_atom_index.borrow_mut();
        let mut slots = self.printed_clause_atom_texts.borrow_mut();
        let mut bodies = self.printed_clause_bodies.borrow_mut();
        for id in &ids {
            let Some(slot) = slots.get_mut((id & ATOM_SLOT_MASK) as usize) else {
                continue;
            };
            if slot.generation != (id >> ATOM_SLOT_BITS) as u16 || slot.references == 0 {
                continue;
            }
            slot.references -= 1;
            if slot.references != 0 {
                continue;
            }
            let Some(text) = slot.text.take() else {
                continue;
            };
            index.remove(&text);
            if let Some(count) = bodies.get_mut(text.body.as_ref()) {
                *count -= 1;
                if *count == 0 {
                    bodies.remove(text.body.as_ref());
                }
            }
            // The text's private owner refunds its allocation only after ALL
            // wire handles, including escaped readers, have actually dropped.
            drop(text);
            if slot.generation < MAX_ATOM_GENERATION {
                slot.generation += 1;
                slot.next_free = self.printed_clause_free_atom.get();
                self.printed_clause_free_atom.set(id & ATOM_SLOT_MASK);
                self.printed_clause_free_atoms
                    .set(self.printed_clause_free_atoms.get() + 1);
            }
        }
        drop(ids);
        match self
            .printed_clause_overhead_bytes
            .get()
            .checked_sub(released)
        {
            Some(n) => self.printed_clause_overhead_bytes.set(n),
            None => self.printed_clause_bytes.poison(),
        }
        self.printed_clause_bytes.subtract(released);
    }

    fn printed_wire_literals(&self, ids: &[PrintedAtomId]) -> Option<Tracked<Vec<WireLiteral>>> {
        if self.printed_clause_bytes.is_poisoned() {
            return None;
        }
        let _scope = ScratchScope::enter(
            &self.printed_replay_scratch,
            super::printed_command::MAX_STEP_BYTES,
            &self.printed_clause_bytes,
        );
        let budget = self.printed_replay_budget();
        let mut lease = budget.reserve(ids.len().checked_mul(size_of::<WireLiteral>())?)?;
        let slots = self.printed_clause_atom_texts.borrow();
        let mut out = Vec::with_capacity(ids.len());
        for id in ids {
            let slot = slots.get((id & ATOM_SLOT_MASK) as usize)?;
            if slot.generation != (id >> ATOM_SLOT_BITS) as u16 {
                return None;
            }
            out.push(slot.text.clone()?);
        }
        lease.resize(
            out.capacity().checked_mul(size_of::<WireLiteral>())?,
            budget.limit,
        )?;
        Some(Tracked::reserved(out, lease))
    }

    fn materialized_wire_literals(&self, wires: &[WireLiteral]) -> Option<Tracked<Vec<OwnedText>>> {
        let _scope = ScratchScope::enter(
            &self.printed_replay_scratch,
            super::printed_command::MAX_STEP_BYTES,
            &self.printed_clause_bytes,
        );
        let scratch = self.printed_replay_budget();
        let mut lease = scratch.reserve(wires.len().checked_mul(size_of::<OwnedText>())?)?;
        let retained = TextBudget::retained(
            Rc::clone(&self.printed_clause_bytes),
            MAX_RECORDED_PRINTED_BYTES,
        );
        let mut out = Vec::with_capacity(wires.len());
        for wire in wires {
            out.push(wire.materialize(&retained)?);
        }
        lease.resize(
            out.capacity().checked_mul(size_of::<OwnedText>())?,
            scratch.limit,
        )?;
        Some(Tracked::reserved(out, lease))
    }

    /// Complete-text readers retain their allocation's private charge.
    pub(super) fn printed_atom_texts(
        &self,
        ids: &[PrintedAtomId],
    ) -> Option<Tracked<Vec<OwnedText>>> {
        let _scope = ScratchScope::enter(
            &self.printed_replay_scratch,
            super::printed_command::MAX_STEP_BYTES,
            &self.printed_clause_bytes,
        );
        self.materialized_wire_literals(&self.printed_wire_literals(ids)?)
    }

    fn printed_replay_budget(&self) -> TextBudget {
        self.printed_replay_scratch
            .borrow()
            .as_ref()
            .cloned()
            .unwrap_or_else(|| {
                TextBudget::with_parent(
                    super::printed_command::MAX_STEP_BYTES,
                    &self.printed_clause_bytes,
                )
            })
    }

    /// The replay identity of one printed literal, computed once per distinct
    /// printed text and reused by every step that cites it.
    ///
    /// This is where the judgement's text is READ, so this is where the
    /// emission work budget is charged for reading it — once, not once per
    /// citing step. Past the memo's cap the identity is still computed and
    /// still charged; it is simply not remembered, which costs time and never
    /// evidence.
    fn printed_literal_identity(&self, text: &str) -> Option<PrintedLiteral> {
        let _scope = ScratchScope::enter(
            &self.printed_replay_scratch,
            super::printed_command::MAX_STEP_BYTES,
            &self.printed_clause_bytes,
        );
        if self.check_emission_progress(0).is_err() {
            return None;
        }
        if let Some(found) = self.printed_literal_identities.borrow().get(text) {
            return Some(found.clone());
        }
        if !self.admit_emission_work(text.len() as u64) {
            return None;
        }
        let budget = self.printed_replay_budget();
        let (atom, depth) = wire_text::decoded_body(text)?;
        let mut nodes = 0;
        let identity = PrintedLiteral {
            atom: budget.copy(atom)?,
            spelling: wire_text::normalise_owned(atom, 0, &mut nodes, &budget)?,
            depth,
        };
        let memo = self.printed_literal_identities.borrow();
        let mut grown = (memo.len() == memo.capacity()).then(|| {
            det_hash_map_with_capacity((memo.len() + 1).max(memo.capacity().saturating_mul(2)))
        });
        let _memo_growth = budget.reserve(grown.as_ref().map_or(0, HashMap::allocation_size))?;
        let growth = grown
            .as_ref()
            .map_or(0, |new: &HashMap<Rc<str>, PrintedLiteral>| {
                new.allocation_size().saturating_sub(memo.allocation_size())
            });
        let cost = rc_text_bytes(text)
            .saturating_add(identity.atom.allocation_bytes())
            .saturating_add(identity.spelling.allocation_bytes())
            .saturating_add(2 * COUNTER_BYTES)
            .saturating_add(growth);
        let total = self
            .printed_literal_identity_bytes
            .get()
            .saturating_add(cost);
        drop(memo);
        if total <= MAX_RECORDED_PRINTED_BYTES {
            let mut memo = self.printed_literal_identities.borrow_mut();
            if let Some(mut new) = grown.take() {
                new.extend(memo.drain());
                *memo = new;
            }
            memo.insert(Rc::from(text), identity.clone());
            self.printed_literal_identity_bytes.set(total);
        }
        Some(identity)
    }

    fn printed_wire_identity(&self, literal: &WireLiteral) -> Option<PrintedLiteral> {
        let _scope = ScratchScope::enter(
            &self.printed_replay_scratch,
            super::printed_command::MAX_STEP_BYTES,
            &self.printed_clause_bytes,
        );
        if self.check_emission_progress(0).is_err() {
            return None;
        }
        if literal.shells == 0 {
            return self.printed_literal_identity(&literal.body);
        }
        if let Some(found) = self.printed_wire_identities.borrow().get(literal) {
            return Some(found.clone());
        }
        if literal.shells > MAX_NORMALISED_DEPTH || !self.admit_emission_work(literal.len()? as u64)
        {
            return None;
        }
        let mut cursor = 0;
        let complete =
            super::surface_tokens::next_smt_term_slice(&literal.body, &mut cursor).ok()??;
        if complete.as_ptr() != literal.body.as_ptr()
            || complete.len() != literal.body.len()
            || super::surface_tokens::next_smt_term_slice(&literal.body, &mut cursor)
                .ok()?
                .is_some()
        {
            return None;
        }
        let budget = self.printed_replay_budget();
        let (atom, remaining) = wire_text::decoded_body(&literal.body)?;
        let depth = remaining.checked_add(literal.shells)?;
        let mut nodes = 0;
        let identity = PrintedLiteral {
            atom: budget.copy(atom)?,
            spelling: wire_text::normalise_owned(atom, 0, &mut nodes, &budget)?,
            depth,
        };
        // This key owns the exact raw body and complete shell count. It never
        // pins a retained-ledger body through the normalized identity memo.
        let key_body = if identity.atom.as_ref() == literal.body.as_ref() {
            identity.atom.clone()
        } else {
            budget.copy(&literal.body)?
        };
        let key = WireLiteral {
            body: key_body,
            shells: literal.shells,
        };
        let memo = self.printed_wire_identities.borrow();
        let mut grown = (memo.len() == memo.capacity()).then(|| {
            det_hash_map_with_capacity((memo.len() + 1).max(memo.capacity().saturating_mul(2)))
        });
        let _growth_owner = budget.reserve(grown.as_ref().map_or(0, HashMap::allocation_size))?;
        let growth = grown
            .as_ref()
            .map_or(0, |new: &HashMap<WireLiteral, PrintedLiteral>| {
                new.allocation_size().saturating_sub(memo.allocation_size())
            });
        let mut cost = key
            .body
            .allocation_bytes()
            .saturating_add(3 * COUNTER_BYTES)
            .saturating_add(growth);
        if !key.body.shares_allocation(&identity.atom) {
            cost = cost.saturating_add(identity.atom.allocation_bytes());
        }
        if !key.body.shares_allocation(&identity.spelling)
            && !identity.atom.shares_allocation(&identity.spelling)
        {
            cost = cost.saturating_add(identity.spelling.allocation_bytes());
        }
        let total = self
            .printed_literal_identity_bytes
            .get()
            .saturating_add(cost);
        drop(memo);
        if total <= MAX_RECORDED_PRINTED_BYTES {
            let mut memo = self.printed_wire_identities.borrow_mut();
            if let Some(mut new) = grown.take() {
                new.extend(memo.drain());
                *memo = new;
            }
            memo.insert(key, identity.clone());
            self.printed_literal_identity_bytes.set(total);
        }
        Some(identity)
    }

    #[cfg(test)]
    fn decode_all<C: AsRef<[OwnedText]>>(
        &self,
        printed: &[C],
    ) -> Option<Tracked<Vec<Vec<PrintedLiteral>>>> {
        let _scope = ScratchScope::enter(
            &self.printed_replay_scratch,
            super::printed_command::MAX_STEP_BYTES,
            &self.printed_clause_bytes,
        );
        let budget = self.printed_replay_budget();
        let count = printed
            .iter()
            .try_fold(0usize, |n, row| n.checked_add(row.as_ref().len()))?;
        let bytes = printed
            .len()
            .checked_mul(size_of::<Vec<PrintedLiteral>>())?
            .checked_add(count.checked_mul(size_of::<PrintedLiteral>())?)?;
        let mut lease = budget.reserve(bytes)?;
        let mut result = Vec::with_capacity(printed.len());
        for row in printed {
            let mut decoded = Vec::with_capacity(row.as_ref().len());
            for literal in row.as_ref() {
                decoded.push(self.printed_literal_identity(literal)?);
            }
            result.push(decoded);
        }
        lease.resize(wire_text::matrix_bytes(&result)?, budget.limit)?;
        Some(Tracked::reserved(result, lease))
    }

    fn decode_wire_all<C: AsRef<[WireLiteral]>>(
        &self,
        printed: &[C],
    ) -> Option<Tracked<Vec<Vec<PrintedLiteral>>>> {
        let _scope = ScratchScope::enter(
            &self.printed_replay_scratch,
            super::printed_command::MAX_STEP_BYTES,
            &self.printed_clause_bytes,
        );
        let budget = self.printed_replay_budget();
        let count = printed
            .iter()
            .try_fold(0usize, |n, row| n.checked_add(row.as_ref().len()))?;
        let bytes = printed
            .len()
            .checked_mul(size_of::<Vec<PrintedLiteral>>())?
            .checked_add(count.checked_mul(size_of::<PrintedLiteral>())?)?;
        let mut lease = budget.reserve(bytes)?;
        let mut result = Vec::with_capacity(printed.len());
        for row in printed {
            let mut decoded = Vec::with_capacity(row.as_ref().len());
            for literal in row.as_ref() {
                decoded.push(self.printed_wire_identity(literal)?);
            }
            result.push(decoded);
        }
        lease.resize(wire_text::matrix_bytes(&result)?, budget.limit)?;
        Some(Tracked::reserved(result, lease))
    }

    fn owned_normalise(&self, text: &str, nodes: &mut usize) -> Option<OwnedText> {
        if !self.admit_emission_work(text.len() as u64) {
            return None;
        }
        wire_text::normalise_owned(text, 0, nodes, &self.printed_replay_budget())
    }
    fn replay_copy(
        &self,
        source: &[Vec<PrintedLiteral>],
        extra: usize,
    ) -> Option<Tracked<Vec<Vec<PrintedLiteral>>>> {
        Tracked::copy_replay(source, extra, &self.printed_replay_budget())
    }

    fn printed_rup_entail(
        &self,
        premises: &[Vec<PrintedLiteral>],
        conclusion: &[PrintedLiteral],
    ) -> Option<bool> {
        let _scope = ScratchScope::enter(
            &self.printed_replay_scratch,
            super::printed_command::MAX_STEP_BYTES,
            &self.printed_clause_bytes,
        );
        printed_clauses_rup_entail_with_budget(premises, conclusion, &self.printed_replay_budget())
    }

    /// The honest floor of every printed judgement: this step's own clause
    /// under the unproved rule, in a PUBLISHED document.
    pub(super) fn printed_hole(&self, id: ProofId, clause: &[TermId]) -> String {
        self.printed_hole_over(id, &self.format_clause(clause))
    }

    /// [`Self::printed_hole`] over a clause the caller has ALREADY rendered.
    ///
    /// The rendering is the charged operation, so a judgement that holds the
    /// text it judged reuses it here rather than paying for the same bytes
    /// a second time (see [`Self::judge_printed_resolution`]).
    pub(super) fn printed_hole_over(&self, id: ProofId, clause_str: &str) -> String {
        format!(
            "(step {id} {clause_str} :rule {})",
            ay_core::UNPROVED_STEP_RULE
        )
    }

    /// Whether a resolution's printed spelling is one THIS PRINTER chose:
    /// some literal of the step's clause, or of a premise's internal clause,
    /// has a subterm the Skolem `choice` channel spells.
    ///
    /// The floor `surface_and_pos` got on 2026-09-16 (`061e437f66`), applied
    /// to the other judgement a carried authored body reaches. When the
    /// divergence is the printer's own (a Skolem instance rendered from an
    /// authored quantifier body, installed by `insert_skolem_override`), a
    /// refusal here refuses the WHOLE EXPORT of a document the base
    /// publishes: no certificate in the default posture, `unsat` moved to
    /// `unknown` under `--strict-proofs`, exit 1 with no verdict under
    /// `--proof FILE` (#8821). MEASURED on `(exists ((z Int)) (not (or (< 0
    /// (- 0 1)) (>= (g z) z))))`, whose carried body mixed two identities and
    /// died at `t16`. The producer's own spellings keep failing loud — this
    /// is not a general relaxation of #8821.
    fn resolution_reaches_printer_channel(&self, clause: &[TermId], premises: &[ProofId]) -> bool {
        let skolem = self.skolem_overrides.borrow();
        if skolem.is_empty() {
            return false;
        }
        let proof_clauses = self.proof_clauses.borrow();
        let mut stack: Vec<TermId> = clause.to_vec();
        for premise in premises {
            if let Some(premise_clause) = proof_clauses.get(premise) {
                stack.extend(premise_clause.iter().copied());
            }
        }
        let mut seen: DetHashSet<TermId> = DetHashSet::default();
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            if skolem.contains_key(&term) {
                return true;
            }
            stack.extend(self.terms.children(term));
        }
        false
    }

    /// Judge a `resolution` / `th_resolution` step over the printed text.
    ///
    /// `clause_str` is the conclusion AS THE CALLER WILL SHIP IT — rendered
    /// once, by the caller, and read here; on `Ok(None)` the caller emits
    /// exactly that string. The judgement used to render the clause itself
    /// and the caller then rendered it again for the emitted step, and the
    /// emission work budget was charged for both (`write_term_into` charges a
    /// cache hit its full length). MEASURED 2026-09-19 on QF_UF
    /// `QG-classification/qg5/iso_icl641`, default posture: the base's ledger
    /// fills at `t2250` and it holes the ~2,000 later resolutions without
    /// reading them, while this judgement — able to read them — charged each
    /// ~5.9 KB conclusion twice, ran the 67,108,864-unit budget out at
    /// `t4482` (67,108,933) on a document the base finishes with under 2 %
    /// headroom, and DISCARDED a 20.7 MB certificate the base publishes. One
    /// rendering, one charge.
    ///
    /// * `Err(EmissionBudgetExhausted)` — the budget is already exhausted, so
    ///   the text a judgement would read is not the document: past
    ///   exhaustion `write_term_into` renders every term as the private
    ///   `@a2b_emission_budget_exhausted` placeholder. On the document above
    ///   the replay ran over a conclusion 32 of whose 43 literals were that
    ///   placeholder, failed, and refused the export as "the printed
    ///   premises do not eliminate the printed resolution pivot" — a
    ///   diagnosis of a divergence that did not exist, in place of the
    ///   exhaustion that did. An exhausted budget is reported AS exhaustion,
    ///   before any text is read. A judgement never runs over placeholders;
    ///   if one ever does, that is a defect here, not a decline.
    /// * `Ok(None)` — emit the step exactly as the caller would have: the
    ///   printed replay succeeds, or the ledger is inactive (an isolated
    ///   helper or a test rendering one step, with nothing recorded to judge
    ///   against).
    /// * `Ok(Some(text))` — emit this rendering instead: a repair, or the
    ///   honest hole over the step's own clause. The hole is the answer
    ///   whenever the judgement CANNOT READ the object the checker will read
    ///   — a premise whose printed clause was unreadable, unrecorded or past
    ///   the ledger's bounds, or a step wider than the work bound — and
    ///   whenever the divergence is a spelling this printer chose
    ///   ([`Self::resolution_reaches_printer_channel`]). Until 2026-09-16 the
    ///   first family shipped UNCHANGED, which is how a command spanning
    ///   lines reopened the tenth false green.
    /// * `Err(..)` — the printed step is not checkable, no bridge reaches it,
    ///   and the spelling is the producer's. Decline the export.
    pub(super) fn judge_printed_resolution(
        &self,
        id: ProofId,
        clause: &[TermId],
        clause_str: &str,
        premises: &[ProofId],
    ) -> Result<Option<String>, AlethePrintError> {
        let _scratch_scope = ScratchScope::enter(
            &self.printed_replay_scratch,
            super::printed_command::MAX_STEP_BYTES,
            &self.printed_clause_bytes,
        );
        if premises.is_empty() || !self.printed_clause_ledger_active.get() {
            return Ok(None);
        }
        // Exhaustion is monotone (`work` never decreases), so a budget that
        // is not exhausted NOW was not exhausted when `clause_str` or any
        // ledgered premise was rendered, and none of them holds a
        // placeholder. Checked before a byte is read.
        if self.work_budget_exhausted() {
            return Err(self.work_budget_error(id.0));
        }
        let decline = |reason: &str| -> Result<Option<String>, AlethePrintError> {
            if ay_core::misc_cli_flags().debug_cert {
                ay_core::safe_eprintln!("c !! printed resolution at {id}: hole ({reason})");
            }
            Ok(Some(self.printed_hole_over(id, clause_str)))
        };
        if clause.len() > MAX_JUDGED_LITERALS {
            return decline("conclusion wider than the judged bound");
        }
        let scratch = self.printed_replay_budget();
        let Some(mut wire_premises) = scratch.vector::<Tracked<Vec<WireLiteral>>>(premises.len())
        else {
            return decline("printed premise scratch capacity exceeded");
        };
        {
            let recorded = self.printed_step_clauses.borrow();
            for premise in premises {
                match recorded.get(premise) {
                    Some(PrintedClause::Literals(ids)) => match self.printed_wire_literals(ids) {
                        Some(texts) => wire_premises.push(texts),
                        None => {
                            return decline("premise atom unreadable or scratch bound exceeded")
                        }
                    },
                    Some(PrintedClause::Unreadable) => {
                        return decline("premise printed no readable clause")
                    }
                    Some(PrintedClause::Unbounded) => {
                        return decline("premise is past the ledger bounds")
                    }
                    None => return decline("premise was never recorded"),
                }
            }
        }
        let total: usize = wire_premises.iter().map(|row| row.len()).sum();
        if total > MAX_JUDGED_LITERALS {
            return decline("premises wider than the judged bound");
        }
        let Some(printed_conclusion) = replay_clause_slices(clause_str, &scratch) else {
            return decline("conclusion unreadable or scratch capacity exceeded");
        };

        let Some(decoded_premises) = self.decode_wire_all(&wire_premises) else {
            return decline("premise replay unreadable or scratch capacity exceeded");
        };
        let Some(mut decoded_conclusion) =
            scratch.vector::<PrintedLiteral>(printed_conclusion.len())
        else {
            return decline("conclusion replay scratch capacity exceeded");
        };
        for literal in printed_conclusion.iter() {
            let Some(decoded) = self.printed_literal_identity(literal) else {
                return decline("conclusion replay unreadable or scratch capacity exceeded");
            };
            decoded_conclusion.push(decoded);
        }

        match self.printed_rup_entail(&decoded_premises, &decoded_conclusion) {
            Some(true) => return Ok(None),
            Some(false) => (),
            None => return decline("printed replay scratch capacity exceeded"),
        }

        let Some(mut printed_premises) =
            scratch.vector::<Tracked<Vec<OwnedText>>>(wire_premises.len())
        else {
            return decline("printed materialization scratch capacity exceeded");
        };
        for row in wire_premises.iter() {
            let Some(texts) = self.materialized_wire_literals(row) else {
                return decline("exact wire materialization exceeds its retained owner");
            };
            printed_premises.push(texts);
        }
        if let Some(text) = self.printed_pivot_bridge(
            id,
            clause_str,
            premises,
            &printed_premises,
            &decoded_premises,
            &decoded_conclusion,
        ) {
            return Ok(Some(text));
        }

        // THE FLOOR: a divergence in a spelling this printer chose is the
        // honest hole in a published document, never a refused export.
        if self.resolution_reaches_printer_channel(clause, premises) {
            return decline("the printed pivot is spelled by the printer's own Skolem channel");
        }

        Err(AlethePrintError::InvalidSurfaceStep {
            id,
            reason: format!(
                "the printed premises do not eliminate the printed resolution pivot{}",
                match unpaired_printed_literal(&decoded_premises, &decoded_conclusion) {
                    Some(literal) => format!(", starting at `{literal}`"),
                    None => String::new(),
                }
            ),
        })
    }

    /// Repair a printed resolution whose pivot prints as two different
    /// spellings of one arithmetic comparison.
    ///
    /// Only a two-premise step is repaired, and only when adding the bridge
    /// clause makes the WHOLE printed step replay — so this never turns a step
    /// that was wrong for another reason into one that merely looks repaired.
    fn printed_arithmetic_pivot_bridge(
        &self,
        id: ProofId,
        clause_str: &str,
        premises: &[ProofId],
        printed_premises: &[Tracked<Vec<OwnedText>>],
        decoded_premises: &[Vec<PrintedLiteral>],
        decoded_conclusion: &[PrintedLiteral],
    ) -> Option<String> {
        let [left_premise, right_premise] = premises else {
            return None;
        };
        let [left, right] = decoded_premises else {
            return None;
        };

        let mut candidate: Option<(OwnedText, OwnedText, ProofId, ProofId)> = None;
        for (left_index, left_literal) in left.iter().enumerate() {
            for (right_index, right_literal) in right.iter().enumerate() {
                // Exactly one side carries the atom positively; the printed
                // texts must differ, or the pair would already be a complement
                // and the replay above would have succeeded.
                let (positive, negative, positive_premise, negative_premise) =
                    match (left_literal.positive(), right_literal.positive()) {
                        (true, false) => (
                            printed_premises[0][left_index].clone(),
                            right_literal.atom.clone(),
                            *left_premise,
                            *right_premise,
                        ),
                        (false, true) => (
                            printed_premises[1][right_index].clone(),
                            left_literal.atom.clone(),
                            *right_premise,
                            *left_premise,
                        ),
                        _ => continue,
                    };
                let mut nodes = 0;
                if self.owned_normalise(&positive, &mut nodes)?
                    == self.owned_normalise(&negative, &mut nodes)?
                {
                    continue;
                }
                // The bridge claims `positive => negative` as a linear
                // tautology, judged by reparsing the printed text.
                if !crate::printed_la_generic_unit_implication_is_supported(&positive, &negative) {
                    continue;
                }
                // Deterministic and unambiguous: two different repairs for one
                // step is a shape this bridge does not understand.
                if candidate
                    .as_ref()
                    .is_some_and(|prior| prior.0 != positive || prior.1 != negative)
                {
                    return None;
                }
                candidate = Some((positive, negative, positive_premise, negative_premise));
            }
        }
        let (positive, negative, positive_premise, negative_premise) = candidate?;

        // Replay the repaired step exactly as the checker will see it.
        let bridge_clause = vec![
            self.printed_literal_identity(&format!("(not {positive})"))?,
            self.printed_literal_identity(&negative)?,
        ];
        let mut repaired = self.replay_copy(decoded_premises, 1)?;
        repaired.push_replay(bridge_clause)?;
        repaired.seal_replay(&self.printed_replay_budget())?;
        if !self.printed_rup_entail(&repaired, decoded_conclusion)? {
            return None;
        }

        Some(format!(
            "(step {id}.p (cl (not {positive}) {negative}) :rule la_generic :args (1 1))\n\
             (step {id} {clause_str} :rule resolution :premises ({positive_premise} {id}.p {negative_premise}))"
        ))
    }
}

#[cfg(test)]
#[path = "../alethe_printer_printed_resolution_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "../alethe_printer_printed_resolution_verify_tests.rs"]
mod verify_tests;

#[cfg(test)]
#[path = "../alethe_printer_printed_ledger_tests.rs"]
mod ledger_tests;

/// Name a printed premise literal the replay could not discharge: one that is
/// neither a literal of the printed conclusion nor complemented by a literal of
/// another printed premise.
///
/// A refusal that only says "the pivot was not eliminated" leaves the operator
/// to diff two multi-megabyte clauses by hand. MEASURED 2026-09-18 on QF_UF
/// `QG-classification/qg5/iso_icl641`, where this guard declines the
/// synthesized-default export at `t4482` while the SAME file's `--proof FILE`
/// export replays and publishes: without the literal, there is no way to tell
/// from the disclosure which of 43 printed literals diverged.
fn unpaired_printed_literal(
    premises: &[Vec<PrintedLiteral>],
    conclusion: &[PrintedLiteral],
) -> Option<String> {
    let in_conclusion: DetHashSet<(&str, bool)> = conclusion
        .iter()
        .map(|literal| (&*literal.spelling, literal.positive()))
        .collect();
    let in_premises: DetHashSet<(&str, bool)> = premises
        .iter()
        .flatten()
        .map(|literal| (&*literal.spelling, literal.positive()))
        .collect();
    premises
        .iter()
        .flatten()
        .find(|literal| {
            let key = (&*literal.spelling, literal.positive());
            !in_conclusion.contains(&key) && !in_premises.contains(&(key.0, !key.1))
        })
        .map(|literal| literal.atom.to_string())
}

#[cfg(test)]
#[path = "printed_resolution/wire_storage_tests.rs"]
mod wire_storage_tests;
