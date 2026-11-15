// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! VeriPB (pseudo-Boolean proof, version 3.0) writer.
//!
//! # Why this exists
//!
//! AY's symmetry-breaking routes (the aux-free WLOG chains and the orbitope
//! staircase) derive clauses that are *substitution redundant* (SR), not RUP or
//! RAT. On the DRAT surface those are serialized as DSR `a`-lines carrying a
//! substitution witness — and only `dsr-trim` accepts them: `drat-trim` and
//! `dpr-trim` both return `s NOT VERIFIED` (measured 2026-08-24). The official
//! SAT-COMP 2026 checker menu is `dpr-trim` / `gratgen` / `VeriPB`, the
//! registrant declares one up front, and a rejected UNSAT proof is
//! disqualifying — so on the DRAT surface the whole symmetry bucket has to be
//! clamped off (see `proof_capability::declared_checker_accepts_sr_witnesses`).
//!
//! VeriPB is the way back: it is on the menu AND its `red` (redundance-based
//! strengthening) rule takes a substitution witness natively, which is exactly
//! the SR side condition
//!
//! ```text
//!     F ∧ ¬C ⊨ (F ∧ C)↾ω
//! ```
//!
//! that `dsr-trim` checks. The correspondence is direct, so this writer is a
//! serializer, not a translator with a proof obligation of its own.
//!
//! # Rule mapping
//!
//! | AY proof step                       | VeriPB rule                          |
//! |-------------------------------------|--------------------------------------|
//! | `add(C)`, C non-empty               | `red <C> : x_p -> 1 ;` (p = `C[0]`)  |
//! | `add(C)`, C empty                   | `rup >= 1 ;` + output/conclusion tail|
//! | `add_pr(C, w)` / `add_sr(C, w)`     | `red <C> : <ω(w)> ;`                 |
//! | `delete(C)`, C derived here         | `del id <n> ;` (see below)           |
//! | `delete(C)`, otherwise              | `del spec <C> ;`                     |
//!
//! Plain additions become `red` with the *pivot* witness rather than `rup`
//! because a DRAT `a`-line is RAT on its first literal, not necessarily RUP:
//! extension-variable definitions (the Tseitin-chunked XOR ladders) and the
//! HHW image-and-chain fragment are RAT-only. `red C : p -> 1` is exactly the
//! RAT condition on `p`, and it subsumes RUP — VeriPB tries a whole-subproof
//! RUP autoprove first, so a genuinely-RUP addition costs the same as `rup`.
//!
//! # Formula file
//!
//! VeriPB parses DIMACS CNF directly (variable `i` is `x<i>`, clause = sum of
//! literals `>= 1`), so no OPB translation is emitted or needed: the checker is
//! invoked as `veripb <instance>.cnf <proof>.pbp`.
//!
//! # Which VeriPB
//!
//! Not any of them. Published 3.0.2 carries eight confirmed wrong-verdict
//! defects — it prints `s VERIFIED UNSATISFIABLE` for satisfiable formulas
//! given the right small proof — so this crate's claims are made against the
//! checker `ci/veripb.pin` names (upstream `4bb10c2c` plus the reviewed AY
//! soundness patch), which must reject all nine `ci/veripb-soundness/`
//! fixtures before any verdict of its own is believed. Measured 2026-08-24 on
//! this machine: a stock build of upstream `main` ACCEPTED five of those nine;
//! the pinned build rejected all nine. Every number in this module's history
//! is a pinned-checker number.
//!
//! # Conclusion
//!
//! The trailer (`output NONE; conclusion UNSAT; end pseudo-Boolean proof;`) is
//! written when the empty clause is added, which is the single centralized
//! UNSAT finalization point (`solve::finalize_unsat`). Writes after that are
//! no-ops: VeriPB ignores everything past the end line, and a doubled trailer
//! would be a parse error. A run that never derives the empty clause leaves an
//! unterminated file, which is the correct outcome — a non-UNSAT proof sidecar
//! is deleted by the caller.

use crate::literal::Literal;
use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher};
use std::io::{self, Write};

mod anchor;
mod collect;
mod definition;

const VERIPB_HEADER: &[u8] = b"pseudo-Boolean proof version 3.0\n";
const VERIPB_TRAILER: &[u8] = b"output NONE;\nconclusion UNSAT;\nend pseudo-Boolean proof;\n";

const VERIPB_LINE_INITIAL_CAPACITY: usize = 256;
const VERIPB_LINE_MAX_RETAINED_CAPACITY: usize = 256 * 1024;

/// The image of a variable's *positive* literal under a witness substitution.
///
/// Mirrors `ay_drat_check::checker::sr::SubImage`: `dsr-trim` stores the image
/// of the positive literal and re-applies the sign on lookup, so a mapping read
/// off a negative source literal is stored negated.
#[derive(Clone, Copy, PartialEq, Eq)]
enum SubImage {
    True,
    False,
    Lit(Literal),
}

impl SubImage {
    fn negate(self) -> Self {
        match self {
            Self::True => Self::False,
            Self::False => Self::True,
            Self::Lit(lit) => Self::Lit(lit.negated()),
        }
    }
}

/// Write `x<n>` / `~x<n>` for a literal, using VeriPB's DIMACS-CNF variable
/// naming (`i` ↦ `x<i>`).
fn push_literal_name(buf: &mut Vec<u8>, lit: Literal) {
    let dimacs = lit.to_dimacs();
    if dimacs < 0 {
        buf.push(b'~');
    }
    buf.push(b'x');
    push_u32_decimal(buf, dimacs.unsigned_abs());
}

fn push_u32_decimal(buf: &mut Vec<u8>, value: u32) {
    push_u64_decimal(buf, u64::from(value));
}

/// Append `value` in decimal. The digits are produced least-significant first
/// straight into `buf` and the appended run is then reversed in place, so no
/// fixed-size digit buffer (and no index into one) is needed.
fn push_u64_decimal(buf: &mut Vec<u8>, mut value: u64) {
    if value == 0 {
        buf.push(b'0');
        return;
    }
    let start = buf.len();
    while value != 0 {
        // `value % 10` is below 16 and b'0' is 0x30, so OR-ing is the ASCII
        // digit exactly (no carry into the high nibble).
        buf.push(b'0' | (value % 10) as u8);
        value /= 10;
    }
    if let Some(digits) = buf.get_mut(start..) {
        digits.reverse();
    }
}

/// Serialize a clause as an OPB-style constraint: `1 l1 1 l2 ... >= 1`.
///
/// The empty clause is `>= 1` — a degree-1 constraint with no terms, i.e.
/// contradiction, which is what VeriPB expects from `rup >= 1 ;`.
fn push_clause_constraint(buf: &mut Vec<u8>, clause: &[Literal]) {
    for lit in clause {
        buf.extend_from_slice(b"1 ");
        push_literal_name(buf, *lit);
        buf.push(b' ');
    }
    buf.extend_from_slice(b">= 1");
}

/// Serialize a DSR/DPR witness token stream as a VeriPB substitution.
///
/// Layout (identical to `DratWriter::add_sr` and `dsr-trim`'s
/// `parse_sr_clause_and_witness`): `pivot [pr-atoms…] [pivot(sep) (l m)…]`.
/// `witness[0]` is the pivot and maps to true; atoms before the second pivot
/// occurrence each map to true (the PR part); after the separating second
/// pivot, tokens are read in `(l, m)` pairs giving `σ(l) = m`.
///
/// Assignments are normalized to the positive literal's image exactly as
/// `Subst::set` does, so the emitted `x<v> -> …` mappings are the same map the
/// SR kernel builds. Re-assignment of a variable keeps its first emission slot
/// and takes the last value (`dsr-trim` permits this only for the pivot
/// variable); VeriPB rejects a substitution that names one variable twice.
fn push_witness_substitution(buf: &mut Vec<u8>, witness: &[Literal]) {
    push_substitution(buf, &witness_map(witness));
}

/// The substitution a DSR/DPR witness token stream denotes (see
/// [`push_witness_substitution`]), one entry per variable in first-emission
/// order.
fn witness_map(witness: &[Literal]) -> Vec<(u32, SubImage)> {
    let Some(&pivot) = witness.first() else {
        return Vec::new();
    };

    // Witnesses are short (a transposition chain over one symmetry generator),
    // so a linear-scan association list beats allocating a variable-indexed map
    // per step.
    // The reservation is only a capacity hint (the map holds at most one
    // entry per witness token): if the allocator refuses it, `push` below
    // grows the vector as needed, exactly as before.
    let mut map: Vec<(u32, SubImage)> = Vec::new();
    let _ = map.try_reserve_exact(witness.len());
    let set = |map: &mut Vec<(u32, SubImage)>, lit: Literal, image: SubImage| {
        let stored = if lit.is_positive() {
            image
        } else {
            image.negate()
        };
        let var = lit.variable().0;
        if let Some(entry) = map.iter_mut().find(|(existing, _)| *existing == var) {
            entry.1 = stored;
        } else {
            map.push((var, stored));
        }
    };

    set(&mut map, pivot, SubImage::True);

    let mut seen_divider = false;
    let mut index = 1;
    // `index` is always below `witness.len()` when read, so the increments
    // cannot overflow; `checked_add` makes that explicit and ends the scan
    // (like running off the end) if it ever could.
    while let Some(&lit) = witness.get(index) {
        let Some(after) = index.checked_add(1) else {
            break;
        };
        if seen_divider {
            // Substitution part: (l, m) pairs. A dangling half-pair is a
            // malformed witness; stop rather than invent a mapping — the
            // checker then rejects the step, which is the fail-closed outcome.
            let Some(&mapped) = witness.get(after) else {
                break;
            };
            set(&mut map, lit, SubImage::Lit(mapped));
            let Some(after_pair) = after.checked_add(1) else {
                break;
            };
            index = after_pair;
        } else if lit == pivot {
            seen_divider = true;
            index = after;
        } else {
            set(&mut map, lit, SubImage::True);
            index = after;
        }
    }

    map
}

/// Write a substitution as VeriPB's `x<v> -> <image>` list.
fn push_substitution(buf: &mut Vec<u8>, map: &[(u32, SubImage)]) {
    for (position, (var, image)) in map.iter().enumerate() {
        if position > 0 {
            buf.push(b' ');
        }
        buf.push(b'x');
        push_u32_decimal(buf, var.saturating_add(1));
        buf.extend_from_slice(b" -> ");
        match image {
            SubImage::True => buf.push(b'1'),
            SubImage::False => buf.push(b'0'),
            SubImage::Lit(lit) => push_literal_name(buf, *lit),
        }
    }
}

/// Add the identity of `anchor` (see `anchor.rs`) to a witness.
fn push_anchor_identity(map: &mut Vec<(u32, SubImage)>, anchor: Option<u32>) {
    if let Some(var) = anchor {
        map.push((
            var,
            SubImage::Lit(Literal::positive(crate::literal::Variable(var))),
        ));
    }
}

/// VeriPB proof writer.
///
/// Error handling matches [`super::DratWriter`]: on the first write failure
/// `io_failed` latches and every later write is a no-op, so a truncated proof
/// is detected once at finalization instead of raising per-step errors through
/// the solver.
pub struct VeripbWriter<W: Write> {
    writer: W,
    line: Vec<u8>,
    added_count: u64,
    deleted_count: u64,
    /// Unit deletions dropped by [`Self::delete`] (see its docs). Kept so the
    /// suppression is observable instead of silent.
    unit_deletions_skipped: u64,
    io_failed: bool,
    header_written: bool,
    /// Set once the trailer is written; later writes are dropped.
    concluded: bool,
    /// Derived constraints written so far (`red`/`rup` lines): VeriPB gives
    /// the k-th one the id m + k, where m is the number of clause lines it
    /// read from the formula (the header count is ignored: measured on
    /// VeriPB 3.0.2 with a header claiming one clause too many, 2026-09-19).
    derived_seq: u64,
    /// m, once known (`set_original_constraints`; the streaming reader learns
    /// it only after the last clause). Until then every deletion is `del spec`.
    original_constraints: Option<u64>,
    /// Order-independent 64-bit key of each live derived clause to the
    /// sequence number of its live copy. A hit turns `del spec <C>` (the
    /// whole clause again, 1.3 KB on a 55-140792 learned clause) into
    /// `del id <n>`; a miss falls back to `del spec`. VeriPB rejects a second
    /// deletion of an id, and `del spec` retires no id but ends all of them
    /// with the last copy (see `originals`), so every live copy must be
    /// deleted by id or none: a key collision between two live clauses swaps
    /// their ids (each deleted once, both derived: sound), and an entry is
    /// never overwritten. A million live learned clauses cost about 20 MB here.
    derived_ids: KeyMap<u64>,
    /// Further live copies of a key already in `derived_ids` (the same clause
    /// derived twice, or a collision): rare, so they get their own map.
    derived_ids_more: KeyMap<Vec<u64>>,
    /// Deletions written as `del id`.
    id_deletions: u64,
    /// Annotated RUP (`--sat-veripb-hints`): the formula's clauses by content
    /// key, each to the VeriPB id of its first clause line (clause line k is
    /// constraint k) and its number of clause lines, filled by
    /// [`Self::note_original`]. VeriPB 3.0.2 keeps identical constraints as
    /// one entry with a copy count: `del spec` lowers the count without
    /// retiring an id, and every id dies with the last copy (measured
    /// 2026-09-29: after one `del spec` of a clause stated twice both ids
    /// still hint, after two neither does). So each `del spec` of the content
    /// takes one line off here, and the key goes with the last: a clause the
    /// CNF states twice stays hinted after the solver drops its duplicate (on
    /// schooltt-5-3-8-2-4-5-10-0.1-0.2-seed1 those were every hint fallback
    /// left). Derived copies only raise VeriPB's count, so this one never
    /// exceeds it. Empty unless hints are on, so the default route pays
    /// nothing. A hash probe per hinted formula clause; the sorted list it
    /// replaces cost a binary search over every formula clause per antecedent.
    originals: KeyMap<(u32, u32)>,
    /// The official checker's anchors (`anchor.rs`): witnesses that would make
    /// CakePB track formula variables forever name a dropped one instead.
    anchor: anchor::CakepbAnchor,
    /// Fresh variables' CakePB lists and their collection steps (`collect.rs`).
    fresh: collect::FreshIndex,
}

/// Hasher for keys that are already [`clause_key`] values: a sum of splitmix64
/// outputs is well mixed, so the key is its own hash. The default SipHash
/// cost a quarter of the annotated-RUP overhead (every hint lookup and every
/// `del id` deletion hashes one key).
#[derive(Default, Clone, Copy)]
struct PremixedKeyHasher(u64);

impl Hasher for PremixedKeyHasher {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.0 = self.0.rotate_left(8) ^ u64::from(b);
        }
    }
    fn write_u64(&mut self, n: u64) {
        self.0 = n;
    }
}

type KeyMap<V> = HashMap<u64, V, BuildHasherDefault<PremixedKeyHasher>>;

/// Order-independent key of a clause: a wrapping sum of a splitmix64 mix of
/// each literal, so the learned clause and its later deletion agree whatever
/// the reduction did to the literal order. A collision between two live derived
/// clauses makes one deletion name the other's id; deleting a derived
/// constraint is sound for a refutation (the database only shrinks), so the
/// cost is at worst a rejected proof, at 2^-64 per pair.
fn clause_key(clause: &[Literal]) -> u64 {
    clause
        .iter()
        .fold(0u64, |acc, &lit| acc.wrapping_add(literal_key(lit)))
}

/// One literal's term of [`clause_key`], so a caller reading a clause anyway
/// can sum the key as it goes ([`VeripbWriter::constraint_id_by_key`]).
#[inline]
pub(crate) fn literal_key(lit: Literal) -> u64 {
    let mut z = u64::from(lit.index() as u32).wrapping_add(0x9E37_79B9_7F4A_7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

impl<W: Write> VeripbWriter<W> {
    /// Create a VeriPB proof writer. VeriPB has no binary encoding, so this is
    /// the only constructor.
    pub fn new(writer: W) -> Self {
        Self {
            writer,
            line: Vec::with_capacity(VERIPB_LINE_INITIAL_CAPACITY),
            added_count: 0,
            deleted_count: 0,
            unit_deletions_skipped: 0,
            io_failed: false,
            header_written: false,
            concluded: false,
            derived_seq: 0,
            original_constraints: None,
            derived_ids: KeyMap::default(),
            derived_ids_more: KeyMap::default(),
            id_deletions: 0,
            originals: KeyMap::default(),
            anchor: anchor::CakepbAnchor::default(),
            fresh: collect::FreshIndex::default(),
        }
    }

    /// Record formula clause `id` (its 1-based clause line, VeriPB's
    /// numbering: tautologies and duplicates count, measured on 3.0.2) so a
    /// later [`Self::constraint_id`] can name it in a hint.
    pub fn note_original(&mut self, clause: &[Literal], id: u64) {
        self.anchor.note_clause(clause);
        if let Ok(id) = u32::try_from(id) {
            self.originals
                .entry(clause_key(clause))
                .or_insert((id, 0))
                .1 += 1;
        }
    }

    /// The VeriPB id of a live constraint whose content is `clause`, if this
    /// writer knows one: a derived constraint still live, else a formula
    /// clause not deleted. `None` whenever the id is not certain, so a caller
    /// falls back to an unannotated step.
    pub fn constraint_id(&mut self, clause: &[Literal]) -> Option<u64> {
        self.constraint_id_by_key(clause_key(clause))
    }

    /// [`Self::constraint_id`] of the clause whose [`clause_key`] is `key`.
    pub fn constraint_id_by_key(&self, key: u64) -> Option<u64> {
        if let Some(base) = self.original_constraints {
            if let Some(&seq) = self.derived_ids.get(&key) {
                return base.checked_add(seq);
            }
        }
        self.originals.get(&key).map(|&(id, _)| u64::from(id))
    }

    /// Log a clause implied by unit propagation as `rup <C> : <ids> ;`
    /// (annotated RUP: VeriPB 3 propagates on the listed constraints only and
    /// rejects the step if they do not reach a conflict; the SAT-COMP 2026
    /// elaboration then has nothing to search for). An empty `hints` writes
    /// plain `rup <C> ;`. Only for steps known to be RUP, never RAT.
    pub fn add_rup(&mut self, clause: &[Literal], hints: &[u64]) -> io::Result<()> {
        if !self.accepting() {
            return Ok(());
        }
        let result = self.write_line(|line| {
            line.extend_from_slice(b"rup ");
            if clause.is_empty() {
                line.extend_from_slice(b">= 1");
            } else {
                push_clause_constraint(line, clause);
            }
            if !hints.is_empty() {
                line.extend_from_slice(b" :");
                for &id in hints {
                    line.push(b' ');
                    push_u64_decimal(line, id);
                }
            }
            line.extend_from_slice(b" ;");
        });
        self.latch(result)?;
        if clause.is_empty() {
            let result = self.writer.write_all(VERIPB_TRAILER);
            self.latch(result)?;
            self.concluded = true;
        }
        self.added_count = self.added_count.saturating_add(1);
        self.record_derived(clause);
        self.note_fresh(clause)
    }

    /// A writer that knows the formula has `original_constraints` clause lines
    /// (as VeriPB numbers them, 1 to m in file order), so it can delete its
    /// own derived constraints by id instead of by specification.
    pub fn with_original_constraints(writer: W, original_constraints: u64) -> Self {
        let mut this = Self::new(writer);
        this.original_constraints = Some(original_constraints);
        this
    }

    /// Tell the writer the formula's clause-line count once it is known (the
    /// streaming reader counts while it loads). Derived constraints written
    /// before this call are numbered from it retroactively, since VeriPB reads
    /// the whole formula before the proof.
    pub fn set_original_constraints(&mut self, original_constraints: u64) {
        self.original_constraints = Some(original_constraints);
    }

    /// Remember the sequence number of the derived line just written.
    ///
    /// The sequence number is an id VeriPB will use, so it never wraps: if it
    /// could not advance (2^64 derived lines, unreachable in practice) the
    /// line is left unrecorded, and deleting it falls back to `del spec`,
    /// which names the clause itself. Every id already recorded stays right.
    fn record_derived(&mut self, clause: &[Literal]) {
        let Some(seq) = self.derived_seq.checked_add(1) else {
            return;
        };
        self.derived_seq = seq;
        if clause.is_empty() {
            return;
        }
        let key = clause_key(clause);
        if let Some(previous) = self.derived_ids.insert(key, self.derived_seq) {
            self.derived_ids_more.entry(key).or_default().push(previous);
        }
    }

    /// True while the writer still accepts steps.
    fn accepting(&self) -> bool {
        !self.io_failed && !self.concluded
    }

    fn ensure_header(&mut self) -> io::Result<()> {
        if self.header_written {
            return Ok(());
        }
        self.header_written = true;
        self.writer.write_all(VERIPB_HEADER)
    }

    /// Build one rule line into the reusable buffer and write it.
    fn write_line(&mut self, build: impl FnOnce(&mut Vec<u8>)) -> io::Result<()> {
        self.ensure_header()?;
        if self.line.capacity() > VERIPB_LINE_MAX_RETAINED_CAPACITY {
            self.line = Vec::with_capacity(VERIPB_LINE_INITIAL_CAPACITY);
        } else {
            self.line.clear();
        }
        build(&mut self.line);
        self.line.push(b'\n');
        // `self.line` is borrowed immutably here while `self.writer` is
        // borrowed mutably; split the borrow explicitly.
        let Self { writer, line, .. } = self;
        writer.write_all(line)
    }

    fn latch(&mut self, result: io::Result<()>) -> io::Result<()> {
        if let Err(error) = result {
            self.io_failed = true;
            return Err(error);
        }
        Ok(())
    }

    /// Log a derived clause.
    ///
    /// Non-empty clauses become `red <C> : <C[0] ↦ true> ;` (the RAT condition
    /// on the DRAT pivot, which subsumes RUP). The empty clause becomes
    /// `rup >= 1 ;` followed by the output/conclusion trailer.
    pub fn add(&mut self, clause: &[Literal]) -> io::Result<()> {
        if !self.accepting() {
            return Ok(());
        }
        let Some(&pivot) = clause.first() else {
            let result = self
                .write_line(|line| line.extend_from_slice(b"rup >= 1 ;"))
                .and_then(|()| self.writer.write_all(VERIPB_TRAILER));
            self.latch(result)?;
            self.concluded = true;
            self.added_count = self.added_count.saturating_add(1);
            self.record_derived(clause);
            return Ok(());
        };
        let mut map = witness_map(&[pivot]);
        let anchor = self.anchor_for(&map)?;
        push_anchor_identity(&mut map, anchor);
        let result = self.write_line(|line| {
            line.extend_from_slice(b"red ");
            push_clause_constraint(line, clause);
            line.extend_from_slice(b" : ");
            push_substitution(line, &map);
            line.extend_from_slice(b" ;");
        });
        self.latch(result)?;
        self.added_count = self.added_count.saturating_add(1);
        self.record_derived(clause);
        self.note_fresh(clause)
    }

    /// Log a propagation-redundancy (DPR) step.
    ///
    /// The witness layout is the assignment-only prefix of the SR stream, so it
    /// shares [`Self::add_sr`]'s serializer.
    pub fn add_pr(&mut self, clause: &[Literal], witness: &[Literal]) -> io::Result<()> {
        self.add_sr(clause, witness)
    }

    /// Log a substitution-redundancy (SR) step — the symmetry routes' output.
    ///
    /// `witness` is the same token stream `DratWriter::add_sr` serializes, so
    /// the two surfaces stay byte-for-byte equivalent in *content*; only the
    /// encoding differs.
    pub fn add_sr(&mut self, clause: &[Literal], witness: &[Literal]) -> io::Result<()> {
        debug_assert!(
            !clause.is_empty() && witness.first() == clause.first(),
            "BUG: SR/DSR witness must begin by repeating the clause pivot clause[0]"
        );
        if !self.accepting() {
            return Ok(());
        }
        let mut map = witness_map(witness);
        let anchor = self.anchor_for(&map)?;
        push_anchor_identity(&mut map, anchor);
        let result = self.write_line(|line| {
            line.extend_from_slice(b"red ");
            push_clause_constraint(line, clause);
            if !map.is_empty() {
                line.extend_from_slice(b" : ");
                push_substitution(line, &map);
            }
            line.extend_from_slice(b" ;");
        });
        self.latch(result)?;
        self.added_count = self.added_count.saturating_add(1);
        self.record_derived(clause);
        self.note_fresh(clause)
    }

    /// Log a clause deletion: `del id <n> ;` for a constraint this writer
    /// derived (its id is known, see `with_original_constraints`), otherwise
    /// `del spec <C> ;`.
    ///
    /// Why id: on 55-140792 (33K variables, learned clauses of 100 to 200
    /// literals) the proof grew at 30 MB/s, `del spec` lines half of it, and
    /// the harness's 8 GB cap stopped the run at 224 s; VeriPB 3.0.2 takes
    /// `del id <n> ;` (measured 2026-09-19: a proof with every derived id
    /// deleted before its final `rup` is rejected, so the ids are the ones the
    /// checker uses).
    ///
    /// Deletions are not optional here. AY's `adv_gc` route collapses shuffled
    /// at-most-one ladders into their pairwise closure (RUP additions *plus*
    /// deletions) before the orbitope detector runs, and the subsequent SR
    /// witnesses are redundant only against the collapsed formula: dropping the
    /// `d` lines makes `adv_gc_n100_k10` fail with an unprovable proofgoal on a
    /// ladder clause that should no longer be in the database (measured).
    ///
    /// Deleting a formula (core) constraint makes VeriPB run a checked-deletion
    /// check; when that fails it prints one warning and downgrades to unchecked
    /// deletion for the rest of the proof. That is harmless for a refutation —
    /// deletion only weakens the database, so a contradiction derived after it
    /// is still a contradiction from a subset of the input — and this writer
    /// claims `output NONE`, i.e. no reformulation guarantee that the downgrade
    /// could invalidate.
    ///
    /// # Unit deletions are dropped
    ///
    /// A *unit* deletion is never written. On the DRAT surface it is already a
    /// no-op: `drat-trim` (drat-trim.c:806-814) and `ay_drat_check`
    /// (`Checker::delete_clause`, `pseudo_unit_skips`) both silently ignore the
    /// deletion of a clause that is the current propagation reason for its
    /// first literal, and a unit clause is unconditionally the reason for its
    /// own literal once it is propagated. VeriPB has no such rule: it removes
    /// the constraint for real, and a root-level fact whose only remaining
    /// derivation *was* that unit stops being derivable for the rest of the
    /// proof.
    ///
    /// That is not hypothetical. On `dc7817dfa2817916b266c1cfacd2ee66` the
    /// stated unit `x12023` was written three times (proof lines 499425/499510/
    /// 499513), deleted three times (518223/518225/915150), and then restated by
    /// `Solver::proof_emit_level0_unit_for_lost_reason` at line 1044184 — at
    /// which point every clause that could propagate it had also been deleted,
    /// so VeriPB rejected with `Proofgoal 343446 could not be autoproven`.
    /// Suppressing the unit deletions makes the restatement trivially RUP
    /// against the still-live unit and the proof verifies.
    ///
    /// Dropping a deletion is always sound for a refutation: it leaves the
    /// checker's database a *superset* of AY's, every member of which was
    /// admitted by a satisfiability-preserving step, so the contradiction
    /// eventually derived still refutes the input. The cost is bounded and
    /// tiny — the same instance emits 5 157 147 deletions of which exactly 9
    /// are units.
    pub fn delete(&mut self, clause: &[Literal]) -> io::Result<()> {
        if !self.accepting() {
            return Ok(());
        }
        if clause.len() == 1 {
            self.unit_deletions_skipped = self.unit_deletions_skipped.saturating_add(1);
            return Ok(());
        }
        let known_id = match self.original_constraints {
            Some(base) => {
                let key = clause_key(clause);
                let seq = self.derived_ids.remove(&key);
                if seq.is_some() {
                    if let Some(older) = self.derived_ids_more.get_mut(&key) {
                        if let Some(previous) = older.pop() {
                            self.derived_ids.insert(key, previous);
                        }
                        if older.is_empty() {
                            self.derived_ids_more.remove(&key);
                        }
                    }
                }
                seq.map(|seq| base.saturating_add(seq))
            }
            None => None,
        };
        if known_id.is_none() && !self.originals.is_empty() {
            // `del spec` may remove a formula clause: one copy fewer.
            let key = clause_key(clause);
            if let Some((_, copies)) = self.originals.get_mut(&key) {
                *copies -= 1;
                if *copies == 0 {
                    self.originals.remove(&key);
                }
            }
        }
        let result = match known_id {
            Some(id) => self.write_line(|line| {
                line.extend_from_slice(b"del id ");
                push_u64_decimal(line, id);
                line.extend_from_slice(b" ;");
            }),
            None => self.write_line(|line| {
                line.extend_from_slice(b"del spec ");
                push_clause_constraint(line, clause);
                line.extend_from_slice(b" ;");
            }),
        };
        self.latch(result)?;
        self.deleted_count = self.deleted_count.saturating_add(1);
        if known_id.is_some() {
            self.id_deletions = self.id_deletions.saturating_add(1);
        }
        Ok(())
    }

    /// `red` steps written with an anchor's identity (see `anchor.rs`).
    pub fn anchored_reds(&self) -> u64 {
        self.anchor.anchored
    }

    /// Collection steps written for fresh variables (see `collect.rs`).
    pub fn fresh_collections(&self) -> u64 {
        self.fresh.collections
    }

    /// Deletions written by id rather than by specification.
    pub fn id_deletions(&self) -> u64 {
        self.id_deletions
    }

    /// Clauses successfully added.
    pub fn added_count(&self) -> u64 {
        self.added_count
    }

    /// Clauses successfully deleted.
    pub fn deleted_count(&self) -> u64 {
        self.deleted_count
    }

    /// Unit deletions dropped rather than written (see [`Self::delete`]).
    #[cfg_attr(not(test), allow(dead_code))]
    pub fn unit_deletions_skipped(&self) -> u64 {
        self.unit_deletions_skipped
    }

    /// True if any write failed.
    pub fn has_io_error(&self) -> bool {
        self.io_failed
    }

    /// True once the output/conclusion trailer has been written.
    pub fn is_concluded(&self) -> bool {
        self.concluded
    }

    /// Flush the underlying writer (no-op after an I/O failure).
    pub fn flush(&mut self) -> io::Result<()> {
        if self.io_failed {
            return Ok(());
        }
        let result = self.writer.flush();
        if let Err(error) = result {
            self.io_failed = true;
            return Err(error);
        }
        Ok(())
    }
    /// The underlying sink, for reading what it recorded (for example the
    /// first write failure a `BoxedWriter` kept).
    pub(crate) fn get_ref(&self) -> &W {
        &self.writer
    }

    /// Recover the inner writer.
    ///
    /// # Errors
    ///
    /// Returns an error if any write failed, which means the proof stream is
    /// truncated.
    pub fn into_inner(self) -> io::Result<W> {
        if self.io_failed {
            return Err(io::Error::other(
                "VeriPB proof writer encountered I/O error during solve",
            ));
        }
        Ok(self.writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::Variable;

    fn pos(v: u32) -> Literal {
        Literal::positive(Variable(v))
    }

    fn neg(v: u32) -> Literal {
        Literal::negative(Variable(v))
    }

    fn render(steps: impl FnOnce(&mut VeripbWriter<Vec<u8>>)) -> String {
        let mut writer = VeripbWriter::new(Vec::new());
        steps(&mut writer);
        String::from_utf8(writer.into_inner().expect("no io error")).expect("utf8")
    }

    #[test]
    fn test_originals_are_numbered_as_veripb_numbers_clause_lines() {
        // Clause lines 1..4 of a formula whose first line is a tautology and
        // whose third repeats the second: VeriPB numbers all of them (measured
        // on 3.0.2), and a duplicate resolves to its first line.
        let mut w = VeripbWriter::with_original_constraints(Vec::new(), 4);
        w.note_original(&[pos(0), neg(0)], 1);
        w.note_original(&[pos(0), pos(1)], 2);
        w.note_original(&[pos(1), pos(0)], 3);
        w.note_original(&[neg(0), pos(1)], 4);
        assert_eq!(w.constraint_id(&[pos(1), pos(0)]), Some(2));
        assert_eq!(w.constraint_id(&[pos(1), neg(0)]), Some(4));
        assert_eq!(w.constraint_id(&[neg(1)]), None);
    }

    #[test]
    fn test_a_deleted_original_is_never_hinted() {
        let mut w = VeripbWriter::with_original_constraints(Vec::new(), 2);
        w.note_original(&[pos(0), pos(1)], 1);
        w.note_original(&[neg(0), pos(1)], 2);
        w.delete(&[pos(1), pos(0)]).expect("write");
        assert_eq!(w.constraint_id(&[pos(0), pos(1)]), None);
        assert_eq!(w.constraint_id(&[neg(0), pos(1)]), Some(2));
    }

    #[test]
    fn test_a_duplicated_original_is_hinted_until_its_last_copy_is_deleted() {
        let mut w = VeripbWriter::with_original_constraints(Vec::new(), 3);
        w.note_original(&[pos(0), pos(1)], 1);
        w.note_original(&[pos(1), pos(0)], 2);
        w.note_original(&[neg(0), pos(1)], 3);
        w.delete(&[pos(0), pos(1)]).expect("write");
        assert_eq!(w.constraint_id(&[pos(0), pos(1)]), Some(1));
        w.delete(&[pos(0), pos(1)]).expect("write");
        assert_eq!(w.constraint_id(&[pos(0), pos(1)]), None);
        assert_eq!(w.constraint_id(&[neg(0), pos(1)]), Some(3));
    }

    #[test]
    fn test_derived_constraints_resolve_to_m_plus_their_sequence() {
        let mut w = VeripbWriter::with_original_constraints(Vec::new(), 10);
        w.add(&[pos(0), pos(1)]).expect("write");
        w.add_rup(&[pos(2)], &[]).expect("write");
        assert_eq!(w.constraint_id(&[pos(1), pos(0)]), Some(11));
        assert_eq!(w.constraint_id(&[pos(2)]), Some(12));
        w.delete(&[pos(0), pos(1)]).expect("write");
        assert_eq!(w.constraint_id(&[pos(0), pos(1)]), None);
    }

    #[test]
    fn test_ids_follow_every_copy_and_deletion() {
        let mut w = VeripbWriter::with_original_constraints(Vec::new(), 2);
        w.note_original(&[pos(0), pos(1)], 1);
        w.note_original(&[neg(0), pos(1)], 2);
        assert_eq!(w.constraint_id(&[pos(0), pos(1)]), Some(1));
        w.add(&[pos(1), pos(0)]).expect("write");
        assert_eq!(w.constraint_id(&[pos(0), pos(1)]), Some(3));
        w.add(&[pos(0), pos(1)]).expect("write");
        assert_eq!(w.constraint_id(&[pos(0), pos(1)]), Some(4));
        w.delete(&[pos(0), pos(1)]).expect("write");
        assert_eq!(w.constraint_id(&[pos(0), pos(1)]), Some(3));
        w.delete(&[pos(0), pos(1)]).expect("write");
        assert_eq!(w.constraint_id(&[pos(0), pos(1)]), Some(1));
        w.delete(&[pos(0), pos(1)]).expect("write");
        assert_eq!(w.constraint_id(&[pos(0), pos(1)]), None);
        assert_eq!(w.constraint_id(&[neg(0), pos(1)]), Some(2));
        let key = clause_key(&[neg(0), pos(1)]);
        assert_eq!(w.constraint_id_by_key(key), Some(2));
    }

    #[test]
    fn test_ids_known_before_the_formula_count_are_renumbered_after_it() {
        let mut w = VeripbWriter::new(Vec::new());
        w.note_original(&[pos(0), pos(1)], 1);
        w.add(&[pos(0), pos(1)]).expect("write");
        assert_eq!(w.constraint_id(&[pos(0), pos(1)]), Some(1));
        w.set_original_constraints(5);
        assert_eq!(w.constraint_id(&[pos(0), pos(1)]), Some(6));
    }

    #[test]
    fn test_annotated_rup_lists_its_hints() {
        let out = render(|w| {
            w.add_rup(&[pos(0), neg(1)], &[3, 7]).expect("write");
            w.add_rup(&[pos(2)], &[]).expect("write");
            w.add_rup(&[], &[4, 5]).expect("write");
        });
        assert_eq!(
            out,
            "pseudo-Boolean proof version 3.0\n\
             rup 1 x1 1 ~x2 >= 1 : 3 7 ;\n\
             rup 1 x3 >= 1 ;\n\
             rup >= 1 : 4 5 ;\n\
             output NONE;\nconclusion UNSAT;\nend pseudo-Boolean proof;\n"
        );
    }

    #[test]
    fn test_plain_addition_is_red_with_the_drat_pivot() {
        // Variable(0) is DIMACS 1: a DRAT `a`-line is RAT on its first literal,
        // which is `red C : x1 -> 1`.
        let out = render(|w| {
            w.add(&[pos(0), neg(1)]).expect("write");
        });
        assert_eq!(
            out,
            "pseudo-Boolean proof version 3.0\nred 1 x1 1 ~x2 >= 1 : x1 -> 1 ;\n"
        );
    }

    #[test]
    fn test_negative_pivot_maps_the_variable_to_false() {
        let out = render(|w| {
            w.add(&[neg(4)]).expect("write");
        });
        assert!(out.ends_with("red 1 ~x5 >= 1 : x5 -> 0 ;\n"), "{out}");
    }

    #[test]
    fn test_empty_clause_writes_rup_contradiction_and_the_trailer() {
        let out = render(|w| {
            w.add(&[]).expect("write");
        });
        assert_eq!(
            out,
            "pseudo-Boolean proof version 3.0\nrup >= 1 ;\noutput NONE;\nconclusion UNSAT;\n\
             end pseudo-Boolean proof;\n"
        );
    }

    #[test]
    fn test_steps_after_the_conclusion_are_dropped() {
        let out = render(|w| {
            w.add(&[]).expect("write");
            w.add(&[pos(0)]).expect("write");
            w.delete(&[pos(1)]).expect("write");
        });
        assert_eq!(out.matches("end pseudo-Boolean proof;").count(), 1);
        assert!(!out.contains("x1"), "{out}");
    }

    #[test]
    fn test_php_sr_witness_translates_to_a_veripb_substitution() {
        // The aux-free PHP shape from `build_php_aux_free_sr`: clause (¬x5),
        // witness [¬x5, x3, ¬x5(sep), (x4 x6) (x6 x4)] — pivot to false, the PR
        // atom to true, then the pigeon-swap transposition.
        let clause = [neg(4)];
        let witness = [neg(4), pos(2), neg(4), pos(3), pos(5), pos(5), pos(3)];
        let out = render(|w| {
            w.add_sr(&clause, &witness).expect("write");
        });
        assert!(
            out.ends_with("red 1 ~x5 >= 1 : x5 -> 0 x3 -> 1 x4 -> x6 x6 -> x4 ;\n"),
            "{out}"
        );
    }

    #[test]
    fn test_substitution_image_of_variable_one_is_not_the_constant_one() {
        // Regression: the image literal `x1` and the constant `1` are distinct
        // in VeriPB, and conflating them silently rewrites the witness (it made
        // php_sudoku's staircase unprovable at goal 29 during bring-up).
        let clause = [neg(3)];
        let witness = [neg(3), pos(0), neg(3), pos(1), pos(0)];
        let out = render(|w| {
            w.add_sr(&clause, &witness).expect("write");
        });
        assert!(out.ends_with("x2 -> x1 ;\n"), "{out}");
    }

    #[test]
    fn test_negative_source_literal_negates_the_image() {
        // σ(¬x2) = x3 is stored as the positive literal's image: x2 -> ~x3.
        let clause = [pos(0)];
        let witness = [pos(0), pos(0), neg(1), pos(2)];
        let out = render(|w| {
            w.add_sr(&clause, &witness).expect("write");
        });
        assert!(
            out.ends_with("red 1 x1 >= 1 : x1 -> 1 x2 -> ~x3 ;\n"),
            "{out}"
        );
    }

    #[test]
    fn test_decimal_writer_appends_exact_digits_at_every_width(
    ) -> Result<(), Box<dyn std::error::Error>> {
        // The prefix pins that only the appended run is reversed.
        let cases: [(u64, &str); 7] = [
            (0, "0"),
            (7, "7"),
            (10, "10"),
            (1_000_000, "1000000"),
            (1_234_567_890, "1234567890"),
            (u64::from(u32::MAX), "4294967295"),
            (u64::MAX, "18446744073709551615"),
        ];
        for (value, expected) in cases {
            let mut buf = b"x ".to_vec();
            push_u64_decimal(&mut buf, value);
            let want = format!("x {expected}");
            if buf != want.as_bytes() {
                return Err(
                    format!("{value}: {:?} != {want:?}", String::from_utf8_lossy(&buf)).into(),
                );
            }
        }
        let mut buf = Vec::new();
        push_u32_decimal(&mut buf, u32::MAX);
        if buf != b"4294967295" {
            return Err(format!("u32::MAX: {:?}", String::from_utf8_lossy(&buf)).into());
        }
        Ok(())
    }

    #[test]
    fn test_deletion_is_emitted_as_del_spec() {
        let out = render(|w| {
            w.delete(&[pos(0), neg(2)]).expect("write");
        });
        assert!(out.ends_with("del spec 1 x1 1 ~x3 >= 1 ;\n"), "{out}");
    }

    /// With the formula's clause count known, a derived clause is deleted by
    /// the id VeriPB gave it (m + 1 for the first derivation), in any literal
    /// order, newest copy first when it was derived twice; a clause the
    /// writer did not derive, a deletion beyond the live copies, and a writer
    /// without the count keep `del spec`.
    #[test]
    fn test_derived_clauses_are_deleted_by_id_when_the_clause_count_is_known() {
        let mut writer = VeripbWriter::with_original_constraints(Vec::new(), 45);
        writer.add(&[pos(0), neg(2), pos(4)]).expect("write");
        writer.add_sr(&[neg(1), pos(3)], &[neg(1)]).expect("write");
        writer.add(&[neg(1), pos(3)]).expect("write");
        writer.delete(&[pos(4), pos(0), neg(2)]).expect("write");
        writer.delete(&[neg(1), pos(3)]).expect("write");
        writer.delete(&[neg(1), pos(3)]).expect("write");
        writer.delete(&[neg(1), pos(3)]).expect("write");
        writer.delete(&[pos(5), pos(6)]).expect("write");
        assert_eq!(writer.id_deletions(), 3);
        assert_eq!(writer.deleted_count(), 5);
        let out = String::from_utf8(writer.into_inner().expect("no io error")).expect("utf8");
        assert_eq!(
            out,
            "pseudo-Boolean proof version 3.0\n\
             red 1 x1 1 ~x3 1 x5 >= 1 : x1 -> 1 ;\n\
             red 1 ~x2 1 x4 >= 1 : x2 -> 0 ;\n\
             red 1 ~x2 1 x4 >= 1 : x2 -> 0 ;\n\
             del id 46 ;\n\
             del id 48 ;\n\
             del id 47 ;\n\
             del spec 1 ~x2 1 x4 >= 1 ;\n\
             del spec 1 x6 1 x7 >= 1 ;\n"
        );
        let mut plain = VeripbWriter::new(Vec::new());
        plain.add(&[pos(0), neg(2)]).expect("write");
        plain.delete(&[pos(0), neg(2)]).expect("write");
        assert_eq!(plain.id_deletions(), 0);
        let out = String::from_utf8(plain.into_inner().expect("no io error")).expect("utf8");
        assert!(out.ends_with("del spec 1 x1 1 ~x3 >= 1 ;\n"), "{out}");
    }

    /// The empty clause takes an id too (it is a `rup` line), so a derivation
    /// after it would be numbered correctly; here the count just moves on.
    #[test]
    fn test_the_empty_clause_consumes_an_id() {
        let mut writer = VeripbWriter::with_original_constraints(Vec::new(), 3);
        writer.add(&[pos(0), pos(1)]).expect("write");
        writer.add(&[]).expect("write");
        assert_eq!(writer.derived_seq, 2);
    }

    /// The streaming reader learns the clause count after the last clause;
    /// derivations written before that are numbered from it retroactively,
    /// and deletions before it stay `del spec`.
    #[test]
    fn test_the_clause_count_can_arrive_after_the_first_derivation() {
        let mut writer = VeripbWriter::new(Vec::new());
        writer.add(&[pos(0), pos(1)]).expect("write");
        writer.add(&[pos(2), pos(3)]).expect("write");
        writer.delete(&[pos(0), pos(1)]).expect("write");
        writer.set_original_constraints(10);
        writer.delete(&[pos(3), pos(2)]).expect("write");
        assert_eq!(writer.id_deletions(), 1);
        let out = String::from_utf8(writer.into_inner().expect("no io error")).expect("utf8");
        assert!(
            out.ends_with("del spec 1 x1 1 x2 >= 1 ;\ndel id 12 ;\n"),
            "{out}"
        );
    }

    #[test]
    fn test_counts_track_additions_and_deletions() {
        let mut writer = VeripbWriter::new(Vec::new());
        writer.add(&[pos(0)]).expect("write");
        writer.add_sr(&[neg(1)], &[neg(1)]).expect("write");
        writer.delete(&[pos(0), neg(2)]).expect("write");
        assert_eq!(writer.added_count(), 2);
        assert_eq!(writer.deleted_count(), 1);
        assert!(!writer.is_concluded());
        writer.add(&[]).expect("write");
        assert!(writer.is_concluded());
    }

    #[test]
    fn test_unit_deletion_is_dropped_so_the_root_fact_stays_derivable() {
        // Regression, dc7817dfa2817916b266c1cfacd2ee66: AY stated the root fact
        // `x12023` as a unit, later deleted it, and later still restated it —
        // by which point nothing could propagate it and VeriPB rejected the
        // restatement (`Proofgoal 343446 could not be autoproven`). drat-trim
        // and ay_drat_check both ignore this deletion; VeriPB does not, so the
        // writer must not emit it.
        let mut writer = VeripbWriter::new(Vec::new());
        writer.add(&[pos(0)]).expect("write");
        writer.delete(&[pos(0)]).expect("write");
        writer.delete(&[neg(0)]).expect("write");
        writer.delete(&[pos(0), neg(2)]).expect("write");
        assert_eq!(writer.deleted_count(), 1);
        assert_eq!(writer.unit_deletions_skipped(), 2);
        let out = String::from_utf8(writer.into_inner().expect("no io error")).expect("utf8");
        assert_eq!(
            out,
            "pseudo-Boolean proof version 3.0\nred 1 x1 >= 1 : x1 -> 1 ;\n\
             del spec 1 x1 1 ~x3 >= 1 ;\n"
        );
    }

    #[test]
    fn test_dangling_substitution_half_pair_is_dropped_rather_than_invented() {
        let clause = [pos(0)];
        let witness = [pos(0), pos(0), pos(1)];
        let out = render(|w| {
            w.add_sr(&clause, &witness).expect("write");
        });
        assert!(out.ends_with("red 1 x1 >= 1 : x1 -> 1 ;\n"), "{out}");
    }
}
