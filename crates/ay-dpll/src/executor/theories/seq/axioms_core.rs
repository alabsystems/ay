// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Core seq axiom collection and len/nth axiom generation.

// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;
use num_bigint::BigInt;
use num_traits::{ToPrimitive, Zero};

use super::super::super::Executor;
use super::scan::SeqTermScan;
use ay_core::term::{Constant, Symbol, TermData, TermId};
use ay_core::Sort;

/// Per-variable plan for the point-read reduction (P0.1 phase-2a).
struct PointReadPlan {
    /// Concrete read index → fresh element variable that replaces
    /// `(seq.nth s k)`.
    reads: ay_core::kani_compat::DetHashMap<usize, TermId>,
    /// Fresh non-negative Int variable that replaces `(seq.len s)`, present only
    /// when the variable has a `seq.len` occurrence.
    plen: Option<TermId>,
}

impl Executor {
    /// Collect all Seq axioms from assertion terms (#5958, #5841, #6005).
    ///
    /// Generates axioms for: len, nth, contains, extract, prefixof, suffixof,
    /// indexof, replace.
    ///
    /// Uses a two-pass approach (#6005): after the first round of axiom
    /// generation, scans the generated axioms for new seq operations that
    /// weren't in the original assertions. If any are found, generates
    /// additional axioms for them. This handles the case where axiom generators
    /// synthesize seq terms (e.g., indexof creates `seq.extract` and
    /// `seq.contains` terms) that themselves need axiomatization.
    ///
    /// Capped at 2 passes to bound axiom growth. In practice, the second pass
    /// rarely finds new operations because generators already inline axioms
    /// for their synthesized terms.
    pub(super) fn collect_seq_len_axioms(&mut self) -> Vec<TermId> {
        // Inject nth-ground equalities into assertions before scanning (#6036).
        // This makes ALL axiom generators benefit from nth reconstruction.
        let nth_equalities = self.generate_nth_ground_equality_axioms();
        if !nth_equalities.is_empty() {
            let mut seen: HashSet<_> = self.ctx.assertions.iter().copied().collect();
            self.ctx.assertions.extend(
                nth_equalities
                    .into_iter()
                    .filter(|axiom| seen.insert(*axiom)),
            );
        }

        let mut scan = self.scan_seq_terms();
        let mut axioms = self.generate_axioms_from_scan(&scan);

        // Second pass: scan generated axioms for new seq operations (#6005).
        // Capped at one extra pass to bound axiom growth. The bridge axiom
        // (contains <=> indexof) creates new terms that get axiomatized here.
        // Snapshot before scanning so we only axiomatize NEW terms — avoids
        // duplicate Skolem variables from re-processing first-pass terms.
        let offsets = scan.snapshot();
        scan.scan_roots(&self.ctx.terms, &axioms);
        let new_op_count = scan.axiom_op_count();
        let prev_op_count = offsets.contains
            + offsets.extract
            + offsets.prefixof
            + offsets.suffixof
            + offsets.indexof
            + offsets.last_indexof
            + offsets.replace;

        if new_op_count > prev_op_count {
            // Generate axioms ONLY for terms discovered in the second scan.
            let new_terms = scan.new_terms_since(&offsets);
            let extra = self.generate_axioms_from_scan(&new_terms);
            axioms.extend(extra);
        }
        // Not `else if` — also handle new nth terms even when new ops were found.
        // The previous `else if` skipped nth depth-iteration when both new ops
        // and new nth terms appeared simultaneously.
        if scan.nth_terms.len() > offsets.nth {
            let new_terms = scan.new_terms_since(&offsets);
            let nth_axioms = self.generate_seq_nth_axioms(&new_terms);
            axioms.extend(nth_axioms);
            for _nth_pass in 0..5 {
                let prev = scan.nth_terms.len();
                scan.scan_roots(&self.ctx.terms, &axioms);
                if scan.nth_terms.len() == prev {
                    break;
                }
                let extra_nth = self.generate_seq_nth_axioms(&scan);
                if extra_nth.is_empty() {
                    break;
                }
                axioms.extend(extra_nth);
            }
        }

        axioms
    }

    /// Generate all seq axioms from a completed scan.
    ///
    /// Ordering: indexof and replace run before contains because they create
    /// fresh `contains(s,t)` terms that need their own axioms (#5998).
    pub(super) fn generate_axioms_from_scan(&mut self, scan: &SeqTermScan) -> Vec<TermId> {
        let mut axioms = self.generate_seq_len_axioms(scan);
        axioms.extend(self.generate_seq_nth_axioms(scan));
        axioms.extend(self.generate_seq_extract_axioms(scan));
        axioms.extend(self.generate_seq_prefixof_axioms(scan));
        axioms.extend(self.generate_seq_suffixof_axioms(scan));

        // Cross-predicate compatibility for pairs of prefixof / pairs of suffixof
        // atoms over the SAME haystack (#seq-pairwise-compat): monotonicity
        // (`pred_long ⟹ pred_short`) plus incompatibility of un-nested ground
        // needles. Closes the symbolic-prefixof×prefixof / suffixof×suffixof
        // wrong-SAT family (including mixed polarity).
        axioms.extend(self.generate_seq_pairwise_compat_axioms(scan));
        // Element pinning: a ground prefixof/suffixof needle over a symbolic
        // haystack pins the haystack's `seq.nth` elements, so a contradictory
        // external `(= (seq.nth s i) v)` pin (with no definite length) is refuted.
        axioms.extend(self.generate_seq_ground_needle_pins(scan));

        let mut new_contains = Vec::new();
        let (indexof_axioms, idx_contains) = self.generate_seq_indexof_axioms(scan);
        axioms.extend(indexof_axioms);
        new_contains.extend(idx_contains);
        let (last_idx_axioms, lidx_contains) = self.generate_seq_last_indexof_axioms(scan);
        axioms.extend(last_idx_axioms);
        new_contains.extend(lidx_contains);
        let (replace_axioms, rpl_contains) = self.generate_seq_replace_axioms(scan);
        axioms.extend(replace_axioms);
        new_contains.extend(rpl_contains);

        axioms.extend(self.generate_seq_contains_axioms(scan));
        if !new_contains.is_empty() {
            axioms.extend(self.generate_seq_contains_axioms_for(&new_contains));
        }

        // Transitivity of subsequence containment (#seq-contains-transitivity):
        // `contains(x,y) ∧ contains(y,z) ⟹ contains(x,z)`. The per-atom skolem
        // decomposition never chains two containments, so a transitivity theorem
        // like `contains(a,b) ∧ contains(b,c) ∧ ¬contains(a,c)` was wrongly SAT.
        axioms.extend(self.generate_seq_contains_transitivity_axioms(scan));

        // A ground prefixof/suffixof needle that covers a contains needle q forces
        // contains(s, q) (#seq-pairwise-compat) — refutes a contradictory
        // `¬contains` even with no definite length.
        axioms.extend(self.generate_seq_endpoint_contains_axioms(scan));

        // contains(s, q) forced from a window of asserted seq.nth pins
        // (#seq-pairwise-compat): a pinned in-range element makes [c] a substring, so
        // a contradictory `¬contains` is refuted even with no definite length.
        axioms.extend(self.generate_seq_contains_from_pins_axioms(scan));

        // Sound three-valued forcing of search predicates over PARTIALLY-determined
        // sequences (#seq-partial-pred): a prefixof/suffixof/contains/indexof whose
        // haystack is a seq var with a definite length and SOME pinned elements
        // (but not fully reconstructed) gets the definite outcome forced from the
        // pinned elements, closing the partial wrong-SAT family.
        axioms.extend(self.generate_seq_partial_predicate_axioms(scan));

        // Bounded joint-placement refutation for multiple positive contains over a
        // definite-length seq (#seq-pairwise-compat): needles that cannot co-occupy
        // s as contiguous blocks make the conjunction UNSAT. Closes the
        // contains-packing wrong-SAT family.
        axioms.extend(self.generate_seq_contains_packing_axioms());
        axioms
    }

    /// Collect only `seq.nth` structural axioms (for non-LIA path, #5841).
    pub(super) fn collect_seq_nth_axioms(&mut self) -> Vec<TermId> {
        let scan = self.scan_seq_terms();
        self.generate_seq_nth_axioms(&scan)
    }

    /// Collect `seq.++` associativity and identity normalization axioms.
    ///
    /// `seq.++` is associative with `seq.empty` as identity. The EUF core treats
    /// `seq.++` as an uninterpreted function, so two associativity-variant concats
    /// like `(seq.++ (seq.++ a b) c)` and `(seq.++ a (seq.++ b c))` are distinct
    /// EUF terms and a negated equality between them is wrongly satisfiable
    /// (#seq-assoc). We restore the algebraic law by flattening every concat term
    /// to its ordered list of non-empty leaves and asserting equality between any
    /// two concat terms that share the same flat form. Identity is folded in by
    /// dropping `seq.empty` leaves while flattening, so `(seq.++ empty s)` and
    /// `(seq.++ s empty)` both flatten to `[s]` and are equated to `s` when `s`
    /// itself is a leaf present in the problem.
    ///
    /// Sound: every emitted equality is a semantic consequence of associativity +
    /// identity, so it can never make a satisfiable problem unsatisfiable. Bounded:
    /// the flattening is over the (finite) scanned concat terms and groups them in
    /// a single pass.
    pub(super) fn collect_seq_concat_normalization_axioms(&mut self) -> Vec<TermId> {
        // #8529: Use deterministic hash maps in all builds.
        use ay_core::kani_compat::DetHashMap as HashMap;

        let scan = self.scan_seq_terms();
        if scan.concat_terms.is_empty() {
            return Vec::new();
        }

        // Group concat terms by their flattened leaf form. Any two terms in the
        // same group are equal by associativity + identity.
        let mut groups: HashMap<Vec<TermId>, Vec<TermId>> = HashMap::default();
        // Also map each flat form to the single leaf it reduces to (if any), so a
        // concat that is identity-equivalent to a bare sub-term gets equated to it.
        for &(concat_term, _) in &scan.concat_terms {
            let flat = self.flatten_seq_concat(concat_term);
            groups.entry(flat).or_default().push(concat_term);
        }

        let mut axioms = Vec::new();
        for (flat, members) in &groups {
            // Equate all concat members sharing the flat form to the first member.
            if members.len() >= 2 {
                let representative = members[0];
                for &other in &members[1..] {
                    if other != representative {
                        axioms.push(self.ctx.terms.mk_eq(representative, other));
                    }
                }
            }
            // Identity collapse: a concat whose flat form is a single leaf equals
            // that leaf directly (e.g. `(seq.++ s seq.empty) = s`).
            if flat.len() == 1 {
                let leaf = flat[0];
                for &member in members {
                    if member != leaf {
                        axioms.push(self.ctx.terms.mk_eq(member, leaf));
                    }
                }
            }
        }
        axioms
    }

    /// If `term` is `(seq.unit e)`, return `Some(e)`; otherwise `None`.
    fn seq_unit_element(&self, term: TermId) -> Option<TermId> {
        match self.ctx.terms.get(term) {
            TermData::App(Symbol::Named(name), args) if name == "seq.unit" && args.len() == 1 => {
                Some(args[0])
            }
            _ => None,
        }
    }

    /// `seq.unit` injectivity/extensionality + `seq.unit`/`seq.empty` length
    /// separation (sound — theory tautologies, never prune a model).
    ///
    /// `(seq.unit e)` is a length-1 sequence whose sole element is `e`, so:
    ///   * two units are EQUAL iff their elements are equal:
    ///     `(= (seq.unit a) (seq.unit b))  <=>  (= a b)`   (injectivity); and
    ///   * a unit is NEVER equal to the empty sequence (length 1 != 0):
    ///     `(not (= (seq.unit a) seq.empty))`               (length separation).
    /// The EUF core treats `seq.unit`/`seq.empty` as uninterpreted functions, so
    /// it knows neither the `<=` injectivity direction nor the length separation —
    /// it cannot derive `(seq.unit false) != (seq.unit true)` from `false != true`,
    /// nor `(seq.unit x) != seq.empty`. Without these, a length-1 vs length-1
    /// CONTENT mismatch and a length-1 vs length-0 mismatch both stay invisible:
    /// e.g. an `(= (seq.at v 0) (ite c (seq.unit true) seq.empty))` distributes
    /// (at elaboration) into the branch atoms `(= [false] [true])` (content) and
    /// `(= [false] empty)` (length), and the plain EUF+Seq path reports SAT
    /// (`seq_falsesat_iteofseq_eq_operand`). The unit-decomposition pass only
    /// fires for MULTI-leaf concats, and the length-congruence pass only for
    /// var=var/var=empty aliases, so neither covers a bare unit literal equality.
    ///
    /// Emit, bounded by a quadratic pair budget:
    ///   * the injectivity biconditional for every unordered pair of distinct
    ///     same-sorted `seq.unit` terms; and
    ///   * the length-separation disequality for every (`seq.unit`, `seq.empty`)
    ///     pair of the same seq sort.
    ///
    /// SOUND: both shapes are tautologies of the sequence theory (a length-1
    /// sequence is determined by its element and is never empty), so they hold in
    /// every model and remove none — they can never flip a genuine SAT to UNSAT;
    /// they only supply the reasoning EUF lacks, recovering content/length
    /// refutations.
    pub(super) fn collect_seq_unit_injectivity_axioms(&mut self) -> Vec<TermId> {
        const MAX_PAIRS: usize = 4096;
        let scan = self.scan_seq_terms();
        // Snapshot (unit_term, element) for each distinct seq.unit term.
        let mut units: Vec<(TermId, TermId)> = Vec::new();
        for &unit_term in &scan.unit_terms {
            if let Some(elem) = self.seq_unit_element(unit_term) {
                units.push((unit_term, elem));
            }
        }
        let empties: Vec<TermId> = scan.empty_terms.clone();
        let mut axioms = Vec::new();
        let mut pairs = 0usize;
        for i in 0..units.len() {
            for j in (i + 1)..units.len() {
                if pairs >= MAX_PAIRS {
                    return axioms;
                }
                let (ui, ei) = units[i];
                let (uj, ej) = units[j];
                // Only same-sorted units can be equal; differing element sorts
                // make `(= ei ej)` ill-typed, so skip such pairs.
                if self.ctx.terms.sort(ui) != self.ctx.terms.sort(uj) {
                    continue;
                }
                pairs += 1;
                let unit_eq = self.ctx.terms.mk_eq(ui, uj);
                let elem_eq = self.ctx.terms.mk_eq(ei, ej);
                axioms.push(self.ctx.terms.mk_eq(unit_eq, elem_eq));
            }
        }
        // Length separation: a unit (length 1) is never the empty sequence.
        for &(ui, _) in &units {
            for &empty in &empties {
                if pairs >= MAX_PAIRS {
                    return axioms;
                }
                // Same seq sort only (an `(= ui empty)` of different element sort
                // is ill-typed and never asserted).
                if self.ctx.terms.sort(ui) != self.ctx.terms.sort(empty) {
                    continue;
                }
                pairs += 1;
                let eq = self.ctx.terms.mk_eq(ui, empty);
                axioms.push(self.ctx.terms.mk_not(eq));
            }
        }
        // Atom-driven length separation: a seq equality atom `(= a b)` where one
        // side is a `seq.unit` (length 1) and the other is PROVABLY EMPTY (length
        // 0) — including a concat of only empty leaves like `(seq.++ empty empty
        // empty)`, which the literal `empty_terms` list above does not cover —
        // can never hold. Emit `(not (= a b))`. Sound (a length-1 sequence is
        // never empty), and only fires when the equality already exists.
        let mut eq_atoms: Vec<TermId> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        let assertions = self.ctx.assertions.clone();
        for &a in &assertions {
            self.collect_seq_equality_atoms(a, &mut eq_atoms, &mut seen);
        }
        for eq_term in eq_atoms {
            let TermData::App(sym, args) = self.ctx.terms.get(eq_term).clone() else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }
            let (l, r) = (args[0], args[1]);
            let unit_empty = (self.seq_unit_element(l).is_some() && self.seq_term_is_empty(r))
                || (self.seq_unit_element(r).is_some() && self.seq_term_is_empty(l));
            if unit_empty {
                axioms.push(self.ctx.terms.mk_not(eq_term));
            }
        }
        axioms
    }

    /// Collect every Seq-sorted equality atom `(= a b)` reachable from `term`.
    fn collect_seq_equality_atoms(
        &self,
        term: TermId,
        out: &mut Vec<TermId>,
        seen: &mut HashSet<TermId>,
    ) {
        if !seen.insert(term) {
            return;
        }
        match self.ctx.terms.get(term).clone() {
            TermData::App(sym, args) => {
                if sym.name() == "=" && args.len() == 2 {
                    if let Sort::Seq(_) = self.ctx.terms.sort(args[0]) {
                        out.push(term);
                    }
                }
                for a in args {
                    self.collect_seq_equality_atoms(a, out, seen);
                }
            }
            TermData::Not(i) => self.collect_seq_equality_atoms(i, out, seen),
            TermData::Ite(c, t, e) => {
                self.collect_seq_equality_atoms(c, out, seen);
                self.collect_seq_equality_atoms(t, out, seen);
                self.collect_seq_equality_atoms(e, out, seen);
            }
            _ => {}
        }
    }

    /// Unit prefix/suffix decomposition for sequence concat equalities (sound
    /// completeness — never prunes a model, only derives implied facts).
    ///
    /// For an equality atom `(= c1 c2)` over sequences, flatten both sides to
    /// their concat-leaf lists. While the leaves at matching positions from the
    /// FRONT are both `seq.unit`, the sequences (when equal) must agree there, so
    /// assert `(=> (= c1 c2) (= e_i e_i'))` for the unit elements; likewise from
    /// the BACK. If BOTH sides are entirely units but of different length they
    /// can never be equal, so assert `(not (= c1 c2))`. This lets the solver
    /// refute e.g. `(seq.++ (seq.unit 2) s) = (seq.++ (seq.unit 1) s)`
    /// (derives `2 = 1`) and — after determined-length expansion turns a length-1
    /// variable into a unit — word equations like `(unit 2)++s = s++(unit 1)`.
    pub(super) fn collect_seq_unit_decomposition_axioms(&mut self) -> Vec<TermId> {
        let assertions = self.ctx.assertions.clone();
        let mut eq_atoms: Vec<TermId> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        for &a in &assertions {
            self.collect_seq_equality_atoms(a, &mut eq_atoms, &mut seen);
        }

        let mut axioms = Vec::new();
        for eq_term in eq_atoms {
            let (lhs, rhs) = match self.ctx.terms.get(eq_term).clone() {
                TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
                    (args[0], args[1])
                }
                _ => continue,
            };
            let flat1 = self.flatten_seq_concat(lhs);
            let flat2 = self.flatten_seq_concat(rhs);
            if flat1.len() < 2 && flat2.len() < 2 {
                continue; // nothing to decompose
            }
            let units1: Vec<Option<TermId>> =
                flat1.iter().map(|&t| self.seq_unit_element(t)).collect();
            let units2: Vec<Option<TermId>> =
                flat2.iter().map(|&t| self.seq_unit_element(t)).collect();
            let not_eq = self.ctx.terms.mk_not(eq_term);

            // Prefix alignment.
            let mut p = 0;
            while p < units1.len() && p < units2.len() {
                let (Some(e1), Some(e2)) = (units1[p], units2[p]) else {
                    break;
                };
                let ee = self.ctx.terms.mk_eq(e1, e2);
                axioms.push(self.ctx.terms.mk_or(vec![not_eq, ee]));
                p += 1;
            }
            // Suffix alignment (positions not already covered by the prefix).
            let mut q = 0;
            while p + q < units1.len() && p + q < units2.len() {
                let i1 = units1.len() - 1 - q;
                let i2 = units2.len() - 1 - q;
                let (Some(e1), Some(e2)) = (units1[i1], units2[i2]) else {
                    break;
                };
                let ee = self.ctx.terms.mk_eq(e1, e2);
                axioms.push(self.ctx.terms.mk_or(vec![not_eq, ee]));
                q += 1;
            }
            // Two all-unit sequences of different length can never be equal.
            let all1 = !units1.is_empty() && units1.iter().all(Option::is_some);
            let all2 = !units2.is_empty() && units2.iter().all(Option::is_some);
            if all1 && all2 && units1.len() != units2.len() {
                axioms.push(not_eq);
            }
        }
        axioms
    }

    /// If `term` is an `(ite c t e)` of Seq sort, return `(c, t, e)`.
    ///
    /// Only matches the dedicated `TermData::Ite` node (how `ite` elaborates).
    /// The branches `t`/`e` are guaranteed same-sorted as the term, which is Seq.
    fn seq_sorted_ite(&self, term: TermId) -> Option<(TermId, TermId, TermId)> {
        if !self.ctx.terms.sort(term).is_seq() {
            return None;
        }
        match self.ctx.terms.get(term) {
            TermData::Ite(c, t, e) => Some((*c, *t, *e)),
            _ => None,
        }
    }

    /// True when some asserted Seq-sorted equality `(= L R)` either has an
    /// `(ite c t e)` operand of Seq sort, OR equates two `seq.unit`/`seq.empty`
    /// literals (a `seq.unit`-vs-`seq.unit` CONTENT comparison, or a
    /// `seq.unit`-vs-`seq.empty` LENGTH comparison). Such cases need the SeqLIA
    /// path: the per-branch content/length facts are only refuted there via the
    /// length axioms + the unit-injectivity / ite-lifting passes.
    ///
    /// The plain EUF+Seq path treats `seq.unit` as an uninterpreted function and
    /// has no length axioms, so it cannot refute `(= (seq.unit false) (seq.unit
    /// true))` (content) or `(= (seq.unit x) seq.empty)` (length) — the wrong-SAT
    /// root of `seq_falsesat_iteofseq_eq_operand`, where an `ite`-over-equality is
    /// distributed at elaboration into branch atoms of exactly these two shapes.
    ///
    /// Triggers ONLY when a CONTENT/LENGTH refutation is actually needed (one side
    /// a `seq.unit`, the other a different `seq.unit` or a `seq.empty`); a plain
    /// `(= s (seq.unit x))` var alias or `(= (seq.unit x) (seq.unit x))` reflexive
    /// is not flagged. Conservative routing — solve_seq_lia is a sound superset.
    pub(super) fn assertions_contain_seq_ite_equality(&self) -> bool {
        let mut eq_atoms: Vec<TermId> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        let assertions = self.ctx.assertions.clone();
        for &a in &assertions {
            self.collect_seq_equality_atoms(a, &mut eq_atoms, &mut seen);
        }
        for eq_term in eq_atoms {
            let TermData::App(sym, args) = self.ctx.terms.get(eq_term).clone() else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }
            let (l, r) = (args[0], args[1]);
            // An `ite`-of-seq operand (if the distribution did not fire upstream).
            if self.seq_sorted_ite(l).is_some() || self.seq_sorted_ite(r).is_some() {
                return true;
            }
            // A `seq.unit` vs different-`seq.unit` (content) or `seq.unit` vs
            // `seq.empty` (length) literal comparison the EUF path cannot refute.
            let lu = self.seq_unit_element(l);
            let ru = self.seq_unit_element(r);
            match (lu, ru) {
                (Some(_), Some(_)) if l != r => return true,
                (Some(_), None) if self.seq_term_is_empty(r) => return true,
                (None, Some(_)) if self.seq_term_is_empty(l) => return true,
                _ => {}
            }
        }
        false
    }

    /// ITE-lifting for Seq-sorted equalities (sound — equivalence-preserving,
    /// never prunes a model, only exposes the per-branch content/length facts).
    ///
    /// When an asserted equality atom `(= L R)` over sequences has an operand that
    /// is `(ite c t e)` of Seq sort, the EUF core treats that `ite` as a single
    /// opaque seq-sorted value and never case-splits the branches, so it unifies
    /// (say) `[false]` with the opaque `ite` and reports a spurious SAT even though
    /// BOTH branches mismatch (`seq_falsesat_iteofseq_eq_operand`). We restore the
    /// branch reasoning by emitting the tautology
    ///   `(= (= L (ite c t e))  (and (=> c (= L t)) (=> (not c) (= L e))))`,
    /// i.e. the SMT-LIB definition of `ite` lifted to the equality root. The
    /// per-branch equalities `(= L t)` / `(= L e)` are then ordinary Seq-sorted
    /// equalities the existing unit-decomposition + length passes decompose, so a
    /// mismatch in either branch is refuted under its guard.
    ///
    /// SOUND: `(= L (ite c t e))` is logically EQUIVALENT to
    /// `(and (=> c (= L t)) (=> (not c) (= L e)))` by the definition of `ite`
    /// (and symmetrically for an `ite` on the left), so asserting the biconditional
    /// between the original atom and the lifted form is a TAUTOLOGY — true in every
    /// model. It therefore removes no models (cannot flip a genuine SAT to UNSAT)
    /// regardless of the polarity of the equality atom in the assertions; it only
    /// forces the solver to enforce the branch constraints it currently skips,
    /// recovering the correct UNSAT. The branch equalities it feeds downstream are
    /// guarded by `c` / `(not c)`, never asserted unconditionally.
    pub(super) fn collect_seq_ite_equality_lifting_axioms(&mut self) -> Vec<TermId> {
        let assertions = self.ctx.assertions.clone();
        let mut eq_atoms: Vec<TermId> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        for &a in &assertions {
            self.collect_seq_equality_atoms(a, &mut eq_atoms, &mut seen);
        }

        let mut axioms = Vec::new();
        for eq_term in eq_atoms {
            let (lhs, rhs) = match self.ctx.terms.get(eq_term).clone() {
                TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
                    (args[0], args[1])
                }
                _ => continue,
            };
            // Lift an `ite` on EITHER side: `(= L (ite c t e))` (and the symmetric
            // `(= (ite c t e) R)`). `other` is the non-ite operand the branches are
            // equated against. If both sides are `ite`, the first match suffices —
            // the branch equalities then themselves carry the other `ite`, which
            // recurses via the equality atoms collected from the emitted axioms in
            // later passes.
            let (other, cond, then_br, else_br) = if let Some((c, t, e)) = self.seq_sorted_ite(rhs)
            {
                (lhs, c, t, e)
            } else if let Some((c, t, e)) = self.seq_sorted_ite(lhs) {
                (rhs, c, t, e)
            } else {
                continue;
            };

            let eq_then = self.ctx.terms.mk_eq(other, then_br);
            let eq_else = self.ctx.terms.mk_eq(other, else_br);
            let imp_then = self.ctx.terms.mk_implies(cond, eq_then);
            let not_cond = self.ctx.terms.mk_not(cond);
            let imp_else = self.ctx.terms.mk_implies(not_cond, eq_else);
            let lifted = self.ctx.terms.mk_and(vec![imp_then, imp_else]);
            // Biconditional with the original atom: a tautology by the definition
            // of `ite`, sound under any polarity of `eq_term`.
            axioms.push(self.ctx.terms.mk_eq(eq_term, lifted));
        }
        axioms
    }

    /// Inline GROUND-resolvable `seq.extract` terms to their literal value
    /// (sound — equisatisfiable, never prunes or adds a model).
    ///
    /// When `(seq.extract s i n)` has a base `s` that resolves (through the
    /// top-level seq equality closure) to a GROUND sequence literal and constant
    /// offset/length `i`/`n` (possibly pinned via the int alias map), the result
    /// is a single concrete sequence value, so SUBSTITUTE the extract term by that
    /// literal throughout the assertions. `(seq.at v 0)` elaborates to
    /// `(seq.extract v 0 1)`, so this also covers it.
    ///
    /// The ground-extract axiom pass already emits `extract = literal`, but EUF's
    /// `seq.extract` node is opaque: when the SAME extract appears as a direct
    /// operand of multiple equalities (e.g. the two BRANCH equalities of an
    /// `(= (seq.at v 0) (ite c [true] empty))` after the `ite` is distributed),
    /// the SeqLIA solver does not always propagate the resulting unit-content
    /// conflict and returns Unknown (false-SAT root cause of
    /// `seq_falsesat_iteofseq_eq_operand`). Replacing the opaque extract with its
    /// literal turns those branch equalities into pure `seq.unit`/`seq.empty`
    /// equalities that the unit-injectivity + length passes refute directly.
    ///
    /// SOUND: the extract term EQUALS its computed literal in every model (the
    /// substitution is the SMT-LIB semantics of `seq.extract` on a fully ground
    /// base with constant bounds), so replacing it everywhere is equisatisfiable
    /// — it can neither add nor remove a model, hence never flips a verdict.
    pub(super) fn inline_ground_seq_extracts(&mut self) {
        for _round in 0..8u32 {
            let scan = self.scan_seq_terms();
            if scan.extract_terms.is_empty() {
                break;
            }
            let ground_map = self.build_ground_seq_map();
            let int_const_aliases = self.build_int_const_alias_map();

            let mut froms: Vec<TermId> = Vec::new();
            let mut tos: Vec<TermId> = Vec::new();
            for &(extract_term, s, i, n) in &scan.extract_terms {
                let i = self.resolve_int_const(i, &int_const_aliases);
                let n = self.resolve_int_const(n, &int_const_aliases);
                let s_ground = ground_map.get(&s).copied().unwrap_or(s);
                let Some(s_elems) = self.try_extract_ground_seq(s_ground) else {
                    continue;
                };
                let (TermData::Const(Constant::Int(i_val)), TermData::Const(Constant::Int(n_val))) =
                    (self.ctx.terms.get(i).clone(), self.ctx.terms.get(n).clone())
                else {
                    continue;
                };
                let (Some(i_usize), Some(n_usize)) = (i_val.to_usize(), n_val.to_usize()) else {
                    continue;
                };
                let result_elems: Vec<TermId> = if i_usize < s_elems.len() && n_usize > 0 {
                    let end = (i_usize + n_usize).min(s_elems.len());
                    s_elems[i_usize..end].to_vec()
                } else {
                    Vec::new() // out of bounds or n == 0 -> empty
                };
                let seq_sort = self.ctx.terms.sort(extract_term).clone();
                let literal = if result_elems.is_empty() {
                    self.mk_seq_empty(&seq_sort)
                } else if result_elems.len() == 1 {
                    result_elems[0]
                } else {
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("seq.++"), result_elems, seq_sort.clone())
                };
                if literal != extract_term && !froms.contains(&extract_term) {
                    froms.push(extract_term);
                    tos.push(literal);
                }
            }
            if froms.is_empty() {
                break;
            }
            let new_assertions: Vec<TermId> = self
                .ctx
                .assertions
                .clone()
                .into_iter()
                .map(|a| self.ctx.terms.substitute(a, &froms, &tos))
                .collect();
            self.ctx.assertions = new_assertions;
        }
    }

    /// True when `term` is a Seq-sorted variable.
    fn is_seq_var(&self, term: TermId) -> bool {
        matches!(self.ctx.terms.get(term), TermData::Var(..)) && self.ctx.terms.sort(term).is_seq()
    }

    /// Flatten `term` into its `seq.unit` element list. Returns `false` unless
    /// every leaf is `(seq.unit e)` or `seq.empty` (nested `seq.++` allowed;
    /// `seq.empty` contributes nothing). Element terms may be SYMBOLIC — the
    /// point-lowering equivalences only need the syntactic length of the shape.
    fn flatten_unit_concat(&self, term: TermId, out: &mut Vec<TermId>) -> bool {
        match self.ctx.terms.get(term) {
            TermData::App(Symbol::Named(n), args) if n == "seq.unit" && args.len() == 1 => {
                out.push(args[0]);
                true
            }
            TermData::App(Symbol::Named(n), args) if n == "seq.empty" && args.is_empty() => true,
            TermData::App(Symbol::Named(n), args) if n == "seq.++" && args.len() >= 2 => args
                .clone()
                .iter()
                .all(|&a| self.flatten_unit_concat(a, out)),
            _ => false,
        }
    }

    /// P0.1 phase-2b (#ssl-residue A): lower ground-window `seq.extract`
    /// equalities and pinned-length `seq.contains` atoms over a seq VARIABLE
    /// into finite conjunctions/disjunctions of concrete-index `seq.nth` reads,
    /// so [`Self::apply_point_read_reduction`] (which runs immediately after)
    /// hands the whole problem to the EUF+LIA core and
    /// `reconstruct_seq_from_len_nth` builds a pinned, gate-confirmable model.
    ///
    /// Rewrites (exact SMT-LIB equivalences, valid at ANY polarity/position):
    /// * `(= (seq.extract s i m) W)` — concrete `i >= 0`, concrete `m`, `W` a
    ///   unit-concat of exactly `m >= 1` elements —
    ///   ⟺ `i+m <= (seq.len s) ∧ AND_j (= (seq.nth s (+ i j)) W_j)`.
    ///   `seq.extract` returns a window of length `min(m, len(s)-i)` (empty when
    ///   `i` is out of bounds or `m <= 0`), which can equal the length-`m`
    ///   sequence `W` iff the window is full (`i+m <= len(s)`, which with
    ///   `m >= 1` implies `i` in bounds) and matches element-wise; every read
    ///   index `i+j < i+m <= len(s)` is in bounds, so no underspecified
    ///   out-of-bounds `seq.nth` value can influence the equivalence (when the
    ///   length conjunct is false, the conjunction is false — and so is the
    ///   original atom, the window being shorter than `W`).
    /// * `(seq.contains s W)` — `W` a unit-concat of `k >= 1` elements, and a
    ///   TOP-LEVEL conjunct pinning `(seq.len s)` to concrete `N` (<= 64) —
    ///   ⟺ `false` when `k > N`, else
    ///   `OR_{p=0..N-k} AND_j (= (seq.nth s (+ p j)) W_j)`.
    ///   Exact under the pinned length: every model of the assertion set
    ///   satisfies `len(s) = N`, and for such models containment is exactly a
    ///   match at some in-bounds start position, so substituting the atom
    ///   anywhere preserves the model set (`A ⊨ c ⟺ d` gives
    ///   `A ∧ φ[c] ≡ A ∧ φ[d]`).
    ///
    /// FAIL-CLOSED GATING: an atom is lowered only when EVERY DAG edge to its
    /// seq variable is a whitelisted `seq.nth`(concrete-index)/`seq.len` read,
    /// an occurrence inside a lowerable extract equality (with the extract term
    /// itself occurring ONLY inside such equalities), or a lowerable contains
    /// atom — i.e. exactly when the variable becomes fully point-read eligible
    /// afterwards. Any other shape leaves the assertions byte-identical
    /// (today's behavior, decided by the downstream passes or failed closed).
    /// Binders or unrecognized node kinds abort the pass entirely, mirroring
    /// the point-read census.
    pub(super) fn apply_extract_contains_point_lowering(&mut self) {
        use ay_core::kani_compat::DetHashMap as HashMap;
        const MAX_PINNED_CONTAINS_LEN: usize = 64;

        if self.ctx.assertions.is_empty() {
            return;
        }

        // DAG census: collect every reachable node; fail closed on binders or
        // unrecognized node kinds (they might carry an occurrence this pass
        // cannot inspect).
        let mut nodes: Vec<TermId> = Vec::new();
        {
            let mut stack: Vec<TermId> = self.ctx.assertions.clone();
            let mut seen: HashSet<TermId> = HashSet::default();
            while let Some(t) = stack.pop() {
                if !seen.insert(t) {
                    continue;
                }
                nodes.push(t);
                match self.ctx.terms.get(t) {
                    TermData::Forall(..) | TermData::Exists(..) | TermData::Let(..) => return,
                    TermData::App(_, args) => stack.extend(args.iter().copied()),
                    TermData::Not(a) => stack.push(*a),
                    TermData::Ite(c, th, el) => {
                        stack.push(*c);
                        stack.push(*th);
                        stack.push(*el);
                    }
                    TermData::Const(_) | TermData::Var(..) => {}
                    _ => return,
                }
            }
        }

        // Top-level pinned concrete lengths: `(= (seq.len v) N)` conjuncts.
        let mut pinned_len: HashMap<TermId, usize> = HashMap::default();
        {
            let assertions = self.ctx.assertions.clone();
            let mut conjuncts: Vec<TermId> = Vec::new();
            for &a in &assertions {
                conjuncts.push(a);
                crate::executor::quantifier_loop::collect_and_conjuncts(
                    &self.ctx.terms,
                    a,
                    &mut conjuncts,
                );
            }
            for &c in &conjuncts {
                let TermData::App(sym, args) = self.ctx.terms.get(c) else {
                    continue;
                };
                if sym.name() != "=" || args.len() != 2 {
                    continue;
                }
                let (l, r) = (args[0], args[1]);
                for (len_side, const_side) in [(l, r), (r, l)] {
                    let TermData::App(ls, largs) = self.ctx.terms.get(len_side) else {
                        continue;
                    };
                    if ls.name() != "seq.len" || largs.len() != 1 || !self.is_seq_var(largs[0]) {
                        continue;
                    }
                    let v = largs[0];
                    let TermData::Const(Constant::Int(n)) = self.ctx.terms.get(const_side) else {
                        continue;
                    };
                    if let Some(n) = n.to_usize() {
                        if n <= MAX_PINNED_CONTAINS_LEN {
                            pinned_len.entry(v).or_insert(n);
                        }
                    }
                }
            }
        }

        // Candidate lowerable atoms.
        struct ExtractLower {
            var: TermId,
            start: usize,
            elems: Vec<TermId>,
        }
        struct ContainsLower {
            var: TermId,
            pinned: usize,
            elems: Vec<TermId>,
        }
        let mut eq_lowers: HashMap<TermId, ExtractLower> = HashMap::default();
        let mut ctn_lowers: HashMap<TermId, ContainsLower> = HashMap::default();
        // Extract terms referenced by a lowerable equality → their seq var.
        let mut extract_vars: HashMap<TermId, TermId> = HashMap::default();

        for &t in &nodes {
            let TermData::App(sym, args) = self.ctx.terms.get(t) else {
                continue;
            };
            match sym.name() {
                "=" if args.len() == 2 => {
                    let (l, r) = (args[0], args[1]);
                    for (ex_side, w_side) in [(l, r), (r, l)] {
                        let TermData::App(es, eargs) = self.ctx.terms.get(ex_side) else {
                            continue;
                        };
                        if es.name() != "seq.extract"
                            || eargs.len() != 3
                            || !self.is_seq_var(eargs[0])
                        {
                            continue;
                        }
                        let (v, it, mt) = (eargs[0], eargs[1], eargs[2]);
                        let TermData::Const(Constant::Int(iv)) = self.ctx.terms.get(it) else {
                            continue;
                        };
                        let TermData::Const(Constant::Int(mv)) = self.ctx.terms.get(mt) else {
                            continue;
                        };
                        let (Some(i), Some(m)) = (iv.to_usize(), mv.to_usize()) else {
                            continue;
                        };
                        if m == 0 {
                            continue;
                        }
                        let mut elems: Vec<TermId> = Vec::new();
                        if !self.flatten_unit_concat(w_side, &mut elems) || elems.len() != m {
                            continue;
                        }
                        eq_lowers.entry(t).or_insert(ExtractLower {
                            var: v,
                            start: i,
                            elems,
                        });
                        extract_vars.insert(ex_side, v);
                        break;
                    }
                }
                "seq.contains" if args.len() == 2 => {
                    let (h, w) = (args[0], args[1]);
                    if !self.is_seq_var(h) {
                        continue;
                    }
                    let Some(&n) = pinned_len.get(&h) else {
                        continue;
                    };
                    let mut elems: Vec<TermId> = Vec::new();
                    if !self.flatten_unit_concat(w, &mut elems) || elems.is_empty() {
                        continue;
                    }
                    ctn_lowers.insert(
                        t,
                        ContainsLower {
                            var: h,
                            pinned: n,
                            elems,
                        },
                    );
                }
                _ => {}
            }
        }
        if eq_lowers.is_empty() && ctn_lowers.is_empty() {
            return;
        }

        // Var-validity census: every edge to a candidate var must be a
        // whitelisted point read, a validated lowerable extract, or a
        // lowerable contains atom. Everything else fails closed for that var.
        let mut bad: HashSet<TermId> = HashSet::default();
        for &t in &nodes {
            match self.ctx.terms.get(t) {
                TermData::App(sym, args) => {
                    let name = sym.name().to_string();
                    let args = args.clone();
                    for (pos, &a) in args.iter().enumerate() {
                        if self.is_seq_var(a) {
                            let ok = match name.as_str() {
                                "seq.nth" if args.len() == 2 && pos == 0 => matches!(
                                    self.ctx.terms.get(args[1]),
                                    TermData::Const(Constant::Int(ci)) if ci.to_usize().is_some()
                                ),
                                "seq.len" if args.len() == 1 && pos == 0 => true,
                                "seq.extract" if pos == 0 => extract_vars.contains_key(&t),
                                "seq.contains" if pos == 0 => ctn_lowers.contains_key(&t),
                                _ => false,
                            };
                            if !ok {
                                bad.insert(a);
                            }
                        }
                        // A lowerable extract term may occur ONLY as a side of
                        // a lowerable equality atom.
                        if let Some(&v) = extract_vars.get(&a) {
                            if !eq_lowers.contains_key(&t) {
                                bad.insert(v);
                            }
                        }
                    }
                }
                TermData::Not(a) => {
                    let a = *a;
                    if self.is_seq_var(a) {
                        bad.insert(a);
                    }
                    if let Some(&v) = extract_vars.get(&a) {
                        bad.insert(v);
                    }
                }
                TermData::Ite(c, th, el) => {
                    for x in [*c, *th, *el] {
                        if self.is_seq_var(x) {
                            bad.insert(x);
                        }
                        if let Some(&v) = extract_vars.get(&x) {
                            bad.insert(v);
                        }
                    }
                }
                _ => {}
            }
        }

        // Build replacements (deterministic order: DAG census order).
        let mut froms: Vec<TermId> = Vec::new();
        let mut tos: Vec<TermId> = Vec::new();
        for &t in &nodes {
            if let Some(lower) = eq_lowers.get(&t) {
                let (var, start) = (lower.var, lower.start);
                let elems = lower.elems.clone();
                if bad.contains(&var) {
                    continue;
                }
                let Some(elem_sort) = self.ctx.terms.sort(var).seq_element().cloned() else {
                    continue;
                };
                if !Self::point_read_reconstructible_sort(&elem_sort) {
                    continue;
                }
                let len_t = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("seq.len"), vec![var], Sort::Int);
                let end = self.ctx.terms.mk_int(BigInt::from(start + elems.len()));
                let mut conj: Vec<TermId> = vec![self.ctx.terms.mk_le(end, len_t)];
                for (j, &w) in elems.iter().enumerate() {
                    let idx = self.ctx.terms.mk_int(BigInt::from(start + j));
                    let nth = self.ctx.terms.mk_app(
                        Symbol::named("seq.nth"),
                        vec![var, idx],
                        elem_sort.clone(),
                    );
                    let eq = self.ctx.terms.mk_eq(nth, w);
                    conj.push(eq);
                }
                let repl = self.ctx.terms.mk_and(conj);
                if repl != t {
                    froms.push(t);
                    tos.push(repl);
                }
            } else if let Some(lower) = ctn_lowers.get(&t) {
                let (var, n) = (lower.var, lower.pinned);
                let elems = lower.elems.clone();
                if bad.contains(&var) {
                    continue;
                }
                let Some(elem_sort) = self.ctx.terms.sort(var).seq_element().cloned() else {
                    continue;
                };
                if !Self::point_read_reconstructible_sort(&elem_sort) {
                    continue;
                }
                let k = elems.len();
                let repl = if k > n {
                    self.ctx.terms.mk_bool(false)
                } else {
                    let mut disj: Vec<TermId> = Vec::new();
                    for p in 0..=(n - k) {
                        let mut conj: Vec<TermId> = Vec::new();
                        for (j, &w) in elems.iter().enumerate() {
                            let idx = self.ctx.terms.mk_int(BigInt::from(p + j));
                            let nth = self.ctx.terms.mk_app(
                                Symbol::named("seq.nth"),
                                vec![var, idx],
                                elem_sort.clone(),
                            );
                            let eq = self.ctx.terms.mk_eq(nth, w);
                            conj.push(eq);
                        }
                        disj.push(self.ctx.terms.mk_and(conj));
                    }
                    self.ctx.terms.mk_or(disj)
                };
                if repl != t {
                    froms.push(t);
                    tos.push(repl);
                }
            }
        }
        if froms.is_empty() {
            return;
        }
        let assertions = self.ctx.assertions.clone();
        self.ctx.assertions = assertions
            .into_iter()
            .map(|a| self.ctx.terms.substitute(a, &froms, &tos))
            .collect();
    }

    /// Point-read reduction (P0.1 phase-2a).
    ///
    /// Substitutes every `(seq.nth s i)` with a fresh uninterpreted function
    /// application `(__ay_pnth!<s> i)` over `s`'s element sort, and every
    /// `(seq.len s)` with a fresh non-negative Int constant `__ay_plen!<s>`, for
    /// EACH Seq variable `s` whose ONLY occurrences in the assertion DAG are the
    /// sequence operand (arg 0) of `seq.nth` / `seq.len`. This hands the element
    /// and length constraints to the mature EUF + LIA/LRA/BV core, which decides
    /// bound + disequality shapes that the seq theory only shares by equality
    /// (`4 < (seq.nth s 0) < 6 ∧ (seq.nth s 0) != 5` — z3 UNSAT, previously AY
    /// `unknown`; the pure-UF analogue `4 < (f 0) < 6 ∧ (f 0) != 5` already
    /// decides via the same combined solver).
    ///
    /// SOUNDNESS — equisatisfiable in BOTH directions. SMT-LIB `seq.nth` is a
    /// TOTAL function whose value at an out-of-bounds index is UNDERSPECIFIED (a
    /// fixed-but-arbitrary value per `(s, i)`), and `seq.len s >= 0` is the only
    /// length obligation of an otherwise-unconstrained `s`.
    /// * original SAT ⟹ reduct SAT: interpret `__ay_pnth!s(i)` as the original
    ///   model's value of `seq.nth(s, i)` (in- OR out-of-bounds) and
    ///   `__ay_plen!s` as `|s|`.
    /// * reduct SAT ⟹ original SAT: take `s` of length `__ay_plen!s` with
    ///   `s[i] := __ay_pnth!s(i)`; every in-bounds read equals `__ay_pnth!s(i)`
    ///   by construction and every out-of-bounds read is free to take
    ///   `__ay_pnth!s(i)` (underspecified). The `__ay_plen!s >= 0` guard makes
    ///   this construction always possible.
    /// The verdict is therefore preserved EXACTLY; the model reconstruction path
    /// (`reconstruct_seq_from_len_nth`) rebuilds `s` from these fresh symbols.
    ///
    /// The eligibility test is a FAIL-CLOSED WHITELIST over a COMPLETE DAG
    /// census: `total[v]` counts EVERY direct-child edge to a Seq var `v`;
    /// `white[v]` counts only the whitelisted edges (arg 0 of `seq.nth`/
    /// `seq.len`). `v` is eligible iff `total == white > 0`. ANY other position
    /// — an `=`/`distinct` operand, another seq op, an `ite`/`not` child, an
    /// index argument, a datatype/array field — is a non-whitelisted edge that
    /// raises `total` above `white` and disqualifies `v`; a masked occurrence
    /// would turn a real UNSAT into a wrong SAT, so the walk visits every child
    /// of every node kind. Binders (`forall`/`exists`/`let`) disqualify the
    /// WHOLE pass (a bound var could alias a free-var `TermId`; the seq model
    /// gate likewise scopes out on quantifiers). Aliasing `(let ((u s)) …)` /
    /// `(= u s)` cannot hide `s`: the alias is itself a non-whitelisted
    /// occurrence of `s` that blocks it.
    pub(super) fn apply_point_read_reduction(&mut self) {
        use ay_core::kani_compat::DetHashMap as HashMap;

        if self.ctx.assertions.is_empty() {
            return;
        }

        let mut total: HashMap<TermId, u32> = HashMap::default();
        let mut white: HashMap<TermId, u32> = HashMap::default();
        let mut has_len: HashMap<TermId, bool> = HashMap::default();
        // Concrete nth indices per var; a NON-concrete index disqualifies the var
        // (a per-(var,concrete-index) fresh element variable cannot capture a
        // symbolic-index read).
        let mut read_indices: HashMap<TermId, Vec<usize>> = HashMap::default();
        let mut bad_index: HashSet<TermId> = HashSet::default();

        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut seen: HashSet<TermId> = HashSet::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t).clone() {
                // Fail-closed: never reduce in the presence of binders.
                TermData::Forall(..) | TermData::Exists(..) | TermData::Let(..) => {
                    return;
                }
                TermData::App(sym, args) => {
                    if let Symbol::Named(name) = &sym {
                        if name == "seq.nth" && args.len() == 2 && self.is_seq_var(args[0]) {
                            *white.entry(args[0]).or_insert(0) += 1;
                            match self.ctx.terms.get(args[1]) {
                                TermData::Const(Constant::Int(ci)) if ci.to_usize().is_some() => {
                                    read_indices
                                        .entry(args[0])
                                        .or_default()
                                        .push(ci.to_usize().unwrap());
                                }
                                _ => {
                                    bad_index.insert(args[0]);
                                }
                            }
                        } else if name == "seq.len" && args.len() == 1 && self.is_seq_var(args[0]) {
                            *white.entry(args[0]).or_insert(0) += 1;
                            has_len.insert(args[0], true);
                        }
                    }
                    for &a in &args {
                        if self.is_seq_var(a) {
                            *total.entry(a).or_insert(0) += 1;
                        }
                        stack.push(a);
                    }
                }
                TermData::Not(a) => {
                    if self.is_seq_var(a) {
                        *total.entry(a).or_insert(0) += 1;
                    }
                    stack.push(a);
                }
                TermData::Ite(c, th, el) => {
                    for a in [c, th, el] {
                        if self.is_seq_var(a) {
                            *total.entry(a).or_insert(0) += 1;
                        }
                        stack.push(a);
                    }
                }
                TermData::Const(_) | TermData::Var(..) => {}
                // Fail-closed on any unrecognized node kind: it might carry a
                // seq occurrence this census cannot inspect.
                _ => return,
            }
        }

        let mut elig: HashMap<TermId, PointReadPlan> = HashMap::default();
        let mut plen_terms: Vec<TermId> = Vec::new();
        for (&v, &tot) in &total {
            let w = white.get(&v).copied().unwrap_or(0);
            if w == 0 || w != tot || bad_index.contains(&v) {
                continue;
            }
            let Some(elem_sort) = self.ctx.terms.sort(v).seq_element().cloned() else {
                continue;
            };
            if !Self::point_read_reconstructible_sort(&elem_sort) {
                continue;
            }
            // Fresh element variable per distinct concrete read index.
            let mut reads: HashMap<usize, TermId> = HashMap::default();
            if let Some(indices) = read_indices.get(&v) {
                for &k in indices {
                    reads.entry(k).or_insert_with(|| {
                        self.ctx
                            .terms
                            .mk_var(format!("__ay_pnth!{}!{}", v.0, k), elem_sort.clone())
                    });
                }
            }
            let plen = if has_len.get(&v).copied().unwrap_or(false) {
                let pt = self
                    .ctx
                    .terms
                    .mk_var(format!("__ay_plen!{}", v.0), Sort::Int);
                plen_terms.push(pt);
                Some(pt)
            } else {
                None
            };
            elig.insert(v, PointReadPlan { reads, plen });
        }
        if elig.is_empty() {
            return;
        }

        let mut memo: HashMap<TermId, TermId> = HashMap::default();
        let new_assertions: Vec<TermId> = self
            .ctx
            .assertions
            .clone()
            .into_iter()
            .map(|a| self.point_read_rewrite(a, &elig, &mut memo))
            .collect();
        self.ctx.assertions = new_assertions;

        // Restore `seq.len s >= 0` on each substituted length constant.
        if !plen_terms.is_empty() {
            let zero = self.ctx.terms.mk_int(BigInt::zero());
            let mut present: HashSet<TermId> = self.ctx.assertions.iter().copied().collect();
            for pt in plen_terms {
                let g = self.ctx.terms.mk_ge(pt, zero);
                if present.insert(g) {
                    self.ctx.assertions.push(g);
                }
            }
        }
    }

    /// Element sorts the point-read reduction can reconstruct a model for.
    fn point_read_reconstructible_sort(sort: &Sort) -> bool {
        matches!(sort, Sort::Int | Sort::Real | Sort::Bool | Sort::BitVec(_))
    }

    /// Bottom-up rewriter for [`Self::apply_point_read_reduction`]: replaces
    /// whitelisted `(seq.nth s k)` / `(seq.len s)` nodes with their fresh
    /// element/length variables and rebuilds every enclosing node. Memoized over
    /// the hash-consed DAG.
    fn point_read_rewrite(
        &mut self,
        term: TermId,
        elig: &ay_core::kani_compat::DetHashMap<TermId, PointReadPlan>,
        memo: &mut ay_core::kani_compat::DetHashMap<TermId, TermId>,
    ) -> TermId {
        if let Some(&r) = memo.get(&term) {
            return r;
        }
        let result = match self.ctx.terms.get(term).clone() {
            TermData::App(Symbol::Named(name), args)
                if name == "seq.nth"
                    && args.len() == 2
                    && elig.contains_key(&args[0])
                    && matches!(self.ctx.terms.get(args[1]),
                        TermData::Const(Constant::Int(ci)) if ci.to_usize().is_some()) =>
            {
                let TermData::Const(Constant::Int(ci)) = self.ctx.terms.get(args[1]) else {
                    unreachable!()
                };
                let k = ci.to_usize().unwrap();
                // Eligibility guaranteed a fresh var for every concrete read.
                elig[&args[0]].reads[&k]
            }
            TermData::App(Symbol::Named(name), args)
                if name == "seq.len"
                    && args.len() == 1
                    && elig.get(&args[0]).is_some_and(|e| e.plen.is_some()) =>
            {
                elig[&args[0]].plen.unwrap()
            }
            TermData::App(sym, args) => {
                let sort = self.ctx.terms.sort(term).clone();
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&a| self.point_read_rewrite(a, elig, memo))
                    .collect();
                if new_args == args {
                    term
                } else {
                    self.ctx.terms.mk_app(sym, new_args, sort)
                }
            }
            TermData::Not(a) => {
                let na = self.point_read_rewrite(a, elig, memo);
                if na == a {
                    term
                } else {
                    self.ctx.terms.mk_not(na)
                }
            }
            TermData::Ite(c, th, el) => {
                let nc = self.point_read_rewrite(c, elig, memo);
                let nt = self.point_read_rewrite(th, elig, memo);
                let ne = self.point_read_rewrite(el, elig, memo);
                if nc == c && nt == th && ne == el {
                    term
                } else {
                    self.ctx.terms.mk_ite(nc, nt, ne)
                }
            }
            // Const / Var (leaves); binders unreachable (pass bailed on them).
            _ => term,
        };
        memo.insert(term, result);
        result
    }

    /// Length abstraction for sequence WORD EQUATIONS (sound completeness —
    /// purely additive necessary conditions, never prunes a real model).
    ///
    /// AY already materializes `seq.len` for concat terms (the sum axiom) and
    /// knows `len >= 0`, but a VARIABLE equated to a concat — e.g.
    /// `(= s2 (seq.++ s1 s1))` — has no `seq.len` term of its own, so the implied
    /// length contradiction stays invisible and the word-equation solver can
    /// return a spurious SAT (`s2 = s1.s1 & s2 = s1 & s2 != empty`).
    ///
    /// We scope the pass to genuine word equations only: it fires solely for the
    /// relevance closure seeded by "var-concats" — a `seq.++` (>=2 leaves) with a
    /// seq-VARIABLE leaf (where a length cycle can arise). Vars that are leaves of
    /// a var-concat, and vars transitively equated to a relevant term, join the
    /// closure. Equalities over only concrete units (`(= t (unit 1) ++ (unit 2))`)
    /// stay outside the closure, so the rich seq decision procedures (prefixof,
    /// extract, ...) keep their own models instead of being over-constrained into
    /// `unknown`. For each in-scope Seq equality atom `(= a b)` emit:
    ///   * `(=> (= a b) (= (seq.len a) (seq.len b)))` — length congruence;
    ///   * `(>= (seq.len a) 0)`, `(>= (seq.len b) 0)`; and, when exactly one side
    ///     is the empty sequence and the other is in scope, the biconditional
    ///   * `(= (= a b) (= (seq.len other) 0))`  — a seq equals empty iff len 0.
    /// Every emitted fact is a valid necessary condition, so the pass is monotone
    /// and can never turn a satisfiable formula unsat unless the word equation is
    /// genuinely infeasible. Intended to run on the pristine user assertions
    /// (before other axiom passes inject their own seq equalities).
    pub(super) fn collect_seq_length_constraint_axioms(&mut self) -> Vec<TermId> {
        const MAX_LEN_CONSTRAINT_ATOMS: usize = 256;
        let assertions = self.ctx.assertions.clone();
        let mut eq_atoms: Vec<TermId> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        for &a in &assertions {
            self.collect_seq_equality_atoms(a, &mut eq_atoms, &mut seen);
        }

        // Seed the relevance set with seq-Var leaves of any var-concat.
        let mut relevant: HashSet<TermId> = HashSet::default();
        for &eq in &eq_atoms {
            let TermData::App(sym, args) = self.ctx.terms.get(eq).clone() else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }
            for &side in &args {
                let leaves = self.flatten_seq_concat(side);
                if leaves.len() >= 2 && leaves.iter().any(|&l| self.is_seq_var(l)) {
                    for &l in &leaves {
                        if self.is_seq_var(l) {
                            relevant.insert(l);
                        }
                    }
                }
            }
        }
        if relevant.is_empty() {
            return Vec::new();
        }
        // A term is in scope if it is itself relevant or has a relevant leaf.
        let in_scope = |this: &Self, t: TermId, rel: &HashSet<TermId>| -> bool {
            rel.contains(&t) || this.flatten_seq_concat(t).iter().any(|l| rel.contains(l))
        };
        // Propagate relevance across equalities to fixpoint (close length cycles).
        let mut changed = true;
        while changed {
            changed = false;
            for &eq in &eq_atoms {
                let TermData::App(sym, args) = self.ctx.terms.get(eq).clone() else {
                    continue;
                };
                if sym.name() != "=" || args.len() != 2 {
                    continue;
                }
                let (a, b) = (args[0], args[1]);
                if in_scope(self, a, &relevant) && self.is_seq_var(b) && relevant.insert(b) {
                    changed = true;
                }
                if in_scope(self, b, &relevant) && self.is_seq_var(a) && relevant.insert(a) {
                    changed = true;
                }
            }
        }

        let zero = self.ctx.terms.mk_int(BigInt::zero());
        let mut axioms = Vec::new();
        for eq_term in eq_atoms.into_iter().take(MAX_LEN_CONSTRAINT_ATOMS) {
            let (lhs, rhs) = match self.ctx.terms.get(eq_term).clone() {
                TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
                    (args[0], args[1])
                }
                _ => continue,
            };
            let lhs_scope = in_scope(self, lhs, &relevant);
            let rhs_scope = in_scope(self, rhs, &relevant);
            if !(lhs_scope || rhs_scope) {
                continue;
            }
            let len_l = self.mk_seq_len(lhs);
            let len_r = self.mk_seq_len(rhs);
            // Length congruence: (= a b) => (= len(a) len(b)).
            let len_eq = self.ctx.terms.mk_eq(len_l, len_r);
            let not_eq = self.ctx.terms.mk_not(eq_term);
            axioms.push(self.ctx.terms.mk_or(vec![not_eq, len_eq]));
            // Non-negativity of the (possibly newly materialized) length terms.
            axioms.push(self.ctx.terms.mk_ge(len_l, zero));
            axioms.push(self.ctx.terms.mk_ge(len_r, zero));
            // Emptiness biconditional when exactly one side is the empty sequence
            // and the non-empty side is in scope.
            let l_empty = self.seq_term_is_empty(lhs);
            let r_empty = self.seq_term_is_empty(rhs);
            if l_empty ^ r_empty {
                let (other, other_len) = if l_empty { (rhs, len_r) } else { (lhs, len_l) };
                if in_scope(self, other, &relevant) {
                    let len_zero = self.ctx.terms.mk_eq(other_len, zero);
                    axioms.push(self.ctx.terms.mk_eq(eq_term, len_zero));
                }
            }
        }
        axioms
    }

    /// Determined-length expansion for PURE seq word equations (sound, decides
    /// what length abstraction alone leaves SAT).
    ///
    /// When a sequence variable's length is forced to a concrete `k` by the linear
    /// length system of the DEFINITELY-TRUE seq equalities, it equals a concat of
    /// `k` element units, so SUBSTITUTE it with `(seq.++ (unit e0) ... (unit
    /// e_{k-1}))` (fresh element vars). The unit-decomposition pass then turns e.g.
    /// `(seq.++ (unit 0) s (unit 2)) = (seq.++ s (unit 1) s)` (which forces |s|=1)
    /// into the element equations `0=e, e=1, 2=e` and refutes it as UNSAT.
    ///
    /// SOUNDNESS — two invariants:
    ///   * Length equations are derived ONLY from DEFINITELY-TRUE seq equalities
    ///     (top-level assertions and the conjuncts of a top-level `(and ...)`).
    ///     Never from an equality under `not`/`or`/`ite`, which may be false — the
    ///     earlier version's unsoundness (17 wrong-UNSAT on fuzz). `|L| = |R|` is a
    ///     necessary consequence of a true `L = R`.
    ///   * Substituting a length-`k` variable by `k` fresh-element units is
    ///     equisatisfiable (a length-`k` sequence IS such a concat for some
    ///     elements), so it can never turn SAT into UNSAT.
    ///
    /// GATED: a variable used inside any RICH seq op (nth/at/extract/indexof/
    /// replace/contains/prefixof/suffixof) is EXCLUDED — those have dedicated
    /// decision procedures keyed on the original variable.
    pub(super) fn expand_determined_length_seq_vars(&mut self) {
        const MAX_LEN: i64 = 8;
        // Pure index reads (seq.nth/seq.at) do NOT block a determined-length
        // substitution: it is equisatisfiable and resolves the index read
        // concretely (#bug15). Only the rich decision procedures stay excluded.
        let excluded = self.collect_rich_op_seq_vars(false);

        // Length equations `sum_v coeff[v]*|v| = rhs` from definitely-true facts.
        // Each entry: (Vec<(var, coeff)>, rhs).
        let mut equations: Vec<(Vec<(TermId, i64)>, i64)> = Vec::new();
        for (l, r) in self.collect_definitely_true_seq_equalities() {
            let (Some((ul, vl)), Some((ur, vr))) =
                (self.seq_length_profile(l), self.seq_length_profile(r))
            else {
                continue;
            };
            let mut coeffs: Vec<(TermId, i64)> = Vec::new();
            let add = |v: TermId, c: i64, coeffs: &mut Vec<(TermId, i64)>| {
                if let Some(e) = coeffs.iter_mut().find(|(x, _)| *x == v) {
                    e.1 += c;
                } else {
                    coeffs.push((v, c));
                }
            };
            for (v, c) in vl {
                add(v, c, &mut coeffs);
            }
            for (v, c) in vr {
                add(v, -c, &mut coeffs);
            }
            coeffs.retain(|(_, c)| *c != 0);
            equations.push((coeffs, ur - ul)); // sum coeff*|v| = unitsR - unitsL
        }
        // Direct `(= (seq.len v) k)` constraints from definitely-true facts.
        for (l, r) in self.collect_definitely_true_seq_equalities_int() {
            let pair = match (
                self.seq_len_inner(l),
                self.int_const_i64(r),
                self.seq_len_inner(r),
                self.int_const_i64(l),
            ) {
                (Some(v), Some(k), _, _) => Some((v, k)),
                (_, _, Some(v), Some(k)) => Some((v, k)),
                _ => None,
            };
            if let Some((v, k)) = pair {
                if self.is_seq_var(v) {
                    equations.push((vec![(v, 1)], k));
                }
            }
        }

        // Iterative single-variable elimination (sound for triangular systems):
        // resolve an equation once all but one of its variables are known.
        let mut known: Vec<(TermId, i64)> = Vec::new();
        let mut changed = true;
        while changed {
            changed = false;
            for (coeffs, rhs) in &equations {
                let mut residual = *rhs;
                let mut unknown: Vec<(TermId, i64)> = Vec::new();
                for &(v, c) in coeffs {
                    if let Some(&(_, kv)) = known.iter().find(|(x, _)| *x == v) {
                        residual -= c * kv;
                    } else {
                        unknown.push((v, c));
                    }
                }
                if unknown.len() == 1 {
                    let (v, c) = unknown[0];
                    if c != 0 && residual % c == 0 {
                        let k = residual / c;
                        if (0..=MAX_LEN).contains(&k)
                            && self.is_seq_var(v)
                            && !known.iter().any(|(x, _)| *x == v)
                        {
                            known.push((v, k));
                            changed = true;
                        }
                    }
                }
            }
        }

        // Substitute determined, non-excluded variables by `k` fresh unit concats.
        let mut froms: Vec<TermId> = Vec::new();
        let mut tos: Vec<TermId> = Vec::new();
        for (v, k) in known {
            if excluded.contains(&v) || !(0..=MAX_LEN).contains(&k) {
                continue;
            }
            let seq_sort = self.ctx.terms.sort(v).clone();
            let Sort::Seq(elem_sort) = seq_sort.clone() else {
                continue;
            };
            let units: Vec<TermId> = (0..k)
                .map(|i| {
                    let ev = self
                        .ctx
                        .terms
                        .mk_fresh_var(&format!("_seqx_{}_{}", v.0, i), (*elem_sort).clone());
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("seq.unit"), vec![ev], seq_sort.clone())
                })
                .collect();
            let replacement = if units.is_empty() {
                self.ctx.terms.mk_app(
                    Symbol::named("seq.empty"),
                    Vec::<TermId>::new(),
                    seq_sort.clone(),
                )
            } else if units.len() == 1 {
                units[0]
            } else {
                self.ctx
                    .terms
                    .mk_app(Symbol::named("seq.++"), units, seq_sort.clone())
            };
            froms.push(v);
            tos.push(replacement);
        }
        if froms.is_empty() {
            return;
        }
        let new_assertions: Vec<TermId> = self
            .ctx
            .assertions
            .clone()
            .into_iter()
            .map(|a| self.ctx.terms.substitute(a, &froms, &tos))
            .collect();
        self.ctx.assertions = new_assertions;
    }

    /// True when `term` contains no variable anywhere in its DAG — a fully ground
    /// value. Bounded DFS; conservatively returns false on budget exhaustion.
    fn seq_term_is_ground(&self, term: TermId) -> bool {
        let mut stack = vec![term];
        let mut budget = 2048u32;
        while let Some(t) = stack.pop() {
            if budget == 0 {
                return false;
            }
            budget -= 1;
            match self.ctx.terms.get(t) {
                TermData::Var(..) => return false,
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                _ => {}
            }
        }
        true
    }

    /// True when `term` is a GROUND seq literal: `seq.empty`, `(seq.unit g)` with
    /// a ground element, or `(seq.++ ...)` of ground seq literals. Such a term
    /// denotes a single concrete sequence value in every model.
    fn is_ground_seq_literal(&self, term: TermId) -> bool {
        match self.ctx.terms.get(term) {
            TermData::App(Symbol::Named(n), args) if n == "seq.empty" && args.is_empty() => true,
            TermData::App(Symbol::Named(n), args) if n == "seq.unit" && args.len() == 1 => {
                self.seq_term_is_ground(args[0])
            }
            TermData::App(Symbol::Named(n), args) if n == "seq.++" && args.len() >= 2 => {
                args.iter().all(|&a| self.is_ground_seq_literal(a))
            }
            _ => false,
        }
    }

    /// Inline a seq variable that a TOP-LEVEL conjunct pins to a GROUND seq
    /// literal (`(= v lit)` / `(= lit v)`, `lit` a `seq.empty` / constant-element
    /// `seq.unit` / concat of such). Substituting `v := lit` everywhere is
    /// equisatisfiable — the equality is a definite top-level fact, so `v` equals
    /// `lit` in every model — and it makes ground predicates such as
    /// `(seq.contains v (seq.unit c))` fully ground so the existing ground
    /// refutation path decides them.
    ///
    /// This closes a wrong-SAT (`#seq-det-var`): when the seq solver returns SAT
    /// it may leave `v` unresolved in the validation model (model completion does
    /// NOT default seq vars to empty, to avoid over-rejecting genuine word-equation
    /// SAT), so the strict `SeqOracle` cannot evaluate `(seq.contains v ...)` to
    /// `Bool(false)` and the broken model escapes (e.g. `(= (seq.unit 3) s1) ∧
    /// (seq.contains s1 (seq.unit -3))`, UNSAT, was reported SAT). After inlining,
    /// the contains is ground and refuted.
    ///
    /// SOUND: a pure equisatisfiable substitution can never flip a genuine
    /// sat/unsat. Scoped to GROUND literals only, so genuine word equations
    /// (`(= (++ a b) (++ b a))`, RHS contains variables) are untouched. Conflicting
    /// bindings (`(= [3] v) ∧ (= [4] v)`) drop out of the binding set and are left
    /// for the transitive/ground refutation passes.
    ///
    /// EXCLUDES vars read by the skolem-DECOMPOSITION ops (extract / indexof /
    /// last_indexof / replace / replace_all): those reductions build overlapping
    /// skolem constraints that lose completeness when fed a ground concat instead
    /// of a variable (`#6033` — `s = [1,2,3] ∧ prefixof([1],s) ∧ extract(s,1,1)=[2]`
    /// regressed sat→unknown). Their own decision procedures keep the var form.
    /// `seq.contains/prefixof/suffixof/at/nth` resolve concretely on a ground
    /// literal, so vars used only by those stay inlinable.
    pub(super) fn inline_determined_ground_seq_vars(&mut self) {
        use ay_core::kani_compat::DetHashMap as HashMap;
        // P0.1 phase-2b (#ssl-residue A): lower ground-window extract
        // equalities / pinned-length contains atoms to concrete point reads
        // first, so the reduction below admits them. Idempotent (lowered atoms
        // contain no `seq.extract`/`seq.contains` over the var anymore).
        self.apply_extract_contains_point_lowering();
        // P0.1 phase-2a: route point-read-only sequence variables into the
        // mature EUF+LIA/BV core BEFORE any ground/word-equation normalization.
        // Idempotent (a reduced var has no `seq.nth`/`seq.len` occurrence left),
        // so the second `solve_seq_lia` invocation of this pass is a no-op.
        self.apply_point_read_reduction();
        // Bounded fixpoint: substituting a var with a ground literal can expose a
        // NEW determined var (`(= s2 s1) ∧ (= [3] s1)` ⟹ after `s1 := [3]`, `s2`
        // is pinned to `[3]`). Each round eliminates >=1 distinct var, so the loop
        // converges in at most (#seq vars) rounds; cap defensively. On a
        // conflicting pin (`(= [3] s) ∧ (= [4] s)`) the first binding wins and the
        // other equality becomes a ground-false fact — sound either way (the
        // formula is genuinely unsat, both substitutions expose that).
        for _round in 0..16u32 {
            // Vars read by a skolem-decomposition op keep their var form (recomputed
            // each round: a substituted var disappears, freeing later chain links).
            let excluded = self.collect_skolem_decomposition_seq_vars();
            let assertions = self.ctx.assertions.clone();
            let mut conjuncts: Vec<TermId> = Vec::new();
            for &a in &assertions {
                conjuncts.push(a);
                crate::executor::quantifier_loop::collect_and_conjuncts(
                    &self.ctx.terms,
                    a,
                    &mut conjuncts,
                );
            }
            let mut binding: HashMap<TermId, TermId> = HashMap::default();
            for &c in &conjuncts {
                if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(c) {
                    if name != "=" || args.len() != 2 {
                        continue;
                    }
                    let (l, r) = (args[0], args[1]);
                    let found = if self.is_seq_var(l) && self.is_ground_seq_literal(r) {
                        Some((l, r))
                    } else if self.is_seq_var(r) && self.is_ground_seq_literal(l) {
                        Some((r, l))
                    } else {
                        None
                    };
                    if let Some((v, lit)) = found {
                        if excluded.contains(&v) {
                            continue;
                        }
                        // Keep the first binding for a var (conflict surfaces as a
                        // ground-false equality after substitution).
                        if !binding.contains_key(&v) {
                            binding.insert(v, lit);
                        }
                    }
                }
            }
            if binding.is_empty() {
                break;
            }
            let froms: Vec<TermId> = binding.keys().copied().collect();
            let tos: Vec<TermId> = froms.iter().map(|v| binding[v]).collect();
            let new_assertions: Vec<TermId> = self
                .ctx
                .assertions
                .clone()
                .into_iter()
                .map(|a| self.ctx.terms.substitute(a, &froms, &tos))
                .collect();
            self.ctx.assertions = new_assertions;
        }
    }

    /// Decide BOUNDED seq word equations by complete length enumeration.
    ///
    /// When every word-equation seq VARIABLE (non-rich-op) has its length
    /// provably bounded by `K <= MAX_LEN` — via a definitely-true direct length
    /// constraint `(= (seq.len T) K)` whose flattened profile is
    /// `sum occ_i*|v_i| = K` with all `occ_i >= 1` (so `|v| <= K` since the other
    /// terms are non-negative) — the variable can only take finitely many lengths
    /// `0..=K`. Enumerate ALL length tuples over those bounds, substitute each
    /// variable by a concat of that many fresh element units, and assert the
    /// DISJUNCTION of the per-tuple substituted assertion sets.
    ///
    /// SOUND + COMPLETE for this fragment: `F` is equisatisfiable to
    /// `OR_tuple F[vars := units_tuple]` because the bounds are valid upper bounds
    /// (every satisfying assignment's lengths are among the enumerated tuples) and
    /// each substitution is equisatisfiable (a length-k sequence IS a k-unit
    /// concat). Infeasible tuples simply yield UNSAT disjuncts (their substituted
    /// length constraints fail), which never affect the disjunction's truth. The
    /// downstream unit-decomposition + length passes then refute each disjunct's
    /// element constraints, deciding e.g. `(= (seq.++ s0 s2 (unit 0) (unit 1))
    /// (seq.++ (unit -1) s0 (unit 1)))` with `(= (seq.len (seq.++ s2 s1 s0 s1))
    /// 2)`. Gated to skip rich-op vars and capped at `MAX_TUPLES` disjuncts.
    pub(super) fn decide_bounded_seq_word_equations(&mut self) {
        const MAX_LEN: i64 = 6;
        const MAX_VARS: usize = 4;
        const MAX_TUPLES: i64 = 64;

        // Conservative: the bounded disjunctive rewrite can over-approximate, so
        // keep index reads rich here (unlike the determined-length expansion).
        let excluded = self.collect_rich_op_seq_vars(true);
        let seq_eqs = self.collect_definitely_true_seq_equalities();
        if seq_eqs.is_empty() {
            return;
        }
        // Only fire on a GENUINE word equation that needs element alignment: a
        // seq equality `(= L R)` where at least one side is a multi-leaf concat
        // and BOTH sides contain a seq-variable leaf. A simple `(= s (seq.unit
        // 42))` (one side has no var) or `(= s1 s2)` (no multi-leaf concat) is
        // already decided by the normal pipeline, so the disjunctive rewrite would
        // only over-approximate it into an Unknown — skip those.
        let has_hard_word_eq = seq_eqs.iter().any(|&(l, r)| {
            let (Some((_, vl)), Some((_, vr))) =
                (self.seq_length_profile(l), self.seq_length_profile(r))
            else {
                return false;
            };
            let l_leaves = self.flatten_seq_concat(l).len();
            let r_leaves = self.flatten_seq_concat(r).len();
            !vl.is_empty() && !vr.is_empty() && (l_leaves >= 2 || r_leaves >= 2)
        });
        if !has_hard_word_eq {
            return;
        }
        // Word variables: non-excluded seq vars occurring in definitely-true seq
        // equalities. Bail if any equality side has an indeterminate-length leaf.
        let mut word_vars: Vec<TermId> = Vec::new();
        for (l, r) in &seq_eqs {
            for &side in &[*l, *r] {
                let Some((_, vars)) = self.seq_length_profile(side) else {
                    return;
                };
                for (v, _) in vars {
                    if !excluded.contains(&v) && !word_vars.contains(&v) {
                        word_vars.push(v);
                    }
                }
            }
        }
        if word_vars.is_empty() || word_vars.len() > MAX_VARS {
            return;
        }
        // Sound per-variable upper bound from positive-occurrence direct length
        // constraints `(= (seq.len T) K)`.
        let mut bound: Vec<(TermId, i64)> = Vec::new();
        for (l, r) in self.collect_definitely_true_seq_equalities_int() {
            let (lenarg, k) = match (
                self.seq_len_inner(l),
                self.int_const_i64(r),
                self.seq_len_inner(r),
                self.int_const_i64(l),
            ) {
                (Some(t), Some(k), _, _) => (t, k),
                (_, _, Some(t), Some(k)) => (t, k),
                _ => continue,
            };
            if !(0..=MAX_LEN).contains(&k) {
                continue;
            }
            let Some((_units, vars)) = self.seq_length_profile(lenarg) else {
                continue;
            };
            for (v, _occ) in vars {
                if let Some(e) = bound.iter_mut().find(|(x, _)| *x == v) {
                    if k < e.1 {
                        e.1 = k;
                    }
                } else {
                    bound.push((v, k));
                }
            }
        }
        // Every word variable must be provably bounded; else bail (unbounded —
        // needs a full word-equation solver, out of scope).
        let bounds: Vec<(TermId, i64)> = match word_vars
            .iter()
            .map(|&v| bound.iter().find(|(x, _)| *x == v).map(|(_, b)| (v, *b)))
            .collect::<Option<Vec<_>>>()
        {
            Some(b) => b,
            None => return,
        };
        let radices: Vec<i64> = bounds.iter().map(|(_, b)| b + 1).collect();
        let total: i64 = radices.iter().product();
        if total <= 1 || total > MAX_TUPLES {
            return;
        }

        let base_assertions = self.ctx.assertions.clone();
        let mut disjuncts: Vec<TermId> = Vec::with_capacity(total as usize);
        for idx in 0..total {
            let mut rem = idx;
            let mut froms: Vec<TermId> = Vec::new();
            let mut tos: Vec<TermId> = Vec::new();
            let mut ok = true;
            for (i, (v, _)) in bounds.iter().enumerate() {
                let k = rem % radices[i];
                rem /= radices[i];
                let seq_sort = self.ctx.terms.sort(*v).clone();
                let Sort::Seq(elem) = seq_sort.clone() else {
                    ok = false;
                    break;
                };
                let units: Vec<TermId> = (0..k)
                    .map(|j| {
                        let ev = self
                            .ctx
                            .terms
                            .mk_fresh_var(&format!("_seqw_{}_{}_{}", v.0, idx, j), (*elem).clone());
                        self.ctx
                            .terms
                            .mk_app(Symbol::named("seq.unit"), vec![ev], seq_sort.clone())
                    })
                    .collect();
                let repl = if units.is_empty() {
                    self.ctx.terms.mk_app(
                        Symbol::named("seq.empty"),
                        Vec::<TermId>::new(),
                        seq_sort.clone(),
                    )
                } else if units.len() == 1 {
                    units[0]
                } else {
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("seq.++"), units, seq_sort.clone())
                };
                froms.push(*v);
                tos.push(repl);
            }
            if !ok {
                return;
            }
            let subst: Vec<TermId> = base_assertions
                .iter()
                .map(|&a| self.ctx.terms.substitute(a, &froms, &tos))
                .collect();
            disjuncts.push(self.ctx.terms.mk_and(subst));
        }
        let disjunction = self.ctx.terms.mk_or(disjuncts);
        self.ctx.assertions = vec![disjunction];
    }

    /// Length congruence for DEFINITELY-TRUE seq equalities: for each top-level
    /// conjunctive `(= a b)` over sequences, emit `(= (seq.len a) (seq.len b))`.
    /// A var=var alias `(= s0 s1)` otherwise leaves `len(s0)`/`len(s1)` independent,
    /// so `len(s0 ++ s1) = len(s0)+len(s1) = 3` stays satisfiable even though
    /// `s0 = s1` forces `2*len(s0) = 3` (no integer) — a spurious SAT
    /// (#seq-len-congruence). The emitted fact is a sound NECESSARY condition
    /// (`a = b ⟹ len(a) = len(b)`, the equality definitely holds), so it only ADDS
    /// refutation power and can never turn a SAT problem UNSAT.
    pub(super) fn collect_seq_definite_length_congruence_axioms(&mut self) -> Vec<TermId> {
        let eqs = self.collect_definitely_true_seq_equalities();
        let mut axioms = Vec::new();
        for (a, b) in eqs {
            if a == b {
                continue;
            }
            // Restrict to var=var / var=empty aliases (each side a bare seq VAR or
            // the empty sequence). Emitting `len` over a unit/concat/rich operand
            // (e.g. `(= s (seq.unit 1))`) adds `seq.len` terms onto the rich-op
            // operands and over-degrades their decision procedures to unknown
            // (#seq-len-congruence prefixof regression); those length facts are
            // already supplied by the concat/unit length axioms anyway.
            let safe = |this: &Self, t: TermId| this.is_seq_var(t) || this.seq_term_is_empty(t);
            if !safe(self, a) || !safe(self, b) {
                continue;
            }
            let la = self.mk_seq_len(a);
            let lb = self.mk_seq_len(b);
            let eq = self.ctx.terms.mk_eq(la, lb);
            axioms.push(eq);
        }
        axioms
    }

    /// Transitive chaining of seq equalities through a shared variable: when two
    /// distinct multi-leaf concat terms `X` and `Y` are BOTH equated (definitely,
    /// i.e. in top-level conjunctive position) to the same seq variable `v`, emit
    /// the derived word equation `(= X Y)`.
    ///
    /// AY already DECIDES a direct word equation `(= (++ s2 s0 (unit -2))
    /// (++ s0 s0 (unit 2)))` (length alignment + trailing-unit decomposition), but
    /// did not combine `(= X v)` and `(= Y v)` into `(= X Y)`, so the conflict
    /// stayed invisible and the solver returned a spurious SAT (#seq-transitive-wordeq).
    /// The emitted equality is a SOUND consequence (transitivity of `=`), so it
    /// can only ADD refutation power — never a wrong-unsat. Bounded per variable.
    pub(super) fn collect_seq_transitive_equality_axioms(&mut self) -> Vec<TermId> {
        const MAX_EXPRS_PER_VAR: usize = 4;
        let eqs = self.collect_definitely_true_seq_equalities();
        // pivot term -> distinct multi-leaf concat expressions equated to it.
        //
        // The pivot is ANY common seq term, not only a variable
        // (#seq-transitive-wordeq generalization): the seq axiom passes emit
        // definite equalities anchored on rich-op APPLICATIONS — e.g.
        // `seq.replace` with a provably-empty pattern yields the definite
        // `(= (seq.replace u empty d) (seq.++ d u))`, and the user asserts
        // `(= (seq.replace u empty d) (seq.++ (seq.unit 0) (seq.unit 1)))`.
        // Chaining through the shared replace term derives the word equation
        // `(= (seq.++ d u) (seq.++ (seq.unit 0) (seq.unit 1)))` that the
        // unit-decomposition pass refutes (qf_slia_seqextract_oob_false_sat:
        // wrong SAT without it). Transitivity of `=` is sound for any pivot.
        let mut by_var: Vec<(TermId, Vec<TermId>)> = Vec::new();
        for (a, b) in eqs {
            for (pivot, expr) in [(a, b), (b, a)] {
                // Only chain multi-leaf concats — the word-equation material
                // the downstream decomposition can refute.
                if self.flatten_seq_concat(expr).len() < 2 {
                    continue;
                }
                if let Some(e) = by_var.iter_mut().find(|(v, _)| *v == pivot) {
                    if !e.1.contains(&expr) && e.1.len() < MAX_EXPRS_PER_VAR {
                        e.1.push(expr);
                    }
                } else {
                    by_var.push((pivot, vec![expr]));
                }
            }
        }
        let mut axioms = Vec::new();
        for (_, exprs) in &by_var {
            for i in 0..exprs.len() {
                for j in (i + 1)..exprs.len() {
                    let eq = self.ctx.terms.mk_eq(exprs[i], exprs[j]);
                    axioms.push(eq);
                }
            }
        }
        axioms
    }

    /// Collect (lhs, rhs) of every DEFINITELY-TRUE Seq-sorted equality: a
    /// top-level assertion `(= L R)` or a conjunct of a top-level `(and ...)`.
    /// Does NOT descend into `not`/`or`/`ite`/`=>`, so a conditionally-asserted
    /// equality (which may be false) is never treated as a length fact.
    fn collect_definitely_true_seq_equalities(&self) -> Vec<(TermId, TermId)> {
        let mut out = Vec::new();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut seen: HashSet<TermId> = HashSet::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            if let TermData::App(sym, args) = self.ctx.terms.get(t).clone() {
                if sym.name() == "and" {
                    stack.extend(args);
                } else if sym.name() == "="
                    && args.len() == 2
                    && self.ctx.terms.sort(args[0]).is_seq()
                {
                    out.push((args[0], args[1]));
                }
            }
        }
        out
    }

    /// Like `collect_definitely_true_seq_equalities` but returns Int-sorted
    /// equalities (for `(= (seq.len v) k)` length facts).
    fn collect_definitely_true_seq_equalities_int(&self) -> Vec<(TermId, TermId)> {
        let mut out = Vec::new();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut seen: HashSet<TermId> = HashSet::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            if let TermData::App(sym, args) = self.ctx.terms.get(t).clone() {
                if sym.name() == "and" {
                    stack.extend(args);
                } else if sym.name() == "=" && args.len() == 2 {
                    out.push((args[0], args[1]));
                }
            }
        }
        out
    }

    /// Seq vars appearing (transitively) inside any RICH seq op's arguments.
    ///
    /// `index_ops_rich` controls whether the pure STRUCTURAL index reads
    /// `seq.nth` / `seq.at` count as rich. They are excluded by the bounded
    /// word-equation decider (conservative: the disjunctive rewrite could
    /// over-approximate), but a var whose length is DETERMINED to a concrete `k`
    /// is soundly substitutable by `k` fresh units even when it is read by
    /// `seq.nth`/`seq.at`: a length-`k` sequence IS that `k`-unit concat, and the
    /// nth/at axioms resolve `(seq.nth (seq.++ u0 ..) i)` concretely. So
    /// `expand_determined_length_seq_vars` passes `false` to refute word
    /// equations like `[2].s.[0] = s.[1].s` that also carry a `(seq.nth s i)`
    /// element constraint (#bug15). The genuine rich decision procedures
    /// (extract/replace/contains/prefixof/suffixof/indexof) stay excluded so they
    /// keep their own models.
    fn collect_rich_op_seq_vars(&self, index_ops_rich: bool) -> HashSet<TermId> {
        const RICH_BASE: &[&str] = &[
            "seq.extract",
            "seq.indexof",
            "seq.last_indexof",
            "seq.replace",
            "seq.replace_all",
            "seq.contains",
            "seq.prefixof",
            "seq.suffixof",
        ];
        const INDEX_OPS: &[&str] = &["seq.nth", "seq.at"];
        let is_rich = |name: &str| -> bool {
            RICH_BASE.contains(&name) || (index_ops_rich && INDEX_OPS.contains(&name))
        };
        let mut out: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut visited: HashSet<TermId> = HashSet::default();
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t).clone() {
                TermData::App(sym, args) => {
                    if is_rich(sym.name()) {
                        for &a in &args {
                            self.collect_seq_vars_in_subtree(a, &mut out);
                        }
                    }
                    for a in args {
                        stack.push(a);
                    }
                }
                TermData::Not(i) => stack.push(i),
                TermData::Ite(c, th, el) => {
                    stack.push(c);
                    stack.push(th);
                    stack.push(el);
                }
                _ => {}
            }
        }
        out
    }

    /// Seq vars appearing (transitively) inside a skolem-DECOMPOSITION op's
    /// arguments (`seq.extract` / `seq.indexof` / `seq.last_indexof` /
    /// `seq.replace` / `seq.replace_all`). These reductions introduce skolem
    /// sub-sequences whose constraints lose completeness when the source is a
    /// ground concat literal rather than a variable, so determined-value inlining
    /// must leave such vars in their variable form (#6033). Predicate ops
    /// (contains/prefixof/suffixof) and concrete index reads (at/nth) are NOT
    /// listed: they resolve directly on a ground literal.
    fn collect_skolem_decomposition_seq_vars(&self) -> HashSet<TermId> {
        const DECOMP_OPS: &[&str] = &[
            "seq.extract",
            "seq.indexof",
            "seq.last_indexof",
            "seq.replace",
            "seq.replace_all",
        ];
        let mut out: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut visited: HashSet<TermId> = HashSet::default();
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t).clone() {
                TermData::App(sym, args) => {
                    if DECOMP_OPS.contains(&sym.name()) {
                        for &a in &args {
                            self.collect_seq_vars_in_subtree(a, &mut out);
                        }
                    }
                    for a in args {
                        stack.push(a);
                    }
                }
                TermData::Not(i) => stack.push(i),
                TermData::Ite(c, th, el) => {
                    stack.push(c);
                    stack.push(th);
                    stack.push(el);
                }
                _ => {}
            }
        }
        out
    }

    /// Collect every Seq-sorted variable in `t`'s subtree.
    fn collect_seq_vars_in_subtree(&self, t: TermId, out: &mut HashSet<TermId>) {
        let mut stack = vec![t];
        let mut seen: HashSet<TermId> = HashSet::default();
        while let Some(x) = stack.pop() {
            if !seen.insert(x) {
                continue;
            }
            if self.is_seq_var(x) {
                out.insert(x);
            }
            match self.ctx.terms.get(x).clone() {
                TermData::App(_, args) => {
                    for a in args {
                        stack.push(a);
                    }
                }
                TermData::Not(i) => stack.push(i),
                TermData::Ite(c, th, el) => {
                    stack.push(c);
                    stack.push(th);
                    stack.push(el);
                }
                _ => {}
            }
        }
    }

    /// Length profile of a seq term: `(unit_count, [(var, occurrences)])` over the
    /// concat leaves, or None if any leaf has indeterminate length (a non-unit,
    /// non-variable, non-empty term such as a rich-op result).
    fn seq_length_profile(&self, t: TermId) -> Option<(i64, Vec<(TermId, i64)>)> {
        let leaves = self.flatten_seq_concat(t);
        let mut units = 0i64;
        let mut vars: Vec<(TermId, i64)> = Vec::new();
        for &leaf in &leaves {
            if self.seq_unit_element(leaf).is_some() {
                units += 1;
            } else if self.is_seq_var(leaf) {
                if let Some(e) = vars.iter_mut().find(|(v, _)| *v == leaf) {
                    e.1 += 1;
                } else {
                    vars.push((leaf, 1));
                }
            } else if self.seq_term_is_empty(leaf) {
                // contributes 0
            } else {
                return None;
            }
        }
        Some((units, vars))
    }

    /// If `term` is `(seq.len s)`, return `Some(s)`.
    fn seq_len_inner(&self, term: TermId) -> Option<TermId> {
        match self.ctx.terms.get(term) {
            TermData::App(Symbol::Named(name), args) if name == "seq.len" && args.len() == 1 => {
                Some(args[0])
            }
            _ => None,
        }
    }

    /// If `term` is an integer constant, return it as i64.
    fn int_const_i64(&self, term: TermId) -> Option<i64> {
        match self.ctx.terms.get(term) {
            TermData::Const(Constant::Int(n)) => n.to_i64(),
            _ => None,
        }
    }

    /// Flatten a `seq.++` term to its ordered list of non-empty leaves, recursing
    /// through nested concats and dropping `seq.empty`/`""` operands (identity).
    /// A non-concat term returns itself as the sole leaf. Bounded by the term DAG.
    fn flatten_seq_concat(&self, term: TermId) -> Vec<TermId> {
        let mut leaves = Vec::new();
        // Push children reversed so the LIFO stack yields left-to-right leaf order.
        let mut stack = vec![term];
        while let Some(t) = stack.pop() {
            match self.ctx.terms.get(t) {
                TermData::App(Symbol::Named(name), args) if name == "seq.++" && args.len() >= 2 => {
                    for &arg in args.iter().rev() {
                        stack.push(arg);
                    }
                }
                TermData::App(Symbol::Named(name), args)
                    if name == "seq.empty" && args.is_empty() =>
                {
                    // Identity: drop empty leaves.
                }
                TermData::Const(Constant::String(s)) if s.is_empty() => {
                    // Empty string is the String-sort identity element.
                }
                _ => leaves.push(t),
            }
        }
        leaves
    }

    /// Collect base tautology axioms for `seq.contains`/`seq.prefixof`/
    /// `seq.suffixof` over empty or reflexive operands (#seq-pred-taut).
    ///
    /// These are unconditional theorems of the sequence theory, but the existing
    /// axiom generators emit only *necessary conditions* (`pred => ...` length and
    /// decomposition lemmas) — never the *sufficient condition* that forces the
    /// predicate true. Without them, the negation of a tautology (e.g.
    /// `(not (seq.contains s (as seq.empty (Seq Int))))`) is wrongly satisfiable.
    ///
    /// Forced facts (each a semantic theorem, so sound):
    /// - `seq.contains(s, empty) = true`   (empty is a subsequence of everything)
    /// - `seq.contains(s, s) = true`        (reflexive containment)
    /// - `seq.prefixof(empty, s) = true`    (empty is a prefix of everything)
    /// - `seq.prefixof(s, s) = true`        (reflexive prefix)
    /// - `seq.suffixof(empty, s) = true`    (empty is a suffix of everything)
    /// - `seq.suffixof(s, s) = true`        (reflexive suffix)
    pub(super) fn collect_seq_predicate_tautology_axioms(&mut self) -> Vec<TermId> {
        let scan = self.scan_seq_terms();
        let mut axioms = Vec::new();
        let zero = self.ctx.terms.mk_int(BigInt::zero());
        // Canonicalize each operand to its CONCAT-LEAF list (aliases resolved,
        // empties dropped). Two operands that are equal only via an asserted alias
        // (`s0 = s1`) or a concat-identity collapse (`empty ++ s0 = s0`) have
        // distinct TermIds; comparing leaf lists recognizes them as equal. The
        // structural sub-relations below are all sound theorems: if needle leaves
        // are a prefix/suffix/contiguous-infix of haystack leaves (each leaf equal
        // as a whole block), the corresponding predicate genuinely holds.
        let aliases = self.build_seq_alias_map();

        // contains(s, t): force true when t is empty OR t's leaves are a contiguous
        // infix of s's leaves (covers reflexive `s == t` and `contains(a++b, a)`).
        // Else the SUFFICIENT `len(t)=0 => contains` (empty/semantically-empty
        // needle, e.g. `(seq.extract s i n)` with n<=0). Sound: semantic theorems.
        for &(contains_term, s, t) in &scan.contains_terms {
            let t_leaves = self.seq_canon_leaves(t, &aliases);
            let s_leaves = self.seq_canon_leaves(s, &aliases);
            if self.seq_term_is_empty(t)
                || t_leaves.is_empty()
                || Self::seq_leaves_infix(&s_leaves, &t_leaves)
            {
                axioms.push(contains_term);
            } else if let (Some(ea), Some(eb)) = (
                (s_leaves.len() == 1)
                    .then(|| self.seq_unit_element(s_leaves[0]))
                    .flatten(),
                (t_leaves.len() == 1)
                    .then(|| self.seq_unit_element(t_leaves[0]))
                    .flatten(),
            ) {
                // Both operands canonicalize to a SINGLE unit `(seq.unit e)`, so
                // each has length 1; a length-1 sequence contains a length-1
                // sequence iff they are equal iff their elements are equal. Emit
                // the EXACT biconditional `contains <=> (= ea eb)` — this refutes
                // a falsely-asserted `(seq.contains (seq.unit 3) (seq.unit -3))`
                // (incl. via an alias `s1 = (seq.unit 3)`) that the positive-only
                // infix/`len=0 => contains` axioms leave satisfiable (#seq-unit-contains).
                let elem_eq = self.ctx.terms.mk_eq(ea, eb);
                axioms.push(self.ctx.terms.mk_eq(contains_term, elem_eq));
            } else {
                let len_t = self.mk_seq_len(t);
                let t_empty = self.ctx.terms.mk_eq(len_t, zero);
                axioms.push(self.ctx.terms.mk_implies(t_empty, contains_term));
            }
        }
        // Transitivity refutation (#seq-contains-transitivity): containment is
        // transitive — `contains(H, mid) ∧ contains(mid, M) => contains(H, M)`.
        // When the OUTER haystack `H` and the INNER needle `M` both resolve to
        // CONCRETE ground sequences but `M` is NOT a contiguous subsequence of
        // `H`, the consequent `contains(H, M)` is provably FALSE, so the two
        // asserted contains atoms cannot both hold: emit the clause
        //   (or (not c1) (not c2)).
        // This refutes e.g.
        //   (seq.contains (seq.unit 5) s0) ∧ (seq.contains s0 (seq.unit 6))
        // (s0 ⊆ [5], so s0 cannot contain [6]) WITHOUT constraining the free
        // middle `mid` (no disjunction over its value), so it never derails the
        // solver's model build on a genuinely-satisfiable contains. Sound:
        // containment transitivity is an exact theorem, so the clause can only
        // remove models that violate it — never flip a genuine SAT to UNSAT.
        let ground_map = self.build_ground_seq_map();
        let resolve_ground = |me: &Self, term: TermId| -> Option<Vec<TermId>> {
            let g = ground_map.get(&term).copied().unwrap_or(term);
            me.try_extract_ground_seq(g)
        };
        for i in 0..scan.contains_terms.len() {
            let (c1, _h, mid1) = scan.contains_terms[i];
            let mid1_leaves = self.seq_canon_leaves(mid1, &aliases);
            // Only consider a free (non-ground) middle: a ground middle is
            // already handled by the per-atom ground evaluation above.
            if resolve_ground(self, mid1).is_some() {
                continue;
            }
            let Some(h_elems) = resolve_ground(self, scan.contains_terms[i].1) else {
                continue;
            };
            for j in 0..scan.contains_terms.len() {
                if j == i {
                    continue;
                }
                let (c2, mid2, m) = scan.contains_terms[j];
                // The inner haystack `mid2` must be the SAME canonical seq as
                // the outer needle `mid1`.
                if self.seq_canon_leaves(mid2, &aliases) != mid1_leaves {
                    continue;
                }
                let Some(m_elems) = resolve_ground(self, m) else {
                    continue;
                };
                // contains(H, M) over the resolved ground element lists.
                if !self.ground_seq_contains(&h_elems, &m_elems) {
                    let not_c1 = self.ctx.terms.mk_not(c1);
                    let not_c2 = self.ctx.terms.mk_not(c2);
                    axioms.push(self.ctx.terms.mk_or(vec![not_c1, not_c2]));
                }
            }
        }
        // prefixof(p, s): force true when p empty OR p's leaves are a PREFIX of s's
        // leaves; else `len(p)=0 => prefixof`.
        for &(prefix_term, p, s) in &scan.prefixof_terms {
            let p_leaves = self.seq_canon_leaves(p, &aliases);
            let s_leaves = self.seq_canon_leaves(s, &aliases);
            if self.seq_term_is_empty(p) || p_leaves.is_empty() || s_leaves.starts_with(&p_leaves) {
                axioms.push(prefix_term);
            } else {
                let len_p = self.mk_seq_len(p);
                let p_empty = self.ctx.terms.mk_eq(len_p, zero);
                axioms.push(self.ctx.terms.mk_implies(p_empty, prefix_term));
            }
        }
        // suffixof(q, s): force true when q empty OR q's leaves are a SUFFIX of s's
        // leaves; else `len(q)=0 => suffixof`.
        for &(suffix_term, q, s) in &scan.suffixof_terms {
            let q_leaves = self.seq_canon_leaves(q, &aliases);
            let s_leaves = self.seq_canon_leaves(s, &aliases);
            if self.seq_term_is_empty(q) || q_leaves.is_empty() || s_leaves.ends_with(&q_leaves) {
                axioms.push(suffix_term);
            } else {
                let len_q = self.mk_seq_len(q);
                let q_empty = self.ctx.terms.mk_eq(len_q, zero);
                axioms.push(self.ctx.terms.mk_implies(q_empty, suffix_term));
            }
        }

        axioms
    }

    /// Concat-leaf list of a seq term with aliases resolved and empties dropped:
    /// resolve the whole term, flatten its `seq.++`, then resolve+reflatten each
    /// leaf (so a leaf aliased to a concat expands). Used to compare seq terms
    /// up to aliasing and concat-identity.
    fn seq_canon_leaves(&self, t: TermId, aliases: &[(TermId, TermId)]) -> Vec<TermId> {
        let root = self.resolve_seq_alias(t, aliases);
        let mut out = Vec::new();
        for leaf in self.flatten_seq_concat(root) {
            let rl = self.resolve_seq_alias(leaf, aliases);
            for l2 in self.flatten_seq_concat(rl) {
                // Drop PROVABLY-EMPTY leaves the syntactic flatten can't see — an
                // `(seq.extract s i n)` with constant `i < 0` or `n <= 0` is empty
                // per SMT-LIB, so it is the concat identity.
                if self.seq_extract_provably_empty(l2) {
                    continue;
                }
                // Collapse var=var alias classes to a single representative:
                // `resolve_seq_alias` returns a bare var unchanged when its class
                // holds no concrete expression, so `s0` and `s1` under `(= s0 s1)`
                // would not unify. The class-min TermId is a consistent rep.
                out.push(self.seq_class_rep(l2, aliases));
            }
        }
        out
    }

    /// Rewrite every PROVABLY-EMPTY `(seq.extract s i n)` subterm (constant
    /// `i < 0` or `n <= 0`) to `(as seq.empty ...)` throughout the assertions.
    ///
    /// Such an extract IS the empty sequence per SMT-LIB regardless of `s`, so the
    /// rewrite is semantically EXACT (sound both directions — neither a wrong-unsat
    /// nor a wrong-sat). It exposes facts the leaf-drop in `seq_canon_leaves`
    /// cannot reach a whole-term equality: `(= (seq.extract s1 -2 3) s1)` becomes
    /// `(= (as seq.empty ..) s1)`, forcing `s1 = empty` (#seq-extract-empty-fold).
    pub(super) fn fold_provably_empty_seq_extracts(&mut self) {
        let mut targets: Vec<TermId> = Vec::new();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut seen: HashSet<TermId> = HashSet::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            if self.seq_extract_provably_empty(t) && !targets.contains(&t) {
                targets.push(t);
            }
            match self.ctx.terms.get(t).clone() {
                TermData::App(_, args) => stack.extend(args),
                TermData::Not(i) => stack.push(i),
                TermData::Ite(c, a, b) => {
                    stack.push(c);
                    stack.push(a);
                    stack.push(b);
                }
                _ => {}
            }
        }
        if targets.is_empty() {
            return;
        }
        let mut froms: Vec<TermId> = Vec::new();
        let mut tos: Vec<TermId> = Vec::new();
        for t in targets {
            let sort = self.ctx.terms.sort(t).clone();
            let empty =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("seq.empty"), Vec::<TermId>::new(), sort);
            froms.push(t);
            tos.push(empty);
        }
        let new_assertions: Vec<TermId> = self
            .ctx
            .assertions
            .clone()
            .into_iter()
            .map(|a| self.ctx.terms.substitute(a, &froms, &tos))
            .collect();
        self.ctx.assertions = new_assertions;
    }

    /// `(seq.extract s i n)` denotes the empty sequence (SMT-LIB) when EITHER the
    /// CONSTANT offset `i < 0`, OR the CONSTANT length `n <= 0`, OR the CONSTANT
    /// offset `i >= len(s)` for a base `s` whose length is determinable as a
    /// constant. In all three cases the extract is empty REGARDLESS of the other
    /// (possibly symbolic) operands, so it can be folded to `(as seq.empty ..)` /
    /// dropped from a concat-leaf list. The fold is semantically EXACT (sound both
    /// directions — neither a wrong-unsat nor a wrong-sat).
    fn seq_extract_provably_empty(&self, t: TermId) -> bool {
        if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(t) {
            if name == "seq.extract" && args.len() == 3 {
                // Capture operands before any further borrows of `self.ctx.terms`.
                let base = args[0];
                let off_term = args[1];
                let len_term = args[2];
                if let TermData::Const(Constant::Int(off)) = self.ctx.terms.get(off_term) {
                    if *off < BigInt::zero() {
                        return true;
                    }
                    // Out-of-bounds offset: a CONSTANT offset `>= len(base)` for a
                    // base sequence whose length is a determinable constant `L`.
                    // SMT-LIB: `(seq.extract s i n)` with `0 <= i` but `i >= |s|`
                    // is the empty sequence regardless of `n` (even symbolic `n`).
                    // `seq_length_profile` returns `(units, vars)`; with NO vars the
                    // length is EXACTLY `units` (each `seq.unit` leaf = 1, `seq.empty`
                    // = 0, ground concat = sum). Guard `units >= 0` for safety.
                    let off = off.clone();
                    if let Some((units, vars)) = self.seq_length_profile(base) {
                        if vars.is_empty() && units >= 0 && off >= BigInt::from(units) {
                            return true;
                        }
                    }
                }
                if let TermData::Const(Constant::Int(len)) = self.ctx.terms.get(len_term) {
                    if *len <= BigInt::zero() {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// Equality-class representative of `t` over the (undirected) seq alias graph:
    /// the minimum TermId reachable. Makes all members of a `(= a b)(= b c)…` class
    /// canonicalize to one term so leaf-list comparison recognizes them as equal.
    fn seq_class_rep(&self, t: TermId, aliases: &[(TermId, TermId)]) -> TermId {
        use ay_core::kani_compat::DetHashSet as HashSet;
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack = vec![t];
        let mut rep = t;
        while let Some(x) = stack.pop() {
            if !seen.insert(x) {
                continue;
            }
            if x < rep {
                rep = x;
            }
            for &(a, b) in aliases {
                if a == x {
                    stack.push(b);
                }
                if b == x {
                    stack.push(a);
                }
            }
        }
        rep
    }

    /// Whether `needle` occurs as a CONTIGUOUS block within `hay` (both already
    /// canonical leaf lists). Empty needle matches anywhere.
    fn seq_leaves_infix(hay: &[TermId], needle: &[TermId]) -> bool {
        if needle.is_empty() {
            return true;
        }
        if needle.len() > hay.len() {
            return false;
        }
        hay.windows(needle.len()).any(|w| w == needle)
    }

    /// True when `term` is syntactically the empty sequence: `seq.empty`, the
    /// empty string literal `""`, or `seq.++` over only empty operands.
    pub(super) fn seq_term_is_empty(&self, term: TermId) -> bool {
        match self.ctx.terms.get(term) {
            TermData::App(Symbol::Named(name), args) if name == "seq.empty" && args.is_empty() => {
                true
            }
            TermData::App(Symbol::Named(name), args) if name == "seq.++" && args.len() >= 2 => {
                args.iter().all(|&arg| self.seq_term_is_empty(arg))
            }
            TermData::Const(Constant::String(s)) => s.is_empty(),
            _ => false,
        }
    }

    /// Check whether assertions contain axiom-generating Seq operations (#5841).
    ///
    /// These operations (contains, extract, prefixof, suffixof, indexof) generate
    /// length constraints that require LIA routing.
    /// True when a POSITIVE (top-level conjunctive) seq equality `(= a b)` has a
    /// `seq.++` operand — a WORD EQUATION needing length reasoning. The EUF+Seq
    /// pipeline treats concat as uninterpreted and cannot refute a length-infeasible
    /// word equation (`(seq.++ s (seq.unit x)) = s`), which it wrongly reports SAT
    /// for Seq<BitVec> elements; `solve_seq_lia` decides it via the element-agnostic
    /// length axioms (#seqbv-concat-routing).
    ///
    /// Descends ONLY a top-level `and` — a NEGATED concat equality
    /// `(not (= (++ s0 s1) (++ s1 s0)))` is genuinely SAT (concat is not
    /// commutative) and the EUF pipeline decides it; routing it to `solve_seq_lia`
    /// would over-degrade it to Unknown.
    pub(super) fn assertions_contain_seq_concat_equality(&self) -> bool {
        let is_concat = |this: &Self, t: TermId| matches!(this.ctx.terms.get(t), TermData::App(s, _) if s.name() == "seq.++");
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut visited: HashSet<TermId> = HashSet::default();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            if let TermData::App(sym, args) = self.ctx.terms.get(term).clone() {
                if sym.name() == "and" {
                    stack.extend(args);
                    continue;
                }
                if sym.name() == "="
                    && args.len() == 2
                    && self.ctx.terms.sort(args[0]).is_seq()
                    && (is_concat(self, args[0]) || is_concat(self, args[1]))
                {
                    return true;
                }
            }
        }
        false
    }

    pub(super) fn assertions_contain_axiom_ops(&self) -> bool {
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut visited = HashSet::default();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    if matches!(
                        name.as_str(),
                        "seq.contains"
                            | "seq.extract"
                            | "seq.prefixof"
                            | "seq.suffixof"
                            | "seq.indexof"
                            | "seq.last_indexof"
                            | "seq.replace"
                    ) {
                        return true;
                    }
                    for &arg in args {
                        stack.push(arg);
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                _ => {}
            }
        }
        false
    }

    /// Scan assertions for seq-typed terms (read-only pass over the term DAG).
    pub(super) fn scan_seq_terms(&self) -> SeqTermScan {
        let mut scan = SeqTermScan::new();
        scan.scan_roots(&self.ctx.terms, &self.ctx.assertions);
        scan
    }

    /// Generate length axiom terms from collected seq structure terms.
    pub(super) fn generate_seq_len_axioms(&mut self, scan: &SeqTermScan) -> Vec<TermId> {
        let mut axioms = Vec::new();
        let mut seen_len_args: HashSet<TermId> =
            scan.len_terms.iter().map(|&(_, inner)| inner).collect();
        let zero = self.ctx.terms.mk_int(BigInt::zero());
        let one = self.ctx.terms.mk_int(BigInt::from(1));

        // Axiom 1: seq.len(s) >= 0 for each seq.len term
        for &(len_term, _) in &scan.len_terms {
            axioms.push(self.ctx.terms.mk_ge(len_term, zero));
        }

        // Axiom 2: seq.len(seq.unit(x)) = 1
        for &unit_term in &scan.unit_terms {
            let len = self.mk_seq_len(unit_term);
            axioms.push(self.ctx.terms.mk_eq(len, one));
            if seen_len_args.insert(unit_term) {
                axioms.push(self.ctx.terms.mk_ge(len, zero));
            }
        }

        // Axiom 3: seq.len(seq.empty) = 0
        for &empty_term in &scan.empty_terms {
            let len = self.mk_seq_len(empty_term);
            axioms.push(self.ctx.terms.mk_eq(len, zero));
        }
        // Bridge explicit String `seq.empty` terms from user assertions to the
        // canonical empty-string term used by internally generated axioms (#6342).
        for &empty_term in &scan.empty_terms {
            let sort = self.ctx.terms.sort(empty_term).clone();
            if sort == Sort::String {
                let canonical = self.mk_seq_empty(&sort);
                if empty_term != canonical {
                    axioms.push(self.ctx.terms.mk_eq(empty_term, canonical));
                }
            }
        }

        // Axiom 4: seq.len(seq.++(a, b)) = seq.len(a) + seq.len(b)
        for (concat_term, args) in &scan.concat_terms {
            let concat_len = self.mk_seq_len(*concat_term);
            let arg_lens: Vec<TermId> = args.iter().map(|&a| self.mk_seq_len(a)).collect();
            let sum = self.ctx.terms.mk_add(arg_lens.clone());
            axioms.push(self.ctx.terms.mk_eq(concat_len, sum));
            for len in arg_lens {
                axioms.push(self.ctx.terms.mk_ge(len, zero));
            }
        }

        axioms
    }

    /// Generate `seq.nth` axioms from collected terms (#5841).
    ///
    /// Axiom 5: `seq.nth(seq.unit(x), 0) = x` — element extraction from unit sequence.
    /// Axiom 6: `seq.nth(seq.++(a, b), i) = ite(i < len(a), nth(a, i), nth(b, i - len(a)))`
    ///
    /// Concat decomposition creates new nth terms that may themselves need the
    /// unit axiom, so we process in two passes.
    pub(super) fn generate_seq_nth_axioms(&mut self, scan: &SeqTermScan) -> Vec<TermId> {
        let mut axioms = Vec::new();
        let zero = self.ctx.terms.mk_int(BigInt::zero());
        // New nth terms created by concat decomposition that need unit-axiom check.
        let mut derived_nth: Vec<(TermId, TermId, TermId)> = Vec::new();

        // Resolve a `seq.nth` argument that is a variable transitively equated
        // to a concrete sequence expression (e.g. `(= sq2 sq)(= sq (seq.unit 1))`)
        // through the alias chain, so the structural axioms below still fire.
        // The original `nth_term = seq.nth(var, idx)` stays the axiom LHS, so we
        // assert `seq.nth(var, idx) = <resolved element>`, which is a sound
        // congruence consequence of the alias equalities (#seq-nth-alias).
        let aliases = self.build_seq_alias_map();

        for &(nth_term, seq_arg, idx_arg) in &scan.nth_terms {
            let seq_arg = self.resolve_seq_alias(seq_arg, &aliases);
            match self.ctx.terms.get(seq_arg) {
                TermData::App(Symbol::Named(name), args)
                    if name == "seq.unit" && args.len() == 1 =>
                {
                    let element = args[0];
                    // Axiom 5: seq.nth(seq.unit(x), i) = x WHEN i = 0 (else the read
                    // is out of bounds / unspecified). Emit the GUARDED form
                    // `(=> (= i 0) (= nth x))` so it also fires when the index is a
                    // VARIABLE the solver equates to 0 (e.g. `(= v10 0)`), not only a
                    // syntactic literal 0. The prior `is_zero_idx` syntactic check
                    // left `(seq.nth (seq.unit 0) v10)` with `v10 = 0` unconstrained,
                    // a false-SAT (fuzzer seq_falsesat_nth_ground_eval). For a
                    // syntactic-0 index the guard `(= 0 0)` is true, preserving the
                    // prior unconditional `nth = x`; for i != 0 it stays unconstrained
                    // (sound — the unit read is unspecified there).
                    let nth_eq_elem = self.ctx.terms.mk_eq(nth_term, element);
                    let idx_is_zero = self.ctx.terms.mk_eq(idx_arg, zero);
                    axioms.push(self.ctx.terms.mk_implies(idx_is_zero, nth_eq_elem));
                }
                TermData::App(Symbol::Named(name), args) if name == "seq.++" && args.len() >= 2 => {
                    let elem_sort = self.ctx.terms.sort(nth_term).clone();
                    let segs = args.clone();

                    // Axiom 6 (n-ary): seq.nth(a0 ++ a1 ++ ... ++ a_{m-1}, i) selects
                    // the segment containing index i:
                    //   nth = nth(a_k, i - (len a0 + ... + len a_{k-1}))   where
                    //         (len a0+...+len a_{k-1}) <= i < (len a0+...+len a_k)
                    // built as a fold of `ite(i < prefix_{k+1}, nth(a_k, off_k), rest)`
                    // from the last segment up. The 2-ary case is exactly the prior
                    // single ite. Each per-segment `nth(a_k, off_k)` is tracked for
                    // the unit/derived second pass so a `seq.unit` operand resolves.
                    let mut prefix = zero; // running sum of segment lengths before k
                    let mut offsets: Vec<(TermId, TermId, TermId, TermId)> = Vec::new();
                    // collect (nth_k, seg_k, off_k, prefix_after_k) per segment
                    for &seg in &segs {
                        let len_seg = self.mk_seq_len(seg);
                        // index offset into this segment: i - prefix
                        let off_k = if prefix == zero {
                            idx_arg
                        } else {
                            self.ctx.terms.mk_sub(vec![idx_arg, prefix])
                        };
                        let nth_k = self.ctx.terms.mk_app(
                            Symbol::named("seq.nth"),
                            vec![seg, off_k],
                            elem_sort.clone(),
                        );
                        let prefix_after = self.ctx.terms.mk_add(vec![prefix, len_seg]);
                        offsets.push((nth_k, seg, off_k, prefix_after));
                        // len(seg) >= 0
                        let len_ge0 = self.ctx.terms.mk_ge(len_seg, zero);
                        axioms.push(len_ge0);
                        prefix = prefix_after;
                    }
                    // Total concat length = sum of every segment length. This is
                    // the running `prefix` after the segment loop above
                    // (prefix_after of the last segment).
                    let concat_len = prefix;
                    // Fold from the last segment upward.
                    let mut result = offsets.last().map(|t| t.0).unwrap_or(nth_term);
                    for k in (0..offsets.len().saturating_sub(1)).rev() {
                        let (nth_k, _seg, _off, prefix_after_k) = offsets[k];
                        let cond = self.ctx.terms.mk_lt(idx_arg, prefix_after_k);
                        result = self.ctx.terms.mk_ite(cond, nth_k, result);
                    }
                    // OOB SOUNDNESS GUARD (#seq-nth-concat-oob): the ite-fold's
                    // innermost else is `nth(last_seg, i - prefix_before_last)`,
                    // and its outermost `then` for a negative index is
                    // `nth(seg0, i)` — neither branch bounds `i` from above (only
                    // the per-segment `i < prefix_after_k` lower splits). An
                    // UNCONDITIONAL `nth(C,i) = result` therefore forces an
                    // out-of-bounds `nth(a++b, i)` (i >= len C, or i < 0) EQUAL to
                    // an independent, underspecified OOB read of a single segment —
                    // an INVALID axiom that ships a wrong-UNSAT. Verified
                    // reproducer:
                    //   (distinct (seq.nth (seq.++ a b) 5) (seq.nth b 4)) with
                    //   |a|=|b|=1 is z3-SAT but the naked equality forces it unsat.
                    // Guard the equality with in-bounds `0 <= i < len C`; the OOB
                    // case stays underspecified — each (s,i) read denotes a fixed
                    // but arbitrary value, exactly z3's semantics (z1/z2 pins).
                    let idx_ge0 = self.ctx.terms.mk_ge(idx_arg, zero);
                    let idx_lt_len = self.ctx.terms.mk_lt(idx_arg, concat_len);
                    let in_bounds = self.ctx.terms.mk_and(vec![idx_ge0, idx_lt_len]);
                    let nth_eq_result = self.ctx.terms.mk_eq(nth_term, result);
                    axioms.push(self.ctx.terms.mk_implies(in_bounds, nth_eq_result));

                    // Track per-segment nth terms for second-pass axiomatization.
                    for (nth_k, seg, off_k, _pref) in offsets {
                        derived_nth.push((nth_k, seg, off_k));
                    }
                }
                _ => {}
            }
        }

        // Second pass: apply unit axiom to nth terms created by concat decomposition.
        // For derived terms, the index may be a symbolic expression (e.g., i - len(a))
        // that equals 0 only after LIA reasoning. We inject:
        //   1. nth(seq.unit(x), 0) = x  (canonical zero-index axiom)
        //   2. idx = 0  => nth(seq.unit(x), idx) = nth(seq.unit(x), 0)
        //      (via EUF congruence once LIA proves idx = 0)
        // Approach: inject the canonical axiom + equality bridge so the
        // Nelson-Oppen combination of LIA and EUF can chain the reasoning.
        for (nth_term, seq_arg, idx_arg) in derived_nth {
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(seq_arg) {
                if name == "seq.unit" && args.len() == 1 {
                    let element = args[0];
                    let is_zero_idx = idx_arg == zero
                        || matches!(
                            self.ctx.terms.get(idx_arg),
                            TermData::Const(Constant::Int(ref v)) if v.is_zero()
                        );
                    if is_zero_idx {
                        // Statically zero — unconditional axiom.
                        axioms.push(self.ctx.terms.mk_eq(nth_term, element));
                    } else {
                        // Symbolic index: create canonical nth(unit(x), 0) = x axiom
                        // and assert idx = 0 => nth_term = nth_at_zero (via implication).
                        let elem_sort = self.ctx.terms.sort(nth_term).clone();
                        let nth_at_zero = self.ctx.terms.mk_app(
                            Symbol::named("seq.nth"),
                            vec![seq_arg, zero],
                            elem_sort,
                        );
                        // Axiom: nth(unit(x), 0) = x
                        axioms.push(self.ctx.terms.mk_eq(nth_at_zero, element));
                        // Bridge: idx = 0 => nth_term = nth_at_zero
                        // (EUF congruence: if idx = 0, then nth(s, idx) = nth(s, 0))
                        let idx_eq_zero = self.ctx.terms.mk_eq(idx_arg, zero);
                        let nth_eq_canonical = self.ctx.terms.mk_eq(nth_term, nth_at_zero);
                        axioms.push(self.ctx.terms.mk_implies(idx_eq_zero, nth_eq_canonical));
                    }
                }
            }
        }

        axioms
    }
}
