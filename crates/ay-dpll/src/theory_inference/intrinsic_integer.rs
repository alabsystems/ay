// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked reconstruction of small integer clauses that reach SAT proof
//! replay without an inference record.

use ay_core::proof_validation::{
    farkas_conflict_lits_linear_holds_with_progress, lia_cut_chain_witness,
};
use ay_core::{
    term::Constant, AletheRule, FarkasAnnotation, Proof, ProofId, ProofStep, Sort, Symbol,
    TermData, TermId, TermStore, TheoryLemmaKind, TheoryLit,
};

const MAX_OCCURRENCES: usize = 192;
const MAX_DEPTH: usize = 24;
const MAX_LITERAL_BITS: u64 = 256;
const MAX_NAME_BYTES: usize = 256;
const MAX_ARGS: usize = 8;
const MAX_CLAUSE_LITERALS: usize = 8;
const MAX_SUBSET_EQUALITIES: usize = 4;
const ADMISSION_WORK: usize = MAX_OCCURRENCES * 2;
const ADMISSION_BYTES: usize = MAX_OCCURRENCES * std::mem::size_of::<(TermId, usize)>()
    + MAX_CLAUSE_LITERALS * std::mem::size_of::<TermId>();
const CUT_PLANNING_WORK: usize = 65_536;
const CUT_PLANNING_BYTES: usize = 262_144;
const EMISSION_BYTES: usize = 16_384;

pub(crate) struct IntrinsicIntegerClause {
    disjuncts: Vec<TermId>,
    packed: Option<TermId>,
    equality: Option<(TermId, [TermId; 2])>,
    /// Exact original literal positions of an independently checked pair.
    /// Remaining original literals are restored by explicit weakening.
    subset: Option<[usize; 2]>,
}

impl IntrinsicIntegerClause {
    /// Inspect only the immediate comparison shape. This prefilter does not
    /// expand the term DAG or allocate a copy of the proof.
    pub(crate) fn may_reconstruct(terms: &TermStore, clause: &[TermId]) -> bool {
        Self::clause_parts(terms, clause).is_some_and(|(disjuncts, _)| {
            if disjuncts.len() <= 4 {
                disjuncts
                    .iter()
                    .all(|&literal| Self::comparison(terms, literal).is_some())
            } else {
                disjuncts.iter().all(|&literal| {
                    terms.entry_stamp(literal).is_some() && terms.sort(literal) == &Sort::Bool
                }) && disjuncts
                    .iter()
                    .filter(|&&literal| {
                        matches!(Self::comparison(terms, literal), Some((_, _, "=", true)))
                    })
                    .take(MAX_SUBSET_EQUALITIES + 1)
                    .count()
                    >= 2
            }
        })
    }

    /// The clause's own literals, in recorded order. Two to four comparisons
    /// may be checked together; a wider bounded clause needs an independently
    /// valid two-equality subset and explicit Boolean weakening. A packed OR
    /// retains its exact original identity. The caller pays every attempted
    /// arithmetic walk and cut search, including declined candidates.
    pub(crate) fn admit(
        terms: &TermStore,
        clause: &[TermId],
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Option<Self> {
        let (disjuncts, packed) = Self::clause_parts(terms, clause)?;
        if disjuncts.len() > 4 {
            return Self::admit_equality_subset(terms, disjuncts, packed, progress);
        }
        let mut equality = None;
        let mut positive_bounds = 0;
        for (index, &literal) in disjuncts.iter().enumerate() {
            if disjuncts[..index].contains(&literal) {
                return None;
            }
            let (atom, operands, operator, negative) = Self::comparison(terms, literal)?;
            match (operator, negative) {
                ("=", false) if equality.is_none() => equality = Some((atom, operands)),
                ("=", true) => {}
                ("<=", false) => positive_bounds += 1,
                ("<=" | "<" | ">=" | ">", _) => {}
                _ => return None,
            }
        }
        if match equality {
            Some(_) => disjuncts.len() != 3 || positive_bounds != 2,
            // A bound-only clause can require integer rounding too:
            // `q <= p || p + 1 <= q`. The cut-chain validator reads the
            // falsity of every literal as an exact Int row; an equality
            // premise is not required for that argument.
            None => false,
        } || !progress(ADMISSION_WORK, ADMISSION_BYTES)
            || !admit_arithmetic_dag(terms, disjuncts)
        {
            return None;
        }
        Some(Self {
            disjuncts: disjuncts.to_vec(),
            packed,
            equality,
            subset: None,
        })
    }

    fn admit_equality_subset(
        terms: &TermStore,
        disjuncts: &[TermId],
        packed: Option<TermId>,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Option<Self> {
        if !progress(ADMISSION_WORK, ADMISSION_BYTES) {
            return None;
        }
        let mut positions = [0usize; MAX_SUBSET_EQUALITIES];
        let mut count = 0;
        for (index, &literal) in disjuncts.iter().enumerate() {
            if terms.entry_stamp(literal).is_none()
                || terms.sort(literal) != &Sort::Bool
                || disjuncts[..index].contains(&literal)
            {
                return None;
            }
            if matches!(Self::comparison(terms, literal), Some((_, _, "=", true))) {
                *positions.get_mut(count)? = index;
                count += 1;
            }
        }
        // At most six exact pairs. Each attempt pays the SAME caller owner
        // before walking/copying; failed pairs cannot reset its allowance.
        for left in 0..count {
            for right in left + 1..count {
                let indices = [positions[left], positions[right]];
                let selected = [disjuncts[indices[0]], disjuncts[indices[1]]];
                if !progress(ADMISSION_WORK, ADMISSION_BYTES) {
                    return None;
                }
                if !admit_arithmetic_dag(terms, &selected) {
                    continue;
                }
                if !progress(CUT_PLANNING_WORK, CUT_PLANNING_BYTES) {
                    return None;
                }
                if lia_cut_chain_witness(terms, &selected).is_some() && progress(0, 0) {
                    return Some(Self {
                        disjuncts: disjuncts.to_vec(),
                        packed,
                        equality: None,
                        subset: Some(indices),
                    });
                }
            }
        }
        None
    }

    fn clause_parts<'a>(
        terms: &'a TermStore,
        clause: &'a [TermId],
    ) -> Option<(&'a [TermId], Option<TermId>)> {
        let (disjuncts, packed) = match clause {
            [unit] if terms.entry_stamp(*unit).is_some() => {
                let TermData::App(Symbol::Named(name), children) = terms.get(*unit) else {
                    return None;
                };
                if name != "or" || terms.sort(*unit) != &Sort::Bool {
                    return None;
                }
                (children.as_slice(), Some(*unit))
            }
            _ => (clause, None),
        };
        (2..=MAX_CLAUSE_LITERALS)
            .contains(&disjuncts.len())
            .then_some((disjuncts, packed))
    }

    fn comparison(terms: &TermStore, literal: TermId) -> Option<(TermId, [TermId; 2], &str, bool)> {
        if terms.entry_stamp(literal).is_none() || terms.sort(literal) != &Sort::Bool {
            return None;
        }
        let (atom, negative) = match terms.get(literal) {
            TermData::Not(inner) => (*inner, true),
            _ => (literal, false),
        };
        if terms.entry_stamp(atom).is_none() || terms.sort(atom) != &Sort::Bool {
            return None;
        }
        let TermData::App(Symbol::Named(operator), operands) = terms.get(atom) else {
            return None;
        };
        let &[left, right] = operands.as_slice() else {
            return None;
        };
        if !matches!(operator.as_str(), "=" | "<=" | "<" | ">=" | ">")
            || [left, right].into_iter().any(|operand| {
                terms.entry_stamp(operand).is_none() || terms.sort(operand) != &Sort::Int
            })
        {
            return None;
        }
        Some((atom, [left, right], operator.as_str(), negative))
    }

    /// Append only an independently validated derivation of these literals.
    /// Theory facts are premiseless; the other steps are checked Boolean
    /// weakening, reordering, and resolutions over those exact facts.
    pub(crate) fn emit(
        &self,
        terms: &mut TermStore,
        proof: &mut Proof,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Option<ProofId> {
        if !progress(16, EMISSION_BYTES) {
            return None;
        }
        let last =
            match self.equality {
                Some((equality, [left, right])) => {
                    self.emit_trichotomy(terms, proof, equality, left, right, progress)?
                }
                None => {
                    let selected;
                    let core = if let Some([left, right]) = self.subset {
                        if left >= right {
                            return None;
                        }
                        selected = [*self.disjuncts.get(left)?, *self.disjuncts.get(right)?];
                        selected.as_slice()
                    } else {
                        self.disjuncts.as_slice()
                    };
                    // The cut proposer is deliberately incomplete for pure
                    // inequality sums. Try an exact unit-weight Farkas proof
                    // first, including the existing checked strengthening of
                    // strict Int rows. No normalized row becomes a premise:
                    // the annotation is validated against these original
                    // physical literals and printed as the same theorem.
                    let ones = [1; MAX_CLAUSE_LITERALS];
                    let coefficients = FarkasAnnotation::from_ints(&ones[..core.len()]);
                    let conflict: Vec<_> = core
                        .iter()
                        .map(|&literal| TheoryLit::new(literal, false))
                        .collect();
                    let unit_farkas = farkas_conflict_lits_linear_holds_with_progress(
                        terms,
                        &conflict,
                        &coefficients,
                        progress,
                    )
                    .ok()?;
                    if !unit_farkas {
                        // The independently metered Farkas check above does
                        // not run the cut search. Charge its existing full
                        // bound only on the branch that actually invokes it.
                        if !progress(CUT_PLANNING_WORK, CUT_PLANNING_BYTES) {
                            return None;
                        }
                        lia_cut_chain_witness(terms, core)?;
                    }
                    // Zero cuts is the exact rational-conflict special case of
                    // the same checked certificate, with a final combination.
                    if !progress(0, 0) {
                        return None;
                    }
                    let unit = proof.add_step(ProofStep::TheoryLemma {
                        theory: "LIA".to_owned(),
                        clause: core.to_vec(),
                        kind: if unit_farkas {
                            TheoryLemmaKind::LraFarkas
                        } else {
                            TheoryLemmaKind::IntCgCutChain
                        },
                        farkas: unit_farkas.then_some(coefficients),
                        lia: None,
                    });
                    if let Some([left, right]) = self.subset {
                        let mut weakened = core.to_vec();
                        weakened.extend(self.disjuncts.iter().enumerate().filter_map(
                            |(i, &literal)| (i != left && i != right).then_some(literal),
                        ));
                        let unit = proof.add_rule_step(
                            AletheRule::Weakening,
                            weakened.clone(),
                            vec![unit],
                            vec![],
                        );
                        if weakened == self.disjuncts {
                            unit
                        } else {
                            proof.add_rule_step(
                                AletheRule::Reordering,
                                self.disjuncts.clone(),
                                vec![unit],
                                vec![],
                            )
                        }
                    } else {
                        unit
                    }
                }
            };
        Some(match self.packed {
            Some(packed) => self.repack(terms, proof, last, packed),
            None => last,
        })
    }

    fn emit_trichotomy(
        &self,
        terms: &mut TermStore,
        proof: &mut Proof,
        equality: TermId,
        left: TermId,
        right: TermId,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Option<ProofId> {
        let mut strong = self
            .disjuncts
            .iter()
            .copied()
            .filter(|&term| term != equality);
        let [a, b] = [strong.next()?, strong.next()?];
        let le = terms.mk_app(Symbol::named("<="), [left, right], Sort::Bool);
        let ge = terms.mk_app(Symbol::named("<="), [right, left], Sort::Bool);
        let coefficients = FarkasAnnotation::from_ints(&[1, 1]);
        let mut checked = |strong, original| {
            farkas_conflict_lits_linear_holds_with_progress(
                terms,
                &[
                    TheoryLit::new(strong, false),
                    TheoryLit::new(original, false),
                ],
                &coefficients,
                progress,
            )
            .is_ok_and(|holds| holds)
        };
        let (from_le, from_ge) = if checked(a, le) && checked(b, ge) {
            (a, b)
        } else if checked(b, le) && checked(a, ge) {
            (b, a)
        } else {
            return None;
        };
        let not_le = terms.mk_not_raw(le);
        let not_ge = terms.mk_not_raw(ge);
        let split = vec![equality, not_le, not_ge];
        let packed = terms.mk_app(Symbol::named("or"), split.clone(), Sort::Bool);
        let lemma = proof.add_rule_step(AletheRule::LaDisequality, vec![packed], vec![], vec![]);
        let split = proof.add_rule_step(AletheRule::Or, split, vec![lemma], vec![]);
        let bridge = |proof: &mut Proof, target, original| {
            proof.add_step(ProofStep::TheoryLemma {
                theory: "LIA".to_owned(),
                clause: vec![target, original],
                kind: TheoryLemmaKind::LraFarkas,
                farkas: Some(coefficients.clone()),
                lia: None,
            })
        };
        let lower = bridge(proof, from_le, le);
        let first = proof.add_resolution(vec![equality, not_ge, from_le], le, split, lower);
        let upper = bridge(proof, from_ge, ge);
        let strengthened = vec![equality, from_le, from_ge];
        let last = proof.add_resolution(strengthened.clone(), ge, first, upper);
        Some(if strengthened == self.disjuncts {
            last
        } else {
            proof.add_rule_step(
                AletheRule::Reordering,
                self.disjuncts.clone(),
                vec![last],
                vec![],
            )
        })
    }

    fn repack(
        &self,
        terms: &mut TermStore,
        proof: &mut Proof,
        mut last: ProofId,
        packed: TermId,
    ) -> ProofId {
        for (index, &disjunct) in self.disjuncts.iter().enumerate() {
            let complement = match terms.get(disjunct) {
                TermData::Not(inner) => *inner,
                _ => terms.mk_not_raw(disjunct),
            };
            let remove =
                proof.add_rule_step(AletheRule::OrNeg, vec![packed, complement], vec![], vec![]);
            let mut remaining = self.disjuncts[index + 1..].to_vec();
            remaining.push(packed);
            last = proof.add_rule_step(
                AletheRule::ThResolution,
                remaining,
                vec![last, remove],
                vec![],
            );
        }
        last
    }
}

fn admit_arithmetic_dag(terms: &TermStore, roots: &[TermId]) -> bool {
    let mut pending = Vec::with_capacity(MAX_OCCURRENCES);
    pending.extend(roots.iter().map(|&root| (root, 0)));
    let mut visited = 0usize;
    let mut literal_bits = 0u64;
    while let Some((term, depth)) = pending.pop() {
        visited += 1;
        if depth > MAX_DEPTH
            || terms.entry_stamp(term).is_none()
            || !matches!(terms.sort(term), Sort::Bool | Sort::Int)
        {
            return false;
        }
        match terms.get(term) {
            TermData::Var(name, _) if name.len() <= MAX_NAME_BYTES => {}
            TermData::Const(Constant::Int(value)) => {
                literal_bits = literal_bits.saturating_add(value.bits());
                if literal_bits > MAX_LITERAL_BITS {
                    return false;
                }
            }
            TermData::Not(inner) if visited + pending.len() < MAX_OCCURRENCES => {
                pending.push((*inner, depth + 1));
            }
            TermData::App(Symbol::Named(name), args)
                if name.len() <= MAX_NAME_BYTES
                    && args.len() <= MAX_ARGS
                    && visited + pending.len() + args.len() <= MAX_OCCURRENCES =>
            {
                pending.extend(args.iter().map(|&arg| (arg, depth + 1)));
            }
            _ => return false,
        }
    }
    true
}
