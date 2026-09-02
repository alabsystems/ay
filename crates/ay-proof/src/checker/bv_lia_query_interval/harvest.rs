// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Clause harvesting and linear normalization for interval refutation.

impl QueryChecker<'_> {
    /// Refute the source conjunction by width-independent interval reasoning.
    ///
    /// Returns `true` only when a clause has been shown to have every literal
    /// false, or an atom's entailed interval is empty. Any unrecognised shape,
    /// any exhausted budget, and any inconclusive fixpoint return `false`, so
    /// the caller's enumerating lanes run exactly as before.
    pub(super) fn has_interval_contradiction(
        &mut self,
        assertions: &[TermId],
    ) -> Result<bool, BvLiaUnsatAuthenticationError> {
        // This lane runs BEFORE the finite enumerator, so it must not be able
        // to spend the budget the enumerator needs. Exceeding its own share
        // declines rather than erroring: an additional lane that cannot answer
        // must leave the query exactly as it found it.
        let entry_work = self.meter.work;
        let mut nodes = MAX_FORM_NODES;
        let mut clauses: Vec<Vec<ClauseLiteral>> = Vec::new();
        for &assertion in assertions {
            self.meter.charge(1)?;
            if clauses.len() >= MAX_CLAUSES {
                return Ok(false);
            }
            // A truncated harvest read the source as something the source does
            // not say (see `Harvest`), so nothing derived from it may be used.
            // Decline the whole query rather than propagate a shrunken clause.
            if self
                .collect_clauses(assertion, true, 0, &mut nodes, &mut clauses)?
                .is_truncated()
            {
                return Ok(false);
            }
        }

        // Add only independently checked universal source-semantics clauses.
        // They are derived after the authored harvest is known complete, so a
        // source disjunct abandoned under a budget can never be hidden by a
        // generated bridge fact.
        if !self.append_int2bv_no_wrap_clauses(&mut clauses, &mut nodes, entry_work)? {
            return Ok(false);
        }

        let Some(mut state) = self.initial_interval_state(&clauses)? else {
            return Ok(false);
        };

        for _ in 0..MAX_INTERVAL_ROUNDS {
            let mut changed = false;
            for clause in &clauses {
                self.meter.charge(1)?;
                if self.meter.work.saturating_sub(entry_work) > MAX_INTERVAL_WORK {
                    return Ok(false);
                }
                let mut unknown: Option<&ClauseLiteral> = None;
                let mut unknown_count = 0usize;
                let mut satisfied = false;
                for literal in clause {
                    match self.literal_truth(literal, &state)? {
                        Some(true) => {
                            satisfied = true;
                            break;
                        }
                        Some(false) => {}
                        None => {
                            unknown_count += 1;
                            unknown = Some(literal);
                        }
                    }
                }
                if satisfied {
                    continue;
                }
                // Every literal refuted: the authored clause is false.
                if unknown_count == 0 {
                    return Ok(true);
                }
                if unknown_count != 1 {
                    continue;
                }
                let Some(literal) = unknown else {
                    // The count and witness are maintained together, but this
                    // lane is only an additional authenticator: any internal
                    // inconsistency must decline rather than manufacture UNSAT.
                    return Ok(false);
                };
                match self.assume_literal(literal, &mut state)? {
                    AssumeOutcome::Conflict => return Ok(true),
                    AssumeOutcome::Changed => changed = true,
                    AssumeOutcome::Stable => {}
                    AssumeOutcome::Decline => return Ok(false),
                }
            }
            if !changed {
                break;
            }
        }
        Ok(false)
    }

    /// Seed every arithmetic atom with the bounds guaranteed by its shape.
    fn initial_interval_state(
        &mut self,
        clauses: &[Vec<ClauseLiteral>],
    ) -> Result<Option<IntervalState>, BvLiaUnsatAuthenticationError> {
        let mut state = IntervalState::default();
        for clause in clauses {
            for literal in clause {
                let ClauseLiteral::Arithmetic { form, .. } = literal else {
                    continue;
                };
                for &atom in form.atoms.keys() {
                    if state.bounds.contains_key(&atom) {
                        continue;
                    }
                    let interval = self.shape_interval(atom)?;
                    let limbs = interval.limbs();
                    if state.bound_limbs.saturating_add(limbs) > MAX_BOUND_LIMBS {
                        return Ok(None);
                    }
                    state.bound_limbs += limbs;
                    self.meter.charge(limbs.max(1))?;
                    state.bounds.insert(atom, interval);
                }
            }
        }
        Ok(Some(state))
    }

    /// Append the universally valid guarded round-trip clause for every
    /// `int2bv` term whose unsigned view occurs in an interpreted literal.
    ///
    /// For `r = int2bv_w(e)` and `M = 2^w`, the clause is
    ///
    /// ```text
    /// e < 0  OR  e >= M  OR  unsigned(r) = e
    /// ```
    ///
    /// The equality is therefore used only on the exact no-wrap interval
    /// `[0, M)`. The term, width and source are all read back from the validated
    /// source store; no production bridge assertion carries authority here.
    fn append_int2bv_no_wrap_clauses(
        &mut self,
        clauses: &mut Vec<Vec<ClauseLiteral>>,
        nodes: &mut u64,
        entry_work: u64,
    ) -> Result<bool, BvLiaUnsatAuthenticationError> {
        let mut relevant = BTreeSet::new();
        for clause in clauses.iter() {
            for literal in clause {
                let ClauseLiteral::Arithmetic { form, .. } = literal else {
                    continue;
                };
                for &atom in form.atoms.keys() {
                    self.meter.charge(1)?;
                    if self.meter.work.saturating_sub(entry_work) > MAX_INTERVAL_WORK {
                        return Ok(false);
                    }
                    let LinearAtom::UnsignedBv(term) = atom else {
                        continue;
                    };
                    if self.int2bv_source(term).is_none() {
                        continue;
                    }
                    relevant.insert(term);
                    if relevant.len() > MAX_RESIDUE_SCHEMAS {
                        return Ok(false);
                    }
                }
            }
        }

        let Some(combined_clause_count) = clauses.len().checked_add(relevant.len()) else {
            return Ok(false);
        };
        if combined_clause_count > MAX_CLAUSES {
            return Ok(false);
        }
        clauses.try_reserve(relevant.len()).map_err(|_| {
            BvLiaUnsatAuthenticationError::ResourceLimit {
                resource: "interval residue clause allocation",
            }
        })?;

        let mut retained_atom_copies = 0usize;
        let mut retained_limb_units = 0u64;
        for bv in relevant {
            let Some((source, width)) = self.int2bv_source(bv) else {
                // The immutable term store was validated before this lane and
                // cannot change through this borrowed checker. If the two reads
                // disagree, decline rather than derive from an unstable shape.
                return Ok(false);
            };
            let Some(clause) = self.int2bv_no_wrap_clause(bv, source, width, nodes, entry_work)?
            else {
                // A three-disjunct theorem may only be appended atomically.
                // Dropping either guard would strengthen it and could forge a
                // contradiction on a wrapping source value.
                return Ok(false);
            };

            // Bound the retained generated formula independently of work. The
            // form combiner bounds one form, but without this aggregate cap a
            // query could retain thousands of maximally wide coefficient maps.
            let mut clause_atom_copies = 0usize;
            let mut clause_limb_units = 0u64;
            for literal in &clause {
                let ClauseLiteral::Arithmetic { form, .. } = literal else {
                    return Ok(false);
                };
                let Some(atoms) = clause_atom_copies.checked_add(form.atoms.len()) else {
                    return Ok(false);
                };
                clause_atom_copies = atoms;
                let Some(limbs) = clause_limb_units.checked_add(integer_limb_units(&form.constant))
                else {
                    return Ok(false);
                };
                clause_limb_units = limbs;
                for coefficient in form.atoms.values() {
                    let Some(limbs) =
                        clause_limb_units.checked_add(integer_limb_units(coefficient))
                    else {
                        return Ok(false);
                    };
                    clause_limb_units = limbs;
                }
            }
            self.meter.charge(
                u64::try_from(clause_atom_copies)
                    .unwrap_or(u64::MAX)
                    .saturating_add(clause_limb_units)
                    .max(1),
            )?;
            if self.meter.work.saturating_sub(entry_work) > MAX_INTERVAL_WORK {
                return Ok(false);
            }
            let Some(atom_copies) = retained_atom_copies.checked_add(clause_atom_copies) else {
                return Ok(false);
            };
            let Some(limb_units) = retained_limb_units.checked_add(clause_limb_units) else {
                return Ok(false);
            };
            if atom_copies > MAX_RESIDUE_ATOM_COPIES || limb_units > MAX_RESIDUE_LIMBS {
                return Ok(false);
            }
            retained_atom_copies = atom_copies;
            retained_limb_units = limb_units;
            clauses.push(clause);
        }
        Ok(true)
    }

    /// Re-read one well-sorted `int2bv` application's exact source and width.
    fn int2bv_source(&self, term: TermId) -> Option<(TermId, u32)> {
        let Sort::BitVec(result_width) = self.terms.sort(term) else {
            return None;
        };
        let TermData::App(Symbol::Indexed(name, indices), args) = self.terms.get(term) else {
            return None;
        };
        let ([width], [source]) = (indices.as_slice(), args.as_slice()) else {
            return None;
        };
        (name == "int2bv"
            && *width > 0
            && *width <= 64
            && result_width.width == *width
            && self.terms.sort(*source) == &Sort::Int)
            .then_some((*source, *width))
    }

    /// Build one complete guarded no-wrap theorem clause, or decline without
    /// returning any prefix when a form/magnitude budget prevents construction.
    fn int2bv_no_wrap_clause(
        &mut self,
        bv: TermId,
        source: TermId,
        width: u32,
        nodes: &mut u64,
        entry_work: u64,
    ) -> Result<Option<Vec<ClauseLiteral>>, BvLiaUnsatAuthenticationError> {
        self.meter.charge(1)?;
        if width == 0 || width > 64 || self.terms.sort(source) != &Sort::Int {
            return Ok(None);
        }

        let source_form = self.linear_form(source, 0, nodes)?;
        if self.meter.work.saturating_sub(entry_work) > MAX_INTERVAL_WORK {
            return Ok(None);
        }
        let one = LinearForm::constant(BigInt::one());
        let Some(negative) = self.combine_forms(&source_form, &one, &BigInt::one())? else {
            return Ok(None);
        };
        if self.meter.work.saturating_sub(entry_work) > MAX_INTERVAL_WORK {
            return Ok(None);
        }

        let modulus = BigInt::one() << width;
        self.meter.charge(integer_limb_units(&modulus).max(1))?;
        if self.meter.work.saturating_sub(entry_work) > MAX_INTERVAL_WORK {
            return Ok(None);
        }
        let modulus = LinearForm::constant(modulus);
        let Some(overflow) = self.combine_forms(&modulus, &source_form, &-BigInt::one())? else {
            return Ok(None);
        };
        if self.meter.work.saturating_sub(entry_work) > MAX_INTERVAL_WORK {
            return Ok(None);
        }

        let unsigned = LinearForm::unsigned_bv_atom(bv);
        let Some(round_trip) = self.combine_forms(&unsigned, &source_form, &-BigInt::one())? else {
            return Ok(None);
        };
        if self.meter.work.saturating_sub(entry_work) > MAX_INTERVAL_WORK {
            return Ok(None);
        }

        Ok(Some(vec![
            ClauseLiteral::Arithmetic {
                // `e < 0` iff `e + 1 <= 0` over the integers.
                form: negative,
                relation: Relation::LessOrEqual,
            },
            ClauseLiteral::Arithmetic {
                // `e >= 2^w` iff `2^w - e <= 0`.
                form: overflow,
                relation: Relation::LessOrEqual,
            },
            ClauseLiteral::Arithmetic {
                form: round_trip,
                relation: Relation::Equal,
            },
        ]))
    }

    // -----------------------------------------------------------------------
    // Source -> clauses
    // -----------------------------------------------------------------------

    /// Split an asserted formula into clauses by the polarity rewriting.
    ///
    /// Only the rewritings that preserve "asserted" are applied: the conjuncts
    /// of an asserted conjunction are asserted, and so are the negated
    /// disjuncts of a negated disjunction. Everything else becomes exactly one
    /// clause, whose literals are collected by [`Self::collect_literals`].
    ///
    /// Reports [`Harvest::Truncated`] when any budget stopped the walk with
    /// source structure unvisited; see [`Harvest`] for why that must decline.
    fn collect_clauses(
        &mut self,
        term: TermId,
        polarity: bool,
        depth: usize,
        nodes: &mut u64,
        out: &mut Vec<Vec<ClauseLiteral>>,
    ) -> Result<Harvest, BvLiaUnsatAuthenticationError> {
        self.meter.charge(1)?;
        if depth > MAX_TERM_DEPTH || out.len() >= MAX_CLAUSES {
            return Ok(Harvest::Truncated);
        }
        let terms = self.terms;
        if let Some(inner) = negation_body(self, term) {
            return self.collect_clauses(inner, !polarity, depth + 1, nodes, out);
        }
        if let TermData::App(Symbol::Named(name), args) = terms.get(term) {
            match (name.as_str(), polarity) {
                ("and", true) | ("or", false) => {
                    let args = args.clone();
                    for arg in args {
                        if self
                            .collect_clauses(arg, polarity, depth + 1, nodes, out)?
                            .is_truncated()
                        {
                            return Ok(Harvest::Truncated);
                        }
                    }
                    return Ok(Harvest::Complete);
                }
                // `not (a => b)` is `a and not b`.
                ("=>" | "implies", false) if args.len() == 2 => {
                    let (left, right) = (args[0], args[1]);
                    let left = self.collect_clauses(left, true, depth + 1, nodes, out)?;
                    let right = self.collect_clauses(right, false, depth + 1, nodes, out)?;
                    return Ok(left.and(right));
                }
                _ => {}
            }
        }
        let mut clause = Vec::new();
        let harvest = self.collect_literals(term, polarity, depth + 1, nodes, &mut clause)?;
        // A truncated clause is STRONGER than the authored one, so it must not
        // reach the propagator even alongside a decline: the caller returns
        // before reading `out`, and this keeps that independent of call order.
        if harvest.is_truncated() {
            return Ok(Harvest::Truncated);
        }
        if !clause.is_empty() {
            out.push(clause);
        }
        Ok(Harvest::Complete)
    }

    /// Collect the literals of one asserted clause, flattening the disjunctive
    /// structure that is still visible at this polarity.
    ///
    /// Every early return here abandons DISJUNCTS of the clause under
    /// construction, which strengthens it. Such a return therefore reports
    /// [`Harvest::Truncated`] instead of leaving a shrunken clause behind
    /// (see [`Harvest`]); a bigger budget would only move the threshold.
    fn collect_literals(
        &mut self,
        term: TermId,
        polarity: bool,
        depth: usize,
        nodes: &mut u64,
        out: &mut Vec<ClauseLiteral>,
    ) -> Result<Harvest, BvLiaUnsatAuthenticationError> {
        self.meter.charge(1)?;
        if depth > MAX_TERM_DEPTH || out.len() >= MAX_CLAUSE_LITERALS {
            return Ok(Harvest::Truncated);
        }
        if let Some(inner) = negation_body(self, term) {
            return self.collect_literals(inner, !polarity, depth + 1, nodes, out);
        }
        let terms = self.terms;
        if let TermData::App(Symbol::Named(name), args) = terms.get(term) {
            match (name.as_str(), polarity) {
                ("or", true) | ("and", false) => {
                    let args = args.clone();
                    for arg in args {
                        // Stop at the first truncation: the query already has
                        // to decline, and continuing would only spend meter
                        // budget the caller's other lanes still need.
                        if self
                            .collect_literals(arg, polarity, depth + 1, nodes, out)?
                            .is_truncated()
                        {
                            return Ok(Harvest::Truncated);
                        }
                    }
                    return Ok(Harvest::Complete);
                }
                // `a => b` is `not a or b`.
                ("=>" | "implies", true) if args.len() == 2 => {
                    let (left, right) = (args[0], args[1]);
                    let left = self.collect_literals(left, false, depth + 1, nodes, out)?;
                    let right = self.collect_literals(right, true, depth + 1, nodes, out)?;
                    return Ok(left.and(right));
                }
                _ => {}
            }
        }
        if let Some(literal) = self.arithmetic_literal(term, polarity, depth + 1, nodes)? {
            out.push(literal);
        } else {
            out.push(ClauseLiteral::Opaque { term, polarity });
        }
        Ok(Harvest::Complete)
    }

    /// Read an Int comparison or unsigned BV order literal as `form REL 0` at
    /// the given polarity. Anything else returns `None` and stays opaque.
    fn arithmetic_literal(
        &mut self,
        term: TermId,
        polarity: bool,
        depth: usize,
        nodes: &mut u64,
    ) -> Result<Option<ClauseLiteral>, BvLiaUnsatAuthenticationError> {
        let terms = self.terms;
        let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
            return Ok(None);
        };
        if args.len() != 2 {
            return Ok(None);
        }
        let (left, right) = (args[0], args[1]);
        // `(low, high, strict)` denotes `low <[=] high` at this polarity.
        let int_order = match (name.as_str(), polarity) {
            ("<=", true) => Some((left, right, false, Relation::LessOrEqual)),
            ("<=", false) => Some((right, left, true, Relation::LessOrEqual)),
            ("<", true) => Some((left, right, true, Relation::LessOrEqual)),
            ("<", false) => Some((right, left, false, Relation::LessOrEqual)),
            (">=", true) => Some((right, left, false, Relation::LessOrEqual)),
            (">=", false) => Some((left, right, true, Relation::LessOrEqual)),
            (">", true) => Some((right, left, true, Relation::LessOrEqual)),
            (">", false) => Some((left, right, false, Relation::LessOrEqual)),
            ("=", true) => Some((left, right, false, Relation::Equal)),
            ("=", false) => Some((left, right, false, Relation::Distinct)),
            _ => None,
        };
        if let Some((low, high, strict, relation)) = int_order {
            if terms.sort(low) != &Sort::Int || terms.sort(high) != &Sort::Int {
                return Ok(None);
            }
            let low_form = self.linear_form(low, depth, nodes)?;
            let high_form = self.linear_form(high, depth, nodes)?;
            return self.comparison_literal(low_form, high_form, strict, relation);
        }

        let unsigned_order = match (name.as_str(), polarity) {
            ("bvult", true) => Some((left, right, true)),
            ("bvult", false) => Some((right, left, false)),
            ("bvule", true) => Some((left, right, false)),
            ("bvule", false) => Some((right, left, true)),
            _ => None,
        };
        let Some((low, high, strict)) = unsigned_order else {
            return Ok(None);
        };
        let (Sort::BitVec(low_width), Sort::BitVec(high_width)) =
            (terms.sort(low), terms.sort(high))
        else {
            return Ok(None);
        };
        if low_width.width == 0 || low_width.width > 64 || low_width.width != high_width.width {
            return Ok(None);
        }
        let Some(low_form) = self.unsigned_bv_form(low)? else {
            return Ok(None);
        };
        let Some(high_form) = self.unsigned_bv_form(high)? else {
            return Ok(None);
        };
        self.comparison_literal(low_form, high_form, strict, Relation::LessOrEqual)
    }

    /// Construct `low <[=] high` as one arithmetic clause literal.
    fn comparison_literal(
        &mut self,
        low_form: LinearForm,
        high_form: LinearForm,
        strict: bool,
        relation: Relation,
    ) -> Result<Option<ClauseLiteral>, BvLiaUnsatAuthenticationError> {
        let Some(mut form) = self.combine_forms(&low_form, &high_form, &-BigInt::one())? else {
            return Ok(None);
        };
        if strict {
            let Some(constant) = self.bounded_add(&form.constant, &BigInt::one())? else {
                return Ok(None);
            };
            form.constant = constant;
        }
        Ok(Some(ClauseLiteral::Arithmetic { form, relation }))
    }

    /// The exact unsigned integer denotation of one validated BV term.
    fn unsigned_bv_form(
        &mut self,
        term: TermId,
    ) -> Result<Option<LinearForm>, BvLiaUnsatAuthenticationError> {
        let Sort::BitVec(sort_width) = self.terms.sort(term) else {
            return Ok(None);
        };
        let width = sort_width.width;
        if width == 0 || width > 64 {
            return Ok(None);
        }
        if let TermData::Const(Constant::BitVec {
            value,
            width: literal_width,
        }) = self.terms.get(term)
        {
            self.meter.charge(integer_limb_units(value).max(1))?;
            let modulus = BigInt::one() << width;
            if *literal_width != width || value.is_negative() || value >= &modulus {
                return Ok(None);
            }
            return Ok(Some(LinearForm::constant(value.clone())));
        }
        Ok(Some(LinearForm::unsigned_bv_atom(term)))
    }

    // -----------------------------------------------------------------------
    // Linear normalisation
    // -----------------------------------------------------------------------

    /// Normalise an Int-sorted term into a linear form. `+`, `-` and
    /// constant-scaled `*` are interpreted; every other node — and every node
    /// beyond a budget — becomes an opaque atom, so the result always denotes
    /// the same integer as the source term.
    fn linear_form(
        &mut self,
        term: TermId,
        depth: usize,
        nodes: &mut u64,
    ) -> Result<LinearForm, BvLiaUnsatAuthenticationError> {
        self.meter.charge(1)?;
        if depth > MAX_TERM_DEPTH || *nodes == 0 {
            return Ok(LinearForm::atom(term));
        }
        *nodes -= 1;
        let terms = self.terms;
        if terms.sort(term) != &Sort::Int {
            return Ok(LinearForm::atom(term));
        }
        if let TermData::Const(Constant::Int(value)) = terms.get(term) {
            let value = value.clone();
            self.meter.charge(integer_limb_units(&value))?;
            return Ok(LinearForm::constant(value));
        }
        let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
            return Ok(LinearForm::atom(term));
        };
        let args = args.clone();
        match name.as_str() {
            "bv2nat" if args.len() == 1 => Ok(self
                .unsigned_bv_form(args[0])?
                .unwrap_or_else(|| LinearForm::atom(term))),
            "+" => {
                let mut accumulated = LinearForm::default();
                for arg in args {
                    let addend = self.linear_form(arg, depth + 1, nodes)?;
                    let Some(combined) =
                        self.combine_forms(&accumulated, &addend, &BigInt::one())?
                    else {
                        return Ok(LinearForm::atom(term));
                    };
                    accumulated = combined;
                }
                Ok(accumulated)
            }
            "-" => {
                let Some((first, rest)) = args.split_first() else {
                    return Ok(LinearForm::atom(term));
                };
                let first = self.linear_form(*first, depth + 1, nodes)?;
                if rest.is_empty() {
                    // SMT-LIB unary minus.
                    let Some(negated) =
                        self.combine_forms(&LinearForm::default(), &first, &-BigInt::one())?
                    else {
                        return Ok(LinearForm::atom(term));
                    };
                    return Ok(negated);
                }
                let mut accumulated = first;
                for &arg in rest {
                    let subtrahend = self.linear_form(arg, depth + 1, nodes)?;
                    let Some(combined) =
                        self.combine_forms(&accumulated, &subtrahend, &-BigInt::one())?
                    else {
                        return Ok(LinearForm::atom(term));
                    };
                    accumulated = combined;
                }
                Ok(accumulated)
            }
            "*" => {
                let mut coefficient = BigInt::one();
                let mut symbolic: Option<LinearForm> = None;
                for arg in args {
                    let factor = self.linear_form(arg, depth + 1, nodes)?;
                    if factor.atoms.is_empty() {
                        let Some(product) =
                            self.bounded_multiply(&coefficient, &factor.constant)?
                        else {
                            return Ok(LinearForm::atom(term));
                        };
                        coefficient = product;
                    } else if symbolic.is_none() {
                        symbolic = Some(factor);
                    } else {
                        // Two symbolic factors: not linear.
                        return Ok(LinearForm::atom(term));
                    }
                }
                let Some(symbolic) = symbolic else {
                    return Ok(LinearForm::constant(coefficient));
                };
                let Some(scaled) =
                    self.combine_forms(&LinearForm::default(), &symbolic, &coefficient)?
                else {
                    return Ok(LinearForm::atom(term));
                };
                Ok(scaled)
            }
            _ => Ok(LinearForm::atom(term)),
        }
    }

    /// `left + factor * right`, or `None` when the result would exceed the
    /// bounded-integer or form-width envelope.
    fn combine_forms(
        &mut self,
        left: &LinearForm,
        right: &LinearForm,
        factor: &BigInt,
    ) -> Result<Option<LinearForm>, BvLiaUnsatAuthenticationError> {
        if left.atoms.len().saturating_add(right.atoms.len()) > MAX_FORM_ATOMS {
            self.meter.charge(1)?;
            return Ok(None);
        }
        let Some(scaled_constant) = self.bounded_multiply(&right.constant, factor)? else {
            return Ok(None);
        };
        let Some(constant) = self.bounded_add(&left.constant, &scaled_constant)? else {
            return Ok(None);
        };
        let mut atoms = left.atoms.clone();
        self.meter
            .charge(u64::try_from(atoms.len()).unwrap_or(u64::MAX).max(1))?;
        for (atom, coefficient) in &right.atoms {
            let Some(scaled) = self.bounded_multiply(coefficient, factor)? else {
                return Ok(None);
            };
            let entry = atoms.entry(*atom).or_insert_with(BigInt::zero);
            let Some(sum) = self.bounded_add(entry, &scaled)? else {
                return Ok(None);
            };
            *entry = sum;
        }
        atoms.retain(|_, coefficient| !coefficient.is_zero());
        Ok(Some(LinearForm { constant, atoms }))
    }
}
