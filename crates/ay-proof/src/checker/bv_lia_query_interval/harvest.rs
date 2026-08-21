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

    /// Read a comparison over Int operands as `form REL 0` at the given
    /// polarity. Anything else returns `None` and stays opaque.
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
        if terms.sort(left) != &Sort::Int || terms.sort(right) != &Sort::Int {
            return Ok(None);
        }
        // `(left, right, strict, is_equality)` for the literal at this
        // polarity, where a non-equality means `left - right (+1 if strict) <= 0`.
        let (low, high, strict, equality) = match (name.as_str(), polarity) {
            ("<=", true) => (left, right, false, false),
            ("<=", false) => (right, left, true, false),
            ("<", true) => (left, right, true, false),
            ("<", false) => (right, left, false, false),
            (">=", true) => (right, left, false, false),
            (">=", false) => (left, right, true, false),
            (">", true) => (right, left, true, false),
            (">", false) => (left, right, false, false),
            ("=", _) => (left, right, false, true),
            _ => return Ok(None),
        };
        let low_form = self.linear_form(low, depth, nodes)?;
        let high_form = self.linear_form(high, depth, nodes)?;
        let Some(mut form) = self.combine_forms(&low_form, &high_form, &-BigInt::one())? else {
            return Ok(None);
        };
        if strict {
            let Some(constant) = self.bounded_add(&form.constant, &BigInt::one())? else {
                return Ok(None);
            };
            form.constant = constant;
        }
        let relation = match (equality, polarity) {
            (false, _) => Relation::LessOrEqual,
            (true, true) => Relation::Equal,
            (true, false) => Relation::Distinct,
        };
        Ok(Some(ClauseLiteral::Arithmetic { form, relation }))
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
