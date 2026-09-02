// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Interval evaluation, unit propagation, and bound tightening.

impl QueryChecker<'_> {
    // -----------------------------------------------------------------------
    // Interval evaluation
    // -----------------------------------------------------------------------

    /// The interval an atom's SHAPE entails, independently of any assertion.
    fn shape_interval(
        &mut self,
        atom: LinearAtom,
    ) -> Result<Interval, BvLiaUnsatAuthenticationError> {
        self.meter.charge(1)?;
        let terms = self.terms;
        if let LinearAtom::UnsignedBv(term) = atom {
            let Sort::BitVec(width) = terms.sort(term) else {
                return Ok(Interval::default());
            };
            let width = width.width;
            if width == 0 || width > 64 {
                return Ok(Interval::default());
            }
            self.meter.charge(u64::from(width).div_ceil(64).max(1))?;
            return Ok(Interval {
                lower: Some(BigInt::zero()),
                upper: Some((BigInt::one() << width) - BigInt::one()),
            });
        }
        let LinearAtom::Int(term) = atom else {
            return Ok(Interval::default());
        };
        // Every shape bound below is a theorem about an Int-sorted application.
        // `validate_fragment_sorting` has already rejected ill-sorted nodes;
        // re-checking here keeps the theorem local to this function.
        if terms.sort(term) != &Sort::Int {
            return Ok(Interval::default());
        }
        let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
            return Ok(Interval::default());
        };
        match (name.as_str(), args.len()) {
            // SMT-LIB defines `bv2nat` as the unsigned value of its operand.
            ("bv2nat", 1) => {
                let Sort::BitVec(width) = terms.sort(args[0]) else {
                    return Ok(Interval::default());
                };
                let width = width.width;
                if width == 0 || u64::from(width) > MAX_INTEGER_BITS {
                    return Ok(Interval::default());
                }
                self.meter.charge(u64::from(width).div_ceil(64).max(1))?;
                Ok(Interval {
                    lower: Some(BigInt::zero()),
                    upper: Some((BigInt::one() << width) - BigInt::one()),
                })
            }
            // `a mod d` for a positive integer literal `d` lies in `[0, d-1]`.
            ("mod", 2) => {
                let TermData::Const(Constant::Int(divisor)) = terms.get(args[1]) else {
                    return Ok(Interval::default());
                };
                if !divisor.is_positive() {
                    return Ok(Interval::default());
                }
                let divisor = divisor.clone();
                let Some(upper) = self.bounded_add(&divisor, &-BigInt::one())? else {
                    return Ok(Interval::default());
                };
                Ok(Interval {
                    lower: Some(BigInt::zero()),
                    upper: Some(upper),
                })
            }
            ("abs", 1) => Ok(Interval {
                lower: Some(BigInt::zero()),
                upper: None,
            }),
            _ => Ok(Interval::default()),
        }
    }

    /// The interval of a linear form under the current bounds, together with
    /// the per-atom minimum contributions used for bound tightening.
    fn form_interval(
        &mut self,
        form: &LinearForm,
        state: &IntervalState,
    ) -> Result<FormInterval, BvLiaUnsatAuthenticationError> {
        let mut minimum = Some(form.constant.clone());
        let mut maximum = Some(form.constant.clone());
        let mut contributions = Vec::new();
        self.meter
            .charge(u64::try_from(form.atoms.len()).unwrap_or(u64::MAX).max(1))?;
        for (&atom, coefficient) in &form.atoms {
            let interval = state.interval(atom);
            let positive = coefficient.is_positive();
            let low_bound = if positive {
                interval.lower.as_ref()
            } else {
                interval.upper.as_ref()
            };
            let high_bound = if positive {
                interval.upper.as_ref()
            } else {
                interval.lower.as_ref()
            };
            let low = match low_bound {
                Some(bound) => self.bounded_multiply(coefficient, bound)?,
                None => None,
            };
            let high = match high_bound {
                Some(bound) => self.bounded_multiply(coefficient, bound)?,
                None => None,
            };
            minimum = match (minimum, &low) {
                (Some(accumulated), Some(value)) => self.bounded_add(&accumulated, value)?,
                _ => None,
            };
            maximum = match (maximum, &high) {
                (Some(accumulated), Some(value)) => self.bounded_add(&accumulated, value)?,
                _ => None,
            };
            contributions.push((atom, coefficient.clone(), low));
        }
        Ok(FormInterval {
            minimum,
            maximum,
            contributions,
        })
    }

    /// Whether a clause literal is entailed true or false by the current
    /// bounds. `None` means undecided.
    fn literal_truth(
        &mut self,
        literal: &ClauseLiteral,
        state: &IntervalState,
    ) -> Result<Option<bool>, BvLiaUnsatAuthenticationError> {
        self.meter.charge(1)?;
        match literal {
            ClauseLiteral::Opaque { term, polarity } => {
                Ok(state.booleans.get(term).map(|value| value == polarity))
            }
            ClauseLiteral::Arithmetic { form, relation } => {
                let interval = self.form_interval(form, state)?;
                let zero = BigInt::zero();
                let below = interval
                    .maximum
                    .as_ref()
                    .is_some_and(|maximum| maximum < &zero);
                let above = interval
                    .minimum
                    .as_ref()
                    .is_some_and(|minimum| minimum > &zero);
                let at_most_zero = interval
                    .maximum
                    .as_ref()
                    .is_some_and(|maximum| maximum <= &zero);
                let exactly_zero = interval
                    .minimum
                    .as_ref()
                    .zip(interval.maximum.as_ref())
                    .is_some_and(|(minimum, maximum)| minimum.is_zero() && maximum.is_zero());
                Ok(match relation {
                    Relation::LessOrEqual => {
                        if at_most_zero {
                            Some(true)
                        } else if above {
                            Some(false)
                        } else {
                            None
                        }
                    }
                    Relation::Equal => {
                        if exactly_zero {
                            Some(true)
                        } else if above || below {
                            Some(false)
                        } else {
                            None
                        }
                    }
                    Relation::Distinct => {
                        if above || below {
                            Some(true)
                        } else if exactly_zero {
                            Some(false)
                        } else {
                            None
                        }
                    }
                })
            }
        }
    }

    /// Assume an entailed literal, narrowing the bounds it justifies.
    fn assume_literal(
        &mut self,
        literal: &ClauseLiteral,
        state: &mut IntervalState,
    ) -> Result<AssumeOutcome, BvLiaUnsatAuthenticationError> {
        self.meter.charge(1)?;
        match literal {
            ClauseLiteral::Opaque { term, polarity } => match state.booleans.get(term) {
                Some(existing) if existing != polarity => Ok(AssumeOutcome::Conflict),
                Some(_) => Ok(AssumeOutcome::Stable),
                None => {
                    if state.booleans.len() >= MAX_CLAUSES {
                        return Ok(AssumeOutcome::Decline);
                    }
                    state.booleans.insert(*term, *polarity);
                    Ok(AssumeOutcome::Changed)
                }
            },
            ClauseLiteral::Arithmetic { form, relation } => match relation {
                Relation::LessOrEqual => self.assume_at_most_zero(form, state),
                Relation::Equal => {
                    let first = self.assume_at_most_zero(form, state)?;
                    if matches!(first, AssumeOutcome::Conflict | AssumeOutcome::Decline) {
                        return Ok(first);
                    }
                    let Some(negated) =
                        self.combine_forms(&LinearForm::default(), form, &-BigInt::one())?
                    else {
                        return Ok(first);
                    };
                    let second = self.assume_at_most_zero(&negated, state)?;
                    Ok(match (first, second) {
                        (AssumeOutcome::Conflict, _) | (_, AssumeOutcome::Conflict) => {
                            AssumeOutcome::Conflict
                        }
                        (AssumeOutcome::Decline, _) | (_, AssumeOutcome::Decline) => {
                            AssumeOutcome::Decline
                        }
                        (AssumeOutcome::Changed, _) | (_, AssumeOutcome::Changed) => {
                            AssumeOutcome::Changed
                        }
                        _ => AssumeOutcome::Stable,
                    })
                }
                // A disequality constrains no interval endpoint on its own.
                Relation::Distinct => Ok(AssumeOutcome::Stable),
            },
        }
    }

    /// Interval-consistency tightening for the entailed constraint `form <= 0`.
    ///
    /// For each atom `j` with coefficient `c`,
    /// `c * a_j <= -constant - sum_{i != j} c_i * a_i`, so the right-hand side
    /// is maximised by the MINIMUM of the sibling contributions. Dividing by
    /// `c` gives a floor bound above (`c > 0`) or a ceiling bound below
    /// (`c < 0`); both are exact over the integers.
    ///
    /// The sibling minima come from one snapshot taken before any narrowing, so
    /// no bound derived here depends on another bound derived here.
    fn assume_at_most_zero(
        &mut self,
        form: &LinearForm,
        state: &mut IntervalState,
    ) -> Result<AssumeOutcome, BvLiaUnsatAuthenticationError> {
        let interval = self.form_interval(form, state)?;
        // The constraint itself is already violated by the entailed bounds.
        if interval
            .minimum
            .as_ref()
            .is_some_and(|minimum| minimum.is_positive())
        {
            return Ok(AssumeOutcome::Conflict);
        }
        let unbounded: Vec<LinearAtom> = interval
            .contributions
            .iter()
            .filter(|(_, _, low)| low.is_none())
            .map(|(atom, _, _)| *atom)
            .take(2)
            .collect();
        let mut outcome = AssumeOutcome::Stable;
        for (atom, coefficient, low) in &interval.contributions {
            self.meter.charge(1)?;
            let sibling_minimum = if unbounded.is_empty() {
                let (Some(total), Some(own)) = (interval.minimum.as_ref(), low.as_ref()) else {
                    continue;
                };
                match self.bounded_subtract(total, own)? {
                    Some(value) => value,
                    None => continue,
                }
            } else if unbounded.len() == 1 && unbounded[0] == *atom {
                // Every OTHER contribution is bounded, so the sibling minimum
                // is the constant plus those contributions.
                let mut accumulated = form.constant.clone();
                let mut usable = true;
                for (other, _, other_low) in &interval.contributions {
                    if other == atom {
                        continue;
                    }
                    let Some(value) = other_low else {
                        usable = false;
                        break;
                    };
                    match self.bounded_add(&accumulated, value)? {
                        Some(sum) => accumulated = sum,
                        None => {
                            usable = false;
                            break;
                        }
                    }
                }
                if !usable {
                    continue;
                }
                accumulated
            } else {
                continue;
            };
            let Some(limit) = self.bounded_subtract(&BigInt::zero(), &sibling_minimum)? else {
                continue;
            };
            // `sibling_minimum` already includes `form.constant`; the bound on
            // `c * a_j` is `-(sibling_minimum)`.
            let step = if coefficient.is_positive() {
                let bound = self.floor_divide(&limit, coefficient)?;
                self.tighten_upper(*atom, bound, state)?
            } else {
                let bound = self.ceiling_divide(&limit, coefficient)?;
                self.tighten_lower(*atom, bound, state)?
            };
            match step {
                AssumeOutcome::Conflict => return Ok(AssumeOutcome::Conflict),
                AssumeOutcome::Decline => return Ok(AssumeOutcome::Decline),
                AssumeOutcome::Changed => outcome = AssumeOutcome::Changed,
                AssumeOutcome::Stable => {}
            }
        }
        Ok(outcome)
    }

    fn tighten_upper(
        &mut self,
        atom: LinearAtom,
        bound: BigInt,
        state: &mut IntervalState,
    ) -> Result<AssumeOutcome, BvLiaUnsatAuthenticationError> {
        let existing = state.interval(atom);
        if let Some(current) = &existing.upper {
            self.charge_integer_comparison(current, &bound)?;
            if current <= &bound {
                return Ok(AssumeOutcome::Stable);
            }
        }
        if let Some(lower) = &existing.lower {
            self.charge_integer_comparison(lower, &bound)?;
            if lower > &bound {
                return Ok(AssumeOutcome::Conflict);
            }
        }
        let updated = Interval {
            lower: existing.lower.clone(),
            upper: Some(bound),
        };
        self.store_interval(atom, existing, updated, state)
    }

    fn tighten_lower(
        &mut self,
        atom: LinearAtom,
        bound: BigInt,
        state: &mut IntervalState,
    ) -> Result<AssumeOutcome, BvLiaUnsatAuthenticationError> {
        let existing = state.interval(atom);
        if let Some(current) = &existing.lower {
            self.charge_integer_comparison(current, &bound)?;
            if current >= &bound {
                return Ok(AssumeOutcome::Stable);
            }
        }
        if let Some(upper) = &existing.upper {
            self.charge_integer_comparison(upper, &bound)?;
            if upper < &bound {
                return Ok(AssumeOutcome::Conflict);
            }
        }
        let updated = Interval {
            lower: Some(bound),
            upper: existing.upper.clone(),
        };
        self.store_interval(atom, existing, updated, state)
    }

    fn store_interval(
        &mut self,
        atom: LinearAtom,
        existing: Interval,
        updated: Interval,
        state: &mut IntervalState,
    ) -> Result<AssumeOutcome, BvLiaUnsatAuthenticationError> {
        let limbs = updated.limbs();
        let retained = state
            .bound_limbs
            .saturating_sub(existing.limbs())
            .saturating_add(limbs);
        if retained > MAX_BOUND_LIMBS {
            return Ok(AssumeOutcome::Decline);
        }
        self.meter.charge(limbs.max(1))?;
        state.bound_limbs = retained;
        state.bounds.insert(atom, updated);
        Ok(AssumeOutcome::Changed)
    }
}
