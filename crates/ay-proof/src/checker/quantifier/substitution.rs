// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact simultaneous substitution, retaining nested-binder masking.

use super::progress::QuantifierMeter;
use super::*;

type MatchFrame = (TermId, TermId, HashSet<String>);

struct SubstitutionMatcher<'a, 's, 'm, 'w, 'p> {
    terms: &'a TermStore,
    substitutions: &'s HashMap<&'a str, TermId>,
    matched_var_ids: HashMap<String, u32>,
    meter: &'m mut QuantifierMeter<'w, 'p>,
    stack: Vec<MatchFrame>,
}

impl SubstitutionMatcher<'_, '_, '_, '_, '_> {
    fn push_copy(
        &mut self,
        left: TermId,
        right: TermId,
        blocked: &HashSet<String>,
    ) -> Result<(), ProofCheckError> {
        self.meter.queue_room(&self.stack)?;
        let names = self.meter.clone_names(blocked)?;
        self.meter.push(&mut self.stack, (left, right, names))
    }

    fn run(&mut self, pattern: TermId, instance: TermId) -> Result<bool, ProofCheckError> {
        self.meter
            .push(&mut self.stack, (pattern, instance, HashSet::default()))?;
        while let Some((expected, actual, blocked)) = self.stack.pop() {
            if !self.match_node(expected, actual, blocked)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn match_node(
        &mut self,
        expected: TermId,
        actual: TermId,
        blocked: HashSet<String>,
    ) -> Result<bool, ProofCheckError> {
        self.meter.visit()?;
        let expected_sort = self.meter.sort(self.terms, expected)?;
        let actual_sort = self.meter.sort(self.terms, actual)?;
        if !self.meter.sort_equal(expected_sort, actual_sort)? {
            return Ok(false);
        }
        match self.meter.term(self.terms, expected)? {
            TermData::Var(name, id) => self.match_variable(name, *id, expected, actual, &blocked),
            TermData::Const(..) => Ok(expected == actual),
            TermData::Not(inner) => {
                let TermData::Not(actual_inner) = self.meter.term(self.terms, actual)? else {
                    return Ok(false);
                };
                self.meter
                    .push(&mut self.stack, (*inner, *actual_inner, blocked))?;
                Ok(true)
            }
            TermData::Ite(c, t, e) => {
                let TermData::Ite(ac, at, ae) = self.meter.term(self.terms, actual)? else {
                    return Ok(false);
                };
                self.push_copy(*c, *ac, &blocked)?;
                self.push_copy(*t, *at, &blocked)?;
                self.meter.push(&mut self.stack, (*e, *ae, blocked))?;
                Ok(true)
            }
            TermData::App(symbol, args) => self.match_app(symbol, args, actual, blocked),
            TermData::Forall(bindings, body, triggers)
            | TermData::Exists(bindings, body, triggers) => {
                self.match_quantifier(expected, actual, bindings, *body, triggers, blocked)
            }
            TermData::Let(..) => Ok(false),
            _ => Ok(false),
        }
    }

    fn match_variable(
        &mut self,
        name: &str,
        id: u32,
        expected: TermId,
        actual: TermId,
        blocked: &HashSet<String>,
    ) -> Result<bool, ProofCheckError> {
        self.meter.lookup(name, blocked.len())?;
        if blocked.contains(name) {
            return Ok(expected == actual);
        }
        self.meter.lookup(name, self.substitutions.len())?;
        let Some(&replacement) = self.substitutions.get(name) else {
            return Ok(expected == actual);
        };
        self.meter.lookup(name, self.matched_var_ids.len())?;
        match self.matched_var_ids.get(name) {
            Some(&seen) if seen != id => return Ok(false),
            Some(_) => {}
            None => {
                self.meter.name_map_entry(&self.matched_var_ids, name)?;
                self.meter.owned_name(name)?;
                self.matched_var_ids.insert(name.to_string(), id);
            }
        }
        Ok(actual == replacement)
    }

    fn match_app(
        &mut self,
        symbol: &Symbol,
        args: &[TermId],
        actual: TermId,
        blocked: HashSet<String>,
    ) -> Result<bool, ProofCheckError> {
        let TermData::App(actual_symbol, actual_args) = self.meter.term(self.terms, actual)? else {
            return Ok(false);
        };
        if !self.meter.symbol_equal(symbol, actual_symbol)? || args.len() != actual_args.len() {
            return Ok(false);
        }
        for (&left, &right) in args.iter().zip(actual_args) {
            self.push_copy(left, right, &blocked)?;
        }
        Ok(true)
    }

    fn match_quantifier(
        &mut self,
        expected: TermId,
        actual: TermId,
        bindings: &[(String, Sort)],
        body: TermId,
        triggers: &[Vec<TermId>],
        mut blocked: HashSet<String>,
    ) -> Result<bool, ProofCheckError> {
        let expected_data = self.meter.term(self.terms, expected)?;
        let actual_data = self.meter.term(self.terms, actual)?;
        let same_polarity = matches!(
            (expected_data, actual_data),
            (TermData::Forall(..), TermData::Forall(..))
                | (TermData::Exists(..), TermData::Exists(..))
        );
        let (actual_bindings, actual_body, actual_triggers) = match actual_data {
            TermData::Forall(bindings, body, triggers)
            | TermData::Exists(bindings, body, triggers) => (bindings, body, triggers),
            _ => return Ok(false),
        };
        if !same_polarity
            || bindings.len() != actual_bindings.len()
            || triggers.len() != actual_triggers.len()
        {
            return Ok(false);
        }
        for ((name, sort), (actual_name, actual_sort)) in bindings.iter().zip(actual_bindings) {
            self.meter.name(name)?;
            self.meter.name(actual_name)?;
            if name != actual_name || !self.meter.sort_equal(sort, actual_sort)? {
                return Ok(false);
            }
        }
        for (left, right) in triggers.iter().zip(actual_triggers) {
            self.meter.charge(1, 0)?;
            if left.len() != right.len() {
                return Ok(false);
            }
        }
        for (name, _) in bindings {
            self.meter.insert_name(&mut blocked, name)?;
        }
        self.push_copy(body, *actual_body, &blocked)?;
        for (left, right) in triggers.iter().zip(actual_triggers) {
            self.meter.charge(1, 0)?;
            for (&left, &right) in left.iter().zip(right) {
                self.push_copy(left, right, &blocked)?;
            }
        }
        Ok(true)
    }
}

pub(super) fn matches_substitution<'a>(
    terms: &'a TermStore,
    pattern: TermId,
    instance: TermId,
    substitutions: &HashMap<&'a str, TermId>,
    meter: &mut QuantifierMeter<'_, '_>,
) -> Result<bool, ProofCheckError> {
    SubstitutionMatcher {
        terms,
        substitutions,
        matched_var_ids: HashMap::default(),
        meter,
        stack: Vec::new(),
    }
    .run(pattern, instance)
}

pub(super) fn matches_single_substitution(
    terms: &TermStore,
    pattern: TermId,
    instance: TermId,
    binder: &str,
    witness: TermId,
    meter: &mut QuantifierMeter<'_, '_>,
) -> Result<bool, ProofCheckError> {
    let mut substitutions = HashMap::default();
    meter.name_map_entry(&substitutions, binder)?;
    substitutions.insert(binder, witness);
    matches_substitution(terms, pattern, instance, &substitutions, meter)
}
