// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Strict validation for datatype value-equality congruence biconditionals.

use ay_core::{ProofId, Symbol, TermData, TermId, TermStore};

use super::{
    constructor_head, equality_sides, flatten_clause_literals, sort_matches_datatype,
    tester_application, DatatypeDecls, ProofCheckError, SelectorDecls,
};

struct Validator<'terms, 'decls> {
    terms: &'terms TermStore,
    dt_decls: DatatypeDecls<'decls>,
    ctor_selectors: SelectorDecls<'decls>,
}

impl<'terms, 'decls> Validator<'terms, 'decls> {
    fn selector_list(&self, constructor: &str) -> Option<&'decls [String]> {
        self.ctor_selectors
            .iter()
            .find_map(|(name, selectors)| (name == constructor).then_some(selectors.as_slice()))
    }

    fn selector_app(&self, term: TermId, expected_subject: TermId) -> Option<String> {
        if let TermData::App(Symbol::Named(name), args) = self.terms.get(term) {
            if let [subject] = args.as_slice() {
                return (*subject == expected_subject).then(|| name.clone());
            }
        }
        None
    }

    fn conjuncts(&self, expansion: TermId) -> Vec<TermId> {
        match self.terms.get(expansion) {
            TermData::App(Symbol::Named(name), args) if name == "and" => args.clone(),
            _ => vec![expansion],
        }
    }

    fn accepts_orientation(&self, equality: TermId, expansion: TermId) -> bool {
        let Some((first, second)) = equality_sides(self.terms, equality) else {
            return false;
        };
        self.accepts_nullary_bridge(first, second, expansion)
            || self.accepts_constructor_expansion(first, second, expansion)
            || self.accepts_value_expansion(first, second, expansion)
    }

    fn accepts_nullary_bridge(&self, first: TermId, second: TermId, expansion: TermId) -> bool {
        let Some((tester_ctor, tester_subject)) = tester_application(self.terms, expansion) else {
            return false;
        };
        [(first, second), (second, first)]
            .into_iter()
            .any(|(subject, ctor_term)| {
                if subject != tester_subject {
                    return false;
                }
                let Some((ctor_name, datatype)) =
                    constructor_head(self.terms, self.dt_decls, ctor_term)
                else {
                    return false;
                };
                ctor_name == tester_ctor
                    && self
                        .selector_list(&ctor_name)
                        .is_some_and(<[String]>::is_empty)
                    && constructor_head(self.terms, self.dt_decls, subject).is_none()
                    && sort_matches_datatype(self.terms.sort(subject), datatype)
            })
    }

    fn accepts_constructor_expansion(
        &self,
        first: TermId,
        second: TermId,
        expansion: TermId,
    ) -> bool {
        [(first, second), (second, first)]
            .into_iter()
            .any(|(subject, ctor_term)| {
                self.accepts_constructor_candidate(subject, ctor_term, expansion)
            })
    }

    fn accepts_constructor_candidate(
        &self,
        subject: TermId,
        ctor_term: TermId,
        expansion: TermId,
    ) -> bool {
        let Some((ctor_name, datatype)) = constructor_head(self.terms, self.dt_decls, ctor_term)
        else {
            return false;
        };
        if constructor_head(self.terms, self.dt_decls, subject).is_some()
            || !sort_matches_datatype(self.terms.sort(subject), datatype)
        {
            return false;
        }
        let TermData::App(_, ctor_args) = self.terms.get(ctor_term) else {
            return false;
        };
        let Some(selectors) = self.selector_list(&ctor_name) else {
            return false;
        };
        if ctor_args.is_empty() || ctor_args.len() != selectors.len() {
            return false;
        }
        let mut tester_seen = false;
        let mut covered = vec![false; selectors.len()];
        for conjunct in self.conjuncts(expansion) {
            if !tester_seen
                && tester_application(self.terms, conjunct)
                    .is_some_and(|(ctor, tested)| ctor == ctor_name && tested == subject)
            {
                tester_seen = true;
                continue;
            }
            if !self.match_constructor_field(conjunct, subject, selectors, ctor_args, &mut covered)
            {
                return false;
            }
        }
        tester_seen && covered.into_iter().all(|field| field)
    }

    fn match_constructor_field(
        &self,
        conjunct: TermId,
        subject: TermId,
        selectors: &[String],
        ctor_args: &[TermId],
        covered: &mut [bool],
    ) -> bool {
        let Some((first, second)) = equality_sides(self.terms, conjunct) else {
            return false;
        };
        for (selector_side, argument_side) in [(first, second), (second, first)] {
            let Some(selector) = self.selector_app(selector_side, subject) else {
                continue;
            };
            let Some(index) = selectors.iter().position(|name| *name == selector) else {
                continue;
            };
            if !covered[index] && ctor_args[index] == argument_side {
                covered[index] = true;
                return true;
            }
        }
        false
    }

    fn accepts_value_expansion(&self, x: TermId, y: TermId, expansion: TermId) -> bool {
        if x == y {
            return false;
        }
        let Some((datatype, constructors)) = self
            .dt_decls
            .iter()
            .find(|(datatype, _)| sort_matches_datatype(self.terms.sort(x), datatype))
            .map(|(datatype, constructors)| (datatype.as_str(), constructors.as_slice()))
        else {
            return false;
        };
        if !sort_matches_datatype(self.terms.sort(y), datatype)
            || constructors.is_empty()
            || constructor_head(self.terms, self.dt_decls, x).is_some()
            || constructor_head(self.terms, self.dt_decls, y).is_some()
        {
            return false;
        }
        let conjuncts = self.conjuncts(expansion);
        match constructors {
            [constructor] => self.accepts_single_constructor(x, y, constructor, &conjuncts),
            _ => self.accepts_multiple_constructors(x, y, constructors, &conjuncts),
        }
    }

    fn match_field_equality(
        &self,
        conjunct: TermId,
        x: TermId,
        y: TermId,
        constructor: &str,
    ) -> Option<String> {
        let (first, second) = equality_sides(self.terms, conjunct)?;
        let selectors = self.selector_list(constructor)?;
        for (x_side, y_side) in [(first, second), (second, first)] {
            let (Some(x_selector), Some(y_selector)) =
                (self.selector_app(x_side, x), self.selector_app(y_side, y))
            else {
                continue;
            };
            if x_selector == y_selector && selectors.iter().any(|name| *name == x_selector) {
                return Some(x_selector);
            }
        }
        None
    }

    fn accepts_single_constructor(
        &self,
        x: TermId,
        y: TermId,
        constructor: &str,
        conjuncts: &[TermId],
    ) -> bool {
        let Some(selectors) = self.selector_list(constructor) else {
            return false;
        };
        if selectors.is_empty() {
            return false;
        }
        let mut covered: Vec<&String> = Vec::new();
        for &conjunct in conjuncts {
            let Some(selector) = self.match_field_equality(conjunct, x, y, constructor) else {
                return false;
            };
            if covered.iter().any(|covered| **covered == selector) {
                return false;
            }
            let Some(slot) = selectors.iter().find(|name| **name == selector) else {
                return false;
            };
            covered.push(slot);
        }
        covered.len() == selectors.len()
    }

    fn match_tester_agreement(
        &self,
        conjunct: TermId,
        x: TermId,
        y: TermId,
        constructors: &[String],
    ) -> Option<String> {
        let (first, second) = equality_sides(self.terms, conjunct)?;
        for (x_side, y_side) in [(first, second), (second, first)] {
            let (Some((x_ctor, x_subject)), Some((y_ctor, y_subject))) = (
                tester_application(self.terms, x_side),
                tester_application(self.terms, y_side),
            ) else {
                continue;
            };
            if x_ctor == y_ctor
                && x_subject == x
                && y_subject == y
                && constructors.iter().any(|ctor| ctor == x_ctor)
            {
                return Some(x_ctor.to_string());
            }
        }
        None
    }

    fn match_guarded_field(
        &self,
        conjunct: TermId,
        x: TermId,
        y: TermId,
        constructors: &[String],
    ) -> Option<(String, String)> {
        let TermData::App(Symbol::Named(name), args) = self.terms.get(conjunct) else {
            return None;
        };
        if name != "or" || args.len() != 2 {
            return None;
        }
        for (guard, field) in [(args[0], args[1]), (args[1], args[0])] {
            let TermData::Not(guard_inner) = self.terms.get(guard) else {
                continue;
            };
            let Some((constructor, subject)) = tester_application(self.terms, *guard_inner) else {
                continue;
            };
            if (subject == x || subject == y)
                && constructors
                    .iter()
                    .any(|candidate| candidate == constructor)
            {
                if let Some(selector) = self.match_field_equality(field, x, y, constructor) {
                    return Some((constructor.to_string(), selector));
                }
            }
        }
        None
    }

    fn accepts_multiple_constructors(
        &self,
        x: TermId,
        y: TermId,
        constructors: &[String],
        conjuncts: &[TermId],
    ) -> bool {
        let mut testers = Vec::new();
        let mut guarded_fields = Vec::new();
        for &conjunct in conjuncts {
            if let Some(constructor) = self.match_tester_agreement(conjunct, x, y, constructors) {
                if testers.contains(&constructor) {
                    return false;
                }
                testers.push(constructor);
                continue;
            }
            let Some(field) = self.match_guarded_field(conjunct, x, y, constructors) else {
                return false;
            };
            if guarded_fields.contains(&field) {
                return false;
            }
            guarded_fields.push(field);
        }
        testers.len() == constructors.len()
            && self.has_complete_field_coverage(constructors, &guarded_fields)
    }

    fn has_complete_field_coverage(
        &self,
        constructors: &[String],
        guarded_fields: &[(String, String)],
    ) -> bool {
        let mut expected = 0usize;
        for constructor in constructors {
            let Some(selectors) = self.selector_list(constructor) else {
                return false;
            };
            expected = expected.saturating_add(selectors.len());
            if selectors.iter().any(|selector| {
                !guarded_fields.iter().any(|(covered_ctor, covered_sel)| {
                    covered_ctor == constructor && covered_sel == selector
                })
            }) {
                return false;
            }
        }
        guarded_fields.len() == expected
    }
}

/// Validate a `DatatypeValueEqCongruence` lemma against the datatype and
/// constructor-to-selector registries.
///
/// Four single-literal biconditional shapes are accepted (equality
/// orientations may be swapped at every level):
///
/// ```text
/// (= (= x C) (is-C x))
/// (= (= t (C b_0 .. b_n))
///    (and (is-C t) (= (sel_0 t) b_0) ..))
/// (= (= x y) (and (= (sel_1 x) (sel_1 y)) ..))
/// (= (= x y)
///    (and (= (is-C1 x) (is-C1 y)) ..
///         (or (not (is-Ci s)) (= (sel_ik x) (sel_ik y))) ..))
/// ```
///
/// The bridge follows from tester evaluation and nullary reconstruction. A
/// constructor-application expansion follows from tester evaluation, selector
/// projection, and reconstruction. For equality expansions, congruence proves
/// the forward direction; exhaustiveness, complete tester agreement, complete
/// guarded field agreement, and reconstruction prove the reverse direction.
/// Every completeness condition is re-derived from the supplied registries,
/// and duplicate, foreign, or leftover conjuncts fail closed.
pub(crate) fn validate_datatype_value_eq_congruence(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    dt_decls: DatatypeDecls<'_>,
    ctor_selectors: SelectorDecls<'_>,
) -> Result<(), ProofCheckError> {
    let invalid = |reason: String| ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason,
    };
    let literals = flatten_clause_literals(terms, clause);
    let [literal] = literals.as_slice() else {
        return Err(invalid(format!(
            "datatype value-equality congruence clause has {} literals; expected one \
             biconditional",
            literals.len()
        )));
    };
    let (first, second) = equality_sides(terms, *literal).ok_or_else(|| {
        invalid("datatype value-equality congruence literal must be an equality".to_string())
    })?;
    let validator = Validator {
        terms,
        dt_decls,
        ctor_selectors,
    };
    if validator.accepts_orientation(first, second) || validator.accepts_orientation(second, first)
    {
        return Ok(());
    }
    Err(invalid(
        "datatype value-equality congruence does not match the bridge, single-constructor, \
         or multi-constructor biconditional against the registries"
            .to_string(),
    ))
}
