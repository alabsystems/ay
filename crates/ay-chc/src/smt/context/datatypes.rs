// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Recover datatype applications by their complete declared signature.

use super::SmtContext;
use crate::term_bridge::sort::chc_sort_to_core;
use crate::{ChcDtConstructor, ChcDtSelector, ChcExpr, ChcSort};
use ay_core::kani_compat::DetHashSet;
use ay_core::{Sort, TermId};
use std::sync::Arc;

#[derive(PartialEq, Eq)]
enum Kind {
    Constructor,
    Selector,
    Tester,
}

struct Application<'a> {
    kind: Kind,
    owner: &'a str,
    result: ChcSort,
}

impl<'a> Application<'a> {
    fn insert(slot: &mut Option<Self>, next: Self) -> Option<()> {
        if let Some(previous) = slot {
            // A datatype may use the same selector on several constructors.
            // Distinct interpretations of an otherwise identical signature
            // are ambiguous and must not depend on registry iteration order.
            return (previous.kind == Kind::Selector
                && next.kind == Kind::Selector
                && previous.owner == next.owner
                && previous.result == next.result)
                .then_some(());
        }
        *slot = Some(next);
        Some(())
    }
}

impl SmtContext {
    /// Name/arity alone cannot resolve overloaded datatype operations. Match
    /// raw argument/result metadata first, then check recovered arguments too.
    /// Missing, mismatched or ambiguous declarations refuse; there is no UF
    /// fallback and no replacement of a receiver's type with another record.
    pub(in crate::smt) fn try_dt_app_to_chc_expr(
        &self,
        name: &str,
        args: &[TermId],
        result: &Sort,
        mut convert_arg: impl FnMut(TermId) -> Option<ChcExpr>,
    ) -> Option<ChcExpr> {
        let mut matched = None;
        if let Some((owner, sort)) = self.declared_datatype(result) {
            for (constructor, fields) in self.datatype_defs.get(owner)? {
                if name == constructor
                    && fields.len() == args.len()
                    && fields.iter().zip(args).all(|((_, sort), arg)| {
                        self.declared_sort(sort, self.terms.sort(*arg)).is_some()
                    })
                {
                    Application::insert(
                        &mut matched,
                        Application {
                            kind: Kind::Constructor,
                            owner,
                            result: sort.clone(),
                        },
                    )?;
                }
            }
        }
        if let [receiver] = args {
            if let Some((owner, _)) = self.declared_datatype(self.terms.sort(*receiver)) {
                for (constructor, fields) in self.datatype_defs.get(owner)? {
                    for (selector, sort) in fields {
                        if name == selector {
                            let Some(result) = self.declared_sort(sort, result) else {
                                continue;
                            };
                            Application::insert(
                                &mut matched,
                                Application {
                                    kind: Kind::Selector,
                                    owner,
                                    result,
                                },
                            )?;
                        }
                    }
                    if result == &Sort::Bool
                        && name.strip_prefix("is-") == Some(constructor.as_str())
                    {
                        Application::insert(
                            &mut matched,
                            Application {
                                kind: Kind::Tester,
                                owner,
                                result: ChcSort::Bool,
                            },
                        )?;
                    }
                }
            }
        }
        let matched = matched?;
        if chc_sort_to_core(&matched.result) != *result {
            return None;
        }
        let arguments = args
            .iter()
            .map(|arg| {
                let expression = convert_arg(*arg)?;
                (chc_sort_to_core(&expression.sort()) == *self.terms.sort(*arg))
                    .then(|| Arc::new(expression))
            })
            .collect::<Option<Vec<_>>>()?;
        Some(ChcExpr::FuncApp(name.to_owned(), matched.result, arguments))
    }

    /// A recursive field may name a registered datatype without expanding it.
    /// Resolve that reference only against an authenticated raw datatype sort,
    /// preserving its full result metadata. This is not arbitrary nominal
    /// equality between uninterpreted and datatype sorts.
    fn declared_sort(&self, expected: &ChcSort, actual: &Sort) -> Option<ChcSort> {
        if chc_sort_to_core(expected) == *actual {
            return Some(expected.clone());
        }
        match (expected, actual) {
            (ChcSort::Uninterpreted(name), Sort::Datatype(_)) => {
                let (owner, sort) = self.declared_datatype(actual)?;
                (name == owner).then_some(sort)
            }
            (ChcSort::Array(key, value), Sort::Array(array)) => Some(ChcSort::Array(
                Box::new(self.declared_sort(key, &array.index_sort)?),
                Box::new(self.declared_sort(value, &array.element_sort)?),
            )),
            _ => None,
        }
    }

    /// Authenticate canonical core metadata, including array-valued fields.
    /// The shared bridge folds recursive references; this is not authentication
    /// of CHC metadata it erases. Unexpanded/foreign core metadata refuses.
    fn declared_datatype<'a>(&'a self, core: &'a Sort) -> Option<(&'a str, ChcSort)> {
        let Sort::Datatype(datatype) = core else {
            return None;
        };
        let constructors = self.datatype_defs.get(&datatype.name)?;
        let mut constructor_names = DetHashSet::default();
        for (name, fields) in constructors {
            let mut field_names = DetHashSet::default();
            if !constructor_names.insert(name)
                || fields.iter().any(|(name, _)| !field_names.insert(name))
            {
                return None;
            }
        }
        let sort = ChcSort::Datatype {
            name: datatype.name.clone(),
            constructors: crate::ChcDtConstructors::new(
                constructors
                    .iter()
                    .map(|(name, fields)| ChcDtConstructor {
                        name: name.clone(),
                        selectors: fields
                            .iter()
                            .map(|(name, sort)| ChcDtSelector {
                                name: name.clone(),
                                sort: sort.clone(),
                            })
                            .collect(),
                    })
                    .collect(),
            ),
        };
        (chc_sort_to_core(&sort) == *core).then_some((datatype.name.as_str(), sort))
    }
}
