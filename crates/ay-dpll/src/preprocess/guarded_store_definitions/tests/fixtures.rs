// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) struct Fixture {
    pub(super) terms: TermStore,
    pub(super) request: GuardedStoreRequest,
    pub(super) roots: Vec<TermId>,
}

impl Fixture {
    pub(super) fn new(width: u32, values: [u8; 2]) -> Self {
        let mut terms = TermStore::new();
        let zero = terms.mk_bitvec(0.into(), width);
        let base = terms.mk_const_array(Sort::Bool, zero);
        let array_sort = terms.sort(base).clone();
        let variable = terms.mk_var("a", array_sort.clone());
        let guards = [terms.mk_var("g", Sort::Bool), terms.mk_var("h", Sort::Bool)];
        let activation = terms.mk_var("active", Sort::Bool);
        let key = terms.false_term();
        let mut cases = [GuardedStoreCase {
            guard: guards[0],
            source: base,
            store: base,
        }; 2];
        for index in 0..2 {
            let mut payload = num_bigint::BigInt::from(values[index]);
            if width == 129 {
                payload += num_bigint::BigInt::from(1) << 128;
            }
            let value = terms.mk_bitvec(payload, width);
            let store = terms.mk_app(
                Symbol::named("store"),
                [base, key, value],
                array_sort.clone(),
            );
            // Reversed equality and an extra conjunct exercise source syntax,
            // not a fabricated top-level array definition.
            let eq = raw_eq(&mut terms, store, variable);
            let tautology = raw_eq(&mut terms, value, value);
            let body = terms.mk_app(Symbol::named("and"), [eq, tautology], Sort::Bool);
            let not_guard = terms.mk_not_raw(guards[index]);
            let source = terms.mk_app(Symbol::named("or"), [body, not_guard], Sort::Bool);
            cases[index] = GuardedStoreCase {
                guard: guards[index],
                source,
                store,
            };
        }
        let cover = terms.mk_app(Symbol::named("or"), [guards[1], guards[0]], Sort::Bool);
        let true_term = terms.true_term();
        let body = terms.mk_app(Symbol::named("and"), [true_term, cover], Sort::Bool);
        let not_active = terms.mk_not_raw(activation);
        let cover_source = terms.mk_app(Symbol::named("or"), [not_active, body], Sort::Bool);
        let roots = vec![cases[0].source, cases[1].source, cover_source, activation];
        Self {
            terms,
            roots,
            request: GuardedStoreRequest {
                variable,
                cases,
                cover_source,
                activation: Some(activation),
            },
        }
    }

    pub(super) fn derive(&mut self) -> Option<GuardedStoreDefinition> {
        derive(&mut self.terms, &self.roots, self.request, &mut |_, _| true)
    }

    pub(super) fn authenticate(&self, proof: &Proof) -> bool {
        ay_proof::authenticate_premise_clauses_strict_with_context_and_progress(
            proof,
            &self.terms,
            None,
            None,
            &self.roots,
            &mut |_, _| true,
        )
        .is_ok()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum Value {
    Bool(bool),
    Bv(u8),
    Array([u8; 2]),
}

/// Tiny independent exhaustive oracle. Only the authored Bool/BV2 fixture
/// grammar is accepted; unsupported syntax panics rather than returning true.
pub(super) fn evaluate(terms: &TermStore, term: TermId, array: [u8; 2], g: bool, h: bool) -> Value {
    use ay_core::Constant;
    use num_traits::ToPrimitive;
    use Value::*;
    let eval = |term| evaluate(terms, term, array, g, h);
    if let Some(fill) = terms.get_const_array(term) {
        let Bv(fill) = eval(fill) else {
            panic!("non-BV fill")
        };
        return Array([fill; 2]);
    }
    match terms.get(term) {
        TermData::Const(Constant::Bool(value)) => Bool(*value),
        TermData::Const(Constant::BitVec { value, width: 2 }) => Bv(value.to_u8().unwrap()),
        TermData::Var(name, _) => match name.as_str() {
            "a" => Array(array),
            "g" => Bool(g),
            "h" => Bool(h),
            "active" => Bool(true),
            _ => panic!("unknown oracle variable"),
        },
        TermData::Not(child) => {
            let Bool(value) = eval(*child) else {
                panic!("non-Bool not")
            };
            Bool(!value)
        }
        TermData::Ite(c, t, e) => {
            let Bool(condition) = eval(*c) else {
                panic!("non-Bool condition")
            };
            eval(if condition { *t } else { *e })
        }
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "=" => {
                assert_eq!(args.len(), 2);
                Bool(eval(args[0]) == eval(args[1]))
            }
            "and" | "or" => {
                let values: Vec<_> = args
                    .iter()
                    .map(|&child| {
                        let Bool(value) = eval(child) else {
                            panic!("non-Bool connective")
                        };
                        value
                    })
                    .collect();
                Bool(if name == "and" {
                    values.iter().all(|v| *v)
                } else {
                    values.iter().any(|v| *v)
                })
            }
            "store" => {
                assert_eq!(args.len(), 3);
                let Array(mut cells) = eval(args[0]) else {
                    panic!("non-array base")
                };
                let Bool(key) = eval(args[1]) else {
                    panic!("non-Bool key")
                };
                let Bv(value) = eval(args[2]) else {
                    panic!("non-BV write")
                };
                cells[usize::from(key)] = value;
                Array(cells)
            }
            _ => panic!("unsupported oracle operator {name}"),
        },
        other => panic!("unsupported oracle term {other:?}"),
    }
}
