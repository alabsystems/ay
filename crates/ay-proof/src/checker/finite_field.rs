// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Independent prime-field theorem checker. Complete mixed-radix enumeration
//! (Knuth, TAOCP 4A, §7.2.1.1); no producer evaluator or presumed bindings.
use super::ProofCheckError;
pub(super) mod ideal;
pub(super) mod linear;
pub(super) mod quadratic;
pub(super) mod univariate;
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Constant, ProofId, Sort, Symbol, TermData, TermId, TermStore};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Value {
    Bool(bool),
    Field(u32, u32),
}
impl Value {
    fn boolean(self) -> Option<bool> {
        if let Self::Bool(b) = self {
            Some(b)
        } else {
            None
        }
    }
}
struct Check<'a, 'p> {
    terms: &'a TermStore,
    values: HashMap<TermId, Value>,
    work: usize,
    progress: &'p mut dyn FnMut(usize, usize) -> bool,
}
impl Check<'_, '_> {
    fn eval(&mut self, term: TermId, depth: usize) -> Option<Value> {
        self.work = self.work.checked_sub(1)?;
        if depth > 128 || !(self.progress)(1, 0) {
            return None;
        }
        let value = match self.terms.get(term) {
            TermData::Const(Constant::Bool(b)) => Value::Bool(*b),
            TermData::Const(Constant::FiniteField { value, field }) if *value < field.modulus() => {
                Value::Field(*value, field.modulus())
            }
            TermData::Var(..) => *self.values.get(&term)?,
            TermData::Not(t) => Value::Bool(!self.eval(*t, depth + 1)?.boolean()?),
            TermData::Ite(c, t, e) => {
                // Check both branches; an unsupported branch cannot hide behind a value.
                let c = self.eval(*c, depth + 1)?.boolean()?;
                let t = self.eval(*t, depth + 1)?;
                let e = self.eval(*e, depth + 1)?;
                if let TermData::Ite(_, a, b) = self.terms.get(term) {
                    if self.terms.sort(*a) != self.terms.sort(term)
                        || self.terms.sort(*b) != self.terms.sort(term)
                    {
                        return None;
                    }
                }
                if std::mem::discriminant(&t) != std::mem::discriminant(&e) {
                    return None;
                }
                if c {
                    t
                } else {
                    e
                }
            }
            TermData::App(Symbol::Named(name), args) => {
                let mut v = Vec::new();
                if args.len() > 1024 {
                    return None;
                }
                for &a in args {
                    v.push(self.eval(a, depth + 1)?);
                }
                match name.as_str() {
                    "not" if v.len() == 1 => Value::Bool(!v[0].boolean()?),
                    "and" | "or" | "xor" => {
                        let mut b = name == "and";
                        for a in v {
                            let a = a.boolean()?;
                            b = match name.as_str() {
                                "and" => b && a,
                                "or" => b || a,
                                _ => b ^ a,
                            };
                        }
                        Value::Bool(b)
                    }
                    "=>" if v.len() == 2 => Value::Bool(!v[0].boolean()? || v[1].boolean()?),
                    "=" | "distinct" if v.len() >= 2 => {
                        if args
                            .iter()
                            .any(|a| self.terms.sort(*a) != self.terms.sort(args[0]))
                        {
                            return None;
                        }
                        let comparisons = if name == "=" {
                            v.len()
                        } else {
                            v.len().checked_mul(v.len() - 1)? / 2
                        };
                        self.work = self.work.checked_sub(comparisons)?;
                        if !(self.progress)(comparisons, 0) {
                            return None;
                        }
                        Value::Bool(if name == "=" {
                            v.iter().all(|a| *a == v[0])
                        } else {
                            (0..v.len()).all(|i| (0..i).all(|j| v[i] != v[j]))
                        })
                    }
                    "ff.add" | "ff.mul" | "ff.neg" | "ff.bitsum" => {
                        if (name == "ff.neg" && v.len() != 1) || (name != "ff.neg" && v.len() < 2) {
                            return None;
                        }
                        let Sort::FiniteField(field) = self.terms.sort(term) else {
                            return None;
                        };
                        let p = u64::from(field.modulus());
                        let mut result = if name == "ff.mul" { 1 } else { 0 };
                        let mut weight = 1;
                        for (i, a) in v.iter().enumerate() {
                            if self.terms.sort(args[i]) != self.terms.sort(term) {
                                return None;
                            }
                            let Value::Field(a, q) = a else {
                                return None;
                            };
                            if u64::from(*q) != p || u64::from(*a) >= p {
                                return None;
                            }
                            result = match name.as_str() {
                                "ff.mul" => result * u64::from(*a) % p,
                                "ff.neg" => (p - u64::from(*a)) % p,
                                "ff.bitsum" => (result + weight * u64::from(*a)) % p,
                                _ => (result + u64::from(*a)) % p,
                            };
                            weight = weight * 2 % p;
                        }
                        Value::Field(result as u32, p as u32)
                    }
                    _ => return None,
                }
            }
            _ => return None,
        };
        match (value, self.terms.sort(term)) {
            (Value::Bool(_), Sort::Bool) => Some(value),
            (Value::Field(n, p), Sort::FiniteField(f)) if p == f.modulus() && n < p => Some(value),
            _ => None,
        }
    }
}
pub(crate) fn validate(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    let valid = (|| -> Option<bool> {
        if clause.is_empty() || clause.len() > 64 {
            return None;
        }
        // Prepay a conservative complete private allocation envelope: at most
        // 128 recursive frames with 1024 tiny values each, plus bounded maps
        // and the 4096-entry walk stack. This is not a process-RSS guarantee.
        if !progress(1, 4 * 1024 * 1024) {
            return None;
        }
        let mut seen = HashSet::default();
        let mut stack = clause.to_vec();
        let mut vars = Vec::new();
        let mut count = 1usize;
        let mut has_field = false;
        while let Some(t) = stack.pop() {
            if !progress(1, 0) {
                return None;
            }
            if !seen.insert(t) {
                continue;
            }
            if seen.len() > 1024 || stack.len() > 4096 {
                return None;
            }
            has_field |= matches!(terms.sort(t), Sort::FiniteField(_));
            if let TermData::Var(..) = terms.get(t) {
                let size = match terms.sort(t) {
                    Sort::Bool => 2,
                    Sort::FiniteField(f) => f.modulus(),
                    _ => return None,
                };
                count = count.checked_mul(size as usize)?;
                if count > 65536 {
                    return None;
                }
                vars.push((t, size));
            }
            // Refuse before `children` clones an attacker-sized argument list.
            if let TermData::App(_, args) = terms.get(t) {
                if args.len() > 1024 {
                    return None;
                }
            }
            if let TermData::App(Symbol::Named(name), _) = terms.get(t) {
                if !progress(name.len(), 0) || terms.is_declared_function(name) {
                    return None;
                }
            }
            if !matches!(
                terms.get(t),
                TermData::Const(_)
                    | TermData::Var(..)
                    | TermData::App(..)
                    | TermData::Not(_)
                    | TermData::Ite(..)
            ) {
                return None;
            }
            let children = terms.children(t);
            if stack.len().checked_add(children.len())? > 4096 {
                return None;
            }
            stack.extend(children);
        }
        if !has_field || clause.iter().any(|t| terms.sort(*t) != &Sort::Bool) {
            return None;
        }
        let mut checker = Check {
            terms,
            values: HashMap::default(),
            work: 4_000_000,
            progress,
        };
        for mut index in 0..count {
            for &(t, p) in &vars {
                let n = (index % p as usize) as u32;
                index /= p as usize;
                checker.values.insert(
                    t,
                    if terms.sort(t) == &Sort::Bool {
                        Value::Bool(n != 0)
                    } else {
                        Value::Field(n, p)
                    },
                );
            }
            let mut holds = false;
            for &t in clause {
                holds |= checker.eval(t, 0)?.boolean()?;
            }
            if !holds {
                return Some(false);
            }
        }
        Some(true)
    })() == Some(true);
    if valid {
        Ok(())
    } else {
        Err(ProofCheckError::InvalidTheoryLemma {
            step,
            reason: "finite-field exhaustive theorem is false, unsupported, or over budget".into(),
        })
    }
}

#[cfg(test)]
mod namespace_tests;
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn falsifiable_and_cancelled_field_lemmas_are_rejected() {
        let mut terms = TermStore::new();
        let f = ay_core::FiniteFieldSort::new(7).unwrap();
        let x = terms.mk_var("x", Sort::FiniteField(f));
        let square = terms.mk_ff_app("ff.mul", &[x, x]).unwrap();
        let three = terms.mk_finite_field(3, f);
        let two = terms.mk_finite_field(2, f);
        let false_claim = terms.mk_eq(square, two);
        let nonroot = terms.mk_eq(square, three);
        let theorem = terms.mk_not_raw(nonroot);
        assert!(validate(&terms, ProofId(0), &[theorem], &mut |_, _| true).is_ok());
        assert!(validate(&terms, ProofId(0), &[false_claim], &mut |_, _| true).is_err());
        assert!(validate(&terms, ProofId(0), &[theorem], &mut |_, _| false).is_err());
        // A valid clause must not disguise an unsupported operator as a UF.
        let foreign = terms.mk_app(Symbol::named("ff.div"), &[x, two], Sort::FiniteField(f));
        let tautology = terms.mk_app(Symbol::named("="), &[foreign, foreign], Sort::Bool);
        assert!(validate(&terms, ProofId(0), &[tautology], &mut |_, _| true).is_err());
    }
}
