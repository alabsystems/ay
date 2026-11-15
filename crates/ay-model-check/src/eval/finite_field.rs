// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Original-input exact modular evaluation. The existing public Int carrier is
//! used only under an authoritative finite-field sort and a canonicality check.
use super::*;
impl Evaluator<'_> {
    pub(super) fn eval_finite_field(&self, term: TermId, depth: usize) -> EvalResult<ModelValue> {
        let Sort::FiniteField(field) = self.terms.sort(term) else {
            return Err("not a field".into());
        };
        let modulus = BigInt::from(field.modulus());
        let value = match self.terms.get(term) {
            TermData::Const(Constant::FiniteField { value, field: q })
                if q == field && *value < field.modulus() =>
            {
                BigInt::from(*value)
            }
            TermData::Var(..) => {
                let v = self
                    .local_binding(term)?
                    .or_else(|| self.model.leaf_value(term))
                    .ok_or_else(|| {
                        EvalError::ModelUnavailable("field leaf is unassigned".into())
                    })?;
                let ModelValue::Int(n) = v else {
                    return Err("field model has wrong carrier".into());
                };
                n
            }
            TermData::Ite(c, t, e) => {
                if self.terms.sort(*t) != self.terms.sort(term)
                    || self.terms.sort(*e) != self.terms.sort(term)
                {
                    return Err("ill-sorted field ite".into());
                }
                let selected = if self.eval_bool(*c, depth + 1)? {
                    *t
                } else {
                    *e
                };
                let ModelValue::Int(n) = self.eval_operand(selected, depth + 1)? else {
                    return Err("field ite carrier".into());
                };
                n
            }
            TermData::App(Symbol::Named(name), args) => {
                if !matches!(name.as_str(), "ff.add" | "ff.mul" | "ff.neg" | "ff.bitsum")
                    || (if name == "ff.neg" {
                        args.len() != 1
                    } else {
                        args.len() < 2
                    })
                    || args
                        .iter()
                        .any(|t| self.terms.sort(*t) != self.terms.sort(term))
                {
                    return Err("unsupported or ill-sorted field application".into());
                }
                let mut result = BigInt::from(u8::from(name == "ff.mul"));
                let mut weight = BigInt::from(1);
                for &a in args {
                    let ModelValue::Int(n) = self.eval_operand(a, depth + 1)? else {
                        return Err("field operand carrier".into());
                    };
                    if n.is_negative() || n >= modulus {
                        return Err("noncanonical field operand".into());
                    }
                    result = match name.as_str() {
                        "ff.mul" => result * n,
                        "ff.neg" => -n,
                        "ff.bitsum" => result + &weight * n,
                        _ => result + n,
                    }
                    .mod_floor(&modulus);
                    weight = (weight * 2u8).mod_floor(&modulus);
                }
                result
            }
            _ => return Err("unsupported finite-field term".into()),
        };
        if value.is_negative() || value >= modulus {
            return Err("noncanonical finite-field model".into());
        }
        Ok(ModelValue::Int(value))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    struct FieldModel(TermId, ModelValue);
    impl ModelView for FieldModel {
        fn leaf_value(&self, t: TermId) -> Option<ModelValue> {
            (t == self.0).then(|| self.1.clone())
        }
        fn array_select_value(&self, _: TermId) -> Option<ModelValue> {
            None
        }
    }
    #[test]
    fn independent_field_model_checks_modular_truth_and_canonical_domain() {
        let f = ay_core::FiniteFieldSort::new(7).unwrap();
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::FiniteField(f));
        let three = terms.mk_finite_field(3, f);
        let one = terms.mk_finite_field(1, f);
        let sum = terms.mk_ff_app("ff.add", &[x, three]).unwrap();
        let goal = terms.mk_eq(sum, one);
        let right = FieldModel(x, ModelValue::Int(5.into()));
        let wrong = FieldModel(x, ModelValue::Int(4.into()));
        let noncanonical = FieldModel(x, ModelValue::Int(12.into()));
        let integer_mix = terms.mk_int(5.into());
        let forged = terms.mk_app(Symbol::named("="), &[x, integer_mix], Sort::Bool);
        assert!(matches!(
            Evaluator::new(&terms, &right).eval(goal, 0),
            Ok(ModelValue::Bool(true))
        ));
        assert!(matches!(
            Evaluator::new(&terms, &wrong).eval(goal, 0),
            Ok(ModelValue::Bool(false))
        ));
        assert!(Evaluator::new(&terms, &noncanonical).eval(goal, 0).is_err());
        assert!(Evaluator::new(&terms, &right).eval(forged, 0).is_err());
    }

    #[test]
    fn full_width_field_model_checks_original_products_and_rejects_wrong_values() {
        let field = ay_core::FiniteFieldSort::new(4_294_967_291).unwrap();
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::FiniteField(field));
        let minus_one = terms.mk_finite_field(field.modulus() - 1, field);
        let one = terms.mk_finite_field(1, field);
        let product = terms.mk_ff_app("ff.mul", &[x, minus_one]).unwrap();
        let assertion = terms.mk_eq(product, one);
        for (value, expected) in [(field.modulus() - 1, true), (1, false)] {
            let model = FieldModel(x, ModelValue::Int(value.into()));
            assert!(matches!(
                Evaluator::new(&terms, &model).eval(assertion, 0),
                Ok(ModelValue::Bool(actual)) if actual == expected
            ));
        }
        let noncanonical = FieldModel(x, ModelValue::Int(field.modulus().into()));
        assert!(Evaluator::new(&terms, &noncanonical)
            .eval(assertion, 0)
            .is_err());
    }
}
