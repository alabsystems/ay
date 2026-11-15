// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Reverse definitional substitution, followed by independent source replay.
//! Reconstruction DATA never authorizes a verdict or a fresh work allowance.
use super::*;
use ay_core::term::reserve_map_counted;
use ay_model_check::{EvalOutcome, ModelValue as Value, ModelView};

#[derive(Debug)]
pub(super) struct Layer {
    definitions: Vec<(TermId, TermId)>,
    previous: Option<Reconstruction>,
}

impl Layer {
    pub(super) fn bindings(&self) -> &[Binding] {
        match &self.previous {
            Some(Reconstruction::Encoded(rows)) => rows,
            _ => &[],
        }
    }
}

pub(super) fn price_integer(
    value: &num_bigint::BigInt,
    name_bytes: usize,
    owner: &dyn TermConstructionAdmission,
) -> Result<(), TacticFailure> {
    let words = usize::try_from(value.bits().div_ceil(32)).map_err(|_| refused(owner))?;
    let bytes = words
        .checked_mul(std::mem::size_of::<u64>())
        .and_then(|n| n.checked_add(name_bytes))
        .ok_or_else(|| refused(owner))?;
    owner
        .admit(
            words
                .checked_add(name_bytes)
                .ok_or_else(|| refused(owner))?,
            bytes,
        )
        .map_err(|_| refused(owner))
}

impl TacticModelConverter {
    pub(in crate::api::solving) fn equations(
        &self,
        terms: &TermStore,
        definitions: Vec<(TermId, TermId)>,
        owner: &dyn TermConstructionAdmission,
    ) -> Result<Self, TacticFailure> {
        if !self.valid(terms) {
            return Err(refused(owner));
        }
        // An empty definitional pass does not change the reconstruction
        // problem. In particular, do not populate defaults ahead of an
        // existing fixed witness: its source assignments are already exact.
        if definitions.is_empty() {
            owner.check().map_err(|_| refused(owner))?;
            return Ok(Self {
                source: Arc::clone(&self.source),
                reconstruction: self.reconstruction.clone(),
            });
        }
        let (mut combined, previous) = match &self.reconstruction {
            Some(Reconstruction::Equations(layer)) => {
                let mut combined = Vec::new();
                reserve_counted(&mut combined, layer.definitions.len(), owner)
                    .map_err(|_| refused(owner))?;
                owner
                    .admit(layer.definitions.len(), 0)
                    .map_err(|_| refused(owner))?;
                combined.extend_from_slice(&layer.definitions);
                (combined, layer.previous.clone())
            }
            prior => (Vec::new(), prior.clone()),
        };
        reserve_counted(&mut combined, definitions.len(), owner).map_err(|_| refused(owner))?;
        owner
            .admit(definitions.len(), 0)
            .map_err(|_| refused(owner))?;
        combined.extend(definitions);
        owner
            .admit(
                1,
                std::mem::size_of::<Layer>() + 2 * std::mem::size_of::<usize>(),
            )
            .map_err(|_| refused(owner))?;
        let result = Self {
            source: Arc::clone(&self.source),
            reconstruction: Some(Reconstruction::Equations(Arc::new(Layer {
                definitions: combined,
                previous,
            }))),
        };
        owner.check().map_err(|_| refused(owner))?;
        Ok(result)
    }

    pub(super) fn check_equation_namespace<'a>(
        &self,
        terms: &TermStore,
        layer: &Layer,
        names: impl Iterator<Item = (&'a String, &'a ay_frontend::SymbolInfo)>,
        adopted: &[(TermId, ay_frontend::DeclarationId)],
        owner: &dyn TermConstructionAdmission,
    ) -> Result<(), TacticFailure> {
        let mut current = Vec::new();
        for entry in names {
            reserve_counted(&mut current, 1, owner).map_err(|_| refused(owner))?;
            owner.admit(1, 0).map_err(|_| refused(owner))?;
            current.push(entry);
        }
        for captured in &self.source.namespace {
            let mut matched = false;
            for &(surface, info) in &current {
                for spelling in std::iter::once(surface).chain(info.internal_name.as_ref()) {
                    owner
                        .admit(
                            captured
                                .name
                                .len()
                                .checked_add(spelling.len())
                                .ok_or_else(|| refused(owner))?,
                            0,
                        )
                        .map_err(|_| refused(owner))?;
                    if captured.name == *spelling {
                        if captured.declaration != *info.declaration_identity()
                            || captured.term != info.term
                        {
                            return Err(refused(owner));
                        }
                        matched = true;
                    }
                }
            }
            if !matched {
                return Err(refused(owner));
            }
        }
        if let Some(prior) = &layer.previous {
            let prior = Self {
                source: Arc::clone(&self.source),
                reconstruction: Some(prior.clone()),
            };
            prior.check_namespace(terms, current.into_iter(), adopted, owner)?;
        }
        owner.check().map_err(|_| refused(owner))
    }

    pub(super) fn convert_equations(
        &self,
        terms: &TermStore,
        input: &Model,
        layer: &Layer,
        owner: &dyn TermConstructionAdmission,
    ) -> Result<Model, TacticFailure> {
        validate_model(input, true, owner)?;
        let mut result = copy_scalar_model(terms, input, &[], owner)?;
        let mut roots = Vec::new();
        reserve_counted(&mut roots, self.source.roots.len(), owner).map_err(|_| refused(owner))?;
        owner
            .admit(self.source.roots.len(), 0)
            .map_err(|_| refused(owner))?;
        roots.extend_from_slice(&self.source.roots);
        for &(variable, value) in &layer.definitions {
            owner.admit(1, 0).map_err(|_| refused(owner))?;
            reserve_counted(&mut roots, 2, owner).map_err(|_| refused(owner))?;
            roots.extend([variable, value]);
        }
        let marked = super::super::tactic_solve_eqs::reachable(terms, &roots, owner)?;
        let mut leaves = Vec::new();
        for (index, present) in marked.iter().enumerate() {
            owner.admit(1, 0).map_err(|_| refused(owner))?;
            if !present {
                continue;
            }
            let id = TermId(index as u32);
            let TermData::Var(key, _) = terms.get(id) else {
                continue;
            };
            // A name-keyed output cannot faithfully represent two identities
            // sharing a spelling (including differently sorted raw variables).
            for &earlier in &leaves {
                let other = name(terms, earlier).ok_or_else(|| refused(owner))?;
                owner
                    .admit(
                        key.len()
                            .checked_add(other.len())
                            .ok_or_else(|| refused(owner))?,
                        0,
                    )
                    .map_err(|_| refused(owner))?;
                if key == other {
                    return Err(refused(owner));
                }
            }
            reserve_counted(&mut leaves, 1, owner).map_err(|_| refused(owner))?;
            leaves.push(id);
            // Materialize defaults in the returned model itself; implicit
            // evaluator defaults must not certify a different public model.
            owner.admit(key.len(), 0).map_err(|_| refused(owner))?;
            let missing = match terms.sort(id) {
                Sort::Bool => !result.bool_values.contains_key(key),
                Sort::Int => !result.int_values.contains_key(key),
                Sort::Real => !result.real_values.contains_key(key),
                Sort::BitVec(_) => !result.bv_values.contains_key(key),
                Sort::FiniteField(_) => !result.field_values.contains_key(key),
                _ => return Err(refused(owner)),
            };
            if missing {
                owner
                    .admit(1, 2 * std::mem::size_of::<u64>())
                    .map_err(|_| refused(owner))?;
                let value = match terms.sort(id) {
                    Sort::Bool => Value::Bool(false),
                    Sort::Int | Sort::FiniteField(_) => Value::Int(0.into()),
                    Sort::Real => Value::Real(num_rational::BigRational::from_integer(0.into())),
                    Sort::BitVec(width) => Value::BitVec {
                        width: width.width,
                        value: 0.into(),
                    },
                    _ => return Err(refused(owner)),
                };
                insert(terms, id, value, &mut result, owner)?;
            }
        }
        for &(variable, value) in layer.definitions.iter().rev() {
            owner.admit(1, 0).map_err(|_| refused(owner))?;
            let view = View {
                terms,
                model: &result,
                owner,
            };
            let EvalOutcome::Value(value) = ay_model_check::evaluate_term(terms, &view, value)
            else {
                return Err(refused(owner));
            };
            insert(terms, variable, value, &mut result, owner)?;
        }
        if let Some(prior) = &layer.previous {
            let prior = Self {
                source: Arc::clone(&self.source),
                reconstruction: Some(prior.clone()),
            };
            result = prior.convert(terms, &result, owner)?;
        }
        let view = View {
            terms,
            model: &result,
            owner,
        };
        if !matches!(
            ay_model_check::confirm_completed_model(terms, &view, &self.source.roots),
            ay_model_check::GateVerdict::ConfirmedSat
        ) {
            return Err(refused(owner));
        }
        owner.check().map_err(|_| refused(owner))?;
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::api::{Logic, Solver, Tactic};

    #[test]
    fn owned_solve_eqs_reconstructs_reverse_integer_definitions_and_replays_source() {
        let mut solver = Solver::new(Logic::All);
        let x = solver.declare_const("equation_x", Sort::Int);
        let y = solver.declare_const("equation_y", Sort::Int);
        let two = solver.int_const(2);
        let five = solver.int_const(5);
        let sum = solver.add(y, two);
        let roots = [solver.eq(x, sum), solver.eq(y, five)];
        let mut goals = solver
            .apply_tactic_subgoals_converted(
                &Tactic::Simplify
                    .then(Tactic::SolveEqs)
                    .then(Tactic::SolveEqs),
                &roots,
                0,
                None,
            )
            .unwrap();
        let goal = goals.remove(0);
        assert!(goal.formulas.is_empty());
        assert_eq!(goal.depth, 3);
        let model = solver
            .convert_tactic_model(goal.model_converter.as_ref().unwrap(), &Model::empty())
            .unwrap();
        assert_eq!(model.int_val("equation_x"), Some(&7.into()));
        assert_eq!(model.int_val("equation_y"), Some(&5.into()));

        #[cfg(any(
            target_os = "macos",
            all(target_os = "linux", not(target_env = "uclibc"))
        ))]
        if let Some(normalized) = super::super::bounded_reference(
            "(set-logic QF_LIA)\n(declare-const equation_x Int)\n(declare-const equation_y Int)\n(assert (= equation_x (+ equation_y 2)))\n(assert (= equation_y 5))\n(check-sat-using (then simplify solve-eqs smt))\n(get-value (equation_x equation_y))\n",
            "owned solve-eqs reconstruction") {
            assert_eq!(normalized, "sat ((equation_x 7) (equation_y 5))");
        }
    }

    #[test]
    fn owned_solve_eqs_materializes_free_defaults_and_refuses_a_violated_residual() {
        let mut solver = Solver::new(Logic::All);
        let x = solver.declare_const("equation_x", Sort::Int);
        let y = solver.declare_const("equation_y", Sort::Int);
        let two = solver.int_const(2);
        let sum = solver.add(y, two);
        let roots = [solver.eq(x, sum)];
        let goals = solver
            .apply_tactic_subgoals_converted(&Tactic::SolveEqs, &roots, 0, None)
            .unwrap();
        let converter = goals[0].model_converter.as_ref().unwrap();
        let model = solver
            .convert_tactic_model(converter, &Model::empty())
            .unwrap();
        assert_eq!(model.int_val("equation_y"), Some(&0.into()));
        assert_eq!(model.int_val("equation_x"), Some(&2.into()));

        let p = solver.bool_var("equation_residual");
        let roots = [roots[0], p];
        let goals = solver
            .apply_tactic_subgoals_converted(&Tactic::SolveEqs, &roots, 0, None)
            .unwrap();
        assert!(solver
            .convert_tactic_model(goals[0].model_converter.as_ref().unwrap(), &Model::empty())
            .is_err());
        let mut witness = Model::empty();
        witness.bool_values.insert("equation_residual".into(), true);
        assert!(solver
            .convert_tactic_model(goals[0].model_converter.as_ref().unwrap(), &witness)
            .is_ok());
    }

    #[test]
    fn owned_solve_eqs_transports_exact_rational_wide_bv_field_and_boolean_values() {
        let mut solver = Solver::new(Logic::All);
        let field = ay_core::FiniteFieldSort::new(7).unwrap();
        let real = solver.declare_const("equation_real", Sort::Real);
        let bv = solver.declare_const("equation_bv", Sort::BitVec(ay_core::BitVecSort::new(137)));
        let ff = solver.declare_const("equation_field", Sort::FiniteField(field));
        let p = solver.bool_var("equation_p");
        let q = solver.bool_var("equation_q");
        let third = solver.rational_const(1, 3);
        let wide: num_bigint::BigInt = (num_bigint::BigInt::from(1u32) << 135usize) + 1u32;
        let bits = solver.bv_const_bigint(&wide, 137);
        let four = solver.finite_field_const(&4.into(), field);
        let negative = solver.not(q);
        let roots = [
            solver.eq(real, third),
            solver.eq(bv, bits),
            solver.eq(ff, four),
            solver.eq(p, negative),
            q,
        ];
        let goals = solver
            .apply_tactic_subgoals_converted(&Tactic::SolveEqs, &roots, 0, None)
            .unwrap();
        let mut witness = Model::empty();
        witness.bool_values.insert("equation_q".into(), true);
        let model = solver
            .convert_tactic_model(goals[0].model_converter.as_ref().unwrap(), &witness)
            .unwrap();
        assert_eq!(
            model.real_val("equation_real"),
            Some(&num_rational::BigRational::new(1.into(), 3.into()))
        );
        assert_eq!(model.bv_val("equation_bv"), Some((wide, 137)));
        assert_eq!(
            model.finite_field_val("equation_field"),
            Some(&ModelValue::FiniteField { value: 4, field })
        );
        assert_eq!(model.bool_val("equation_p"), Some(false));
        assert_eq!(model.bool_val("equation_q"), Some(true));
    }
}

fn insert(
    terms: &TermStore,
    id: TermId,
    value: Value,
    model: &mut Model,
    owner: &dyn TermConstructionAdmission,
) -> Result<(), TacticFailure> {
    let key = name(terms, id).ok_or_else(|| refused(owner))?;
    owner
        .admit(key.len(), key.len())
        .map_err(|_| refused(owner))?;
    match (terms.sort(id), value) {
        (Sort::Bool, Value::Bool(value)) => {
            reserve_map_counted(&mut model.bool_values, 1, owner).map_err(|_| refused(owner))?;
            model.bool_values.insert(key.to_owned(), value);
        }
        (Sort::Int, Value::Int(value)) => {
            reserve_map_counted(&mut model.int_values, 1, owner).map_err(|_| refused(owner))?;
            model.int_values.insert(key.to_owned(), value);
        }
        (Sort::Real, Value::Real(value)) => {
            reserve_map_counted(&mut model.real_values, 1, owner).map_err(|_| refused(owner))?;
            model.real_values.insert(key.to_owned(), value);
        }
        (
            Sort::BitVec(width),
            Value::BitVec {
                width: actual,
                value,
            },
        ) if actual == width.width
            && value.sign() != num_bigint::Sign::Minus
            && value.bits() <= u64::from(actual) =>
        {
            reserve_map_counted(&mut model.bv_values, 1, owner).map_err(|_| refused(owner))?;
            model.bv_values.insert(key.to_owned(), (value, actual));
        }
        (Sort::FiniteField(field), Value::Int(value)) => {
            let value = value
                .to_u32()
                .filter(|v| *v < field.modulus())
                .ok_or_else(|| refused(owner))?;
            reserve_map_counted(&mut model.field_values, 1, owner).map_err(|_| refused(owner))?;
            model.field_values.insert(
                key.to_owned(),
                ModelValue::FiniteField {
                    value,
                    field: *field,
                },
            );
        }
        _ => return Err(refused(owner)),
    }
    owner.check().map_err(|_| refused(owner))
}

struct View<'a> {
    terms: &'a TermStore,
    model: &'a Model,
    owner: &'a dyn TermConstructionAdmission,
}
impl ModelView for View<'_> {
    fn has_evaluation_admission(&self) -> bool {
        true
    }
    fn admit_evaluation_work(&self, work: usize, bytes: usize) -> Result<(), String> {
        self.owner.admit(work, bytes).map_err(|e| e.to_string())
    }
    fn refuse_evaluation_work(&self, _: &str) {
        ay_core::render_admission::invalid(Some(self.owner));
    }
    fn functional_array_interrupted(&self) -> bool {
        self.owner.check().is_err()
    }
    fn charge_functional_array_work(&self, work: usize) -> Result<(), String> {
        self.admit_evaluation_work(work, 0)
    }
    fn leaf_value(&self, id: TermId) -> Option<Value> {
        let key = name(self.terms, id)?;
        self.owner.admit(key.len(), 0).ok()?;
        match self.terms.sort(id) {
            Sort::Bool => self.model.bool_values.get(key).copied().map(Value::Bool),
            Sort::Int => {
                let value = self.model.int_values.get(key)?;
                price_integer(value, 0, self.owner).ok()?;
                Some(Value::Int(value.clone()))
            }
            Sort::Real => {
                let value = self.model.real_values.get(key)?;
                price_integer(value.numer(), 0, self.owner).ok()?;
                price_integer(value.denom(), 0, self.owner).ok()?;
                Some(Value::Real(value.clone()))
            }
            Sort::BitVec(width) => {
                let (value, actual) = self.model.bv_values.get(key)?;
                if *actual != width.width {
                    return None;
                }
                price_integer(value, 0, self.owner).ok()?;
                Some(Value::BitVec {
                    width: *actual,
                    value: value.clone(),
                })
            }
            Sort::FiniteField(field) => match self.model.field_values.get(key)? {
                ModelValue::FiniteField {
                    value,
                    field: actual,
                } if actual == field && *value < field.modulus() => {
                    self.owner.admit(1, std::mem::size_of::<u64>()).ok()?;
                    Some(Value::Int((*value).into()))
                }
                _ => None,
            },
            _ => None,
        }
    }
}
