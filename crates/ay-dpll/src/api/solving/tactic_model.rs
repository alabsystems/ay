// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Immutable typed reconstruction for field-to-BV goal transformations.
//! A converter carries source DATA, never a solver verdict or proof permit.

use super::field_to_bv::Binding;
use super::tactics::TacticFailure;
use crate::api::{Model, ModelValue};
use ay_core::term::{reserve_counted, TermConstructionAdmission, TermStoreSnapshotStamp};
use ay_core::{Sort, Symbol, TermData, TermId, TermStore};
use num_traits::ToPrimitive;
use std::sync::Arc;

#[cfg(all(
    test,
    any(
        target_os = "macos",
        all(target_os = "linux", not(target_env = "uclibc"))
    )
))]
pub(super) fn bounded_reference(input: &str, suite: &str) -> Option<String> {
    use std::io::Write as _;
    let oracle = ay_test_support::z3::optional_z3(suite)?;
    let mut file = tempfile::Builder::new().suffix(".smt2").tempfile().unwrap();
    file.write_all(input.as_bytes()).unwrap();
    file.flush().unwrap();
    let mut command = oracle.command();
    command.arg(file.path());
    let output = ay_sys::metadata_capture::capture(
        command,
        ay_sys::metadata_capture::CaptureLimits {
            timeout: std::time::Duration::from_secs(5),
            output_bytes: 4096,
            resident_bytes: Some(256 << 20),
        },
        suite,
    )
    .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    Some(
        String::from_utf8(output.stdout)
            .unwrap()
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" "),
    )
}

mod equations;
mod fixed;

#[derive(Debug)]
struct Source {
    stamp: TermStoreSnapshotStamp,
    roots: Vec<TermId>,
    namespace: Vec<NamespaceBinding>,
}

#[derive(Debug)]
struct NamespaceBinding {
    name: String,
    declaration: ay_frontend::DeclarationId,
    term: Option<TermId>,
}

#[derive(Debug, Clone)]
enum Reconstruction {
    Encoded(Arc<Vec<Binding>>),
    Fixed(Arc<fixed::Witness>),
    Equations(Arc<equations::Layer>),
}

/// A context-bound, immutable model reconstruction attached to a tactic goal.
/// Its constructors are private: caller-provided assignments gain no authority.
#[derive(Debug, Clone)]
pub struct TacticModelConverter {
    source: Arc<Source>,
    reconstruction: Option<Reconstruction>,
}

fn refused(owner: &dyn TermConstructionAdmission) -> TacticFailure {
    let message = "tactic model reconstruction refused or original admission stopped";
    if owner.admit(message.len(), message.len()).is_err() {
        return TacticFailure::new("tactic model conversion original owner stopped");
    }
    TacticFailure::new(message)
}

fn name(terms: &TermStore, id: TermId) -> Option<&str> {
    match terms.get(id) {
        TermData::Var(name, _) => Some(name),
        TermData::App(Symbol::Named(name), args) if args.is_empty() => Some(name),
        _ => None,
    }
}

impl TacticModelConverter {
    pub(super) fn capture<'a>(
        terms: &TermStore,
        roots: &[TermId],
        names: impl Iterator<Item = (&'a String, &'a ay_frontend::SymbolInfo)>,
        owner: &dyn TermConstructionAdmission,
    ) -> Result<Self, TacticFailure> {
        let mut original = Vec::new();
        reserve_counted(&mut original, roots.len(), owner).map_err(|_| refused(owner))?;
        owner.admit(roots.len(), 0).map_err(|_| refused(owner))?;
        original.extend_from_slice(roots);
        let mut namespace = Vec::new();
        for (surface, info) in names {
            for name in std::iter::once(surface).chain(info.internal_name.as_ref()) {
                reserve_counted(&mut namespace, 1, owner).map_err(|_| refused(owner))?;
                owner
                    .admit(
                        name.len().checked_add(1).ok_or_else(|| refused(owner))?,
                        name.len(),
                    )
                    .map_err(|_| refused(owner))?;
                namespace.push(NamespaceBinding {
                    name: name.clone(),
                    declaration: info.declaration_identity().clone(),
                    term: info.term,
                });
            }
        }
        owner
            .admit(
                1,
                std::mem::size_of::<Source>() + 2 * std::mem::size_of::<usize>(),
            )
            .map_err(|_| refused(owner))?;
        let source = Arc::new(Source {
            stamp: terms.snapshot_stamp(),
            roots: original,
            namespace,
        });
        owner.check().map_err(|_| refused(owner))?;
        Ok(Self {
            source,
            reconstruction: None,
        })
    }

    pub(super) fn is_active(&self) -> bool {
        self.reconstruction.is_some()
    }
    pub(super) fn valid(&self, terms: &TermStore) -> bool {
        self.source.stamp.is_append_only_prefix_of(terms)
    }
    pub(super) fn namespace(&self) -> impl Iterator<Item = &str> + Clone {
        self.source
            .namespace
            .iter()
            .map(|binding| binding.name.as_str())
    }

    pub(super) fn bindings(&self) -> &[Binding] {
        match &self.reconstruction {
            Some(Reconstruction::Encoded(bindings)) => bindings,
            Some(Reconstruction::Equations(layer)) => layer.bindings(),
            _ => &[],
        }
    }
    pub(super) fn check_namespace<'a>(
        &self,
        terms: &TermStore,
        names: impl Iterator<Item = (&'a String, &'a ay_frontend::SymbolInfo)>,
        adopted: &[(TermId, ay_frontend::DeclarationId)],
        owner: &dyn TermConstructionAdmission,
    ) -> Result<(), TacticFailure> {
        if !self.valid(terms) {
            return Err(refused(owner));
        }
        let bindings = match &self.reconstruction {
            Some(Reconstruction::Equations(layer)) => {
                return self.check_equation_namespace(terms, layer, names, adopted, owner)
            }
            Some(Reconstruction::Encoded(bindings)) => bindings,
            Some(Reconstruction::Fixed(rows)) => {
                return self.check_fixed_namespace(terms, rows, names, owner)
            }
            None => return Ok(()),
        };
        for (surface, info) in names {
            for current in std::iter::once(surface).chain(info.internal_name.as_ref()) {
                for binding in bindings.iter() {
                    let representative =
                        name(terms, binding.representative).ok_or_else(|| refused(owner))?;
                    owner
                        .admit(
                            current
                                .len()
                                .checked_add(representative.len())
                                .ok_or_else(|| refused(owner))?,
                            0,
                        )
                        .map_err(|_| refused(owner))?;
                    if binding.field.is_some() && current == representative {
                        owner.admit(adopted.len(), 0).map_err(|_| refused(owner))?;
                        if info.term != Some(binding.representative)
                            || !adopted.iter().any(|(term, identity)| {
                                *term == binding.representative
                                    && identity == info.declaration_identity()
                            })
                        {
                            return Err(refused(owner));
                        }
                    }
                    let original = name(terms, binding.source).ok_or_else(|| refused(owner))?;
                    owner
                        .admit(
                            current
                                .len()
                                .checked_add(original.len())
                                .ok_or_else(|| refused(owner))?,
                            0,
                        )
                        .map_err(|_| refused(owner))?;
                    if current == original {
                        let mut matched = false;
                        for captured in &self.source.namespace {
                            owner
                                .admit(
                                    captured
                                        .name
                                        .len()
                                        .checked_add(current.len())
                                        .ok_or_else(|| refused(owner))?,
                                    0,
                                )
                                .map_err(|_| refused(owner))?;
                            matched |= captured.name == *current
                                && captured.declaration == *info.declaration_identity();
                        }
                        if !matched {
                            return Err(refused(owner));
                        }
                    }
                }
            }
        }
        owner.check().map_err(|_| refused(owner))?;
        Ok(())
    }
    pub(super) fn encoded(
        &self,
        bindings: Vec<Binding>,
        owner: &dyn TermConstructionAdmission,
    ) -> Result<Self, TacticFailure> {
        owner
            .admit(
                1,
                std::mem::size_of::<Vec<Binding>>() + 2 * std::mem::size_of::<usize>(),
            )
            .map_err(|_| refused(owner))?;
        let result = Self {
            source: Arc::clone(&self.source),
            reconstruction: Some(Reconstruction::Encoded(Arc::new(bindings))),
        };
        owner.check().map_err(|_| refused(owner))?;
        Ok(result)
    }

    /// Copy the scalar DATA of a models-disabled goal without reconstructing
    /// or removing any auxiliary interpretation. This supplies no verdict.
    pub(super) fn copy_unconverted(
        &self,
        terms: &TermStore,
        input: &Model,
        owner: &dyn TermConstructionAdmission,
    ) -> Result<Model, TacticFailure> {
        if !self.valid(terms) {
            return Err(refused(owner));
        }
        validate_scalar_model(input, owner)?;
        copy_scalar_model(terms, input, &[], owner)
    }

    /// Convert only supported scalar leaves and independently replay every
    /// original root. Missing/out-of-range/forged representatives refuse.
    pub(super) fn convert(
        &self,
        terms: &TermStore,
        input: &Model,
        owner: &dyn TermConstructionAdmission,
    ) -> Result<Model, TacticFailure> {
        if !self.valid(terms) {
            return Err(refused(owner));
        }
        if let Some(Reconstruction::Equations(layer)) = &self.reconstruction {
            return self.convert_equations(terms, input, layer, owner);
        }
        validate_scalar_model(input, owner)?;
        let bindings = match &self.reconstruction {
            Some(Reconstruction::Encoded(bindings)) => bindings,
            Some(Reconstruction::Fixed(rows)) => {
                return self.convert_fixed(terms, input, rows, owner)
            }
            Some(Reconstruction::Equations(_)) => return Err(refused(owner)),
            None => return Err(refused(owner)),
        };
        // The public model is name keyed. Distinct source identities sharing
        // one spelling cannot be represented faithfully by that carrier.
        for (index, binding) in bindings.iter().enumerate() {
            let source_name = name(terms, binding.source).ok_or_else(|| refused(owner))?;
            for earlier in &bindings[..index] {
                let earlier_name = name(terms, earlier.source).ok_or_else(|| refused(owner))?;
                owner
                    .admit(
                        source_name
                            .len()
                            .checked_add(earlier_name.len())
                            .ok_or_else(|| refused(owner))?,
                        0,
                    )
                    .map_err(|_| refused(owner))?;
                if binding.source != earlier.source && source_name == earlier_name {
                    return Err(refused(owner));
                }
            }
        }
        let mut leaves = Vec::new();
        reserve_counted(&mut leaves, bindings.len(), owner).map_err(|_| refused(owner))?;
        for binding in bindings.iter() {
            owner.admit(1, 0).map_err(|_| refused(owner))?;
            let representative =
                name(terms, binding.representative).ok_or_else(|| refused(owner))?;
            let value = if let Some(field) = binding.field {
                let Sort::BitVec(width) = terms.sort(binding.representative) else {
                    return Err(refused(owner));
                };
                if terms.sort(binding.source) != &Sort::FiniteField(field) {
                    return Err(refused(owner));
                }
                let (value, stored_width) = input
                    .bv_values
                    .get(representative)
                    .ok_or_else(|| refused(owner))?;
                // Inspect bounded encoding BEFORE any BigInt clone/conversion.
                if *stored_width != width.width
                    || value.sign() == num_bigint::Sign::Minus
                    || value.bits() > u64::from(width.width)
                {
                    return Err(refused(owner));
                }
                let value = value
                    .to_u32()
                    .filter(|v| *v < field.modulus())
                    .ok_or_else(|| refused(owner))?;
                ModelValue::FiniteField { value, field }
            } else {
                if terms.sort(binding.source) != &Sort::Bool
                    || binding.source != binding.representative
                {
                    return Err(refused(owner));
                }
                ModelValue::Bool(
                    *input
                        .bool_values
                        .get(representative)
                        .ok_or_else(|| refused(owner))?,
                )
            };
            leaves.push((binding.source, value));
        }
        let mut result = copy_scalar_model(terms, input, bindings, owner)?;
        for (id, value) in leaves {
            let name = name(terms, id).ok_or_else(|| refused(owner))?;
            owner
                .admit(name.len(), name.len())
                .map_err(|_| refused(owner))?;
            match value {
                ModelValue::Bool(v) => {
                    result.bool_values.insert(name.to_owned(), v);
                }
                ModelValue::FiniteField { .. } => {
                    result.field_values.insert(name.to_owned(), value);
                }
                _ => return Err(refused(owner)),
            }
        }
        struct View<'a> {
            bindings: &'a [Binding],
            terms: &'a TermStore,
            model: &'a Model,
            owner: &'a dyn TermConstructionAdmission,
        }
        impl ay_model_check::ModelView for View<'_> {
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
            fn leaf_value(&self, id: TermId) -> Option<ay_model_check::ModelValue> {
                self.owner
                    .admit(self.bindings.len(), std::mem::size_of::<u64>())
                    .ok()?;
                let binding = self.bindings.iter().find(|binding| binding.source == id)?;
                let key = name(self.terms, id)?;
                if let Some(field) = binding.field {
                    match self.model.field_values.get(key)? {
                        ModelValue::FiniteField {
                            value,
                            field: actual,
                        } if *actual == field && *value < field.modulus() => {
                            Some(ay_model_check::ModelValue::Int((*value).into()))
                        }
                        _ => None,
                    }
                } else {
                    self.model
                        .bool_values
                        .get(key)
                        .copied()
                        .map(ay_model_check::ModelValue::Bool)
                }
            }
        }
        let view = View {
            bindings,
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

fn validate_scalar_model(
    input: &Model,
    owner: &dyn TermConstructionAdmission,
) -> Result<(), TacticFailure> {
    validate_model(input, false, owner)
}

fn validate_model(
    input: &Model,
    arithmetic: bool,
    owner: &dyn TermConstructionAdmission,
) -> Result<(), TacticFailure> {
    // This scalar converter has no interpretation transport for functions,
    // arrays, strings, algebraic reals or FP. Refuse BEFORE copying any
    // candidate data rather than silently dropping those interpretations.
    if (!arithmetic && (!input.int_values.is_empty() || !input.real_values.is_empty()))
        || !input.string_values.is_empty()
        || !input.fp_values.is_empty()
        || !input.seq_values.is_empty()
        || !input.array_values.is_empty()
        || !input.datatype_values.is_empty()
        || !input.uninterpreted_values.is_empty()
    {
        return Err(refused(owner));
    }
    let scans = input
        .bool_values
        .capacity()
        .checked_add(input.field_values.capacity())
        .and_then(|n| n.checked_add(input.bv_values.capacity()))
        .ok_or_else(|| refused(owner))?;
    owner.admit(scans, 0).map_err(|_| refused(owner))?;
    for value in input.field_values.values() {
        if !matches!(value,ModelValue::FiniteField{value,field} if *value<field.modulus()) {
            return Err(refused(owner));
        }
    }
    for (value, width) in input.bv_values.values() {
        if *width == 0
            || value.sign() == num_bigint::Sign::Minus
            || value.bits() > u64::from(*width)
        {
            return Err(refused(owner));
        }
    }
    Ok(())
}

fn copy_scalar_model(
    terms: &TermStore,
    input: &Model,
    bindings: &[Binding],
    owner: &dyn TermConstructionAdmission,
) -> Result<Model, TacticFailure> {
    // Bound the native hashbrown tables before any bucket allocation. The
    // same native conservative growth envelope as counted registry maps
    // covers buckets, controls and rehash copies; no extra allowance.
    let count = input
        .bool_values
        .len()
        .checked_add(input.int_values.len())
        .and_then(|n| n.checked_add(input.real_values.len()))
        .and_then(|n| n.checked_add(input.field_values.len()))
        .and_then(|n| n.checked_add(input.bv_values.len()))
        .and_then(|n| n.checked_add(bindings.len()))
        .ok_or_else(|| refused(owner))?;
    let entries = count
        .checked_mul(std::mem::size_of::<(String, ModelValue)>())
        .and_then(|n| n.checked_mul(4))
        .and_then(|n| n.checked_add(if count == 0 { 0 } else { 4096 }))
        .ok_or_else(|| refused(owner))?;
    owner.admit(count, entries).map_err(|_| refused(owner))?;
    let mut result = Model::empty();
    result
        .int_values
        .try_reserve(input.int_values.len())
        .map_err(|_| refused(owner))?;
    result
        .real_values
        .try_reserve(input.real_values.len())
        .map_err(|_| refused(owner))?;
    owner
        .admit(
            input
                .int_values
                .capacity()
                .checked_add(input.real_values.capacity())
                .ok_or_else(|| refused(owner))?,
            0,
        )
        .map_err(|_| refused(owner))?;
    for (name, value) in &input.int_values {
        equations::price_integer(value, name.len(), owner)?;
        result.int_values.insert(name.clone(), value.clone());
    }
    for (name, value) in &input.real_values {
        equations::price_integer(value.numer(), name.len(), owner)?;
        equations::price_integer(value.denom(), 0, owner)?;
        result.real_values.insert(name.clone(), value.clone());
    }
    owner.admit(bindings.len(), 0).map_err(|_| refused(owner))?;
    let field_count = bindings
        .iter()
        .filter(|binding| binding.field.is_some())
        .count();
    let bool_count = bindings
        .len()
        .checked_sub(field_count)
        .ok_or_else(|| refused(owner))?;
    result
        .field_values
        .try_reserve(
            input
                .field_values
                .len()
                .checked_add(field_count)
                .ok_or_else(|| refused(owner))?,
        )
        .map_err(|_| refused(owner))?;
    result
        .bool_values
        .try_reserve(
            input
                .bool_values
                .len()
                .checked_add(bool_count)
                .ok_or_else(|| refused(owner))?,
        )
        .map_err(|_| refused(owner))?;
    result
        .bv_values
        .try_reserve(input.bv_values.len())
        .map_err(|_| refused(owner))?;
    for (name, value) in &input.bool_values {
        owner
            .admit(name.len(), name.len())
            .map_err(|_| refused(owner))?;
        result.bool_values.insert(name.clone(), *value);
    }
    for (name, value) in &input.field_values {
        owner
            .admit(name.len(), name.len())
            .map_err(|_| refused(owner))?;
        result.field_values.insert(name.clone(), value.clone());
    }
    for (name, (value, width)) in &input.bv_values {
        owner.admit(bindings.len(), 0).map_err(|_| refused(owner))?;
        // Remove only actual generated representatives, never unrelated BV
        // assignments supplied by the caller's model.
        if bindings.iter().any(|binding| {
            binding.field.is_some()
                && self::name(terms, binding.representative) == Some(name.as_str())
        }) {
            continue;
        }
        let words = usize::try_from(value.bits().div_ceil(32)).map_err(|_| refused(owner))?;
        let bytes = words
            .checked_mul(std::mem::size_of::<u64>())
            .and_then(|n| n.checked_add(name.len()))
            .ok_or_else(|| refused(owner))?;
        owner
            .admit(
                words
                    .checked_add(name.len())
                    .ok_or_else(|| refused(owner))?,
                bytes,
            )
            .map_err(|_| refused(owner))?;
        result
            .bv_values
            .insert(name.clone(), (value.clone(), *width));
    }
    owner.check().map_err(|_| refused(owner))?;
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::api::{Logic, Solver, Tactic};
    use ay_core::original_query::{CountedAdmission, FiniteAdmissionGrant};

    fn original() -> CountedAdmission {
        CountedAdmission::new(
            FiniteAdmissionGrant::new(20_000_000, 64 << 20),
            None,
            Arc::new(|| false),
        )
        .unwrap()
    }

    #[test]
    fn ff2bv_actual_solver_model_reconstructs_field_values_and_composes() {
        let mut solver = Solver::new(Logic::All);
        let field = ay_core::FiniteFieldSort::new(7).unwrap();
        let x = solver.declare_const("x", Sort::FiniteField(field));
        let y = solver.declare_const("y", Sort::FiniteField(field));
        let three = solver.finite_field_const(&3.into(), field);
        let two = solver.finite_field_const(&2.into(), field);
        let sum = solver.try_finite_field_app("ff.add", &[x, y]).unwrap();
        let roots = [solver.eq(x, three), solver.eq(sum, two)];
        let tactic = Tactic::FieldToBv.then(Tactic::FlattenAnd).repeat_up_to(2);
        let mut goals = solver
            .apply_tactic_subgoals_converted(&tactic, &roots, 0, None)
            .unwrap();
        assert_eq!(goals.len(), 1);
        let goal = goals.remove(0);
        assert!(goal.depth >= 2);
        solver
            .adopt_tactic_model_constants(goal.model_converter.as_ref().unwrap())
            .unwrap();
        for &root in &goal.formulas {
            solver.assert_term(root);
        }
        assert!(solver.check_sat().is_sat());
        let witness = solver.model().unwrap();
        let converted = solver
            .convert_tactic_model(goal.model_converter.as_ref().unwrap(), witness.model())
            .unwrap();
        assert_eq!(
            converted.finite_field_val("x"),
            Some(&ModelValue::FiniteField { value: 3, field })
        );
        assert_eq!(
            converted.finite_field_val("y"),
            Some(&ModelValue::FiniteField { value: 6, field })
        );
        assert!(!converted.names().any(|name| name.starts_with("@ay.ff2bv.")));
        let applied = solver
            .apply_tactic_subgoals_converted(
                &Tactic::Skip,
                &goal.formulas,
                goal.depth,
                goal.model_converter,
            )
            .unwrap();
        assert_eq!(applied[0].depth, goal.depth);
    }

    #[test]
    fn ff2bv_models_disabled_copies_encoded_data_without_reconstruction_or_verdict() {
        let mut solver = Solver::new(Logic::All);
        let field = ay_core::FiniteFieldSort::new(7).unwrap();
        let x = solver.declare_const("x", Sort::FiniteField(field));
        let three = solver.finite_field_const(&3.into(), field);
        let root = solver.eq(x, three);
        let goal = solver
            .apply_tactic_subgoals_converted(&Tactic::FieldToBv, &[root], 0, None)
            .unwrap()
            .remove(0);
        let converter = goal.model_converter.unwrap();
        let representative = name(solver.terms(), converter.bindings()[0].representative)
            .unwrap()
            .to_owned();
        let mut input = Model::empty();
        input
            .bv_values
            .insert(representative.clone(), (2.into(), 3));
        input
            .field_values
            .insert("x".into(), ModelValue::FiniteField { value: 4, field });
        assert!(solver.convert_tactic_model(&converter, &input).is_err());
        let operation = solver.begin_tactic_operation().unwrap();
        let copied = solver
            .copy_unconverted_tactic_model_in_operation(&operation, &converter, &input)
            .unwrap();
        assert_eq!(copied.field_values, input.field_values);
        assert_eq!(copied.bv_values, input.bv_values);
        assert!(copied.bv_values.contains_key(&representative));
    }

    #[test]
    fn ff2bv_contradictory_authored_field_roots_are_unsat_after_lowering() {
        let mut solver = Solver::new(Logic::All);
        let field = ay_core::FiniteFieldSort::new(7).unwrap();
        let x = solver.declare_const("x", Sort::FiniteField(field));
        let three = solver.finite_field_const(&3.into(), field);
        let four = solver.finite_field_const(&4.into(), field);
        let roots = [solver.eq(x, three), solver.eq(x, four)];
        let goal = solver
            .apply_tactic_subgoals_converted(&Tactic::FieldToBv, &roots, 0, None)
            .unwrap()
            .remove(0);
        solver
            .adopt_tactic_model_constants(goal.model_converter.as_ref().unwrap())
            .unwrap();
        for root in goal.formulas {
            solver.assert_term(root);
        }
        assert!(solver.check_sat().is_unsat());
    }

    #[test]
    fn ff2bv_name_keyed_output_refuses_distinct_same_spelling_source_leaves() {
        let mut solver = Solver::new(Logic::All);
        let field = ay_core::FiniteFieldSort::new(7).unwrap();
        let a = solver
            .terms_mut()
            .mk_fresh_named_var("ambiguous", Sort::FiniteField(field));
        let b = solver
            .terms_mut()
            .mk_fresh_named_var("ambiguous", Sort::FiniteField(field));
        let a = solver.wrap_term(a);
        let b = solver.wrap_term(b);
        let three = solver.finite_field_const(&3.into(), field);
        let four = solver.finite_field_const(&4.into(), field);
        let roots = [solver.eq(a, three), solver.eq(b, four)];
        let goal = solver
            .apply_tactic_subgoals_converted(&Tactic::FieldToBv, &roots, 0, None)
            .unwrap()
            .remove(0);
        let converter = goal.model_converter.unwrap();
        let mut candidate = Model::empty();
        for binding in converter.bindings() {
            let value = if binding.source == a.id() { 3 } else { 4 };
            candidate.bv_values.insert(
                name(solver.terms(), binding.representative)
                    .unwrap()
                    .to_owned(),
                (value.into(), 3),
            );
        }
        // Both TermId-based source equations have witnesses, but one public
        // name-keyed map cannot represent their different interpretations.
        assert!(solver.convert_tactic_model(&converter, &candidate).is_err());
    }

    #[test]
    fn ff2bv_closed_goals_still_replay_the_actual_empty_model() {
        let mut solver = Solver::new(Logic::All);
        for expected in [true, false] {
            let root = solver.bool_const(expected);
            let goal = solver
                .apply_tactic_subgoals_converted(&Tactic::FieldToBv, &[root], 0, None)
                .unwrap()
                .remove(0);
            let converted = solver
                .convert_tactic_model(goal.model_converter.as_ref().unwrap(), &Model::empty());
            assert_eq!(converted.is_ok(), expected);
        }
    }

    #[test]
    fn ff2bv_later_user_declaration_cannot_claim_generated_identity() {
        let mut solver = Solver::new(Logic::All);
        let field = ay_core::FiniteFieldSort::new(7).unwrap();
        let x = solver.declare_const("x", Sort::FiniteField(field));
        let three = solver.finite_field_const(&3.into(), field);
        let root = solver.eq(x, three);
        let goal = solver
            .apply_tactic_subgoals_converted(&Tactic::FieldToBv, &[root], 0, None)
            .unwrap()
            .remove(0);
        let converter = goal.model_converter.unwrap();
        let binding = converter.bindings()[0];
        let rep = name(solver.terms(), binding.representative)
            .unwrap()
            .to_owned();
        let mut candidate = Model::empty();
        candidate.bv_values.insert(rep.clone(), (3.into(), 3));
        assert!(solver.convert_tactic_model(&converter, &candidate).is_ok());
        // The user adopts this spelling through the public declaration path;
        // equal bytes/sort do not confer our exact declaration receipt.
        solver.bv_var(&rep, 3);
        assert!(solver.convert_tactic_model(&converter, &candidate).is_err());
        assert!(solver.adopt_tactic_model_constants(&converter).is_err());
    }

    #[test]
    fn ff2bv_large_prime_product_uses_exact_double_width_before_reduction() {
        let mut solver = Solver::new(Logic::All);
        let field = ay_core::FiniteFieldSort::new(4_294_967_291).unwrap();
        let x = solver.declare_const("x", Sort::FiniteField(field));
        let y = solver.declare_const("y", Sort::FiniteField(field));
        let a = solver.finite_field_const(&(field.modulus() - 1).into(), field);
        let b = solver.finite_field_const(&(field.modulus() - 2).into(), field);
        let two = solver.finite_field_const(&2.into(), field);
        let product = solver.try_finite_field_app("ff.mul", &[x, y]).unwrap();
        let roots = [solver.eq(x, a), solver.eq(y, b), solver.eq(product, two)];
        let goal = solver
            .apply_tactic_subgoals_converted(&Tactic::FieldToBv, &roots, 0, None)
            .unwrap()
            .remove(0);
        let converter = goal.model_converter.as_ref().unwrap();
        let mut candidate = Model::empty();
        for binding in converter.bindings().iter() {
            let value = if binding.source == x.id() {
                field.modulus() - 1
            } else {
                field.modulus() - 2
            };
            candidate.bv_values.insert(
                name(solver.terms(), binding.representative)
                    .unwrap()
                    .to_owned(),
                (value.into(), 32),
            );
        }
        struct BvView<'a> {
            terms: &'a TermStore,
            model: &'a Model,
        }
        impl ay_model_check::ModelView for BvView<'_> {
            fn leaf_value(&self, id: TermId) -> Option<ay_model_check::ModelValue> {
                let (value, width) = self.model.bv_values.get(name(self.terms, id)?)?;
                Some(ay_model_check::ModelValue::BitVec {
                    value: value.clone(),
                    width: *width,
                })
            }
        }
        let ids: Vec<_> = goal.formulas.iter().map(|term| term.id()).collect();
        assert!(matches!(
            ay_model_check::confirm_completed_model(
                solver.terms(),
                &BvView {
                    terms: solver.terms(),
                    model: &candidate
                },
                &ids
            ),
            ay_model_check::GateVerdict::ConfirmedSat
        ));
        let converted = solver.convert_tactic_model(converter, &candidate).unwrap();
        assert_eq!(
            converted.finite_field_val("x"),
            Some(&ModelValue::FiniteField {
                value: field.modulus() - 1,
                field
            })
        );
    }

    #[test]
    fn ff2bv_reconstruction_rejects_forged_missing_out_of_range_and_foreign_witnesses() {
        let mut solver = Solver::new(Logic::All);
        let field = ay_core::FiniteFieldSort::new(7).unwrap();
        let x = solver.declare_const("x", Sort::FiniteField(field));
        let three = solver.finite_field_const(&3.into(), field);
        let root = solver.eq(x, three);
        let goal = solver
            .apply_tactic_subgoals_converted(&Tactic::FieldToBv, &[root], 0, None)
            .unwrap()
            .remove(0);
        let converter = goal.model_converter.unwrap();
        let binding = converter.bindings()[0];
        let representative = name(solver.terms(), binding.representative)
            .unwrap()
            .to_owned();
        let mut candidate = Model::empty();
        assert!(solver.convert_tactic_model(&converter, &candidate).is_err());
        for value in [2, 7] {
            candidate
                .bv_values
                .insert(representative.clone(), (value.into(), 3));
            assert!(solver.convert_tactic_model(&converter, &candidate).is_err());
        }
        candidate.bv_values.insert(representative, (3.into(), 3));
        candidate
            .bool_values
            .insert("unrelated_boolean".into(), true);
        candidate
            .bv_values
            .insert("unrelated_bv".into(), (1.into(), 1_000_000));
        candidate.field_values.insert(
            "unrelated_field".into(),
            ModelValue::FiniteField { value: 4, field },
        );
        let converted = solver.convert_tactic_model(&converter, &candidate).unwrap();
        assert_eq!(converted.bool_val("unrelated_boolean"), Some(true));
        assert_eq!(
            converted.bv_val("unrelated_bv"),
            Some((1.into(), 1_000_000))
        );
        assert_eq!(
            converted.finite_field_val("unrelated_field"),
            candidate.finite_field_val("unrelated_field")
        );
        let foreign = Solver::new(Logic::All);
        assert!(foreign
            .convert_tactic_model(&converter, &candidate)
            .is_err());
        candidate.int_values.insert("unsupported".into(), 1.into());
        assert!(solver.convert_tactic_model(&converter, &candidate).is_err());
    }

    #[test]
    fn ff2bv_native_ite_rejects_different_fields_with_the_same_bv_width() {
        let owner = original();
        let f = ay_core::FiniteFieldSort::new(5).unwrap();
        let g = ay_core::FiniteFieldSort::new(7).unwrap();
        let entries = |other| {
            vec![
                (TermData::Var("condition".into(), 0), Sort::Bool),
                (
                    TermData::Const(ay_core::Constant::FiniteField { value: 1, field: f }),
                    Sort::FiniteField(f),
                ),
                (
                    TermData::Const(ay_core::Constant::FiniteField {
                        value: 1,
                        field: other,
                    }),
                    Sort::FiniteField(other),
                ),
                (
                    TermData::Ite(TermId(0), TermId(1), TermId(2)),
                    Sort::FiniteField(f),
                ),
                (
                    TermData::App(Symbol::Named("=".into()), vec![TermId(3), TermId(1)]),
                    Sort::Bool,
                ),
            ]
        };
        // A real checker-only snapshot can carry malformed native Ite DATA.
        // Exercise the SAME production preflight before its producer builder,
        // distinguishing type refusal from blanket read-only construction refusal.
        let valid = TermStore::from_entries(entries(f), None, None, 1);
        let invalid = TermStore::from_entries(entries(g), None, None, 1);
        assert!(super::super::field_to_bv::reachable_nodes(&valid, &[TermId(4)], &owner).is_ok());
        assert!(
            super::super::field_to_bv::reachable_nodes(&invalid, &[TermId(4)], &owner).is_err()
        );
    }

    #[test]
    fn ff2bv_original_owner_stops_before_dense_metadata_and_never_renews() {
        let owner =
            CountedAdmission::new(FiniteAdmissionGrant::new(1, 1), None, Arc::new(|| false))
                .unwrap();
        let mut terms = TermStore::new();
        let root = terms.mk_bool(true);
        let stamp = terms.snapshot_stamp();
        assert!(
            super::super::field_to_bv::encode(&mut terms, &[root], std::iter::empty(), &owner)
                .is_err()
        );
        assert!(
            super::super::field_to_bv::encode(&mut terms, &[root], std::iter::empty(), &owner)
                .is_err()
        );
        assert_eq!(terms.snapshot_stamp(), stamp);
    }

    #[test]
    fn ff2bv_retained_adapter_operation_cannot_renew_or_cross_context() {
        let mut solver = Solver::new(Logic::All);
        let yes = solver.bool_const(true);
        let operation = solver.begin_tactic_operation().unwrap();
        let stamp = solver.terms().snapshot_stamp();
        assert!(operation.admission().admit(usize::MAX, 0).is_err());
        assert!(solver
            .apply_tactic_subgoals_in_operation(&operation, &Tactic::FieldToBv, &[yes], 0, None)
            .is_err());
        assert!(solver.begin_tactic_operation().is_err());
        assert_eq!(solver.terms().snapshot_stamp(), stamp);
        drop(operation);
        assert!(solver
            .apply_tactic_subgoals_converted(&Tactic::FieldToBv, &[yes], 0, None)
            .is_ok());
        let operation = solver.begin_tactic_operation().unwrap();
        let mut foreign = Solver::new(Logic::All);
        let foreign_yes = foreign.bool_const(true);
        assert!(foreign
            .apply_tactic_subgoals_in_operation(
                &operation,
                &Tactic::FieldToBv,
                &[foreign_yes],
                0,
                None
            )
            .is_err());
    }

    #[test]
    fn ff2bv_owned_composite_refuses_unowned_legacy_work_before_mutating_terms() {
        let mut solver = Solver::new(Logic::All);
        let a = solver.declare_const("a", Sort::Bool);
        let b = solver.declare_const("b", Sort::Bool);
        let formula = solver.or(a, b);
        let stamp = solver.terms().snapshot_stamp();
        let tactic = Tactic::TseitinCnf.then(Tactic::FieldToBv);
        assert!(solver
            .apply_tactic_subgoals_converted(&tactic, &[formula], 0, None)
            .is_err());
        assert_eq!(solver.terms().snapshot_stamp(), stamp);
        let tactic = Tactic::Fail.or_else(Tactic::FieldToBv).repeat_up_to(2);
        assert!(solver
            .apply_tactic_subgoals_converted(&tactic, &[formula], 0, None)
            .is_ok());
    }
}
