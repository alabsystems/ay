// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Fixed field witnesses are source-bound DATA, never solver/proof authority.
use super::*;
use ay_core::term::reserve_map_counted;
type Row = (TermId, u32, ay_core::FiniteFieldSort);
#[derive(Debug)]
pub(super) struct Witness {
    fields: Vec<Row>,
    booleans: Vec<(TermId, bool)>,
}
impl Witness {
    fn ids(&self) -> impl Iterator<Item = TermId> + Clone + '_ {
        self.fields
            .iter()
            .map(|row| row.0)
            .chain(self.booleans.iter().map(|row| row.0))
    }
    fn len(&self) -> usize {
        self.fields.len() + self.booleans.len()
    }
}

impl TacticModelConverter {
    pub(in crate::api::solving) fn fixed_field(
        &self,
        terms: &TermStore,
        rows: Vec<Row>,
        roots: &[TermId],
        owner: &dyn TermConstructionAdmission,
    ) -> Result<Self, TacticFailure> {
        self.fixed_boolean_field(terms, rows, Vec::new(), roots, owner)
    }

    pub(in crate::api::solving) fn fixed_boolean_field(
        &self,
        terms: &TermStore,
        rows: Vec<Row>,
        booleans: Vec<(TermId, bool)>,
        roots: &[TermId],
        owner: &dyn TermConstructionAdmission,
    ) -> Result<Self, TacticFailure> {
        if !self.valid(terms) || self.is_active() {
            return Err(refused(owner));
        }
        // Validate field IDs before cross-family name comparisons below.
        for &(id, value, field) in &rows {
            owner.admit(1, 0).map_err(|_| refused(owner))?;
            if id.index() >= terms.len()
                || terms.sort(id) != &Sort::FiniteField(field)
                || value >= field.modulus()
                || !matches!(terms.get(id), TermData::Var(..))
            {
                return Err(refused(owner));
            }
        }
        for (index, &(id, _)) in booleans.iter().enumerate() {
            owner
                .admit(index + rows.len() + 1, 0)
                .map_err(|_| refused(owner))?;
            if id.index() >= terms.len()
                || terms.sort(id) != &Sort::Bool
                || !matches!(terms.get(id), TermData::Var(..))
                || booleans[..index].iter().any(|row| row.0 == id)
                || rows.iter().any(|row| row.0 == id)
            {
                return Err(refused(owner));
            }
            let key = name(terms, id).ok_or_else(|| refused(owner))?;
            let mut declared = false;
            for captured in &self.source.namespace {
                owner
                    .admit(
                        key.len()
                            .checked_add(captured.name.len())
                            .and_then(|n| n.checked_add(1))
                            .ok_or_else(|| refused(owner))?,
                        0,
                    )
                    .map_err(|_| refused(owner))?;
                declared |= captured.name == key && captured.term == Some(id);
            }
            if !declared {
                return Err(refused(owner));
            }
            for earlier in rows
                .iter()
                .map(|r| r.0)
                .chain(booleans[..index].iter().map(|r| r.0))
            {
                let other = name(terms, earlier).ok_or_else(|| refused(owner))?;
                owner
                    .admit(
                        key.len()
                            .checked_add(other.len())
                            .and_then(|n| n.checked_add(1))
                            .ok_or_else(|| refused(owner))?,
                        0,
                    )
                    .map_err(|_| refused(owner))?;
                if key == other {
                    return Err(refused(owner));
                }
            }
        }
        for (index, &(id, value, field)) in rows.iter().enumerate() {
            owner.admit(index + 1, 0).map_err(|_| refused(owner))?;
            if id.index() >= terms.len()
                || terms.sort(id) != &Sort::FiniteField(field)
                || value >= field.modulus()
                || !matches!(terms.get(id), TermData::Var(..))
                || rows[..index].iter().any(|row| row.0 == id)
            {
                return Err(refused(owner));
            }
            let key = name(terms, id).ok_or_else(|| refused(owner))?;
            let mut declared = false;
            for captured in &self.source.namespace {
                owner
                    .admit(
                        key.len()
                            .checked_add(captured.name.len())
                            .and_then(|n| n.checked_add(1))
                            .ok_or_else(|| refused(owner))?,
                        0,
                    )
                    .map_err(|_| refused(owner))?;
                declared |= captured.name == key && captured.term == Some(id);
            }
            if !declared {
                return Err(refused(owner));
            }
            for earlier in &rows[..index] {
                let other = name(terms, earlier.0).ok_or_else(|| refused(owner))?;
                owner
                    .admit(
                        key.len()
                            .checked_add(other.len())
                            .and_then(|n| n.checked_add(1))
                            .ok_or_else(|| refused(owner))?,
                        0,
                    )
                    .map_err(|_| refused(owner))?;
                if key == other {
                    return Err(refused(owner));
                }
            }
        }
        owner
            .admit(
                1,
                std::mem::size_of::<Witness>() + 2 * std::mem::size_of::<usize>(),
            )
            .map_err(|_| refused(owner))?;
        let result = Self {
            source: Arc::clone(&self.source),
            reconstruction: Some(Reconstruction::Fixed(Arc::new(Witness {
                fields: rows,
                booleans,
            }))),
        };
        // Confirm the ORIGINAL authored roots before an empty goal can escape.
        // The retained witness is checked again against the actual converted
        // model on every later model-conversion request.
        let model = result.convert(terms, &Model::empty(), owner)?;
        let Some(Reconstruction::Fixed(rows)) = &result.reconstruction else {
            return Err(refused(owner));
        };
        confirm(terms, &model, rows, roots, owner)?;
        owner.check().map_err(|_| refused(owner))?;
        Ok(result)
    }

    pub(super) fn check_fixed_namespace<'a>(
        &self,
        terms: &TermStore,
        rows: &Witness,
        names: impl Iterator<Item = (&'a String, &'a ay_frontend::SymbolInfo)>,
        owner: &dyn TermConstructionAdmission,
    ) -> Result<(), TacticFailure> {
        let mut present = Vec::new();
        reserve_counted(&mut present, rows.len(), owner).map_err(|_| refused(owner))?;
        owner.admit(rows.len(), 0).map_err(|_| refused(owner))?;
        present.resize(rows.len(), false);
        for (surface, info) in names {
            owner.admit(1, 0).map_err(|_| refused(owner))?;
            for current in std::iter::once(surface).chain(info.internal_name.as_ref()) {
                owner
                    .admit(
                        current.len().checked_add(1).ok_or_else(|| refused(owner))?,
                        0,
                    )
                    .map_err(|_| refused(owner))?;
                for (index, id) in rows.ids().enumerate() {
                    let original = name(terms, id).ok_or_else(|| refused(owner))?;
                    owner
                        .admit(
                            current
                                .len()
                                .checked_add(original.len())
                                .and_then(|n| n.checked_add(1))
                                .ok_or_else(|| refused(owner))?,
                            0,
                        )
                        .map_err(|_| refused(owner))?;
                    if current == original {
                        let mut matched = false;
                        for captured in &self.source.namespace {
                            owner
                                .admit(
                                    current
                                        .len()
                                        .checked_add(captured.name.len())
                                        .and_then(|n| n.checked_add(1))
                                        .ok_or_else(|| refused(owner))?,
                                    0,
                                )
                                .map_err(|_| refused(owner))?;
                            matched |= captured.name == *current
                                && captured.term == Some(id)
                                && info.term == Some(id)
                                && captured.declaration == *info.declaration_identity();
                        }
                        if !matched {
                            return Err(refused(owner));
                        }
                        present[index] = true;
                    }
                }
            }
        }
        owner.admit(present.len(), 0).map_err(|_| refused(owner))?;
        if present.iter().any(|found| !*found) {
            return Err(refused(owner));
        }
        owner.check().map_err(|_| refused(owner))
    }

    pub(super) fn convert_fixed(
        &self,
        terms: &TermStore,
        input: &Model,
        rows: &Witness,
        owner: &dyn TermConstructionAdmission,
    ) -> Result<Model, TacticFailure> {
        let mut result = copy_scalar_model(terms, input, &[], owner)?;
        reserve_map_counted(&mut result.field_values, rows.fields.len(), owner)
            .map_err(|_| refused(owner))?;
        for &(id, value, field) in &rows.fields {
            owner.admit(1, 0).map_err(|_| refused(owner))?;
            if id.index() >= terms.len()
                || terms.sort(id) != &Sort::FiniteField(field)
                || value >= field.modulus()
            {
                return Err(refused(owner));
            }
            let key = name(terms, id).ok_or_else(|| refused(owner))?;
            let value = ModelValue::FiniteField { value, field };
            owner
                .admit(key.len(), key.len())
                .map_err(|_| refused(owner))?;
            if input
                .field_values
                .get(key)
                .is_some_and(|existing| *existing != value)
            {
                return Err(refused(owner));
            }
            result.field_values.insert(key.to_owned(), value);
        }
        reserve_map_counted(&mut result.bool_values, rows.booleans.len(), owner)
            .map_err(|_| refused(owner))?;
        for &(id, value) in &rows.booleans {
            owner.admit(1, 0).map_err(|_| refused(owner))?;
            if id.index() >= terms.len() || terms.sort(id) != &Sort::Bool {
                return Err(refused(owner));
            }
            let key = name(terms, id).ok_or_else(|| refused(owner))?;
            owner
                .admit(key.len(), key.len())
                .map_err(|_| refused(owner))?;
            if input.bool_values.get(key).is_some_and(|old| *old != value) {
                return Err(refused(owner));
            }
            result.bool_values.insert(key.to_owned(), value);
        }
        confirm(terms, &result, rows, &self.source.roots, owner)?;
        Ok(result)
    }
}
fn confirm(
    terms: &TermStore,
    result: &Model,
    rows: &Witness,
    roots: &[TermId],
    owner: &dyn TermConstructionAdmission,
) -> Result<(), TacticFailure> {
    struct View<'a> {
        terms: &'a TermStore,
        rows: &'a Witness,
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
            self.owner.admit(self.rows.len(), 0).ok()?;
            let key = name(self.terms, id)?;
            self.owner.admit(key.len(), 0).ok()?;
            if self.rows.booleans.iter().any(|row| row.0 == id) {
                return self
                    .model
                    .bool_values
                    .get(key)
                    .map(|value| ay_model_check::ModelValue::Bool(*value));
            }
            let &(_, _, field) = self.rows.fields.iter().find(|row| row.0 == id)?;
            self.owner.admit(1, std::mem::size_of::<u64>()).ok()?;
            match self.model.field_values.get(key)? {
                ModelValue::FiniteField {
                    value,
                    field: actual,
                } if *actual == field && *value < field.modulus() => {
                    Some(ay_model_check::ModelValue::Int((*value).into()))
                }
                _ => None,
            }
        }
    }
    let view = View {
        terms,
        rows,
        model: result,
        owner,
    };
    if !matches!(
        ay_model_check::confirm_completed_model(terms, &view, roots),
        ay_model_check::GateVerdict::ConfirmedSat
    ) {
        return Err(refused(owner));
    }
    owner.check().map_err(|_| refused(owner))?;
    Ok(())
}
