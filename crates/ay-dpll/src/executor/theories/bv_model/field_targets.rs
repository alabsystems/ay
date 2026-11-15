// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Datatype-field substitution targets (#dt-field-subst-target).
//!
//! A declared datatype constant `z` elaborates to its constructor
//! `(mk z!ptr z!len z!dat)`; with `z = (select A i)` asserted, preprocessing
//! eliminates the field variable `z!dat := (dat (select A i))`. The eager
//! AUFBV lane bit-blasts that selector application as an opaque array base, so
//! its committed reads are live model evidence. Substitution recovery resolved
//! only variable, const-array and store targets, so `z!dat` stayed withheld
//! (read-conflicted, `43455aaf1`) and unpinned; the W6 inventory then declined
//! the datatype class (its constructor source `z!dat` would not materialize)
//! and every DT round of
//! `dt_array_field_model_witness::datatype_array_field_select_congruence_certifies`
//! ended on `arrays-read-conflict-uneval` over the generated identity
//! `(= z!dat (dat (mk z!ptr z!len z!dat)))`.
//!
//! This module publishes such a target's own committed reads before
//! `populate_array_models_from_substitutions` runs, and resolves the target to
//! exactly that published entry (the fallback arm of
//! `resolve_substitution_target_interp`). Nothing here is SAT authority: the W6
//! certificate and the strict and independent gates still re-check every
//! assertion against the completed model.
//!
//! Recovering `z!dat` is necessary but not sufficient for that test: the
//! congruent read `(select A j)` must also share the cell's carrier, or W6
//! builds it a second, partial class
//! (`model/completion/select_congruence.rs`, #carrier-select-congruence).

use super::*;

impl Executor {
    /// [`Self::populate_array_models_from_substitutions`], after first
    /// publishing every datatype-field target
    /// ([`Self::extract_datatype_field_target_arrays`]) against this
    /// executor's exact datatype-selector declarations (the same identity
    /// check the W6 inventory uses for selector applications).
    pub(in crate::executor) fn populate_array_models_with_field_targets(
        &self,
        bv_model: &BvModel,
        array_substitutions: &[(TermId, TermId)],
        substituted_vars: &HashSet<TermId>,
        array_model: &mut ArrayModel,
    ) {
        Self::extract_datatype_field_target_arrays(
            &self.ctx.terms,
            bv_model,
            array_substitutions,
            substituted_vars,
            |name| {
                self.ctx
                    .exact_datatype_member_info(name)
                    .is_some_and(|info| {
                        info.declaration_kind() == ay_frontend::DeclarationKind::DatatypeSelector
                    })
            },
            array_model,
        );
        Self::populate_array_models_from_substitutions(
            &self.ctx.terms,
            bv_model,
            array_substitutions,
            array_model,
        );
    }

    /// Publish, under the target term itself, the interpretation the extractor
    /// gives a variable base -- canonical default plus every committed read --
    /// for each array substitution whose target is a DATATYPE-FIELD read.
    ///
    /// Fail-closed: only a unary datatype-SELECTOR application over BV indices
    /// and BV/Bool elements qualifies; the target must mention no eliminated
    /// variable (its reads are then the live post-substitution bits, never a
    /// decoupled cache); an existing entry is never overwritten; and a target
    /// whose committed reads are incomplete or disagree on one cell publishes
    /// nothing (see [`Self::field_target_interp`]).
    fn extract_datatype_field_target_arrays(
        terms: &TermStore,
        bv_model: &BvModel,
        array_substitutions: &[(TermId, TermId)],
        substituted_vars: &HashSet<TermId>,
        is_datatype_selector: impl Fn(&str) -> bool,
        array_model: &mut ArrayModel,
    ) {
        let mut targets: HashMap<TermId, Vec<(TermId, TermId)>> = HashMap::default();
        for &(from_var, to_term) in array_substitutions {
            let (TermData::App(symbol, args), Sort::Array(sort)) =
                (terms.get(to_term), terms.sort(to_term))
            else {
                continue;
            };
            if args.len() == 1
                && terms.sort(from_var) == terms.sort(to_term)
                && matches!(sort.index_sort, Sort::BitVec(_))
                && matches!(sort.element_sort, Sort::BitVec(_) | Sort::Bool)
                && !array_model.array_values.contains_key(&to_term)
                && is_datatype_selector(symbol.name())
                && !Self::term_mentions_any_var(terms, to_term, substituted_vars)
            {
                targets.entry(to_term).or_default();
            }
        }
        if targets.is_empty() {
            return;
        }
        for &read in bv_model.values.keys().chain(bv_model.bool_overrides.keys()) {
            if let TermData::App(symbol, args) = terms.get(read) {
                if symbol.name() == "select" && args.len() == 2 {
                    if let Some(reads) = targets.get_mut(&args[0]) {
                        reads.push((args[1], read));
                    }
                }
            }
        }
        for (target, reads) in targets {
            match Self::field_target_interp(terms, bv_model, target, &reads, substituted_vars) {
                Ok(Some(interp)) => {
                    array_model.array_values.insert(target, interp);
                }
                Ok(None) => {}
                Err(()) => {
                    // A contradictory committed read is a protected failure,
                    // not a removable pending-definition latch. Substitution
                    // recovery propagates this reason to every alias source.
                    array_model.read_conflicted.insert(target);
                }
            }
        }
    }

    /// Fallback resolution arm of `resolve_substitution_target_interp`: a
    /// unary application target resolves to exactly the entry
    /// [`Self::extract_datatype_field_target_arrays`] published for it, and
    /// anything else to `None`. The extractor keys only variable bases, so
    /// that is the only producer of an application-keyed entry before
    /// substitution recovery. A compound target never receives a minted
    /// default.
    pub(super) fn published_field_target_interp(
        terms: &TermStore,
        to_term: TermId,
        array_model: &ArrayModel,
    ) -> Option<ArrayInterpretation> {
        let (TermData::App(_, args), Sort::Array(sort)) = (terms.get(to_term), terms.sort(to_term))
        else {
            return None;
        };
        if args.len() != 1 {
            return None;
        }
        let interp = array_model.array_values.get(&to_term)?;
        (interp.index_sort.as_ref() == Some(&sort.index_sort)
            && interp.element_sort.as_ref() == Some(&sort.element_sort)
            && interp.default.is_some())
        .then(|| interp.clone())
    }

    /// One target's interpretation from its committed reads. A read whose
    /// index mentions an eliminated variable is decoupled junk and is skipped
    /// (its post-substitution counterpart supplies the pair), exactly as in
    /// `extract_array_model_from_bv_model`; an unresolved index or value, or
    /// two committed reads of one cell that disagree never invents a default.
    /// Missing data is `Ok(None)`; an observed disagreement is a protected Err.
    fn field_target_interp(
        terms: &TermStore,
        bv_model: &BvModel,
        target: TermId,
        reads: &[(TermId, TermId)],
        substituted_vars: &HashSet<TermId>,
    ) -> Result<Option<ArrayInterpretation>, ()> {
        let Sort::Array(sort) = terms.sort(target) else {
            return Ok(None);
        };
        let Sort::BitVec(index_bv) = &sort.index_sort else {
            return Ok(None);
        };
        let default = match &sort.element_sort {
            Sort::BitVec(element_bv) => format_bitvec(&BigInt::from(0u8), element_bv.width),
            Sort::Bool => "false".to_string(),
            _ => return Ok(None),
        };
        let mut cells: HashMap<String, String> = HashMap::default();
        for &(index, read) in reads {
            if Self::term_mentions_any_var(terms, index, substituted_vars) {
                continue;
            }
            let Some(index_value) = bv_model
                .values
                .get(&index)
                .cloned()
                .or_else(|| Self::evaluate_bv_expr(terms, index, &bv_model.values))
            else {
                return Ok(None);
            };
            let value = match &sort.element_sort {
                Sort::BitVec(element_bv) => bv_model
                    .values
                    .get(&read)
                    .cloned()
                    .or_else(|| Self::evaluate_bv_expr(terms, read, &bv_model.values))
                    .map(|value| format_bitvec(&value, element_bv.width)),
                _ => bv_model.bool_overrides.get(&read).map(bool::to_string),
            };
            let Some(value) = value else {
                return Ok(None);
            };
            let key = format_bitvec(&index_value, index_bv.width);
            if cells.get(&key).is_some_and(|previous| *previous != value) {
                return Err(());
            }
            cells.insert(key, value);
        }
        let mut stores: Vec<(String, String)> = cells.into_iter().collect();
        stores.sort();
        Ok(Some(ArrayInterpretation {
            index_sort: Some(sort.index_sort.clone()),
            element_sort: Some(sort.element_sort.clone()),
            default: Some(default),
            stores,
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::term::Symbol;

    fn empty_bits() -> BvModel {
        BvModel {
            values: HashMap::default(),
            bool_overrides: HashMap::default(),
            term_to_bits: HashMap::default(),
        }
    }

    fn cell(interp: &ArrayInterpretation, index: &str) -> String {
        interp
            .stores
            .iter()
            .find(|(key, _)| key == index)
            .map(|(_, value)| value.clone())
            .or_else(|| interp.default.clone())
            .expect("complete interpretation")
    }

    struct Fixture {
        terms: TermStore,
        field: TermId,
        eliminated: TermId,
        bits: BvModel,
    }

    /// `z!dat := (dat c)` with committed reads `#x00 -> #x11`, `#x05 -> #x22`.
    fn fixture() -> Fixture {
        let mut terms = TermStore::new();
        let array_sort = Sort::array(Sort::bitvec(8), Sort::bitvec(8));
        let slice = terms.mk_var("c", Sort::Uninterpreted("Slice".to_string()));
        let field = terms.mk_app(Symbol::named("dat"), vec![slice], array_sort.clone());
        let eliminated = terms.mk_var("z!dat", array_sort);
        let zero = terms.mk_bitvec(BigInt::from(0u8), 8);
        let five = terms.mk_bitvec(BigInt::from(5u8), 8);
        let read_zero = terms.mk_select(field, zero);
        let read_five = terms.mk_select(field, five);
        let mut bits = empty_bits();
        bits.values.insert(read_zero, BigInt::from(0x11u8));
        bits.values.insert(read_five, BigInt::from(0x22u8));
        Fixture {
            terms,
            field,
            eliminated,
            bits,
        }
    }

    fn recover(fixture: &Fixture, selector: &str) -> ArrayModel {
        recover_with(fixture, selector, fixture.field, &[])
    }

    /// [`recover`] for an explicit `target`, with `also_eliminated` added to
    /// the substituted-variable set.
    fn recover_with(
        fixture: &Fixture,
        selector: &str,
        target: TermId,
        also_eliminated: &[TermId],
    ) -> ArrayModel {
        let substitutions = [(fixture.eliminated, target)];
        let mut substituted = HashSet::default();
        substituted.insert(fixture.eliminated);
        substituted.extend(also_eliminated.iter().copied());
        let mut arrays = ArrayModel::default();
        Executor::extract_datatype_field_target_arrays(
            &fixture.terms,
            &fixture.bits,
            &substitutions,
            &substituted,
            |name| name == selector,
            &mut arrays,
        );
        Executor::populate_array_models_from_substitutions(
            &fixture.terms,
            &fixture.bits,
            &substitutions,
            &mut arrays,
        );
        arrays
    }

    /// RED before this module: the eliminated field variable stayed withheld
    /// because no resolution arm covered a selector-application target.
    #[test]
    fn datatype_field_target_recovers_exactly_its_committed_reads() {
        let fixture = fixture();
        let arrays = recover(&fixture, "dat");
        assert!(!arrays.is_withheld(&fixture.eliminated));
        let interp = &arrays.array_values[&fixture.eliminated];
        assert_eq!(cell(interp, "#x00"), "#x11");
        assert_eq!(cell(interp, "#x05"), "#x22");
        assert_eq!(cell(interp, "#x07"), "#x00");
    }

    #[test]
    fn non_selector_application_target_stays_withheld() {
        let fixture = fixture();
        let arrays = recover(&fixture, "not_a_selector");
        assert!(arrays.is_withheld(&fixture.eliminated));
        assert_eq!(
            arrays.pending_definitions[&fixture.eliminated].target(),
            fixture.field,
        );
        assert!(!arrays.array_values.contains_key(&fixture.field));
    }

    /// Two committed reads of one cell that disagree are not an
    /// interpretation: nothing is published and the variable stays withheld.
    #[test]
    fn disagreeing_field_reads_publish_nothing() {
        let mut fixture = fixture();
        let index = fixture.terms.mk_var("k", Sort::bitvec(8));
        let clash = fixture.terms.mk_select(fixture.field, index);
        fixture.bits.values.insert(index, BigInt::from(0u8));
        fixture.bits.values.insert(clash, BigInt::from(0x33u8));
        let arrays = recover(&fixture, "dat");
        assert!(arrays.read_conflicted.contains(&fixture.eliminated));
        assert!(arrays.read_conflicted.contains(&fixture.field));
        assert!(!arrays.pending_definitions.contains_key(&fixture.eliminated));
        assert!(!arrays.array_values.contains_key(&fixture.field));
    }

    /// A target over an eliminated variable has only decoupled bits
    /// (`43455aaf1`): nothing is published and the variable stays withheld.
    #[test]
    fn target_over_an_eliminated_variable_stays_withheld() {
        let mut fixture = fixture();
        let array_sort = Sort::array(Sort::bitvec(8), Sort::bitvec(8));
        let gone = fixture
            .terms
            .mk_var("gone", Sort::Uninterpreted("Slice".to_string()));
        let field = fixture
            .terms
            .mk_app(Symbol::named("dat"), vec![gone], array_sort);
        let zero = fixture.terms.mk_bitvec(BigInt::from(0u8), 8);
        let read = fixture.terms.mk_select(field, zero);
        fixture.bits.values.insert(read, BigInt::from(0x11u8));
        let arrays = recover_with(&fixture, "dat", field, &[gone]);
        assert!(arrays.is_withheld(&fixture.eliminated));
        assert_eq!(
            arrays.pending_definitions[&fixture.eliminated].target(),
            field
        );
        assert!(!arrays.array_values.contains_key(&field));
    }

    /// A read whose index mentions an eliminated variable is decoupled junk:
    /// it neither plants a cell nor conflicts with the live read of that cell.
    #[test]
    fn reads_at_decoupled_indices_are_skipped() {
        let mut fixture = fixture();
        let gone = fixture.terms.mk_var("gone", Sort::bitvec(8));
        let junk = fixture.terms.mk_select(fixture.field, gone);
        fixture.bits.values.insert(gone, BigInt::from(0u8));
        fixture.bits.values.insert(junk, BigInt::from(0x33u8));
        let arrays = recover_with(&fixture, "dat", fixture.field, &[gone]);
        assert!(!arrays.is_withheld(&fixture.eliminated));
        assert_eq!(
            cell(&arrays.array_values[&fixture.eliminated], "#x00"),
            "#x11"
        );
    }
}
