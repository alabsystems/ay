// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Test-only fixture construction at the candidate producer's lexical owner.
//! Production candidate/view visibility and source admission are unchanged.

use crate::executor::model::{Model, SymbolicAdmission, SymbolicRecoveryScope};
use crate::executor::Executor;
use ay_core::TermId;

impl Executor {
    #[cfg(test)]
    pub(in crate::executor) fn prepare_symbolic_output_fixture(
        &mut self,
        roots: &[TermId],
    ) -> (Model, SymbolicAdmission) {
        let scope = SymbolicRecoveryScope::enter(self, Box::new(|_, _| true)).unwrap();
        let owner = scope.admission();
        let candidate = self.qmc_symbolic_candidate(roots, &owner).unwrap();
        let mut model = Model::empty();
        self.install_model_check_symbolic_ufs(&mut model, candidate, &owner)
            .unwrap();
        drop(scope);
        (model, owner)
    }
}

#[test]
fn symbolic_uf_source_scan_prices_actual_selected_head_width_on_one_original_owner() {
    let (executor, _) = super::fixture(
        "(set-logic AUFLIA)(declare-fun weather (Int) Bool)",
        &["(forall ((x Int)) (= (weather x) (< x 5)))"],
    );
    let scope = SymbolicRecoveryScope::enter(&executor, Box::new(|_, _| true)).unwrap();
    let owner = scope.admission();
    let before = owner.remaining();
    let (actual, actual_footprint) =
        crate::executor::model::symbolic_source_inventory_work(&executor, &owner, "weather".len())
            .unwrap();
    let after_actual = owner.remaining();
    assert_eq!(before.0 - after_actual.0, actual);
    let (padded, padded_footprint) =
        crate::executor::model::symbolic_source_inventory_work(&executor, &owner, 256).unwrap();
    let after_padded = owner.remaining();
    assert_eq!(after_actual.0 - after_padded.0, padded);
    assert!(actual < padded, "actual={actual} opaque_maximum={padded}");
    assert!(actual >= actual_footprint.work());
    assert!(actual_footprint.matches_storage(&executor.ctx));
    assert!(padded_footprint.matches_storage(&executor.ctx));
    assert!(owner.pay(after_padded.0, 0));
    assert!(
        crate::executor::model::symbolic_source_inventory_work(&executor, &owner, "weather".len(),)
            .is_none(),
        "an accurate fee never renews the original ledger"
    );
}

#[test]
fn symbolic_uf_actual_width_still_pays_unselected_namespace_payload() {
    fn measure(ambient: &str) -> usize {
        let declarations = format!(
            "(set-logic AUFLIA)(declare-fun weather (Int) Bool)(declare-fun {ambient} (Int) Int)"
        );
        let (executor, _) = super::fixture(
            &declarations,
            &["(forall ((x Int)) (= (weather x) (< x 5)))"],
        );
        let scope = SymbolicRecoveryScope::enter(&executor, Box::new(|_, _| true)).unwrap();
        crate::executor::model::symbolic_source_inventory_work(
            &executor,
            &scope.admission(),
            "weather".len(),
        )
        .unwrap()
        .0
    }
    let short = measure("ambient");
    let long = measure(&"ambient".repeat(32));
    assert!(
        long > short,
        "retained actual name width remains paid: short={short} long={long}"
    );
}
