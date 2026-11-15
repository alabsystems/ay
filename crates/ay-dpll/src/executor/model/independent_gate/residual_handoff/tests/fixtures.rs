// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn append(exec: &mut Executor, source: &str) {
    for command in ay_frontend::parse(source).unwrap() {
        assert!(!matches!(command, ay_frontend::Command::CheckSat));
        exec.ctx.process_command(&command).unwrap();
    }
}

pub(super) fn fixture() -> (Executor, TermId) {
    let mut exec = Executor::new();
    append(
        &mut exec,
        "(set-logic ALL)
        (declare-datatype Inner ((mkInner (len (_ BitVec 64))
            (data (Array (_ BitVec 64) (_ BitVec 8))))))
        (declare-datatype Outer ((mkOuter (flag Bool) (inner Inner))))
        (declare-const a (Array (_ BitVec 64) Outer))
        (assert (= (len (inner (select a (_ bv9 64)))) (_ bv5 64)))",
    );
    let array = exec.ctx.source_constant_for_value("a").unwrap().0;
    exec.last_model = Some(Model::empty());
    (exec, array)
}

pub(super) fn full_replay(exec: &Executor) -> GateVerdict {
    let roots = independent_gate_query_roots(exec).unwrap();
    let _cache = GateViewCacheSession::new();
    let view = IndependentModelView::new(exec, exec.last_model.as_ref().unwrap());
    view.ensure_def_index().unwrap();
    ay_model_check::confirm_completed_model(&exec.ctx.terms, &view, &roots)
}

pub(super) fn forge_initial_confirmation(exec: &mut Executor) {
    // Deliberately synthesize only the prior gate's bookkeeping, NOT a checked
    // theorem. The changed-model replay must reject false/unsupported roots
    // even if that first gate was handed this impossible stale authority.
    let roots = independent_gate_query_roots(exec).unwrap();
    let epoch = exec.query_authority_epoch.clone();
    let source = exec.ctx.source_context_stamp();
    let scope = QuantifiedModelCheckScope::capture(exec, epoch, source, &roots).unwrap();
    exec.quantified_model_confirmation = Some(scope.finish(exec).unwrap());
}
