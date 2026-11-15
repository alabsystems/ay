// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The vendored SMT-LIB fixtures behind three soundness guards are the
//! published benchmarks, byte for byte, on the side each guard's oracle needs.
//!
//! `qf_auflia_storecomm_8785` and `qf_nra_horner_refining` reject `unsat`, so
//! their inputs must be satisfiable; `qf_uf_hwbench_soundness` rejects `sat`,
//! so its inputs must be unsatisfiable. A fixture swapped for one from the other
//! side, or edited until a guard passes, would leave that guard green while it
//! checks nothing. The digests pin the bytes to the SMT-LIB release 2025
//! archives (Zenodo record 15493090: `QF_AUFLIA.tar.zst`, `QF_UF.tar.zst`,
//! `QF_NRA.tar.zst`, CC BY 4.0); the declared `:status` pins the side, and
//! z3 4.8.12 agrees with every one.

use sha2::{Digest, Sha256};

use crate::corpus::tracked_fixture;

/// `(workspace-relative path, sha256, declared status)`.
const FIXTURES: &[(&str, &str, &str)] = &[
    (
        "benchmarks/smtcomp/QF_AUFLIA/storecomm_invalid_t1_np_nf_ni_00030_007.cvc.smt2",
        "0fb7b51d93aa516ff0ce0189c63d933b12fb6baf53eec7f5dd865eebf759e97b",
        "sat",
    ),
    (
        "benchmarks/smtcomp/QF_AUFLIA/storecomm_invalid_t3_pp_nf_ni_00040_002.cvc.smt2",
        "82a5695d33b7cec74b04f049a6017c6fb1c019dac976b1b1b1c92bfdacc164f0",
        "sat",
    ),
    (
        "benchmarks/smtcomp/QF_AUFLIA/storecomm_invalid_t3_pp_nf_ni_00040_003.cvc.smt2",
        "5d768c11d336bcf381678af8d8b531025de8ebf9ae62153af18746f3be55478c",
        "sat",
    ),
    (
        "benchmarks/smtcomp/non-incremental/QF_UF/2018-Goel-hwbench/QF_UF_cache_coherence_three_ab_reg_max.smt2",
        "b35a7d2cec7da37b04074a0617446edb69d2822694ef98e6e365d07686630fad",
        "unsat",
    ),
    (
        "benchmarks/smtcomp/non-incremental/QF_UF/2018-Goel-hwbench/QF_UF_h_Arbiter_ab_reg_max.smt2",
        "9a682663666f2ce501b6834b3b00514506514956491ded29a00e731a509ff60e",
        "unsat",
    ),
    (
        "benchmarks/smtcomp/non-incremental/QF_UF/2018-Goel-hwbench/QF_UF_h_BufAl_ab_fp_max.smt2",
        "336397bf994d82fb402fe69dcb0754999c4eb3a7cee97fbfb1930d7ef52740b1",
        "unsat",
    ),
    (
        "benchmarks/smtcomp/non-incremental/QF_UF/2018-Goel-hwbench/QF_UF_h_Rrobin_ab_cti_max.smt2",
        "c8e4939cbb063dbe15d45b5f392e15d317d5fd11313d9721dd5347eb8e3d5a5e",
        "unsat",
    ),
    (
        "benchmarks/smtcomp/non-incremental/QF_UF/2018-Goel-hwbench/QF_UF_h_TicTacToe_ab_reg_max.smt2",
        "068f162d6e512c51a684bf21ff15f28d7dd0b5ed6bbcbfb080a99ce249ae46b2",
        "unsat",
    ),
    (
        "benchmarks/smtcomp/non-incremental/QF_UF/2018-Goel-hwbench/QF_UF_h_Vlunc_ab_cti_max.smt2",
        "dea5fe34baed0a0edcab25bba8f1b2f3d9892262cc8c8130cb9aae996a7ce6cc",
        "unsat",
    ),
    (
        "benchmarks/smtcomp/non-incremental/QF_UF/2018-Goel-hwbench/QF_UF_h_b04_ab_cti_max.smt2",
        "5cc6625e28393c0396c57b641c00492d20a71b9d41e661c493d31bc92f212671",
        "unsat",
    ),
    (
        "benchmarks/smtcomp/non-incremental/QF_UF/2018-Goel-hwbench/QF_UF_h_b04_ab_reg_max.smt2",
        "539fe25bf58daf113167888c73810e55171cd87f0fe6f705d191ff0ab39b83ca",
        "unsat",
    ),
    (
        "benchmarks/smtcomp/non-incremental/QF_UF/2018-Goel-hwbench/QF_UF_itc99_b13_ab_cti_max.smt2",
        "5697a3b7a370006e44d3d10ff6455fcfeac8b232f6972c5edf24872d6f6be9ba",
        "unsat",
    ),
    (
        "benchmarks/smt/regression/horner_refining/non-incremental__QF_NRA__meti-tarski__sqrt__1mcosq__7__sqrt-1mcosq-7-chunk-0170.smt2",
        "0fb05338361ed93118fd89f2288d72c332f79536e717bee66dd9c63c5ab49fda",
        "sat",
    ),
    (
        "benchmarks/smt/regression/horner_refining/non-incremental__QF_NRA__meti-tarski__heartdipole__heartdipole-chunk-0047.smt2",
        "a05c90fb06ad5a283f4e60dcce2667942a38af121974392edc2d8383f7b6cdfc",
        "sat",
    ),
    (
        "benchmarks/smt/regression/horner_refining/non-incremental__QF_NRA__meti-tarski__Chua__2__IL__L__Chua-2-IL-L-chunk-0107.smt2",
        "3b307677d364de475f98c25c167cc6a6aee5c8998caa63f6af46eaca8bbc4774",
        "sat",
    ),
    (
        "benchmarks/smt/regression/horner_refining/non-incremental__QF_NRA__meti-tarski__atan__vega__3__atan-vega-3-chunk-0298.smt2",
        "dc467facd8d696fcef426811cacf08f03a3a5c5e58cc277ae0ab8cb4e7191cb3",
        "sat",
    ),
    (
        "benchmarks/smt/regression/horner_refining/non-incremental__QF_NRA__meti-tarski__sin__problem__7__weak2__sin-problem-7-weak2-chunk-0099.smt2",
        "62d3e5d339b4a60862bf1c00c92be35d00cd6f50f29140b7011fa0f225052fba",
        "sat",
    ),
];

#[test]
fn vendored_soundness_fixtures_match_smtlib_bytes_and_status() {
    let mut drift = Vec::new();
    for &(relative, sha256, status) in FIXTURES {
        let path = tracked_fixture(relative);
        let bytes =
            std::fs::read(&path).unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
        let digest = format!("{:x}", Sha256::digest(&bytes));
        let declared = format!("(set-info :status {status})");
        if digest != sha256 || !String::from_utf8_lossy(&bytes).contains(&declared) {
            drift.push(format!(
                "{relative}: sha256 {digest}, want {sha256} declaring {declared}"
            ));
        }
    }
    assert!(
        drift.is_empty(),
        "vendored soundness fixtures drifted from SMT-LIB:\n{}",
        drift.join("\n")
    );
}
