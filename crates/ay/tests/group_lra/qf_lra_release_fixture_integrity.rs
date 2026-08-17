// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Always-on integrity preflight for the hermetic QF_LRA release canaries.

use sha2::{Digest, Sha256};
use std::path::{Path, PathBuf};

const FIXTURES: [(&str, &str); 3] = [
    (
        "benchmarks/smt/regression/qf_lra_release_soundness/slack_reason_sat.smt2",
        "f9abd0caee659dfe9fcd7913359766261cf2a2aff74e682ce3a8af8f12745d95",
    ),
    (
        "benchmarks/smt/regression/qf_lra_release_soundness/open_zero_lower_sat.smt2",
        "3fbb760c5fc81d983dbece1301e010901af5ef88c2d4d1c78909b8e6f40aed1a",
    ),
    (
        "benchmarks/smt/regression/qf_lra_release_soundness/open_zero_upper_sat.smt2",
        "fcc948619ada5050508803e16a197a9d10a6c916d1415732e32540511f79e11f",
    ),
];

const PINNED_ARCHIVE_SHA256: &str =
    "8e551882cf78432953f9e6f452cde098835e6cdc64b301becf42135609ee9881";

fn workspace_path(relative: impl AsRef<Path>) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(relative)
}

#[test]
fn qf_lra_release_fixtures_exist_and_match_pinned_bytes() {
    for (relative, expected_sha256) in FIXTURES {
        let path = workspace_path(relative);
        let bytes = std::fs::read(&path)
            .unwrap_or_else(|error| panic!("missing release fixture {}: {error}", path.display()));
        assert_eq!(
            format!("{:x}", Sha256::digest(&bytes)),
            expected_sha256,
            "release fixture bytes changed: {}",
            path.display()
        );

        let text = std::str::from_utf8(&bytes)
            .unwrap_or_else(|error| panic!("fixture {} is not UTF-8: {error}", path.display()));
        assert!(
            text.contains("(set-logic QF_LRA)")
                && text.contains("(set-info :status sat)")
                && text.contains("(check-sat)"),
            "fixture lost its QF_LRA/SAT/check-sat contract: {}",
            path.display()
        );
    }

    let fetcher_path = workspace_path("scripts/download_smtcomp_benchmarks.sh");
    let fetcher = std::fs::read_to_string(&fetcher_path).unwrap_or_else(|error| {
        panic!("missing corpus fetcher {}: {error}", fetcher_path.display())
    });
    let hash_contract = format!("QF_LRA_ARCHIVE_SHA256=\"{PINNED_ARCHIVE_SHA256}\"");
    for contract in [
        "ZENODO_RECORD=\"11061097\"",
        hash_contract.as_str(),
        "QF_LRA_ARCHIVE_SMTS=1753",
        ".QF_LRA-2024.sha256",
    ] {
        assert!(
            fetcher.contains(contract),
            "QF_LRA pinned archive contract missing {contract:?} from {}",
            fetcher_path.display()
        );
    }
}
