// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Private, binary-embedded copy of the verified LRAT soundness project.

use std::io;
use std::path::{Path, PathBuf};
use std::process::Command;

const LAKEFILE: &str = include_str!("../../../../verification/lean/lakefile.toml");
const LAKE_MANIFEST: &str = include_str!("../../../../verification/lean/lake-manifest.json");
const LEAN_TOOLCHAIN: &str = include_str!("../../../../verification/lean/lean-toolchain");
const LRAT_SOURCE: &str = include_str!("../../../../verification/lean/AySoundness/Lrat.lean");

/// A private project containing the exact checker source and toolchain metadata
/// embedded when this `ay` binary was built.
pub(super) struct SoundnessProject {
    directory: tempfile::TempDir,
}

impl SoundnessProject {
    pub(super) fn create() -> io::Result<Self> {
        let directory = tempfile::Builder::new()
            .prefix("ay-lean-soundness-")
            .tempdir()?;
        let root = directory.path();
        std::fs::create_dir(root.join("AySoundness"))?;
        std::fs::write(root.join("lakefile.toml"), LAKEFILE)?;
        std::fs::write(root.join("lake-manifest.json"), LAKE_MANIFEST)?;
        std::fs::write(root.join("lean-toolchain"), LEAN_TOOLCHAIN)?;
        std::fs::write(root.join("AySoundness/Lrat.lean"), LRAT_SOURCE)?;
        Ok(Self { directory })
    }

    pub(super) fn root(&self) -> &Path {
        self.directory.path()
    }

    pub(super) fn module_path(&self) -> PathBuf {
        self.root().join(".lake/build/lib/lean")
    }

    pub(super) fn build_command(&self) -> Command {
        let mut command = Command::new("lake");
        command
            .current_dir(self.root())
            .arg("build")
            .arg("AySoundness.Lrat");
        command
    }

    pub(super) fn pinned_lean_command(&self) -> Command {
        let mut command = Command::new("lake");
        command
            .current_dir(self.root())
            .arg("env")
            .arg("lean")
            .arg("-j1")
            // The verified checker reduces generated clause tables recursively.
            // Keep the worker stack large enough for known 1.5k-row proofs,
            // while retaining explicit process-memory and wall-time bounds.
            .arg("-s65536")
            .arg("-M2048");
        command
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn materialized_project_contains_pinned_soundness_theorem() {
        let project = SoundnessProject::create().expect("materialize soundness project");
        let source = std::fs::read_to_string(project.root().join("AySoundness/Lrat.lean"))
            .expect("read materialized LRAT checker");
        assert!(source.contains("theorem lratCheck_sound"));
        assert_eq!(
            std::fs::read_to_string(project.root().join("lean-toolchain")).expect("read toolchain"),
            LEAN_TOOLCHAIN
        );
        let command = project.pinned_lean_command();
        let args: Vec<_> = command
            .get_args()
            .map(|arg| arg.to_string_lossy())
            .collect();
        assert!(args.iter().any(|arg| arg == "-s65536"));
        assert!(args.iter().any(|arg| arg == "-M2048"));
    }
}
