// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! In-memory binding to an actual native compiler-artifact, not a cache search.
use anyhow::{bail, Context, Result};
use sha2::{Digest, Sha256};
use std::fs::File;
use std::io::{BufRead, BufReader, Read};
use std::path::{Path, PathBuf};
use std::process::Command;

pub(super) struct Library {
    path: PathBuf,
    digest: String,
}
impl Library {
    pub(super) fn from_messages(root: &Path, messages: File) -> Result<Self> {
        let manifest = root.join("crates/ay-ffi/Cargo.toml").canonicalize()?;
        let source = root.join("crates/ay-ffi/src/lib.rs").canonicalize()?;
        let mut selected = None;
        for line in BufReader::new(messages).lines() {
            let line = line?;
            let message: serde_json::Value =
                serde_json::from_str(&line).context("invalid native compiler JSON")?;
            if message["reason"] != "compiler-artifact" {
                continue;
            }
            if message["manifest_path"]
                .as_str()
                .is_none_or(|p| Path::new(p).canonicalize().ok().as_ref() != Some(&manifest))
            {
                continue;
            }
            if message["target"]["name"] != "ay_ffi"
                || message["target"]["src_path"]
                    .as_str()
                    .is_none_or(|p| Path::new(p).canonicalize().ok().as_ref() != Some(&source))
                || message["profile"]["test"].as_bool() != Some(false)
                || !message["target"]["crate_types"]
                    .as_array()
                    .is_some_and(|kinds| kinds.iter().any(|k| k == "staticlib"))
            {
                continue;
            }
            for name in message["filenames"]
                .as_array()
                .context("native artifact filenames missing")?
            {
                let path = PathBuf::from(
                    name.as_str()
                        .context("native artifact filename is not text")?,
                );
                if path
                    .file_name()
                    .is_none_or(|n| n != "libay_ffi.a" && n != "ay_ffi.lib")
                {
                    continue;
                }
                if !path.is_absolute() {
                    bail!("native static library path is not absolute");
                }
                if selected.as_ref().is_some_and(|old: &PathBuf| old != &path) {
                    bail!("ambiguous native FFI static library");
                }
                selected = Some(path);
            }
        }
        let path = selected.context("compiler did not produce the required FFI static library")?;
        let digest = hash(&path)?;
        Ok(Self { path, digest })
    }
    pub(super) fn verify(&self) -> Result<()> {
        if hash(&self.path)? != self.digest {
            bail!("produced FFI static library changed before consumer completion");
        }
        Ok(())
    }
    pub(super) fn bind(&self, command: &mut Command) {
        command
            .env("AY_FFI_STATIC_LIBRARY", &self.path)
            .env("AY_FFI_STATIC_LIBRARY_SHA256", &self.digest);
    }
}
fn hash(path: &Path) -> Result<String> {
    let mut file = File::open(path).context("open produced FFI static library")?;
    if !file.metadata()?.is_file() {
        bail!("produced FFI artifact is not a regular file");
    }
    let mut hash = Sha256::new();
    let mut buffer = vec![0u8; 65536].into_boxed_slice();
    loop {
        let n = file.read(&mut buffer)?;
        if n == 0 {
            break;
        }
        hash.update(&buffer[..n]);
    }
    Ok(format!("{:x}", hash.finalize()))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture() -> (tempfile::TempDir, PathBuf, File) {
        let root = tempfile::tempdir().unwrap();
        let package = root.path().join("crates/ay-ffi");
        std::fs::create_dir_all(package.join("src")).unwrap();
        std::fs::write(package.join("Cargo.toml"), "[package]\nname='ay-ffi'\n").unwrap();
        std::fs::write(package.join("src/lib.rs"), "").unwrap();
        let library = root.path().join("libay_ffi.a");
        std::fs::write(&library, b"original native artifact").unwrap();
        let messages = tempfile::tempfile().unwrap();
        (root, library, messages)
    }

    fn message(root: &Path, library: &Path) -> serde_json::Value {
        serde_json::json!({"reason":"compiler-artifact", "manifest_path":root.join("crates/ay-ffi/Cargo.toml"),
            "target":{"name":"ay_ffi", "src_path":root.join("crates/ay-ffi/src/lib.rs"), "crate_types":["rlib","staticlib","cdylib"]},
            "profile":{"test":false}, "filenames":[library]})
    }

    #[test]
    fn ffi_artifact_bytes_and_exact_producer_are_required() {
        use std::io::{Seek, SeekFrom, Write};
        let (root, library, mut messages) = fixture();
        writeln!(messages, "{}", message(root.path(), &library)).unwrap();
        messages.seek(SeekFrom::Start(0)).unwrap();
        let selected = Library::from_messages(root.path(), messages).unwrap();
        selected.verify().unwrap();
        std::fs::write(&library, b"corrupt native artifact").unwrap();
        assert!(selected.verify().is_err());
        let foreign = tempfile::tempdir().unwrap();
        let mut messages = tempfile::tempfile().unwrap();
        let mut wrong = message(root.path(), &library);
        wrong["manifest_path"] = serde_json::json!(foreign.path().join("Cargo.toml"));
        writeln!(messages, "{wrong}").unwrap();
        messages.seek(SeekFrom::Start(0)).unwrap();
        assert!(Library::from_messages(root.path(), messages).is_err());
    }

    #[test]
    fn ffi_artifact_native_plan_reuses_one_graph_and_links_the_bound_output() {
        use super::super::{Runner, StepKind};
        use crate::cmd_gate::land::{plan, scope::RustScope};
        // The containing native test owns admission. Like land_batch's actual
        // fixture, use that SAME inherited bank, with a separate build tree.
        let own_target = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target");
        std::fs::create_dir_all(&own_target).unwrap();
        let temporary = tempfile::tempdir_in(own_target).unwrap();
        let root = temporary.path().canonicalize().unwrap();
        let write = |path: &str, content: &str| {
            let path = root.join(path);
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(path, content).unwrap();
        };
        write(
            "Cargo.toml",
            "[workspace]\nmembers=['crates/ay','crates/ay-ffi','dependency']\nresolver='2'\n",
        );
        write("dependency/Cargo.toml", "[package]\nname='dependency'\nversion='0.1.0'\nedition='2021'\n[features]\ncli=[]\ntesting=[]\ntool=[]\nother=[]\n[[bin]]\nname='selected-tool'\npath='src/bin/tool.rs'\nrequired-features=['tool']\n[[bin]]\nname='unrelated-tool'\npath='src/bin/unrelated.rs'\nrequired-features=['other']\n");
        write("dependency/src/lib.rs", "pub fn value()->u32 { 6 + u32::from(cfg!(feature=\"testing\")) + 16*u32::from(cfg!(feature=\"cli\")) }\n");
        write("dependency/src/main.rs", "#[cfg(not(test))] fn main(){assert_eq!(dependency::value(),6); println!(\"default-production\");}\n#[cfg(test)] fn main(){}\n");
        write("dependency/src/bin/tool.rs", "#[cfg(not(test))] fn main(){assert!(cfg!(feature=\"tool\")); println!(\"selected-production\");}\n#[cfg(test)] fn main(){}\n");
        write(
            "dependency/src/bin/unrelated.rs",
            "compile_error!(\"unrelated optional tool must not be compiled\"); fn main(){}\n",
        );
        write("crates/ay/Cargo.toml", "[package]\nname='ay'\nversion='0.1.0'\nedition='2021'\n[features]\ncli=['dependency/cli']\nbench=[]\n[dependencies]\ndependency={path='../../dependency'}\n");
        write(
            "crates/ay/src/main.rs",
            "fn main(){assert_eq!(dependency::value(),22);}\n",
        );
        write("crates/ay-ffi/Cargo.toml", "[package]\nname='ay-ffi'\nversion='0.1.0'\nedition='2021'\n[lib]\ncrate-type=['rlib','staticlib']\n[dependencies]\ndependency={path='../../dependency'}\n[dev-dependencies]\ndependency={path='../../dependency',features=['testing']}\n");
        let source = "#[no_mangle] pub extern \"C\" fn sample()->u32 { dependency::value() }\n";
        write("crates/ay-ffi/src/lib.rs", source);
        write(
            "crates/ay-ffi/tests/group_ffi.rs",
            r#"#[test] fn actual_c_consumer() {
    let output=std::env::var_os("AY_FFI_STATIC_LIBRARY").expect("produced artifact binding");
    let root=std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let source=root.join("consumer.c"); let binary=root.join("consumer");
    std::fs::write(&source,"extern unsigned sample(void); int main(void){return sample()!=7;}").unwrap();
    let link=std::process::Command::new("cc").arg(&source).arg(output).arg("-o").arg(&binary).status().unwrap();
    assert!(link.success()); assert!(std::process::Command::new(binary).status().unwrap().success());
}
"#,
        );
        let metadata = Command::new("targo")
            .args(["metadata", "--offline", "--format-version", "1"])
            .current_dir(&root)
            .output()
            .unwrap();
        assert!(
            metadata.status.success(),
            "{}",
            String::from_utf8_lossy(&metadata.stderr)
        );
        let metadata: plan::Metadata = serde_json::from_slice(&metadata.stdout).unwrap();
        let plan = plan::select(
            &root,
            &metadata,
            vec![
                "crates/ay/src/main.rs".into(),
                "crates/ay-ffi/tests/group_ffi.rs".into(),
                "dependency/src/lib.rs".into(),
                "dependency/src/bin/tool.rs".into(),
            ],
            None,
            &RustScope::default(),
        )
        .unwrap();
        let mut runner = Runner::new(root.clone());
        let mut prepare = None;
        let mut consume = None;
        for mut step in plan.steps {
            let build = step
                .compiler_payload()
                .is_some_and(|args| args.first().is_some_and(|a| a == "build"));
            if !build && step.kind != StepKind::FfiArtifactTests {
                continue;
            }
            // Native test is already admitted. Preserve the generated Targo
            // payload verbatim, without taking another machine-wide claim.
            let payload = step.compiler_payload().unwrap().to_vec();
            step.program = "targo".into();
            step.args = std::iter::once("--unverified".into())
                .chain(payload)
                .collect();
            // The inherited target belongs to the containing owner. In
            // particular, this fixture also builds a binary named `ay` and
            // must never replace that owner's real CLI.
            step.args.splice(
                2..2,
                [
                    "--target-dir".into(),
                    root.join("isolated-target").to_str().unwrap().into(),
                ],
            );
            if step.kind == StepKind::FfiArtifactBuild {
                prepare = Some(step.clone());
            }
            if step.kind == StepKind::FfiArtifactTests {
                step.args.insert(2, "--message-format=json".into());
                consume = Some(step);
            } else {
                runner.execute(&step).unwrap();
            }
        }
        let consume = consume.expect("actual selected C consumer");
        // No CLI feature may leak into this graph: the linked C check returns
        // failure for 23 (CLI+testing) instead of the required dev-graph 7.
        let library = runner.ffi_artifact.as_ref().unwrap();
        assert!(library.path.starts_with(root.join("isolated-target")));
        assert!(root.join("isolated-target/debug/ay").is_file());
        for (name, expected) in [
            ("dependency", "default-production"),
            ("selected-tool", "selected-production"),
        ] {
            let output = ay_sys::metadata_capture::capture(
                Command::new(root.join("isolated-target/debug").join(name)),
                ay_sys::metadata_capture::CaptureLimits {
                    timeout: std::time::Duration::from_secs(5),
                    output_bytes: 4096,
                    resident_bytes: Some(256 << 20),
                },
                "native land production companion",
            )
            .unwrap();
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), expected);
        }
        let before = std::fs::metadata(&library.path)
            .unwrap()
            .modified()
            .unwrap();
        let output = runner.execute_tests(&consume).unwrap();
        let fresh = output
            .split(|b| *b == b'\n')
            .filter_map(|line| serde_json::from_slice::<serde_json::Value>(line).ok())
            .any(|message| {
                message["reason"] == "compiler-artifact"
                    && message["target"]["name"] == "ay_ffi"
                    && message["fresh"] == true
            });
        eprintln!("native same-graph FFI library fresh={fresh}");
        // Conservative compiler cohorts may legitimately refuse freshness.
        // Observe that decision rather than relax their integrity guard.
        if fresh {
            assert_eq!(
                std::fs::metadata(&runner.ffi_artifact.as_ref().unwrap().path)
                    .unwrap()
                    .modified()
                    .unwrap(),
                before
            );
        }
        let old = runner.ffi_artifact.take().unwrap();
        write(
            "crates/ay-ffi/src/lib.rs",
            "#[no_mangle] pub extern \"C\" fn sample()->u32 { dependency::value()+1 }\n",
        );
        runner.execute(&prepare.unwrap()).unwrap();
        assert_ne!(
            old.digest,
            runner.ffi_artifact.as_ref().unwrap().digest,
            "changed production code must produce different bytes"
        );
        assert!(
            runner.execute_tests(&consume).is_err(),
            "actual C behavior rejects changed value"
        );
        let selected = runner.ffi_artifact.as_ref().unwrap();
        std::fs::write(&selected.path, b"corrupt selected library").unwrap();
        assert!(
            runner.execute_tests(&consume).is_err(),
            "corruption must refuse before compiler execution"
        );
        assert!(runner.ffi_artifact.as_ref().unwrap().verify().is_err());
    }
}
