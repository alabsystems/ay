//! Which Cargo-family frontend a subcommand that builds, tests or lints this
//! repository spawns.
//!
//! The gates and audits in this binary describe their Rust steps as Cargo
//! argv (`build -p ay --release`, `clippy --workspace`, ...). On a machine with
//! the Trust toolchain those steps must run on `targo`, in a named lane: a
//! compilation command takes `--unverified` (these steps measure the tree,
//! they make no proof claim), `clippy` is `tippy`, and `fmt` stays `fmt`. A
//! machine without that toolchain — a public clone — keeps plain `cargo`.
//!
//! Selection is a request, not tool identity or readiness. Any Targo path
//! entry (even dangling/refused), unknown path observation, or managed Trust
//! context selects Targo. Actual failures propagate; they never license stock
//! fallback. Only genuine absence outside managed Trust selects Cargo.

use std::io;
use std::path::Path;
use std::sync::OnceLock;

/// The frontend that runs this repository's Cargo-family steps.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RustFrontend {
    /// The Trust toolchain's `targo`, on its unverified lane.
    Targo,
    /// Plain Cargo, for a machine without the Trust toolchain.
    Cargo,
}

/// Cargo subcommands that compile, and therefore need a named Targo lane.
const COMPILE_SUBCOMMANDS: &[&str] = &[
    "build", "b", "check", "c", "test", "t", "run", "r", "bench", "rustc", "install",
];

impl RustFrontend {
    /// The frontend on this machine, probed once per process.
    pub(crate) fn current() -> Self {
        static CURRENT: OnceLock<RustFrontend> = OnceLock::new();
        *CURRENT.get_or_init(Self::detect)
    }

    fn detect() -> Self {
        let context = if std::env::var_os("ATPKG_BIN").is_some() {
            FrontendContext::ManagedTrust
        } else {
            FrontendContext::Public
        };
        select_frontend(targo_presence(), context)
    }

    /// The program to spawn.
    pub(crate) fn program(self) -> &'static str {
        match self {
            Self::Targo => "targo",
            Self::Cargo => "cargo",
        }
    }

    /// Translate Cargo arguments (without the leading `cargo`) into this
    /// frontend's arguments. Plain Cargo keeps them as they are.
    pub(crate) fn args<S: AsRef<str>>(self, cargo_args: &[S]) -> Vec<String> {
        let mut args: Vec<String> = cargo_args.iter().map(|a| a.as_ref().to_string()).collect();
        if self == Self::Cargo {
            return args;
        }
        match args.first().map(String::as_str) {
            Some("clippy") => args[0] = "tippy".to_string(),
            Some(sub) if COMPILE_SUBCOMMANDS.contains(&sub) => {
                args.insert(0, "--unverified".to_string());
            }
            _ => {}
        }
        args
    }

    /// Respell a whole argv whose program is `cargo`; any other argv is
    /// returned unchanged.
    pub(crate) fn argv<S: AsRef<str>>(self, argv: &[S]) -> Vec<String> {
        match argv.split_first() {
            Some((program, rest)) if program.as_ref() == "cargo" => {
                let mut spelled = vec![self.program().to_string()];
                spelled.extend(self.args(rest));
                spelled
            }
            _ => argv.iter().map(|a| a.as_ref().to_string()).collect(),
        }
    }

    /// Respell a human-readable `cargo ...` command line for this frontend.
    /// Text that does not start with `cargo ` is returned unchanged.
    pub(crate) fn render(self, cargo_command: &str) -> String {
        let Some(rest) = cargo_command.strip_prefix("cargo ") else {
            return cargo_command.to_string();
        };
        let (sub, tail) = rest.split_once(' ').unwrap_or((rest, ""));
        let mut words = self.args(&[sub]);
        words.insert(0, self.program().to_string());
        if !tail.is_empty() {
            words.push(tail.to_string());
        }
        words.join(" ")
    }
}

#[derive(Clone, Copy)]
enum ToolPresence {
    Present,
    Absent,
    Unknown,
}
#[derive(Clone, Copy)]
enum FrontendContext {
    ManagedTrust,
    Public,
}

fn select_frontend(presence: ToolPresence, context: FrontendContext) -> RustFrontend {
    match (presence, context) {
        (ToolPresence::Absent, FrontendContext::Public) => RustFrontend::Cargo,
        _ => RustFrontend::Targo,
    }
}

fn targo_presence() -> ToolPresence {
    let mut unknown = false;
    let names = if cfg!(windows) {
        &["targo", "targo.exe", "targo.cmd", "targo.bat", "targo.com"][..]
    } else {
        &["targo"][..]
    };
    if let Some(path) = std::env::var_os("PATH") {
        for directory in std::env::split_paths(&path) {
            for name in names {
                match std::fs::symlink_metadata(Path::new(&directory).join(name)) {
                    Ok(_) => return ToolPresence::Present,
                    Err(error) if error.kind() == io::ErrorKind::NotFound => {}
                    Err(_) => unknown = true,
                }
            }
        }
    }
    if unknown {
        ToolPresence::Unknown
    } else {
        ToolPresence::Absent
    }
}

#[cfg(test)]
mod selection_tests {
    use super::*;
    #[test]
    fn failed_or_unknown_trust_never_selects_stock_fallback() {
        for context in [FrontendContext::ManagedTrust, FrontendContext::Public] {
            for presence in [ToolPresence::Present, ToolPresence::Unknown] {
                assert_eq!(select_frontend(presence, context), RustFrontend::Targo);
            }
        }
        assert_eq!(
            select_frontend(ToolPresence::Absent, FrontendContext::ManagedTrust),
            RustFrontend::Targo
        );
        assert_eq!(
            select_frontend(ToolPresence::Absent, FrontendContext::Public),
            RustFrontend::Cargo
        );
    }
}

#[cfg(test)]
mod tests {
    use super::RustFrontend;

    #[test]
    fn targo_names_the_unverified_lane_for_compilation_commands() {
        for sub in ["build", "check", "test", "run", "bench", "rustc", "install"] {
            assert_eq!(
                RustFrontend::Targo.args(&[sub, "-p", "ay"]),
                ["--unverified", sub, "-p", "ay"],
                "{sub}"
            );
        }
    }

    #[test]
    fn targo_lints_with_tippy_and_formats_without_a_lane() {
        assert_eq!(
            RustFrontend::Targo.args(&["clippy", "--workspace"]),
            ["tippy", "--workspace"]
        );
        assert_eq!(
            RustFrontend::Targo.args(&["fmt", "--check", "--all"]),
            ["fmt", "--check", "--all"]
        );
        assert_eq!(
            RustFrontend::Targo.args(&["metadata", "--no-deps"]),
            ["metadata", "--no-deps"]
        );
    }

    #[test]
    fn plain_cargo_keeps_its_arguments() {
        assert_eq!(
            RustFrontend::Cargo.args(&["clippy", "--workspace"]),
            ["clippy", "--workspace"]
        );
        assert_eq!(RustFrontend::Cargo.args(&["build"]), ["build"]);
    }

    #[test]
    fn argv_respells_only_a_cargo_program() {
        assert_eq!(
            RustFrontend::Targo.argv(&["cargo", "test", "-p", "ay"]),
            ["targo", "--unverified", "test", "-p", "ay"]
        );
        assert_eq!(
            RustFrontend::Cargo.argv(&["cargo", "test"]),
            ["cargo", "test"]
        );
        assert_eq!(
            RustFrontend::Targo.argv(&["python3", "x.py"]),
            ["python3", "x.py"]
        );
    }

    #[test]
    fn render_respells_only_a_leading_cargo() {
        assert_eq!(
            RustFrontend::Targo.render("cargo test -p ay --features=\"cli\" --test group_cli"),
            "targo --unverified test -p ay --features=\"cli\" --test group_cli"
        );
        assert_eq!(
            RustFrontend::Targo.render("cargo build"),
            "targo --unverified build"
        );
        assert_eq!(
            RustFrontend::Targo.render("cargo clippy --workspace"),
            "targo tippy --workspace"
        );
        assert_eq!(
            RustFrontend::Cargo.render("cargo test -p ay"),
            "cargo test -p ay"
        );
        assert_eq!(RustFrontend::Targo.render("bash x.sh"), "bash x.sh");
    }
}
