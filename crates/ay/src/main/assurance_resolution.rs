// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by the binary root to preserve assurance test FQNs.

impl SolveArgs {
    /// Collapse the `--assurance` dial and the legacy alias flags onto a single
    /// canonical assurance level, without duplicating any downstream logic.
    ///
    /// Precedence (documented on `--assurance`) is MONOTONE — the STRONGEST
    /// level any given flag requests wins (certified > strict > standard >
    /// fast), so no flag is ever silently downgraded:
    ///   - lone `--assurance L`, or a lone legacy alias, resolves to that level;
    ///   - `--assurance L` plus a legacy alias resolves to the stronger of the
    ///     two (`--self-check --assurance fast` -> certified, never fast);
    ///   - two contradictory aliases resolve to the highest. None -> standard.
    ///
    /// The result is projected back onto the three legacy switches
    /// (`competition`, `strict_proofs`, `self_check`) that the whole solve
    /// pipeline already reads, so a level is byte-for-byte equivalent to its
    /// alias and no consuming code has to learn about `--assurance`.
    fn effective_assurance(&self) -> CliAssuranceLevel {
        // Assurance is MONOTONE: the result is the STRONGEST level any given flag
        // asks for, so no combination can ever land below something the user
        // explicitly requested. `--self-check --assurance fast` resolves to
        // `certified`, never `fast` — a stronger flag is never silently dropped.
        // Ranking: certified > strict > standard > fast.
        fn rank(level: CliAssuranceLevel) -> u8 {
            match level {
                CliAssuranceLevel::Fast => 0,
                CliAssuranceLevel::Standard => 1,
                CliAssuranceLevel::Strict => 2,
                CliAssuranceLevel::Certified => 3,
            }
        }
        // The level a legacy alias explicitly asks for — `None` when no alias is
        // set (so it imposes no floor). Contradictory aliases take the highest.
        let alias_level = if self.self_check {
            Some(CliAssuranceLevel::Certified)
        } else if self.strict_proofs {
            Some(CliAssuranceLevel::Strict)
        } else if self.competition {
            Some(CliAssuranceLevel::Fast)
        } else {
            None
        };
        // The strongest level any explicitly-given flag requests; a stronger flag
        // is never silently downgraded. Standard when nothing is set.
        match (self.assurance, alias_level) {
            (Some(a), Some(b)) if rank(a) >= rank(b) => a,
            (Some(_), Some(b)) => b,
            (Some(a), None) => a,
            (None, Some(b)) => b,
            (None, None) => CliAssuranceLevel::Standard,
        }
    }

    /// Normalize the assurance dial in place before any consumption.
    ///
    /// ONLY projects when `--assurance` is explicitly given. Without it, the
    /// legacy alias flags are left EXACTLY as the user set them — because they
    /// are not perfectly mutually exclusive: `--competition` also carries an
    /// orthogonal proof-suppression meaning the fail-closed CHC-certificate gate
    /// depends on, so collapsing a legacy-only combo like
    /// `--strict-proofs --competition` onto a single level would DROP
    /// `--competition` and leak that gate. The single-enum `--assurance` dial is
    /// the mutually-exclusive surface; legacy-only combos keep their historical
    /// additive semantics. Note this does NOT clear the SAT-competition env
    /// auto-enable: `competition_mode()` ORs that signal in regardless.
    fn resolve_assurance(&mut self) {
        // Legacy-only invocation: leave the alias booleans untouched (additive),
        // so no orthogonal flag meaning is lost to the projection.
        if self.assurance.is_none() {
            return;
        }
        match self.effective_assurance() {
            CliAssuranceLevel::Fast => {
                self.competition = true;
                self.strict_proofs = false;
                self.self_check = false;
            }
            CliAssuranceLevel::Standard => {
                self.competition = false;
                self.strict_proofs = false;
                self.self_check = false;
            }
            CliAssuranceLevel::Strict => {
                self.competition = false;
                self.strict_proofs = true;
                self.self_check = false;
            }
            CliAssuranceLevel::Certified => {
                self.competition = false;
                self.strict_proofs = false;
                self.self_check = true;
            }
        }
    }
}

#[cfg(test)]
mod assurance_resolution_tests {
    use super::{CliAssuranceLevel, SolveArgs};

    fn args(
        assurance: Option<CliAssuranceLevel>,
        competition: bool,
        strict_proofs: bool,
        self_check: bool,
    ) -> SolveArgs {
        SolveArgs {
            assurance,
            competition,
            strict_proofs,
            self_check,
            ..SolveArgs::default()
        }
    }

    #[test]
    fn single_flags_and_lone_dial_are_unchanged() {
        use CliAssuranceLevel::*;
        assert_eq!(
            args(None, false, false, false).effective_assurance(),
            Standard
        );
        assert_eq!(args(None, true, false, false).effective_assurance(), Fast);
        assert_eq!(args(None, false, true, false).effective_assurance(), Strict);
        assert_eq!(
            args(None, false, false, true).effective_assurance(),
            Certified
        );
        // A lone `--assurance` with no alias resolves to itself — crucially Fast,
        // which the earlier floor bug wrongly promoted to Standard.
        assert_eq!(
            args(Some(Fast), false, false, false).effective_assurance(),
            Fast
        );
        assert_eq!(
            args(Some(Certified), false, false, false).effective_assurance(),
            Certified
        );
    }

    #[test]
    fn assurance_is_monotone_never_downgrades_a_stronger_flag() {
        use CliAssuranceLevel::*;
        // The footgun: an explicit weak dial must NOT clear a stronger alias.
        assert_eq!(
            args(Some(Fast), false, false, true).effective_assurance(),
            Certified
        );
        assert_eq!(
            args(Some(Fast), true, false, false).effective_assurance(),
            Fast
        );
        assert_eq!(
            args(Some(Standard), false, false, true).effective_assurance(),
            Certified
        );
        assert_eq!(
            args(Some(Strict), false, false, true).effective_assurance(),
            Certified
        );
        // An explicit dial STRONGER than the alias wins (upgrade is fine).
        assert_eq!(
            args(Some(Certified), true, false, false).effective_assurance(),
            Certified
        );
        assert_eq!(
            args(Some(Strict), true, false, false).effective_assurance(),
            Strict
        );
        // Contradictory aliases take the highest.
        assert_eq!(
            args(None, true, true, true).effective_assurance(),
            Certified
        );
    }

    #[test]
    fn legacy_only_combo_keeps_orthogonal_flags_no_projection() {
        // REGRESSION: without an explicit --assurance, resolve_assurance must NOT
        // project onto a single level — that dropped --competition's orthogonal
        // proof-suppression for `--strict-proofs --competition`, leaking the
        // fail-closed CHC certificate gate. Legacy-only combos stay additive.
        let mut a = args(None, true, true, false); // --strict-proofs --competition
        a.resolve_assurance();
        assert!(
            a.competition,
            "legacy --competition must survive (proof suppression)"
        );
        assert!(a.strict_proofs, "legacy --strict-proofs must survive");
        // A lone legacy alias is likewise untouched.
        let mut b = args(None, false, false, true); // --self-check
        b.resolve_assurance();
        assert!(b.self_check && !b.competition && !b.strict_proofs);
        // An explicit dial DOES project (monotone strongest-wins).
        let mut c = args(Some(CliAssuranceLevel::Fast), false, false, true); // certified wins
        c.resolve_assurance();
        assert!(
            c.self_check && !c.competition,
            "certified alias beats explicit fast"
        );
    }
}

#[cfg(test)]
mod assurance_cli_tests {
    use std::path::Path;

    use clap::{CommandFactory as _, Parser as _};

    use super::{Cli, CliAssuranceLevel, CliProofFormat, Command, SolveArgs};

    fn args(
        assurance: Option<CliAssuranceLevel>,
        competition: bool,
        strict_proofs: bool,
        self_check: bool,
    ) -> SolveArgs {
        SolveArgs {
            assurance,
            competition,
            strict_proofs,
            self_check,
            ..SolveArgs::default()
        }
    }

    fn parse_solve_args(arguments: &[&str]) -> SolveArgs {
        let argv = ["ay", "solve"].into_iter().chain(arguments.iter().copied());
        let cli = Cli::try_parse_from(argv).expect("CLI arguments should parse");
        match cli.command {
            Some(Command::Solve(args)) => args,
            _ => panic!("expected the solve subcommand"),
        }
    }

    fn strongest(
        assurance: Option<CliAssuranceLevel>,
        competition: bool,
        strict_proofs: bool,
        self_check: bool,
    ) -> CliAssuranceLevel {
        use CliAssuranceLevel::*;

        if self_check || assurance == Some(Certified) {
            Certified
        } else if strict_proofs || assurance == Some(Strict) {
            Strict
        } else if assurance == Some(Standard) {
            Standard
        } else if competition || assurance == Some(Fast) {
            Fast
        } else {
            Standard
        }
    }

    #[test]
    fn every_dial_alias_combination_resolves_without_losing_legacy_flags() {
        use CliAssuranceLevel::*;

        for assurance in [
            None,
            Some(Fast),
            Some(Standard),
            Some(Strict),
            Some(Certified),
        ] {
            for mask in 0_u8..8 {
                let competition = mask & 1 != 0;
                let strict_proofs = mask & 2 != 0;
                let self_check = mask & 4 != 0;
                let expected = strongest(assurance, competition, strict_proofs, self_check);
                let mut actual = args(assurance, competition, strict_proofs, self_check);
                actual.validate = true;
                actual.no_validate = true;
                actual.proof = Some("explicit.proof".into());
                actual.proof_format = Some(CliProofFormat::Lrat);
                actual.proof_binary = true;
                actual.verify_proof = true;

                assert_eq!(actual.effective_assurance(), expected);
                actual.resolve_assurance();
                let expected_flags = if assurance.is_none() {
                    (competition, strict_proofs, self_check)
                } else {
                    match expected {
                        Fast => (true, false, false),
                        Standard => (false, false, false),
                        Strict => (false, true, false),
                        Certified => (false, false, true),
                    }
                };
                assert_eq!(
                    (actual.competition, actual.strict_proofs, actual.self_check),
                    expected_flags
                );
                assert!(actual.validate && actual.no_validate);
                assert_eq!(actual.proof.as_deref(), Some(Path::new("explicit.proof")));
                assert!(matches!(actual.proof_format, Some(CliProofFormat::Lrat)));
                assert!(actual.proof_binary && actual.verify_proof);
            }
        }
    }

    #[test]
    fn clap_accepts_the_dial_and_hidden_legacy_aliases() {
        use CliAssuranceLevel::*;

        for (arguments, expected) in [
            (&["--competition"][..], Fast),
            (&["--strict-proofs"][..], Strict),
            (&["--self-check"][..], Certified),
            (&["--assurance", "certified"][..], Certified),
            (&["--assurance", "standard", "--competition"][..], Standard),
            (&["--assurance", "fast", "--self-check"][..], Certified),
        ] {
            let mut parsed = parse_solve_args(arguments);
            assert_eq!(parsed.effective_assurance(), expected);
            parsed.resolve_assurance();
            assert_eq!(
                (parsed.competition, parsed.strict_proofs, parsed.self_check),
                match expected {
                    Fast => (true, false, false),
                    Standard => (false, false, false),
                    Strict => (false, true, false),
                    Certified => (false, false, true),
                }
            );
        }

        let mut command = Cli::command();
        let help = command
            .find_subcommand_mut("solve")
            .expect("solve subcommand")
            .render_long_help()
            .to_string();
        assert!(help.contains("Assurance ladder (--assurance <LEVEL>"));
        assert!(help.contains("fast       batteries off for speed"));
        assert!(help.contains("certified  fail-closed"));

        let proof_conflict = Cli::try_parse_from([
            "ay",
            "solve",
            "--proof-artifact",
            "artifact.json",
            "--no-proof",
        ]);
        assert!(proof_conflict.is_err());
    }

    #[test]
    fn clap_fine_grained_knobs_survive_assurance_resolution() {
        let mut parsed = parse_solve_args(&[
            "--assurance",
            "strict",
            "--no-validate",
            "--proof",
            "explicit.lrat",
            "--proof-format",
            "lrat",
            "--proof-binary",
            "--verify-proof",
        ]);

        parsed.resolve_assurance();

        assert!(parsed.no_validate);
        assert_eq!(parsed.proof.as_deref(), Some(Path::new("explicit.lrat")));
        assert!(matches!(parsed.proof_format, Some(CliProofFormat::Lrat)));
        assert!(parsed.proof_binary && parsed.verify_proof);
    }

    #[test]
    fn clap_accepts_b33_chc_and_sat_opt_outs() {
        let parsed = parse_solve_args(&[
            "--chc-no-array-relational",
            "--chc-no-array-relational-v2",
            "--chc-no-dt-bmc",
            "--chc-no-qual-mine",
            "--chc-no-qual-mixed",
            "--sat-no-factor-dense-init",
        ]);
        assert_eq!(parsed.ab_switches.b33_opt_outs(), [true; 6]);
    }
}
