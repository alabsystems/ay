// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! In-process pseudo-Boolean proof checking through the integrated libraries.

use anyhow::{bail, Context, Result};

pub(super) fn run(args: ay_veripb::args::Args) -> Result<()> {
    if args.lenient_header_counts {
        bail!("AY certificate checking requires strict input header counts");
    }
    if args.ignore_file_path_check {
        bail!("AY certificate checking requires the input/output path checks");
    }
    let supplied_output_formula = args.output_formula.is_some();
    let report = ay_veripb::check(args).context("pseudo-Boolean proof checking failed")?;
    if supplied_output_formula && !report.checked_output_file() {
        bail!(
            "the proof did not check the supplied output formula; an output FILE rule is required"
        );
    }
    report
        .write_to(&mut std::io::stdout().lock())
        .context("could not write the checked proof report")?;
    if !report.is_fully_verified() {
        bail!(
            "the derivation did not establish a fully verified certificate: \
               no substantive conclusion, unproved assertions, or weakened guarantees"
        );
    }
    Ok(())
}
