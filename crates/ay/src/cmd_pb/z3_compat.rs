// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `cmd_pb` to preserve private item DefPaths.

/// Solve an `.opb` file selected by Z3's extension-based input dispatch and
/// translate the PB-competition writer into Z3's compact transcript.
///
/// The explicit `-opb` switch intentionally remains rejected: the exact Z3
/// 5.0.0 reference binary advertises it but rejects it with command-line exit
/// 109. Extension-based `.opb` dispatch is live in that same binary.
pub(crate) fn run_z3_compat(
    path: Option<&Path>,
    use_stdin: bool,
    display_model: bool,
    display_stats: bool,
    timeout: Option<u64>,
) -> Result<i32> {
    let mut staged_input = None;
    let file = if use_stdin {
        let mut staged = tempfile::Builder::new()
            .prefix("ay-z3-opb-")
            .suffix(".opb")
            .tempfile()
            .context("creating private OPB stdin snapshot")?;
        io::copy(&mut io::stdin().lock(), &mut staged)
            .context("materializing OPB stdin snapshot")?;
        staged.flush().context("flushing OPB stdin snapshot")?;
        let path = staged.path().to_path_buf();
        staged_input = Some(staged);
        path
    } else {
        path.context("input file was not specified")?.to_path_buf()
    };
    let command = PbCommand::Solve {
        file,
        timeout,
        proof: None,
        // Read from `argv` by the governor before this parser exists; see
        // `ay_sys::govern::CLI_BUDGET_FLAG`.
        memory_mb: None,
        stats: false,
        stats_json: false,
        native: false,
        ab_switches: Default::default(),
    };
    // The competition writer's stdout is captured and translated above, but the
    // engines' `c dual N` progress line goes straight to stderr, and z3's stderr
    // is silent. Whether an engine reaches that line before the portfolio
    // winner stops it is a thread race, so it leaked on a varying share of
    // runs. This process answers one Z3-mode query, so silence it here.
    ay_pb::optimize::shared_bounds::set_reported_dual_stderr(false);
    let mut captured = Vec::new();
    let status = run_with_writer(&command, &mut captured)?;
    drop(staged_input);
    let transcript = String::from_utf8(captured).context("PB solver emitted non-UTF-8 output")?;
    let objective = transcript
        .lines()
        .rev()
        .find_map(|line| line.strip_prefix("o "));
    let assignment = parse_competition_assignment(&transcript)?;

    match status {
        PbStatus::OptimumFound | PbStatus::Satisfiable => {
            println!("sat");
            if display_stats {
                println!("time:                0.00 secs");
            }
            if display_model {
                emit_z3_boolean_model(&assignment);
            }
            if let Some(value) = objective {
                println!("   {value}");
            }
        }
        PbStatus::Unsatisfiable => println!("unsat"),
        PbStatus::Unknown | PbStatus::Unsupported => println!("unknown"),
    }
    Ok(0)
}

fn parse_competition_assignment(transcript: &str) -> Result<Vec<bool>> {
    let mut assignment = Vec::new();
    for token in transcript
        .lines()
        .filter_map(|line| line.strip_prefix("v "))
        .flat_map(str::split_whitespace)
    {
        let (value, variable) = token
            .strip_prefix("-x")
            .map(|variable| (false, variable))
            .or_else(|| token.strip_prefix('x').map(|variable| (true, variable)))
            .context("invalid PB assignment token")?;
        let index = variable
            .parse::<usize>()
            .context("invalid PB assignment variable")?;
        if index == 0 {
            anyhow::bail!("PB assignment variables are one-indexed");
        }
        assignment.resize(assignment.len().max(index), false);
        assignment[index - 1] = value;
    }
    Ok(assignment)
}

fn emit_z3_boolean_model(assignment: &[bool]) {
    for (offset, value) in assignment.iter().enumerate() {
        let variable = offset + 1;
        println!("(define-fun k!{variable} () Bool");
        println!("  {value})");
    }
}
