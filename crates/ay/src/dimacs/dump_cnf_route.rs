// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// `--dump-cnf` / `--extend-model`: the preprocess-only DIMACS routes.
//
// Both hook the one place every sequential DIMACS route reaches with a
// fully-configured solver and no search yet performed — immediately after
// `configure_dimacs_solver`, immediately before `solve_interruptible`. They
// run preprocessing to its initial fixpoint and then exit; neither ever
// enters the CDCL loop.
//
// `run_solve` rejects an explicit `--proof` on these routes and suppresses the
// implicit default, so neither ever runs with proof emission armed: they stop
// before any verdict a proof could certify, and an early exit would otherwise
// strand a staged proof file beside the input.
//
// The two halves:
//
// * `--dump-cnf F'` writes the residual formula, so a different core can
//   solve it. Equisatisfiable with the input, same variable numbering.
// * `--extend-model M` reads that core's assignment over `F'` and replays
//   AY's reconstruction stack to recover a model of the ORIGINAL formula —
//   the half without which a SAT answer from the downstream core cannot be
//   reported.

/// Run whichever preprocess-only route is armed. Never returns if one is.
fn maybe_run_preprocess_only_route(solver: &mut SatSolver) {
    if crate::EXTEND_MODEL_PATH.get().is_none() && crate::DUMP_CNF_PATH.get().is_none() {
        return;
    }

    // The clause arena must BE the formula. An arena that is already empty at
    // this point means some route lifted the constraints out of it — the XOR
    // route is the live example: `XOR: detected 529 constraints, 7744 clauses
    // consumed, 0 remaining` leaves a solver holding nothing while the real
    // problem lives in a Gaussian extension. Dumping that produced `p cnf 529
    // 0` for an UNSATISFIABLE instance, i.e. a wrong answer. Refuse instead.
    if solver.live_clause_count() == 0 {
        safe_eprintln!(
            "Error: preprocess-only route refused: the SAT solver holds no clauses, so the \
             formula is not in the clause arena (an XOR/Gaussian or other extension route \
             owns it). A dump taken here would be a strict weakening of the input."
        );
        let _ = io::stdout().flush();
        let _ = io::stderr().flush();
        std::process::exit(1);
    }

    if let Some(path) = crate::EXTEND_MODEL_PATH.get() {
        run_extend_model_route(solver, path);
    }
    if let Some(path) = crate::DUMP_CNF_PATH.get() {
        run_dump_cnf_route(solver, path);
    }
}

/// Refuse the preprocess-only routes on the extension-carrying solve path.
///
/// `run_dimacs_solver_with_extension` hands the solver a companion `Extension`
/// (the XOR/Gaussian engine) that propagates constraints the clause arena does
/// not contain. Even a PARTIALLY consumed formula (`N remaining`) is unsafe to
/// dump: the residual CNF alone is weaker than the input, so an UNSAT instance
/// can dump to a satisfiable file. There is no sound dump here, so say so.
fn reject_preprocess_only_route_for_extension() {
    let flag = if crate::DUMP_CNF_PATH.get().is_some() {
        "--dump-cnf"
    } else if crate::EXTEND_MODEL_PATH.get().is_some() {
        "--extend-model"
    } else {
        return;
    };
    safe_eprintln!(
        "Error: {flag} is incompatible with the XOR/Gaussian extension route: part of the \
         formula is carried outside the clause arena, so the residual CNF would be weaker \
         than the input. Re-run with the XOR route disabled."
    );
    let _ = io::stdout().flush();
    let _ = io::stderr().flush();
    std::process::exit(1);
}

fn run_dump_cnf_route(solver: &mut SatSolver, path: &Path) -> ! {
    let report = match solver.preprocess_and_dump_cnf(path) {
        Ok(report) => report,
        Err(e) => {
            safe_eprintln!("Error: --dump-cnf: {}: {e}", path.display());
            let _ = io::stdout().flush();
            let _ = io::stderr().flush();
            std::process::exit(1);
        }
    };

    match report.verdict {
        ay_sat::DumpCnfVerdict::Unsat => {
            // Preprocessing itself decided the instance. A formula file cannot
            // express "already refuted", so none was written — say so, and
            // report the verdict honestly with its proper exit code.
            safe_eprintln!(
                "c dump-cnf: preprocessing derived the empty clause; no formula written to {}",
                path.display()
            );
            crate::mark_verdict_printed();
            safe_println!("s UNSATISFIABLE");
            let _ = io::stdout().flush();
            let _ = io::stderr().flush();
            std::process::exit(crate::dimacs_verdict_exit_code(20));
        }
        ay_sat::DumpCnfVerdict::Sat | ay_sat::DumpCnfVerdict::Dumped => {}
    }

    emit_dump_cnf_summary(&report, path);

    if report.verdict == ay_sat::DumpCnfVerdict::Sat {
        // Preprocessing left no clauses. That IS a decision, so report it —
        // but only behind the same model gate every other SAT exit uses: the
        // reconstruction stack has to produce an assignment that satisfies
        // every original clause before `s SATISFIABLE` is allowed out.
        let extended = solver.extend_dumped_model(&[]);
        if extended.verified_against_source {
            safe_eprintln!("c dump-cnf: preprocessing solved the instance outright");
            crate::mark_verdict_printed();
            safe_println!("s SATISFIABLE");
            emit_extended_model_lines(&extended.model);
            let _ = io::stdout().flush();
            let _ = io::stderr().flush();
            std::process::exit(crate::dimacs_verdict_exit_code(10));
        }
        safe_eprintln!(
            "c dump-cnf: residual formula is empty but reconstruction did not verify \
             against the original clauses; withholding a SAT verdict"
        );
    }

    let _ = io::stdout().flush();
    let _ = io::stderr().flush();
    std::process::exit(0);
}

fn emit_dump_cnf_summary(report: &ay_sat::DumpCnfReport, path: &Path) {
    safe_eprintln!(
        "c dump-cnf: wrote {} ({} vars, {} clauses: {} units + {} arena, {} redundant)",
        path.display(),
        report.max_var,
        report.num_clauses,
        report.num_units,
        report.num_arena_clauses,
        report.num_redundant,
    );
    safe_eprintln!(
        "c dump-cnf: source {} vars / {} clauses; removed {} vars, fixed {} vars; \
         preprocess {} ms",
        report.source_num_vars,
        report.source_num_clauses,
        report.removed_vars,
        report.fixed_vars,
        report.preprocess_ms,
    );
    if report.skipped_removed_units > 0 {
        safe_eprintln!(
            "c dump-cnf: omitted {} level-0 assignment(s) of removed variables",
            report.skipped_removed_units
        );
    }
    if report.leaked_removed_var_clauses > 0 {
        // Loud on purpose: this is a preprocessing invariant violation, and a
        // dump that quietly carries eliminated variables is exactly the kind
        // of silent corruption this route exists to avoid.
        safe_eprintln!(
            "c dump-cnf: WARNING {} emitted clause(s) still mention an eliminated or \
             substituted variable — the dump may not be equisatisfiable",
            report.leaked_removed_var_clauses
        );
    }
}

fn run_extend_model_route(solver: &mut SatSolver, path: &Path) -> ! {
    let assignment = match read_dimacs_assignment(path) {
        Ok(a) => a,
        Err(e) => {
            safe_eprintln!("Error: --extend-model: {}: {e}", path.display());
            let _ = io::stdout().flush();
            let _ = io::stderr().flush();
            std::process::exit(1);
        }
    };

    let (verdict, preprocess_ms) = solver.preprocess_for_dump();
    if verdict == ay_sat::DumpCnfVerdict::Unsat {
        safe_eprintln!(
            "c extend-model: preprocessing derived the empty clause; the supplied \
             assignment cannot correspond to this formula"
        );
        crate::mark_verdict_printed();
        safe_println!("s UNSATISFIABLE");
        let _ = io::stdout().flush();
        let _ = io::stderr().flush();
        std::process::exit(crate::dimacs_verdict_exit_code(20));
    }

    let extended = solver.extend_dumped_model(&assignment);
    safe_eprintln!(
        "c extend-model: {} input literals ({} out of range), {} reconstruction steps \
         replayed, preprocess {} ms",
        extended.assigned_from_input,
        extended.out_of_range_literals,
        extended.reconstruction_steps,
        preprocess_ms,
    );

    if !extended.verified_against_source {
        // The composition produced a wrong answer. Never launder that into a
        // SAT verdict.
        safe_eprintln!(
            "c extend-model: FAILED — the reconstructed assignment does not satisfy every \
             original clause; refusing to emit a model"
        );
        let _ = io::stdout().flush();
        let _ = io::stderr().flush();
        std::process::exit(1);
    }

    safe_eprintln!("c extend-model: verified against every original clause");
    crate::mark_verdict_printed();
    safe_println!("s SATISFIABLE");
    emit_extended_model_lines(&extended.model);
    let _ = io::stdout().flush();
    let _ = io::stderr().flush();
    std::process::exit(crate::dimacs_verdict_exit_code(10));
}

/// Parse DIMACS literals from a solver's model output. Accepts raw whitespace-
/// separated integers and SAT-competition `v` lines interchangeably, and skips
/// `c`/`s` lines, so a downstream solver's stdout can be piped in unedited.
fn read_dimacs_assignment(path: &Path) -> io::Result<Vec<i32>> {
    let text = std::fs::read_to_string(path)?;
    let mut out = Vec::new();
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('c') || line.starts_with('s') {
            continue;
        }
        let body = line.strip_prefix("v ").unwrap_or(line);
        for token in body.split_whitespace() {
            if token == "v" {
                continue;
            }
            match token.parse::<i32>() {
                Ok(0) => {}
                Ok(lit) => out.push(lit),
                Err(_) => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        format!("not a DIMACS literal: {token:?}"),
                    ));
                }
            }
        }
    }
    Ok(out)
}

/// Emit `v` lines in the SAT-competition wrapping, matching the normal model
/// output path.
fn emit_extended_model_lines(model: &[i32]) {
    let mut line = String::from("v");
    for &lit in model {
        let token = format!(" {lit}");
        if line.len() + token.len() > 78 {
            safe_println!("{line}");
            line = String::from("v");
        }
        line.push_str(&token);
    }
    if line.len() > 1 {
        safe_println!("{line}");
    }
    safe_println!("v 0");
}
