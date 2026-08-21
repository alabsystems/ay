// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Textually included by `main` to preserve CLI value-type DefPaths.

/// Exit-code convention for a DIMACS verdict.
///
/// The SAT Competition reserves 10 for SATISFIABLE and 20 for UNSATISFIABLE.
/// Z3 does not: it exits 0 for both, reporting the verdict on stdout only. A
/// drop-in `z3` install therefore has to follow Z3, or every caller that tests
/// `$?` sees a nonzero status and reads it as failure.
#[derive(Debug, Clone, Copy, PartialEq, Eq, clap::ValueEnum)]
enum SatExitCodes {
    /// Exit 0 for SAT and UNSAT alike, as Z3 does.
    Z3,
    /// Exit 10 for SAT and 20 for UNSAT, as the SAT Competition requires.
    Competition,
}
