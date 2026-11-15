use anyhow::Result;
use clap::Parser;
use colored::Colorize;
use git_version::git_version;
use log::Level;
use std::io::Write;

use veripb::{args::Args, run_checker};

/// Explain an internal panic instead of leaving a bare backtrace.
///
/// The release profile enables overflow checks, so an arithmetic bug that
/// would once have wrapped silently -- and printed a wrong `s VERIFIED ...`
/// with exit 0 -- now aborts here. That is the safe outcome, but a user
/// holding an `.opb` and a `.pbp` deserves to be told which of the two it
/// means. The verdict is only ever printed after the whole run succeeds
/// (see `run_checker`), so no `s VERIFIED` line can precede this.
fn install_panic_explainer() {
    let previous = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        previous(info);
        eprintln!(
            "{}: the above is an INTERNAL ERROR in VeriPB, not a verdict about \
             your proof. The proof was NOT verified. Please report it with the \
             formula and proof that triggered it.",
            "Error".red().bold()
        );
    }));
}

/// Main function of the VeriPB tool.
fn main() -> Result<()> {
    install_panic_explainer();
    println!(
        "Running VeriPB version {}{}",
        env!("CARGO_PKG_VERSION"),
        git_version!(args = ["--tags"], fallback = env!("CARGO_PKG_VERSION"))
            .strip_prefix(env!("CARGO_PKG_VERSION"))
            .unwrap_or("")
    );
    let args = Args::parse();
    env_logger::Builder::new()
        .filter_level(args.log_level_filter())
        .format(|buf, record| {
            let label = match record.level() {
                Level::Error => "Error".red().bold(),
                Level::Warn => "Warning".yellow().bold(),
                Level::Info => "Info".cyan().bold(),
                Level::Debug | Level::Trace => "Debug".bright_black().bold(),
            };
            writeln!(buf, "{label}: {}", record.args())
        })
        .init();
    let outcome = run_checker(args)?;

    // A run that could not give the guarantee it was asked for exits with a
    // dedicated status, so that callers which only look at the exit code do not
    // read it as an unqualified pass. `std::process::exit` skips destructors, so
    // flush stdout explicitly.
    let exit_code = outcome.exit_code();
    if exit_code != 0 {
        std::io::stdout().flush().ok();
        std::process::exit(exit_code);
    }
    Ok(())
}
