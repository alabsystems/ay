// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native local landing command. Release publication belongs to `pub`.

use anyhow::Result;
use clap::Subcommand;

mod land;

#[derive(Subcommand)]
pub(crate) enum GateCommand {
    /// Validate the changed packages and land the exact validated commit.
    Land(land::LandArgs),
}

pub(crate) fn run(command: GateCommand) -> Result<i32> {
    match command {
        GateCommand::Land(args) => land::run(args),
    }
}
