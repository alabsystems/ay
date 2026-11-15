//! Error type for VeriPB tool.

use thiserror::Error;
use veripb_checker::error::ForwardsCheckerError;

/// Error type for VeriPB tool.
#[derive(Debug, Error)]
pub enum VeriPBError {
    #[error("{0}")]
    ForwardsChecker(#[from] ForwardsCheckerError),
}
