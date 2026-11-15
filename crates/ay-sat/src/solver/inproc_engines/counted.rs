// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::counted_storage::Result;
use ay_core::original_query::{CountedAdmission, CountedAdmissionError, QueryError};

impl InprocessingEngines {
    /// Construct every ordinary engine under the same original admission owner.
    pub(crate) fn try_new_counted(num_vars: usize, owner: &CountedAdmission) -> Result<Self> {
        owner.admit(1, std::mem::size_of::<Self>())?;
        if ay_core::misc_cli_flags().sat_mem_probe {
            // The diagnostic branch constructs a second engine set and prints
            // per-engine measurements. Its extra work is not covered here.
            return Err(owner.refuse(CountedAdmissionError::Original(
                QueryError::Invalid("counted SAT construction does not cover memory probes").into(),
            )));
        }
        // The remaining ordinary constructors below contain only empty
        // containers and bounded scalar/default initialization. OccList(0)
        // allocates no rows, and Kitten's antecedent toggle allocates nothing.
        let mut definition_kitten = Kitten::new();
        definition_kitten.enable_antecedent_tracking();
        Ok(Self {
            vivifier: Vivifier::new(),
            subsumer: Subsumer::try_new_counted(num_vars, owner)?,
            prober: crate::probe::Prober::try_new_counted(num_vars, owner)?,
            bve: BVE::try_new_counted(num_vars, owner)?,
            bce: BCE::new(num_vars),
            cce: Cce::try_new_counted(num_vars, owner)?,
            conditioning: Conditioning::try_new_counted(num_vars, owner)?,
            decompose_engine: Decompose::try_new_counted(num_vars, owner)?,
            factor_engine: Factor::try_new_counted(num_vars, owner)?,
            sbva_engine: Sbva::try_new_counted(num_vars, owner)?,
            transred_engine: TransRed::try_new_counted(num_vars, owner)?,
            htr: HTR::new(num_vars),
            gate_extractor: GateExtractor::new(num_vars),
            congruence: CongruenceClosure::try_new_counted(num_vars, owner)?,
            sweeper: Sweeper::try_new_counted(num_vars, owner)?,
            definition_kitten,
            reconstruction: ReconstructionStack::new(),
            preprocess_transactions: PreprocessTransactionLedger::new(),
        })
    }
}

#[cfg(test)]
mod tests;
