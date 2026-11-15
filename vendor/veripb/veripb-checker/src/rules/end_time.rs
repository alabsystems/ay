use std::{
    rc::Rc,
    time::{Duration, Instant},
};

use log::warn;
use veripb_formula::prelude::*;
use veripb_rules::EndTimerRule;

use crate::{prelude::*, rules::Checkable};

impl Checkable for EndTimerRule {
    fn compute(
        &mut self,
        context: &mut Context,
        _database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        if context.config.record_stats {
            let end = Instant::now();
            if let Some(start) = context.running_timers.remove(&self.name) {
                let total_duration = context
                    .timer_totals
                    .entry(self.name.clone())
                    .or_insert(Duration::ZERO);
                *total_duration += end.duration_since(start);
            } else {
                warn!(
                    "No timer with the name '{}' has been started, hence the timer can not be ended!",
                    self.name
                );
            }
        }

        Ok(vec![])
    }

    fn is_subproof_friendly(&self) -> bool {
        true
    }
}
