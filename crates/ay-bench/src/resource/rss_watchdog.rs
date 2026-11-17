// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A native campaign observation, retaining the original Child's identity.

use super::*;

#[derive(Debug)]
pub(crate) struct RssWatchdog {
    #[cfg(all(unix, not(any(target_os = "redox", target_os = "solaris"))))]
    watch: native::Watch,
    #[cfg(all(unix, not(any(target_os = "redox", target_os = "solaris"))))]
    _observer: std::sync::Arc<native::Observer>,
    pub(super) aggregate_lease: Option<std::sync::Arc<GlobalHarnessLease>>,
    #[cfg(unix)]
    identity: ay_sys::supervisor::process_group::ProcessIdentity,
    terminal: Option<WatchdogOutcome>,
    #[cfg(test)]
    pub(super) pending_identity_observations: std::cell::Cell<usize>,
}

impl RssWatchdog {
    #[cfg(unix)]
    pub(super) fn identity(&self) -> ay_sys::supervisor::process_group::ProcessIdentity {
        self.identity
    }

    #[cfg(all(unix, not(any(target_os = "redox", target_os = "solaris"))))]
    pub(super) fn new(observer: std::sync::Arc<native::Observer>, watch: native::Watch) -> Self {
        Self {
            identity: watch.identity(),
            watch,
            _observer: observer,
            aggregate_lease: None,
            terminal: None,
            #[cfg(test)]
            pending_identity_observations: std::cell::Cell::new(0),
        }
    }

    pub(super) fn observe_owned_child(
        &self,
        child: &Child,
        label: &str,
    ) -> Result<UnreapedChildState> {
        #[cfg(test)]
        if let Some(left) = self.pending_identity_observations.get().checked_sub(1) {
            self.pending_identity_observations.set(left);
            return Err(std::io::Error::from(std::io::ErrorKind::WouldBlock).into());
        }
        #[cfg(unix)]
        {
            owned_child::observe_original_unreaped(child, &self.identity, label).map_err(Into::into)
        }
        #[cfg(not(unix))]
        {
            observe_child_unreaped(child, true, label)
        }
    }

    fn ensure_aggregate_lease_alive(&self) -> Result<()> {
        if let Some(lease) = self.aggregate_lease.as_deref() {
            lease.ensure_alive("guarded solver")?;
        }
        Ok(())
    }

    /// Observation never authorizes signalling. Cleanup retains the Child.
    pub(crate) fn poll(&mut self) -> Result<Option<WatchdogOutcome>> {
        self.ensure_aggregate_lease_alive()?;
        if let Some(outcome) = self.terminal {
            return Ok(Some(outcome));
        }
        #[cfg(all(unix, not(any(target_os = "redox", target_os = "solaris"))))]
        {
            let outcome = self.watch.poll()?;
            self.terminal = outcome;
            Ok(outcome)
        }
        #[cfg(not(all(unix, not(any(target_os = "redox", target_os = "solaris")))))]
        {
            Err(BenchError::msg(
                "native campaign watchdog unsupported on this target",
            ))
        }
    }

    pub(crate) fn finish(mut self) -> Result<WatchdogOutcome> {
        let deadline = Instant::now() + Duration::from_secs(12);
        loop {
            if let Some(outcome) = self.poll()? {
                return Ok(outcome);
            }
            if Instant::now() >= deadline {
                return Err(BenchError::msg(
                    "native RSS watchdog did not report completion within 12 seconds",
                ));
            }
            std::thread::sleep(Duration::from_millis(20));
        }
    }

    pub(super) fn finish_after_target_cleanup(self) -> Result<WatchdogOutcome> {
        self.finish()
    }
}
