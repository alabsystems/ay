// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Batch adjacent integration targets with exactly the same execution policy.
//! Targo owns parallel compilation and sequential test-executable execution.

use super::Step;
use crate::cmd_gate::land::process::StepKind;

struct Batch {
    common: Vec<String>,
    insertion: usize,
    targets: Vec<String>,
}

impl Batch {
    fn read(step: &Step) -> Option<Self> {
        if step.kind != StepKind::RustTests || step.needs_quiet_host() {
            return None;
        }
        let args = step.compiler_payload()?;
        if args.first()?.as_str() != "test" {
            return None;
        }
        let mut common = args[..1].to_vec();
        let mut targets = Vec::new();
        let mut insertion = None;
        let mut package = false;
        let mut index = 1;
        while let Some(argument) = args.get(index) {
            match argument.as_str() {
                "--" => {
                    // Harness filters/options must match byte-for-byte. They
                    // apply independently to every selected executable.
                    common.extend_from_slice(&args[index..]);
                    break;
                }
                "--test" => {
                    index += 1;
                    let target = args.get(index)?;
                    if target.is_empty()
                        || target.starts_with('-')
                        || target.contains(['*', '?', '[', ']'])
                        || targets.contains(target)
                    {
                        return None;
                    }
                    insertion.get_or_insert(common.len());
                    targets.push(target.clone());
                }
                "-p" | "--package" | "--features" | "--profile" => {
                    let value = args.get(index + 1)?;
                    if value.is_empty() || value.starts_with('-') {
                        return None;
                    }
                    if matches!(argument.as_str(), "-p" | "--package") {
                        if package {
                            return None;
                        }
                        package = true;
                    }
                    common.extend([argument.clone(), value.clone()]);
                    index += 1;
                }
                "--locked"
                | "--offline"
                | "--frozen"
                | "--no-default-features"
                | "--all-features" => common.push(argument.clone()),
                // In particular, --no-fail-fast changes when later targets
                // run after a failure; unit/bin/workspace selections and
                // unknown compiler controls stay separate and unchanged.
                _ => return None,
            }
            index += 1;
        }
        package.then_some(Self {
            common,
            insertion: insertion?,
            targets,
        })
    }

    fn extend(&mut self, next: &Self) -> bool {
        if self.common != next.common
            || self.insertion != next.insertion
            || next
                .targets
                .iter()
                .any(|target| self.targets.contains(target))
        {
            return false;
        }
        self.targets.extend(next.targets.iter().cloned());
        true
    }

    fn finish(self) -> Step {
        let mut args = self.common;
        args.splice(
            self.insertion..self.insertion,
            self.targets
                .into_iter()
                .flat_map(|target| ["--test".into(), target]),
        );
        Step::compiler(args)
    }
}

pub(super) fn compatible(steps: Vec<Step>) -> Vec<Step> {
    let mut result = Vec::with_capacity(steps.len());
    let mut pending: Option<Batch> = None;
    for step in steps {
        let next = Batch::read(&step);
        if let (Some(batch), Some(next)) = (&mut pending, &next) {
            if batch.extend(next) {
                continue;
            }
        }
        if let Some(batch) = pending.take() {
            result.push(batch.finish());
        }
        match next {
            Some(batch) => pending = Some(batch),
            None => result.push(step),
        }
    }
    if let Some(batch) = pending {
        result.push(batch.finish());
    }
    result
}

#[cfg(test)]
#[path = "land_batch_tests.rs"]
mod tests;
