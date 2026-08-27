// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::env;
use std::ffi::OsString;
use std::path::PathBuf;

use crate::{GateError, GateResult};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Action {
    Check,
    Ratchet,
    List,
    Help,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Tier {
    Fast,
    All,
}

impl Tier {
    pub(crate) const fn label(self) -> &'static str {
        match self {
            Self::Fast => "fast",
            Self::All => "all",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum BusyPolicy {
    RequireQuiet,
    AllowBusy,
}

pub(crate) struct Args {
    pub(crate) corpora: Vec<PathBuf>,
    pub(crate) probe: Option<PathBuf>,
    pub(crate) limit_secs: f64,
    pub(crate) tier: Tier,
    pub(crate) action: Action,
    pub(crate) busy_policy: BusyPolicy,
}

struct Parser {
    words: std::vec::IntoIter<OsString>,
    action: Option<Action>,
    corpora: Vec<PathBuf>,
    probe: Option<PathBuf>,
    limit_secs: f64,
    tier: Tier,
    busy_policy: BusyPolicy,
}

impl Parser {
    fn new(words: Vec<OsString>) -> Self {
        Self {
            words: words.into_iter(),
            action: None,
            corpora: Vec::new(),
            probe: None,
            limit_secs: 600.0,
            tier: Tier::Fast,
            busy_policy: BusyPolicy::RequireQuiet,
        }
    }

    fn value(&mut self, option: &str) -> GateResult<OsString> {
        self.words
            .next()
            .ok_or_else(|| GateError::setup(format!("{option} requires a value")))
    }

    fn set_action(&mut self, action: Action, option: &str) -> GateResult<()> {
        if let Some(previous) = self.action {
            return Err(GateError::setup(format!(
                "{option} conflicts with the previously selected action {previous:?}"
            )));
        }
        self.action = Some(action);
        Ok(())
    }

    fn parse_limit(&mut self, raw: OsString) -> GateResult<()> {
        let text = raw
            .to_str()
            .ok_or_else(|| GateError::setup("--limit must be valid UTF-8"))?;
        let limit = text
            .parse::<f64>()
            .map_err(|error| GateError::setup(format!("invalid --limit {text:?}: {error}")))?;
        if !limit.is_finite() || limit < 1.0 {
            return Err(GateError::setup(
                "--limit must be finite and at least 1 second",
            ));
        }
        self.limit_secs = limit;
        Ok(())
    }

    fn parse_tier(&mut self, raw: OsString) -> GateResult<()> {
        self.tier = match raw.to_str() {
            Some("fast") => Tier::Fast,
            Some("all") => Tier::All,
            _ => return Err(GateError::setup("--tier must be `fast` or `all`")),
        };
        Ok(())
    }

    fn parse_word(&mut self, word: OsString) -> GateResult<()> {
        match word.to_str() {
            Some("--check") => self.set_action(Action::Check, "--check"),
            Some("--ratchet") => self.set_action(Action::Ratchet, "--ratchet"),
            Some("--list") => self.set_action(Action::List, "--list"),
            Some("--help" | "-h") => self.set_action(Action::Help, "--help"),
            Some("--allow-busy") => {
                self.busy_policy = BusyPolicy::AllowBusy;
                Ok(())
            }
            Some("--corpus") => {
                let value = self.value("--corpus")?;
                self.corpora.push(PathBuf::from(value));
                Ok(())
            }
            Some("--probe") => {
                let value = self.value("--probe")?;
                self.probe = Some(PathBuf::from(value));
                Ok(())
            }
            Some("--limit") => {
                let value = self.value("--limit")?;
                self.parse_limit(value)
            }
            Some("--tier") => {
                let value = self.value("--tier")?;
                self.parse_tier(value)
            }
            Some(text) => Err(GateError::setup(format!("unknown argument {text:?}"))),
            None => Err(GateError::setup("arguments must be valid UTF-8")),
        }
    }

    fn finish(mut self) -> GateResult<Args> {
        while let Some(word) = self.words.next() {
            self.parse_word(word)?;
        }
        if self.corpora.is_empty() {
            let home = env::var_os("HOME")
                .ok_or_else(|| GateError::setup("HOME is unset; pass --corpus explicitly"))?;
            self.corpora
                .push(PathBuf::from(home).join("ay-bench/milp-gate/instances"));
        }
        Ok(Args {
            corpora: self.corpora,
            probe: self.probe,
            limit_secs: self.limit_secs,
            tier: self.tier,
            action: self.action.unwrap_or(Action::List),
            busy_policy: self.busy_policy,
        })
    }
}

pub(crate) fn parse() -> GateResult<Args> {
    Parser::new(env::args_os().skip(1).collect()).finish()
}

pub(crate) fn print_help() {
    println!(
        "ay-milp exact-rim regression gate\n\n\
         Usage: milp_rim_gate [--check | --ratchet | --list] [OPTIONS]\n\n\
         Options:\n\
           --corpus DIR    Directory of .mps/.mps.gz models; repeatable\n\
           --probe PATH    ay-milp lib test binary; otherwise ask Cargo\n\
           --limit SECS    Per-instance rim deadline (default: 600)\n\
           --tier TIER     fast or all (default: fast)\n\
           --allow-busy    Override the quiet-host precondition\n\
           -h, --help      Print this help\n\n\
         No action lists the committed pins without measuring."
    );
}
