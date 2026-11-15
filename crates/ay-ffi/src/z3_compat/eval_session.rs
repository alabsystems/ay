// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Persistent SMT-LIB command state, matching Z3 api_parsers.cpp's cmd_context.

use ay_dpll::api::NativeProofInputBinding;
use ay_dpll::Executor;
use ay_frontend::{Command, CommandStream, CommandStreamItem, OptionValue, SExpr};

pub(crate) struct EvalSession {
    executor: Executor,
    bindings: Vec<NativeProofInputBinding>,
    proof_ready: Vec<bool>,
    scopes: Vec<usize>,
}

pub(super) struct EvalReply {
    pub text: String,
    pub error: Option<String>,
}

impl Default for EvalSession {
    fn default() -> Self {
        Self {
            executor: Executor::new(),
            bindings: Vec::new(),
            proof_ready: Vec::new(),
            scopes: Vec::new(),
        }
    }
}

impl EvalSession {
    pub(super) fn with_proofs(proofs: bool) -> Self {
        let mut session = Self::default();
        session.executor.set_produce_proofs(proofs);
        session
    }
    fn print_success(&self) -> bool {
        matches!(
            self.executor.context().get_option("print-success"),
            Some(OptionValue::Bool(true))
        )
    }

    pub(super) fn evaluate_with_proof_view(
        &mut self,
        input: &str,
        mut proof_view: impl FnMut(
            &Executor,
            &[NativeProofInputBinding],
            ProofEvent,
            bool,
        ) -> Result<Option<String>, String>,
    ) -> EvalReply {
        let mut stream = CommandStream::new(input);
        let mut outputs = Vec::new();
        let mut first_error = None;
        while let Some(item) = stream.next_command() {
            let command = match item {
                CommandStreamItem::Command(command) => command,
                CommandStreamItem::Error(error) => {
                    record_error(error.to_string(), &mut outputs, &mut first_error);
                    continue;
                }
            };
            // Exit terminates this input stream without exposing Executor's
            // internal "exit" sentinel. The context itself remains usable.
            if matches!(*command, Command::Exit) {
                if self.print_success() {
                    outputs.push("success".to_string());
                }
                break;
            }
            let proofs = self.executor.is_producing_proofs();
            let cores = matches!(
                self.executor.context().get_option("produce-unsat-cores"),
                Some(OptionValue::Bool(true))
            );
            let fresh_label = match command.as_ref() {
                Command::Assert(parsed) if cores => match tracking_name(parsed) {
                    Ok(Some(name)) => !self.executor.context().has_symbol_binding(&name),
                    Ok(None) => true,
                    Err(()) => false,
                },
                _ => true,
            };
            match self.executor.execute(&command) {
                Ok(Some(output)) => {
                    self.record_command(&command, proofs, cores, fresh_label);
                    let output = if matches!(*command, Command::GetProof)
                        && self.executor.last_proof().is_some()
                    {
                        match proof_view(
                            &self.executor,
                            &self.bindings,
                            ProofEvent::GetProof,
                            self.proof_ready.iter().all(|ready| *ready),
                        ) {
                            Ok(Some(view)) => view,
                            Ok(None) => output,
                            Err(error) => {
                                record_error(error, &mut outputs, &mut first_error);
                                continue;
                            }
                        }
                    } else {
                        output
                    };
                    if output.trim_start().starts_with("(error ") && first_error.is_none() {
                        first_error = Some(output.clone());
                    }
                    outputs.push(output);
                    if matches!(*command, Command::CheckSat | Command::CheckSatAssuming(_))
                        && self.executor.last_result_is_unsat()
                    {
                        match proof_view(
                            &self.executor,
                            &self.bindings,
                            ProofEvent::UnsatCheck,
                            self.proof_ready.iter().all(|ready| *ready),
                        ) {
                            Ok(Some(report)) if !report.is_empty() => outputs.push(report),
                            Ok(_) => {}
                            Err(error) => record_error(error, &mut outputs, &mut first_error),
                        }
                    }
                }
                Ok(None) => {
                    self.record_command(&command, proofs, cores, fresh_label);
                    if self.print_success() {
                        outputs.push("success".to_string());
                    }
                }
                Err(error) => record_error(error.to_string(), &mut outputs, &mut first_error),
            }
        }
        let mut text = String::new();
        for output in outputs {
            text.push_str(&output);
            if !output.ends_with('\n') {
                text.push('\n');
            }
        }
        EvalReply {
            text,
            error: first_error,
        }
    }

    fn record_command(&mut self, command: &Command, proofs: bool, cores: bool, fresh_label: bool) {
        match command {
            Command::Assert(parsed) => {
                self.proof_ready.push(proofs);
                self.bindings.push(if cores {
                    if fresh_label {
                        tracking_binding(parsed, &self.executor)
                    } else {
                        NativeProofInputBinding::Unsupported
                    }
                } else {
                    NativeProofInputBinding::Untracked
                });
            }
            Command::Push(count) => {
                for _ in 0..*count {
                    self.scopes.push(self.bindings.len());
                }
            }
            Command::Pop(count) => {
                for _ in 0..*count {
                    if let Some(len) = self.scopes.pop() {
                        self.bindings.truncate(len);
                        self.proof_ready.truncate(len);
                    }
                }
            }
            Command::Reset | Command::ResetAssertions => {
                self.bindings.clear();
                self.proof_ready.clear();
                self.scopes.clear();
            }
            _ => {}
        }
    }
}

#[derive(Clone, Copy)]
pub(super) enum ProofEvent {
    GetProof,
    UnsatCheck,
}

fn tracking_name(parsed: &ay_frontend::command::Term) -> Result<Option<String>, ()> {
    use ay_frontend::command::Term as Parsed;
    let mut body = parsed;
    let mut name = None;
    while let Parsed::Annotated(inner, attributes) = body {
        for (key, value) in attributes {
            if key == ":named" {
                if name.is_some() {
                    return Err(());
                }
                let SExpr::Symbol(label) = value else {
                    return Err(());
                };
                name = Some(label.clone());
            }
        }
        body = inner;
    }
    if ay_frontend::term_has_named_label(body) {
        return Err(());
    }
    Ok(name)
}

fn tracking_binding(
    parsed: &ay_frontend::command::Term,
    executor: &Executor,
) -> NativeProofInputBinding {
    let name = match tracking_name(parsed) {
        Ok(Some(name)) => name,
        Ok(None) => return NativeProofInputBinding::Untracked,
        Err(()) => return NativeProofInputBinding::Unsupported,
    };
    let Some(info) = executor.context().symbol_info(&name) else {
        return NativeProofInputBinding::Unsupported;
    };
    if info.sort != ay_core::Sort::Bool || !info.arg_sorts.is_empty() {
        return NativeProofInputBinding::Unsupported;
    }
    NativeProofInputBinding::Tracked {
        name,
        identity: info.declaration_identity().clone(),
    }
}

fn record_error(message: String, outputs: &mut Vec<String>, first_error: &mut Option<String>) {
    outputs.push(format!("(error {})", SExpr::String(message.clone())));
    if first_error.is_none() {
        *first_error = Some(message);
    }
}
