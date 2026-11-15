// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Z3 5.3.3 poly_rewriter/arith_rewriter configuration, never resource grants.
use super::tactic_parameters::TacticParameterValue as V;
use super::tactics::TacticFailure;

/// Supported polynomial options. Absence retains the global/default setting.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PolynomialParameters {
    pub(crate) som: Option<bool>,
    pub(crate) som_blowup: Option<u32>,
    pub(crate) flat: Option<bool>,
    pub(crate) expand_power: Option<bool>,
    pub(crate) mul_to_power: Option<bool>,
    pub(crate) max_degree: Option<u32>,
    pub(crate) sort_sums: Option<bool>,
    pub(crate) push_to_real: Option<bool>,
}
#[derive(Clone, Copy)]
pub(super) struct Settings {
    pub som: bool,
    pub blowup: u32,
    pub flat: bool,
    pub expand_power: bool,
    pub mul_to_power: bool,
    pub max_degree: u32,
    pub sort_sums: bool,
    pub push_to_real: bool,
}
impl PolynomialParameters {
    /// Pinned upstream defaults, as configuration DATA rather than authority.
    pub fn default_value(name: &str) -> Option<V> {
        match name {
            "som" | "expand_power" | "mul_to_power" | "sort_sums" => Some(V::Bool(false)),
            "flat" | "push_to_real" => Some(V::Bool(true)),
            "som_blowup" => Some(V::UInt(10)),
            "max_degree" => Some(V::UInt(64)),
            _ => None,
        }
    }
    /// Visit only explicit values without copying names or allocating a table.
    pub fn visit<E>(
        &self,
        mut emit: impl FnMut(&'static str, V) -> Result<(), E>,
    ) -> Result<(), E> {
        for (name, value) in [
            ("som", self.som),
            ("flat", self.flat),
            ("expand_power", self.expand_power),
            ("mul_to_power", self.mul_to_power),
            ("sort_sums", self.sort_sums),
            ("push_to_real", self.push_to_real),
        ] {
            if let Some(value) = value {
                emit(name, V::Bool(value))?;
            }
        }
        for (name, value) in [
            ("som_blowup", self.som_blowup),
            ("max_degree", self.max_degree),
        ] {
            if let Some(value) = value {
                emit(name, V::UInt(value))?;
            }
        }
        Ok(())
    }
    pub fn recognizes(name: &str) -> bool {
        matches!(
            name,
            "som"
                | "som_blowup"
                | "flat"
                | "expand_power"
                | "mul_to_power"
                | "max_degree"
                | "sort_sums"
                | "push_to_real"
        )
    }
    pub fn set(&mut self, name: &str, value: V) -> Result<(), TacticFailure> {
        match (name, value) {
            ("som", V::Bool(v)) => self.som = Some(v),
            ("som_blowup", V::UInt(v)) => self.som_blowup = Some(v),
            ("flat", V::Bool(v)) => self.flat = Some(v),
            ("expand_power", V::Bool(v)) => self.expand_power = Some(v),
            ("mul_to_power", V::Bool(v)) => self.mul_to_power = Some(v),
            ("max_degree", V::UInt(v)) => self.max_degree = Some(v),
            ("sort_sums", V::Bool(v)) => self.sort_sums = Some(v),
            ("push_to_real", V::Bool(v)) => self.push_to_real = Some(v),
            _ => {
                return Err(TacticFailure::new(
                    "unsupported polynomial parameter name or type",
                ))
            }
        }
        Ok(())
    }
    pub(crate) fn over(self, previous: Self) -> Self {
        Self {
            som: self.som.or(previous.som),
            som_blowup: self.som_blowup.or(previous.som_blowup),
            flat: self.flat.or(previous.flat),
            expand_power: self.expand_power.or(previous.expand_power),
            mul_to_power: self.mul_to_power.or(previous.mul_to_power),
            max_degree: self.max_degree.or(previous.max_degree),
            sort_sums: self.sort_sums.or(previous.sort_sums),
            push_to_real: self.push_to_real.or(previous.push_to_real),
        }
    }
    /// simplify_cmd.cpp forces flat for a LOCAL true SOM keyword. Direct C and
    /// tactic parameters intentionally do not perform this surface override.
    pub fn for_smt_command(mut self) -> Self {
        if self.som == Some(true) {
            self.flat = Some(true)
        }
        self
    }
    pub(super) fn settings(self) -> Settings {
        let flat = self.flat.unwrap_or(true);
        let expand = self.expand_power.unwrap_or(false);
        Settings {
            som: self.som.unwrap_or(false) && flat,
            blowup: self.som_blowup.unwrap_or(10),
            flat,
            expand_power: expand,
            mul_to_power: self.mul_to_power.unwrap_or(false) && !expand,
            max_degree: self.max_degree.unwrap_or(64),
            sort_sums: self.sort_sums.unwrap_or(false),
            push_to_real: self.push_to_real.unwrap_or(true),
        }
    }
}
