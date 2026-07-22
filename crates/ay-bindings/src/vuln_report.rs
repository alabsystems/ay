// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Vulnerability explanation engine: generate human-readable security reports
//! from SMT solver results.
//!
//! When AY finds a vulnerability (SAT result with a model showing an exploit),
//! the raw model is hard to interpret. This module turns solver results into
//! structured, human-readable security reports.
//!
//! ## Usage
//!
//! ```rust
//! use ay_bindings::vuln_report::{VulnType, classify_vulnerability, VulnerabilityReport};
//!
//! // Classify from assertion name
//! let vuln = classify_vulnerability("assert_valid_access");
//! assert_eq!(vuln, VulnType::UseAfterFree);
//!
//! // Build a report manually
//! let report = VulnerabilityReport::new(
//!     VulnType::BufferOverflow,
//!     vec![("input_len".into(), "0x00000100".into())],
//! );
//! let text = report.format();
//! assert!(text.contains("Buffer Overflow"));
//! ```

use std::fmt;

/// Type of memory safety vulnerability detected.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum VulnType {
    /// Write or read beyond allocated buffer bounds.
    BufferOverflow,
    /// Access to memory after it has been freed.
    UseAfterFree,
    /// Freeing memory that has already been freed.
    DoubleFree,
    /// Dereferencing a null pointer.
    NullDeref,
    /// Returning a pointer to stack-allocated memory.
    StackEscape,
    /// Arithmetic overflow leading to unexpected behavior.
    IntegerOverflow,
}

impl VulnType {
    /// Human-readable name of this vulnerability type.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::BufferOverflow => "Buffer Overflow",
            Self::UseAfterFree => "Use-After-Free",
            Self::DoubleFree => "Double Free",
            Self::NullDeref => "Null Pointer Dereference",
            Self::StackEscape => "Stack Pointer Escape",
            Self::IntegerOverflow => "Integer Overflow",
        }
    }

    /// CWE identifier for this vulnerability type.
    #[must_use]
    pub fn cwe(self) -> &'static str {
        match self {
            Self::BufferOverflow => "CWE-120",
            Self::UseAfterFree => "CWE-416",
            Self::DoubleFree => "CWE-415",
            Self::NullDeref => "CWE-476",
            Self::StackEscape => "CWE-562",
            Self::IntegerOverflow => "CWE-190",
        }
    }

    /// Brief description of this vulnerability type.
    #[must_use]
    pub fn description(self) -> &'static str {
        match self {
            Self::BufferOverflow => {
                "An access exceeds the bounds of an allocated buffer, potentially \
                 allowing an attacker to read or write adjacent memory."
            }
            Self::UseAfterFree => {
                "Memory is accessed after it has been freed, potentially allowing \
                 an attacker to control the contents of the freed region."
            }
            Self::DoubleFree => {
                "Memory is freed more than once, corrupting the heap allocator \
                 metadata and potentially enabling arbitrary write."
            }
            Self::NullDeref => {
                "A null pointer is dereferenced, causing a crash. On some \
                 platforms this can be exploitable if null page is mappable."
            }
            Self::StackEscape => {
                "A pointer to stack-allocated memory escapes the function scope, \
                 leading to use of dangling stack references."
            }
            Self::IntegerOverflow => {
                "An arithmetic operation overflows, potentially causing incorrect \
                 size calculations that lead to buffer overflows or other issues."
            }
        }
    }
}

impl fmt::Display for VulnType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

/// Severity level of a vulnerability.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum Severity {
    /// Low impact — crash or minor information leak.
    Low,
    /// Medium impact — potential for limited exploitation.
    Medium,
    /// High impact — likely exploitable for code execution or arbitrary write.
    High,
}

impl Severity {
    /// Human-readable name.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::Low => "Low",
            Self::Medium => "Medium",
            Self::High => "High",
        }
    }
}

impl fmt::Display for Severity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

/// A memory region affected by the vulnerability.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemoryRegion {
    /// Object ID in the split-pointer model.
    pub object_id: u32,
    /// Offset within the object where the violation occurs.
    pub offset: u32,
    /// Size of the access that caused the violation (in bytes).
    pub access_size: u32,
    /// Allocated size of the object (if known).
    pub allocated_size: Option<u32>,
}

impl fmt::Display for MemoryRegion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "object #{} at offset 0x{:08x} (access size: {} bytes",
            self.object_id, self.offset, self.access_size
        )?;
        if let Some(alloc_size) = self.allocated_size {
            write!(f, ", allocated: {alloc_size} bytes")?;
        }
        write!(f, ")")
    }
}

/// Structured vulnerability report generated from a SAT model.
///
/// Contains all information needed to understand and reproduce a
/// vulnerability found by the SMT solver.
#[derive(Debug, Clone)]
pub struct VulnerabilityReport {
    /// Type of vulnerability detected.
    pub vuln_type: VulnType,
    /// Severity of the vulnerability.
    pub severity: Severity,
    /// Variable name -> value pairs from the minimized model.
    ///
    /// Each entry is `(variable_name, formatted_value)`.
    pub exploit_input: Vec<(String, String)>,
    /// Which memory region is affected (if applicable).
    pub affected_memory: Option<MemoryRegion>,
    /// Human-readable explanation of the vulnerability.
    pub explanation: String,
}

impl VulnerabilityReport {
    /// Create a new vulnerability report with default severity based on type.
    ///
    /// # Arguments
    /// * `vuln_type` - The type of vulnerability detected.
    /// * `exploit_input` - Variable name -> value pairs from the SAT model.
    #[must_use]
    pub fn new(vuln_type: VulnType, exploit_input: Vec<(String, String)>) -> Self {
        let severity = compute_severity_from_type(vuln_type);
        let explanation = build_explanation(vuln_type, &exploit_input, None);
        Self {
            vuln_type,
            severity,
            exploit_input,
            affected_memory: None,
            explanation,
        }
    }

    /// Create a report with a specific memory region.
    #[must_use]
    pub fn with_memory_region(mut self, region: MemoryRegion) -> Self {
        self.explanation = build_explanation(self.vuln_type, &self.exploit_input, Some(&region));
        self.affected_memory = Some(region);
        self
    }

    /// Override the severity (e.g., when model analysis reveals more context).
    #[must_use]
    pub fn with_severity(mut self, severity: Severity) -> Self {
        self.severity = severity;
        self
    }

    /// Format the report as human-readable text.
    #[must_use]
    pub fn format(&self) -> String {
        format_report(self)
    }

    /// Format the report as markdown.
    #[must_use]
    pub fn format_markdown(&self) -> String {
        format_report_markdown(self)
    }
}

/// Classify a vulnerability from an assertion name.
///
/// Maps the assertion function names used in `MemoryModel` to vulnerability
/// types. Unknown assertion names default to `BufferOverflow`.
///
/// # Examples
///
/// ```rust
/// use ay_bindings::vuln_report::{classify_vulnerability, VulnType};
///
/// assert_eq!(classify_vulnerability("assert_valid_access"), VulnType::UseAfterFree);
/// assert_eq!(classify_vulnerability("assert_in_bounds"), VulnType::BufferOverflow);
/// assert_eq!(classify_vulnerability("assert_valid_free"), VulnType::DoubleFree);
/// assert_eq!(classify_vulnerability("assert_non_null"), VulnType::NullDeref);
/// ```
#[must_use]
pub fn classify_vulnerability(assertion_name: &str) -> VulnType {
    // Normalize: strip leading/trailing whitespace, convert to lowercase for matching
    let name = assertion_name.trim();

    // Exact matches for MemoryModel assertion methods
    if name == "assert_valid_access" {
        return VulnType::UseAfterFree;
    }
    if name == "assert_in_bounds" || name == "read_ok" || name == "write_ok" {
        return VulnType::BufferOverflow;
    }
    if name == "assert_valid_free" || name == "dealloc_ok" {
        return VulnType::DoubleFree;
    }
    if name == "assert_non_null" {
        return VulnType::NullDeref;
    }

    // Substring-based matching for user-defined assertion names.
    // Order matters: check more specific patterns before general ones.
    let lower = name.to_ascii_lowercase();
    if lower.contains("use_after") || lower.contains("uaf") || lower.contains("dangling") {
        return VulnType::UseAfterFree;
    }
    if lower.contains("null") || lower.contains("nullptr") {
        return VulnType::NullDeref;
    }
    if lower.contains("free") || lower.contains("dealloc") {
        return VulnType::DoubleFree;
    }
    if lower.contains("stack_escape") || lower.contains("stack_return") {
        return VulnType::StackEscape;
    }
    if lower.contains("overflow") || lower.contains("underflow") || lower.contains("wrap") {
        return VulnType::IntegerOverflow;
    }
    if lower.contains("bounds") || lower.contains("oob") || lower.contains("buffer") {
        return VulnType::BufferOverflow;
    }

    // Default: buffer overflow (most common class)
    VulnType::BufferOverflow
}

/// Compute severity from vulnerability type alone (simple heuristic).
///
/// - UAF, DoubleFree: High (heap corruption, often exploitable)
/// - BufferOverflow: High (often exploitable for code execution)
/// - StackEscape: High (dangling pointer, potential code execution)
/// - IntegerOverflow: Medium (depends on context)
/// - NullDeref: Medium (usually crash, sometimes exploitable)
#[must_use]
pub fn compute_severity_from_type(vuln_type: VulnType) -> Severity {
    match vuln_type {
        VulnType::UseAfterFree
        | VulnType::DoubleFree
        | VulnType::BufferOverflow
        | VulnType::StackEscape => Severity::High,
        VulnType::IntegerOverflow | VulnType::NullDeref => Severity::Medium,
    }
}

/// Build a human-readable explanation string.
fn build_explanation(
    vuln_type: VulnType,
    exploit_input: &[(String, String)],
    region: Option<&MemoryRegion>,
) -> String {
    let mut explanation = String::new();

    explanation.push_str(vuln_type.description());

    if let Some(region) = region {
        explanation.push_str("\n\nAffected memory: ");
        explanation.push_str(&region.to_string());
        explanation.push('.');

        // Add specific context based on vulnerability type
        match vuln_type {
            VulnType::BufferOverflow => {
                if let Some(alloc_size) = region.allocated_size {
                    let end = region.offset.saturating_add(region.access_size);
                    if end > alloc_size {
                        explanation.push_str(&format!(
                            "\nThe access at offset 0x{:x} with size {} exceeds the \
                             allocation boundary at {} bytes (overflow by {} bytes).",
                            region.offset,
                            region.access_size,
                            alloc_size,
                            end - alloc_size
                        ));
                    }
                }
            }
            VulnType::UseAfterFree => {
                explanation.push_str(&format!(
                    "\nObject #{} was freed before this access at offset 0x{:x}.",
                    region.object_id, region.offset
                ));
            }
            VulnType::DoubleFree => {
                explanation.push_str(&format!(
                    "\nObject #{} was already freed when a second free was attempted.",
                    region.object_id
                ));
            }
            _ => {}
        }
    }

    if !exploit_input.is_empty() {
        explanation.push_str("\n\nExploit inputs:");
        for (name, value) in exploit_input {
            explanation.push_str(&format!("\n  {name} = {value}"));
        }
    }

    explanation
}

/// Format a vulnerability report as human-readable plain text.
#[must_use]
pub fn format_report(report: &VulnerabilityReport) -> String {
    let mut out = String::new();

    // Header
    out.push_str(&format!(
        "=== Vulnerability Report ===\n\
         Type:     {}\n\
         Severity: {}\n\
         CWE:      {}\n",
        report.vuln_type.name(),
        report.severity.name(),
        report.vuln_type.cwe(),
    ));

    // Memory region
    if let Some(ref region) = report.affected_memory {
        out.push_str(&format!("Memory:   {region}\n"));
    }

    // Exploit inputs
    if !report.exploit_input.is_empty() {
        out.push_str("\n--- Exploit Inputs ---\n");
        for (name, value) in &report.exploit_input {
            out.push_str(&format!("  {name} = {value}\n"));
        }
    }

    // Explanation
    out.push_str(&format!("\n--- Explanation ---\n{}\n", report.explanation));

    out
}

/// Format a vulnerability report as markdown.
#[must_use]
pub fn format_report_markdown(report: &VulnerabilityReport) -> String {
    let mut out = String::new();

    // Header
    out.push_str(&format!(
        "# Vulnerability: {} ({})\n\n\
         **Severity:** {}  \n\
         **CWE:** [{}](https://cwe.mitre.org/data/definitions/{}.html)\n\n",
        report.vuln_type.name(),
        report.vuln_type.cwe(),
        report.severity.name(),
        report.vuln_type.cwe(),
        &report.vuln_type.cwe()[4..], // strip "CWE-" prefix for URL
    ));

    // Memory region
    if let Some(ref region) = report.affected_memory {
        out.push_str(&format!("**Affected memory:** {region}\n\n"));
    }

    // Exploit inputs
    if !report.exploit_input.is_empty() {
        out.push_str("## Exploit Inputs\n\n");
        out.push_str("| Variable | Value |\n");
        out.push_str("|----------|-------|\n");
        for (name, value) in &report.exploit_input {
            out.push_str(&format!("| `{name}` | `{value}` |\n"));
        }
        out.push('\n');
    }

    // Explanation
    out.push_str(&format!("## Explanation\n\n{}\n", report.explanation));

    out
}

#[cfg(test)]
#[path = "vuln_report_tests.rs"]
mod tests;
