// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Tests for vulnerability report generation.

use super::*;

// ===== VulnType Tests =====

#[test]
fn test_vuln_type_name_returns_human_readable_string() {
    assert_eq!(VulnType::BufferOverflow.name(), "Buffer Overflow");
    assert_eq!(VulnType::UseAfterFree.name(), "Use-After-Free");
    assert_eq!(VulnType::DoubleFree.name(), "Double Free");
    assert_eq!(VulnType::NullDeref.name(), "Null Pointer Dereference");
    assert_eq!(VulnType::StackEscape.name(), "Stack Pointer Escape");
    assert_eq!(VulnType::IntegerOverflow.name(), "Integer Overflow");
}

#[test]
fn test_vuln_type_cwe_returns_correct_identifiers() {
    assert_eq!(VulnType::BufferOverflow.cwe(), "CWE-120");
    assert_eq!(VulnType::UseAfterFree.cwe(), "CWE-416");
    assert_eq!(VulnType::DoubleFree.cwe(), "CWE-415");
    assert_eq!(VulnType::NullDeref.cwe(), "CWE-476");
    assert_eq!(VulnType::StackEscape.cwe(), "CWE-562");
    assert_eq!(VulnType::IntegerOverflow.cwe(), "CWE-190");
}

#[test]
fn test_vuln_type_description_is_nonempty() {
    let types = [
        VulnType::BufferOverflow,
        VulnType::UseAfterFree,
        VulnType::DoubleFree,
        VulnType::NullDeref,
        VulnType::StackEscape,
        VulnType::IntegerOverflow,
    ];
    for vuln in &types {
        let desc = vuln.description();
        assert!(!desc.is_empty(), "{vuln:?} has empty description");
        assert!(desc.len() > 20, "{vuln:?} has too-short description");
    }
}

#[test]
fn test_vuln_type_display() {
    assert_eq!(format!("{}", VulnType::BufferOverflow), "Buffer Overflow");
    assert_eq!(format!("{}", VulnType::UseAfterFree), "Use-After-Free");
}

// ===== Severity Tests =====

#[test]
fn test_severity_ordering() {
    assert!(Severity::Low < Severity::Medium);
    assert!(Severity::Medium < Severity::High);
}

#[test]
fn test_severity_display() {
    assert_eq!(format!("{}", Severity::Low), "Low");
    assert_eq!(format!("{}", Severity::Medium), "Medium");
    assert_eq!(format!("{}", Severity::High), "High");
}

// ===== Classification Tests =====

#[test]
fn test_classify_vulnerability_exact_matches() {
    assert_eq!(
        classify_vulnerability("assert_valid_access"),
        VulnType::UseAfterFree
    );
    assert_eq!(
        classify_vulnerability("assert_in_bounds"),
        VulnType::BufferOverflow
    );
    assert_eq!(
        classify_vulnerability("assert_valid_free"),
        VulnType::DoubleFree
    );
    assert_eq!(
        classify_vulnerability("assert_non_null"),
        VulnType::NullDeref
    );
    assert_eq!(classify_vulnerability("read_ok"), VulnType::BufferOverflow);
    assert_eq!(classify_vulnerability("write_ok"), VulnType::BufferOverflow);
    assert_eq!(classify_vulnerability("dealloc_ok"), VulnType::DoubleFree);
}

#[test]
fn test_classify_vulnerability_substring_matches() {
    assert_eq!(
        classify_vulnerability("check_null_ptr"),
        VulnType::NullDeref
    );
    assert_eq!(
        classify_vulnerability("assert_no_nullptr"),
        VulnType::NullDeref
    );
    assert_eq!(
        classify_vulnerability("check_free_valid"),
        VulnType::DoubleFree
    );
    assert_eq!(
        classify_vulnerability("use_after_free_check"),
        VulnType::UseAfterFree
    );
    assert_eq!(
        classify_vulnerability("uaf_detector"),
        VulnType::UseAfterFree
    );
    assert_eq!(
        classify_vulnerability("dangling_pointer_check"),
        VulnType::UseAfterFree
    );
    assert_eq!(
        classify_vulnerability("stack_escape_check"),
        VulnType::StackEscape
    );
    assert_eq!(
        classify_vulnerability("integer_overflow_check"),
        VulnType::IntegerOverflow
    );
    assert_eq!(
        classify_vulnerability("bounds_check"),
        VulnType::BufferOverflow
    );
    assert_eq!(
        classify_vulnerability("oob_access"),
        VulnType::BufferOverflow
    );
}

#[test]
fn test_classify_vulnerability_default_is_buffer_overflow() {
    assert_eq!(
        classify_vulnerability("unknown_assertion"),
        VulnType::BufferOverflow
    );
}

#[test]
fn test_classify_vulnerability_strips_whitespace() {
    assert_eq!(
        classify_vulnerability("  assert_valid_access  "),
        VulnType::UseAfterFree
    );
}

// ===== Severity Computation Tests =====

#[test]
fn test_compute_severity_high_for_memory_corruption() {
    assert_eq!(
        compute_severity_from_type(VulnType::UseAfterFree),
        Severity::High
    );
    assert_eq!(
        compute_severity_from_type(VulnType::DoubleFree),
        Severity::High
    );
    assert_eq!(
        compute_severity_from_type(VulnType::BufferOverflow),
        Severity::High
    );
    assert_eq!(
        compute_severity_from_type(VulnType::StackEscape),
        Severity::High
    );
}

#[test]
fn test_compute_severity_medium_for_lesser_vulns() {
    assert_eq!(
        compute_severity_from_type(VulnType::IntegerOverflow),
        Severity::Medium
    );
    assert_eq!(
        compute_severity_from_type(VulnType::NullDeref),
        Severity::Medium
    );
}

// ===== MemoryRegion Tests =====

#[test]
fn test_memory_region_display_without_alloc_size() {
    let region = MemoryRegion {
        object_id: 3,
        offset: 0x10,
        access_size: 4,
        allocated_size: None,
    };
    let s = format!("{region}");
    assert!(s.contains("object #3"));
    assert!(s.contains("0x00000010"));
    assert!(s.contains("4 bytes"));
}

#[test]
fn test_memory_region_display_with_alloc_size() {
    let region = MemoryRegion {
        object_id: 1,
        offset: 0x20,
        access_size: 8,
        allocated_size: Some(32),
    };
    let s = format!("{region}");
    assert!(s.contains("object #1"));
    assert!(s.contains("allocated: 32 bytes"));
}

// ===== VulnerabilityReport Tests =====

#[test]
fn test_report_new_sets_default_severity() {
    let report = VulnerabilityReport::new(
        VulnType::UseAfterFree,
        vec![("ptr".into(), "0x00010020".into())],
    );
    assert_eq!(report.vuln_type, VulnType::UseAfterFree);
    assert_eq!(report.severity, Severity::High);
    assert_eq!(report.exploit_input.len(), 1);
    assert!(report.affected_memory.is_none());
    assert!(!report.explanation.is_empty());
}

#[test]
fn test_report_with_memory_region() {
    let region = MemoryRegion {
        object_id: 2,
        offset: 0x40,
        access_size: 16,
        allocated_size: Some(8),
    };
    let report =
        VulnerabilityReport::new(VulnType::BufferOverflow, vec![]).with_memory_region(region);
    assert!(report.affected_memory.is_some());
    let mem = report.affected_memory.as_ref().unwrap();
    assert_eq!(mem.object_id, 2);
    // offset=0x40=64, access_size=16 => end=80, alloc=8 => overflow by 72
    assert!(report.explanation.contains("overflow by 72 bytes"));
}

#[test]
fn test_report_with_severity_override() {
    let report = VulnerabilityReport::new(VulnType::NullDeref, vec![]).with_severity(Severity::Low);
    assert_eq!(report.severity, Severity::Low);
}

// ===== Format Tests =====

#[test]
fn test_format_report_contains_required_sections() {
    let report = VulnerabilityReport::new(
        VulnType::DoubleFree,
        vec![
            ("ptr".into(), "0x00020000".into()),
            ("size".into(), "64".into()),
        ],
    );
    let text = report.format();

    assert!(text.contains("Vulnerability Report"));
    assert!(text.contains("Double Free"));
    assert!(text.contains("High"));
    assert!(text.contains("CWE-415"));
    assert!(text.contains("Exploit Inputs"));
    assert!(text.contains("ptr = 0x00020000"));
    assert!(text.contains("size = 64"));
    assert!(text.contains("Explanation"));
}

#[test]
fn test_format_report_with_memory_region() {
    let region = MemoryRegion {
        object_id: 5,
        offset: 0,
        access_size: 4,
        allocated_size: Some(4),
    };
    let report =
        VulnerabilityReport::new(VulnType::UseAfterFree, vec![]).with_memory_region(region);
    let text = report.format();
    assert!(text.contains("Memory:"));
    assert!(text.contains("object #5"));
}

#[test]
fn test_format_report_markdown_contains_headers() {
    let report = VulnerabilityReport::new(
        VulnType::BufferOverflow,
        vec![("input_len".into(), "256".into())],
    );
    let md = report.format_markdown();

    assert!(md.contains("# Vulnerability:"));
    assert!(md.contains("Buffer Overflow"));
    assert!(md.contains("**Severity:** High"));
    assert!(md.contains("CWE-120"));
    assert!(md.contains("## Exploit Inputs"));
    assert!(md.contains("| `input_len` | `256` |"));
    assert!(md.contains("## Explanation"));
}

#[test]
fn test_format_report_markdown_empty_inputs() {
    let report = VulnerabilityReport::new(VulnType::NullDeref, vec![]);
    let md = report.format_markdown();

    // No exploit inputs section when empty
    assert!(!md.contains("## Exploit Inputs"));
    assert!(md.contains("Null Pointer Dereference"));
}

// ===== Report for Each Vuln Type =====

#[test]
fn test_generate_report_for_each_vuln_type() {
    let types = [
        VulnType::BufferOverflow,
        VulnType::UseAfterFree,
        VulnType::DoubleFree,
        VulnType::NullDeref,
        VulnType::StackEscape,
        VulnType::IntegerOverflow,
    ];

    for vuln_type in &types {
        let report = VulnerabilityReport::new(*vuln_type, vec![("test_var".into(), "42".into())]);

        // Report is well-formed
        assert_eq!(report.vuln_type, *vuln_type);
        assert!(!report.explanation.is_empty());

        // Format produces non-empty text
        let text = report.format();
        assert!(!text.is_empty());
        assert!(text.contains(vuln_type.name()));

        // Markdown format produces non-empty text
        let md = report.format_markdown();
        assert!(!md.is_empty());
        assert!(md.contains(vuln_type.cwe()));
    }
}

// ===== Buffer Overflow Explanation Detail =====

#[test]
fn test_buffer_overflow_explanation_with_overflow_detail() {
    let region = MemoryRegion {
        object_id: 1,
        offset: 8,
        access_size: 4,
        allocated_size: Some(10),
    };
    let report =
        VulnerabilityReport::new(VulnType::BufferOverflow, vec![]).with_memory_region(region);
    // Access at offset 8 with size 4 = end at 12, alloc is 10 => overflow by 2
    assert!(report.explanation.contains("overflow by 2 bytes"));
}

#[test]
fn test_uaf_explanation_mentions_freed_object() {
    let region = MemoryRegion {
        object_id: 7,
        offset: 0,
        access_size: 8,
        allocated_size: None,
    };
    let report =
        VulnerabilityReport::new(VulnType::UseAfterFree, vec![]).with_memory_region(region);
    assert!(report.explanation.contains("Object #7 was freed"));
}

#[test]
fn test_double_free_explanation_mentions_object() {
    let region = MemoryRegion {
        object_id: 3,
        offset: 0,
        access_size: 0,
        allocated_size: None,
    };
    let report = VulnerabilityReport::new(VulnType::DoubleFree, vec![]).with_memory_region(region);
    assert!(report.explanation.contains("Object #3 was already freed"));
}
