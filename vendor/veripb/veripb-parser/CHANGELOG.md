# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## 0.1.2 - 2026-03-20

### Bug Fixes
- Add OPB parser when degree is larger than sum of coefficients

### Commits

- Fix OPB parser if degree has larger type than coeff sum
- Add more parsing test cases
- Fix test
- Ignore some doc tests generated for non-rust code.

## 0.1.1 - 2025-11-02

### New Features
- Complete documentation for library function

### Changes
- Give useful errors if derivation file does not exist

### Bug Fixes
- Parsing of less than or equal constraint in OPB parser

### Commits

- Add documentation for parsing library
- Change to give useful errors when formula or derivation does not exist
- Fix OPB parser to parse <= constraints

## 0.1.0

This is the initial release of the library.
