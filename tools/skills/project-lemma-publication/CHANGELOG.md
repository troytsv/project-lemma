# Skill changelog

## 1.1.0 · 25 November 2026

Added the Palomar toolchain-floor check, exact-commit hosted preflight, and separate confirmation steps for submission and permanent registration. The Problem 001 port provides an example with seven independently stated contracts.

## 1.0.0 · 25 November 2026

First portable version. Adds Prepare, Publish, Audit and Disseminate, numbered-problem and index helpers, immutable action receipts, public release verification, manuscript and publication-record templates, and dated eligibility guidance. Uses the existing repository packager. The Problem 001 baseline distinguishes its published GitHub result, pending Zenodo inquiry, Palomar migration requirements and already-sent Covering Repository notice.

Scaffolding also generates draft citation metadata. Set the version, release date and persistent URL for the actual release. Run the offline regression suite from the repository root with `python -B tools/tests/test_publication_skill.py -v`. It exercises repeat allocation, index updates, uncertain actions, conflicting receipts, scoped archives and tamper detection.
