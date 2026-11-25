---
name: project-lemma-publication
description: Prepare, publish, audit, or disseminate a numbered Project Lemma mathematical investigation. Use for research releases, proof and citation checks, archive eligibility, or targeted database updates in troytsv/project-lemma.
---

# Project Lemma publication

Resolve the checkout of `troytsv/project-lemma`, problem directory, version and requested mode. Run bundled Python scripts using their paths relative to **this skill**. Run repository commands from the checkout. Assume no access to earlier chats. Use the problem README, verification evidence, dated policy decisions and `PUBLICATION.md` to reconstruct state. For 001, that Markdown record predates the action-receipt helper and remains authoritative for past actions.

| Mode | What to execute |
| --- | --- |
| **Prepare** | Assemble the investigation locally. Review the proof, replay applicable checks, compile the paper, build candidate assets and update the local index. Leave publishing and contact for their authorized stage. |
| **Publish** | Perform Prepare checks and reconcile the remote. An instruction to publish a named problem authorizes ordinary GitHub commit, push, CI, tagged release and public download verification. Carry out supplementary submissions or notifications only within their own authorization. |
| **Audit** | Read-only. Check a specified version, inspect the action record, independently replay checks in a temporary checkout/output directory and report discrepancies. Keep the original tree and all external services read-only. |
| **Disseminate** | Start from a verified published version. Recheck external eligibility, existing records and correspondence. Perform only authorized outstanding registrations or targeted notifications. |

1. **Identify the result.** Start with [research and manuscript checks](references/research.md). Report mathematical correctness, scope of mechanical verification, historical priority and independent peer review separately. Preserve the actual intellectual contributions. Unknown priority can be disclosed. Unresolved proof, material privacy, rights or reproducibility defects block publication.
2. **Prepare or audit the artifacts.** Follow [GitHub and recovery procedures](references/release.md). Use the existing per-problem commands. `scripts/audit_release.py` checks the public assets against the tagged Git tree and named workflow at the same commit. A successful download alone cannot verify a proof. Inspect the report and actual theorem contracts.
3. **Register or notify.** Consult the [dated platform registry](references/platforms.md) and current official rules. Check eligibility for the origin of the mathematics as well as the formalization. Record the reason for skipping a destination and continue independent work. A DOI is optional.
4. **Finish with receipts.** Update the problem's publication record after each stage, including negative results and outstanding decisions. Verify the public outcome of each external action. A skill invocation conveys no blanket external authorization. Spend nothing. For auth, CAPTCHA, missing permission, or a material decision, request only the specific intervention required. Keep recipients, portals and prior submissions scoped to the problem.

After a completed publication, record operational lessons in the problem history. Apply reusable fixes to the portable source under `tools/skills/project-lemma-publication/`, test in a disposable checkout, update its [changelog](CHANGELOG.md), and synchronize the installed copy. Journal or arXiv submissions, paid options, affiliations and broad outreach are outside ordinary GitHub publication.

Examples: `$project-lemma-publication Prepare Problem 002`, `$project-lemma-publication Publish Problem 002 to GitHub`, `$project-lemma-publication Audit Problem 001`, `$project-lemma-publication Disseminate Problem 002: notify the specified database once`.
