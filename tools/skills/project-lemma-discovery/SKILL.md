---
name: project-lemma-discovery
description: Survey, shortlist, probe, and recommend open mathematical problems for Project Lemma. Use for opportunity screening, historical novelty, bounded mathematical experiments and research handoffs before a numbered project is selected.
---

# Project Lemma discovery

Work from the Project Lemma repository. Keep the campaign under `discovery/private/` (local and ignored by Git). Use the bundled `scripts/discover.py` and [operating guide](references/operations.md). Reuse the existing SQLite ledger across campaigns. Begin by reading earlier outcomes, deferred items and the latest completed research. The [evaluation rubric](references/rubric.md) sets the gates, score, effort allocation and stopping rules. The [source guide](references/sources.md) gives starting points.

| Mode | Deliverable |
| --- | --- |
| Survey | Source snapshot, dated candidate batch, retained exclusions and deduplicated ledger. Record a parameter family once when a single argument would resolve it. |
| Shortlist | Primary statement, current bounds, equivalent formulations, later citations, formal and AI searches, competing groups, independent checker and cost ceiling. Resolve disagreement before marking the open gate true. |
| Probe | Run bounded, conventional computation or a mathematical reduction. Preserve inputs, code, budgets, time, baseline and exact outcomes. Verify any witness separately. Reassess the scores and record a reason to continue or stop. |
| Recommend | Rank eligible candidates, compare fields and valuable partial outcomes. Generate a standalone handoff for every recommended candidate, explaining why it beats alternatives and when to switch. |

Keep the seven-factor base out of 100. For eligible candidates, subtract 0.8 × (10 − public competition headroom on a 0–10 scale), floored at zero. Report both numbers. A failed gate always excludes a candidate, even with a base of 100.

An open label or an unsuccessful search cannot certify global priority. Distinguish a sourced historical question from a new question derived during this campaign. Treat a claimed proof, a solved special case, an open family and a missing formalization separately. Keep retrospective evidence out of contemporary estimates.

Use the existing subscription, local computer and freely readable sources. Never spend, submit, publish, register a result, or contact a maintainer as part of ordinary discovery. Keep the public skill portable and the working database, experiment outputs and recommendation files private. End at the handoff. Creating a permanent numbered investigation or beginning a full attempt requires the user's selection.

After a completed investigation, record what actually worked, resources and priority evidence with `feedback`; consult `outcomes` at the next campaign. Maintain the portable instructions, tests and installed copy together. Change rubric weights only after reviewing outcomes across several investigations and recording an explicit rationale and version.
