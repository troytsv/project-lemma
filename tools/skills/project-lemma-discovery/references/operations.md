# Running a campaign

Use Python 3 and the installed skill directory when locating scripts. From the repository root run `python <skill>/scripts/discover.py --db discovery/private/opportunities.sqlite COMMAND ...`. Omit --db for that default. The database uses SQLite transactions and requires no service or packages. The candidate format is [candidate.schema.json](../assets/candidate.schema.json). The importer accepts a JSON array and validates required fields. A candidate's key is its stable ID. Dates use YYYY-MM-DD. Unavailable information gets an explicit reason. Use an empty score object for leads that have not been assessed in depth.

| Command | Operation |
|---|---|
| ingest FILE | Import the entire batch atomically. Same key and contents replay cleanly. Statement, title and curated aliases detect duplicates across keys. Inspect reported collisions. Compare equivalent formulations manually. |
| show KEY | Return a record and its revision. An ingested alternate key resolves to the original. |
| revise FILE --expected REVISION | Replace one complete canonical record after a probe/novelty check. A concurrent or stale revision is rejected. Retain superseded records in history. |
| status KEY STATE --reason TEXT | Change status with an evidence-based reason. Solved records cannot advance. All five gates and justified scores are required for the shortlist and recommendations. |
| rank / export | Show the eligible scored shortlist or all canonical rows as JSON. |
| handoff KEY | Write Markdown to stdout for an eligible shortlisted or recommended row. Save under the campaign folder. Include any setup, executable probe paths, source-by-source evidence and a comparison with alternatives in the finished document. |
| feedback KEY FILE / outcomes | Store and retrieve post-investigation outcomes; repeated identical feedback is idempotent. Use the seven fields in [feedback.json](../assets/feedback.json). |

Keep source snapshots, immutable input batches, candidate revisions, dated query logs and probe receipts under a dated campaign folder alongside the database. Save checkpoints after Survey, Shortlist, Probe and Recommend. On interruption, inspect existing exports, notes and results and rerun the last uncommitted batch. SQLite rolls incomplete edits back. Check an existing probe receipt before rerunning a costly computation; keep its parameters and input digest. Use a fresh output filename for a changed experiment. The text export is readable without SQLite. Back up the database while closed along with the local directory. It is outside normal Git backup.

After a study, separate what was known at screening from information learned later. Record estimate vs actual, promising and exhausted approaches, measured usage, obstacles, reusable techniques, novelty outcome and disposition. Read these outcomes before changing scores, reopening old candidates or designing new probes.
