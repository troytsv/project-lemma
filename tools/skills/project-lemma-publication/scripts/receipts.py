"""Record external-action intent and evidence. No network operations."""
import argparse
import json
import re
from datetime import datetime, timezone
from pathlib import Path


def write_once(path, data):
    with path.open("x", encoding="utf-8") as output:
        json.dump({"utc": datetime.now(timezone.utc).isoformat(), **data}, output,
                  ensure_ascii=False, indent=2)
        output.write("\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("problem", type=Path)
    parser.add_argument("action", choices=("inspect", "begin", "finish"))
    parser.add_argument("key", help="Stable ID for version, destination and purpose")
    parser.add_argument("--evidence", help="Public request scope or reconciled outcome reference")
    parser.add_argument("--outcome", choices=("confirmed", "rejected", "withdrawn"))
    args = parser.parse_args()
    if not re.fullmatch(r"[a-z0-9][a-z0-9.-]{0,150}", args.key):
        parser.error("invalid receipt key")
    if not (args.problem / "PUBLICATION.md").is_file():
        parser.error("expected the problem directory with its publication record")
    folder = args.problem / "publication-actions" / args.key
    start, end = folder / "intent.json", folder / "outcome.json"
    if args.action == "inspect":
        if not folder.exists():
            print("No structured receipt. Reconcile PUBLICATION.md and the external service.")
        elif end.exists():
            print(json.dumps(json.loads(end.read_text(encoding="utf-8")), ensure_ascii=False))
        else:
            print("Unresolved intent. Inspect the external service before any retry.")
        return
    if not args.evidence or not args.evidence.strip():
        parser.error("an evidence reference is required")
    if args.action == "begin":
        folder.parent.mkdir(exist_ok=True)
        try:
            folder.mkdir()
        except FileExistsError:
            parser.exit(2, "Existing intent or outcome. Reconcile it; do not perform a second action.\n")
        write_once(start, {"key": args.key, "scope": args.evidence})
        return
    if not args.outcome or not start.exists():
        parser.error("finish requires a recorded intent and known outcome")
    if end.exists():
        recorded = json.loads(end.read_text(encoding="utf-8"))
        if recorded["outcome"] != args.outcome or recorded["evidence"] != args.evidence:
            parser.error("conflicting evidence; preserve the original and document the correction")
        return
    write_once(end, {"key": args.key, "outcome": args.outcome, "evidence": args.evidence})


if __name__ == "__main__":
    main()
