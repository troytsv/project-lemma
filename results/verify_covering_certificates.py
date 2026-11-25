"""Verify the ten bundled constructions and optionally replay all 39 archive entries."""

import argparse
import csv
import hashlib
import json
import re
from itertools import combinations
from pathlib import Path


def verify(key, blocks, size):
    v, k = map(int, re.fullmatch(r"C\((\d+),(\d+),2\)", key).groups())
    points = set(range(1, v + 1))
    if len(blocks) != size or len({frozenset(block) for block in blocks}) != size:
        raise SystemExit(f"{key}: expected {size} distinct blocks.")
    if any(len(block) != k or len(set(block)) != k or not set(block) <= points
           for block in blocks):
        raise SystemExit(f"{key}: block size, duplication, or point range error.")
    covered = {pair for block in blocks for pair in combinations(sorted(block), 2)}
    missing = set(combinations(sorted(points), 2)) - covered
    if missing:
        raise SystemExit(f"{key}: missing pair {min(missing)}.")
    return len(covered)


def check_archive(prefix, rows, bundled):
    expected_hash = "baa5b3c9f226248f5f4afb7172f165e5f6916c029b9053eb62d9cbffee8d70cf"
    if hashlib.sha256(prefix).hexdigest() != expected_hash:
        raise SystemExit("Expected bytes 0 through 4,999,999 of the pinned covers.json.")

    decoder = json.JSONDecoder()
    archive = prefix.decode("utf-8")
    for row in rows:
        key = f"C({row['v']},{row['k']},2)"
        start = archive.index("[", archive.index(json.dumps(key)))
        blocks, _ = decoder.raw_decode(archive, start)
        verify(key, blocks, int(row["archive_upper"]))
        if key in bundled and blocks != bundled[key]:
            raise SystemExit(f"{key}: bundled blocks differ from covers.json.")
    print(f"Verified all {len(rows)} archive entries and matched the bundled block lists.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive-prefix", type=Path)
    args = parser.parse_args()
    directory = Path(__file__).parent
    covers = json.loads((directory / "covering-certificates.json").read_text(encoding="utf-8"))
    with (directory / "pair-coverings.csv").open(encoding="utf-8-sig", newline="") as table:
        rows = list(csv.DictReader(table))
    expected_keys = {f"C({row['v']},{row['k']},2)" for row in rows
                     if row["earlier_project_excludes_14"] == "0" and row["outcome"] == "exact"}
    if len(covers) != 10 or covers.keys() != expected_keys:
        raise SystemExit("Expected ten certificates matching the exact cells beyond 3/10.")
    for key, blocks in covers.items():
        print(f"{key}: verified 15 blocks and {verify(key, blocks, 15)} pairs.")
    if args.archive_prefix:
        check_archive(args.archive_prefix.read_bytes(), rows, covers)


if __name__ == "__main__":
    main()
