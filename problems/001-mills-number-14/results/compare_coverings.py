"""Compare the 14-block obstruction with a pinned pair-covering index."""

import argparse
import csv
import hashlib
import json
import re
import sys
from fractions import Fraction
from math import gcd
from pathlib import Path


ARCHIVE_MD5 = "b2c626b07f216aac830d344eff5ad523"
CONTEMPORARY_UPPER = {(70, 21): 15}


def ceil_div(a, b):
    return (a + b - 1) // b


def compare(index):
    rows = []
    for key, entry in index.items():
        v, k, t = map(int, re.fullmatch(r"C\((\d+),(\d+),(\d+)\)", key).groups())
        archive_lower = int(entry["low_bd"])
        if t != 2 or 7 * v <= 23 * k or archive_lower >= 15:
            continue

        archive_upper = int(entry["size"])
        schoenheim = ceil_div(v * ceil_div(v - 1, k - 1), k)
        pair_count = ceil_div(v * (v - 1), k * (k - 1))
        # Compare k/v with (123 + sqrt(1297))/532 without rounding.
        radical_term = 532 * k - 123 * v
        hhs_excludes_14 = radical_term <= 0 or radical_term**2 <= 1297 * v**2
        earlier_project_excludes_14 = 10 * k <= 3 * v
        compared_upper = min(archive_upper, CONTEMPORARY_UPPER.get((v, k), archive_upper))
        if max(archive_lower, schoenheim, pair_count) > 14 or compared_upper < 15:
            raise ValueError(f"Inconsistent comparison for {key}")

        scale = gcd(v, k)
        upper_source = "La Jolla v1.2.1"
        if compared_upper < archive_upper:
            upper_source = "IRSI Sep 2026 / Meliwat and Canli Oct 2026"
        rows.append({
            "v": v,
            "k": k,
            "t": t,
            "k_over_v": str(Fraction(k, v)),
            "archive_lower": archive_lower,
            "archive_upper": archive_upper,
            "schoenheim_lower": schoenheim,
            "pair_count_lower": pair_count,
            "hhs_excludes_14": int(hhs_excludes_14),
            "earlier_project_excludes_14": int(earlier_project_excludes_14),
            "theorem_lower": 15,
            "compared_upper": compared_upper,
            "upper_source": upper_source,
            "outcome": "exact" if compared_upper == 15 else "lower_bound",
            "primitive_v": v // scale,
            "primitive_k": k // scale,
            "scale": scale,
        })
    return sorted(rows, key=lambda row: (row["v"], row["k"]))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("coverdata", type=Path, help="coverdata.json from Zenodo record 24119701")
    args = parser.parse_args()
    raw = args.coverdata.read_bytes()
    if hashlib.md5(raw, usedforsecurity=False).hexdigest() != ARCHIVE_MD5:
        raise SystemExit("Expected coverdata.json from La Jolla v1.2.1.")
    rows = compare(json.loads(raw))
    # These counts detect changes in the date-stamped comparison.
    if (len(rows), sum(row["hhs_excludes_14"] for row in rows),
            sum(row["earlier_project_excludes_14"] for row in rows),
            sum(row["outcome"] == "exact" for row in rows)) != (39, 24, 29, 20):
        raise SystemExit("Unexpected comparison totals.")
    writer = csv.DictWriter(sys.stdout, fieldnames=rows[0].keys(), lineterminator="\n")
    writer.writeheader()
    writer.writerows(rows)


if __name__ == "__main__":
    main()
