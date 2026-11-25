"""Compare k/v for all t=2, size<=14 entries in the November 2026 La Jolla index.

Pass coverdata.json from https://doi.org/10.5281/zenodo.24119701.
"""

import hashlib
import json
import re
import sys
from fractions import Fraction
from pathlib import Path


def main(path):
    raw = path.read_bytes()
    if hashlib.md5(raw, usedforsecurity=False).hexdigest() != "b2c626b07f216aac830d344eff5ad523":
        raise ValueError("Expected the coverdata.json file from version 1.2.1.")
    index = json.loads(raw)
    ratios = []
    for key, bounds in index.items():
        v, k, t = map(int, re.fullmatch(r"C\((\d+),(\d+),(\d+)\)", key).groups())
        if t == 2 and int(bounds["size"]) <= 14:
            ratios.append((Fraction(k, v), key))
    least = min(ratio for ratio, _ in ratios)
    print(f"{len(ratios)} qualifying entries. Minimum listed k/v = {least}.")
    for ratio, key in ratios:
        if ratio == least:
            print(key, index[key])


if __name__ == "__main__":
    main(Path(sys.argv[1]))
