"""Verify 15 blocks on 70 points by accumulating every pair within each block."""

import argparse
from collections import Counter
from itertools import combinations
from pathlib import Path


def check(path):
    blocks = [
        tuple(sorted(map(int, line.split())))
        for line in path.read_text(encoding="utf-8-sig").splitlines()
        if line.strip()
    ]
    if len(blocks) != 15 or len(set(blocks)) != 15:
        raise ValueError("expected fifteen distinct blocks")
    counts = Counter()
    for block in blocks:
        if len(block) != 21 or len(set(block)) != 21 or not (1 <= block[0] <= block[-1] <= 70):
            raise ValueError("expected 21 distinct points from 1 to 70 per block")
        counts.update(combinations(block, 2))
    if len(counts) != 2415:
        missing = next(pair for pair in combinations(range(1, 71), 2) if pair not in counts)
        raise ValueError(f"only {len(counts)} pairs covered, missing {missing}")
    return dict(sorted(Counter(counts.values()).items()))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("files", nargs="+", type=Path)
    for path in parser.parse_args().files:
        print(f"{path}: 2415 pairs verified, multiplicities {check(path)}")
