"""Verify a pair covering by testing intersections of point incidence masks."""

import argparse
from pathlib import Path


def verify(source: str, points: int = 70, size: int = 21, count: int = 15) -> int:
    rows = [line.split() for line in source.splitlines() if line.strip()]
    if len(rows) != count:
        raise ValueError(f"expected {count} blocks, found {len(rows)}")

    masks = [0] * points
    for index, row in enumerate(rows, start=1):
        block = [int(token) for token in row]
        if len(block) != size or len(set(block)) != size:
            raise ValueError(f"block {index} must contain {size} distinct points")
        for point in block:
            if not 1 <= point <= points:
                raise ValueError(f"block {index} contains out-of-range point {point}")
            masks[point - 1] |= 1 << (index - 1)

    checked = 0
    for right, mask in enumerate(masks):
        for left in range(right):
            if masks[left] & mask == 0:
                raise ValueError(f"uncovered pair ({left + 1}, {right + 1})")
            checked += 1
    return checked


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="+", type=Path)
    parser.add_argument("--blocks", type=int, default=15)
    args = parser.parse_args()
    if args.blocks < 1:
        parser.error("--blocks must be positive")

    failed = False
    for path in args.paths:
        try:
            checked = verify(path.read_text(encoding="utf-8-sig"), count=args.blocks)
        except (OSError, ValueError) as exc:
            print(f"{path}: FAIL: {exc}")
            failed = True
        else:
            print(f"{path}: PASS: {args.blocks} blocks of 21, {checked} pairs covered")
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
