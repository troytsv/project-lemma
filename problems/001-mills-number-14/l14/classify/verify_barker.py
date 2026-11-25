"""Check Colin Barker's archived 14-block covering and its relabeling.

Source: Daniel M. Gordon, La Jolla Coverings Repository v1.2.1,
https://doi.org/10.5281/zenodo.24119701 (CC BY 4.0).
Entry C(69,21,2) in covers.json, bytes 3243870 through 3244787 inclusive.
Contributor: Colin Barker, 2008-12-28, simulated annealing.
"""

from collections import Counter
from itertools import combinations

from verify_witness import EDGE_WEIGHTS


BLOCKS = (
    (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21),
    (1, 5, 10, 12, 21, 22, 23, 29, 33, 36, 38, 41, 44, 49, 50, 53, 56, 58, 62, 65, 66),
    (1, 5, 10, 12, 21, 24, 26, 28, 31, 34, 35, 37, 39, 43, 45, 48, 52, 57, 59, 60, 61),
    (1, 5, 10, 12, 21, 25, 27, 30, 32, 40, 42, 46, 47, 51, 54, 55, 63, 64, 67, 68, 69),
    (2, 6, 14, 15, 16, 19, 22, 26, 28, 32, 34, 36, 41, 44, 51, 52, 61, 63, 65, 68, 69),
    (2, 6, 14, 15, 16, 19, 23, 25, 30, 42, 45, 46, 47, 48, 49, 56, 57, 58, 59, 60, 62),
    (2, 6, 16, 24, 27, 29, 31, 33, 35, 37, 38, 39, 40, 43, 50, 53, 54, 55, 64, 66, 67),
    (3, 4, 8, 9, 18, 22, 24, 25, 30, 31, 35, 36, 37, 39, 41, 42, 43, 44, 46, 47, 65),
    (3, 4, 8, 9, 18, 23, 26, 27, 28, 34, 40, 49, 52, 54, 55, 56, 58, 61, 62, 64, 67),
    (3, 4, 8, 9, 18, 29, 32, 33, 38, 45, 48, 50, 51, 53, 57, 59, 60, 63, 66, 68, 69),
    (7, 11, 13, 17, 20, 22, 27, 36, 40, 41, 44, 45, 48, 54, 55, 57, 59, 60, 64, 65, 67),
    (7, 11, 13, 17, 20, 23, 24, 31, 32, 35, 37, 39, 43, 49, 51, 56, 58, 62, 63, 68, 69),
    (7, 11, 13, 17, 20, 25, 26, 28, 29, 30, 33, 34, 38, 42, 46, 47, 50, 52, 53, 61, 66),
    (14, 15, 19, 24, 27, 29, 31, 33, 35, 37, 38, 39, 40, 43, 50, 53, 54, 55, 64, 66, 67),
)
BARKER_TO_WITNESS = (5, 1, 6, 10, 7, 11, 0, 9, 8, 2, 4, 3, 12, 13)


def main():
    points = set(range(1, 70))
    if len(BLOCKS) != 14 or len({frozenset(block) for block in BLOCKS}) != 14:
        raise SystemExit("Expected 14 distinct blocks.")
    if any(len(block) != 21 or len(set(block)) != 21 or not set(block) <= points
           for block in BLOCKS):
        raise SystemExit("Each block must contain 21 distinct points from 1 through 69.")
    covered = {pair for block in BLOCKS for pair in combinations(sorted(block), 2)}
    if covered != set(combinations(sorted(points), 2)):
        raise SystemExit("The blocks do not cover all point pairs.")
    if sorted(BARKER_TO_WITNESS) != list(range(14)):
        raise SystemExit("The block relabeling must be a permutation of 0 through 13.")
    incidence = Counter(
        sum(1 << bit for block, bit in zip(BLOCKS, BARKER_TO_WITNESS) if point in block)
        for point in points
    )
    if incidence != Counter(dict(EDGE_WEIGHTS)):
        raise SystemExit("The relabeled weighted incidence patterns differ from the Lean witness.")
    print(f"Verified Barker's 14 blocks, all {len(covered)} point pairs, and the weighted relabeling.")

    split = {0, 13}
    edges = {frozenset(bit for bit in range(14) if mask & (1 << bit)): weight
             for mask, weight in incidence.items()}
    profile = Counter((len(edge & split), weight) for edge, weight in edges.items())
    if profile != {(0, 5): 9, (1, 3): 2, (2, 6): 3}:
        raise SystemExit("The edge weights do not match the split-point construction.")
    if len({edge - split for edge in edges if len(edge & split) == 1}) != 1:
        raise SystemExit("The two split edges must share all three old points.")
    plane = {(edge - split) | ({0} if edge & split else set()) for edge in edges}
    if len(plane) != 13 or any(len(line) != 4 for line in plane):
        raise SystemExit("Reuniting the split point must give thirteen 4-point lines.")
    line_pairs = Counter(pair for line in plane for pair in combinations(sorted(line), 2))
    if line_pairs != Counter(combinations(range(13), 2)):
        raise SystemExit("The recovered lines do not form a projective plane of order three.")
    print("Verified the projective plane of order three after reuniting bits 0 and 13.")


if __name__ == "__main__":
    main()
