"""Check the fourteen-block upper witness using integer incidence only."""

from itertools import combinations


EDGE_WEIGHTS = (
    (7680, 5),
    (2209, 3),
    (4152, 5),
    (4544, 5),
    (804, 5),
    (2132, 5),
    (1122, 5),
    (1164, 5),
    (9489, 6),
    (658, 5),
    (2314, 5),
    (8777, 6),
    (12295, 6),
    (10400, 3),
)


def main():
    masks = [mask for mask, _ in EDGE_WEIGHTS]
    assert len(set(masks)) == len(masks) == 14
    assert all(0 < mask < 1 << 14 and weight > 0 for mask, weight in EDGE_WEIGHTS)
    assert all(left & right for left, right in combinations(masks, 2))

    points = [mask for mask, weight in EDGE_WEIGHTS for _ in range(weight)]
    assert len(points) == 69
    blocks = [
        {point for point, mask in enumerate(points) if mask & (1 << vertex)}
        for vertex in range(14)
    ]
    assert len({frozenset(block) for block in blocks}) == 14
    assert all(len(block) == 21 for block in blocks)
    covered_pairs = {pair for block in blocks for pair in combinations(sorted(block), 2)}
    assert covered_pairs == set(combinations(range(69), 2))
    print(f"Verified 14 distinct 21-point blocks cover all {len(covered_pairs)} pairs on 69 points.")
    print("Therefore C(69,21,2) <= 14 and L(14) <= 7/23.")


if __name__ == "__main__":
    main()
