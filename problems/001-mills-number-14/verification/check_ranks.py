"""Recheck the numerical cases of the weighted proof using exact fractions."""

from fractions import Fraction
from itertools import combinations_with_replacement


def possible_profiles():
    # At most 6 of 30 units have rank >4, by the excess bound. Each four
    # carries at most 2. At most 14 positive weights survive compression.
    for fours in range(15):
        if 2 * fours + 6 < 30:
            continue
        for others in range(15 - fours):
            for higher in combinations_with_replacement(range(5, 15), others):
                remaining = Fraction(30)
                excess = Fraction(0)
                # Filling lower ranks first minimizes excess for a fixed total.
                # Allowing zero weights here relaxes the feasibility conditions.
                for rank in (4,) * fours + higher:
                    cap = Fraction(9 * rank - 30, rank - 1)
                    weight = min(cap, remaining)
                    remaining -= weight
                    excess += (rank - 4) * weight
                if remaining == 0 and excess <= 6:
                    yield (fours, higher, excess)


if __name__ == "__main__":
    profiles = list(possible_profiles())
    if profiles != [(12, (5, 5), 6)]:
        raise SystemExit(f"unexpected profiles: {profiles}")
    # In the surviving profile every four weighs 2 and every load equals 9.
    # At least four indices avoid both fives and have only weight-2 summands.
    outside = 14 - 2 * 5
    loads_from_fours = {2 * through for through in range(13)}
    if outside <= 0 or 9 in loads_from_fours:
        raise SystemExit("the final contradiction failed")
    print("Only profile: twelve fours and two fives. Outside load 9 is impossible.")
