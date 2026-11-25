from pathlib import Path
import unittest

from verify_dual import verify


BASELINE = Path(__file__).resolve().parents[2] / "certificates"
# Each permutation maps 1-based indices from known15.txt to the named file.
RELABELINGS = {
    "meliwat15.txt": (
        (2, 7, 3, 5, 10, 14, 15, 9, 12, 11, 4, 1, 6, 8, 13),
        (
            17, 1, 4, 22, 45, 8, 33, 5, 9, 19, 3, 11, 18, 26, 28, 10, 41, 49,
            7, 32, 39, 13, 38, 54, 14, 6, 16, 50, 48, 63, 70, 12, 15, 35, 27, 44,
            51, 20, 24, 62, 21, 2, 31, 25, 68, 23, 58, 60, 64, 69, 29, 42, 47,
            56, 30, 53, 40, 34, 52, 37, 36, 61, 57, 43, 65, 66, 46, 55, 59, 67,
        ),
    ),
    "irsi-original.txt": (
        (13, 6, 3, 15, 5, 1, 2, 10, 9, 11, 4, 7, 8, 14, 12),
        (
            32, 56, 36, 37, 19, 64, 44, 1, 23, 9, 57, 11, 24, 48, 65, 2, 33,
            45, 40, 18, 52, 12, 67, 41, 3, 27, 4, 53, 20, 21, 69, 58, 59, 49, 70,
            34, 54, 28, 25, 26, 29, 31, 5, 38, 39, 60, 30, 66, 46, 22, 13, 50,
            68, 42, 14, 15, 10, 6, 35, 61, 7, 43, 51, 62, 47, 16, 8, 63, 55, 17,
        ),
    ),
}


class VerificationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.known = (BASELINE / "known15.txt").read_text(encoding="utf-8-sig")

    def test_bundled_certificate_covers_all_pairs(self):
        self.assertEqual(verify(self.known), 2415)

    def test_published_certificates_are_isomorphic(self):
        known = [set(map(int, line.split())) for line in self.known.splitlines()]
        for name, (block_map, point_map) in RELABELINGS.items():
            with self.subTest(certificate=name):
                path = BASELINE / name
                if not path.is_file():
                    self.skipTest(f"optional comparison certificate: {path.name}")
                source = path.read_text(encoding="utf-8-sig")
                self.assertEqual(verify(source), 2415)
                other = [set(map(int, line.split())) for line in source.splitlines()]
                self.assertEqual(sorted(block_map), list(range(1, 16)))
                self.assertEqual(sorted(point_map), list(range(1, 71)))
                for block, mapped_index in zip(known, block_map, strict=True):
                    self.assertEqual(
                        {point_map[point - 1] for point in block}, other[mapped_index - 1]
                    )

    def test_rejects_missing_block(self):
        truncated = "\n".join(self.known.splitlines()[1:])
        with self.assertRaisesRegex(ValueError, "expected 15 blocks, found 14"):
            verify(truncated)

    def test_rejects_invalid_point_lists(self):
        for replacement, message in (("5", "21 distinct points"), ("71", "point 71")):
            with self.subTest(replacement=replacement):
                with self.assertRaisesRegex(ValueError, message):
                    verify(self.known.replace("2 5 ", f"{replacement} 5 ", 1))

    def test_rejects_uncovered_pair_after_legal_point_swap(self):
        damaged = self.known.replace("2 5 ", "1 5 ", 1)
        with self.assertRaisesRegex(ValueError, r"uncovered pair \(2, 5\)"):
            verify(damaged)


if __name__ == "__main__":
    unittest.main()
