"""Offline regression tests for the publication workflow. All writes are temporary."""
import hashlib
import io
import shutil
import subprocess
import sys
import tempfile
import unittest
import zipfile
from pathlib import Path


TOOLS = Path(__file__).resolve().parents[1]
SKILL = TOOLS / "skills/project-lemma-publication"
sys.path.insert(0, str(SKILL / "scripts"))
from audit_release import verify_archive


class PublicationTest(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.repo = Path(temp.name)
        (self.repo / "problems/001-first").mkdir(parents=True)
        (self.repo / "problems/001-first/witness.txt").write_text("old research")
        (self.repo / "README.md").write_text("# Project\n\n## Research index\n\nOriginal narrative.\n")
        (self.repo / "problems/README.md").write_text(
            "| Problem | Result | Status |\n| --- | --- | --- |\n"
            "| [001 · First](001-first/README.md) | a | published |\n", encoding="utf-8")
        self.name = "002-second"
        self.problem = self.repo / "problems" / self.name
        self.allocate()

    def run_script(self, script, *args, success=True):
        result = subprocess.run([sys.executable, "-B", str(script), *map(str, args)],
                                cwd=self.repo, capture_output=True, text=True)
        self.assertEqual(result.returncode == 0, success, result.stderr)
        return result.stdout

    def allocate(self):
        return self.run_script(SKILL / "scripts/problem.py", "--repo", self.repo,
                               "new", "second", "--title", 'Second "question"')

    def test_scaffold_and_index_replay(self):
        self.assertIn(self.name, self.allocate())
        self.assertTrue((self.problem / "paper/paper.tex").is_file())
        self.assertIn(r'Second \"question\"', (self.problem / "CITATION.cff").read_text())
        args = [SKILL / "scripts/problem.py", "--repo", self.repo, "index", self.name,
                "--title", "Second", "--summary", "A result", "--status", "Draft"]
        indexes = [self.repo / "README.md", self.repo / "problems/README.md"]
        self.run_script(*args)
        before = [p.read_bytes() for p in indexes]
        self.run_script(*args)
        self.assertEqual(before, [p.read_bytes() for p in indexes])
        for contents in before:
            self.assertEqual(contents.count(b"002-second/README.md"), 1)
            self.assertIn(b"001-first/README.md", contents)
        self.assertIn(b"Original narrative.", before[0])

    def test_recover_uncertain_action(self):
        script = SKILL / "scripts/receipts.py"
        def action(command, *args, success=True):
            return self.run_script(script, self.problem, command, "v1.registry", *args,
                                   success=success)
        self.assertIn("No structured receipt", action("inspect"))
        action("begin", "--evidence", "test scope")
        self.assertIn("Unresolved intent", action("inspect"))
        action("begin", "--evidence", "test scope", success=False)
        for _ in range(2):
            action("finish", "--outcome", "confirmed", "--evidence", "verified test ID")
        action("finish", "--outcome", "rejected", "--evidence", "conflict", success=False)
        self.assertIn("verified test ID", action("inspect"))

    def test_package_selected_problem_and_detect_tampering(self):
        (self.repo / "tools").mkdir()
        pack = self.repo / "tools/package_release.py"
        shutil.copyfile(TOOLS / pack.name, pack)
        with (self.problem / "CITATION.cff").open("a", encoding="utf-8") as citation:
            citation.write('\nversion: "1.2.3"\n')
        paper = b"%PDF-test-fixture"
        (self.problem / "paper/paper.pdf").write_bytes(paper)
        def git(*args):
            return subprocess.check_output(["git", "-C", str(self.repo), *args])
        git("init", "-q")
        git("add", ".")
        git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
            "-c", "commit.gpgsign=false", "commit", "-qm", "fixture")
        tag = "second-v1.2.3"
        out = self.repo / "build"
        self.run_script(pack, out, "--problem", self.name, "--tag", tag)
        self.run_script(pack, out, "--problem", self.name, "--tag", "second-v1.0.0", success=False)
        for line in (out / "SHA256SUMS.txt").read_text().splitlines():
            digest, name = line.split("  ")
            self.assertEqual(hashlib.sha256((out / name).read_bytes()).hexdigest(), digest)
        bundle = out / (tag + "-sources.zip")
        with zipfile.ZipFile(bundle) as zipped:
            self.assertFalse(any("001-first/" in n for n in zipped.namelist()))
        tree = out / "git.tar"
        git("archive", "--format=tar", "--output", str(tree), "HEAD")
        args = [tree, git("rev-parse", "HEAD").decode().strip(), "problems/" + self.name, tag]
        verify_archive(bundle, *args, paper)
        with self.assertRaisesRegex(ValueError, "PDF differs"):
            verify_archive(bundle, *args, b"wrong paper")
        altered = io.BytesIO(bundle.read_bytes())
        with zipfile.ZipFile(altered, "a") as zipped:
            zipped.writestr("unexpected-file", "oops")
        with self.assertRaisesRegex(ValueError, "file list"):
            verify_archive(altered, *args, paper)


if __name__ == "__main__":
    unittest.main()
