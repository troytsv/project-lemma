"""Package a committed Project Lemma investigation and its exact manuscript."""
import argparse
import hashlib
import io
import re
import subprocess
import tarfile
import zipfile
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PROBLEM = "problems/001-mills-number-14"

def git(*args):
    return subprocess.check_output(["git", "-C", str(ROOT), *args])

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--rev", default="HEAD")
    parser.add_argument("--problem", default=PROBLEM.split("/")[-1],
                        help="Numbered directory name under problems/")
    parser.add_argument("--tag", help="Release tag ending in -v<the CFF version>")
    args = parser.parse_args()
    if not re.fullmatch(r"[0-9]{3,}-[a-z0-9]+(?:-[a-z0-9]+)*", args.problem):
        parser.error("expected a numbered problem directory name")
    problem = "problems/" + args.problem
    commit = git("rev-parse", "--verify", "--end-of-options", args.rev + "^{commit}").decode().strip()
    citation = git("show", f"{commit}:{problem}/CITATION.cff").decode()
    version_line = next((s for s in citation.splitlines() if s.startswith("version: ")), None)
    if version_line is None:
        parser.error("set the release version in the problem's CITATION.cff before packaging")
    version = version_line.split(": ", 1)[1].strip().strip("\"'")
    default_prefix = "mills-14" if problem == PROBLEM else args.problem.split("-", 1)[1]
    stem = args.tag or f"{default_prefix}-v{version}"
    if not re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*-v[0-9]+(?:\.[0-9]+){2}", stem) or not stem.endswith("-v" + version):
        parser.error("expected a safe release tag matching the quoted CFF version")
    epoch = int(git("show", "-s", "--format=%ct", commit))
    timestamp = datetime.fromtimestamp(epoch, timezone.utc).timetuple()[:6]
    args.output.mkdir(parents=True, exist_ok=True)
    with tarfile.open(fileobj=io.BytesIO(git("archive", "--format=tar", commit))) as tree:
        files = {m.name: tree.extractfile(m).read() for m in tree if m.isfile() and
                 (not m.name.startswith("problems/") or m.name.startswith(problem + "/")
                  or m.name == "problems/README.md")}
    archive = args.output / (stem + "-sources.zip")
    paper = args.output / (stem + ".pdf")
    with zipfile.ZipFile(archive, "w") as output:
        output.comment = commit.encode("ascii")
        for name, data in sorted(files.items()):
            entry = zipfile.ZipInfo(f"{stem}/{name}", timestamp)
            entry.create_system = 3
            entry.external_attr = 0o100644 << 16
            output.writestr(entry, data, compress_type=zipfile.ZIP_DEFLATED)
    paper.write_bytes(files[problem + "/paper/paper.pdf"])
    hashes = [f"{hashlib.sha256(f.read_bytes()).hexdigest()}  {f.name}" for f in (paper, archive)]
    (args.output / "SHA256SUMS.txt").write_bytes(("\n".join(hashes) + "\n").encode("ascii"))
    print(commit, *hashes, sep="\n")

if __name__ == "__main__":
    main()
