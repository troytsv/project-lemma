"""Package the tagged Problem 001 Git tree and exact manuscript for GitHub."""
import argparse
import hashlib
import io
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
    args = parser.parse_args()
    commit = git("rev-parse", "--verify", args.rev + "^{commit}").decode().strip()
    epoch = int(git("show", "-s", "--format=%ct", commit))
    timestamp = datetime.fromtimestamp(epoch, timezone.utc).timetuple()[:6]
    args.output.mkdir(parents=True, exist_ok=True)
    with tarfile.open(fileobj=io.BytesIO(git("archive", "--format=tar", commit))) as tree:
        files = {m.name: tree.extractfile(m).read() for m in tree if m.isfile()}
    version_line = next(s for s in files[PROBLEM + "/CITATION.cff"].decode().splitlines() if s.startswith("version: "))
    version = version_line.split(": ", 1)[1].strip('"')
    stem = f"mills-14-v{version}"
    archive = args.output / (stem + "-sources.zip")
    paper = args.output / (stem + ".pdf")
    with zipfile.ZipFile(archive, "w") as output:
        output.comment = commit.encode("ascii")
        for name, data in sorted(files.items()):
            entry = zipfile.ZipInfo(f"{stem}/{name}", timestamp)
            entry.create_system = 3
            entry.external_attr = 0o100644 << 16
            output.writestr(entry, data, compress_type=zipfile.ZIP_DEFLATED)
    paper.write_bytes(files[PROBLEM + "/paper/paper.pdf"])
    hashes = [f"{hashlib.sha256(f.read_bytes()).hexdigest()}  {f.name}" for f in (paper, archive)]
    (args.output / "SHA256SUMS.txt").write_bytes(("\n".join(hashes) + "\n").encode("ascii"))
    print(commit, *hashes, sep="\n")

if __name__ == "__main__":
    main()
