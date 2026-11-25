"""Build the source release, arXiv sources and journal files from one Git tree."""

import argparse
import gzip
import hashlib
import io
import re
import subprocess
import tarfile
import zipfile
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PAPER_SOURCES = ("paper.tex", "references.bib", "paper.bbl")


def git(*args):
    return subprocess.check_output(["git", "-C", str(ROOT), *args])


def write_zip(path, files, commit, timestamp):
    with zipfile.ZipFile(path, "w") as output:
        output.comment = commit.encode("ascii")
        for name, data in sorted(files.items()):
            entry = zipfile.ZipInfo(name, timestamp)
            entry.create_system = 3
            entry.external_attr = 0o100644 << 16
            output.writestr(entry, data, compress_type=zipfile.ZIP_DEFLATED)


def write_tarball(path, files, epoch):
    with path.open("wb") as raw, gzip.GzipFile(filename="", fileobj=raw, mode="wb", mtime=epoch) as gz:
        with tarfile.open(fileobj=gz, mode="w", format=tarfile.USTAR_FORMAT) as output:
            for name, data in sorted(files.items()):
                entry = tarfile.TarInfo(name)
                entry.size, entry.mtime = len(data), epoch
                output.addfile(entry, io.BytesIO(data))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--rev", default="HEAD")
    args = parser.parse_args()
    commit = git("rev-parse", "--verify", f"{args.rev}^{{commit}}").decode().strip()
    epoch = int(git("show", "-s", "--format=%ct", commit))
    timestamp = datetime.fromtimestamp(epoch, timezone.utc).timetuple()[:6]
    with tarfile.open(fileobj=io.BytesIO(git("archive", "--format=tar", commit))) as tree:
        files = {m.name: tree.extractfile(m).read() for m in tree if m.isfile()}
    version = re.search(r'^version: "([0-9.]+)"$', files["CITATION.cff"].decode(), re.M)[1]
    prefix = f"project-lemma-{version}"
    args.output.mkdir(parents=True, exist_ok=True)
    release = args.output / f"{prefix}.zip"
    arxiv = args.output / f"{prefix}-arxiv.tar.gz"
    journal = args.output / f"{prefix}-journal.zip"
    write_zip(release, {f"{prefix}/{n}": data for n, data in files.items()}, commit, timestamp)
    paper = {name: files[name] for name in PAPER_SOURCES}
    write_tarball(arxiv, {**paper, "00README.json": files["publication/arxiv-processing.json"]}, epoch)
    write_zip(journal, {**paper, "paper.pdf": files["paper.pdf"]}, commit, timestamp)
    hashes = [f"{hashlib.sha256(p.read_bytes()).hexdigest()}  {p.name}" for p in (release, arxiv, journal)]
    (args.output / "SHA256SUMS.txt").write_bytes(("\n".join(hashes) + "\n").encode("ascii"))
    print(f"Packaged {commit}.")
    print("\n".join(hashes))


if __name__ == "__main__":
    main()
