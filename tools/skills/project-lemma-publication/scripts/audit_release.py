"""Verify an existing public release with anonymous GET requests and local Git reads."""
import argparse
import hashlib
import io
import json
import re
import subprocess
import tarfile
import tempfile
import zipfile
from pathlib import Path
from urllib.request import Request, urlopen

PROJECT = "troytsv/project-lemma"
API = "https://api.github.com/repos/" + PROJECT


def fetch(url):
    request = Request(url, headers={"User-Agent": "Project-Lemma-publication-audit"})
    with urlopen(request, timeout=90) as response:
        return response.read()


def check(ok, message):
    if not ok:
        raise ValueError(message)


def verify_archive(archive, git_tree, commit, problem, tag, paper):
    prefix = tag + "/"
    with zipfile.ZipFile(archive) as bundle, tarfile.open(git_tree) as tree:
        check(bundle.comment == commit.encode(), "source ZIP commit mismatch")
        files = {m.name: m for m in tree if m.isfile() and
                 (not m.name.startswith("problems/") or m.name.startswith(problem + "/")
                  or m.name == "problems/README.md")}
        names = bundle.namelist()
        check(len(names) == len(files) and set(names) == {prefix + n for n in files},
              "source ZIP file list differs from the tagged tree")
        for name, entry in files.items():
            check(bundle.read(prefix + name) == tree.extractfile(entry).read(), "mismatched file: " + name)
        check(bundle.read(prefix + problem + "/paper/paper.pdf") == paper, "PDF differs from source ZIP")


def audit(args):
    def git(*parts):
        return subprocess.check_output(["git", "-C", str(args.repo), *parts]).decode().strip()

    check(re.fullmatch(r"\d{3,}-[a-z0-9]+(?:-[a-z0-9]+)*", args.problem), "invalid problem")
    check(re.fullmatch(r"[a-z0-9-]+-v\d+\.\d+\.\d+", args.tag), "invalid version tag")
    check(re.fullmatch(r"[a-zA-Z0-9_-]+\.ya?ml", args.workflow), "expected workflow filename")
    tag = args.tag
    problem = "problems/" + args.problem
    sha = git("rev-parse", "--verify", "refs/tags/" + tag + "^{commit}")
    check(json.loads(fetch(API + "/commits/" + tag))["sha"] == sha, "public tag differs from local tag")
    release = json.loads(fetch(API + "/releases/tags/" + tag))
    check(release["tag_name"] == tag and not release["draft"], "missing public release")
    names = {tag + ".pdf", tag + "-sources.zip", "SHA256SUMS.txt"}
    assets = {a["name"]: a for a in release["assets"]}
    check(names <= assets.keys(), "missing release asset")
    contents, hashes = {}, {}
    for name in sorted(names):
        asset = assets[name]
        url = "https://github.com/" + PROJECT + "/releases/download/" + tag + "/" + name
        check(asset["browser_download_url"] == url, "unexpected asset URL")
        contents[name] = fetch(url)
        hashes[name] = hashlib.sha256(contents[name]).hexdigest()
        check(asset["size"] == len(contents[name]), "asset length mismatch")
        check(asset["digest"] == "sha256:" + hashes[name], "GitHub digest mismatch: " + name)
    expected = {f"{hashes[n]}  {n}" for n in names - {"SHA256SUMS.txt"}}
    lines = contents["SHA256SUMS.txt"].decode("ascii").splitlines()
    check(len(lines) == 2 and set(lines) == expected, "SHA256SUMS.txt differs")
    with tempfile.TemporaryDirectory() as temp:
        tree = Path(temp) / "source.tar"
        subprocess.run(["git", "-C", str(args.repo), "archive", "--format=tar",
                        "--output", str(tree), sha], check=True)
        verify_archive(io.BytesIO(contents[tag + "-sources.zip"]), tree, sha, problem, tag,
                       contents[tag + ".pdf"])
    runs = json.loads(fetch(f"{API}/actions/workflows/{args.workflow}/runs?head_sha={sha}&per_page=100"))
    candidates = [r for r in runs["workflow_runs"] if r["head_sha"] == sha and r["event"] in ("push","workflow_dispatch")]
    check(candidates, "no branch or manual workflow run for this exact commit")
    run = max(candidates, key=lambda r: (r["run_number"], r["run_attempt"]))
    check(run["conclusion"] == "success", "latest matching workflow did not pass: " + run["html_url"])
    jobs = json.loads(fetch(run["jobs_url"] + "?per_page=100"))
    statuses = {j["name"]: j["conclusion"] for j in jobs["jobs"]}
    check(jobs["total_count"] == len(jobs["jobs"]), "job list incomplete")
    check(all(statuses.get(name) == "success" for name in args.require_job),
          "a required job was absent, skipped or failed")
    return {"tag": tag, "commit": sha, "release": release["html_url"], "sha256": hashes,
            "workflow": run["html_url"], "jobs": statuses}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    for option in ("problem", "tag", "workflow"):
        parser.add_argument("--" + option, required=True)
    parser.add_argument("--require-job", action="append", required=True, help="Repeat for every required job")
    print(json.dumps(audit(parser.parse_args()), indent=2))
