"""Allocate a problem locally or update both Project Lemma research indexes."""
import argparse
import json
import os
import re
import tempfile
from pathlib import Path

ASSETS = Path(__file__).resolve().parents[1] / "assets"
NAME = re.compile(r"(\d{3,})-([a-z0-9]+(?:-[a-z0-9]+)*)")
START = "<!-- project-lemma problem index -->"
END = "<!-- end project-lemma problem index -->"


def write_changed(path, content):
    if path.exists() and path.read_text(encoding="utf-8") == content:
        return
    with tempfile.NamedTemporaryFile(dir=path.parent, delete=False) as f:
        f.write(content.encode("utf-8"))
    os.replace(f.name, path)


def field(value):
    if not value.strip() or any(c in value for c in "\r\n|"):
        raise ValueError("index fields must be nonempty single-line Markdown without pipes")
    return value.strip()


def update_index(root, problem, title, summary, status):
    path = root / "problems/README.md"
    rows = path.read_text(encoding="utf-8").splitlines()
    heading = "| Problem | Result | Status |"
    pos = rows.index(heading) + 2
    end = pos
    while end < len(rows) and rows[end].startswith("|"):
        end += 1
    table = [r for r in rows[pos:end] if f"]({problem}/README.md)" not in r]
    number = problem.split("-", 1)[0]
    if any(f"[{number} · " in r for r in table):
        raise ValueError("identifier already belongs to another problem")
    table.append(f"| [{number} · {title}]({problem}/README.md) | {summary} | {status} |")
    table.sort(key=lambda r: int(re.search(r"\[(\d+) · ", r)[1]))
    catalog = "\n".join([*rows[:pos], *table, *rows[end:]]) + "\n"
    home = root / "README.md"
    contents = home.read_text(encoding="utf-8")
    block = "\n".join([START, "", heading, "| --- | --- | --- |",
                       *[r.replace("](", "](problems/", 1) for r in table], "", END])
    if START in contents or END in contents:
        if contents.count(START) != 1 or contents.count(END) != 1 or contents.index(START) > contents.index(END):
            raise ValueError("repair ambiguous root index markers first")
        before, rest = contents.split(START)
        contents = before + block + rest.split(END)[1]
    else:
        heading = "## Research index\n"
        if contents.count(heading) != 1:
            raise ValueError("expected one root Research index heading")
        contents = contents.replace(heading, heading + "\n" + block + "\n")
    write_changed(path, catalog)
    write_changed(home, contents)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    commands = parser.add_subparsers(dest="command", required=True)
    new = commands.add_parser("new")
    new.add_argument("slug")
    new.add_argument("--title", required=True)
    index = commands.add_parser("index")
    index.add_argument("problem")
    index.add_argument("--title", required=True)
    index.add_argument("--summary", required=True)
    index.add_argument("--status", required=True)
    args = parser.parse_args()
    root = args.repo.resolve()
    directory = root / "problems"
    title = field(args.title)
    lock = directory / ".publication-index.lock"
    lock.mkdir()
    try:
        if args.command == "index":
            if not NAME.fullmatch(args.problem) or not (directory / args.problem / "README.md").is_file():
                raise ValueError("unknown problem directory")
            update_index(root, args.problem, title, field(args.summary), field(args.status))
            return
        if not re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", args.slug):
            raise ValueError("use a lowercase hyphenated slug")
        names = [p for p in directory.iterdir() if p.is_dir() and NAME.fullmatch(p.name)]
        existing = [p for p in names if p.name.split("-", 1)[1] == args.slug]
        if len(existing) > 1:
            raise ValueError("ambiguous problem slug")
        if existing:
            print(existing[0])
            return
        number = max((int(p.name.split("-", 1)[0]) for p in names), default=0) + 1
        dest = directory / f"{number:03d}-{args.slug}"
        with tempfile.TemporaryDirectory(dir=directory) as temp:
            draft = Path(temp) / "problem"
            (draft / "paper").mkdir(parents=True)
            (draft / "README.md").write_text("# " + title + "\n", encoding="utf-8")
            citation = (ASSETS / "citation.cff").read_text(encoding="utf-8")
            (draft / "CITATION.cff").write_text(
                citation.replace("TITLE_JSON", json.dumps(title, ensure_ascii=False)), encoding="utf-8")
            for template, target in [("manuscript.tex", "paper/paper.tex"), ("publication.md", "PUBLICATION.md")]:
                (draft / target).write_bytes((ASSETS / template).read_bytes())
            draft.rename(dest)
        print(dest)
    finally:
        lock.rmdir()


if __name__ == "__main__":
    main()
