"""Local, transaction-safe mathematical opportunity ledger. Python standard library."""
import argparse
import datetime
import hashlib
import json
import re
import sqlite3
import sys
import unicodedata
from pathlib import Path
from urllib.parse import urlsplit

ROOT = Path(__file__).resolve().parents[1]
WEIGHTS = {"tractability": 25, "openness": 20, "computation": 15, "significance": 15,
           "verification": 10, "leverage": 10, "implications": 5}
GATES = ("precision", "open", "success", "verification", "resources")
ACTIVE = {"shortlisted", "recommended"}
STATES = ACTIVE | {"screened", "deferred", "rejected", "solved", "attempted"}
TEXT = ("key title statement field posed bounds unresolved checked attempts formal strategy difficulty "
        "verification significance leverage experiment competition downside budget stop success status lane").split()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def encode(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True)


def digest(row):
    return hashlib.sha256(encode(row).encode()).hexdigest()[:16]


def validate(r):
    for k in TEXT:
        require(isinstance(r.get(k), str) and r[k].strip(), f"missing or blank {k}")
    require(re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", r["key"]), "invalid key")
    datetime.date.fromisoformat(r["checked"])
    require(r["status"] in STATES and r["lane"] in {"overlooked","ambitious","high-risk"}, "bad status or lane")
    require(isinstance(r.get("sources"),list) and r["sources"] and
            all(isinstance(s,str) and urlsplit(s).scheme in {"http","https"} and urlsplit(s).netloc for s in r["sources"]), "source URLs required")
    require(isinstance(r.get("aliases"),list) and all(isinstance(a,str) and a.strip() for a in r["aliases"]), "bad aliases")
    require(set(r["gates"]) == set(GATES) and all(type(v) is bool for v in r["gates"].values()), "invalid gates")
    sc = r["scores"]
    require(isinstance(sc,dict) and (not sc or set(sc) == set(WEIGHTS) | {"competition"}), "incomplete scores")
    for k,v in sc.items():
        require(isinstance(v,list) and len(v)==2 and type(v[0]) is int and 0<=v[0]<=10 and
                isinstance(v[1],str) and v[1].strip(), f"invalid score {k}")
    if r["status"] in ACTIVE:
        require(all(r["gates"].values()) and sc, "shortlisting requires five passed gates and all score reasons")


def identities(r):
    # Preserve case and notation in statements. Authors supply aliases for mathematical equivalence.
    def normalized(s):
        return " ".join(unicodedata.normalize("NFC",s).split())
    return {"key:" + r["key"], "statement:" + normalized(r["statement"]),
            *("label:" + normalized(a).casefold() for a in [r["title"], *r["aliases"]])}


def scores(r):
    base = sum(w*r["scores"][k][0] for k,w in WEIGHTS.items())/10
    penalty = .8*(10-r["scores"]["competition"][0])
    return round(base,2), round(max(0,base-penalty),2)


def save(db, r, prior=None):
    validate(r)
    key = r["key"]
    if prior and prior["status"]=="solved":
        require(r["status"]=="solved", "retain solved record; create a separately scoped extension")
    # Never delete a previous alias; future surveys must still recognize a renamed record.
    for identity in identities(r):
        db.execute("INSERT OR IGNORE INTO identities VALUES (?,?)",(identity,key))
        owner = db.execute("SELECT key FROM identities WHERE identity=?",(identity,)).fetchone()[0]
        require(owner==key, f"identity already belongs to {owner}; reconcile explicitly")
    db.execute("INSERT OR REPLACE INTO candidates VALUES (?,?)",(key,encode(r)))
    db.execute("INSERT INTO history(key,document) VALUES (?,?)",(key,encode(r)))


def lookup(db,key):
    hit=db.execute("SELECT document FROM candidates WHERE key=?",(key,)).fetchone()
    require(hit, "unknown candidate: "+key)
    return json.loads(hit[0])


def ingest(db,rows):
    counts={"added":0,"unchanged":0,"duplicate":0}
    for r in rows:
        validate(r)
        hits={row[0] for identity in identities(r) for row in db.execute("SELECT key FROM identities WHERE identity=?",(identity,))}
        require(len(hits)<=1, "aliases point to multiple candidates; reconcile before import")
        if not hits:
            save(db,r)
            counts["added"]+=1
            continue
        owner=hits.pop()
        original=lookup(db,owner)
        if owner==r["key"]:
            require(original==r, f"{owner} differs; revise using its current revision")
            counts["unchanged"]+=1
        else:
            same_statement=bool({i for i in identities(r) & identities(original) if i.startswith("statement:")})
            require(same_statement or r.get("equivalent_to")==owner,
                    f"shared label with {owner} but different statement; qualify aliases or verify equivalent_to")
            if r["status"]=="solved" and original["status"]!="solved":
                resolved=dict(original,status="solved",unresolved=r["unresolved"],checked=r["checked"],
                              sources=list(dict.fromkeys(original["sources"]+r["sources"])),
                              gates=dict(original["gates"],open=False))
                save(db,resolved,original)
            # Keep both external keys addressable without replacing the authoritative record.
            for identity in identities(r):
                db.execute("INSERT OR IGNORE INTO identities VALUES (?,?)",(identity,owner))
            print(f"duplicate {r['key']} -> {owner}",file=sys.stderr)
            counts["duplicate"]+=1
    return counts


def render(r):
    validate(r)
    require(r["status"] in ACTIVE,"handoff requires an eligible shortlisted or recommended candidate")
    body=(ROOT/"assets/handoff.md").read_text(encoding="utf8")
    for field in TEXT:
        body=body.replace("{{"+field+"}}",r[field])
    base,adjusted=scores(r)
    reasons="\n".join(f"- {k} {v[0]}/10 — {v[1]}" for k,v in r["scores"].items())
    return body.replace("{{sources}}","\n".join("- "+s for s in r["sources"])).replace(
        "{{ranking}}",f"Base {base:g}/100. Competition-adjusted {adjusted:g}/100.\n\n{reasons}")


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--db",type=Path,default=Path("discovery/private/opportunities.sqlite"))
    cmds=p.add_subparsers(dest="cmd",required=True)
    for op in ("ingest","revise"):
        c=cmds.add_parser(op); c.add_argument("file",type=Path)
        if op=="revise": c.add_argument("--expected",required=True)
    c=cmds.add_parser("status"); c.add_argument("key"); c.add_argument("state",choices=sorted(STATES)); c.add_argument("--reason",required=True)
    c=cmds.add_parser("show"); c.add_argument("key")
    cmds.add_parser("rank"); cmds.add_parser("export"); cmds.add_parser("outcomes")
    c=cmds.add_parser("handoff"); c.add_argument("key")
    c=cmds.add_parser("feedback"); c.add_argument("key"); c.add_argument("file",type=Path)
    a=p.parse_args()
    if a.cmd=="ingest": a.db.parent.mkdir(exist_ok=True,parents=True)
    else: require(a.db.is_file(),"database missing; ingest first")
    with sqlite3.connect(a.db, timeout=15) as db:
        db.executescript("""CREATE TABLE IF NOT EXISTS candidates(key TEXT PRIMARY KEY, document TEXT NOT NULL);
        CREATE TABLE IF NOT EXISTS identities(identity TEXT PRIMARY KEY, key TEXT NOT NULL);
        CREATE TABLE IF NOT EXISTS history(id INTEGER PRIMARY KEY, key TEXT, document TEXT, at TEXT DEFAULT CURRENT_TIMESTAMP);
        CREATE TABLE IF NOT EXISTS outcomes(key TEXT, document TEXT, PRIMARY KEY(key,document));""")
        db.execute("BEGIN IMMEDIATE" if a.cmd in {"ingest","revise","status","feedback"} else "BEGIN")
        if a.cmd=="ingest":
            rows=json.loads(a.file.read_text(encoding="utf-8-sig"))
            require(isinstance(rows,list),"expected array")
            print(encode(ingest(db,rows))); return
        if a.cmd=="revise":
            row=json.loads(a.file.read_text(encoding="utf-8-sig")); orig=lookup(db,row["key"])
            require(digest(orig)==a.expected,"stale revision"); save(db,row,orig); return
        if a.cmd=="outcomes":
            print(encode([{"key":k,"outcome":json.loads(d)} for k,d in db.execute(
                "SELECT key, document FROM outcomes ORDER BY key,document")]))
            return
        if a.cmd in {"rank","export"}:
            rows=[json.loads(s) for s, in db.execute("SELECT document FROM candidates ORDER BY key")]
            if a.cmd=="rank":
                rows=[r for r in rows if r["status"] in ACTIVE and all(r["gates"].values())]
                rows.sort(key=lambda r:(-scores(r)[1],-scores(r)[0],r["key"]))
                rows=[dict(key=r["key"],title=r["title"],base=scores(r)[0],priority=scores(r)[1],lane=r["lane"]) for r in rows]
            print(json.dumps(rows,ensure_ascii=False,indent=2)); return
        hit=db.execute("SELECT key FROM identities WHERE identity=?",("key:"+a.key,)).fetchone()
        r=lookup(db,hit[0] if hit else a.key)
        if a.cmd=="show": print(encode({"revision":digest(r),"candidate":r})); return
        if a.cmd=="handoff": print(render(r)); return
        if a.cmd=="feedback":
            note=json.loads(a.file.read_text(encoding="utf-8-sig"))
            fields=("estimated_vs_actual","approaches","resources","obstacles","techniques","novelty","disposition")
            require(all(isinstance(note.get(k),str) and note[k].strip() for k in fields),"incomplete feedback")
            db.execute("INSERT OR IGNORE INTO outcomes VALUES (?,?)",(r["key"],encode(note))); return
        require(a.reason.strip(),"status reason required")
        changed=dict(r,status=a.state,status_reason=a.reason)
        if changed!=r:save(db,changed,r)


if __name__=="__main__":
    if hasattr(sys.stdout,"reconfigure"):sys.stdout.reconfigure(encoding="utf-8")
    try: main()
    except (ValueError, KeyError, TypeError, sqlite3.Error, OSError) as exc:
        sys.exit(str(exc))
