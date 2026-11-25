"""Behavioural tests on a disposable ledger, including the historically solved control."""
import importlib.util
import json
import os
import sqlite3
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT=Path(__file__).resolve().parents[1]/"skills/project-lemma-discovery/scripts/discover.py"
spec=importlib.util.spec_from_file_location("discovery",SCRIPT)
discovery=importlib.util.module_from_spec(spec)
spec.loader.exec_module(discovery)


class Workflow(unittest.TestCase):
    def setUp(self):
        temp=tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.dir=Path(temp.name)
        self.db=self.dir/"test.sqlite"
        self.row={k:"fixture" for k in discovery.TEXT}
        self.row.update(key="mills-control",title="Mills 14",statement="Determine L(14).",checked="2026-11-25",
                        status="solved",lane="overlooked",sources=["https://github.com/troytsv/project-lemma"],
                        aliases=["first Mills number on fourteen vertices"],scores={},
                        gates={k:k!="open" for k in discovery.GATES})
    def cli(self,*args,ok=True):
        result=subprocess.run([sys.executable,"-B",str(SCRIPT),"--db",str(self.db),*map(str,args)],
                              capture_output=True,encoding="utf8")
        self.assertEqual(result.returncode==0,ok,result.stderr)
        return result.stdout
    def batch(self,*rows):
        p=self.dir/"batch.json"; p.write_text(json.dumps(rows),encoding="utf8")
        return p
    def prospective(self):
        return dict(self.row,key="synthetic-extension",title="Synthetic extension",statement="Test Q.",
                    aliases=[],status="shortlisted",gates=dict.fromkeys(discovery.GATES,True),
                    scores={k:[8,"fixture evidence"] for k in [*discovery.WEIGHTS,"competition"]})
    def test_ingest_replay_and_solved_alias(self):
        b=self.batch(self.row); self.cli("ingest",b); self.cli("ingest",b)
        alternate=dict(self.row,key="equivalent",title="Historical equivalent")
        self.cli("ingest",self.batch(alternate))
        self.assertEqual(len(json.loads(self.cli("export"))),1)
        self.assertEqual(json.loads(self.cli("show","equivalent"))["candidate"]["key"],"mills-control")
        self.cli("status","equivalent","recommended","--reason","test",ok=False)
        self.assertEqual(json.loads(self.cli("rank")),[])
    def test_recovery_and_gates(self):
        self.cli("ingest",self.batch(self.row,dict(self.prospective(),gates=dict.fromkeys(discovery.GATES,False))),ok=False)
        self.assertEqual(json.loads(self.cli("export")),[])
        self.cli("ingest",self.batch(self.row))
        code="import sqlite3,os,sys;c=sqlite3.connect(sys.argv[1]);c.execute('DELETE FROM candidates');os._exit(7)"
        self.assertEqual(subprocess.run([sys.executable,"-c",code,str(self.db)]).returncode,7)
        self.assertEqual(len(json.loads(self.cli("export"))),1)
    def test_related_parameter_cases_are_distinct(self):
        r=self.prospective()
        s=dict(r,key="different-order",title="Another order",statement="Test Q at another order.",
               aliases=["common research method"])
        r["aliases"]=["common research method"]
        self.cli("ingest",self.batch(r,s),ok=False)
        self.assertEqual(json.loads(self.cli("export")),[])
        s["aliases"]=["different parameter instance"]
        self.cli("ingest",self.batch(r,s))
        self.assertEqual(len(json.loads(self.cli("rank"))),2)
    def test_scores_handoff_and_revision(self):
        r=self.prospective(); self.cli("ingest",self.batch(r))
        rank=json.loads(self.cli("rank"))[0]
        self.assertEqual((rank["base"],rank["priority"]),(80,78.4))
        self.assertIn(r["statement"],self.cli("handoff",r["key"]))
        rev=json.loads(self.cli("show",r["key"]))["revision"]
        p=self.dir/"revision.json"; p.write_text(json.dumps(dict(r,experiment="new evidence")))
        self.cli("revise",p,"--expected",rev); self.cli("revise",p,"--expected",rev,ok=False)
        self.cli("status",r["key"],"deferred","--reason","budget exhausted")
        self.cli("handoff",r["key"],ok=False)
    def test_later_resolution_and_feedback(self):
        r=self.prospective();self.cli("ingest",self.batch(r))
        self.cli("ingest",self.batch(dict(r,key="new-source",status="solved",scores={},unresolved="proof found")))
        self.assertEqual(json.loads(self.cli("rank")),[])
        p=SCRIPT.parents[1]/"assets/feedback.json"
        for _ in range(2):self.cli("feedback",r["key"],p)
        self.assertEqual(len(json.loads(self.cli("outcomes"))),1)

if __name__=="__main__":unittest.main()
