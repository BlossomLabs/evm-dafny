"""Verify the full clean core closure, excluding optional crypto adapters."""
import argparse, csv, hashlib, json, re, shutil, subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ENTRIES = ['src/dafny/pure-steps.dfy','src/dafny/checked-add.dfy',
           'src/dafny/boundaries.dfy','src/dafny/trace-proof.dfy']

def closure(entries):
    result=set()
    def visit(path):
        path=path.resolve()
        if path in result: return
        assert path.is_relative_to(ROOT), path
        result.add(path)
        for include in re.findall(r'^\s*include\s+"([^"]+)"',path.read_text(),re.M):
            visit(path.parent/include)
    for entry in entries: visit(ROOT/entry)
    return sorted(result)

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def run(dafny,output):
    assert not output.exists(), 'Use a fresh evidence directory'
    output.mkdir(parents=True)
    sources=closure(ENTRIES)
    for path in sources:
        text = re.sub(r'/\*.*?\*/|//[^\n]*','',path.read_text(),flags=re.S)
        assert not re.search(r'\bassume\b|\{:\s*(?:axiom|verify\s+false)',text), path
        dest=output/'snapshot'/path.relative_to(ROOT)
        dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(path,dest)
    assert subprocess.check_output([str(dafny),'--version'],text=True).strip().split('+')[0]=='4.11.0'
    z3=dafny.parent/'z3/bin/z3-4.12.1'
    assert subprocess.check_output([str(z3),'-version'],text=True).startswith('Z3 version 4.12.1')
    entries=[str(output/'snapshot'/p) for p in ENTRIES]
    commands=[('verify',[str(dafny),'verify',*entries,'--verify-included-files','--manual-lemma-induction',
              '--isolate-assertions','--cores','2','--verification-time-limit','30','--solver-path',str(z3),
              '--log-format','csv;LogFileName='+str(output/'native.csv')]),
              ('audit',[str(dafny),'audit',*entries]),
              ('format',[str(dafny),'format','--check',*[str(output/'snapshot'/p.relative_to(ROOT)) for p in sources]])]
    receipt={'status':'running','sources':{str(p.relative_to(ROOT)):sha(p) for p in sources},
             'tools':{str(p):sha(p) for p in [dafny,z3,dafny.parent/'Dafny.dll']},'results':[],
             'excluded':['src/dafny/core/precompiled-crypto.dfy','src/dafny/t8n.dfy','legacy example proofs'],
             'scope':'Complete imported clean core and reusable summaries; no full EVM conformance claim'}
    def save(): (output/'manifest.json').write_text(json.dumps(receipt,indent=2)+'\n')
    save()
    for gate,cmd in commands:
        with (output/(gate+'.log')).open('w') as log: p=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT)
        text=(output/(gate+'.log')).read_text();passed=p.returncode==0
        result={'gate':gate,'command':cmd,'exitCode':p.returncode}
        if gate=='verify':
            rows=list(csv.DictReader((output/'native.csv').open())) if (output/'native.csv').exists() else []
            summary=re.search(r'finished with (\d+) verified, (\d+) errors',text)
            passed &= bool(rows) and all(r['TestResult.Outcome']=='Passed' for r in rows)
            passed &= bool(summary) and int(summary[1])==len(rows) and int(summary[2])==0
            passed &= not bool(re.search(r'time.?out|inconclusive|Error:',text,re.I))
            result['rows']=len(rows)
        if gate=='audit': passed &= 'auditor completed with 0 findings' in text
        result['passed']=passed;receipt['results'].append(result);save()
    passed=all(r['passed'] for r in receipt['results']) and all(sha(ROOT/p)==h for p,h in receipt['sources'].items())
    receipt['status']='verified' if passed else 'failed'
    receipt['evidenceSha256']={str(p.relative_to(output)):sha(p) for p in output.rglob('*') if p.is_file() and p.name!='manifest.json'}
    save();return 0 if passed else 1

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--dafny',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();raise SystemExit(run(a.dafny.resolve(),a.output.resolve()))
