from pathlib import Path
import subprocess,json,hashlib
ROOT=Path(__file__).resolve().parents[3]; OUT=Path(__file__).resolve().parent
names='Model Local Equilibrium Players Rows Derivative Paths Occupation Cuts Visits Uniqueness Transition Payoff'.split()
rows=[]
for name in names:
 p=ROOT/f'formalization/Thesis/SoftplusCircuit{name}.lean'
 cmd=['lake','env','lean','-o',str(ROOT/f'formalization/.lake/diagnostics/softplus-circuit-review/Thesis/SoftplusCircuit{name}.olean'),str(p)]
 with (OUT/f'source-{name}.log').open('w') as f:r=subprocess.run(cmd,cwd=ROOT/'formalization',stdout=f,stderr=subprocess.STDOUT)
 rows.append({'module':'Thesis.SoftplusCircuit'+name,'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'command':cmd,'exit_code':r.returncode})
 (OUT/'source-checks.json').write_text(json.dumps(rows,indent=2)+'\n')
 print(name,r.returncode,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
