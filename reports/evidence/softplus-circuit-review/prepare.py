from pathlib import Path
import json,hashlib,importlib.util
ROOT=Path(__file__).resolve().parents[3];OUT=Path(__file__).resolve().parent
manifest=json.loads((ROOT/'reports/softplus-circuit-expected-types.json').read_text())
(OUT/'expected-types.json').write_text(json.dumps(manifest,indent=2)+'\n')
source={}
for p in sorted((ROOT/'formalization/Thesis').glob('SoftplusCircuit*.lean')):
 target=OUT/'source'/p.name;target.write_bytes(p.read_bytes());source[str(p.relative_to(ROOT))]=hashlib.sha256(p.read_bytes()).hexdigest()
(OUT/'source-sha256.json').write_text(json.dumps(source,indent=2)+'\n')
spec=importlib.util.spec_from_file_location('verify',ROOT/'formalization/scripts/verify.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
driver=m.exact_driver({'public_root':'All','targets':manifest['targets']},OUT)
driver=driver.replace('import All\n','import Thesis.SoftplusCircuitUniqueness\nimport Thesis.SoftplusCircuitVisits\nimport Thesis.SoftplusCircuitPayoff\n')
(OUT/'ExactTypes.lean').write_text(driver)
print('20 exact targets; 13 frozen source snapshots')
