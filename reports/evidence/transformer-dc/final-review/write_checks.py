"""Render independently authored contracts with the repository's exact checker."""
from pathlib import Path
import importlib.util, json
ROOT=Path(__file__).resolve().parents[4]
OUT=Path(__file__).resolve().parent
ns='HiddenMonotonicity.TransformerDC'
def target(name,module,typ,universes=()):
    return {'task':'transformer-final-'+name.replace('.','-'),'module':'HiddenMonotonicity.'+module,'declaration':ns+'.'+name,'universes':list(universes),'open_namespaces':[ns],'expected_type':typ}
contracts={'public_root':'HiddenMonotonicity.TransformerCorrectness','targets':[
target('Transformer.decompose_exact','TransformerCorrectness',
'''∀ {t d o : ℕ} (net : Transformer t d o) (x : DoubledInput (Fin t × Fin d)) (i : Fin o),
  (net.decompose x i).1 - (net.decompose x i).2 = net.eval (x.1 - x.2) i'''),
target('Transformer.decompose_regular','TransformerCorrectness',
'''∀ {t d o : ℕ} (net : Transformer t d o) (i : Fin o),
  Regular (Set.Ici (0 : DoubledInput (Fin t × Fin d))) (fun x => net.decompose x i)'''),
target('Transformer.dc_decomposition','TransformerCorrectness',
'''∀ {t d o : ℕ} (net : Transformer t d o),
  MonotoneOn net.decompose (Set.Ici (0 : DoubledInput (Fin t × Fin d))) ∧
  (∀ i, ConvexOn ℝ (Set.Ici (0 : DoubledInput (Fin t × Fin d))) (fun x => (net.decompose x i).1)) ∧
  (∀ i, ConvexOn ℝ (Set.Ici (0 : DoubledInput (Fin t × Fin d))) (fun x => (net.decompose x i).2)) ∧
  (∀ x, 0 ≤ x → 0 ≤ net.decompose x) ∧
  ∀ x i, (net.decompose x i).1 - (net.decompose x i).2 = net.eval (x.1 - x.2) i'''),
target('Transformer.raw_dc_decomposition','TransformerCorrectness',
'''∀ {t d o : ℕ} (net : Transformer t d o),
  (∀ i, ConvexOn ℝ Set.univ (fun x : Fin t × Fin d → ℝ => (net.rawDecompose x i).1)) ∧
  (∀ i, ConvexOn ℝ Set.univ (fun x : Fin t × Fin d → ℝ => (net.rawDecompose x i).2)) ∧
  (∀ x, 0 ≤ net.rawDecompose x) ∧
  ∀ x i, (net.rawDecompose x i).1 - (net.rawDecompose x i).2 = net.eval x i'''),
target('Expr.decompose_regular','TransformerExprProperties',
'''∀ {ι : Type u} (e : Expr ι), Regular (Set.Ici (0 : DoubledInput ι)) e.decompose''',['u']),
target('Expr.decompose_exact','TransformerExprProperties',
'''∀ {ι : Type u} (e : Expr ι) (x : DoubledInput ι), value (e.decompose x) = e.eval (x.1 - x.2)''',['u']),
target('Expr.rawDecompose_convex','TransformerExprProperties',
'''∀ {ι : Type u} (e : Expr ι),
  ConvexOn ℝ Set.univ (fun x : ι → ℝ => (e.rawDecompose x).1) ∧
  ConvexOn ℝ Set.univ (fun x : ι → ℝ => (e.rawDecompose x).2)''',['u']),
target('Expr.rawDecompose_exact','TransformerExprProperties',
'''∀ {ι : Type u} (e : Expr ι) (x : ι → ℝ), value (e.rawDecompose x) = e.eval x''',['u']),
]}
(OUT/'contracts.json').write_text(json.dumps(contracts,ensure_ascii=False,indent=2)+'\n')
spec=importlib.util.spec_from_file_location('verify',ROOT/'formalization/scripts/verify.py')
mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
(OUT/'Exact.lean').write_text(mod.exact_driver(contracts,OUT))
