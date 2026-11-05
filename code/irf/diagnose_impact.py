"""Bounded impact-output audit. Does not establish optimality or full equilibrium."""
from pathlib import Path
import contextlib
import csv
import importlib.util
import io
import json
import math
import sys

HERE = Path(__file__).resolve().parent
OUT = HERE / "output" / "impact_diagnosis"


def load_rows(folder):
    with (folder / "finite_irf_paths.csv").open(newline="", encoding="utf-8") as f:
        return list(csv.DictReader(f))


def run_case(name, shock, step):
    spec = importlib.util.spec_from_file_location("impact_runner", HERE / "finite_irf.py")
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    original = m.numerical_jacobian
    m.numerical_jacobian = lambda f, x: original(f, x, step=step)
    folder = OUT / name
    argv = sys.argv
    try:
        sys.argv = [str(HERE / "finite_irf.py"), f"--shock={shock}", "--output", str(folder)]
        with contextlib.redirect_stdout(io.StringIO()):
            m.main()
    finally:
        sys.argv = argv
    report = json.loads((folder / "finite_irf_validation.json").read_text())
    if not all(all(g.values()) for g in report["numerical_gates"].values()):
        raise AssertionError(f"Numerical gate failed: {name}")
    rows = load_rows(folder)
    return {b: float(next(r for r in rows if r['branch']==b and r['period']=='0')['output_log_deviation_pct'])
            for b in ('slack', 'binding')}


def main():
    OUT.mkdir(exist_ok=True)
    target = OUT / "diagnosis.json"
    target.write_text(json.dumps({"status": "running"})+"\n", encoding="utf-8")
    rows = load_rows(HERE / "output/main")
    results = {}
    for b in ('slack', 'binding'):
        x = next(r for r in rows if r['branch']==b and r['period']=='0')
        xp = next(r for r in rows if r['branch']==b and r['period']=='1')
        dlog = lambda key: math.log(float(x[key])/float(x[key+'_baseline']))
        dm, dc, dl, dy = (dlog(k) for k in ('input_price','worker_consumption','labor','output'))
        # At impact K_i and A_i fixed, beta=.5, phi=1, sigma_W=1.
        beta, phi, sigma, eps, price_cost = .5, 1., 1., 6., 150.
        gamma = beta/(1-beta+phi)
        contributions = {"input_price_log_pct": 100*gamma*dm,
                         "worker_consumption_log_pct": -100*gamma*sigma*dc}
        errors = {"labor_supply": abs(dlog('wage')-phi*dl-sigma*dc),
                  "labor_demand": abs((1-beta)*dl-dm+dlog('wage')),
                  "production": abs(dy-beta*dl),
                  "joint_output": abs(dy-gamma*(dm-sigma*dc))}
        def nk_terms(suffix):
            pi = float(x['inflation'+suffix]); pin = float(xp['inflation'+suffix])
            sdf = .99*float(x['worker_consumption'+suffix])/float(xp['worker_consumption'+suffix])
            yr = float(xp['output'+suffix])/float(x['output'+suffix])
            current = price_cost/eps*pi*(pi-1)
            future = -price_cost/eps*sdf*yr*pin*(pin-1)
            return current,future
        now,future = nk_terms(''); now0,future0=nk_terms('_baseline')
        mc = float(x['input_price']); mc0=float(x['input_price_baseline'])
        errors['NKPC_levels'] = abs(mc-mc0-(now-now0)-(future-future0))
        # Exact additive accounting in logs via the log-mean conversion factor.
        factor = dm/(mc-mc0) if mc!=mc0 else 1/mc0
        nk_contributions = {"current_inflation_component_output_log_pct":100*gamma*factor*(now-now0),
                           "future_pricing_component_output_log_pct":100*gamma*factor*(future-future0),
                           "worker_consumption_component_output_log_pct":-100*gamma*dc}
        errors['decomposition'] = abs(sum(nk_contributions.values())-100*dy)
        if max(errors.values())>1e-10:
            raise AssertionError(f"Economic identity discrepancy: {b}: {errors}")
        results[b] = {"output_log_pct":100*dy,"joint_identity_contributions":contributions,
            "NKPC_accounting_contributions":nk_contributions,"identity_errors":errors,
            "warning":"Accounting decomposition, not independent causal counterfactuals"}
    sensitivities={}
    for name,shock,step in [('half_shock',-5e-6,2e-6),('tenth_shock',-1e-6,2e-6),
                            ('smaller_jacobian_step',-1e-5,5e-7),('larger_jacobian_step',-1e-5,8e-6)]:
        sensitivities[name]={"shock":shock,"jacobian_step":step,
                             "impact_output_log_pct":run_case(name,shock,step)}
    report={"status":"passed_scoped_identity_checks", "full_equilibrium_validated":False,
        "impact":results,"sensitivities":sensitivities,
        "negative_in_all_tested_cases":all(y<0 for q in sensitivities.values()
                                          for y in q['impact_output_log_pct'].values()),
        "unresolved":["Independent nonlinear continuation comparison",
          "Complete reduced-to-economic-equilibrium sufficiency and dynamic optimality",
          "Full 33-row source-to-code audit beyond the displayed block"],
        "horizon_caution":"Extending forward simulation does not change the local-linear terminal graph used to solve the prefix."}
    target.write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    lines=['# Diagnóstico acotado de la caída inicial de producción','',
      'Se revisan condiciones laborales, tecnología corriente y curva de Phillips frente al artículo.',
      'El capital instalado es fijo al impacto. Con beta=0.5, phi=1 y sigma_W=1:',
      '`Delta log Y_0 = (Delta log m_0 - Delta log Cw_0) / 3`.','',
      'Las contribuciones siguientes son identidades de equilibrio evaluadas en la solución; no identifican efectos causales independientes.','']
    for b,q in results.items():
        lines += [f'## Rama {b}',f"Producción al impacto (log %): {q['output_log_pct']:.10g}",
          f"Contribución precio del insumo: {q['joint_identity_contributions']['input_price_log_pct']:.10g}",
          f"Contribución consumo del hogar: {q['joint_identity_contributions']['worker_consumption_log_pct']:.10g}",
          f"Error máximo de las identidades: {max(q['identity_errors'].values()):.4g}",'']
    lines += ['## Curva de Phillips: descomposición exacta evaluada', '',
      'm_0 = (epsilon-1)/epsilon + (phi_p/epsilon) Pi_0(Pi_0-1)',
      '      - (phi_p/epsilon) Lambda_01 (Y_1/Y_0) Pi_1(Pi_1-1).',
      'El término contemporáneo y el término futuro se calculan en cada trayectoria y se restan sus referencias.',
      'La conversión a contribuciones logarítmicas usa el factor exacto Delta log(m)/Delta m; no sustituye un contrafactual.', '']
    for b,q in results.items():
        lines.append(f"- {b}: {q['NKPC_accounting_contributions']}")
    lines += ['', 'El componente futuro negativo supera al contemporáneo positivo en ambas ramas. Esto localiza la importancia del bloque de expectativas y continuación, pero no identifica una causa exógena independiente.', '', '## Sensibilidad','']
    for name,q in sensitivities.items(): lines.append(f"- {name}: {q['impact_output_log_pct']}")
    lines += ['','## Conclusión provisional',
      'La caída persiste con los choques menores y los pasos de Jacobiano comprobados si `negative_in_all_tested_cases` es verdadero en diagnosis.json.',
      'No se observa contradicción en las identidades acotadas revisadas. Esto no descarta errores en otros bloques ni acredita optimalidad.',
      'Falta contrastar con una continuación no lineal independiente y completar la correspondencia económica.',
      'El horizonte 160/320 del reproductor anterior no constituye una prueba independiente del cierre lineal.',
      '', 'Reproducción: `python code/irf/diagnose_impact.py`. No cambia ecuaciones, parámetros ni las IRF principales.']
    (OUT/'REPORT.md').write_text('\n'.join(lines)+'\n',encoding='utf-8')
    print(json.dumps(report,indent=2))


if __name__=='__main__':
    try:
        main()
    except Exception as error:
        OUT.mkdir(exist_ok=True)
        (OUT/'diagnosis.json').write_text(json.dumps({'status':'failed','error':str(error)})+'\n',encoding='utf-8')
        raise
