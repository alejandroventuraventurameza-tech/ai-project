"""Trace exact reduced-path Euler, monetary-rule and Phillips identities.

These are accounting/conditional equations evaluated on jointly solved paths,
not independent causal interventions and not full-equilibrium certification.
"""
from pathlib import Path
import csv
import hashlib
import json
import math

import numpy as np
from compare_nonlinear_tail import StackedPath
import finite_irf as model

HERE=Path(__file__).resolve().parent
OUT=HERE/'output/transmission_trace'


def require(ok,message):
    if not ok: raise AssertionError(message)


def terminal_metrics(problem, solution):
    """Only contemporaneous objects needed by the previous-date equations.

    Do not fabricate next-period capital, collateral or returns beyond T.
    """
    s,b=problem.s,problem.base
    z=solution[problem.indices(problem.T)]
    x=model.expand_compact_state(s,[b.X2[i]*math.exp(z[i]) for i in range(6)])
    u=[s.base[6+i]*math.exp(z[6+i]) for i in range(10)]
    labor,output,_,_=model.production(s,x[:2],u)
    Y=model.dot(s.mass,output)
    rr=s.rr*math.exp(.5*math.log(x[5]/s.rr)+.75*math.log(u[5])+.0625*math.log(Y/s.Y))
    return dict(worker_consumption=u[2],wage=u[3],input_price=u[4],inflation=u[5],
                deposit_rate=u[7],loan_rate=u[8],reserve_rate=rr,output=Y,
                labor=model.dot(s.mass,labor))


def main():
    OUT.mkdir(exist_ok=True)
    report={'status':'running','full_equilibrium_validated':False,'branch':{},
        'scope':'Deterministic reduced nonlinear path, T=640, local stable graph at terminal date; equations evaluated jointly, not causal counterfactuals.'}
    target=OUT/'REPORT.json';target.write_text(json.dumps(report)+'\n',encoding='utf-8')
    mat=json.loads((HERE/'inputs/rational_preconditioners.json').read_text())
    p,f=np.asarray(mat['P0'],float),np.asarray(mat['F0'],float)
    checks=json.loads((HERE/'output/nonlinear_tail_comparison/REPORT.json').read_text())
    csvrows=[]
    try:
        for branch in ['slack','binding']:
            problem=StackedPath(640,branch,-1e-5,'linear_graph',p,f)
            reference=StackedPath(640,branch,0.,'linear_graph',p,f)
            sol,history=problem.solve();sol0,history0=reference.solve()
            rows,baseline=problem.metrics(sol),reference.metrics(sol0)
            _,failures=model.validate_margins(rows,branch);require(not failures,str(failures))
            rows.append(terminal_metrics(problem,sol));baseline.append(terminal_metrics(reference,sol0))
            def dlog(t,k):return math.log(rows[t][k]/baseline[t][k])
            output=100*dlog(0,'output')
            earlier=next(q for q in checks['experiments'] if q['branch']==branch and q['T']==640 and q['terminal']=='linear_graph')
            require(abs(output-earlier['impact']['output'])<1e-10,'Reconstruction does not reproduce nonlinear comparison')
            max_euler=max_rule=max_phillips=max_loan=max_deposit=0.
            bank_terms=[]
            real=[];terms=[]
            for t in range(640):
                r,rn=rows[t],rows[t+1];r0,r0n=baseline[t],baseline[t+1]
                real.append(dlog(t,'deposit_rate')-dlog(t+1,'inflation'))
                eg=dlog(t+1,'worker_consumption')-dlog(t,'worker_consumption')-real[-1]
                max_euler=max(max_euler,abs(eg))
                lag=.5*dlog(t-1,'reserve_rate') if t else 0.
                infl=.75*dlog(t,'inflation'); activity=.0625*dlog(t,'output')
                innovation=-1e-5 if t==0 else 0.
                rule=dlog(t,'reserve_rate')-lag-infl-activity-innovation
                max_rule=max(max_rule,abs(rule))
                # Euler allows Lambda = Pi_(t+1)/R^D_t in this deterministic case.
                def phillips(a,an):
                    now=25*a['inflation']*(a['inflation']-1)
                    future=-25*(an['output']/a['output'])*an['inflation']**2*(an['inflation']-1)/a['deposit_rate']
                    return now,future
                now,future=phillips(r,rn);now0,future0=phillips(r0,r0n)
                err=(r['input_price']-r0['input_price'])-(now-now0)-(future-future0)
                max_phillips=max(max_phillips,abs(err))
                terms.append(dict(current=now-now0,future=future-future0))
                def bank(a):
                    theta=a['tightness'];match=1/(1+math.sqrt(2-theta))
                    cm=problem.s.Delta*(1-problem.s.aa+problem.s.aa*match)
                    cp=problem.s.Delta*theta*problem.s.aa*match
                    average=(cm+cp)/2
                    risk=(a['deposit_rate']/a['reserve_rate']-problem.s.rho)*problem.s.zeta*(cm-cp)/2
                    return average,risk
                avg,risk=bank(r);avg0,risk0=bank(r0)
                rr=r['reserve_rate']-r0['reserve_rate']
                loan=r['loan_rate']-r0['loan_rate']
                deposit=r['deposit_rate']-r0['deposit_rate']
                max_loan=max(max_loan,abs(loan-rr-avg+avg0))
                max_deposit=max(max_deposit,abs(deposit-rr-(1-problem.s.rho)*(avg-avg0)+risk-risk0))
                bank_terms.append({'reserve_rate_difference_bp':1e4*rr,
                    'mean_liquidity_slope_difference_bp':1e4*(avg-avg0),
                    'deposit_liquidity_component_bp':1e4*(1-problem.s.rho)*(avg-avg0),
                    'deposit_payment_risk_component_bp':-1e4*(risk-risk0),
                    'loan_rate_difference_bp':1e4*loan,'deposit_rate_difference_bp':1e4*deposit})
                out={'branch':branch,'period':t,'real_deposit_return_log_bp':10000*real[-1],
                     'rule_lag_log_bp':10000*lag,'rule_inflation_log_bp':10000*infl,
                     'rule_output_log_bp':10000*activity,'rule_innovation_log_bp':10000*innovation,
                     'Euler_difference_error':eg,'rule_difference_error':rule,'NKPC_reduced_error':err}
                for key in ['worker_consumption','input_price','wage','labor','inflation','deposit_rate','reserve_rate','loan_rate','output']:
                    out[key]=r[key];out[key+'_baseline']=r0[key];out[key+'_log_difference']=dlog(t,key)
                csvrows.append(out)
            c0=100*dlog(0,'worker_consumption');ct=100*dlog(640,'worker_consumption')
            early=-100*sum(real[:3]);later=-100*sum(real[3:])
            telescope=abs(c0-ct-early-later)
            require(max(max_euler,max_rule,max_phillips,max_loan,max_deposit,telescope)<1e-9,'Trace identity failed')
            gamma=1/3
            dm=dlog(0,'input_price');level_dm=rows[0]['input_price']-baseline[0]['input_price']
            factor=dm/level_dm
            pc=100*gamma*factor*terms[0]['current'];pf=100*gamma*factor*terms[0]['future']
            cc=-gamma*c0
            require(abs(pc+pf+cc-output)<1e-9,'Output decomposition failed')
            report['branch'][branch]={
                'output_impact_log_pct':output,
                'consumption_impact_log_pct':c0,
                'bank_pricing_impact_level_bp':bank_terms[0],
                'consumption_telescope_log_pct':{'terminal':ct,'real_returns_dates_0_to_2':early,'real_returns_dates_3_to_639':later,'identity_error':telescope},
                'output_identity_contributions_log_pct':{'current_inflation_term':pc,'future_pricing_term':pf,'worker_consumption_term':cc},
                'first_eight_periods':[{k:v for k,v in row.items() if k in ['period','real_deposit_return_log_bp'] or k.endswith('_log_difference') or k.startswith('rule_')} for row in csvrows if row['branch']==branch and row['period']<8],
                'first_nonnegative_reserve_rate_deviation_date':next((t for t in range(640) if dlog(t,'reserve_rate')>=0),None),
                'max_errors':{'Euler':max_euler,'policy_rule':max_rule,'Phillips_Euler_reduction':max_phillips,'loan_pricing':max_loan,'deposit_pricing':max_deposit},
                'solver_final_residual':history[-1]}
            print(branch,report['branch'][branch]['consumption_telescope_log_pct'],flush=True)
        report['status']='passed_scoped_transmission_identity_checks'
        report['input_sha256']={str(q.relative_to(HERE)):hashlib.sha256(q.read_bytes()).hexdigest()
            for q in [HERE/'finite_irf.py',HERE/'compare_nonlinear_tail.py',HERE/'inputs/rational_preconditioners.json']}
    except Exception as error:
        report['status']='failed';report['error']=str(error);raise
    finally:
        target.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    with (OUT/'paths.csv').open('w',newline='',encoding='utf-8') as handle:
        writer=csv.DictWriter(handle,fieldnames=list(csvrows[0]));writer.writeheader();writer.writerows(csvrows)
    text=['# Transmisión: regla monetaria, Euler y precios','',
      'Este diagnóstico usa la solución reducida no lineal con T=640 y cierre de gráfica estable en T. No cambia parámetros, estados heredados ni anuncios.',
      '', '## Ecuaciones enlazadas',
      '0. Banco en el régimen interior utilizado: RL_t = RR_t + chi_bar_t; RD_t = RR_t + (1-rho)chi_bar_t - (RD_t/RR_t-rho)*zeta*chi_diff_t/2. Las pendientes provienen del matching y corredor, no se estiman como residuo.',
      '1. Regla: Delta log RR_t = 0.5 Delta log RR_(t-1) + 0.75 Delta log Pi_t + 0.0625 Delta log Y_t + v_t.',
      '   Los anuncios de referencia se mantienen: v_0=-1e-5 y v_t=0 después. Las contribuciones son logaritmos, no diferencias de tasas brutas.',
      '2. Euler del hogar: Delta log Cw_(t+1) - Delta log Cw_t = Delta log RD_t - Delta log Pi_(t+1).',
      '3. En este experimento determinista, Lambda_(t,t+1)=Pi_(t+1)/RD_t. Entonces la curva de Phillips puede escribirse:',
      '   m_t = 5/6 + 25 Pi_t(Pi_t-1) - 25 (Y_(t+1)/Y_t) Pi_(t+1)^2(Pi_(t+1)-1)/RD_t.',
      '4. Con capital y tecnología fijos al impacto: Delta log Y_0 = (Delta log m_0 - Delta log Cw_0)/3.',
      '', '## Qué permite concluir esta cadena',
      'La regla baja inicialmente la remuneración por la innovación, pero la retroalimentación de inflación y producto y la persistencia afectan toda su trayectoria. La reversión posterior de la tasa es endógena a las reglas y a la solución; no es una segunda sorpresa monetaria añadida.',
      'Euler describe crecimiento de consumo entre fechas, no determina su nivel inicial a partir de la tasa real inicial. El nivel también depende del resto de la trayectoria y del anclaje terminal, que aquí se deja explícito.',
      'El término futuro de la curva de Phillips incluye simultáneamente inflación futura, producción relativa y la tasa de depósito. Su contribución negativa puede superar la contemporánea positiva y reducir el precio del insumo m_t.',
      'Con capital instalado fijo, el menor precio recibido por las empresas en relación con el salario reduce su demanda de trabajo y su producción. La caída del consumo del hogar, a m fijo, operaría en sentido compensador mediante la oferta laboral.',
      '', '## Resultados cuantitativos','']
    for b,q in report['branch'].items():
        text += [f'### Rama {b}',
          f"Output inicial, log %: {q['output_impact_log_pct']:.10g}.",
          f"Contribuciones de las ecuaciones bancarias, diferencias de tasas en pb: {q['bank_pricing_impact_level_bp']}.",
          f"Consumo inicial del hogar, log %: {q['consumption_impact_log_pct']:.10g}.",
          f"Descomposición Euler del consumo inicial: {q['consumption_telescope_log_pct']}.",
          f"Contribuciones contables al output inicial: {q['output_identity_contributions_log_pct']}.",
          f"Primera fecha con remuneración de reservas no inferior a su referencia: {q['first_nonnegative_reserve_rate_deviation_date']}.",
          f"Errores máximos de identidades: {q['max_errors']}.", '']
    text += ['## Límites de interpretación',
      'Las descomposiciones evalúan identidades sobre una trayectoria conjunta. No aíslan intervenciones causales independientes: mantener otros términos fijos en una derivada parcial no equivale a resolver otro equilibrio.',
      'El canal del precio del insumo afecta producción corriente. La pérdida asignativa reportada en las IRF usa producción del período siguiente, por lo que no es la misma variable ni el mismo horizonte.',
      'No se demuestra optimalidad dinámica bancaria, selección de rama ni equilibrio completo. Tampoco se valida una economía abierta o crecimiento sostenido.',
      '', 'Reproducción: `python code/irf/trace_transmission.py`. Requiere los insumos y el reporte de `compare_nonlinear_tail.py`.']
    (OUT/'REPORT.md').write_text('\n'.join(text)+'\n',encoding='utf-8')


if __name__=='__main__':main()
