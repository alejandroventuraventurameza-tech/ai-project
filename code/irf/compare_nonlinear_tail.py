"""Finite-horizon nonlinear reduced-path comparison; not full equilibrium certification.

Nonlinear equations are solved jointly through T-1, with a stated terminal
condition at T. The comparison reuses the economic residuals, but replaces the
original all-tail linear propagation by a sparse Newton stacked-path solve.
"""
from pathlib import Path
import argparse
import csv
import hashlib
import json
import math
import sys
import time

import numpy as np
import scipy
from scipy.sparse import lil_matrix
from scipy.sparse.linalg import spsolve
import finite_irf as model

HERE = Path(__file__).resolve().parent


def jacobian(f, x, step=2e-6):
    return np.asarray(model.numerical_jacobian(f, list(x), step=step), dtype=float)


class StackedPath:
    def __init__(self, horizon, branch, shock, terminal, p0, f0):
        if horizon < 3:
            raise ValueError('horizon must be >= 3')
        self.T, self.branch, self.shock, self.terminal = horizon, branch, shock, terminal
        self.p, self.f = p0, f0
        self.s = model.steady_case()
        self.base = model.make_boundary(self.s)
        self.n = 43 + 16*(horizon-2)

    def indices(self, t):
        if t == 2:
            return np.r_[np.arange(17,23),np.arange(33,43)]
        a = 43+16*(t-3)
        return np.arange(a,a+16)

    def seed(self):
        base, p, branch = self.base, self.p.tolist(), self.branch
        f0 = lambda z:model.prefix_residual(base,p,branch,0.,z)
        z0, _, j0 = model.newton(f0,[0.]*33)
        d=1e-6
        forcing=(np.asarray(model.prefix_residual(base,p,branch,d,z0))-
                 np.asarray(model.prefix_residual(base,p,branch,-d,z0)))/(2*d)
        tangent,_=model.solve_linear(j0,(-forcing).tolist())
        z,_,_=model.newton(lambda z:model.prefix_residual(base,p,branch,self.shock,z),
                          (np.asarray(z0)+self.shock*np.asarray(tangent)).tolist())
        out=np.zeros(self.n)
        out[:33]=z
        x=np.asarray(z[17:23])
        out[33:43]=(self.p@x)[6:]
        for t in range(3,self.T+1):
            x=self.f@x
            out[self.indices(t)]=np.r_[x,(self.p@x)[6:]]
        # Explicit consistency test: independent prefix assembly equals the old
        # prefix when supplied with precisely the old linear control closure.
        old=np.asarray(model.prefix_residual(base,p,branch,self.shock,z))
        err=np.max(np.abs(self.prefix(out[:43])-old))
        if err>1e-12:
            raise AssertionError(f'Prefix assembly discrepancy: {err}')
        self.prefix_assembly_error=float(err)
        return out

    def prefix(self, v):
        s,b=self.s,self.base
        x1=[b.X1[i]*math.exp(v[i]) for i in range(7)]
        u0=[b.U0[i]*math.exp(v[7+i]) for i in range(10)]
        x2=[b.X2[i]*math.exp(v[17+i]) for i in range(6)]
        u1=[b.U1[i]*math.exp(v[23+i]) for i in range(10)]
        u2=[s.base[6+i]*math.exp(v[33+i]) for i in range(10)]
        e0=[b.e0[0]+self.shock,b.e0[1]]
        a0=model.auxiliary(s,b.X0,u0,x1[:2],e0)
        a1=model.auxiliary(s,x1,u1,model.expand_compact_state(s,x2)[:2],b.e1)
        sdf=[s.be*u0[i]/u1[i] for i in range(2)]
        ans=[]
        for i in range(2):
            h=s.pledge[i]*s.ad*u1[5]*u1[6]
            ans.append(u0[i]+u0[6]*x1[i]-x1[2+i]/u0[8]-a0['N'][i])
            if self.branch=='slack' and i==1:
                ans.extend([u0[6]-sdf[i]*(a1['uk'][i]+s.ad*u1[6]),
                            math.log(u0[8]*sdf[i]/u1[5])])
            else:
                ans.extend([u0[6]-h/u0[8]-sdf[i]*(a1['uk'][i]+s.ad*u1[6]-h/u1[5]),
                            math.log(x1[2+i]/(h*x1[i]))])
        ans.extend(model.remaining_residuals(s,b.X0,u0,x1,u1,a0,a1))
        ans.extend(model.binding_period_residual(s,x1,u1,x2,u2,b.e1))
        return np.asarray(ans)

    def recurrent(self, v):
        s,b=self.s,self.base
        x=[b.X2[i]*math.exp(v[i]) for i in range(6)]
        u=[s.base[6+i]*math.exp(v[6+i]) for i in range(10)]
        xp=[b.X2[i]*math.exp(v[16+i]) for i in range(6)]
        up=[s.base[6+i]*math.exp(v[22+i]) for i in range(10)]
        return np.asarray(model.binding_period_residual(s,model.expand_compact_state(s,x),u,xp,up,[0.,0.]))

    def residual(self, v):
        ans=[self.prefix(v[:43])]
        for t in range(2,self.T):
            ans.append(self.recurrent(np.r_[v[self.indices(t)],v[self.indices(t+1)]]))
        last=v[self.indices(self.T)]
        ans.append(last[6:]-(self.p[6:]@last[:6] if self.terminal=='linear_graph' else 0.))
        return np.concatenate(ans)

    def derivative(self, v):
        j=lil_matrix((self.n,self.n),dtype=float)
        j[:33,:43]=jacobian(self.prefix,v[:43])
        row=33
        for t in range(2,self.T):
            ix=np.r_[self.indices(t),self.indices(t+1)]
            block=jacobian(self.recurrent,v[ix])
            j[np.arange(row,row+16)[:,None],ix]=block
            row+=16
        block=np.c_[-self.p[6:] if self.terminal=='linear_graph' else np.zeros((10,6)),np.eye(10)]
        j[np.arange(row,row+10)[:,None],self.indices(self.T)]=block
        if row+10!=self.n:
            raise AssertionError('Stack dimension mismatch')
        return j.tocsc()

    def solve(self, tolerance=2e-12, max_iterations=10):
        v=self.seed()
        history=[]
        for it in range(max_iterations):
            r=self.residual(v); norm=float(np.max(np.abs(r))); history.append(norm)
            if norm<tolerance:
                return v,history
            d=spsolve(self.derivative(v),-r)
            if not np.all(np.isfinite(d)):
                raise ArithmeticError('Nonfinite Newton direction')
            scale=1.
            while scale>=2.**-16:
                try:
                    candidate=v+scale*d
                    cn=float(np.max(np.abs(self.residual(candidate))))
                except (ValueError,OverflowError,ZeroDivisionError):
                    cn=math.inf
                if cn<norm:
                    v=candidate;break
                scale*=.5
            else:
                raise ArithmeticError(f'Line search failed, residual {norm}')
        raise ArithmeticError(f'Newton limit, last residual {history[-1]}')

    def metrics(self,v):
        b,s=self.base,self.s
        x1=[b.X1[i]*math.exp(v[i]) for i in range(7)]
        u0=[b.U0[i]*math.exp(v[7+i]) for i in range(10)]
        u1=[b.U1[i]*math.exp(v[23+i]) for i in range(10)]
        states={}; controls={}
        for t in range(2,self.T+1):
            y=v[self.indices(t)]
            states[t]=model.expand_compact_state(s,[b.X2[i]*math.exp(y[i]) for i in range(6)])
            controls[t]=[s.base[6+i]*math.exp(y[6+i]) for i in range(10)]
        e0=[b.e0[0]+self.shock,b.e0[1]]
        rows=[model.period_metrics(s,b.X0,u0,x1,u1,e0,self.branch),
              model.period_metrics(s,x1,u1,states[2],controls[2],b.e1,'binding')]
        rows.extend(model.period_metrics(s,states[t],controls[t],states[t+1],controls[t+1],
                                        [0.,0.],'binding') for t in range(2,self.T))
        return rows


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--horizons',type=int,nargs='+',default=[20,40,80,160,320,640])
    parser.add_argument('--shock',type=float,default=-1e-5)
    parser.add_argument('--output',type=Path,default=HERE/'output/nonlinear_tail_comparison')
    args=parser.parse_args();args.output.mkdir(exist_ok=True,parents=True)
    report={'status':'running','full_equilibrium_validated':False,'experiments':[],
        'scope':'Finite deterministic reduced paths with nonlinear rows through T-1 and an explicit boundary at T; no exact infinite-path or bank-optimality claim.',
        'shock':args.shock,'method':'Sparse stacked Newton; central finite-difference local Jacobian blocks; backtracking; no value function iteration.',
        'terminal_conditions':{'linear_graph':'u_T=P0_controls*x_T in log deviations',
                               'zero_controls':'u_T=0 in log deviations; x_T remains endogenous'},
        'remaining':['Full source-to-code audit','Exact infinite nonlinear continuation comparison beyond finite terminal experiments',
                     'Dynamic policy optimality and complete economic equilibrium correspondence']}
    target=args.output/'REPORT.json'
    target.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    matrices=json.loads((HERE/'inputs/rational_preconditioners.json').read_text())
    p=np.asarray(matrices['P0'],dtype=float);f=np.asarray(matrices['F0'],dtype=float)
    pinned=HERE/'inputs/rational_preconditioners.json'
    if hashlib.sha256(pinned.read_bytes()).hexdigest()!=model.SOURCE_HASHES['rational_preconditioners.json']:
        raise AssertionError('Pinned graph changed')
    original_validation=json.loads((HERE/'output/main/finite_irf_validation.json').read_text())
    if args.shock!=original_validation['shock']['value']:
        raise ValueError('Comparison currently requires the same shock as the stored main IRF')
    report['inputs_sha256']={str(q.relative_to(HERE)):hashlib.sha256(q.read_bytes()).hexdigest()
       for q in [HERE/'finite_irf.py',HERE/'inputs/rational_preconditioners.json']}
    original={}
    with (HERE/'output/main/finite_irf_paths.csv').open(newline='',encoding='utf-8') as handle:
        for row in csv.DictReader(handle): original[(row['branch'],int(row['period']))]=row
    report['jacobian_directional_checks']={}
    rng=np.random.default_rng(20261102)
    for branch in ['slack','binding']:
        probe=StackedPath(6,branch,args.shock,'linear_graph',p,f)
        point=probe.seed(); direction=rng.normal(size=probe.n); direction/=np.max(np.abs(direction))
        h=1e-6
        fd=(probe.residual(point+h*direction)-probe.residual(point-h*direction))/(2*h)
        error=float(np.max(np.abs(probe.derivative(point)@direction-fd)))/max(1.,float(np.max(np.abs(fd))))
        if error>=1e-7: raise AssertionError(f'Stacked derivative check failed: {branch}: {error}')
        report['jacobian_directional_checks'][branch]=error
    try:
        cases=[(T,'linear_graph') for T in args.horizons]
        cases += [(T,'zero_controls') for T in args.horizons if T>=80]
        if not any(T>=80 for T in args.horizons):
            cases += [(T,'zero_controls') for T in args.horizons[-2:]]
        for T,terminal in cases:
            for branch in ['slack','binding']:
                started=time.monotonic()
                problem=StackedPath(T,branch,args.shock,terminal,p,f)
                sol,history=problem.solve()
                # Reference is solved with precisely the same terminal condition.
                reference=StackedPath(T,branch,0.,terminal,p,f)
                zref,href=reference.solve()
                rows=problem.metrics(sol);baselines=reference.metrics(zref)
                minima,failures=model.validate_margins(rows,branch)
                impact={key:100*math.log(rows[0][key]/baselines[0][key])
                    for key in ['output','worker_consumption','input_price','wage','labor','credit_H','credit_L']}
                impact['loss_100_log_difference']=100*(rows[0]['conditional_misallocation_loss']-baselines[0]['conditional_misallocation_loss'])
                source=original[(branch,0)]
                old=float(source['output_log_deviation_pct'])
                entry={'branch':branch,'T':T,'terminal':terminal,'unknowns':problem.n,
                    'newton_residual_history':history,'reference_residual_history':href,
                    'prefix_assembly_difference':problem.prefix_assembly_error,
                    'impact':impact,'original_impact_output_log_pct':old,
                    'impact_output_difference_log_pct':impact['output']-old,
                    'terminal_state_log_sup':float(np.max(np.abs(sol[problem.indices(T)][:6]))),
                    'strict_regime_failures':failures,'runtime_seconds':time.monotonic()-started}
                report['experiments'].append(entry)
                name=f'{branch}_T{T}_{terminal}.csv'
                with (args.output/name).open('w',newline='',encoding='utf-8') as handle:
                    keys=['period','output','output_baseline','output_log_deviation_pct','input_price','wage','worker_consumption',
                          'collateral_dual_L','collateral_slack_L','conditional_misallocation_loss']
                    writer=csv.DictWriter(handle,fieldnames=keys);writer.writeheader()
                    for t,row in enumerate(rows):
                        writer.writerow({'period':t,**{k:row[k] for k in keys[1:] if k not in ['output_baseline','output_log_deviation_pct']},
                          'output_baseline':baselines[t]['output'],
                          'output_log_deviation_pct':100*math.log(row['output']/baselines[t]['output'])})
                target.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
                print(json.dumps({'branch':branch,'T':T,'terminal':terminal,'output':impact['output'],
                    'residual':history[-1],'failed_margins':failures,'seconds':entry['runtime_seconds']}),flush=True)
        report['all_tested_regime_margins_passed']=all(not q['strict_regime_failures'] for q in report['experiments'])
        report['status']='completed_finite_horizon_comparison' if report['all_tested_regime_margins_passed'] else 'completed_with_regime_failures'
    except Exception as error:
        report['status']='failed'; report['error']=str(error)
        raise
    finally:
        target.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    text=['# Comparación de la continuación no lineal','',report['scope'],'',
       'Todas las tasas, preferencias, tecnologías, posiciones heredadas y anuncios del prefijo se mantienen.',
       'La condición terminal se declara y se varía. Una solución finita no certifica existencia, unicidad o determinación infinitas.',
       '', '| Rama | T | Cierre | Output inicial (log %) | Diferencia frente a IRF original | Residuo máximo | Fallos de margen |',
       '|---|---:|---|---:|---:|---:|---|']
    for q in report['experiments']:
        text.append(f"| {q['branch']} | {q['T']} | {q['terminal']} | {q['impact']['output']:.10g} | {q['impact_output_difference_log_pct']:.4g} | {q['newton_residual_history'][-1]:.3g} | {q['strict_regime_failures']} |")
    text += ['', '## Lectura y límites',
        'La comparación reemplaza la propagación lineal por ecuaciones no lineales en todos los períodos interiores, resolviendo el prefijo y la cola conjuntamente.',
        'Reutiliza los residuos económicos existentes: no es una implementación independiente de todo el DSGE ni una prueba de suficiencia de sus condiciones marginales.',
        'El cierre `zero_controls` es una condición terminal alternativa, no una afirmación de que los controles económicos deban ser cero: sus desviaciones logarítmicas terminales son cero.',
        'Examinar convergencia entre horizontes y cierres, márgenes y signos antes de interpretar el resultado.',
        '', 'Reproducción: `python code/irf/compare_nonlinear_tail.py`. No sobrescribe las IRF principales.']
    (args.output/'REPORT.md').write_text('\n'.join(text)+'\n',encoding='utf-8')
    provenance={'python':sys.version,'numpy':np.__version__,'scipy':scipy.__version__,
        'comparison_status':report['status'],
        'sha256':{str(q.relative_to(HERE)):hashlib.sha256(q.read_bytes()).hexdigest()
            for q in [Path(__file__),HERE/'finite_irf.py',HERE/'inputs/rational_preconditioners.json']},
        'report_sha256':hashlib.sha256(target.read_bytes()).hexdigest()}
    (args.output/'REPRODUCTION.json').write_text(json.dumps(provenance,indent=2)+'\n',encoding='utf-8')
    if not report['all_tested_regime_margins_passed']:
        raise SystemExit('Some finite-horizon roots violate the prescribed branch. See REPORT.json.')


if __name__=='__main__':
    main()
