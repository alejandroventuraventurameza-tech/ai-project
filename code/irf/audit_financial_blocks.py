"""Audit unreduced firm KKT and literal bank settlement on nonlinear paths.

Reconstructs multipliers and the two payment settlements rather than treating
reduced residuals alone as proof. This is a numerical necessary-condition and
accounting audit, not global intertemporal optimality or Lean reflection.
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
OUT=HERE/'output/financial_blocks_audit'


def require(ok,message):
    if not ok:raise AssertionError(message)


def unpack(problem,sol):
    b,s=problem.base,problem.s
    states={0:list(b.X0),1:[b.X1[i]*math.exp(sol[i]) for i in range(7)]}
    controls={0:[b.U0[i]*math.exp(sol[7+i]) for i in range(10)],
              1:[b.U1[i]*math.exp(sol[23+i]) for i in range(10)]}
    for t in range(2,problem.T+1):
        y=sol[problem.indices(t)]
        states[t]=model.expand_compact_state(s,[b.X2[i]*math.exp(y[i]) for i in range(6)])
        controls[t]=[s.base[6+i]*math.exp(y[6+i]) for i in range(10)]
    return states,controls


def node(problem,states,controls,t):
    s=problem.s;x,u=states[t],controls[t];xp,up=states[t+1],controls[t+1]
    a=model.auxiliary(s,x,u,xp[:2], [problem.base.e0[0]+problem.shock,problem.base.e0[1]] if t==0 else problem.base.e1 if t==1 else [0.,0.])
    # Independent literal labor condition and production, not stored uk/profit.
    ell=[(s.beta*u[4]*s.technology[i]*x[i]**s.alpha/u[3])**(1/(1-s.beta)) for i in range(2)]
    y=[s.technology[i]*x[i]**s.alpha*ell[i]**s.beta for i in range(2)]
    ellp=[(s.beta*up[4]*s.technology[i]*xp[i]**s.alpha/up[3])**(1/(1-s.beta)) for i in range(2)]
    yp=[s.technology[i]*xp[i]**s.alpha*ellp[i]**s.beta for i in range(2)]
    firms=[]
    for i in range(2):
        operating_profit=u[4]*y[i]-u[3]*ell[i]
        resale=s.ad*u[6]*x[i]; inherited_repayment=x[2+i]/u[5]
        N=operating_profit+resale-inherited_repayment
        b=xp[2+i]/u[8];h=s.pledge[i]*s.ad*up[5]*up[6]
        discount=s.be*u[i]/up[i]
        upsilon=1/u[8]-discount/up[5]
        mu=upsilon/u[i]  # sigma_E=1, lambda=1/c.
        gap=h*xp[i]-u[8]*b
        deposit_dual=1-discount*u[7]/up[5]
        capital_error=u[6]-discount*(s.alpha*up[4]*yp[i]/xp[i]+s.ad*up[6])-upsilon*h
        budget_error=u[i]+u[6]*xp[i]-N-b
        n=N-u[i];effective=u[6]-h/u[8]
        firms.append(dict(net_worth=N,own_investible=n,credit=b,capital_next=xp[i],
          operating_profit=operating_profit,resale_value=resale,inherited_repayment=inherited_repayment,consumption=u[i],
          collateral_per_capital=h,effective_price=effective,normalized_dual=upsilon,utility_dual=mu,
          collateral_slack=gap,deposit_corner_dual=deposit_dual,
          capital_KKT_error=capital_error,budget_error=budget_error,
          complementarity_error=upsilon*gap,
          funding_KKT_error=discount*u[8]/up[5]+upsilon*u[8]-1,
          labor_error=s.beta*u[4]*y[i]/ell[i]-u[3]))
    B=sum(s.mass[i]*firms[i]['credit'] for i in range(2));E=x[4]/u[5]
    D=a['money']/a['h'];M=a['money'];theta=u[9]
    require(0<theta<1,'This audit uses the bilateral theta<1 branch')
    psiminus=s.aa;psiplus=theta*s.aa
    rF=a['rr']+s.Delta/(1+math.sqrt(2-theta));rW=a['rr']+s.Delta
    cm=psiminus*(rF-a['rr'])+(1-psiminus)*(rW-a['rr'])
    cp=psiplus*(rF-a['rr'])
    atoms=[]
    for omega,psi in [(-s.zeta,psiminus),(s.zeta,psiplus)]:
        surplus=M-s.rho*D+(u[7]/a['rr']-s.rho)*omega*D
        interbank=-psi*surplus
        facility=-(1-psi)*surplus if surplus<0 else 0.
        post=M+(u[7]/a['rr'])*omega*D+interbank+facility
        gross=(u[8]*B+a['rr']*post-u[7]*D*(1+omega)-rF*interbank-rW*facility)/up[5]
        compact=(u[8]*B+a['rr']*M-u[7]*D+(cm if surplus<0 else cp)*surplus)/up[5]
        atoms.append(dict(surplus=surplus,interbank=interbank,facility=facility,post=post,
              reserve_requirement_margin=post-s.rho*D*(1+omega),real_return=gross,
              compact_return_error=gross-compact))
    expected=sum(z['real_return'] for z in atoms)/2
    gbar=(cm+cp)/2
    gweighted=(cm*(-s.zeta)+cp*s.zeta)/2
    # Supporting-slope coefficients in E[N] <= ax*x + aL*L + aD*D.
    ax=a['rr']+gbar
    aL=u[8]-a['rr']-gbar
    aD=a['rr']-u[7]+(1-s.rho)*gbar+(u[7]/a['rr']-s.rho)*gweighted
    bank=dict(equity=E,loans=B,deposits=D,reserves=M,tightness=theta,
       balance_error=B+M-D-E,deposit_cap_margin=4*E-D,loan_cap_margin=6*E-B,
       expected_interbank_error=sum(z['interbank'] for z in atoms)/2,
       expected_return_error=expected-u[8]*E/up[5],
       expected_renewal_face_error=xp[4]-s.aB*expected*up[5],
       slope_order_margin=cm-cp,loan_support_coefficient=aL,deposit_support_coefficient=aD,
       equity_support_error=ax-u[8],
       SDF_return_ratio_error=s.bw*u[2]/up[2]*expected/E-u[8]/u[7],
       payment_atoms=atoms,loan_rate=u[8],deposit_rate=u[7],reserve_rate=a['rr'])
    return firms,bank


def source_map():
    mapping={}
    for name in model.PREFIX_ROW_NAMES:
        if name.startswith('firm_budget'):refs=['eq:firmbudget','eq:wealth'];kind='Budget with inherited nominal face and no firm deposits'
        elif name.startswith('firm_capital_euler'):refs=['eq:capitalFOC','eq:loanFOC'];kind='Capital FOC after eliminating normalized collateral dual'
        elif name.startswith('firm_regime'):refs=['eq:collateral','eq:complementarity','eq:loanFOC'];kind='H binding; L slack only at date 0 in S, binding in B'
        elif name.startswith('bank_equity'):refs=['eq:bankwealth','eq:equityidentity'];kind='Expected return plus exit/entry renewal, full retention'
        elif name.startswith('capital_supply'):refs=['eq:q'];kind='Interior capital production'
        elif name.startswith('resources'):refs=['eq:resources'];kind='Aggregate resource identity'
        elif name.startswith('worker_labor'):refs=['eq:household'];kind='Labor FOC displayed after household budget'
        elif name.startswith('household_euler'):refs=['eq:household'];kind='Interior deposit Euler displayed after household budget'
        elif name.startswith('nkpc'):refs=['eq:nkpc'];kind='Symmetric price FOC; sufficiency separate'
        elif name.startswith('reserve_'):refs=['sec:v0m_source_11'];kind='Instrument rule with inherited lag and announced innovation'
        elif name.startswith('loan_pricing'):refs=['eq:bankFOCL'];kind='Bank FOC, inactive caps, no atom at settlement kink'
        elif name.startswith('deposit_pricing'):refs=['eq:bankFOCD'];kind='Bank FOC, inactive caps, two mean-zero payment atoms'
        elif name.startswith('bank_balance'):refs=['eq:bankbalance','eq:IBclearing'];kind='Balance after eliminating deposits through OTC clearing'
        elif name.startswith('common_pledge'):refs=['eq:H','eq:initial_faces_manifold'];kind='Common future pledge value on the regenerated binding manifold'
        else:raise ValueError(name)
        mapping[name]={'paper_labels':refs,'interpretation':kind,'global_sufficiency_proved_here':False}
    require(len(mapping)==33,'Incomplete row inventory')
    return mapping


def main():
    OUT.mkdir(exist_ok=True)
    report={'status':'running','full_equilibrium_validated':False,'branches':{},
      'scope':'Literal numerical firm KKT, deposit corner, bank balance and two-atom settlement on the deterministic reduced nonlinear T=640 path. Necessary conditions and a conditional one-period concavity bound; no global dynamic sufficiency claim.'}
    target=OUT/'REPORT.json';target.write_text(json.dumps(report)+'\n',encoding='utf-8')
    data=json.loads((HERE/'inputs/rational_preconditioners.json').read_text())
    p,f=np.asarray(data['P0'],float),np.asarray(data['F0'],float)
    records=[]
    try:
        for branch in ['slack','binding']:
            problem=StackedPath(640,branch,-1e-5,'linear_graph',p,f)
            reference=StackedPath(640,branch,0.,'linear_graph',p,f)
            sol,history=problem.solve();ref,_=reference.solve()
            states,controls=unpack(problem,sol);states0,controls0=unpack(reference,ref)
            seed_fraction=(problem.s.aB-(1-problem.s.eta))/problem.s.eta
            require(0<=seed_fraction<=1,'Implied entry-seed fraction outside source domain')
            maxima={};minima={};nodes=[]
            def err(key,value):maxima[key]=max(maxima.get(key,0.),abs(value))
            def margin(key,value):minima[key]=min(minima.get(key,math.inf),value)
            for t in range(problem.T):
                firms,bank=node(problem,states,controls,t);nodes.append((firms,bank))
                for i,z in enumerate(firms):
                    for key in ['capital_KKT_error','budget_error','complementarity_error','funding_KKT_error','labor_error']:err(key,z[key])
                    for key in ['net_worth','own_investible','effective_price','deposit_corner_dual','credit']:margin(key,z[key])
                    margin('dual_nonnegative',z['normalized_dual']);margin('collateral_feasible',z['collateral_slack'])
                    record={'branch':branch,'period':t,'firm':'H' if i==0 else 'L',**z};records.append(record)
                for key in ['balance_error','expected_interbank_error','expected_return_error','expected_renewal_face_error','loan_support_coefficient','deposit_support_coefficient','equity_support_error','SDF_return_ratio_error']:err(key,bank[key])
                for key in ['deposit_cap_margin','loan_cap_margin','slope_order_margin']:margin(key,bank[key])
                for atom in bank['payment_atoms']:
                    err('compact_return_error',atom['compact_return_error'])
                    margin('reserve_requirement_margin',atom['reserve_requirement_margin'])
                    margin('real_bank_return',atom['real_return']);margin('facility_nonnegative',atom['facility'])
            require(max(maxima.values())<1e-9,f'Financial identity failure: {maxima}')
            require(all(v>0 for k,v in minima.items() if k not in ['dual_nonnegative','collateral_feasible','reserve_requirement_margin','facility_nonnegative']),str(minima))
            require(all(minima[k]>=-1e-10 for k in ['dual_nonnegative','collateral_feasible','reserve_requirement_margin','facility_nonnegative']),str(minima))
            firm0,bank0=nodes[0];firmref,bankref=node(reference,states0,controls0,0)
            H,H0=firm0[0],firmref[0]
            own_delta=H['own_investible']-H0['own_investible']
            own_log=math.log(H['own_investible']/H0['own_investible'])
            own_factor=100*own_log/own_delta if own_delta else 100/H0['own_investible']
            wealth_parts={
                'operating_profit':own_factor*(H['operating_profit']-H0['operating_profit']),
                'resale_value_installed_capital':own_factor*(H['resale_value']-H0['resale_value']),
                'negative_inherited_real_repayment':-own_factor*(H['inherited_repayment']-H0['inherited_repayment']),
                'negative_consumption':-own_factor*(H['consumption']-H0['consumption'])}
            require(abs(sum(wealth_parts.values())-100*own_log)<1e-9,'Own resources accounting failed')
            dk=100*math.log(H['capital_next']/H0['capital_next'])
            dn=100*math.log(H['own_investible']/H0['own_investible'])
            dp=-100*math.log(H['effective_price']/H0['effective_price'])
            db=100*math.log(H['credit']/H0['credit'])
            dh=100*math.log(H['collateral_per_capital']/H0['collateral_per_capital'])
            dr=-100*math.log(bank0['loan_rate']/bankref['loan_rate'])
            require(abs(dk-dn-dp)<1e-8,'Capital identity mismatch')
            require(abs(db-dh-dk-dr)<1e-8,'Credit identity mismatch')
            report['branches'][branch]={'max_absolute_errors':maxima,'min_margins':minima,
              'impact_H':{'credit_log_pct':db,'capital_next_log_pct':dk,
               'normalized_multiplier_change':H['normalized_dual']-H0['normalized_dual'],
               'utility_multiplier_change':H['utility_dual']-H0['utility_dual'],
               'capital_identity_contributions':{'own_investible_resources':dn,'negative_effective_price':dp},
               'own_resources_identity_contributions_log_pct':wealth_parts,
               'credit_identity_contributions':{'pledge_value_per_capital':dh,'capital_next':dk,'negative_loan_rate':dr}},
              'L_date0_normalized_dual':firm0[1]['normalized_dual'],
              'L_date0_collateral_gap':firm0[1]['collateral_slack'],
              'min_L_dual_after_date0':min(z[0][1]['normalized_dual'] for z in nodes[1:]),
              'solver_final_residual':history[-1],
              'entry_seed_fraction_implied_by_renewal_factor':seed_fraction}
            print(branch,report['branches'][branch]['impact_H'],flush=True)
        report['status']='passed_scoped_financial_block_audit'
        report['source_row_inventory']=source_map()
        paper=HERE.parents[1]/'paper/paper.tex'
        text=paper.read_text(encoding='utf-8')
        for row in report['source_row_inventory'].values():
            for label in row['paper_labels']:require('\\label{'+label+'}' in text,f'Missing source label: {label}')
        report['input_sha256']={str(q.relative_to(HERE.parents[1])):hashlib.sha256(q.read_bytes()).hexdigest()
           for q in [Path(__file__),HERE/'finite_irf.py',HERE/'compare_nonlinear_tail.py',HERE/'inputs/rational_preconditioners.json',paper]}
    except Exception as error:
        report['status']='failed';report['error']=str(error);raise
    finally:target.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    with (OUT/'firm_conditions.csv').open('w',newline='',encoding='utf-8') as handle:
        writer=csv.DictWriter(handle,fieldnames=list(records[0]));writer.writeheader();writer.writerows(records)
    lines=['# Auditoría de empresas y liquidación bancaria','',report['scope'],'',
      '## Empresa: condiciones sin eliminar el multiplicador',
      'Se reconstruye N a partir de producción, salario, capital heredado y repago nominal; no se define como residuo del presupuesto.',
      'Con u_E(c)=log(c), M_E=beta_E*c_t/c_(t+1) y h=theta_i(1-delta)Pi_(t+1)q_(t+1):',
      '- upsilon=mu/lambda=1/RL-M_E/Pi_(t+1). Esta igualdad reconstruye el dual desde la FOC de préstamos.',
      '- Se comprueban además capital, caja, complemento, no negatividad del dual y del colateral, y la esquina sin depósitos.',
      '- El dual de no depositar es 1-M_E*RD/Pi_(t+1); resulta positivo. Crédito positivo con depósitos empresariales cero es consistente con esa esquina.',
      '- La cobertura robusta se especializa a la única transición agregada del experimento; no audita un árbol agregado estocástico general.',
      '', '## Identidades para H restringida',
      'k_(H,t+1)=(N_Ht-c_Ht)/(q_t-h_Ht/RL_t).',
      'Delta log k_next = Delta log(N-c) - Delta log(q-h/RL).',
      'b_Ht=h_Ht*k_(H,t+1)/RL_t; por tanto Delta log b = Delta log h + Delta log k_next - Delta log RL.',
      'Las contribuciones son identidades sobre soluciones conjuntas, no contrafactuales causales independientes.',
      '', '| Rama | Crédito H (log %) | Capital elegido H (log %) | Cambio dual normalizado H |',
      '|---|---:|---:|---:|']
    for b,q in report['branches'].items():
        h=q['impact_H'];lines.append(f"| {b} | {h['credit_log_pct']:.10g} | {h['capital_next_log_pct']:.10g} | {h['normalized_multiplier_change']:.10g} |")
    lines += ['', '## Recursos propios de H: trazabilidad de patrimonio y consumo',
      'n=N-c=beneficio operativo + valor de reventa del capital instalado - repago real heredado - consumo.',
      'Se verifica su descomposición exacta en niveles y se convierte a contribuciones logarítmicas mediante Delta log(n)/Delta n. No son efectos causales aislados.', '']
    for branch,q in report['branches'].items():
        lines.append(f"- {branch}: {q['impact_H']['own_resources_identity_contributions_log_pct']}")
    lines+=['', '## Banco: contabilidad y condiciones de reducción',
      'Se calculan por separado los dos pagos, el exceso de reservas, préstamo interbancario, facilidad, reservas finales y retorno detallado. Se verifican clearing esperado, encaje posterior, caps holgados, orden de pendientes, solvencia y renovación.',
      'Bajo los precios y matching del régimen, chi es cóncava y homogénea. Su pendiente en cada átomo candidato proporciona una cota superior global de una etapa:',
      'E[N_nominal] <= (RR+E[g])*x + (RL-RR-E[g])*L + (RR-RD+E[g*(1-rho+(xi-rho)*omega)])*D.',
      'Las ecuaciones de precios anulan los coeficientes de L y D y hacen RR+E[g]=RL. Por ello la cota es RL*x. Se comprueban sus coeficientes numéricamente y que la cartera candidata alcanza la igualdad.',
      'Este argumento requiere precios y matching dados e independencia de los pesos futuros respecto al pago individual. No resuelve por sí solo la elección dinámica de dividendos ni demuestra el valor infinito.',
      '', '## Resultado e interpretación',
      'En S, H recibe más crédito, elige más capital y baja su dual. En B, recibe más crédito, pero elige menos capital y sube su dual. El capital efectivo y las promesas no se confunden con el principal del préstamo.',
      'Por tanto, el experimento no justifica describir las dos ramas como relajación económica uniforme de la restricción. La expansión de crédito no equivale a una mejora asignativa ni a una caída del valor marginal del colateral.',
      'Los errores y márgenes se detallan en REPORT.json; el inventario de las 33 filas es una trazabilidad de fuente, no cobertura formal ni prueba de suficiencia.',
      '', '## Pendientes',
      'Optimalidad dinámica, valor y dominación de todas las políticas admisibles; suficiencia de los demás agentes; instancia de equilibrio completo y reflexión Lean de la evidencia externa.',
      '', 'Reproducción: `python code/irf/audit_financial_blocks.py`. No cambia las IRF principales ni parámetros.']
    (OUT/'REPORT.md').write_text('\n'.join(lines)+'\n',encoding='utf-8')


if __name__=='__main__':main()
