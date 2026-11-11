#!/usr/bin/env python3
"""Conditional eight-row SOURCE firm bridge; six identities, two pledge shears.

Tests both regimes, four monetary shocks, off-root positive states and
33 numerical coordinate derivatives. The SOURCE economic operator is NOT
executed in Python: this is an independently transcribed, source-anchored
candidate bridge, not a proof of the full SOURCE 33x33 Jacobian.
"""
from __future__ import annotations
import hashlib
import json
import math
import re
from pathlib import Path
import finite_irf as model

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SOURCE = ROOT / "lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
ENGINE = HERE / "finite_irf.py"
P0 = HERE / "inputs/rational_preconditioners.json"
OUT = HERE / "output/source_firm_budget_euler_shear_audit.json"
# SOURCE index -> Python index and SOURCE label
INDEX = {0:(0,"firmBudgetZeroH"), 1:(3,"firmBudgetZeroL"),
         2:(1,"firmCapitalEulerZeroH"), 3:(4,"firmCapitalEulerZeroL"),
         17:(17,"firmBudgetOneH"), 18:(19,"firmBudgetOneL"),
         19:(18,"firmCapitalEulerOneH"),20:(20,"firmCapitalEulerOneL")}
DIRECT={0,1,2,3,17,18}
SHEAR={19,20}


def require(ok,msg):
    if not ok: raise AssertionError(msg)


def hsha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_transcription(base,p0,z,branch):
    """Evaluate SOURCE reduced firm rows under the Python parameter/coordinate chart.

    Profits use value added minus wage bills, and MPK uses the literal
    Cobb-Douglas expression; labor and output come from common primitives.
    """
    s=base.s
    x1=[base.X1[j]*math.exp(z[j]) for j in range(7)]
    u0=[base.U0[j]*math.exp(z[7+j]) for j in range(10)]
    x2c=[base.X2[j]*math.exp(z[17+j]) for j in range(6)]
    u1=[base.U1[j]*math.exp(z[23+j]) for j in range(10)]
    u2log=model.matvec(p0,z[17:23])
    u2=[s.base[6+j]*math.exp(u2log[6+j]) for j in range(10)]
    x2=model.expand_compact_state(s,x2c)
    values={}; shears={}; rootcoeff={}
    for t,(x,u,xn,un) in enumerate(((base.X0,u0,x1,u1),(x1,u1,x2,u2))):
        lab,outputs,_,_=model.production(s,x[:2],u)
        labn,_,_,_=model.production(s,xn[:2],un)
        for i in (0,1):
            rate=u[8]; pi=u[5]; pin=un[5]
            require(min(rate,pi,pin,x[i],xn[i],u[i],un[i])>0,
                    "Outside positive firm chart")
            profit=u[4]*outputs[i]-u[3]*lab[i]
            wealth=profit+s.ad*u[6]*x[i]-x[2+i]/pi
            budget=u[i]+u[6]*xn[i]-xn[2+i]/rate-wealth
            sdf=s.be*(u[i]/un[i])**s.sigmaE
            uk=(s.alpha*un[4]*s.technology[i]*
                xn[i]**(s.alpha-1)*labn[i]**s.beta)
            physical=s.pledge[i]*s.ad*pin*un[6]
            if t==0:
                ib,ie=(0,2) if i==0 else (1,3)
                if branch=="slack" and i==1:
                    euler=u[6]-sdf*(uk+s.ad*un[6])
                else:
                    euler=(u[6]-physical/rate -
                       sdf*(uk+s.ad*un[6]-physical/pin))
            else:
                ib,ie=(17,19) if i==0 else (18,20)
                euler=(u[6]-physical/rate -
                    sdf*(uk+s.ad*un[6]-physical/pin))
                J=x2c[2]; A=s.ad*pin*un[6]
                shears[ie]=s.pledge[i]*(J-A)*(1/rate-sdf/pin)
                rootcoeff[ie]=s.pledge[i]*A*(1/rate-sdf/pin)
            values[ib]=budget;values[ie]=euler
    J=x2c[2]; A=s.ad*u2[5]*u2[6]
    require(J>0 and A>0,"Common pledge log undefined")
    g=math.log(J/A)
    require(set(values)==set(INDEX) and set(shears)==SHEAR,
            "Missing firm row")
    require(all(math.isfinite(v) for v in
                [*values.values(),*shears.values(),*rootcoeff.values(),g]),
            "Nonfinite firm residual")
    return values,shears,g,rootcoeff


def smooth_expm1_div(g):
    """Smooth quotient expm1(g)/g, including the value 1 at zero."""
    if abs(g)<1e-7:
        return 1 + g/2 + g*g/6 + g*g*g/24 + g**4/120
    return math.expm1(g)/g


def main():
    src=SOURCE.read_text(encoding="utf-8")
    a=src.index("def localPrefixEquationOfIndex : Fin 33")
    b=src.index("noncomputable def localReducedPrefixResidualVector",a)
    names={int(i):name for i,name in re.findall(
          r"^\s*\|\s*(\d+)\s*=>\s*\.(\w+)\s*$",src[a:b],re.M)}
    require(len(names)==33,"SOURCE index count changed")
    for i,(j,name) in INDEX.items():
        require(names[i]==name,"SOURCE index mapping moved: "+str(i))
    for tag in ("noncomputable def localReducedFirmBudgetResidual",
                "noncomputable def localReducedFirmCapitalEulerResidual",
                "localPrefixFirmWealth P d i",
                "localPrefixNextMarginalProduct P d i",
                "localPrefixPledgeUnit P d i",
                "localPrefixStateSixFace P Z.stateTwo"):
        require(tag in src,"SOURCE row definition changed: "+tag)
    expect={0:"firm_budget_0_H",1:"firm_budget_0_L",
            2:"firm_capital_euler_0_H",3:"firm_capital_euler_0_L",
            17:"firm_budget_1_H",18:"firm_budget_1_L",
            19:"firm_capital_euler_1_H",20:"firm_capital_euler_1_L"}
    for i,(j,_) in INDEX.items():
        require(model.PREFIX_ROW_NAMES[j]==expect[i],
                "Python index mapping moved: "+str(i))
    s=model.steady_case()
    require(s.be==.96 and s.sigmaE==1 and s.ad==1-s.delta,
            "Illustrative entrepreneur preference/depreciation changed")
    p=json.loads(P0.read_text(encoding="utf-8"))
    p0=[[float(v) for v in row] for row in p["P0"]]
    require(len(p0)==16 and all(len(row)==6 for row in p0),
            "Pinned P0 dimensions changed")
    base=model.make_boundary(s)
    shocks=((0.,0.,0.,0.),(-1e-5,0.,0.,0.),(0.,-1e-5,0.,0.),
            (0.,0.,-1e-5,0.),(0.,0.,0.,-1e-5))
    zs=([0.]*33,
        [5e-4*math.sin((j+1)*1.71) for j in range(33)],
        [-8e-4*math.cos((j+1)*.81) for j in range(33)])
    max_direct=0.;max_shear=0.;max_deriv=0.;max_root_deriv=0.;n=0
    coeff_record={}
    max_functional_shear=0.
    max_product_derivative=0.
    offroot_shear_direction_checks=0
    for branch in ("binding","slack"):
        for shock in shocks:
            for z in zs:
                f,shear,g,_=source_transcription(base,p0,z,branch)
                py=model.prefix_residual(base,p0,branch,shock,z)
                require(abs(g-py[21])<1e-12,"Common pledge row mismatch")
                for i in DIRECT:
                    max_direct=max(max_direct,abs(f[i]-py[INDEX[i][0]]))
                for i in SHEAR:
                    max_shear=max(max_shear,
                        abs(f[i]-py[INDEX[i][0]]-shear[i]))
                    # The exact off-root row transformation has a
                    # state-dependent coefficient, not the root a_i.
                    _,_,_,coeff=source_transcription(base,p0,z,branch)
                    transformed=coeff[i]*smooth_expm1_div(g)*g
                    max_functional_shear=max(max_functional_shear,
                        abs(f[i]-py[INDEX[i][0]]-transformed))
                n+=1
        f0,sh0,g0,coef=source_transcription(base,p0,zs[0],branch)
        require(abs(g0)<1e-9,"Stationary common pledge root changed")
        coeff_record[branch]={str(i):coef[i] for i in SHEAR}
        for col in range(33):
            h=1e-6
            zp=list(zs[1]);zm=list(zs[1]);zp[col]+=h;zm[col]-=h
            fp,sp,_,_=source_transcription(base,p0,zp,branch)
            fm,sm,_,_=source_transcription(base,p0,zm,branch)
            gp=model.prefix_residual(base,p0,branch,shocks[1],zp)
            gm=model.prefix_residual(base,p0,branch,shocks[1],zm)
            _,_,g_plus,coef_plus=source_transcription(base,p0,zp,branch)
            _,_,g_minus,coef_minus=source_transcription(base,p0,zm,branch)
            for i in INDEX:
                dF=(fp[i]-fm[i])/(2*h)
                dG=(gp[INDEX[i][0]]-gm[INDEX[i][0]])/(2*h)
                dS=0. if i in DIRECT else (sp[i]-sm[i])/(2*h)
                max_deriv=max(max_deriv,abs(dF-dG-dS))
                if i in SHEAR:
                    # Finite difference the full smooth shear a(z)*g(z),
                    # including the derivative of the variable coefficient.
                    transformed_plus=coef_plus[i]*smooth_expm1_div(g_plus)*g_plus
                    transformed_minus=coef_minus[i]*smooth_expm1_div(g_minus)*g_minus
                    transformed_deriv=(transformed_plus-transformed_minus)/(2*h)
                    max_product_derivative=max(max_product_derivative,
                        abs(dF-dG-transformed_deriv))
                    offroot_shear_direction_checks+=1
            zp=[0.]*33;zm=[0.]*33;zp[col]=h;zm[col]=-h
            fp,_,_,_=source_transcription(base,p0,zp,branch)
            fm,_,_,_=source_transcription(base,p0,zm,branch)
            gp=model.prefix_residual(base,p0,branch,shocks[0],zp)
            gm=model.prefix_residual(base,p0,branch,shocks[0],zm)
            dg=(gp[21]-gm[21])/(2*h)
            for i in SHEAR:
                df=(fp[i]-fm[i])/(2*h)
                dp=(gp[INDEX[i][0]]-gm[INDEX[i][0]])/(2*h)
                max_root_deriv=max(max_root_deriv,abs(df-dp-coef[i]*dg))
    require(max_direct<3e-9,"Six firm SOURCE direct rows mismatched")
    require(max_shear<3e-9,"Common-pledge Euler row shear mismatched")
    require(max_functional_shear<3e-9,
            "Exact smooth off-root Euler row transformation mismatched")
    require(offroot_shear_direction_checks==2*33*2,
            "Incomplete two-branch, two-Euler, 33-direction product test")
    require(max_product_derivative<3e-6,
            "Off-root derivative of smooth shear coefficient mismatched")
    require(max_deriv<3e-6,"Off-root 33-column derivative mismatch")
    require(max_root_deriv<3e-6,"Root log-pledge row shear mismatch")
    report={
        "status":"CONDITIONAL_EIGHT_FIRM_ROWS_SIX_DIRECT_TWO_SHEAR_NOT_FULL_SOURCE_OPERATOR",
        "firm_source_to_python":{str(i):j for i,(j,_) in INDEX.items()},
        "direct_indices":sorted(DIRECT),"pledge_shear_indices":sorted(SHEAR),
        "identity":"F_source_Euler_i1-G_python_Euler_i1=theta_i*(J2-A2)*(1/RL1-m_i/Pi2)",
        "root_shear":"D F_source=D G_python+theta_i*A2*(1/RL1-m_i/Pi2)*D G_commonpledge",
        "root_shear_coefficients":coeff_record,
        "evaluated_branch_instrument_state_combinations":n,
        "derivative_columns":33,"derivative_branches":2,
        "max_direct_level_error":max_direct,"max_shear_level_error":max_shear,
        "max_off_root_derivative_error":max_deriv,
        "smooth_offroot_row_transform":"SOURCE_Euler = Python_Euler + a_i(z)*g(z), a_i=theta_i*A2*(1/RL1-m_i/Pi2)*expm1(g)/g",
        "max_smooth_offroot_transform_error":max_functional_shear,
        "max_smooth_offroot_product_derivative_error":max_product_derivative,
        "offroot_euler_product_derivative_direction_checks":offroot_shear_direction_checks,
        "max_root_log_shear_derivative_error":max_root_deriv,
        "total_candidate_positions_after_prior_25":33,
        "source_inputs_sha256":{str(f.relative_to(ROOT)):hsha(f)
                                for f in (SOURCE,ENGINE,P0)},
        "literal_source_operator_equality_proved":False,
        "complete_33x33_jacobian_bridge_proved":False,
        "infinite_equilibrium_or_growth_proved":False,
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    print(json.dumps({"status":report["status"],"n":n,"direct":max_direct,
                      "shear":max_shear,"derivative":max_deriv,
                      "root_derivative":max_root_deriv,"out":str(OUT)},indent=2))


if __name__=="__main__":
    main()
