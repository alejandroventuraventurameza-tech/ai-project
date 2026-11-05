"""Uniform second derivative and small-risk certificate; no histories are simulated."""
from pathlib import Path
from fractions import Fraction
from decimal import Decimal as D
import json
import random
import numpy as np
from verified_linear_operator import I,UP,DOWN,NEAR,steady,arr,sum_up,product_up,quotient_up

HERE=Path(__file__).parent

class Jet:
    """Interval value and upper bounds on |Df| and |D²f| in the input sup norm."""
    __slots__=('x','d','h')
    def __init__(self,x,d=0,h=0):self.x=I(x);self.d=D(d);self.h=D(h)
    def __add__(self,b):
        b=asjet(b)
        return Jet(self.x+b.x,UP.add(self.d,b.d),UP.add(self.h,b.h))
    __radd__=__add__
    def __neg__(self):return Jet(-self.x,self.d,self.h)
    def __sub__(self,b):return self+-asjet(b)
    def __rsub__(self,b):return asjet(b)+-self
    def __mul__(self,b):
        b=asjet(b);ma,mb=self.x.magnitude(),b.x.magnitude()
        return Jet(self.x*b.x,
                   sum_up([product_up(self.d,mb),product_up(ma,b.d)]),
                   sum_up([product_up(self.h,mb),product_up(D(2),self.d,b.d),product_up(ma,b.h)]))
    __rmul__=__mul__
    def reciprocal(self):
        r=self.x.reciprocal();mag=r.magnitude()
        return Jet(r,product_up(mag,mag,self.d),
                   sum_up([product_up(D(2),mag,mag,mag,self.d,self.d),product_up(mag,mag,self.h)]))
    def __truediv__(self,b):return self*asjet(b).reciprocal()
    def __rtruediv__(self,b):return asjet(b)*self.reciprocal()
    def __pow__(self,n):
        assert isinstance(n,int)
        if n<0:return (self**(-n)).reciprocal()
        if n==0:return Jet(1)
        if n==1:return self
        half=self**(n//2);value=half*half
        return value if n%2==0 else value*self
    def exp(self):
        value=self.x.exp();bound=value.hi
        return Jet(value,product_up(bound,self.d),product_up(bound,sum_up([self.h,product_up(self.d,self.d)])))
    def ln(self):
        assert self.x.lo>0
        rec=quotient_up(D(1),self.x.lo)
        return Jet(self.x.ln(),product_up(rec,self.d),
                   sum_up([product_up(rec,self.h),product_up(rec,rec,self.d,self.d)]))
    def power(self,r):return (asjet(r)*self.ln()).exp()

def asjet(x):return x if isinstance(x,Jet) else Jet(x)
def total(values):return sum(values,Jet(0))
def average(values):return total(values)/4

def enclose(box=D('1e-6'), point=None):
    s=steady()
    position=iter(point) if point is not None else None
    new=lambda:Jet(I(str(next(position))) if position is not None else I(-box,box),1,0)
    y=[new() for _ in range(16)];X1=[new() for _ in range(6)]
    U1=[[new() for _ in range(10)] for _ in range(4)];e=[new(),new()]
    now=[asjet(s.base[i])*y[i].exp() for i in range(16)]
    future=[[asjet(s.base[i])*v.exp() for i,v in enumerate(X1+U1[j])] for j in range(4)]
    def production(k,w,m):
        ell=[(asjet(s.beta)*m*s.technology[i]*k[i].power(s.alpha)/w)**2 for i in range(2)]
        output=[w*ell[i]/(asjet(s.beta)*m) for i in range(2)]
        profit=[(1-asjet(s.beta))*m*v for v in output]
        uk=[asjet(s.alpha)*m*output[i]/k[i] for i in range(2)]
        return ell,output,profit,uk
    k0,k1=now[:2],future[0][:2];J0,J1=now[2],future[0][2]
    c0=now[6:8];cw0=now[8];w0,m0,pi0,q0,rd0,rl0,th0=now[9:]
    l0,yy0,pr0,_=production(k0,w0,m0)
    next_production=[production(v[:2],v[9],v[10]) for v in future]
    K0=total([asjet(s.mass[i])*k0[i] for i in range(2)])
    K1=total([asjet(s.mass[i])*k1[i] for i in range(2)])
    Y0=total([asjet(s.mass[i])*yy0[i] for i in range(2)])
    L0=total([asjet(s.mass[i])*l0[i] for i in range(2)])
    Y1=[total([asjet(s.mass[i])*pr[1][i] for i in range(2)]) for pr in next_production]
    logrr=asjet(I('.5'))*y[4]+asjet(I('.5'))*(asjet(I('1.5'))*y[11]+asjet(I('.125'))*(Y0/s.Y).ln())+e[0]
    logmm=asjet(I('.5'))*y[5]+e[1]
    rr0=asjet(s.rr)*logrr.exp();mm0=asjet(s.M)*logmm.exp()
    nu=1/(1+(2-th0).power(I('.5')))
    cm=asjet(s.Delta)*(1-asjet(s.aa)+asjet(s.aa)*nu)
    cp=asjet(s.Delta)*th0*s.aa*nu
    cb,cd=(cm+cp)/2,cm-cp
    xi=rd0/rr0
    h=asjet(s.rho)+(xi-s.rho)*s.zeta*(1-th0)/(1+th0)
    pp=[q0-asjet(s.pledge[i])*J1/rl0 for i in range(2)]
    NN=[pr0[i]+asjet(s.ad)*q0*k0[i]-asjet(s.pledge[i])*J0*k0[i]/pi0 for i in range(2)]
    inv=K1-asjet(s.ad)*K0
    Gamma=inv+asjet(s.phiI)*inv**2/(2*K0)
    Rot=asjet(75)*(pi0-1)**2*Y0
    le=[[asjet(s.be)*c0[i]/v[6+i] for i in range(2)] for v in future]
    lw=[asjet(s.bw)*cw0/v[8] for v in future]
    collateral=X1[2]-U1[2][5]-U1[2][6]
    euler=[pp[i]-average([le[j][i]*(next_production[j][3][i]+asjet(s.ad)*future[j][12]-asjet(s.pledge[i])*J1/future[j][11]) for j in range(4)]) for i in range(2)]
    res=[c0[i]+pp[i]*k1[i]-NN[i] for i in range(2)]
    res.extend([euler[i]-asjet(s.be*s.pledge[i]*s.J)*collateral for i in range(2)])
    res.extend([collateral,
                X1[3]-y[14]-y[3]+y[11],
                q0-1-asjet(s.phiI)*inv/K0,
                cw0+total([asjet(s.mass[i])*c0[i] for i in range(2)])+Gamma+Rot-Y0,
                (w0/(asjet(s.chiW)*L0*cw0)).ln(),
                (rd0*average([lw[j]/future[j][11] for j in range(4)])).ln(),
                1-asjet(s.eps)+asjet(s.eps)*m0-asjet(150)*pi0*(pi0-1)+asjet(150)*average([lw[j]*Y1[j]/Y0*future[j][11]*(future[j][11]-1) for j in range(4)]),
                X1[4]-logrr,X1[5]-logmm,
                rl0-rr0-cb,
                rr0+(1-asjet(s.rho))*cb-(xi-s.rho)*s.zeta*cd/2-rd0,
                total([asjet(s.mass[i]*s.pledge[i])*J1*k1[i]/rl0 for i in range(2)])-(now[3]/pi0+(1/h-1)*mm0)])
    assert len(res)==16
    bankE=now[3]/pi0;bankD=mm0/h;bankB=bankE+bankD-mm0
    margins={
        'investment':inv.x,'effective_price_H':pp[0].x,'effective_price_L':pp[1].x,
        'collateral_dual_H':(1/rl0-average([le[j][0]/future[j][11] for j in range(4)])).x,
        'collateral_dual_L':(1/rl0-average([le[j][1]/future[j][11] for j in range(4)])).x,
        'no_deposit_dual_H':(1-rd0*average([le[j][0]/future[j][11] for j in range(4)])).x,
        'no_deposit_dual_L':(1-rd0*average([le[j][1]/future[j][11] for j in range(4)])).x,
        'deposit_cap_slack_per_equity':(4-bankD/bankE).x,
        'loan_cap_slack_per_equity':(6-bankB/bankE).x,
        'reserve_ratio_lower':h.x,'reserve_ratio_upper':(1-h).x,
        'OTC_tightness_lower':th0.x,'OTC_tightness_upper':(1-th0).x,
        'xi_minus_rho':(xi-s.rho).x,
        'bank_retention_gain':(rl0/rd0-1).x,
        'bank_continuation_gap':(1-asjet(I('.9'))*rl0/rd0).x,
        'public_bonds_example_Gbar_2Mbar':(2*asjet(s.M)-mm0).x,
        'marginal_cost_global_pricing_margin':(m0-asjet(I('.82'))).x,
        'inflation_global_pricing_margin':I('.02')-((pi0-1).x.magnitude()),
    }
    for omega,slope,name in [(I('-.2'),cm,'minus'),(I('.2'),cp,'plus')]:
        surplus=mm0-asjet(s.rho)*bankD+(xi-s.rho)*omega*bankD
        margins['payment_sign_'+name]=(-surplus if name=='minus' else surplus).x
        margins['bank_solvency_'+name]=((rl0*bankB+rr0*mm0-rd0*bankD+slope*surplus)/bankE).x
    for name,value in margins.items():assert value.lo>0,(name,value)
    return max(v.h for v in res),[str(v.h) for v in res],margins,[v.x for v in res]

def arithmetic_checks():
    rng=random.Random(155454);count=0
    for _ in range(100):
        a=Fraction(rng.randrange(-100,101),rng.randrange(1,101))
        b=Fraction(rng.randrange(1,101),rng.randrange(1,101))
        ai=I(a.numerator)/I(a.denominator);bi=I(b.numerator)/I(b.denominator)
        for box,exact in [(ai+bi,a+b),(ai-bi,a-b),(ai*bi,a*b),(ai/bi,a/b),(ai**2,a*a)]:
            assert Fraction(box.lo)<=exact<=Fraction(box.hi)
            count+=1
    return count

def main():
    checks=arithmetic_checks()
    Hess,rows,margins,_=enclose()
    previous=json.loads(HERE.joinpath('verified_linear_bounds.json').read_text(encoding='utf-8'))
    C=D(previous['augmented_inverse_including_initial_coverage_upper'])
    M=D(previous['first_variation_plan_norm_upper'])
    gap=D(previous['worst_child_separation'][0])
    # Deliberately round all constants UP to simple decimal bounds.
    def up_simple(x):
        exponent=x.adjusted()
        return D(10)**(exponent+1)
    C,H,M=map(up_simple,(C,Hess,M))
    g=D('.0008');assert gap>g
    box=D('1e-6');oneplus=UP.add(M,D(1))
    inverse_condition=DOWN.divide(D(1),product_up(D(4),C,H,oneplus))
    box_condition=DOWN.divide(DOWN.multiply(D(4),box),product_up(D(5),oneplus))
    selection_condition=DOWN.divide(g,product_up(D(8),C,H,oneplus,oneplus))
    threshold=min(inverse_condition,box_condition,selection_condition)
    eta=D(10)**(threshold.adjusted()-1)
    rho=product_up(C,H,oneplus,oneplus,eta,eta)
    logbound=sum_up([product_up(M,eta),rho])
    contraction=product_up(C,H,sum_up([logbound,eta]))
    image_argument=sum_up([product_up(oneplus,eta),rho])
    image=UP.divide(product_up(C,H,image_argument,image_argument),D(2))
    order_gap=DOWN.subtract(DOWN.multiply(g,eta),UP.multiply(D(4),rho))
    assert image<rho and contraction<D('.5') and logbound<box and order_gap>0
    # If the minimum remains endogenous, the uniform selector-tree lemma
    # gives the same inverse Lipschitz bound without an order-gap condition.
    min_threshold=min(inverse_condition,box_condition)
    min_eta=D(10)**(min_threshold.adjusted()-1)
    min_rho=product_up(C,H,oneplus,oneplus,min_eta,min_eta)
    min_logbound=sum_up([product_up(M,min_eta),min_rho])
    min_lip=product_up(C,H,sum_up([min_logbound,min_eta]))
    min_argument=sum_up([product_up(oneplus,min_eta),min_rho])
    min_image=UP.divide(product_up(C,H,min_argument,min_argument),D(2))
    assert min_image<min_rho and min_lip<D('.5') and min_logbound<box
    out={
        'scope':__doc__,'rational_arithmetic_containment_checks':checks,
        'nonlinear_domain_log_box':str(box),
        'hessian_bilinear_sup_norm_upper':str(Hess),'hessian_rows_upper':rows,
        'rounded_certificate_constants':{'C_aug':str(C),'H':str(H),'M_first':str(M),'g_min':str(g)},
        'sufficient_eta_thresholds':{'contraction':str(inverse_condition),'domain':str(box_condition),'worst_child':str(selection_condition)},
        'certified_eta_upper':str(eta),'correction_sup_norm_upper':str(rho),
        'total_loglevel_sup_bound':str(logbound),'nonlinear_map_contraction_upper':str(contraction),
        'nonlinear_map_image_upper':str(image),'strict_child_order_gap_lower':str(order_gap),
        'endogenous_minimum_without_fixed_order':{
            'certified_eta_upper':str(min_eta),
            'correction_sup_norm_upper':str(min_rho),
            'total_loglevel_sup_bound':str(min_logbound),
            'nonlinear_map_contraction_upper':str(min_lip),
            'nonlinear_map_image_upper':str(min_image),
            'condition':'Uniform eight-step comparison for arbitrary node selectors and their convex mixtures; no fixed-child gap condition.',
        },
        'strict_margins_enclosures':{k:[str(v.lo),str(v.hi)] for k,v in margins.items()},
        'initialization':'Five initial logstocks eta*(P_X mean_shift) excluding J; initial J solved jointly using exact linear logcoverage row B0*y=0. Relative retail price before initial date equals 1.',
        'fiscal_completion':'For the numerical witness only, Gbar=2*Mbar. No impact on the 16 core equations; other interior holdings require their own margin.',
        'limits':'Very conservative sufficient radius, not an estimate or maximum allowable shock. No evidence that larger shocks lack an equilibrium. Computer-assisted certificate, not Lean/AML; no simulation or IRF.',
    }
    HERE.joinpath('verified_nonlinear_radius.json').write_text(json.dumps(out, indent=2), encoding='utf-8', newline='\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
