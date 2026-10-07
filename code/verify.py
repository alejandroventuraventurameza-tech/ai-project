"""Verify the project's conditional results, financial regimes and counterexamples.

Run from any directory with Python >= 3.10. No third-party packages are required.
Numerical checks do not replace the analytic proof or establish empirical causality.
"""
from pathlib import Path
import csv
import json
import math
import random

HERE = Path(__file__).resolve().parent
SEED = 20261007
DRAWS = 10000


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def close(a, b, scale=1.0, tol=1e-8):
    require(abs(a-b) <= tol*max(scale, abs(a), abs(b)), f"Mismatch: {a} != {b}")


def bisect(f, lo, hi):
    flo, fhi = f(lo), f(hi)
    if abs(flo) < 1e-14:
        return lo
    if abs(fhi) < 1e-14:
        return hi
    require(flo*fhi <= 0, "Root is not bracketed")
    for _ in range(90):
        mid = (lo+hi)/2
        fm = f(mid)
        if fm == 0:
            return mid
        if flo*fm <= 0:
            hi = mid
        else:
            lo, flo = mid, fm
    return (lo+hi)/2


def demand(a, n, h, alpha, rho, t, price):
    require(a > 0 and n > 0 and h > 0 and 0 < alpha < 1, "Invalid firm primitives")
    require(price > 0 and t > rho > 0, "Invalid prices")
    power = 1/(1-alpha)
    own = n/price
    cap = (n+h/t)/price
    ksave = (alpha*a/(rho*price))**power
    kborrow = (alpha*a/(t*price))**power
    if ksave < own:
        return ksave, "self"
    if kborrow <= own:
        return own, "kink"
    if kborrow < cap:
        return kborrow, "interior"
    return cap, "capped"


def check_kkt(a, n, h, alpha, rho, t, price):
    k, regime = demand(a, n, h, alpha, rho, t, price)
    x, b = min(price*k, n), max(price*k-n, 0)
    mp = alpha*a*k**(alpha-1)
    close(price*k, x+b)
    require(x <= n+1e-8 and t*b <= h+1e-8*max(1,h), "Budget/collateral failure")
    if regime == "self":
        close(mp, rho*price)
    elif regime == "kink":
        require(rho*price-1e-8 <= mp <= t*price+1e-8, "Kink subgradient failure")
    elif regime == "interior":
        close(mp, t*price)
    else:
        close(t*b, h)
        require(mp >= t*price-1e-8, "Negative collateral multiplier")
    # Independently compare nearby feasible capital choices with the objective.
    cap = (n+h/t)/price
    def payoff(q):
        return a*q**alpha-rho*price*q-(t-rho)*max(price*q-n,0)+rho*n
    candidates = [0, n/price, cap, max(0,k*(1-1e-4)), min(cap,k*(1+1e-4))]
    for q in candidates:
        require(payoff(q) <= payoff(k)+1e-8*max(1,abs(payoff(k))), "Nonoptimal demand")
    return regime


def mixed(nh, hh, al, alpha, rho, t, capital):
    s = 1/(1-alpha)
    def clearing(price):
        return (nh+hh/t)/price+(alpha*al/(rho*price))**s-capital
    lo, hi = 1e-9, 1.0
    while clearing(hi) > 0:
        hi *= 2
    price = bisect(clearing, lo, hi)
    kh = (nh+hh/t)/price
    kl = (alpha*al/(rho*price))**s
    close(kh+kl, capital)
    return price, kh, kl


def two_capped(nh,nl,hh,hl,t,capital):
    price = (nh+nl+(hh+hl)/t)/capital
    kh = capital*(t*nh+hh)/(t*(nh+nl)+hh+hl)
    kl = capital-kh
    close(price*kh, nh+hh/t)
    close(price*kl, nl+hl/t)
    return price, kh, kl


def efficient(ah,al,alpha,capital):
    ratio = math.exp(math.log(ah/al)/(1-alpha))
    kh = capital*ratio/(1+ratio)
    return kh, ah*kh**alpha+al*(capital-kh)**alpha


def measures(ah,al,alpha,kh,kl):
    _, ystar = efficient(ah,al,alpha,kh+kl)
    y = ah*kh**alpha+al*kl**alpha
    gap = abs(math.log(ah/al)+(alpha-1)*math.log(kh/kl))
    return y, 1-y/ystar, gap


def bank_rate(m,total_h,rho,c,kappa,delta,equity):
    def residual(t):
        b = total_h/t
        deposits = b+m-equity
        return t-rho-c-kappa*delta*max(delta*deposits-m,0)
    lo, hi = rho+c, max(2*(rho+c),1)
    while residual(hi) < 0:
        hi *= 2
    return bisect(residual,lo,hi)


def main():
    rng = random.Random(SEED)
    regimes = dict.fromkeys(["self","kink","interior","capped"],0)
    signs = dict.fromkeys(["H_gains","H_loses","neutral"],0)
    efficiency_checks = 0
    max_mixed_error = max_bank_error = 0.0
    for _ in range(DRAWS):
        alpha=rng.uniform(.2,.75); rho=rng.uniform(.7,1.4); t=rho+rng.uniform(.1,1.5)
        a,n,h,price=[10**rng.uniform(-1,1) for _ in range(4)]
        regimes[check_kkt(a,n,h,alpha,rho,t,price)] += 1

        capital=rng.uniform(1,8); nh=rng.uniform(.1,2); hh=rng.uniform(.1,3)
        al=rng.uniform(.5,2)
        price,kh,kl=mixed(nh,hh,al,alpha,rho,t,capital)
        nl=price*kl+rng.uniform(.01,.3)
        hl=rng.uniform(.1,3)
        # Choose productivity to make the H collateral cap strictly optimal.
        ah=max(al*1.2,1.3*t*price/(alpha*kh**(alpha-1)))
        require(demand(ah,nh,hh,alpha,rho,t,price)[1]=="capped", "P1 H regime")
        require(demand(al,nl,hl,alpha,rho,t,price)[1]=="self", "P1 L regime")
        step=min(1e-5*t,(t-rho)/100)
        p1,k1,l1=mixed(nh,hh,al,alpha,rho,t-step,capital)
        p2,k2,l2=mixed(nh,hh,al,alpha,rho,t+step,capital)
        s=1/(1-alpha)
        analytical=-s*kl*hh/(t*t*price*(kh+s*kl))
        numerical=(k2-k1)/(2*step)
        err=abs(numerical-analytical)/max(1,abs(analytical))
        max_mixed_error=max(max_mixed_error,err)
        require(err<2e-7,"P1 implicit derivative mismatch")
        close((p2-p1)/(2*step),-hh/(t*t*(kh+s*kl)),tol=2e-7)
        require(demand(al,nl,hl,alpha,rho,t-step,p1)[1]=="self", "P1 regime changed")
        require(demand(ah,nh,hh,alpha,rho,t-step,p1)[1]=="capped", "P1 regime changed")
        before=measures(ah,al,alpha,kh,kl); after=measures(ah,al,alpha,k1,l1)
        require(k1>kh and after[0]>before[0] and after[1]<before[1] and after[2]<before[2],"P1 efficiency sign")

        nl=rng.uniform(.1,2); hl=rng.uniform(.1,3)
        price,kh,kl=two_capped(nh,nl,hh,hl,t,capital)
        # Productivities keep both firms strictly collateral constrained.
        al=2*t*price/(alpha*kl**(alpha-1))
        ah=max(1.2*al,2*t*price/(alpha*kh**(alpha-1)))
        require(demand(ah,nh,hh,alpha,rho,t,price)[1]=="capped", "P2 H regime")
        require(demand(al,nl,hl,alpha,rho,t,price)[1]=="capped", "P2 L regime")
        _,ka,la=two_capped(nh,nl,hh,hl,t-step,capital)
        change=ka-kh
        finite=capital*((t-step)-t)*(nh*hl-nl*hh)/((t*(nh+nl)+hh+hl)*((t-step)*(nh+nl)+hh+hl))
        close(change,finite)
        direction=hh*nl-hl*nh
        require(change*direction>0,"P2 allocation sign")
        signs["H_gains" if direction>0 else "H_loses"]+=1
        mp_h=alpha*ah*kh**(alpha-1); mp_l=alpha*al*kl**(alpha-1)
        khstar,_=efficient(ah,al,alpha,capital)
        # Strict efficiency signs require distance from the equality boundary;
        # otherwise the O(step^2) output difference is below floating precision.
        if (kh-khstar)*(ka-khstar)>0 and min(abs(kh-khstar),abs(ka-khstar))>1e-3*capital:
            efficiency_checks += 1
            before=measures(ah,al,alpha,kh,kl); after=measures(ah,al,alpha,ka,la)
            expected=change*(mp_h-mp_l)
            require((after[0]-before[0])*expected>0,"P2 output sign")
            require((after[2]-before[2])*expected<0,"P2 MRPK-gap sign")

        # Verify the endogenously cleared banking rate, not a fixed-B derivative.
        total_h=hh+(hl if rng.random()<.5 else 0)
        equity=0; delta=rng.uniform(.2,.8); c=.02
        kappa=5*(t-rho-c)/(delta*delta*(total_h/t))
        require(kappa>0,"Invalid constructed liquidity cost")
        m=(delta*(total_h/t)-(t-rho-c)/(kappa*delta))/(1-delta)
        require(m>0,"Negative reserves")
        rate=bank_rate(m,total_h,rho,c,kappa,delta,equity)
        close(rate,t)
        b=total_h/rate; deposits=b+m-equity
        require(deposits>=0 and delta*deposits-m>0,"Invalid scarce bank regime")
        mstep=1e-5*max(m,.1)
        minus=bank_rate(m-mstep,total_h,rho,c,kappa,delta,equity)
        plus=bank_rate(m+mstep,total_h,rho,c,kappa,delta,equity)
        derivative=-kappa*delta*(1-delta)/(1+kappa*delta*delta*total_h/(rate*rate))
        err=abs((plus-minus)/(2*mstep)-derivative)/max(1,abs(derivative))
        max_bank_error=max(max_bank_error,err)
        require(err<2e-7 and plus<minus,"Bank equilibrium derivative mismatch")

    require(all(v>0 for v in regimes.values()),"A demand regime was not tested")
    # Exact finite-difference signs with rational arithmetic, including equality.
    from fractions import Fraction as F
    for nh,nl,hh,hl in [(1,2,4,1),(1,2,1,4),(1,2,2,4)]:
        t0,t1,capital=F(3),F(2),F(5)
        def share(t):
            return capital*(t*nh+hh)/(t*(nh+nl)+hh+hl)
        identity=capital*(t1-t0)*(nh*hl-nl*hh)/((t0*(nh+nl)+hh+hl)*(t1*(nh+nl)+hh+hl))
        require(share(t1)-share(t0)==identity,"Exact P2 identity failure")
        if nh*hl==nl*hh:
            signs["neutral"]+=1
    # Deliberately adverse and favorable examples: both caps and unchanged regimes.
    examples=[]
    for label,ah,al,nh,nl,hh,hl in [
        ("H_underallocated_and_gains",100,30,1,1,3,1),
        ("H_underallocated_but_loses",100,30,1,1,1,3),
        ("H_overallocated_and_gains",60,50,1,1,10,1),
        ("equal_ratios_neutral",100,30,1,2,2,4),
    ]:
        alpha=.5; rho=1; capital=2; t0=1.2; t1=1.1
        points=[]
        for t in [t0,t1]:
            price,kh,kl=two_capped(nh,nl,hh,hl,t,capital)
            require(demand(ah,nh,hh,alpha,rho,t,price)[1]=="capped","Counterexample H cap is not optimal")
            require(demand(al,nl,hl,alpha,rho,t,price)[1]=="capped","Counterexample L cap is not optimal")
            y,loss,gap=measures(ah,al,alpha,kh,kl)
            points.append((kh,y,loss,gap))
        examples.append(dict(case=label,kh_before=points[0][0],kh_after=points[1][0],
            output_before=points[0][1],output_after=points[1][1],loss_before=points[0][2],
            loss_after=points[1][2],gap_before=points[0][3],gap_after=points[1][3]))
    require(examples[0]["loss_after"]<examples[0]["loss_before"],"Positive example failed")
    require(examples[1]["loss_after"]>examples[1]["loss_before"],"Reverse-ratio counterexample failed")
    require(examples[2]["loss_after"]>examples[2]["loss_before"],"Overallocated-H counterexample failed")
    close(examples[3]["kh_after"],examples[3]["kh_before"])
    # Abundant-reserve neutrality, with c>0 to keep t>rho.
    close(bank_rate(10,1,1,.02,1,.2,0),1.02)
    close(bank_rate(20,1,1,.02,1,.2,0),1.02)
    out=HERE/"output"; out.mkdir(exist_ok=True)
    report=dict(seed=SEED,draws=DRAWS,firm_regimes=regimes,two_capped_signs=signs,
        strict_two_capped_efficiency_checks=efficiency_checks,
        max_mixed_derivative_error=max_mixed_error,max_bank_derivative_error=max_bank_error,
        exact_identity="passed",counterexamples="passed",abundant_reserve_neutrality="passed",
        limitation="Numerical verification, not a Lean proof or causal empirical evidence")
    (out/"verification.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    with (out/"allocation_cases.csv").open("w",newline="",encoding="utf-8") as f:
        writer=csv.DictWriter(f,fieldnames=list(examples[0])); writer.writeheader(); writer.writerows(examples)
    print(json.dumps(report,indent=2))


if __name__ == "__main__":
    main()
