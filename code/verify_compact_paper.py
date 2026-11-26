#!/usr/bin/env python3
"""Eight-result compact paper: scoped algebra/source checks, not Lean proofs."""
from __future__ import annotations

import cmath
from fractions import Fraction as Q
import hashlib
import json
import math
from pathlib import Path
import random
import re

ROOT = Path(__file__).resolve().parent.parent
EXPECTED = {
    "prop:local_macro_multiplicity",
    "prop:compact_exact_tail_power",
    "lem:compact_robust_tail_power",
    "prop:compact_source_collateral_effective_wedge",
    "lem:repayment",
    "lem:v0m_original_6_2",
    "prop:v0m_original_6_3",
    "lem:allocation_loss_identity",
}

def require(condition, message):
    if not condition:
        raise AssertionError(message)

def verify_source():
    parts = [ROOT/"paper"/f for f in (
        "paper.tex", "body_compact_intro.tex", "body_compact_after.tex",
        "appendix_eight_results.tex")]
    src = "\n".join(p.read_text(encoding="utf-8") for p in parts)
    found = re.findall(
        r"\\begin\{(?:lemma|proposition)\}(?:\[[^]]+\])?\s*\\label\{([^}]+)\}",
        src)
    require(len(found) == 8 and set(found) == EXPECTED,
            f"Paper no longer contains the eight expected results: {found}")
    require(src.count(r"\begin{proof}") == src.count(r"\end{proof}") == 8,
            "Eight complete proof environments required")
    labels = re.findall(r"\\label\{([^}]+)\}", src)
    require(len(labels) == len(set(labels)), "Duplicate source labels")
    refs = re.findall(r"\\(?:ref|eqref|autoref|cref)\{([^}]+)\}", src)
    require(set(refs) <= set(labels),
            f"Unresolved cross-refs: {set(refs)-set(labels)}")
    bib = (ROOT/"paper/references.bib").read_text(encoding="utf-8")
    keys = set(re.findall(r"@\w+\s*\{\s*([^,\s]+)", bib))
    cites = set(key.strip() for group in re.findall(
        r"\\cite(?:t|p|alt|alp|author|year)?\{([^}]+)\}", src)
        for key in group.split(","))
    require(cites <= keys, f"Missing references: {cites-keys}")
    historic = ROOT/"paper/historical/paper_full_20261118.tex"
    ledger = json.loads((ROOT/"paper/result_ledger.json").read_text(encoding="utf-8"))
    digest = hashlib.sha256(historic.read_bytes()).hexdigest()
    require(digest == ledger["paper_sha256"] and ledger["numbered_results"] == 57,
            "Archived original does not match 57-result ledger")
    return {"compact_results": 8, "historical_results": 57,
            "historic_source_sha256": digest, "cited_keys": len(cites)}

def verify_finance_and_scalar():
    rng = random.Random(20261125)
    for _ in range(80):
        a,b = -Q(rng.randint(1,8)), -Q(rng.randint(1,8))
        h = -Q(rng.randint(1,15),1000)
        m = lambda s,shock: b*s + a*shock
        root = -a*h/b
        require(root>0 and m(Q(0),h)>0 and m(root,h)==0 and m(Q(0),-h)<0,
                "Linear local-complementarity stress check failed")
        rl = Q(rng.randint(110,190),100)
        rd = rl-Q(1,10)
        pi = Q(rng.randint(90,120),100)
        theta = Q(rng.randint(1,90),100)
        delta = Q(rng.randint(0,30),100)
        qnext = Q(rng.randint(110,200),100)
        k = Q(rng.randint(1,200),25)
        op = Q(rng.randint(0,50),100)
        deposits = Q(rng.randint(0,100),100)
        bound = theta*(1-delta)*pi*qnext*k/rl
        debt = bound*Q(rng.randint(0,100),100)
        N = op + (1-delta)*qnext*k - rl*debt/pi + rd*deposits/pi
        Nlower = op+(1-theta)*(1-delta)*qnext*k+rd*deposits/pi
        require(N>=Nlower>=0, "Repayment inequality violated")
        sdf = Q(rng.randint(1,100),100)
        mu = Q(rng.randint(0,100),100)
        require(sdf*(rl-rd)/pi+mu*rl>0,
                "No-simultaneous-saving/borrowing KKT contradiction failed")
        n,q,H,R = Q(3),Q(2),Q(1),Q(2)
        denom=q-H/R
        kmax=n/denom
        loan=H*kmax/R
        require(q*kmax==n+loan and R*loan==H*kmax,
                "Financing-capacity equality failed")
        require(-n*H/(R*R*denom*denom)<0,
                "Financing-capacity derivative must be negative")
        thetaH,thetaL=Q(1,5),Q(3,5)
        J=(1-delta)*pi*qnext
        price=Q(3)
        pH=price-thetaH*J/rl
        pL=price-thetaL*J/rl
        require(pH-pL==(thetaL-thetaH)*J/rl>0,
                "Effective financial-wedge identity failed")

def verify_allocation():
    rng=random.Random(20261125)
    alpha,beta=.3,.4
    d=1-alpha-beta
    for _ in range(80):
        ah,al=rng.uniform(.6,2.4),rng.uniform(.6,2.4)
        mh,ml=rng.uniform(.5,1.8),rng.uniform(.5,1.8)
        kh,kl=rng.uniform(.5,3),rng.uniform(.5,3)
        labor=rng.uniform(.8,4)
        def loss(h,l):
            K=mh*h+ml*l
            gh=ah**(1/(1-beta))*h**(alpha/(1-beta))
            gl=al**(1/(1-beta))*l**(alpha/(1-beta))
            G=mh*gh+ml*gl
            Z=mh*ah**(1/d)+ml*al**(1/d)
            Y=labor**beta*G**(1-beta)
            Yef=K**alpha*labor**beta*Z**d
            return cmath.log(Yef/Y),mh*gh/G,mh*h/K
        L,shareY,shareK=loss(kh,kl)
        require(L.real>=-1e-11,"Efficient benchmark below observed product")
        step=1e-20
        observed=loss(kh*cmath.exp(1j*step),kl)[0].imag/step
        predicted=alpha*(shareK-shareY)
        require(abs(observed-predicted)<1e-9,
                "Allocation-loss log differential mismatch")
        gh=ah**(1/(1-beta))*kh**(alpha/(1-beta))
        gl=al**(1/(1-beta))*kl**(alpha/(1-beta))
        lh=labor*gh/(mh*gh+ml*gl)
        ll=labor*gl/(mh*gh+ml*gl)
        yh=ah*kh**alpha*lh**beta
        yl=al*kl**alpha*ll**beta
        require((shareY>shareK)==(yh/kh>yl/kl),
                "Output-share and MPK ordering disagree")

def verify_exact_matrix_certificate():
    report=ROOT/"code/irf/output/exact_linear_tail_power_certificate.json"
    require(report.is_file(),
            "Run code/verify.py: exact 48-step matrix output missing")
    d=json.loads(report.read_text(encoding="utf-8"))
    require(d["status"]=="EXACT_RATIONAL_LINEAR_GRAPH_POWER_CERTIFICATE"
            and d["block_power"]==48
            and d["robust_strict_48_step_bound"]=="49/50",
            "Unexpected exact matrix certificate")
    input_file=ROOT/"code/irf/inputs/rational_preconditioners.json"
    require(d["source_sha256"]==hashlib.sha256(input_file.read_bytes()).hexdigest(),
            "Matrix certificate input SHA drift")

def main():
    source=verify_source()
    verify_finance_and_scalar()
    verify_allocation()
    verify_exact_matrix_certificate()
    result={
        "status":"passed_eight_result_scoped_checks_not_a_lean_proof",
        "source":source,
        "finance_and_scalar_cases":80,
        "allocation_cases":80,
        "limits":[
            "Examples and identities do not establish competitive equilibrium",
            "Historical 57-result checks use a distinct pinned source",
            "Full literal Lean correspondence remains to be demonstrated",
        ],
    }
    out=ROOT/"code/output/compact_paper_verification.json"
    out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(result,indent=2))

if __name__=="__main__":
    main()
