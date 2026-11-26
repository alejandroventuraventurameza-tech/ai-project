#!/usr/bin/env python3
"""Outward rational interval certificate for SOURCE (NUMERICO, not Lean).

Only integers and Fraction are used; fractional powers are enclosed using
integer nth-root comparisons. The formulas independently transcribe the
source's stationary bank, real scale, boundary firm, root, and initial state.
A successful test verifies *these transcribed formulas*, not kernel-level
identification with the original Lean terms or equilibrium existence.
"""
from fractions import Fraction
from math import gcd
import json

S = 10**42

def ceil(a, b): return -((-a)//b)

class V:
    def __init__(self, lo, hi):
        assert lo <= hi
        self.lo, self.hi = lo, hi
    @staticmethod
    def of(a):
        if isinstance(a, V): return a
        x = Fraction(a)
        return V(x.numerator*S//x.denominator,ceil(x.numerator*S,x.denominator))
    @staticmethod
    def rat(a,b=1): return V.of(Fraction(a,b))
    def __neg__(self): return V(-self.hi,-self.lo)
    def __add__(self,y):
        y=V.of(y); return V(self.lo+y.lo,self.hi+y.hi)
    __radd__=__add__
    def __sub__(self,y): return self+-V.of(y)
    def __rsub__(self,y): return V.of(y)+-self
    def __mul__(self,y):
        y=V.of(y)
        v=[a*b for a in (self.lo,self.hi) for b in (y.lo,y.hi)]
        return V(min(v)//S,ceil(max(v),S))
    __rmul__=__mul__
    def __truediv__(self,y):
        y=V.of(y)
        assert y.lo>0 or y.hi<0, 'division by interval containing zero'
        v=[Fraction(a*S,b) for a in (self.lo,self.hi) for b in (y.lo,y.hi)]
        return V(min(x.numerator//x.denominator for x in v),
                 max(ceil(x.numerator,x.denominator) for x in v))
    def __rtruediv__(self,y): return V.of(y)/self
    def __pow__(self,n):
        assert isinstance(n,int) and n>=0
        if not n:return Q(1)
        if self.lo>=0:return V(self.lo**n//S**(n-1),ceil(self.hi**n,S**(n-1)))
        if self.hi<=0:return -((-self)**n) if n%2 else (-self)**n
        if n%2:return V(self.lo**n//S**(n-1),ceil(self.hi**n,S**(n-1)))
        return V(0,ceil(max(-self.lo,self.hi)**n,S**(n-1)))
    @staticmethod
    def root_floor(x,p,q):
        assert x>=0 and p>0 and q>0
        if not x:return 0
        target=x**p*S**max(q-p,0)
        factor=S**max(p-q,0)
        def ok(y):return y**q*factor<=target
        hi=1
        while ok(hi): hi*=2
        lo=hi//2
        while hi-lo>1:
            mid=(hi+lo)//2
            if ok(mid):lo=mid
            else:hi=mid
        return lo
    def rp(self,p,q=1):
        assert self.lo>=0 and q>0
        if not p:return Q(1)
        if p<0:return Q(1)/self.rp(-p,q)
        z=gcd(p,q);p//=z;q//=z
        lo=self.root_floor(self.lo,p,q)
        hi=self.root_floor(self.hi,p,q)
        exact=(hi**q*S**max(p-q,0)==self.hi**p*S**max(q-p,0))
        return V(lo,hi if exact else hi+1)
    def fmt(self,n=24):
        def dec(a,round_up):
            a=(ceil(a*10**n,S) if round_up else a*10**n//S)
            sign='-' if a<0 else ''
            whole,frac=divmod(abs(a),10**n)
            return f'{sign}{whole}.{frac:0{n}d}'
        return [dec(self.lo,False),dec(self.hi,True)]

def Q(a,b=1):return V.rat(a,b)
def avg(v):return sum(v,Q(0))/len(v)

# Source stationary bank, real economy, government-independent initial faces
weight=1/(1+Q(3,2).rp(1,2));m=(2+3*weight)/400; slope=(2+weight)/200
RD=Q(100,99); A=RD-Q(9,10)*m-slope/100
RR=(A+(A**2+Q(2,5)*RD*slope).rp(1,2))/2;RL=RR+m
rho=Q(1,10)+(RD/RR-Q(1,10))/15
theta=[Q(3,20),Q(2,5)];tech=[Q(101,100),Q(1)];P=Q(81,80)
J=Q(39,40)*P
user=[P*((1-v*Q(39,40)/RL)/Q(24,25)-Q(39,40)*(1-v)) for v in theta]
profc=[(Q(5,6)*v)**2/4 for v in tech];cs=[(Q(4,5)*profc[i]/user[i])**5 for i in range(2)]
Ys=avg([3*user[i]*cs[i] for i in range(2)]);Ls=avg([Q(5,4)*user[i]*cs[i] for i in range(2)])
Bs=avg([theta[i]*J*cs[i]/RL for i in range(2)])
CWs=Q(7,12)*Ys+avg(cs)/6400+(RL-1)*Bs;W=(Ls*CWs).rp(1,12)
Kfirm=[v/W**5 for v in cs];Yfirm=[3*user[i]*Kfirm[i] for i in range(2)]
face=[theta[i]*J*Kfirm[i] for i in range(2)];loan=[v/RL for v in face]
Cfirm=[Q(5,12)*Yfirm[i]-Q(1,40)*P*Kfirm[i]-(RL-1)*loan[i] for i in range(2)]
K,Y,B=avg(Kfirm),avg(Yfirm),avg(loan);CW=Y-avg(Cfirm)-Q(161,6400)*K
E=B/(3-2*rho);D=2*E;M=2*rho*E;F=(RD/RR-Q(1,10))*D/30
Mpost=M+F;RF=RR+Q(1,50);aB=1/RL
parent_gap=RD*D-avg(face)-RR*Mpost+RF*F+E/aB

def candidate(R):
    Vcont=[v+J for v in user];P0=Vcont[1]/R
    effective=[P0-theta[i]*J/R for i in range(2)]
    parent_effective=[P-theta[i]*J/RL for i in range(2)]
    C0=[Cfirm[0]*effective[0]/parent_effective[0],Cfirm[1]/(Q(24,25)*R)]
    scale=1/(Q(39,40)+(P0-1)/Q(1,2));K0=[scale*k for k in Kfirm]
    rr0=R-m; term=slope/10
    rd0=(rr0+Q(9,10)*m+Q(1,10)*term)/(1+term/rr0)
    cw0=CW/(Q(99,100)*rd0)
    w0=W*((cw0/CW)*scale.rp(4,5)).rp(1,3)
    labor0=[(Q(1,2)*Q(5,6)*tech[i]*K0[i].rp(2,5)/w0)**2 for i in range(2)]
    output0=[tech[i]*K0[i].rp(2,5)*labor0[i].rp(1,2) for i in range(2)]
    profit0=[Q(5,6)*output0[i]-w0*labor0[i] for i in range(2)]
    inherited=[profit0[i]+Q(39,40)*P0*K0[i]-C0[i]-effective[i]*Kfirm[i] for i in range(2)]
    invest=K-Q(39,40)*scale*K
    gamma=invest+Q(1,2)*invest**2/(2*scale*K)
    residual=avg(output0)-cw0-avg(C0)-gamma
    bankFace=E*RL/R
    gap=RD*D-avg(inherited)-RR*Mpost+RF*F+bankFace/aB
    decomp=avg([face[i]-inherited[i] for i in range(2)])+(bankFace-E)/aB
    assert not (gap.lo>decomp.hi or decomp.lo>gap.hi)
    return residual,gap

if __name__=='__main__':
    assert parent_gap.lo<=0<=parent_gap.hi
    left=Q(1029135,1000000);right=Q(1029136,1000000)
    rleft,_=candidate(left);rright,_=candidate(right)
    assert rleft.hi<0 and 0<rright.lo
    rbin=V(left.lo,right.hi)
    _,gap=candidate(rbin)
    assert gap.lo>0 and gap.lo>Q(8,100).hi and gap.hi<Q(9,100).lo
    print(json.dumps({
       'kind':'EXACT_INTEGER_OUTWARD_INTERVALS_NOT_LEAN',
       'source_root_bracket':['1029135/1000000','1029136/1000000'],
       'resource_at_lower':rleft.fmt(),
       'resource_at_upper':rright.fmt(),
       'inherited_gap_over_entire_bracket':gap.fmt(),
       'stationary_parent_gap':parent_gap.fmt(),
       'certified_arithmetic':'Integer directed rounding at precision 10^42; all positive-root bounds checked by integer-power comparisons',
       'scope':'Independent transcription audit only; Lean identity/endpoint proofs remain pending.'
       },indent=2))
