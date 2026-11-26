#!/usr/bin/env python3
"""Isolated 33-D algebraic regression; not a SOURCE economics certificate."""
import math

N=33
PERM=[(7*i)%N for i in range(N)]
assert sorted(PERM)==list(range(N))
B=[1.0+0.03*i for i in range(N)]
A=[0.012*(i+1) for i in range(N)]

def psi(z):
    return [B[i]*math.exp(z[i]) for i in range(N)]

def source(x):
    return [x[i]-B[i]+0.006*(x[(i+1)%N]-B[(i+1)%N]) for i in range(N)]

def df_dz(z):
    x=psi(z)
    d=[[0.0]*N for _ in range(N)]
    for i in range(N):
        d[i][i]+=x[i]
        d[i][(i+1)%N]+=0.006*x[(i+1)%N]
    return d

def T(z):
    d=[1.1+0.002*i+0.03*z[i] for i in range(N)]
    m=[[0.0]*N for _ in range(N)]
    for i in range(N): m[i][i]=d[i]
    m[19][21]+=A[19]*(1+z[4]);m[20][21]+=A[20]*(1-z[5])
    return m

def dt_f(z, f):
    out=[[0.0]*N for _ in range(N)]
    for i in range(N): out[i][i]+=0.03*f[i]
    out[19][4]+=A[19]*f[21];out[20][5]-=A[20]*f[21]
    return out

def t_times(m,f):
    return [sum(m[i][j]*f[j] for j in range(N)) for i in range(N)]

def result(z):
    f=source(psi(z)); y=t_times(T(z),f)
    return [y[PERM[i]] for i in range(N)]

def analytical_jac(z, drop_product=False):
    f=source(psi(z)); m=T(z); d=df_dz(z)
    prod=dt_f(z,f)
    jac=[[sum(m[i][k]*d[k][j] for k in range(N)) + (0 if drop_product else prod[i][j]) for j in range(N)] for i in range(N)]
    return [jac[PERM[i]] for i in range(N)]

def run():
    max_error=0.0; omission=0.0
    for trial in range(3):
        z=[0.0]*N if trial==0 else [0.025*math.sin((i+2)*(trial+1)*0.6) for i in range(N)]
        expected=analytical_jac(z); missing=analytical_jac(z,True)
        for j in range(N):
            h=1e-6; zp=z.copy(); zm=z.copy();zp[j]+=h;zm[j]-=h
            fp=result(zp); fm=result(zm)
            for i in range(N):
                numeric=(fp[i]-fm[i])/(2*h)
                max_error=max(max_error,abs(numeric-expected[i][j]))
                if trial>0: omission=max(omission,abs(numeric-missing[i][j]))
        if trial==0:
            assert max(abs(v) for v in result(z))<1e-12
            assert max(abs(expected[i][j]-missing[i][j]) for i in range(N) for j in range(N))<1e-12
    assert max_error<1e-7, max_error
    assert omission>1e-5, omission
    print(f'PASS: 33x33 permutation/coordinate/row-chain test; error={max_error:.3g}; omitted-product witness={omission:.3g}')
    print('Synthetic mathematical regression only; SOURCE/Python economic functional equality NOT verified.')

if __name__=='__main__':run()
