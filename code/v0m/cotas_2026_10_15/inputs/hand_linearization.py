"""Audited coefficient stencil, parsed as AST with interval parameters; not a standalone solver."""
def coefficients(phi_pi=1.5,phi_y=.125,rR=.8,rM=.5,phiP=60.):
    n=16
    eye=np.eye(n)
    logell=(eye[10]-eye[9]+alpha*eye[:2])/(1-beta)
    logy=(beta*eye[10]-beta*eye[9]+alpha*eye[:2])/(1-beta)
    logprofit=(eye[10]-beta*eye[9]+alpha*eye[:2])/(1-beta)
    logu=(eye[10]-beta*eye[9]-gap*eye[:2])/(1-beta)
    logK=(mass*k/K)@eye[:2]
    logY=(mass*yy/Y)@logy
    logL=(mass*ell/L)@logell
    logRR=rR*eye[4]+(1-rR)*(phi_pi*eye[11]+phi_y*logY)
    logM=rM*eye[5]
    vp=1/(2*math.sqrt(1.5)*(1+math.sqrt(1.5))**2)
    cbp=Delta*aa/2*(vv+(1+tight)*vp)
    cdp=Delta*aa*((1-tight)*vp-vv)
    jR=1+rd*zeta*cdiff/(2*rr*rr)
    jD=1+zeta*cdiff/(2*rr)
    jT=(1-rho)*cbp-(xi-rho)*zeta*cdp/2
    dh=xi*zeta*(1-tight)/(1+tight)*(eye[13]-logRR)-2*zeta*(xi-rho)*tight/(1+tight)**2*eye[15]
    rows0=[]; rows1=[]
    def row(current,next_):
        rows0.append(current);rows1.append(next_)
    for i in range(2):
        cur=cc[i]*eye[6+i]+delta*q*k[i]*eye[12]+b[i]*eye[14]-profit[i]*logprofit[i]+F[i]*eye[2]-(1-pledge[i])*ad*q*k[i]*eye[i]-F[i]*eye[11]
        nxt=p[i]*k[i]*eye[i]-b[i]*eye[2]
        row(cur,nxt)
    for i in range(2):
        cur=q*eye[12]+b[i]/k[i]*eye[14]-p[i]*sigmaE*eye[6+i]
        nxt=-b[i]/k[i]*eye[2]+p[i]*sigmaE*eye[6+i]-be*uc[i]*logu[i]-be*(1-pledge[i])*ad*q*eye[12]
        row(cur,nxt)
    row(np.zeros(n),eye[2]-eye[11]-eye[12])
    row(-eye[3]-eye[14]+eye[11],eye[3])
    row(q*eye[12]+phiI*logK,-phiI*logK)
    row(CW*eye[8]+sum(mass[i]*cc[i]*eye[6+i] for i in range(2))-K*(q*ad+phiI*delta*delta/2)*logK-Y*logY,q*K*logK)
    row(eye[9]-varphi*logL-sigmaW*eye[8],np.zeros(n))
    row(eye[13]+sigmaW*eye[8],-eye[11]-sigmaW*eye[8])
    row(eps*mc*eye[10]-phiP*eye[11],bw*phiP*eye[11])
    row(-logRR,eye[4])
    row(-logM,eye[5])
    row(rate*eye[14]-rr*logRR-cbp*tight*eye[15],np.zeros(n))
    row(jR*rr*logRR-jD*rd*eye[13]+jT*tight*eye[15],np.zeros(n))
    row(-B*eye[14]-E*(eye[3]-eye[11])-(D-M)*logM+D/h*dh,B*((mass*b/B)@eye[:2]+eye[2]))
    C0,C1=np.array(rows0),np.array(rows1)
    assert C0.shape==(16,16)
    return C0,C1,dict(cbp=cbp,cdp=cdp,jR=jR,jD=jD,jT=jT,ellR=(1-cbp*jR/jT)*rr/rate,ellD=cbp*jD/jT*rd/rate)
