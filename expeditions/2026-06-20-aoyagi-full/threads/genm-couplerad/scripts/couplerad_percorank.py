# a=b=1 charge exponent per cell + per singular value: is the charge INERT (gamma=0) except at the
# deepest leaf s=0? And at s=0 which corank/measure absorbs gamma=a*e1? Exact.
from fractions import Fraction as Fr
import itertools
def beta(p,k): return [(p-k+1)+2*(k-i) for i in range(1,k+1)]
def gamma_at(e,a,b,s):
    k=len(e); lo=max(0,b-s); hi=min(b,k); best=None
    for h in range(lo,hi+1):
        v=a*sum(e[:h]) - h*(s-b+h)
        if best is None or v>best: best=v
    return best if best is not None else 0
def loss_num_and_gamma(u,rho,k,p,a,b):
    # at the CHARGED LP optimum vertex: report N_loss, gamma, N_charged, D, and the binding ray e
    s=rho-k; bt=beta(p,k); P=u*(rho-k); half=Fr(1,2); best=None; arg=None
    for assign in itertools.product([0,1],repeat=k):
        e=[half if x==0 else Fr(0) for x in assign]; g=[Fr(0) if x==0 else half for x in assign]
        if any(e[i]>e[i+1] for i in range(k-1)): continue
        f=half; D=min([2*f]+[2*(e[i]+g[i]) for i in range(k)])
        if D<=0: continue
        gc=gamma_at(e,a,b,s)
        Nl=sum(e[i]*bt[i] for i in range(k))+P*f+u*sum(g)
        val=2*(Nl-gc)/D
        if best is None or val<best: best=val; arg=(list(e),list(g),Nl,gc,D)
    return best,arg
print("a=b=1: per-cell charge exponent gamma at the CHARGED-LP binding vertex (is it 0 except s=0?)")
for (M,u) in [((4,4,4,4),3),((5,5,5,5),4),((3,3,4,4),2),((3,4,5,4),2)]:  # last is a=1,b=2 (not a=b=1) for contrast
    a=M[0]-u; b=M[1]-u; rho=min(M[2:]); n=M[-1]; exc=abs(M[2]-n)
    print(f"\n M={M} u={u} a={a} b={b} rho={rho} exc={exc}")
    for k in range(1,rho+1):
        s=rho-k; p=k+exc
        C,arg=loss_num_and_gamma(u,rho,k,p,a,b)
        e,g,Nl,gc,D=arg
        print(f"   k={k} s={s}: binding e={e} g={g}  N_loss={Nl} gamma={gc} N_charged={Nl-gc} 2N/D={C}  charge-inert(gamma==0)={gc==0}")
