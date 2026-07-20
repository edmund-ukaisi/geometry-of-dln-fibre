import sympy as sp, sys
BATT = "/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/root/expeditions/2026-07-17-aoyagi-engine/threads/24-alpha-cover/battery"
sys.path.insert(0, BATT)
from rg_shape import init_params, layer_mat, spine, beta_blowup, alpha_Lg, alpha_Rg_crosslayer
def wmin(M,n): return min(M[:n+1])
def node_completed(P,M,S,c):
    P,_=alpha_Lg(P,M,S,c); P,_=alpha_Rg_crosslayer(P,M,S,c); P,_=beta_blowup(P,M,S,c); return P
def iszero(x):
    n,_=sp.fraction(sp.together(x)); return sp.expand(n)==0
def prod_layers(P,M,upto):
    Pr=layer_mat(P,M,0)
    for s in range(1,upto+1): Pr=Pr*layer_mat(P,M,s)
    return Pr
def classify(Mtx,m0):
    out=[]
    for i in range(m0):
        nz=[j for j in range(Mtx.shape[1]) if not iszero(Mtx[i,j])]
        out.append('ZERO' if not nz else ('DIAG' if nz==[i] else 'RESID'))
    return out
def resolvedRows(M,layer,cleared,L): return wmin(M,L) if layer==L else cleared
def dropThreshold(M,layer,cleared): return wmin(M,layer+1) if wmin(M,layer+1)<=cleared else wmin(M,layer)
def run(M):
    L=len(M)-1; m0=M[0]; P=init_params(M); states=[]
    def snap(layer,cleared):
        upto=min(layer,L-1); Pr=prod_layers(P,M,upto); return (layer,cleared,classify(Pr,m0))
    states.append(snap(0,0))
    for S in range(L):
        cap=wmin(M,S+1)
        for J in range(1,cap+1):
            P=node_completed(P,M,S,J-1); states.append(snap(S,J))
        states.append(snap(S+1 if S+1<L else L,0))
    ok=True
    print(f"M={tuple(M)} widthMinUpto={[wmin(M,n) for n in range(len(M))]}")
    for (layer,cleared,cls) in states:
        rr=resolvedRows(M,layer,cleared,L); dt=dropThreshold(M,layer,cleared)
        cs={i for i in range(m0) if i<rr}; ds={i for i in range(m0) if i>=dt}
        diag={i for i in range(m0) if cls[i]=='DIAG'}; zero={i for i in range(m0) if cls[i]=='ZERO'}
        c_ok=cs<=diag; d_ok=ds<=zero; ok=ok and c_ok and d_ok
        fl="" if (c_ok and d_ok) else "  <<< VIOLATION"
        print(f"  ({layer},{cleared}) {cls} cleared(i<{rr})={sorted(cs)}=>DIAG:{c_ok} dropped(i>={dt})={sorted(ds)}=>ZERO:{d_ok}{fl}")
    Prf=prod_layers(P,M,L-1)
    isd=all(iszero(Prf[i,j]) for i in range(m0) for j in range(Prf.shape[1]) if i!=j)
    print(f"  leaf diagonal(offdiag all 0)? {isd}   InvVal3 all states? {ok}\n")
    return ok,isd
import sys as _s
tgt=_s.argv[1] if len(_s.argv)>1 else "334"
run([3,3,4] if tgt=="334" else [4,3,4])
