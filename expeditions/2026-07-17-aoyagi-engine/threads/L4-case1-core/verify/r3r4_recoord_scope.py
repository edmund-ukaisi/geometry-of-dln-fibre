"""Does restricting ed2's recoord sum to the REMAINING block (i >= cleared) dissolve the u001^2?
The u001^2 = ed2's recoord reading readEntry(0,i=0,1)=u001, where row 0 is ed1's ALREADY-CLEARED row.
If the recoord should only compensate the REMAINING-block column clear (rows i >= cleared), it must NOT
sum i=0. Test both scopes."""
import sympy as sp
def make(d):
    N=len(d)-1; return N,{(L,r,c):sp.Symbol(f"u{L}{r}{c}") for L in range(N) for r in range(d[L+1]) for c in range(d[L])}
def rd(u,d,S,row,col):
    N=len(d)-1; return u[(S,row,col)] if (0<=S<N and 0<=row<d[S+1] and 0<=col<d[S]) else sp.Integer(0)
def shear(u,d,sL,sC,piv,sign,remaining_only):
    a,b=piv[1],piv[2]; w=dict(u)
    for (L,r,c) in u:
        if L==sL and sC<=r and sC<=c:
            if r!=a and c!=b: w[(L,r,c)]=u[(L,r,c)]-rd(u,d,sL,r,b)*rd(u,d,sL,a,c)
            elif (r,c)!=(a,b): w[(L,r,c)]=sp.Integer(0)   # R4 clear own pivot row/col (r,c >= cleared)
        elif L==sL+1 and c==a:
            lo = sC if remaining_only else 0               # <-- the scope knob
            w[(L,r,c)]=u[(L,r,c)]+sign*sum((rd(u,d,sL,i,b)*rd(u,d,sL+1,r,i) for i in range(lo,d[sL+1]) if i!=c),sp.Integer(0))
    return w
def ae(u,d,case,sL,sC,piv,cen,delta,sign,ro):
    w=dict(u) if case in ("case11","rollover") else shear(u,d,sL,sC,piv,sign,ro)
    out={}
    for k in u:
        if case=="rollover": out[k]=w[k]
        elif delta==1: out[k]=sp.Integer(1) if k==piv else w[k]
        else: out[k]=(w[piv] if k==piv else (w[piv]*w[k] if k in cen else w[k]))
    return out
def core(u,d):
    N=len(d)-1; P=sp.Matrix(d[N],d[N-1],lambda r,c:u[(N-1,r,c)])
    for L in range(N-2,-1,-1): P=P*sp.Matrix(d[L+1],d[L],lambda r,c:u[(L,r,c)])
    return [sp.expand(P[i,j]) for i in range(P.rows) for j in range(P.cols)]
def fold(d,edges,sign,ro):
    N,u=make(d); v=dict(u)
    for e in reversed(edges): v=ae(v,d,*e,sign,ro)
    return core(v,d),u
def md(f,x): return 0 if x not in f.free_symbols else sp.Poly(sp.expand(f),x).degree()
for d,br in [((2,2,2,2),[("case2",0,0,(0,0,0),set(),1),("case2",0,1,(0,1,1),{(0,1,1)},0),("rollover",0,2,None,set(),0)]),
             ((2,3,2,2),[("case2",0,0,(0,0,0),set(),1),("case2",0,1,(0,1,1),{(0,1,1),(0,2,1)},0),("rollover",0,2,None,set(),0)])]:
    print(f"d={d}")
    for ro,lbl in [(False,"recoord sums ALL i≠a (current formula)"),(True,"recoord sums only i≥cleared (remaining block)")]:
        ents,u=fold(d,br,-1,ro); u001=u[(0,0,1)]
        m=max(md(f,u001) for f in ents)
        print(f"   {lbl}: max deg_u001 = {m}"+("  <-- u001^2" if m>=2 else "  <-- CLEAN (deg ≤1)"))
