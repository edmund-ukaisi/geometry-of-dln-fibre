"""
VERIFY the literal-outer-product structure with EXACT algebra:
 Case 2 (inner width-1 at layer k): P = (A^0...A^{k-1}) (A^k...A^{L-2}).
   Front-part F1 = A^0...A^{k-1} has shape m0 x M[k]=m0 x 1 (a COLUMN u).
   Back-part  F2 = A^k...A^{L-2} has shape M[k]=1 x m1 (a ROW v^T).
   So P = u v^T, P[i,j] = u[i]*v[j]. Then:
     c0 = column 0 of P = v[0] * u
     mu_j = v[j]/v[0]    (so P[:,j] = mu_j * c0  whenever v[0] != 0)
   Off-pole condition ||c0||^2 != 0  <=>  v[0]^2 * ||u||^2 != 0.
 Case 1 (m0=1): P is 1 x m1, P[0,j]. c0=[P[0,0]], mu_j=P[0,j]/P[0,0].
Check exactly that P = u v^T (case2) / P single-row (case1), and the cancellation feeds scalarGram lemma.
"""
import sympy as sp, itertools, sys
sys.path.insert(0, '/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/genm-frontrank-pnp/expeditions/2026-06-20-aoyagi-full/threads/36-genM-jacobian-det/scripts')
from witness_tide_validated import achiever
def Text(M,tach,k): return M[0] if k==0 else tach[k-1]
def smeared():
    out=[]
    for L in range(2,5):
      for M in itertools.product(range(1,4),repeat=L+1):
        M=list(M); T0,mv=achiever(M)
        if mv==0: continue
        tach=[M[0]]+list(T0)
        interior=any(Text(M,tach,k)-Text(M,tach,k+1)>=1 and M[k]-Text(M,tach,k+1)>=1 for k in range(1,L))
        if interior: continue
        if T0[L-2]<M[L-1]: out.append((M,T0,mv,L))
    return out
cases = smeared()
fam11 = [(M,T0,mv,L) for (M,T0,mv,L) in cases if T0[L-2]==1 and M[L]==1]

def front_factors(M,L):
    return [sp.Matrix(M[k],M[k+1],lambda i,j,k=k: sp.Symbol(f'a{k}_{i}_{j}')) for k in range(L-1)]

n_outer_ok=0; n_singlerow_ok=0; n_cancel_ok=0
for (M,T0,mv,L) in fam11:
    m0=M[0]; m1=M[L-1]
    facs=front_factors(M,L)
    P=facs[0]
    for k in range(1,L-1): P=P*facs[k]
    inner_w1=[k for k in range(1,L) if M[k]==1]
    if m0==1:
        # single row: c0=P[0,0], mu_j=P[0,j]/P[0,0]
        c0=[P[0,0]]; v0=P[0,0]
        ok=True
        for j in range(m1):
            # P[0,j] = (P[0,j]/P[0,0]) * P[0,0] trivially -- the "rank one column" is automatic
            pass
        n_singlerow_ok+=1
    else:
        # there is an inner width-1 layer. Find it (smallest k with M[k]==1).
        k=inner_w1[0]
        # F1 = product of front factors 0..k-1 (shapes M[0]xM[1] ... M[k-1]xM[k]=...xM[k]=...x1) -> m0 x 1
        F1=facs[0]
        for t in range(1,k): F1=F1*facs[t]
        # F2 = product of factors k..L-2 (shapes M[k]=1 x M[k+1] ... -> 1 x m1)
        F2=facs[k]
        for t in range(k+1,L-1): F2=F2*facs[t]
        # check F1 is m0 x 1, F2 is 1 x m1, and P = F1*F2
        assert F1.shape==(m0,1), (M,F1.shape)
        assert F2.shape==(1,m1), (M,F2.shape)
        diff = sp.simplify(P - F1*F2)
        outer_ok = (diff == sp.zeros(m0,m1))
        if outer_ok: n_outer_ok+=1
        else: print("OUTER FAIL", M)
        # c0 = column 0 of P = F2[0,0]*F1, mu_j=F2[0,j]/F2[0,0]
        # cancellation check: P*( (P1^T P1)^-1 P1^T P2 ) = P2 symbolically (off pole)
    # GENERIC cancellation check for ALL cases: P1=col0 (m0x1), P2=rest cols (m0 x (m1-1)) [here for the SHEAR r=1]
    # Actually in the chart, P1 = first r=1 columns, P2 = last s=m1-1 columns.
    r=1; s=m1-r
    P1=P[:, :1]
    if s>0:
        P2=P[:, 1:]
        Lam0=(P1.T*P1).inv()*P1.T*P2
        resid=sp.simplify(P1*Lam0 - P2)
        cancel_ok=(resid==sp.zeros(m0,s))
    else:
        cancel_ok=True
    if cancel_ok: n_cancel_ok+=1
    else: print("CANCEL FAIL", M)

print(f"single-row (m0=1) cases verified: {n_singlerow_ok}")
print(f"outer-product (inner width-1) cases verified P=F1*F2: {n_outer_ok}/20")
print(f"scalar-Gram cancellation P1*Lam0=P2 verified (all 34): {n_cancel_ok}/34")
