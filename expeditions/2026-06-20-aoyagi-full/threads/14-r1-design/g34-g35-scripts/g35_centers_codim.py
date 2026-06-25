import sympy as sp
import numpy as np
from itertools import product
# DIRECT EXACT TEST of "every blow-up center has full codim = an admissible Mval >= min_Adm Mval".
# The flag-resolution of {prod=0} blows up centers = nested-rank loci. The set of centers it visits,
# along ALL branches, is exactly {S(t) : t admissible}. I verify by COMPUTING the codim of each
# rank-locus directly (as a determinantal variety) and confirming it equals Mval(t), and that the
# resolution only ever blows up these (never a lower-codim non-admissible locus).
#
# codim of {A1 A2 = 0, rank(A1) <= t1} type loci. For L=2, the centers are indexed by t1 = the rank
# bound. The relevant determinantal codims:
def Mval(M,t):
    tt=[M[0]]+list(t); L=len(M)-1
    return sum((tt[j-1]-tt[j])*(M[j]-tt[j]) for j in range(1,L+1))

# For (3,3,3): the stratum S(t1,0) = {rank(A1)=t1, rank(A1 A2)=0} (i.e. A1 A2=0, rank A1=t1).
# Its codim in the 18-dim space. Compute NUMERICALLY via the rank of the Jacobian of the defining
# equations at a generic stratum point (codim = Jacobian rank of the local defining ideal).
np.random.seed(3)
def stratum_codim(t1, M=(3,3,3), trials=5):
    m=M[0]
    codims=[]
    for _ in range(trials):
        # generic point of S(t1,0): A1 rank t1, A2 with cols in ker(A1) (so A1 A2=0)
        U=np.random.randn(m,t1); V=np.random.randn(t1,m); A1 = U@V if t1>0 else np.zeros((m,m))
        if t1<m:
            ns = np.linalg.svd(A1)[2][t1:].T  # ker basis m x (m-t1)
            A2 = ns @ np.random.randn(m-t1, m)
        else:
            A2 = np.zeros((m,m))
        # defining equations of {A1 A2 = 0}: the m*m entries of A1 A2. Jacobian wrt all 18 vars.
        # The stratum is a COMPONENT; its codim = rank of the Jacobian of {entries of A1A2} restricted
        # to the component's tangent... Actually codim of {A1A2=0} component through this point =
        # rank of d(A1 A2) at the point (the generators' Jacobian rank).
        a=sp.symbols('a0:9'); b=sp.symbols('b0:9')
        A1s=sp.Matrix(3,3,a); A2s=sp.Matrix(3,3,b); P=A1s*A2s
        gens=[P[i,j] for i in range(3) for j in range(3)]
        allv=list(a)+list(b)
        sub={**{a[i]:float(A1.flat[i]) for i in range(9)}, **{b[i]:float(A2.flat[i]) for i in range(9)}}
        J=np.array(sp.Matrix([[float(sp.diff(g,v).subs(sub)) for v in allv] for g in gens]),dtype=float)
        codims.append(np.linalg.matrix_rank(J,tol=1e-7))
    return codims

print("=== (3,3,3): codim of stratum S(t1,0) (Jacobian rank of A1A2 generators at generic pt) vs Mval ===")
for t1 in range(4):
    cods = stratum_codim(t1)
    print(f"  S({t1},0): generator-Jac-rank (codim of {{A1A2=0}} at this pt) = {cods}, Mval({t1},0) = {Mval((3,3,3),(t1,0))}")
print()
print("The Jacobian rank = codim of the smooth locus of {A1A2=0} at a rank-t1 point. Compare to Mval.")
print("If they MATCH for the achievers (t1=1,2 -> 7), the centers are codim-7 (admissible) -> ratio 7/2.")
