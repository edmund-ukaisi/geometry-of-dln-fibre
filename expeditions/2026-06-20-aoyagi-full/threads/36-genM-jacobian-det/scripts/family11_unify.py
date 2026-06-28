"""
UNIFICATION test: does P ALWAYS factor as a literal outer product u v^T (u: m0 x 1, v: 1 x m1)
through a SINGLE Fin-1 inner dimension, across ALL 34 cases?
For Case 1 (m0=1): u = column vector [P[0,0],...]? No -- m0=1 means u is 1x1.
  P = u v^T with u=1x1=[1] (or [P[0,0]]) and v^T = P (1 x m1). Works trivially (u=identity).
For Case 2: factor at the inner width-1 layer.
The CLEANEST uniform statement for Lean: P = U * V where U : Fin m0 x Fin 1, V : Fin 1 x Fin m1.
  This is EXACTLY the matrix-product associativity through a Fin 1 inner dim.
Question: is there ALWAYS a SPLIT POINT k* in {0,1,...,L-1} where the running width is 1?
  running widths: M[0], M[1], ..., M[L-1] (the bottleneck path). min=1 at some position p*.
  Split P = (A^0...A^{p*-1}) * (A^{p*}...A^{L-2}):
    left  = m0 x M[p*]=m0 x 1   (if p*>=1)  OR  identity (if p*=0, then left=1x1? no, m0 x m0 but m0=1)
    right = M[p*]=1 x m1
Let me verify: for EVERY case, splitting at the FIRST position p* where M[p*]==1 gives P = left * right
with left having 1 column and right having 1 row.
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

n_unify=0
pstar_dist={}
for (M,T0,mv,L) in fam11:
    m0=M[0]; m1=M[L-1]
    # running widths along the front path: M[0..L-1]. find first p* with M[p*]==1.
    path=[M[k] for k in range(0,L)]   # M[0],...,M[L-1]
    pstar=path.index(1)               # first position with width 1
    pstar_dist[(L,pstar, 'p*=0(m0=1)' if pstar==0 else 'inner' )]=pstar_dist.get((L,pstar,'p*=0(m0=1)' if pstar==0 else 'inner'),0)+1
    facs=[sp.Matrix(M[k],M[k+1],lambda i,j,k=k: sp.Symbol(f'a{k}_{i}_{j}')) for k in range(L-1)]
    P=facs[0]
    for k in range(1,L-1): P=P*facs[k]
    # left = A^0...A^{pstar-1} : m0 x M[pstar]=m0 x 1; right=A^{pstar}...A^{L-2}: 1 x m1
    if pstar==0:
        left=sp.eye(m0)   # = m0 x m0 = 1x1 (m0=1)
        right=P
    else:
        left=facs[0]
        for t in range(1,pstar): left=left*facs[t]
        right=facs[pstar]
        for t in range(pstar+1,L-1): right=right*facs[t]
    # shapes
    Lshape=left.shape; Rshape=right.shape
    diff=sp.simplify(P-left*right)
    ok=(diff==sp.zeros(m0,m1)) and Lshape[1]==1 and Rshape[0]==1
    if ok: n_unify+=1
    else: print("UNIFY FAIL", M, "L=",Lshape,"R=",Rshape)

print(f"UNIFIED outer-product P=left*right thru Fin 1 (split at first width-1 pos): {n_unify}/34")
print("\np* distribution (L, p*, type):")
for k,v in sorted(pstar_dist.items()): print(f"  {k}: {v}")
