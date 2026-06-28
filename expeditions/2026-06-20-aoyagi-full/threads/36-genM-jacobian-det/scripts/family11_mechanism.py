"""
Pin the front-bottleneck -> rank-one mechanism for the (r,c)=(1,1) family (34 M).
For each (1,1)-family M:
  - r = T0[L-2], c = M[L], m1 = M[L-1]
  - front widths along the path A^0 A^1 ... A^{L-2}: M[0], M[1], ..., M[L-1]
  - "front-bottleneck" = min of those widths
  - LOCATE the width-1 layer (the index where the front path attains its min)
  - Build P = A^0 A^1 ... A^{L-2} symbolically; check:
      (a) every column of P is a scalar multiple of column 0 (rank-one COLUMNS)
      (b) extract c0 (= column 0) and mu (per-column scalars) in terms of front coords
  - Mechanism test: is the rank-one-columns property because P FACTORS THROUGH a Fin-1 inner dim
    (a LITERAL outer product P = u v^T), i.e. there is a width-1 layer in the chain?
"""
import sympy as sp, itertools, os, sys
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
print(f"(1,1) family: {len(fam11)} cases")
print(f"  L-distribution: L=2:{sum(1 for c in fam11 if c[3]==2)} L=3:{sum(1 for c in fam11 if c[3]==3)} L=4:{sum(1 for c in fam11 if c[3]==4)}")
print()

allpass=True
loc_dist={}
for (M,T0,mv,L) in fam11:
    r=T0[L-2]; c=M[L]; m1=M[L-1]
    # front widths along P = A^0 ... A^{L-2}: dims M[0] x M[1], M[1] x M[2], ..., M[L-2] x M[L-1]
    # inner dims traversed: M[1], M[2], ..., M[L-1] (the "intermediate" widths); also M[0] is the row count
    front_widths = [M[k] for k in range(0, L)]   # M[0..L-1]
    bottleneck = min(front_widths)
    # location of the min in the inner dims M[1..L-1] (the layer whose OUTPUT width is 1)
    inner = [M[k] for k in range(1, L)]   # M[1..L-1], these are the inner contracted dims
    min_inner = min(inner) if inner else None
    # build P symbolically (L-1 front factors: A^0,...,A^{L-2})
    facs=[sp.Matrix(M[k],M[k+1],lambda i,j,k=k: sp.Symbol(f'a{k}_{i}_{j}')) for k in range(L-1)]
    P=facs[0]
    for k in range(1,L-1): P=P*facs[k]
    # P is M[0] x M[L-1] = m0 x m1
    m0=M[0]
    # rank-one COLUMNS test: every column proportional to column 0
    col0 = P[:, 0]
    rankone_cols = True
    mus = []  # per-column scalar (symbolic), column j = mu_j * col0
    for j in range(m1):
        colj = P[:, j]
        # check colj = lam * col0 as rational functions: cross products colj[i]*col0[i'] == colj[i']*col0[i]
        ok=True
        for i1 in range(m0):
            for i2 in range(m0):
                if sp.simplify(colj[i1]*col0[i2] - colj[i2]*col0[i1]) != 0:
                    ok=False
        rankone_cols = rankone_cols and ok
    # locate width-1 layer: is there a k in 1..L-1 with M[k]==1?  (the inner bottleneck = 1)
    width1_inner = [k for k in range(1,L) if M[k]==1]
    rankP = P.rank()
    loc = (tuple(M), tuple(front_widths), bottleneck, width1_inner, rankP, rankone_cols)
    key = (L, bottleneck, tuple(sorted(set(width1_inner))))
    loc_dist[key]=loc_dist.get(key,0)+1
    status = "OK" if (bottleneck==r and rankone_cols and rankP<=r) else "FAIL"
    if status=="FAIL":
        allpass=False
        print(f"  {status} M={M} L={L} front_w={front_widths} bottleneck={bottleneck} r={r} w1_inner={width1_inner} rankP={rankP} rankone_cols={rankone_cols}")

print(f"\nALL PASS: {allpass}")
print("\nLocation distribution (L, bottleneck, width-1-inner-layers):")
for k,v in sorted(loc_dist.items()):
    print(f"  {k}: {v}")
