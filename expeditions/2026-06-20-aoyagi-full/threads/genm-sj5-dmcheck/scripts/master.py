"""
D/m >= n0 collapse hunt — master combinatorial sweep.

Structure (all from the banked certs, RE-VERIFIED here independently):
  Chain M = (M0, M1, ..., ML), L+1 nodes, L layers A_0..A_{L-1}.
  Front block A0 = M0 x M1.  Deeper product P = A1 A2 ... A_{L-1}, dims M1 x ML.
  Generic rank r = min(M1,...,ML).
  Cell by corank q of P: rho = r - q surviving rank, q = 0..r.
    d_q = M0 * rho          (front charge on rho surviving directions)
    D_q = cCodim(P; rho)    (PRODUCT-rank tube codim = codim{rank P <= rho})
  Per-cell RLCT threshold = 1/2 (D_q + d_q).
  Collapse-free  <=>  min_q (D_q + d_q) = minAdm(M)   [front-peel/QIP linchpin]
  The db2 single-branch "full value iff D/m >= n0":  D/m = cCodim(binding tube),
    n0 = ab at the binding config.  We check cCodim vs ab explicitly and diagnose.
"""
from functools import lru_cache
import itertools

@lru_cache(None)
def minAdm(M):
    M = tuple(M)
    if len(M) <= 1: return 0
    if len(M) == 2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t) + minAdm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))

@lru_cache(None)
def cCodim(c, rho):
    """codim{ rank(product of chain c) <= rho } via partial-product-rank profile enumeration.
       c = (n0,...,nk), product n0 x nk. rho = allowed final rank."""
    c = tuple(c); L = len(c)-1
    if L == 0: return 0
    if L == 1:
        r = min(rho, c[0], c[1]); return (c[0]-r)*(c[1]-r)
    best = None
    rng = range(0, max(c)+1)
    for T in itertools.product(rng, repeat=L):   # T = ranks of partial products A0, A0A1, ...
        if any(T[i] < T[i+1] for i in range(L-1)): continue    # weakly decreasing
        if T[0] > min(c[0], c[1]): continue
        if T[-1] > rho: continue                                # final rank <= rho
        if not all(T[j] <= min(T[j-1], c[j+1]) for j in range(1, L)): continue
        val = (c[0]-T[0])*(c[1]-T[0]) + sum((T[j-1]-T[j])*(c[j+1]-T[j]) for j in range(1, L))
        if best is None or val < best: best = val
    return best if best is not None else 0

def analyze(M):
    M = tuple(M)
    ma = minAdm(M)
    deeper = M[1:]                       # chain of P = A1...A_{L-1}
    r = min(deeper) if len(deeper) >= 1 else 0   # generic rank of P
    M0 = M[0]
    cells = []
    for q in range(0, r+1):
        rho = r - q
        Dq = cCodim(deeper, rho)
        dq = M0 * rho
        cells.append((q, rho, Dq, dq, Dq+dq))
    thr = [c[4] for c in cells]
    minthr = min(thr) if thr else None
    binding_qs = [c for c in cells if c[4] == minthr]
    return dict(M=M, minAdm=ma, r=r, cells=cells, minthr=minthr,
                linchpin_ok=(minthr == ma), binding=binding_qs)

# ---- sweep ----
sweep = [
    # anchor + flagged bottleneck chains from the brief
    (3,3,3,4),
    (3,5,2,5), (2,4,2,5), (2,4,4,5), (2,5,2,2,5),
    # corank-2/3 stressers, various L
    (4,4,4,4), (5,5,5,5), (2,5,5,5), (5,5,5,2),
    (3,3,3,3,4), (4,4,4,4,4), (2,4,4,4,5),
    (3,3,2,2), (4,3,3,4), (2,4,3,5), (3,4,5,4,3),
    (5,2,5), (5,2,2,5), (6,2,6), (7,2,2,2,7),
    (2,6,2,6,2), (3,6,3), (4,2,4,2,4),
]

print("="*100)
print("LINCHPIN + COLLAPSE SWEEP:  min_q(D_q+d_q) == minAdm ?   (top-level front-peel, geometric cCodim)")
print("="*100)
allok = True
for M in sweep:
    a = analyze(M)
    allok = allok and a['linchpin_ok']
    bstr = ",".join(f"q={c[0]}(rho={c[1]},D={c[2]},d={c[3]},thr={c[4]})" for c in a['binding'])
    flag = "" if a['linchpin_ok'] else "   <<< LINCHPIN FAIL (collapse!)"
    print(f"M={str(M):16} minAdm={a['minAdm']:3} r={a['r']} | min_thr={a['minthr']:3} ok={a['linchpin_ok']} | binding: {bstr}{flag}")
print(f"\nALL linchpins hold (min_q(D_q+d_q)==minAdm): {allok}")
