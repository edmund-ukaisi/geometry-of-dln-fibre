"""
Cross-layer (uniform-per-layer) hierarchical ray for a MULTI-LAYER deep product:
  layer i (matrix X_i, dims w_{i-1} x w_i) degenerates as tau^{c_i}, uniform within the layer.
  loss = ||X_1...X_L||^2 ~ tau^{2 sum c_i}.  measure exponent sum_i (w_{i-1} w_i) c_i.
  ray codim = 2 * [sum_i (w_{i-1} w_i) c_i] / [2 sum_i c_i] = weighted avg of layer dims >= min_i(w_{i-1}w_i).
Claim: min_i(w_{i-1} w_i) >= minAdm(chain)  (single-layer collapse gives product=0, codim = that layer's dim).
So cross-layer scale differences (incl. "one layer t, another t^2") NEVER bind below minAdm; the binding
directions are the RANK-SPLIT (reduced-rank) ones, captured exactly by minAdm.
"""
import itertools
from functools import lru_cache

@lru_cache(maxsize=None)
def minAdm(M):
    M=tuple(M)
    if len(M)==2: return M[0]*M[1]
    m0,m1=M[0],M[1]; rest=M[2:]
    return min((m0-t)*(m1-t)+minAdm((t,)+rest) for t in range(0,min(m0,m1)+1))

def crosslayer_min_codim(chain):
    # min over uniform-per-layer rays = min_i(w_{i-1} w_i)  (put all scale weight on cheapest layer)
    dims=[chain[i]*chain[i+1] for i in range(len(chain)-1)]
    return min(dims)

# verify min_i(layer dim) >= minAdm(chain), and specific "t vs t^2" example
bad=0; ncase=0
for L in range(2,5):
    for chain in itertools.product(range(1,7),repeat=L+1):
        ncase+=1
        cl=crosslayer_min_codim(chain)
        mA=minAdm(chain)
        if cl < mA: bad+=1
print(f"chains tested={ncase};  min_i(layer dim) < minAdm  (cross-layer ray below floor): {bad}")

# concrete "one layer as t, another as t^2" for a specific deep chain (u prepended)
def ray_codim_uniform(chain, cs):
    dims=[chain[i]*chain[i+1] for i in range(len(chain)-1)]
    num=sum(d*c for d,c in zip(dims,cs)); den=sum(cs)
    return 2*num/(2*den)   # = weighted avg of dims

examples=[((2,2,2,2),[1,1,2]),   # F~t, A2~t, A3~t^2  (u=2, deep=(2,2,2))
          ((3,4,4,4),[1,2,1]),   # A2~t^2 the middle
          ((2,3,2,3),[1,2,3])]   # escalating scales
for chain,cs in examples:
    mA=minAdm(chain)
    rc=ray_codim_uniform(chain,cs)
    print(f" chain(u,deep)={chain} ray scales c={cs}: cross-layer ray codim={rc:.2f}  >= minAdm={mA}? {rc>=mA-1e-9}")
