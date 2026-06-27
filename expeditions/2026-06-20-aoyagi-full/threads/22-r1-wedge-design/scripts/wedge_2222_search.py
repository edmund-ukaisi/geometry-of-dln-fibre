import sympy as sp
import itertools
# SEARCH for a {0,1} weighting of (2,2,2,2)'s 12 coords s.t. F = (homogeneous u^2)·U exactly 
# (no u^4 term, in the limit -- actually F can have higher terms but the LEADING is u^2 AND 
# #scaled = minAdm=3 for the Jacobian to be u^{minAdm-1}=u^2).
# F = u^2·U with U bounded below requires: every product entry's MIN path-weight = 1 (so each entry 
# ~ u^1 leading), and we want exactly minAdm coords scaled... but the Jacobian power = #scaled - 1 
# ONLY if it's a clean radial blow-up of those coords. If #scaled=3, Jac u^2, but the binding axis 
# needs (1, minAdm-1)=(1,2) so h=2=#scaled-1 => #scaled=3=minAdm. ✓ consistent.
# 
# So: find weighting with #scaled = 3, every active product entry order exactly 1.
# (2,2,2,2): the achiever minAdm=3. Can 3 scaled coords make EVERY product entry ~u^1? 
# prod entry (i,k) = Σ_{a,b} C1[i,a] C2[a,b] C3[b,k]. Order = min over (a,b) of wt(C1[i,a])+wt(C2[a,b])+wt(C3[b,k]).
# For ALL 4 entries (i,k)∈{0,1}^2 to have order exactly 1 with only 3 ones total among 12 coords... 
# Each path i->a->b->k uses 3 coords. min path weight = 1 means: the BEST path has total weight 1.
# With only 3 scaled coords, and 4 output entries each needing a weight-1 best path... let me search.
M=[2,2,2,2]; L=3
coords=[]
for s in range(L):
    for i in range(M[s]):
        for j in range(M[s+1]):
            coords.append((s,i,j))
# coords: 4 (C1) + 4 (C2) + 4 (C3) = 12.
idx={c:n for n,c in enumerate(coords)}
def path_orders(wt):
    # for each (i,k), min over (a,b) of wt[C1 i a]+wt[C2 a b]+wt[C3 b k]
    orders={}
    for i in range(2):
        for k in range(2):
            mn=99
            for a in range(2):
                for b in range(2):
                    w=wt[idx[(0,i,a)]]+wt[idx[(1,a,b)]]+wt[idx[(2,b,k)]]
                    mn=min(mn,w)
            orders[(i,k)]=mn
    return orders
found=[]
for ones in itertools.combinations(range(12),3):
    wt=[1 if n in ones else 0 for n in range(12)]
    o=path_orders(wt)
    if all(v==1 for v in o.values()):
        found.append(ones)
print(f"(2,2,2,2): #weightings with 3 scaled coords & all 4 entries order-1: {len(found)}")
if found:
    ones=found[0]
    print("  example scaled coords:", [coords[n] for n in ones])
else:
    print("  NONE. A single 3-coord {0,1} weighting CANNOT make all entries order-1.")
    # try allowing more scaled coords but Jacobian-correct via weighted (non-{0,1}) weights:
    print("  => the clean single-weighted-blowup FAILS for (2,2,2,2). Chain/gauge needed.")
