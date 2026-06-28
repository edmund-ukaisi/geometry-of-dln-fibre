import sys; sys.path.insert(0,'.')
import pp_smear_GATE as G
cases = G.smeared()
from collections import Counter
def Text(M,tach,k): return M[0] if k==0 else tach[k-1]
shapes = Counter(); regime = Counter(); rcs = Counter()
for M,T0,mv,L in cases:
    r = Text(M,T0,L)        # deepRank
    m1 = M[L-1]             # deepRows
    c = M[L]
    s = m1 - r
    minAdm = r*c
    regime['minAdm=1' if minAdm==1 else 'minAdm>=2'] += 1
    rcs[(r,c,s)] += 1
    shapes[(r,c)] += 1
print("total smeared:", len(cases))
print("regime split:", dict(regime))
print("(r,c,s) shapes:", dict(sorted(rcs.items())))
print("(r,c) shapes:", dict(sorted(shapes.items())))
# c>1 cases (radial block is r x c, multi-column) -- harder than my validate-smalls (both c=1)
cgt1 = sum(v for (r,c),v in shapes.items() if c>1)
rgt1 = sum(v for (r,c),v in shapes.items() if r>1)
print("cases with c>1 (multi-col radial):", cgt1)
print("cases with r>1 (r x r Gram, no explicit inverse):", rgt1)
print("cases with r=1 AND c=1 (scalar, like (1,2,1)):", shapes.get((1,1),0))
