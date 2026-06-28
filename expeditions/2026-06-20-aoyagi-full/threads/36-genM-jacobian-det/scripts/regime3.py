import sys; sys.path.insert(0,'.')
import pp_smear_GATE as G
from collections import Counter
cases = G.smeared()
regime=Counter(); rcs=Counter(); rc=Counter(); minadms=Counter()
for M,T0,mv,L in cases:
    r=T0[L-2]; c=M[L]; m1=M[L-1]; s=m1-r; minAdm=r*c
    regime['minAdm=1' if minAdm==1 else 'minAdm>=2']+=1
    rcs[(r,c,s)]+=1; rc[(r,c)]+=1; minadms[minAdm]+=1
print("total:", len(cases))
print("regime:", dict(regime))
print("minAdm distribution:", dict(sorted(minadms.items())))
print("(r,c) shapes:", dict(sorted(rc.items())))
print("(r,c,s):", dict(sorted(rcs.items())))
print("r>1 (no explicit r×r inverse):", sum(v for (r,c),v in rc.items() if r>1))
print("c>1 (multi-col radial):", sum(v for (r,c),v in rc.items() if c>1))
print("r=1,c=1 (scalar, (1,2,1)-like):", rc.get((1,1),0))
# print a few examples per shape
seen={}
for M,T0,mv,L in cases:
    r=T0[L-2]; c=M[L]; key=(r,c)
    if key not in seen: seen[key]=[]
    if len(seen[key])<3: seen[key].append(M)
print("examples per (r,c):", seen)
