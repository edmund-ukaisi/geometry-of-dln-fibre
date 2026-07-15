from functools import lru_cache
from itertools import product as iproduct

@lru_cache(maxsize=None)
def CRp(widths, s):
    """Return (codim, profile) where profile = list of (reduced_widths, r_chosen, E_codim) down the recursion."""
    v = tuple(widths)
    if len(v) == 2:
        v0, v1 = v
        c = 0 if s >= min(v0,v1) else (v0-s)*(v1-s)
        return c, [(v, min(v0,v1) if s>=min(v0,v1) else s, c)]
    vpm1, vp = v[-2], v[-1]
    best=None; bestprof=None
    for r in range(0, min(vpm1,vp)+1):
        outer=(vpm1-r)*(vp-r)
        if r <= s:
            inner=0; prof=[(v, r, outer)]
        else:
            inner, sub = CRp(v[:-2]+(r,), s)
            prof=[(v, r, outer)]+sub
        val=outer+inner
        if best is None or val<best:
            best=val; bestprof=prof
    return best, bestprof

# How many layers drop STRICTLY below generic rank (E_codim>0) in the minimizer?
print("=== minimizer structure: # layers with E_codim>0 (strict rank drop) ===")
from collections import Counter
cnt=Counter()
examples={}
for p in range(2,5):
  for widths in iproduct(range(1,6), repeat=p+1):
    rho=min(widths)
    for s in range(0,rho):
        c,prof=CRp(widths,s)
        ndrop=sum(1 for (_,_,ec) in prof if ec>0)
        cnt[ndrop]+=1
        if ndrop>=2 and (widths,s) and len(examples.get(ndrop,[]))<6:
            examples.setdefault(ndrop,[]).append((widths,s,c,[(w,r,ec) for (w,r,ec) in prof if ec>0]))
for nd in sorted(cnt): print(f"  {nd} layer(s) drop: {cnt[nd]} cases")
print("\n=== examples with >=2 layers dropping ===")
for nd in sorted(examples):
    for ex in examples[nd][:6]:
        print(f"  widths={ex[0]} s={ex[1]} CR={ex[2]} drops={ex[3]}")
