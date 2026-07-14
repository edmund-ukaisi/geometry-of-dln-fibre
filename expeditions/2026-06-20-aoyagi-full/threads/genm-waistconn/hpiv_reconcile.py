from functools import lru_cache
from itertools import product
@lru_cache(maxsize=None)
def minadm(M):
    L1=len(M)
    if L1==1: return 0
    if L1==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minadm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))
def redchain(u,M): return (u,)+M[2:]
def tailminwidth(M): return min(M[1:])            # min(M1,...,Mlast)
def bindingcut(M):                                 # smallest t* achieving minAdm (Nat.find)
    best=minadm(M)
    for t in range(min(M[0],M[1])+1):
        if (M[0]-t)*(M[1]-t)+minadm(redchain(t,M))==best: return t
    raise
def hpiv(u,M): return minadm(redchain(u,M)) <= u*tailminwidth(M)
def is_waist(M): return M[1] < min(M[2:])

# (1) EQUIVALENCE: NOT hpiv(bindingCut) <=> M1 < min(M2,...,Mlast)
bad1=[]; nbc0=0
for nw in range(3,7):
  for M in product(range(1,6),repeat=nw):
    bc=bindingcut(M)
    lhs = not hpiv(bc,M)                # hpiv FAILS at binding cut
    rhs = is_waist(M)                   # M1 < min(M2,...,Mlast)
    if lhs!=rhs: bad1.append((M,bc,minadm(redchain(bc,M)),bc*tailminwidth(M),is_waist(M)))
    if bc==0: nbc0+=1
print("(1) ¬hpiv(bindingCut) ⟺ M₁<min(M₂..M_last):",
      "OK all" if not bad1 else "FAIL "+str(len(bad1))+" eg "+str(bad1[:8]))
print("    (binding cut =0 count, sanity:",nbc0,")")

# (2) PER-CUT COHERENCE: non-waist (M1>=min(M2..)) => hpiv(u) for ALL u in [1,min(M0,M1)]
#     equivalently hpiv(bindingCut) <=> hpiv(u) for all per-cut u.
bad2=[]; bad2b=[]
for nw in range(3,7):
  for M in product(range(1,6),repeat=nw):
    us=range(1,min(M[0],M[1])+1)
    allpercut = all(hpiv(u,M) for u in us) if list(us) else True
    nonwaist = not is_waist(M)
    if nonwaist and not allpercut: bad2.append((M,[u for u in us if not hpiv(u,M)]))
    # coherence: hpiv(bc) <=> all per-cut hpiv
    if hpiv(bindingcut(M),M) != allpercut: bad2b.append((M,bindingcut(M)))
print("(2) non-waist ⟹ hpiv(u) ∀u∈[1,min(M₀,M₁)]:",
      "OK all" if not bad2 else "FAIL "+str(len(bad2))+" eg "+str(bad2[:8]))
print("    hpiv(bindingCut) ⟺ hpiv(u)∀u (per-cut coherence, NO gap):",
      "OK all" if not bad2b else "FAIL "+str(len(bad2b))+" eg "+str(bad2b[:8]))

print("\n=== CORRECTED (per-cut, u>=1) equivalence + waist direction ===")
# (1') EXISTS u in [1,min(M0,M1)] : NOT hpiv(u)   <=>   M1 < min(M2,...,Mlast)
bad1p=[]
for nw in range(3,7):
  for M in product(range(1,7),repeat=nw):
    us=[u for u in range(1,min(M[0],M[1])+1)]
    exists_fail = any(not hpiv(u,M) for u in us)
    if exists_fail != is_waist(M): bad1p.append((M,us,is_waist(M),[u for u in us if not hpiv(u,M)]))
print("(1') (∃u≥1 ¬hpiv(u)) ⟺ M₁<min(M₂..):", "OK all" if not bad1p else "FAIL "+str(len(bad1p))+" eg "+str(bad1p[:6]))

# waist ⟹ ∃ failing u≥1  (does every waist have a real failing peel?)
bad_wd=[]
for nw in range(3,7):
  for M in product(range(1,7),repeat=nw):
    if is_waist(M):
      us=[u for u in range(1,min(M[0],M[1])+1)]
      if not any(not hpiv(u,M) for u in us): bad_wd.append((M,us))
print("    waist ⟹ ∃u≥1 failing:", "OK all" if not bad_wd else "FAIL(waist with NO failing peel!) "+str(len(bad_wd))+" eg "+str(bad_wd[:10]))

# does a waist ever have NO real peel (min(M0,M1)=0 impossible since widths>=1; but bindingcut can still be >=1)?
# characterize the bc=0 waist cases: are they exactly M0=1 or M1 s.t. peel-to-0 is optimal?
bc0waist=[M for nw in range(3,6) for M in product(range(1,6),repeat=nw) if is_waist(M) and bindingcut(M)==0]
print("    waist chains with bindingCut=0 (degenerate, why binding-cut framing fails):", len(bc0waist), "eg", bc0waist[:6])
# for these, is there still a failing per-cut u>=1?
print("    ... all of THOSE still have a failing per-cut u>=1:",
      all(any(not hpiv(u,M) for u in range(1,min(M[0],M[1])+1)) for M in bc0waist))
