# Refined: GENUINE off-sector shells only (a>=1 AND b>=1 -- nonempty corank block).
# Question: within GOOD (non-waist) chains, does hcvg hold at every genuine non-empty shell?
from functools import lru_cache
from itertools import product

def sub(x, y): return x - y if x > y else 0
@lru_cache(maxsize=None)
def minAdm(M):
    M = tuple(M)
    if len(M) == 1: return 0
    if len(M) == 2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))
def redChain(u, M): return (u,) + tuple(M[2:])
def bindingCut(M):
    best = minAdm(M)
    for u in range(min(M[0],M[1])+1):
        if (M[0]-u)*(M[1]-u)+minAdm(redChain(u,M))==best: return u
def tailMinWidth(M): return min(M[1:])
def deepTailMin(M): return min(M[2:])

RANGES = [(range(1,8),3), (range(1,7),4), (range(1,6),5)]

# Cross-tabulate over GENUINE non-empty shells (a>=1,b>=1,hrange). Count (hcvg,hpiv) cells.
from collections import Counter
cells = Counter()
witness_hpiv_true_hcvg_false = []   # THE decisive class: good shell where cover breaks
seen=set()
for rng,length in RANGES:
    for M in product(rng,repeat=length):
        if M in seen: continue
        seen.add(M)
        M0,M1,M2,Mlast=M[0],M[1],M[2],M[-1]
        tstar=bindingCut(M)
        if tstar<1: continue                # cover needs ht1: 1<=t*
        r=min(sub(M0,tstar),sub(M1,tstar))
        Lam=min(M1,Mlast)
        for j in range(0,r+1):
            u=tstar+j; a=sub(M0,u); b=sub(M1,u)
            if a<1 or b<1: continue          # GENUINE corner only
            m=sub(Lam,j); hrange=(m<=M2)
            if not hrange: continue          # non-empty only
            hcvg=(a+b<=m)
            hpiv=(minAdm(redChain(u,M))<=u*tailMinWidth(M))
            cells[(hcvg,hpiv)]+=1
            if hpiv and not hcvg:
                witness_hpiv_true_hcvg_false.append((M,tstar,j,u,a,b,m,deepTailMin(M),M1))

print("Cross-tab over GENUINE non-empty shells (hcvg, hpiv) -> count:")
for (hc,hp),n in sorted(cells.items()):
    print(f"   hcvg={hc!s:5} hpiv={hp!s:5} : {n}")
print()
print(f"DECISIVE class hpiv=True & hcvg=False (cover breaks in good case): {len(witness_hpiv_true_hcvg_false)}")
for w in witness_hpiv_true_hcvg_false[:20]:
    M,tstar,j,u,a,b,m,dtm,M1=w
    print(f"   M={M} t*={tstar} j={j} u={u} a={a} b={b} m={m} a+b={a+b} | deepTailMin={dtm} M1={M1} nonwaist(dtm<=M1)={dtm<=M1}")
print()
# Also: among the decisive class, how many also satisfy the brief's deepTailMin<=M1 gate?
both = [w for w in witness_hpiv_true_hcvg_false if w[7]<=w[8]]
print(f"   of those, ALSO deepTailMin<=M1 (brief's good gate): {len(both)}")
for w in both[:20]:
    M,tstar,j,u,a,b,m,dtm,M1=w
    print(f"     M={M} t*={tstar} j={j} u={u} a={a} b={b} m={m} a+b={a+b} deepTailMin={dtm}<=M1={M1}")
