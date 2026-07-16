import itertools
from functools import lru_cache

@lru_cache(maxsize=None)
def minAdm(M):
    M=tuple(M); n=len(M)
    if n==1: return 0
    if n==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdm((t,)+M[2:]) for t in range(0,min(M[0],M[1])+1))

# (1) zero-leading chain minAdm(0, ...) == 0
zfail=0
for arity in (2,3,4,5):
    for tail in itertools.product(range(0,7), repeat=arity-1):
        if minAdm((0,)+tail)!=0: zfail+=1
print(f"minAdm(0, ...) == 0 fails: {zfail}")

# (2) F2 widen: minAdm(redChain s M) <= s*M2, arity 3..6, widths 0..7
f2fail=[]
for arity in (3,4,5,6):
    for M in itertools.product(range(0,8), repeat=arity):
        M2=M[2]
        for s in range(0,min(M[0],M[1])+1):
            red=(s,)+M[2:]
            if minAdm(red) > s*M2: f2fail.append((M,s,minAdm(red),s*M2))
print(f"F2 minAdm(redChain s M) <= s*M2  fails (arity 3..6, w 0..7): {len(f2fail)}")
for x in f2fail[:6]: print("   ",x)

# (3) TIGHT gate == banked minAdm_le_peelCharge_add_redChain at s:
#     minAdm(M) <= (M0-s)(M1-s) + minAdm(redChain s M),  s <= min(M0,M1).   (must be 0 fails)
# (4) the recursion min is ACHIEVED (exists binding t): minAdm(M)= min_t[...]  -> equality at some t.
tfail=0; achieved_fail=0
for arity in (3,4,5,6):
    for M in itertools.product(range(0,8), repeat=arity):
        mm=minAdm(M); M0,M1=M[0],M[1]; mb=min(M0,M1)
        terms=[(M0-t)*(M1-t)+minAdm((t,)+M[2:]) for t in range(0,mb+1)]
        for s in range(0,mb+1):
            if mm > (M0-s)*(M1-s)+minAdm((s,)+M[2:]): tfail+=1
        if min(terms)!=mm: achieved_fail+=1
print(f"TIGHT gate (=banked at s) fails: {tfail}")
print(f"recursion-min achieved fails: {achieved_fail}")

# (5) Is s*M2 vs minAdm(redChain s M): report a rich L=1 example where the deep binds strictly.
print("\nEXAMPLE L=1 chains where minAdm(redChain s M) < s*M2 (deep binds, tight<naive):")
cnt=0
for M in itertools.product(range(2,6), repeat=4):
    M2=M[2]
    for s in range(1,min(M[0],M[1])+1):
        red=(s,)+M[2:]; d=minAdm(red)
        if d < s*M2:
            print(f"   M={M}, s={s}: minAdm(redChain s M)={d} < s*M2={s*M2}   (naive slack {s*M2-d})")
            cnt+=1
            if cnt>=8: break
    if cnt>=8: break

# (6) The full LHS min (tight) equals minAdm(M)-ab over feasible s in [0,u]? Check min over s in[0,u] of tight terms
#     minus ab equals... just confirm min_{s in [0,u]} [(M0-s)(M1-s)+minAdm(redChain s M)] >= minAdm(M).
subfail=0
for arity in (3,4,5):
    for M in itertools.product(range(1,7), repeat=arity):
        mm=minAdm(M); M0,M1=M[0],M[1]; mb=min(M0,M1)
        for u in range(0,mb+1):
            sub=min([(M0-s)*(M1-s)+minAdm((s,)+M[2:]) for s in range(0,u+1)])
            if sub < mm: subfail+=1
print(f"\nmin_(s in [0,u]) tight-term >= minAdm(M) fails: {subfail}")
