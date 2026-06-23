import itertools
from functools import lru_cache

# Mval, Adm, minAdm per the Lean defs (Lambda.lean).
def admBound(M, j, L):
    # j : 0..L-1 ; admBound = min(M0,M1) if j==0 else M[j+1]
    if j == 0: return min(M[0], M[1])
    return M[j+1]

def tPrev(M, T, j):
    return M[0] if j == 0 else T[j-1]

def Mval(M, T, L):
    return sum((tPrev(M,T,j) - T[j])*(M[j+1] - T[j]) for j in range(L))

def admissible(M, T, L):
    # weak decrease, last=0, block bounds
    for j in range(L):
        if T[j] > admBound(M,j,L): return False
    for i in range(L):
        for j in range(L):
            if i <= j and not (T[j] <= T[i]): return False
    # last index (j with j == L-1) must be 0
    if L >= 1 and T[L-1] != 0: return False
    return True

def minAdm(M):
    L = len(M) - 1
    if L == 0:
        return 0  # no layers
    best = None
    ranges = [range(admBound(M,j,L)+1) for j in range(L)]
    for T in itertools.product(*ranges):
        if admissible(M, list(T), L):
            v = Mval(M, list(T), L)
            if best is None or v < best: best = v
    return best

def schurStateRed(M):
    return tuple(M[s]-1 if s <= 1 else M[s] for s in range(len(M)))

def check(M):
    L = len(M)-1
    lhs = minAdm(M)
    mk = M[0]*M[1]
    n = M[len(M)-1]  # M(Fin.last L) = M[L] = output width
    child = schurStateRed(M)
    # child must have nonneg widths (schurStateRed drops front by 1)
    if any(w < 0 for w in child): 
        return ('skip-neg', M, lhs)
    rhs = min(mk, n + minAdm(child))
    return (lhs == rhs, M, lhs, mk, n, minAdm(child), rhs)

fails = []
total = 0
# L=1 (2 widths) .. L=4 (5 widths), widths 1..5 (and a few wider tails)
for L in range(1,5):
    for M in itertools.product(range(1,5), repeat=L+1):
        total += 1
        r = check(M)
        if r[0] == 'skip-neg': continue
        if r[0] is not True:
            fails.append(r)
print(f"checked {total} nodes, {len(fails)} failures")
for f in fails[:20]:
    print("FAIL", f)
# also a few wide-tail nodes explicitly
for M in [(2,2,4),(2,2,2),(3,2,3),(2,1,3),(1,1,2),(2,2,2,2),(3,3,3,3),(2,2,2,5),(4,3,2),(2,3,2,4)]:
    print(M, "->", check(M))

print("\n=== failure structure analysis ===")
le = gt = 0
gaps = {}
sample_gt = []
for L in range(1,5):
    for M in itertools.product(range(1,5), repeat=L+1):
        r = check(M)
        if r[0] == 'skip-neg': continue
        if r[0] is True: continue
        lhs, rhs = r[2], r[6]
        if lhs <= rhs: le += 1
        else:
            gt += 1
            if len(sample_gt) < 10: sample_gt.append((M, lhs, rhs))
        gaps[rhs-lhs] = gaps.get(rhs-lhs,0)+1
print(f"failures: lhs<=rhs (min OVERSHOOTS true): {le}, lhs>rhs (min UNDERSHOOTS): {gt}")
print("gap (rhs-lhs) distribution:", dict(sorted(gaps.items())))
print("lhs>rhs samples (min undershoots true minAdm — would be UNSOUND):", sample_gt[:10])

# Is the TRUE identity maybe min(mk, n + minAdm(child)) with a DIFFERENT n? 
# Try: solve for the n that makes min(mk, n + child) = lhs, i.e. what n is needed.
print("\n=== what n WOULD work? (n_needed = lhs - minAdm(child) when lhs<mk) ===")
for M in [(3,3,3,3),(2,2,2,5),(2,3,2,4),(2,2),(3,3),(1,2,1,2)]:
    L=len(M)-1
    lhs=minAdm(M); mk=M[0]*M[1]; child=schurStateRed(M); cm=minAdm(child)
    # if lhs == mk, the mk branch binds; else need n+cm=lhs => n=lhs-cm
    n_last = M[L]
    print(f"{M}: minAdm={lhs} mk={mk} child={child} minAdm(child)={cm} | n=last={n_last} gives {n_last+cm}; n_needed={lhs-cm if lhs<mk else 'mk-binds'}")

print("\n=== is n_needed always nRegOf = minAdm M - minAdm(child)? (L>=2, mk doesn't bind) ===")
allmatch = True
mismatch = []
for L in range(2,5):
    for M in itertools.product(range(1,5), repeat=L+1):
        child = schurStateRed(M)
        if any(w<0 for w in child): continue
        lhs = minAdm(M); mk=M[0]*M[1]; cm=minAdm(child)
        nReg = lhs - cm  # the additive (regularized) count
        # the identity min(mk, nReg + cm) = min(mk, lhs) = lhs iff lhs<=mk (F2). check F2:
        if lhs > mk: mismatch.append(('F2-FAIL', M, lhs, mk))
# F2 check across all L>=1
f2fail=[]
for L in range(1,5):
    for M in itertools.product(range(1,6), repeat=L+1):
        if minAdm(M) > M[0]*M[1]: f2fail.append((M, minAdm(M), M[0]*M[1]))
print("F2 (minAdm <= M0*M1) failures:", len(f2fail), f2fail[:5])
print("L>=2 F2-fails (would break the regularized min):", mismatch[:5], "count", len(mismatch))

# So with n := nRegOf (regularized), min(mk, nReg+cm)=min(mk,minAdm M)=minAdm M (by F2). 
# Confirm this REGULARIZED identity holds for ALL L>=2:
print("\n=== REGULARIZED identity minAdm M = min(M0*M1, nRegOf + minAdm(child)), L>=2 ===")
rfail=[]
for L in range(2,5):
    for M in itertools.product(range(1,6), repeat=L+1):
        child=schurStateRed(M)
        if any(w<0 for w in child): continue
        lhs=minAdm(M); mk=M[0]*M[1]; cm=minAdm(child); nReg=lhs-cm
        if min(mk, nReg+cm) != lhs: rfail.append((M,lhs,mk,nReg,cm))
print(f"regularized identity failures (L>=2): {len(rfail)}", rfail[:5])
# and L=1?
r1=[]
for M in itertools.product(range(1,6), repeat=2):
    child=schurStateRed(M)
    if any(w<0 for w in child): continue
    lhs=minAdm(M); mk=M[0]*M[1]; cm=minAdm(child); nReg=lhs-cm
    if min(mk,nReg+cm)!=lhs: r1.append((M,lhs,mk,nReg,cm))
print(f"regularized identity failures (L=1): {len(r1)}", r1[:5])
