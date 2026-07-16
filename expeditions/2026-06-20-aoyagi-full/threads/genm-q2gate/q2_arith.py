from functools import lru_cache
from fractions import Fraction as F

# minAdmRec (exact, certified equal to minAdm in Lean via minAdmRec_succ_succ / leaf)
# M is a tuple of widths (length = arity = L+1). redChain t M = (t, M[2], M[3], ...).
def redChain(t, M):
    return (t,) + M[2:]

@lru_cache(maxsize=None)
def minAdm(M):
    L1 = len(M)  # number of widths
    if L1 == 1:
        return 0
    if L1 == 2:
        return M[0]*M[1]
    # >=3 widths
    best = None
    for t in range(0, min(M[0], M[1]) + 1):
        v = (M[0]-t)*(M[1]-t) + minAdm(redChain(t, M))
        best = v if best is None else min(best, v)
    return best

def peelCharge(M, u):
    return (M[0]-u)*(M[1]-u)

def nondeg_cut_exists(M):
    # 1<=t, t+1<=min(M0,M1), minAdm M = peelCharge M t + minAdm(redChain t M), 0<minAdm(redChain t M)
    cuts=[]
    for t in range(1, min(M[0],M[1])):  # t+1<=min => t<=min-1
        if t+1 <= min(M[0],M[1]):
            rc = redChain(t, M)
            if minAdm(M) == peelCharge(M,t) + minAdm(rc) and minAdm(rc) > 0:
                cuts.append(t)
    return cuts

def saturated_params(M):
    # saturated shell u = min(M0,M1); a=M0-u, b=M1-u
    u = min(M[0], M[1])
    a = M[0]-u
    b = M[1]-u
    M2 = M[2]
    # density order A = max_{1<=j<=min(u,M2)} j*(M2 - b - j), clamp negative to 0 via max with 0
    cands = [0]
    for j in range(1, min(u, M2)+1):
        cands.append(j*(M2 - b - j))
    A = max(cands)
    rc = redChain(u, M)  # (u, M2, ...)
    twoDelta = minAdm(rc) - minAdm(M)
    return dict(u=u,a=a,b=b,A=A,minAdm_M=minAdm(M),minAdm_rc=minAdm(rc),
               twoDelta=twoDelta, needed_thr=F(minAdm(M),2), rc=rc,
               fold_reaches=F(minAdm(M),2) - (F(A,2) - F(twoDelta,2)))

print("chain | nondeg cuts | u a b | A 2Δ | minAdm(M) minAdm(rc) | needed_thr | fold_reaches | Q2HARD?")
tests = [
 (2,2,2,2),(3,3,3,3),(2,2,3,3),(2,2,4,4),(2,3,4,4),(1,1,3,1),(1,2,3,3),
 (2,2,2),(2,2,2,2,2),(3,3,3,3,3),(2,2,3),(4,4,4,4),(2,2,2,3),(3,3,4,4),
 (2,3,3,3),(1,1,2,2),(1,2,2,2),(2,4,3,3),(1,1,4,4),(2,2,5,5),
]
for M in tests:
    if len(M) < 3:
        continue
    sp = saturated_params(M)
    cuts = nondeg_cut_exists(M)
    q2hard = sp['A'] > sp['twoDelta']
    print(f"{M} | cuts={cuts} | u={sp['u']} a={sp['a']} b={sp['b']} | A={sp['A']} 2Δ={sp['twoDelta']} | {sp['minAdm_M']} {sp['minAdm_rc']} (rc={sp['rc']}) | need={sp['needed_thr']} | fold={sp['fold_reaches']} | {'*** Q2-HARD' if q2hard else 'clean'}")
