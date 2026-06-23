#!/usr/bin/env python3
"""
pen-and-paper #121 adjudication — EXACT (sympy over QQ) rankFn(cascadeTuple M T) vs the two
candidate r* objects.  NO float ranks.

Committed semantics (origin/fm3/routem):
  partialId k r c t  = Matrix (Fin r) (Fin c) :  entry (a,b)=1 iff a=b (as nat) and a<t, else 0.
  cascadeTuple M T s = partialId (M_{s+1}) (M_s) (T_s)      [block A_s : (M_{s+1}) x (M_s)]
  submult M A i j (i<=j) = A_{j-1} * ... * A_i   :  Matrix (Fin M_j) (Fin M_i)   (LEFT-multiply build)
       (empty product at i=j is the identity 1 : Matrix (Fin M_i)(Fin M_i))
  rankPattern M A i j = (submult M A i j).rank
  rankFn M A i j = if i<=j then rankPattern else 0     [total, 0 off the i<=j triangle]

  Core-proven (rankPattern_cascade):
     rankPattern (cascade) i j = survivors (M_j) (M_i) (cascadeWindow i j)
        = min( cascadeWindow i j , min(M_j, M_i) )
     cascadeWindow i j = (min over i<=p<j of T_p) capped at base width M_i  (= M_i at j=i)
  i.e. EXACTLY survivors(M_j,M_i, window-min of T over [i,j)).   CAPPED by min(M_i,M_j).

Two candidate r* objects:
  (CODEX) achieverRankPattern M T i j :=  if i<j then expSurvivor M T j  else if i=j then M_i else 0
          expSurvivor M T 0 = M_0,  expSurvivor M T (j+1) = T_j   (so expSurvivor is t_j, the running rank)
          ==> COLUMN-CONSTANT in i, value t_j on the whole column i<j, NOT capped by min(M_i,M_j).
  (CORE)  coreRankPattern M T i j :=  survivors(M_j,M_i, windowMin_T[i,j))  (the committed cascade pattern)

Admissibility (committed admPred, Lambda.lean):
  admBound j = min(M_0,M_1) if j=0 else M_{j+1}
  admPred:  (i) T_j <= admBound j   (ii) i<=j => T_j<=T_i  (weak decrease)   (iii) T_{L-1}=0
"""
import sympy as sp
from itertools import product

# ---------- committed admissibility ----------
def admBound(M, j):
    return min(M[0], M[1]) if j == 0 else M[j+1]

def admPred(M, T):
    L = len(M) - 1
    if any(T[j] > admBound(M, j) for j in range(L)):
        return False
    for i in range(L):
        for j in range(i, L):
            if T[j] > T[i]:
                return False
    if L >= 1 and T[L-1] != 0:
        return False
    return True

def Adm(M):
    L = len(M) - 1
    return [list(T) for T in product(*[range(admBound(M, j)+1) for j in range(L)])
            if admPred(M, list(T))]

# ---------- EXACT cascade matrices over QQ ----------
def partialId(r, c, t):
    """Matrix (Fin r)(Fin c): entry (a,b)=1 iff a==b and a<t."""
    return sp.Matrix(r, c, lambda a, b: 1 if (a == b and a < t) else 0)

def submult(M, T, i, j):
    """submult M (cascade) i j = A_{j-1} * ... * A_i, exact over QQ.  i<=j."""
    Mi = M[i]
    P = sp.eye(Mi)                      # empty product = identity on Fin M_i  (Mi x Mi)
    for s in range(i, j):               # left-multiply by A_s = partialId(M_{s+1},M_s,T_s)
        A_s = partialId(M[s+1], M[s], T[s])
        P = A_s * P                     # (M_{s+1} x M_s)*(M_s x M_i) = (M_{s+1} x M_i)
    return P

def rankFn_cascade_exact(M, T):
    """EXACT rankFn of the actual cascade tuple (sympy .rank over QQ)."""
    L = len(M) - 1
    R = {}
    for i in range(L+1):
        for j in range(L+1):
            if i < j:
                R[(i, j)] = submult(M, T, i, j).rank()
            elif i == j:
                R[(i, j)] = M[i]            # rankPattern_self: identity rank = M_i
            else:
                R[(i, j)] = 0
    return R

# ---------- candidate r* objects ----------
def expSurvivor(M, T, j):           # the running rank t_j
    return M[0] if j == 0 else T[j-1]

def codex_rstar(M, T):
    """CODEX achieverRankPattern: column-constant, value t_j, NOT capped."""
    L = len(M) - 1
    R = {}
    for i in range(L+1):
        for j in range(L+1):
            if i < j:
                R[(i, j)] = expSurvivor(M, T, j)
            elif i == j:
                R[(i, j)] = M[i]
            else:
                R[(i, j)] = 0
    return R

def windowMin_T(M, T, i, j):        # min over i<=p<j of T_p ; empty (i==j) = +inf
    if i == j:
        return None
    return min(T[p] for p in range(i, j))

def core_rstar(M, T):
    """CORE committed cascade pattern: survivors(M_j,M_i, windowMin_T[i,j)) = capped."""
    L = len(M) - 1
    R = {}
    for i in range(L+1):
        for j in range(L+1):
            if i < j:
                w = windowMin_T(M, T, i, j)
                R[(i, j)] = min(w, min(M[i], M[j]))
            elif i == j:
                R[(i, j)] = M[i]
            else:
                R[(i, j)] = 0
    return R

# =====================================================================================
# CHECK A: does the EXACT cascade rankFn match CORE? (sanity — it must, Core proves it)
# CHECK B: does the EXACT cascade rankFn match CODEX? (the codex statement as written)
# CHECK C: for ADMISSIBLE T, do CODEX and CORE coincide? (the monotonicity/cap subtlety)
# Run over all admissible T for a sweep of M, AND record the FIRST place codex != core (any T).
# =====================================================================================
def run():
    coreFail = []       # (M,T) where exact cascade != core   (should be empty)
    codexFail_adm = []  # (M,T,cell) admissible where exact cascade != codex
    codexFail_any = []  # (M,T,cell) ANY T where codex != core (shows the cap bites off-admissible)
    checked_adm = 0
    for L in [2, 3, 4]:
        for M in product(range(1, 5), repeat=L+1):
            M = list(M)
            adm = Adm(M)
            for T in adm:
                checked_adm += 1
                Rexact = rankFn_cascade_exact(M, T)
                Rcore = core_rstar(M, T)
                Rcodex = codex_rstar(M, T)
                # A: exact == core
                for k in Rexact:
                    if Rexact[k] != Rcore[k]:
                        coreFail.append((tuple(M), tuple(T), k, Rexact[k], Rcore[k]))
                # B: exact == codex (admissible)
                for k in Rexact:
                    if Rexact[k] != Rcodex[k]:
                        codexFail_adm.append((tuple(M), tuple(T), k, Rexact[k], Rcodex[k]))
    # C: where does CODEX != CORE for NON-admissible (non-monotone) T? — show the cap is real content
    # pick a small M and sweep ALL T (not just admissible) to localize the difference
    for M in [[3,2,3], [2,3,2], [2,3,4,3], [4,2,4,2]]:
        L = len(M)-1
        for T in product(*[range(M[s+1]+1) for s in range(L)]):
            T = list(T)
            Rcore = core_rstar(M, T)
            Rcodex = codex_rstar(M, T)
            diffs = [(k, Rcore[k], Rcodex[k]) for k in Rcore if Rcore[k] != Rcodex[k]]
            if diffs:
                codexFail_any.append((tuple(M), tuple(T), admPred(M, T), diffs[:3]))

    print(f"[CHECK A] exact cascade rankFn vs CORE survivors/window-min:")
    print(f"   admissible T checked (L=2..4, widths 1..4): {checked_adm}")
    print(f"   MISMATCHES exact!=core: {len(coreFail)}   (must be 0 — Core proves it)")
    if coreFail[:5]:
        for f in coreFail[:5]:
            print("     ", f)
    print()
    print(f"[CHECK B] exact cascade rankFn vs CODEX column-constant, on ADMISSIBLE T:")
    print(f"   MISMATCHES exact!=codex (admissible): {len(codexFail_adm)}")
    if codexFail_adm[:8]:
        for f in codexFail_adm[:8]:
            print("     ", f)
    print()
    print(f"[CHECK C] CODEX vs CORE difference localization (ALL T, small M) — where the CAP bites:")
    n_adm_diff = sum(1 for (_,_,isadm,_) in codexFail_any if isadm)
    n_nonadm_diff = sum(1 for (_,_,isadm,_) in codexFail_any if not isadm)
    print(f"   (M,T) with codex != core:  admissible={n_adm_diff}  non-admissible={n_nonadm_diff}")
    for f in codexFail_any[:10]:
        print("     M,T,admissible?,diffs(cell,core,codex):", f)

if __name__ == "__main__":
    run()
