"""
Exact replica of the Lean Core definitions on branch origin/fm3/routem-ga.

minAdm M  = min over T in Adm(M) of Mval(M,T)      (an INTEGER; Lean: (Adm M).inf' Mval)
schurState M = (M0-1, M1-1, M2, M3, ...)            (front two widths reduced by 1)

Definitions (Lambda.lean):
  tPrev M T j = M0           if j == 0
              = T[j-1]       else
  Mval M T = sum_{j=0..L-1} (tPrev_j - T_j) * (M_{j+1} - T_j)        over Z

  admBound M j = min(M0, M1)   if j == 0
               = M_{j+1}       else
  admPred M T  =  (forall j: T_j <= admBound M j)
              and (forall i<=j: T_j <= T_i)          (weak decrease)
              and (forall j with j == L-1: T_j == 0)  (last exponent zero)
  Adm M = { T in prod_j [0..admBound M j] : admPred M T }

Indexing: M : Fin(L+1) -> N, so M has length L+1; T : Fin L -> N, length L.
A "non-leaf" M for the recursion: hMid requires all widths > 0 at pivot vertices etc.;
for the witness sweep we follow rs-grind's sweep description (L=1..3, widths 1..4, non-leaf).
"""

from itertools import product

def tPrev(M, T, j):
    # M list length L+1, T list length L, j in 0..L-1
    if j == 0:
        return M[0]
    else:
        return T[j-1]

def Mval(M, T):
    L = len(T)
    s = 0
    for j in range(L):
        s += (tPrev(M, T, j) - T[j]) * (M[j+1] - T[j])
    return s

def admBound(M, j):
    L = len(M) - 1
    if j == 0:
        return min(M[0], M[1])
    else:
        return M[j+1]

def admPred(M, T):
    L = len(T)
    # T_j <= admBound M j
    for j in range(L):
        if not (T[j] <= admBound(M, j)):
            return False
    # weak decrease: T_j <= T_i for i <= j
    for i in range(L):
        for j in range(L):
            if i <= j:
                if not (T[j] <= T[i]):
                    return False
    # last exponent zero: j == L-1 => T_j == 0
    for j in range(L):
        if j == L - 1:
            if T[j] != 0:
                return False
    return True

def Adm(M):
    L = len(M) - 1
    ranges = [range(admBound(M, j) + 1) for j in range(L)]
    out = []
    for T in product(*ranges):
        T = list(T)
        if admPred(M, T):
            out.append(tuple(T))
    return out

def minAdm(M):
    adm = Adm(M)
    assert len(adm) > 0
    return min(Mval(M, list(T)) for T in adm)

def achievers(M):
    """All admissible T achieving the min, with the min value."""
    m = minAdm(M)
    return m, [T for T in Adm(M) if Mval(M, list(T)) == m]

def schurState(M):
    """(M0-1, M1-1, M2, ...). Requires M0,M1 >= 1."""
    Mp = list(M)
    Mp[0] -= 1
    Mp[1] -= 1
    return Mp

def is_non_leaf(M):
    """
    Recursion is entered under hMid; pivot vertices (s.val <= 1) need 1 <= M s for schurState
    to be defined. The recursion's 'non-leaf' (hMid) requires 0 < M s for s <= 1 at least.
    rs-grind's sweep: non-leaf M. We require M0>=1 and M1>=1 so schurState is defined.
    Additionally a genuine 'leaf' (L=1, rank-0 core) would be M=(1,1) type; we follow the
    sweep that excludes pure leaves. For the monotonicity claim we only need schurState defined.
    """
    return M[0] >= 1 and M[1] >= 1

# ============================================================================
# CERTIFICATE CHECK (pp-rstar, #149): minAdm(schurStateRed M) <= minAdm M
# Construction: uniform cap  T'_j := min(T_j, min(M0,M1)-1)   (Codex-decorrelated).
# ============================================================================
if __name__ == "__main__":
    from itertools import product
    import random
    random.seed(42)
    def cap(M, T):
        c = min(M[0], M[1]) - 1
        return tuple(min(T[j], c) for j in range(len(M) - 1))
    sweep = []
    for L in range(1, 4):
        for M in product(range(1, 5), repeat=L + 1):
            M = list(M)
            if M[0] < 1 or M[1] < 1: continue
            sweep.append(tuple(M))
    f_minadm = f_adm = f_val = npairs = 0
    for M in sweep:
        M = list(M); Mp = schurState(M); AdmMp = set(Adm(Mp))
        if minAdm(Mp) > minAdm(M): f_minadm += 1
        for T in Adm(M):
            npairs += 1; Tp = cap(M, T)
            if Tp not in AdmMp: f_adm += 1
            if Mval(Mp, list(Tp)) > Mval(M, list(T)): f_val += 1
    print(f"336 sweep: pairs={npairs} minAdm_fail={f_minadm} adm_fail={f_adm} val_fail={f_val}")
    assert f_minadm == f_adm == f_val == 0, "certificate broken"
    print("CERTIFICATE CLEAN")
