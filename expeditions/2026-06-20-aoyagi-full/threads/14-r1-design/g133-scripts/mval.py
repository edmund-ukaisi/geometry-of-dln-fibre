"""
Exact reproduction of the Lean Mval / admPred / Adm / lambdaCore objects
(DLNFibre.DLN.RLCT.Foundations.Lambda), in plain integer arithmetic.

Lean indexing (M : Fin (L+1) -> N, T : Fin L -> N):
  - L+1 widths M[0..L]; L exponents T[0..L-1].
  - tPrev M T j = M[0] if j==0 else T[j-1]   (the "t^{j-1}" with t^0 := M^1 = M[0])
  - Mval M T = sum_{j=0}^{L-1} (tPrev[j] - T[j]) * (M[j+1] - T[j])         (over Z)
  - admBound M j = min(M[0],M[1]) if j==0 else M[j+1]
  - admPred:
      (a) for all j: T[j] <= admBound[j]
      (b) weak-decrease: for all i<=j: T[j] <= T[i]   (so T weakly decreasing)
      (c) last-zero: for all j with j == L-1: T[j] == 0
  - Adm = all T in prod_j range(admBound[j]+1) with admPred
  - lambdaCore = (1/2) * min_{T in Adm} Mval(M,T)

This is the GROUND TRUTH the pivot-tree atlas claims to reproduce as a codim-min.
"""
from itertools import product
from fractions import Fraction

def tPrev(M, T, j):
    return M[0] if j == 0 else T[j-1]

def Mval(M, T):
    L = len(T)
    s = 0
    for j in range(L):
        s += (tPrev(M, T, j) - T[j]) * (M[j+1] - T[j])
    return s

def admBound(M, j):
    if j == 0:
        return min(M[0], M[1])
    return M[j+1]

def adm_pred(M, T):
    L = len(T)
    # (a) per-block bound
    for j in range(L):
        if T[j] > admBound(M, j):
            return False
    # (b) weak-decrease for i<=j: T[j] <= T[i]
    for i in range(L):
        for j in range(i, L):
            if T[j] > T[i]:
                return False
    # (c) last-zero
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
        if adm_pred(M, T):
            out.append(tuple(T))
    return out

def lambdaCore(M):
    A = Adm(M)
    mn = min(Mval(M, T) for T in A)
    return Fraction(1, 2) * mn

def adm_with_vals(M):
    A = Adm(M)
    return sorted([(T, Mval(M, T)) for T in A], key=lambda kv: (kv[1], kv[0]))

if __name__ == "__main__":
    # Ground-truth cross-checks from Lean Lambda.lean #eval block (r=0 so aoyagiLambda = lambdaCore).
    checks = {
        (2,2,2): Fraction(3,2),
        (2,1,2): Fraction(1,1),
        (2,2,2,2): Fraction(3,2),
        (3,3,3,3): Fraction(3,1),
    }
    for M, exp in checks.items():
        got = lambdaCore(list(M))
        flag = "OK" if got == exp else "MISMATCH"
        print(f"M={M}: lambdaCore={got}  expected={exp}  [{flag}]")
    print()
    for M in [(2,2,2),(2,1,2),(1,2,1),(3,1,3),(2,3,2),(3,2,1),(1,2,3),(3,3,3,3),(2,2,2,2)]:
        av = adm_with_vals(list(M))
        mn = av[0][1]
        print(f"M={M}: minMval={mn} lambdaCore={Fraction(mn,2)}")
        for T,v in av:
            mark = " <-- MIN" if v==mn else ""
            print(f"    T={T}  Mval={v}{mark}")
        print()
