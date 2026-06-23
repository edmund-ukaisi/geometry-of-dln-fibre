#!/usr/bin/env python3
"""
#136 de-risk — is the GEOMETRIC-BRIDGE identity Mval(M,T*) = multSum/orbitLinearCodim TRUE + provable?

The LR "geometric codimension is the new content" link. Decorrelated exact-algebra (integer arithmetic).

CHAIN (decl-grounded against origin/fm3/routem):
  T*  : the achiever exponent (T* ∈ Adm M, Mval M T* = minAdm M).
  r   = achieverRankPattern M T*  : the (i,j) rank pattern of T*'s stratum (#121 object, the running ranks).
        achieverRankPattern i j = T*_{j-1} (=ρ_j) if i<j ;  M_i if i=j ;  0 if i>j.   [r_{ij}]
  embedRank r : r_{ij} on 0≤i,j≤N, 0 outside (the ℤ-embedded pattern).
  m = diff(embedRank r) : the Kostant multiplicity array (second difference, OrbitKostant.diffArrayOfRank):
        m_{ij} = r_{ij} − r_{i,j+1} − r_{i-1,j} + r_{i-1,j+1}   (out-of-range = 0).   [RankPattern.diff_apply]
  multSum(m) = Σ_{1≤i≤u≤j≤v≤N} m_{i-1,j-1} · m_{uv}             [OrbitLinearCodim.orbitLinearCodim_eq_multSum]
             = orbitLinearCodim(M_{T*}) = finrank Ext¹  (= codim Ō_{M_{T*}} via Voigt, char 0).

  Mval(M,T) = Σ_{j=0}^{L-1} (tPrev_j − T_j)(M_{j+1} − T_j),  tPrev_0=M_0, tPrev_j=T_{j-1}.   [Lambda.Mval]

TEST: does multSum(diff(embedRank(achieverRankPattern M T*))) == Mval(M, T*) ?
  AND, stronger (the genuine identity, not just at the achiever): does it hold for EVERY admissible T,
  i.e. Mval(M,T) = multSum of T's stratum?  (Mval is defined for all admissible T; the geometric codim
  of the stratum r(T) should equal it if the bridge is the genuine LR identity, not an achiever accident.)
"""
from itertools import product

# ---------- RLCT side: Mval, Adm ----------
def tPrev(M, T, j): return M[0] if j == 0 else T[j-1]
def Mval(M, T):
    L = len(M)-1
    return sum((tPrev(M, T, j) - T[j]) * (M[j+1] - T[j]) for j in range(L))
def admBound(M, j): return min(M[0], M[1]) if j == 0 else M[j+1]
def admPred(M, T):
    L = len(M)-1
    if any(T[j] > admBound(M, j) for j in range(L)): return False
    if any(T[j] > T[i] for i in range(L) for j in range(i, L)): return False
    if L >= 1 and T[L-1] != 0: return False
    return True
def Adm(M):
    L = len(M)-1
    return [list(T) for T in product(*[range(admBound(M, j)+1) for j in range(L)]) if admPred(M, list(T))]
def achievers(M):
    a = Adm(M); mn = min(Mval(M, T) for T in a)
    return mn, [T for T in a if Mval(M, T) == mn]

# ---------- geometric side: achieverRankPattern, embedRank, diff, multSum ----------
def expSurv(M, T, j): return M[0] if j == 0 else T[j-1]          # ρ_j (running rank)
def achieverRankPattern(M, T):
    """r_{ij} on the Fin(N+1) grid (N=L). r_{ij}=ρ_j (i<j), M_i (i=j), 0 (i>j)."""
    N = len(M)-1
    return {(i, j): (expSurv(M, T, j) if i < j else (M[i] if i == j else 0))
            for i in range(N+1) for j in range(N+1)}
def embedRank(r, N):
    """r_{ij} for 0≤i,j≤N, else 0 (integer ℤ-array)."""
    def f(i, j):
        if 0 <= i <= N and 0 <= j <= N: return r[(i, j)]
        return 0
    return f
def diff_array(R):
    """m_{ij} = R_{ij} − R_{i,j+1} − R_{i-1,j} + R_{i-1,j+1}  (the second difference)."""
    return lambda i, j: R(i, j) - R(i, j+1) - R(i-1, j) + R(i-1, j+1)
def multSum(m, N):
    """Σ_{1≤i≤u≤j≤v≤N} m_{i-1,j-1} · m_{uv}."""
    tot = 0
    for i in range(1, N+1):
        for u in range(i, N+1):
            for j in range(u, N+1):
                for v in range(j, N+1):
                    tot += m(i-1, j-1) * m(u, v)
    return tot

def geom_codim(M, T):
    """multSum of the stratum r(T) — the LR geometric codim (orbitLinearCodim)."""
    N = len(M)-1
    r = achieverRankPattern(M, T)
    R = embedRank(r, N)
    m = diff_array(R)
    return multSum(m, N)

# ============================================================================
# TEST 1: achiever T* — does Mval(M,T*) == geom_codim(M,T*) == minAdm ?
# TEST 2 (stronger): for ALL admissible T, Mval(M,T) == geom_codim(M,T) ?  (the genuine LR identity)
# ============================================================================
print("=== TEST 1: achiever T* — Mval(M,T*) vs geom multSum(diff(achieverRankPattern)) ===")
for M in [[2,2,2],[2,1,2],[3,2,3],[4,3,2],[2,2,2,2],[3,3,3,3],[5,4,3,2]]:
    mn, ach = achievers(M)
    for T in ach[:1]:
        mv = Mval(M, T); gc = geom_codim(M, T)
        print(f"  M={M} T*={T}: Mval={mv} (minAdm={mn}), geom multSum={gc}, MATCH={mv==gc}")
print()

print("=== TEST 2 (the genuine identity): Mval(M,T) == geom_codim(M,T) for ALL admissible T? ===")
fails = 0; checked = 0; fail_ex = []
for L in [2, 3, 4]:
    for M in product(range(1, 5), repeat=L+1):
        M = list(M)
        for T in Adm(M):
            checked += 1
            if Mval(M, T) != geom_codim(M, T):
                fails += 1
                if len(fail_ex) < 10: fail_ex.append((tuple(M), tuple(T), Mval(M, T), geom_codim(M, T)))
print(f"  checked {checked} admissible (L=2..4, widths 1..4): Mval == geom multSum  fails = {fails}")
for e in fail_ex: print("    MISMATCH M,T,Mval,geom:", e)
print()

# ============================================================================
# TEST 3: cross-check against the COMMITTED Lean anchors (OrbitLinearCodim.lean examples):
#   (2,2,2) (1,1)-orbit [(0,0),(0,1),(1,2),(2,2)] -> orbitLinearCodim 3   (the achiever stratum)
#   (2,2,2) zero-product [(0,0),(0,0),(1,2),(1,2)] -> orbitLinearCodim 4   (the T=0 / origin stratum)
# Verify my multSum reproduces these from the corresponding rank patterns.
# ============================================================================
print("=== TEST 3: reproduce committed OrbitLinearCodim anchors from rank patterns ===")
# (2,2,2): achiever T*=(1,0) -> r pattern; T=0 (origin) -> r pattern. Check geom_codim matches 3 and 4.
M = [2,2,2]
print(f"  (2,2,2) achiever T*=(1,0): geom_codim={geom_codim(M,[1,0])} (committed (1,1)-orbit codim=3, =minAdm)")
print(f"  (2,2,2) origin   T =(0,0): geom_codim={geom_codim(M,[0,0])} (committed zero-product codim=4, =Mval(0,0))")
print(f"     Mval(2,2,2)(1,0)={Mval(M,[1,0])}, Mval(2,2,2)(0,0)={Mval(M,[0,0])}")
