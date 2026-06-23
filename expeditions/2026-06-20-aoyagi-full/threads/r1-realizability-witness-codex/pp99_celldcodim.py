#!/usr/bin/env python3
"""
#99 cap-class adjudication — does the non-leaf cell/codim decomposition compute the rank-pattern read
WITHOUT an intermediate-width-pinch bug in the per-cell Mval?

The redeploy question: rs-grind is building the non-leaf rank-pattern read -> cells + per-cell
admissible-Mval codims, root-anchored. Truth-value: does that cell/codim decomposition correctly compute
the rank-pattern read for general non-leaf M WITHOUT an endpoint-cap-class bug (an intermediate-width
pinch in the per-cell Mval)?

THE TWO CANDIDATE BUG SITES (committed semantics, origin/fm3/routem):

  (Site 1) The CODIM FORMULA Mval itself.
     Mval M T = Σ_j (tPrev_j - T_j)*(M_{j+1} - T_j),  tPrev_0 = M_0, tPrev_j = T_{j-1}.
     This is PURE COMBINATORIAL in (M,T): NO matrix rank, NO window-min, NO endpoint cap.
     => the cap-class pinch CANNOT live here. (Confirm: Mval references no rank.)

  (Site 2) The CELL's T_c READ — how the dispatcher reads T_c off the cell's rank-drop profile.
     Route (a) (committed architecture, feasibility-CERT §3): codim c := (Mval M₀ T_c).toNat for a
     T_c the dispatcher PICKS from the rank-drop profile of the cell's ChainDimSplit. The pinch could
     enter IF T_c is read as a running-rank vector via a rank pattern with the intermediate-width cap bug.
     The genuine running-rank read (the #121 result) is:
        t_j = rankFn M₀ A 0 j   (the (0,j) prefix row),  exact rank = min(window-min T, min over ALL
        widths M_0..M_j).  The endpoint-only cap min(M_0,M_j) is WRONG in general (the #121 pinch),
        correct only when no intermediate width binds.

  So the #99 cap-class test = does the cell's T_c (running-rank profile) read use the CORRECT all-widths
  rank, or could a non-leaf M with an interior width pinch produce a WRONG T_c -> wrong codim?

THIS SCRIPT:
  (A) Confirm Site-1: Mval is rank-free (structural — asserted, verified by re-eval matching #eval anchors).
  (B) Build the genuine non-leaf rank-pattern read of a tuple over a general M: the running ranks
      t_j = exact rank of the (0,j) prefix product, AND the achiever T* via Adm/Mval.
  (C) For ADVERSARIAL non-leaf M with an INTERIOR WIDTH PINCH (M_s small in the middle), compute:
      - the genuine prefix running-rank read of the diagonal-cascade achiever (exact rank over QQ);
      - the codim Mval M₀ T_c emitted from that read;
      - compare to the codim emitted from a PINCHED (endpoint-cap) read of T_c.
      If the two reads give DIFFERENT codims on a non-leaf M, the cap-class bug is LIVE and must be fenced.
  (D) Anchor: (2,2,2) and (3,2,3) reproduce the known codims (4,3 / minAdm) under the genuine read.
"""
import sympy as sp
from itertools import product

# ---------- committed Mval / Adm (Lambda.lean) ----------
def tPrev(M, T, j):
    return M[0] if j == 0 else T[j-1]
def Mval(M, T):
    L = len(M) - 1
    return sum((tPrev(M, T, j) - T[j]) * (M[j+1] - T[j]) for j in range(L))
def admBound(M, j):
    return min(M[0], M[1]) if j == 0 else M[j+1]
def admPred(M, T):
    L = len(M) - 1
    if any(T[j] > admBound(M, j) for j in range(L)): return False
    if any(T[j] > T[i] for i in range(L) for j in range(i, L)): return False
    if L >= 1 and T[L-1] != 0: return False
    return True
def Adm(M):
    L = len(M) - 1
    return [list(T) for T in product(*[range(admBound(M, j)+1) for j in range(L)]) if admPred(M, list(T))]
def minAdm(M):
    return min(Mval(M, T) for T in Adm(M))
def achievers(M):
    mn = minAdm(M)
    return mn, [T for T in Adm(M) if Mval(M, T) == mn]

# ---------- exact cascade prefix running-rank read ----------
def partialId(r, c, t):
    return sp.Matrix(r, c, lambda a, b: 1 if (a == b and a < t) else 0)
def submult(M, T, i, j):
    P = sp.eye(M[i])
    for s in range(i, j):
        P = partialId(M[s+1], M[s], T[s]) * P
    return P
def prefix_running_ranks_exact(M, T):
    """t_j = exact rank of the (0,j) prefix product of the diagonal cascade for exponent vector T."""
    L = len(M) - 1
    return [submult(M, T, 0, j).rank() for j in range(L+1)]   # t_0=M_0, ..., t_L

# ---------- two reads of T_c from running ranks ----------
def Tc_from_running(t):
    """The exponent vector read off the running ranks: T_c[s] = t_{s+1} (drop the prefix t_0=M_0)."""
    return list(t[1:])
def running_endpoint_pinch(M, T):
    """The PINCHED (endpoint-cap) running-rank read: t_j = min(window-min T over [0,j), min(M_0,M_j)).
    This is the BUGGY formula (endpoint cap only) — what a careless read would emit."""
    L = len(M) - 1
    out = [M[0]]
    for j in range(1, L+1):
        wmin = min(T[p] for p in range(0, j))
        out.append(min(wmin, min(M[0], M[j])))
    return out
def running_allwidths_correct(M, T):
    """The CORRECT all-widths running-rank read: t_j = min(window-min T, min over ALL widths M_0..M_j)."""
    L = len(M) - 1
    out = [M[0]]
    for j in range(1, L+1):
        wmin = min(T[p] for p in range(0, j))
        out.append(min(wmin, min(M[r] for r in range(0, j+1))))
    return out

# ===================================================================================
print("=== (A) Site-1: Mval is rank-free (structural) — re-eval matches committed #eval anchors ===")
# committed #guard anchors: lambdaCore via aoyagiLambda; here check Mval/minAdm directly
for M, exp_minadm in [([2,2,2], 3), ([2,1,2], 2), ([2,2,2,2], 3), ([3,3,3,3], 6)]:
    mn, ach = achievers(M)
    print(f"   M={M}: minAdm={mn} (expected lambdaCore*2={exp_minadm}), achievers={ach}")
print("   Mval uses tPrev/T/M arithmetic only — no Matrix.rank, no min-cap. Site-1 cannot pinch.")
print()

print("=== (C) ADVERSARIAL non-leaf M with INTERIOR WIDTH PINCH: do the two T_c reads diverge? ===")
# non-leaf: minAdm(M) > 0 (NOT a geometric leaf). interior pinch: an M_s (0<s<L) strictly less than
# a neighbor so an intermediate width can bind.
def is_nonleaf(M):
    return minAdm(M) > 0
diverge = []
checked = 0
for L in [2, 3, 4]:
    for M in product(range(1, 5), repeat=L+1):
        M = list(M)
        if not is_nonleaf(M): continue
        # interior pinch present?
        if not any(M[s] < M[s-1] and M[s] < M[s+1] for s in range(1, L)): continue
        mn, ach = achievers(M)
        for Tstar in ach:
            checked += 1
            t_exact = prefix_running_ranks_exact(M, Tstar)        # genuine exact running ranks
            t_correct = running_allwidths_correct(M, Tstar)        # all-widths formula
            t_pinch = running_endpoint_pinch(M, Tstar)             # endpoint-cap buggy formula
            # sanity: exact == correct (all-widths)
            assert t_exact == t_correct, (M, Tstar, t_exact, t_correct)
            # the two T_c reads
            Tc_correct = Tc_from_running(t_correct)
            Tc_pinch = Tc_from_running(t_pinch)
            # the emitted codims
            cod_correct = Mval(M, Tstar)                 # the genuine achiever codim (should = minAdm)
            cod_from_correct_read = Mval(M, Tc_correct)  # codim from the correct running read
            cod_from_pinch_read = Mval(M, Tc_pinch)      # codim from the pinched running read
            if Tc_correct != Tc_pinch or cod_from_correct_read != cod_from_pinch_read:
                diverge.append((tuple(M), tuple(Tstar), t_correct, t_pinch,
                                Tc_correct, Tc_pinch, cod_from_correct_read, cod_from_pinch_read))
print(f"   non-leaf interior-pinch achiever cases checked: {checked}")
print(f"   cases where the CORRECT vs PINCHED T_c read DIVERGE: {len(diverge)}")
for d in diverge[:8]:
    M, Tstar, tc, tp, Tcc, Tcp, cc, cp = d
    print(f"     M={M} T*={Tstar}: t_correct={tc} t_pinch={tp}  Tc_correct={Tcc}(codim {cc}) Tc_pinch={Tcp}(codim {cp})")
print()

# ===================================================================================
print("=== (D) anchors reproduce known codims under the genuine read ===")
for M in [[2,2,2], [3,2,3], [4,3,2], [3,3,3,3]]:
    mn, ach = achievers(M)
    Tstar = ach[0]
    t = prefix_running_ranks_exact(M, Tstar)
    print(f"   M={M}: achiever T*={Tstar} minAdm={mn}; exact prefix running ranks t={t};"
          f" Mval(M,T*)={Mval(M,Tstar)} (=minAdm: {Mval(M,Tstar)==mn})")
