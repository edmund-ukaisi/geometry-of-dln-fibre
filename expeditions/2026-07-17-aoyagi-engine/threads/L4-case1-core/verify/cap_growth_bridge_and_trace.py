"""
For seat-killfin's render-pricing: (1) is the FOLD-level escaped coefficient = the PURE row-e-of-P_S
(bridge trivial), or does it differ (bridge = real Lean work)?  (trace) the per-level descent bookkeeping.

(1) BRIDGE. At the last clear of layer S, escaped coord m=(S+1,a,e), e≥wmu(S+1). Compare:
   fold c_m := coeff of u_m in the REAL foldResid child (blow-ups + shears on layers ≤ S);
   pure c_m := coeff of u_m in coreGen (= [left, layers≥S+2] × row-e-of-P_S).
The escaped coord is a SPECTATOR as an OUTPUT of Φ (shears write only block cols < wmu(S+1)), but the
shear branch-(ii) READS escaped coords to write block cols, so coreGen reading those block-col slots picks
up u_m — so fold c_m may carry shear corrections. This script measures: fold c_m ?= pure c_m, and whether
BOTH ∈ ⟨couplings⟩ (⟹ the fold-level statement holds regardless, and a fold-native proof is viable).
"""
import sympy as sp
from cap_frontier_sufficiency import make, widthMinUpto, real_foldResid, coreGen

def cc(d, S, J):
    cap = widthMinUpto(d, S)
    return {(L, r, c) for (L, r, c) in make(d)[1] if L == S and J <= r and J <= c and c < cap}

def couplingCoords(d, pivots):
    S = set()
    for (pL, pa, pb) in pivots:
        S |= {(pL, r, pb) for r in range(d[pL + 1]) if r > pa}
    return S

def bridge(d, S):
    N, u = make(d)
    edges = []; pivots = []
    for L in range(S + 1):
        for J in range(widthMinUpto(d, L + 1)):
            edges.append(("case2", L, J, (L, J, J), cc(d, L, J), 1 if J == 0 else 0)); pivots.append((L, J, J))
        if L < S:
            edges.append(("rollover", L, widthMinUpto(d, L + 1), (L + 1, 0, 0), set(), 0))
    fold = [sp.expand(f) for f in real_foldResid(u, d, edges)]
    pure = [sp.expand(f) for f in coreGen(u, d)]              # coreGen = ∏A, no blow-ups
    cpl = couplingCoords(d, pivots); zc = {u[k]: 0 for k in cpl}
    wmuS1 = widthMinUpto(d, S + 1)
    escaped = sorted(k for k in u if k[0] == S + 1 and k[2] >= wmuS1)
    print(f"d={d}, last-clear S={S}, escaped {escaped}:")
    for m in escaped[:1]:                                    # one representative escaped coord
        eq_all = True; foldkill = True; purekill = True
        for j in range(len(fold)):
            cf = sp.expand(fold[j].coeff(u[m], 1)); cp = sp.expand(pure[j].coeff(u[m], 1))
            if cf != cp: eq_all = False
            if sp.expand(cf.subs(zc)) != 0: foldkill = False
            if sp.expand(cp.subs(zc)) != 0: purekill = False
        print(f"  u_{m}: fold c_m == pure c_m (bridge trivial)? {eq_all};  "
              f"fold c_m ∈⟨couplings⟩? {foldkill};  pure c_m ∈⟨couplings⟩? {purekill}")
    return

print("=== (1) BRIDGE: fold-level vs pure-coreGen escaped coefficient ===")
for d in [(2, 3, 3, 3), (3, 2, 3, 3)]:
    bridge(d, 1)

print("\n=== (trace) per-level descent bookkeeping, d=(2,3,3,3), P_1 row e=2 ===")
# P_L = A_L···A_0; trace the split of row e=2 of P_1 (S=1): peel A_1·P_0, split contraction index j.
d = (2, 3, 3, 3); N, u = make(d)
def Amat(m): return sp.Matrix(d[m + 1], d[m], lambda r, c: u[(m, r, c)])
P0 = Amat(0)                                  # P_0 = A_0  (3x2)
P1 = Amat(1) * P0                             # P_1 = A_1·A_0  (3x2)
e = 2                                          # remnant row, e >= wmu(2)=2
print(f"  wmu(2)={widthMinUpto(d,2)}; row e={e} of P_1 = A_1·A_0; peel P_1[e,k] = Σ_j A_1[e,j]·P_0[j,k]:")
for j in range(d[1]):                          # contraction index j over cols of A_1 (= d_1 = 3)
    tag = ("COUPLING (j<wmu(2)=2, A_1[e,j] below-diag cleared)" if j < widthMinUpto(d, 2)
           else "RECURSE (j>=wmu(2)=2 uncleared → row j of P_0)")
    print(f"    j={j}: A_1[{e},{j}]=u_{(1,e,j)}  [{tag}]")
print(f"  bottleneck B=0 (d_0=2=wmu(2)) ⟹ layer-0 cols all cleared; recurse rows of P_0 bottom in couplings.")
print(f"  IH form: for a REMNANT ROW j (wmu(L)≤j<d_L) of P_{{L-1}}, ALL entries P_{{L-1}}[j,k] (∀k) ∈ ⟨couplings⟩.")
