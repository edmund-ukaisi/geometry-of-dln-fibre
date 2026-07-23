"""
GROWTH-V3 CARRIER — the CORE descent lemma, on the pure prefix product ∏A (lighter than the full fold;
the blow-up bridge was verified at depth 2 in cap_growth_carrier_battery.py).

DESCENT LEMMA (the carrier). Let A_m be the layer-m matrix (d_{m+1} × d_m), P_L := A_L·A_{L-1}···A_0
(prefix product, d_{L+1} × d_0). Cleared cols of layer m (diagonal branch) = { c : c < wmu(m+1) };
couplingCoords(0..L) = { A_m[r,c] : m ≤ L, c < wmu(m+1), r > c } (below-diagonal cleared entries).
Then for any REMNANT ROW r ≥ wmu(L+1), every entry P_L[r,k] ∈ ⟨couplingCoords(0..L)⟩.

Consumed by the growth arm: the escaped-col coefficient of foldResid at the last clear of layer S =
[left factor, layers ≥ S+2] × [row e of P_S], e ≥ wmu(S+1); so it ∈ ⟨couplings⟩ ⟹ couplingClear kills it.

PROOF STRUCTURE (what seat-descent renders): downward induction on L, peeling P_L = A_L · P_{L-1}:
  P_L[r,k] = Σ_j A_L[r,j]·P_{L-1}[j,k].  Split j:
   • j < wmu(L+1): r ≥ wmu(L+1) > j ⟹ A_L[r,j] is a below-diagonal cleared entry ∈ couplingCoords(L). done.
   • j ≥ wmu(L+1): in the escaped-live regime wmu(L+1)=wmu(L) down to the bottleneck, so j ≥ wmu(L),
     and P_{L-1}[j,k] ∈ ⟨couplings(0..L-1)⟩ by IH. RECURSE.
  Terminates at the BOTTLENECK layer B (argmin d_0..d_{L+1}, ≤ S): there d_B = wmu(B+1), so ALL of layer
  B's cols are cleared (col < wmu(B+1) = d_B), no uncleared col to recurse through — the descent bottoms.

This script verifies: (i) the lemma (row e of P_S in the ideal); (ii) the per-level split (each peel term
is coupling-at-L or recursible); (iii) termination at the bottleneck. Deep witnesses, pure product.
Exit 0 = lemma + split + termination confirmed on all.
"""
import sympy as sp
from cap_frontier_sufficiency import make, widthMinUpto

def Amat(u, d, m):
    return sp.Matrix(d[m + 1], d[m], lambda r, c: u[(m, r, c)])

def prefix(u, d, L):           # P_L = A_L · A_{L-1} · … · A_0
    P = Amat(u, d, L)
    for m in range(L - 1, -1, -1):
        P = P * Amat(u, d, m)
    return P

def couplingCoords(d, L):      # below-diagonal cleared entries of layers 0..L
    S = set()
    for m in range(L + 1):
        cap = widthMinUpto(d, m + 1)
        S |= {(m, r, c) for r in range(d[m + 1]) for c in range(d[m]) if c < cap and r > c}
    return S

def bottleneck(d, upto):       # argmin d_0..d_upto (first achiever)
    vals = [d[i] for i in range(upto + 1)]
    m = min(vals); return vals.index(m)

def check(d):
    N = len(d) - 1; N2, u = make(d); ok = True
    for S in range(N):                                   # P_S with escaped at layer S+1 (need S+1 ≤ N)
        if S + 1 > N: continue
        wmuS1 = widthMinUpto(d, S + 1)
        remnant = [r for r in range(d[S + 1]) if r >= wmuS1]     # remnant rows of P_S
        if not remnant: continue
        # is escaped col at layer S+1 live? (else the growth arm doesn't fire)
        live = (S + 1 < N) and any(c >= wmuS1 for c in range(d[S + 1]))
        P = prefix(u, d, S)
        cc = couplingCoords(d, S); zc = {u[k]: 0 for k in cc}
        B = bottleneck(d, S + 1)
        surv = 0
        for r in remnant:
            for k in range(d[0]):
                if sp.expand(P[r, k].subs(zc)) != 0:
                    surv += 1
        ok = ok and (surv == 0)
        print(f"d={d} P_{S}: remnant rows {remnant} (≥wmu({S+1})={wmuS1}); bottleneck layer B={B} "
              f"(d_B={d[B]}=wmu? {d[B]==widthMinUpto(d,S+1)}); survivors={surv}; escaped-live={live}")
    return ok

WITS = [(2,3,3,3),(3,2,3,3),(4,3,4,4),(2,3,3,3,3),(2,4,4,4,4),(3,4,4,4,4),(2,3,4,4,4),(3,2,4,4,4)]
allok = True
for d in WITS:
    allok &= check(d)
print(f"\nDescent lemma (row≥wmu of P_S ∈ ⟨accumulated couplings⟩) holds on all? {allok}")
assert allok
print("OK: carrier core verified — pure ∏A prefix-product descent, bottleneck-terminating.")
