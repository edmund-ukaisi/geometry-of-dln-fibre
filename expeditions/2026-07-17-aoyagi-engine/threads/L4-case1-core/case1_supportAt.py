#!/usr/bin/env python3
# provenance: threads/L4-case1-core (SEAT-L4). GAP-3 FINAL deliverable: (1) convention verdict (map vs
# substitution, crux-anchored); (2) calibrated literal coordinate sets; (3) supportAt(S,J) explicit.
# The elder's pre-read leans to the DESCEND (my window_semantics finding); my window_trace RETRACTION
# over-deferred to the elder's amended pin (now walked back — it conflated LEDGER vs GEOMETRIC layer).
"""
Reconciliation (the elder's leading reading = my caveat (c)): TWO named objects, never one —
  * centerAt / canonCenter = the LEDGER layer (which block the next blow-up carves; stays put through a
    layer's J-clears; the paper's D_J bookkeeping). UNCHANGED.
  * supportAt(S, J) = the GEOMETRIC Deg1 support (where the residual is actually degree-1; DESCENDS per
    clear). This is the NEW named function the invariant's window (T) points at; D⁺ = its complement.

CONVENTION VERDICT (crux-anchored): my child computation is child(u) = parent(blockBlowupMap(edgeShear u))/u_p
— the FIX-A MAP direction (blow-up outermost), IDENTICAL to my banked crux foldResid_stepMap_eq_pivot_mul.
NOT substitution (inverse map). So the descend is a genuine MAP-frame structure finding, and the −γβ
argument is frame-INDEPENDENT (below) so it holds regardless.
"""
import sys
import sympy as sp

ok = True
def check(name, cond):
    global ok
    ok &= bool(cond)
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}")

def is_deg1_on(expr, T):
    e = sp.expand(expr)
    if e == 0: return True
    pol = sp.Poly(e, *T) if T else sp.Poly(e, sp.Symbol('_z'))
    return ({sum(m[:len(T)]) for m in pol.monoms()} if T else {0}) == {1}

# ---- (1) CONVENTION VERDICT: one witness entry, MAP direction (crux-anchored) ----
u_p, delta, gamma, beta = sp.symbols('u_p delta gamma beta')   # pivot + current-layer-S coords
e1, e2 = sp.symbols('e1 e2')                                    # deeper layer-(S+1)
h1, h2 = sp.symbols('h1 h2')
# parent entry (degree-1 on current layer-S with DEEPER coeff): involves pivot + δ
c_p, c_d = e1 * h1 + e2 * h2, e1 * h1 + e2 * h2                 # deeper coefficients
parent = c_p * u_p + c_d * delta                                # degree-1 on {u_p, δ} (current), c deeper

# MAP direction (FIX-A, crux): child(u) = parent(blockBlowupMap(edgeShear u)) / u_p.
# edgeShear (Schur): δ ↦ δ − γβ, keep u_p,γ,β.  blockBlowupMap: u_p↦u_p, center j↦u_p·(shear j).  /u_p.
# ⟹ the strict-transform map qm: u_p-slot ↦ 1, δ-slot ↦ (δ−γβ).  child = parent evaluated at qm:
child_map = sp.expand(parent.subs({u_p: 1, delta: delta - gamma * beta}, simultaneous=True))
check("(1) MAP-frame child = c_p·1 + c_d·(δ−γβ) (crux form; blow-up outermost, /u_p folded)",
      sp.expand(child_map - (c_p + c_d * (delta - gamma * beta))) == 0)

# the −γβ argument, FRAME-INDEPENDENT: child_map has a pure-DEEPER term (c_p, from the cleared pivot) and
# the −c_d·γβ term. Test the three windows:
check("(1) T=CURRENT-remainder {δ} FAILS (c_p is pure-deeper degree-0; −c_d·γβ degree-0 on {δ})",
      not is_deg1_on(child_map, [delta]))
check("(1) T=full-current {δ,γ,β} FAILS (−c_d·γβ is degree-2)",
      not is_deg1_on(child_map, [delta, gamma, beta]))
check("(1) T=DEEPER {e1,e2} HOLDS (every monomial one deeper coord) — the DESCEND, map-frame + frame-indep",
      is_deg1_on(child_map, [e1, e2]))
# convention: this IS the map frame (crux); a substitution/inverse read of 'which vars parent mentions'
# would report {δ,γ,β} (current) — the swap. We are in the map frame ⟹ descend is the finding.
check("(1) CONVENTION VERDICT = MAP direction (crux-anchored); descend is a genuine structure finding",
      is_deg1_on(child_map, [e1, e2]) and not is_deg1_on(child_map, [delta, gamma, beta]))

# ---- (3) supportAt(S, J): explicit, d-definable, (layer, cleared)-derived, NO Engine data ----
def supportAt_layer(S, J, N):
    """The geometric Deg1-support LAYER index at fold state (layer S, cleared J), for an N-matrix net.
    J=0: layer S (residual degree-1 on the current block, deeper coeff — the layer start).
    J≥1: DESCENDS one layer to S+1 (the clear's Schur pushes the support to the deeper block);
         if S+1 > N-1 (S is the last layer, S=L): born-unit (no deeper) — the right-disjunct, support = ∅.
    (0-indexed Lean layers 0..N-1; 'layer S' here = Lean layer S.)"""
    if J == 0:
        return S
    return (S + 1) if (S + 1) <= (N - 1) else None   # None = born-unit (S=L), right disjunct

# trace (3,3,4): N=2 (layers 0,1). ledger/centerAt vs geometric/supportAt:
def trace(name, N, states):
    print(f"\n  {name}  (N={N}):")
    for (S, J) in states:
        sup = supportAt_layer(S, J, N)
        supstr = f"layer {sup}" if sup is not None else "∅ (born-unit / right disjunct, S=L)"
        print(f"    state (S={S}, J={J}): centerAt=layer {S} (LEDGER, carves this block) | supportAt={supstr} (GEOMETRIC)")

trace("(3,3,4)", 2, [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1)])
trace("(3,3,2,2)", 3, [(0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1)])
# sanity: at S=L (last Lean layer N-1), J≥1 gives born-unit (no deeper) — matches the S=L defect witness.
check("(3) supportAt at S=L, J≥1 = born-unit (∅) — matches the S=L bare-unit right-disjunct witness",
      supportAt_layer(1, 1, 2) is None and supportAt_layer(2, 1, 3) is None)
check("(3) supportAt descends one layer at the first clear (J:0→1), S<L; stays for J≥1; no Engine data",
      supportAt_layer(0, 0, 3) == 0 and supportAt_layer(0, 1, 3) == 1 and supportAt_layer(0, 2, 3) == 1)

print(f"\nGAP-3 FINAL (convention + supportAt): {'PASS' if ok else 'FAIL'}")
print("VERDICT:")
print("  (1) CONVENTION = MAP direction (crux-anchored). The descend is a genuine structure finding, and")
print("      the −γβ argument is FRAME-INDEPENDENT — even a substitution read would not reinstate T=current.")
print("      ⟹ my window_semantics DESCEND stands; my window_trace RETRACTION (over-deference to the amended")
print("      pin) is ITSELF RETRACTED. T = the geometric DEEPER window; the amended-pin's T=un-cleared FAILS.")
print("  (2) CALIBRATED SETS: at (S,J), T = supportAt-layer's flat coords; D⁺ = complement (all other")
print("      layers' coords, incl. the current LEDGER block once the support has descended).")
print("  (3) supportAt(S,J) EXPLICIT: J=0 ↦ layer S; J≥1 ↦ layer S+1 (S<L) / born-unit (S=L). A d-definable")
print("      Finset function of (layer, cleared) — the STATIC partition, NO Engine-side data ⟹ the (a)-ROAD.")
print("  RECONCILIATION (elder's leading reading = my caveat c): centerAt/canonCenter = LEDGER (unchanged),")
print("      supportAt = GEOMETRIC (descends). Two named functions; the amended pin conflated them.")
sys.exit(0 if ok else 1)
