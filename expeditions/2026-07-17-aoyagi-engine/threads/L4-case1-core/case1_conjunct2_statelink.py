#!/usr/bin/env python3
# provenance: threads/L4-case1-core (SEAT-L4). Verify Codex's (decorrelated, xhigh) verdict that
# case1_preserves_stepInv CONJUNCT-2 is FALSE AS STATED for a FREE ed.nextState — the leaf needs a
# state-transition law (DescendView) that ShearGrades does NOT encode; plus a layerwise-affine gap in
# ShearGrades. SETTLE-BEFORE-PROOF-INVESTMENT (statement pressure → route to controller, do not absorb).
"""
Conjunct-2 goal: ∀j, Deg1SupportedSlot (foldResid child) j S' (supportLayerOf ed.nextState), where
S' = supportAt(ed.nextState). Deg1SupportedSlot's ∃c-decomposition forces child = ∑_{i∈S'} c_i·u_i.

GAP 1 (DECISIVE — free ed.nextState). ed.nextState is a FREE TreeEdge field; S' = supportAt(ed.nextState)
is computed from it, with NO hypothesis linking it to p.conState. ShearGrades (hgrade) does NOT encode a
transition (zero shear satisfies it for EVERY S'). So pick the free next state = parent's (L,0): then
S' = blockCoords(L) = P. But the δ=1 child is the STRICT TRANSFORM (pivot p → 1), which SHIFTS support
DOWN one layer (the pivot factor, in layer L, is removed) — so the child lives in layers ≥ L+1, NOT on
blockCoords(L). Codex's witness: F = v_p·v_s·v_e (p∈L, s∈L+1, e∈L+2), case11, zero shear, center={p}.

GAP 2 (ShearGrades too weak for conjunct-B). The layerwise-degree-2 shear σ_s = u_s + u_r² (s,r∈S')
satisfies hgrade (a) [γ_ss=1, γ_sr=u_r, both per-layer-deg1] and (b), yet is degree-2 within the r-layer,
so the child reading σ becomes degree-2 → PerLayerDeg1From (conjunct B) FAILS.
"""
import sys
import sympy as sp

ok = True
def check(name, cond):
    global ok; ok &= bool(cond)
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}")

# ---- layers: L={p, x}, L+1={s}, L+2={e}  (p the pivot; x a spectator layer-L coord) ----
p, x, s, e = sp.symbols('p x s e')
P = [p, x]        # blockCoords(L) = supportAt at cleared=0, layer L
C_next = [s]      # blockCoords(L+1) = the DESCENDED support (what the strict transform lands on)

# ============ GAP 1: free next state kept at (L,0) → S' = P, child NOT supported on P ============
F = p * s * e                                   # parent residual slot: cross-layer product, deg-1 per layer
# hinv-2 holds: F = c_p·p with c_p = s·e (supported on {p}⊆P); per-layer deg-1 everywhere.
check("hinv-2 (A): F = ∑_{i∈P} c_i·u_i holds (c_p = s·e, F = c_p·p)",
      sp.expand(F - (s * e) * p) == 0)
check("hinv-2 (B): F is per-layer deg-1 (deg 1 in each of layers L={p,x}, L+1={s}, L+2={e})",
      all(sp.Poly(F, *g).total_degree() <= 1 for g in ([p, x], [s], [e])))

# δ=1 case11 zero-shear child = strict transform: qm sets pivot p→1, else identity
child_g1 = sp.expand(F.subs({p: 1}))            # = s·e
print(f"    δ=1 child (strict transform, p→1) = {child_g1}")

# FREE next state = (L,0)  ⟹  S' = supportAt(L,0) = blockCoords(L) = P
Sprime_g1 = P
# Deg1SupportedSlot on S'=P requires child = ∑_{i∈P} c_i·u_i, which VANISHES when all P-coords = 0.
child_at_P0 = child_g1.subs({p: 0, x: 0, s: 1, e: 1})   # zero the P-coords, set s=e=1
check("(GAP-1) child = s·e is NONZERO when all S'=P coords are 0 (s=e=1 ⟹ child=1)",
      child_at_P0 == 1)
check("(GAP-1) ⟹ NO decomposition ∑_{i∈P} c_i·u_i can equal the child (RHS=0 at P=0) — conjunct-2 FALSE",
      child_at_P0 != 0)
# Contrast: with the DESCENDED S' = blockCoords(L+1) = {s}, the child IS supported (child = s·e = (e)·s)
check("(GAP-1 fix) with the DESCENDED S'={s}: child = e·s IS deg-1-supported (vanishes at s=0)",
      sp.expand(child_g1 - e * s) == 0 and child_g1.subs({s: 0}) == 0)

# ============ GAP 2: ShearGrades (a)+(b) admits a layerwise-degree-2 shear ============
# S' = {s, r} both in one layer; shear σ_s = u_s + u_r², σ_r = u_r.
r = sp.Symbol('r')
Sprime_g2 = [s, r]
sigma_s = s + r**2
# hgrade (a): σ_s = γ_ss·s + γ_sr·r with γ_ss=1, γ_sr=r (each per-layer-deg1 as a COEFFICIENT: r is deg-1)
gamma_ss, gamma_sr = sp.Integer(1), r
check("(GAP-2) hgrade (a) SATISFIED by σ_s=s+r²: = γ_ss·s + γ_sr·r with γ_ss=1, γ_sr=r",
      sp.expand(sigma_s - (gamma_ss * s + gamma_sr * r)) == 0)
check("(GAP-2) the coefficients γ_ss=1, γ_sr=r are per-layer degree ≤ 1 (hgrade's PerLayerDeg1 clause)",
      sp.Poly(gamma_sr, r).total_degree() <= 1)
# yet σ_s = u_s + u_r² is DEGREE-2 in the layer {s,r} ⟹ not AffineOn ⟹ conjunct-B (PerLayerDeg1) FAILS
check("(GAP-2) yet σ_s = s + r² is DEGREE-2 in layer {s,r} (r² term) — NOT AffineOn ⟹ conjunct-B breaks",
      sp.Poly(sigma_s, s, r).total_degree() == 2)

print(f"\nconjunct-2 state-link + shear-strength check: {'PASS (Codex verdict confirmed)' if ok else 'FAIL'}")
print("VERDICT: case1_preserves_stepInv conjunct-2 is FALSE AS STATED for a FREE ed.nextState.")
print("  GAP-1 (decisive): the δ=1 strict transform SHIFTS support L→L+1 (pivot factor removed), so the")
print("    child is Deg1-supported on blockCoords(L+1), NOT on an arbitrary S'. A free ed.nextState kept")
print("    at (L,0) gives S'=blockCoords(L), on which the child (=s·e) is NOT supported (nonzero at P=0).")
print("    ShearGrades does NOT encode the transition (zero shear satisfies it for every S'). NEEDS a")
print("    state-link hypothesis DescendView(p.conState, ed.nextState) [construction: layer'=layer,")
print("    cleared'=cleared+1] — ABSENT from the leaf.")
print("  GAP-2: ShearGrades (a)+(b) admits a layerwise-degree-2 shear (σ_s=s+r²) ⟹ conjunct-B can fail;")
print("    needs a LayerwiseAffine clause (shear affine per layer), not just per-layer-deg1 coefficients.")
print("  GAP-3 (δ=1, noted by Codex): the parent witness on P gives no C-factor after qm kills the pivot;")
print("    needs a fold-specific 'next-layer support' fact (parent ALSO supported on blockCoords(L+1)).")
sys.exit(0 if ok else 1)
