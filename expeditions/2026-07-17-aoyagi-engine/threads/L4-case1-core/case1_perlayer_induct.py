#!/usr/bin/env python3
# provenance: threads/L4-case1-core (SEAT-L4). LOCK/CORRECT arch-C's PerLayerDeg1 render for the parent-h
# tighten: does PerLayerDeg1 over ALL layers INDUCT under the δ=1 clear, or must it be over ≥ support-layer?
"""
arch-C proposed: PerLayerDeg1 d f V := ∀ ℓ, AffineOn f (layerCoords d ℓ) V  (deg≤1 in EVERY layer).
Deg1SupportedSlot := (∃c support-decomp on S) ∧ PerLayerDeg1 (resid j).
Question (1): does the child (= foldResid_p(qm), qm = blockBlowupCoordQuot pivot · ∘ blockShear φ) satisfy
PerLayerDeg1, i.e. does the form INDUCT? Concern: the Schur δ↦δ−γβ makes the CLEARED layer degree-2.

Model layers: S (carve = {p,ga,be,de}); S+1 (child support = {s1}); S+2 (deeper = {e}).
Parent = PerLayerDeg1 (deg-1 per layer, multilinear): a representative slot = de·s1·e (one factor per layer).
"""
import sys
import sympy as sp

ok = True
def check(name, cond):
    global ok; ok &= bool(cond)
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}")

p, ga, be, de = sp.symbols('p ga be de')     # layer S (carve)
s1 = sp.Symbol('s1')                          # layer S+1 (child support)
e = sp.Symbol('e')                            # layer S+2 (deeper)
layers = {0: [p, ga, be, de], 1: [s1], 2: [e]}   # layer index → coords

def maxdeg_in(expr, X):
    ex = sp.expand(expr)
    if ex == 0 or not X: return 0
    return max((sum(m) for m in sp.Poly(ex, *X).monoms()), default=0)

def per_layer_deg1(expr, from_layer=0):
    """deg ≤ 1 in every layer ℓ ≥ from_layer."""
    return all(maxdeg_in(expr, layers[l]) <= 1 for l in layers if l >= from_layer)

def child(shear_disp, resid):
    B = {c: c + shear_disp.get(c, 0) for c in sum(layers.values(), [])}
    qm = dict(B); qm[p] = sp.Integer(1)
    return sp.expand(resid.subs(qm, simultaneous=True))

resid = de * s1 * e     # parent slot: deg-1 per layer (multilinear)
check("parent is PerLayerDeg1 over ALL layers (multilinear, deg-1 each)", per_layer_deg1(resid, 0))

schur = {de: -ga * be}   # the construction Schur fold (within carve = layer S)
ch = child(schur, resid)
print(f"    child = {ch}")

# (1a) PerLayerDeg1 over ALL layers — does it hold for the child? (arch-C's proposed form)
check("(1a) child PerLayerDeg1 over ALL layers — arch-C's form: EXPECT FAIL (Schur γβ makes layer S deg-2)",
      not per_layer_deg1(ch, 0))
check("    confirm: child is DEGREE-2 in the cleared layer S {p,ga,be,de} (the γ·β term)",
      maxdeg_in(ch, layers[0]) == 2)

# (1b) PerLayerDeg1 over layers ≥ child support-layer (= 1) — the CORRECTED form
check("(1b) child PerLayerDeg1 over layers ≥ S+1 (child support layer): HOLDS (layer S is below, exempt)",
      per_layer_deg1(ch, 1))
check("    deg in child support layer S+1 {s1} is ≤ 1", maxdeg_in(ch, layers[1]) <= 1)
check("    deg in deeper layer S+2 {e} is ≤ 1", maxdeg_in(ch, layers[2]) <= 1)

# (∃c) support decomposition on S' = {s1} (child support): child = ∑_{i∈S'} c_i·u_i, vanishes at S'=0?
check("(∃c) child vanishes at child-support s1=0 (⟹ deg-1 no-constant on S', the ∃c decomposition)",
      sp.expand(ch.subs(s1, 0)) == 0)

# INDUCTION check: parent PerLayerDeg1-over-≥S (=0) → child PerLayerDeg1-over-≥(S+1) (=1). Threshold advances.
check("INDUCT: parent ≥S=0 ✓ → child ≥S+1=1 ✓ (threshold advances with the descend; cleared layer drops out)",
      per_layer_deg1(resid, 0) and per_layer_deg1(ch, 1))

print(f"\nPerLayerDeg1 induction check: {'PASS' if ok else 'FAIL'}")
print("ANSWER TO arch-C (question 1): PerLayerDeg1 over ALL layers does NOT INDUCT — the Schur δ↦δ−γβ makes")
print("  the CLEARED carve layer S degree-2 in the child. CORRECTION: PerLayerDeg1 must be over layers")
print("  ≥ the SUPPORT layer (the cleared/cofactor layers below the support are allowed degree-2). With")
print("  that threshold the form INDUCTS (parent ≥S → child ≥S+1, threshold advances with the descend),")
print("  supplies conjunct-B (∃c on S' gives deg-1+vanishing on the support; PerLayerDeg1-≥S' gives the")
print("  per-layer structure for the NEXT descend). The ∃c decomposition STAYS (it gives no-constant on S',")
print("  which PerLayerDeg1's affine form does not). supportLayer is the state-derived layer of supportAt.")
sys.exit(0 if ok else 1)
