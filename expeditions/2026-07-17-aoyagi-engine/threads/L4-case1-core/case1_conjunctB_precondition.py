#!/usr/bin/env python3
# provenance: threads/L4-case1-core (SEAT-L4). The EXACT conjunct-B precondition (arch-C: "the exact pin
# form is YOUR conjunct-B call"). Within-carve (canonShearOf=Pin C) is IDENTITY on S'=L+1, so the S'-grading
# is trivial — but conjunct-B (PerLayerDeg1From from L+1) has a SEPARATE requirement on the shear's
# QUADRATIC cross-term (the Schur δ↦δ−γβ). Feeds the elder's GAP-2 shape ruling.
"""
Within-carve shear writes only the CARVE (layer L) coords: blockShear φ maps de ↦ de + φ(u)_de, where the
Schur displacement φ(u)_de = −γβ is QUADRATIC (γ,β are matrix entries). blockShear φ is IDENTITY on layers
≠ L. The child = foldResid_p(qm) reads the carve coords through this quadratic map, so the child inherits
φ's cross-term. conjunct-B needs the child PerLayerDeg1From from L+1 (deg ≤1 per layer ℓ ≥ L+1).

CLAIM: conjunct-B HOLDS iff the Schur cross-term γβ is confined to layers < L+1 (the cleared CARVE layer L),
below the advanced threshold — the elder-ratified perlayer_induct assumption. If γβ reaches layer ≥ L+1 the
child is degree-≥2 THERE and conjunct-B FAILS. So the within-carve PIN alone (identity on S') is NECESSARY
but NOT sufficient for conjunct-B; it ALSO needs 'the shear's quadratic fold stays in the carve layer'.
Model: de∈L (carve, the sheared coord), s1,s1'∈L+1 (child support), e∈L+2 (deeper).
"""
import sys
import sympy as sp

ok = True
def check(name, cond):
    global ok; ok &= bool(cond)
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}")

p_piv = sp.Symbol('p')                        # pivot (carve L)
de = sp.Symbol('de')                          # carve L: the sheared coord
be, ga = sp.symbols('be ga')                  # carve L: candidate γ,β (Case A)
s1, s1p = sp.symbols('s1 s1p')                # child support S' = layer L+1
e = sp.Symbol('e')                            # deeper L+2
layers = {0: [p_piv, de, be, ga], 1: [s1, s1p], 2: [e]}   # 0=carve L, 1=L+1, 2=L+2

def per_layer_deg1_from(expr, from_layer):
    ex = sp.expand(expr)
    for l, coords in layers.items():
        if l >= from_layer and coords:
            if ex != 0 and sp.Poly(ex, *coords).total_degree() > 1:
                return False
    return True

resid = de * s1 * e     # parent slot (deg-1 per layer)

def child_of(shear_map):
    sheared = {c: shear_map.get(c, c) for c in sum(layers.values(), [])}
    qm = dict(sheared); qm[p_piv] = sp.Integer(1)
    return sp.expand(resid.subs(qm, simultaneous=True))

# ---- Case A: γβ in the CARVE (layer L), below threshold L+1 (elder-ratified perlayer_induct) ----
childA = child_of({de: de - be * ga})     # φ(u)_de = −be·ga, be,ga ∈ carve L
print(f"    Case A (γβ in carve L): child = {childA}")
check("(A) child PerLayerDeg1From from L+1 HOLDS (be·ga is deg-2 in layer L, BELOW threshold ⟹ exempt)",
      per_layer_deg1_from(childA, 1))
check("(A) confirm child IS deg-2 in the carve L (be·ga) — exempt only because L < threshold L+1",
      sp.Poly(sp.expand(childA), p_piv, de, be, ga).total_degree() == 2)

# ---- Case B: γβ reaches layer L+1 (child support) — the FAILURE mode ----
childB = child_of({de: de - s1 * s1p})    # φ(u)_de = −s1·s1', s1,s1' ∈ L+1
print(f"    Case B (γβ in L+1): child = {childB}")
check("(B) child PerLayerDeg1From from L+1 FAILS (s1·s1'·s1 = s1²·s1' is deg-3 in layer L+1)",
      not per_layer_deg1_from(childB, 1))

print(f"\nconjunct-B precondition check: {'PASS' if ok else 'FAIL'}")
print("VERDICT (conjunct-B pin form, seat-L4's call — input to the elder's GAP-2 shape ruling):")
print("  The within-carve PIN (canonShearOf = shearφ identity on S'=L+1) is NECESSARY but NOT SUFFICIENT")
print("  for conjunct-B. conjunct-B (PerLayerDeg1From from L+1) ALSO needs the Schur QUADRATIC cross-term")
print("  γβ confined to layers < L+1 (the cleared carve layer L) — where it is degree-2 but BELOW the")
print("  advanced threshold, hence exempt (the elder-ratified perlayer_induct mechanism). If γβ reaches")
print("  L+1 the child is degree-≥2 there and conjunct-B FAILS (Case B).")
print("  ⟹ the honest conjunct-B pin is TWO facts on canonShearOf's within-carve shear:")
print("     (i)  shearφ IDENTITY on layers ≥ L+1 (identity on S' and deeper) — the within-carve pin;")
print("     (ii) shearφ's displacement (the γβ fold) reads/writes only carve (layer L) coords — so the")
print("          child's only degree-2 damage is in layer L, below the L+1 threshold.")
print("  Both are delivered by 'shearφ supported on the carve block (layer L)'. This is the exact form to")
print("  confirm when arch-C relays the GAP-2/ShearGrades ruling — the ShearGrades-on-S' clause is trivial")
print("  under (i); the LOAD-BEARING content is (ii) + the parent PerLayerDeg1From, not the S'-grading.")
sys.exit(0 if ok else 1)
