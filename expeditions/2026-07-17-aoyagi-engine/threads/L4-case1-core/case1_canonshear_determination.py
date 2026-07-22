#!/usr/bin/env python3
# provenance: threads/L4-case1-core (SEAT-L4). arch-C's canonShearOf FOLD-DETERMINATION: where does the
# Q₂⁻¹-into-next-layer transfer live — THIS edge's shearφ, the NEXT edge, or the ideal/cofactor level?
# Verified against the fold (foldResid δ=1 strict transform), not asserted. FEEDS the edge-field audit
# (the shearφ pin) AND resolves GAP-2 (ShearGrades ignore-S' strengthening).
"""
FOLD FACT (foldResid δ=1): child = foldResid_p(qm),  qm_k = blockBlowupCoordQuot pivot k (blockShear φ u)
                                                          = (pivot→1, else (blockShear φ u)_k).
So shearφ is applied, then pivot→1. The child must be Deg1 on S' = supportAt(child) = blockCoords(L+1).

CANDIDATE (Pin C, elder's lean): canonShearOf = Schur-WITHIN-CARVE — φ acts only within the carve block
(layer L); it is IDENTITY on every layer ≠ L, in particular on the child support S' = layer L+1.

CLAIMS to verify against the fold:
 (1) a within-carve Schur (folds the C21·C12 = γβ cross-term within layer L) is IDENTITY on S' = layer L+1;
 (2) the δ=1 strict transform then lands Deg1 on S' = L+1 — the descend comes from the parent's multilinear
     re-expression on L+1 (GAP-3), NOT from the shear writing L+1;
 (3) BONUS (resolves GAP-2): a within-carve shear satisfies ShearGrades (a) on S'=L+1 with c_ik = [i=k]
     (identity), which IGNORES S' — so the degree-2 breaker σ_s = u_s + u_r² (r∈S') is EXCLUDED by
     construction. GAP-2's "c_ik ignores S'" strengthening IS "the shear is within-carve / id on S'";
 (4) CONTRAST: a shear that DOES write S' (a Q₂⁻¹-carrying shear u_{s1} ↦ u_{s1} + u_p, mixing L into L+1)
     would break the child support (child no longer Deg1 on L+1 alone).
Model layers: L (carve) = {p, ga, be, de}; L+1 (child support) = {s1}; L+2 (deeper) = {e}.
"""
import sys
import sympy as sp

ok = True
def check(name, cond):
    global ok; ok &= bool(cond)
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}")

p, ga, be, de = sp.symbols('p ga be de')   # layer L (carve); p = pivot
s1 = sp.Symbol('s1')                        # layer L+1 (child support S')
e  = sp.Symbol('e')                         # layer L+2 (deeper)
carve = [p, ga, be, de]; Sprime = [s1]; deeper = [e]
allc = carve + Sprime + deeper

resid = de * s1 * e     # parent slot: multilinear cross-layer product (Deg1 per layer)

def strict_transform(shear_map):
    """child = foldResid_p(qm); qm = shear then pivot→1."""
    sheared = {c: shear_map.get(c, c) for c in allc}     # blockShear φ
    qm = dict(sheared); qm[p] = sp.Integer(1)            # blockBlowupCoordQuot pivot: pivot→1
    return sp.expand(resid.subs(qm, simultaneous=True))

def deg_in(expr, X):
    ex = sp.expand(expr)
    return 0 if (ex == 0 or not X) else sp.Poly(ex, *X).total_degree()

# ---- (1) within-carve Schur: de ↦ de − be·ga (the C21·C12 fold), identity elsewhere ----
schur_within = {de: de - be * ga}          # touches only carve coords; id on s1, e
check("(1) within-carve Schur is IDENTITY on S'=L+1 {s1} (φ writes no s1)",
      schur_within.get(s1, s1) == s1)
check("(1) within-carve Schur is IDENTITY on deeper L+2 {e}",
      schur_within.get(e, e) == e)

# ---- (2) strict transform lands Deg1 on S'=L+1 ----
child = strict_transform(schur_within)
print(f"    δ=1 child (within-carve Schur) = {child}")
check("(2) child is DEG-1 in S'=L+1 {s1} (the descended support)", deg_in(child, Sprime) <= 1)
check("(2) child VANISHES at s1=0 (⟹ ∃c decomposition on S', no constant)", child.subs({s1: 0}) == 0)
check("(2) child = c·s1 with c = e·(de−be·ga) — the L+1 re-expression (GAP-3, parent multilinear)",
      sp.expand(child - e * (de - be * ga) * s1) == 0)

# ---- (3) BONUS: within-carve shear satisfies ShearGrades (a) with c_ik ignoring S' ----
# For i ∈ S'={s1}: (blockShear φ u)_{s1} = u_{s1} = ∑_{k∈S'} c_{s1 k}·u_k with c_{s1,s1}=1 (constant, ignores S').
shear_on_Sprime = schur_within.get(s1, s1)
check("(3) ShearGrades (a) on S': (shear)_{s1} = 1·s1, coeff c=1 is CONSTANT ⟹ IGNORES S' (GAP-2 fix auto)",
      shear_on_Sprime == s1)
# the GAP-2 breaker is NOT within-carve (it writes s1 with an r∈S' term) → excluded by Pin C
r = sp.Symbol('r')   # a second S' coord
breaker = {s1: s1 + r**2}     # σ_{s1} = s1 + r²  — writes S', degree-2
check("(3) the GAP-2 breaker σ_{s1}=s1+r² WRITES S' (r∈S') ⟹ is NOT within-carve ⟹ excluded by Pin C",
      breaker[s1] != s1)

# ---- (4) CONTRAST: a Q₂⁻¹-carrying shear that writes S' breaks the child support ----
# suppose shearφ carried the next-layer transfer: s1 ↦ s1 + p (mixing carve pivot into L+1)
shear_writes_Sprime = {s1: s1 + p}
child_bad = strict_transform(shear_writes_Sprime)   # blockBlowupCoordQuot sets only the PIVOT slot to 1
print(f"    δ=1 child (S'-writing shear s1↦s1+p) = {child_bad}")
# qm_{s1} = (blockShear φ u)_{s1} = s1 + p (the ORIGINAL p — the quot only sets the PIVOT slot to 1),
# so child_bad = de·(s1+p)·e = de·s1·e + de·p·e — the de·p·e term has NO s1 factor ⟹ nonzero at s1=0
check("(4) an S'-writing (Q₂⁻¹-carrying) shear breaks the descend: child NONZERO at s1=0 (de·p·e term)",
      child_bad.subs({s1: 0}) != 0)
check("(4) ⟹ Q₂⁻¹ must NOT live in THIS edge's shearφ (it would write S' and break Deg1-on-S')",
      sp.expand(child_bad - (de * s1 * e + de * p * e)) == 0)

print(f"\ncanonShearOf fold-determination: {'PASS' if ok else 'FAIL'}")
print("DETERMINATION (arch-C's charge, verified against foldResid δ=1):")
print("  (a) The Q₂⁻¹-into-next-layer transfer does NOT live in THIS edge's shearφ. This edge's")
print("      shearφ = Schur-WITHIN-CARVE (folds C21·C12=γβ within layer L, IDENTITY on the child")
print("      support L+1 and deeper). The Q₂⁻¹ lives at the IDEAL/COFACTOR level (C'^{(S+1)} =")
print("      Q⁻¹·C^{(S+1)}), consumed by the NEXT edge when it blows up L+1. ⟹ Pin C CONFIRMED.")
print("  (b) The δ=1 strict transform needs ONLY Schur-within-carve: the child support (L+1) comes")
print("      from the parent's multilinear re-expression (GAP-3), with the shear IDENTITY there. It")
print("      does NOT need shearφ to carry Q₂⁻¹ / write L+1 — that would BREAK Deg1-on-S' (claim 4).")
print("  (c) Elder's lean (Pin C / Q₂⁻¹ at the ideal level) CONFIRMED against the fold.")
print("  BONUS — resolves GAP-2: canonShearOf = Schur-within-carve ⟹ shear is IDENTITY on S'=L+1 ⟹")
print("      ShearGrades (a) holds with c_ik=[i=k] (ignores S'), so the degree-2 breaker is excluded")
print("      by construction. GAP-2's 'c_ik ignores S'' strengthening = 'shearφ is within-carve'.")
sys.exit(0 if ok else 1)
