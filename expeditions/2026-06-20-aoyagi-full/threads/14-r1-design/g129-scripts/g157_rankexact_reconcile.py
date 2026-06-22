import sympy as sp
# RECONCILE #56 rank-exact scope vs crux2's D1 non-rank-exact v.
# IsDeepLayers (the deepest point) = ∀s rank(v s)=r (rank-EXACT every layer). But a general
# v ∈ optimalSet only needs ∏(v)=B (rank B = r); the INDIVIDUAL layer ranks rank(v s) can be ANYTHING
# ≥ r (as long as the product has rank r). So crux2 is RIGHT: D1's v ranges over optimalSet, where
# rank(v s) VARIES (≥ r), NOT rank-exact. My #56 Part 1 (gauge slice at rank-exact v) covers only the
# rank-exact stratum. Does it cover non-rank-exact v?
print("=== #56 rank-exact vs D1 non-rank-exact v — crux2 is right, reconcile ===")
print("""
optimalSet H B = {v : ∏(v) = B}, rank B = r. A general v ∈ optimalSet has ∏(v) rank r, but the
INDIVIDUAL layer ranks rank(v s) ∈ [r, min(H_s, H_{s+1})] — can be ANY value ≥ r (e.g. a layer can be
FULL rank while the product is rank r, if a later layer drops). So optimalSet is NOT all rank-exact;
the rank-exact locus {∀s rank(v s)=r} is the DEEPEST stratum (the most degenerate), a SUBSET.

⟹ my #56 Part 1 (gauge slice at RANK-EXACT v) covers the rank-exact stratum (incl. the deepest point).
For D1 (a) — rlctAt(deepest) ≤ rlctAt(v) for ALL v ∈ optimalSet, including NON-rank-exact v — Part 1
does NOT directly give the gauge chart at a non-rank-exact v (the gauge slice C_s=[[I_r+X,Y],[Z,T]]
assumes rank(v s)=r; at a higher-rank layer the slice is [[I_{s_s}+X,Y],[Z,T]] with s_s = rank(v s) > r,
a DIFFERENT (larger) regular block). So crux2's broader homogeneous-residual split is REAL.
""")
print("=== BUT does D1 (a) NEED the gauge chart at non-rank-exact v? Re-examine the actual obligation ===")
print("""
D1 (a) = rlctAt(deepest) ≤ rlctAt(v). This is a COMPARISON, not an equality at v. We do NOT need to
COMPUTE rlctAt(v) via a gauge chart — we need rlctAt(deepest) ≤ rlctAt(v). The cleanest route (avoiding
the non-rank-exact gauge chart entirely): the rlctAtOn_mono domination DIRECTLY on the losses at the two
points, WITHOUT charting v. I.e.:
  rlctAt(dlnLoss H B)(deepest) ≤ rlctAt(dlnLoss H B)(v)  via rlctAtOn_mono with
    |dlnLoss near deepest| ≤ |dlnLoss near v| (deepest loss vanishes faster / more degenerate).
This needs ONLY: the deepest loss is pointwise-dominated by the v loss near their basepoints (the
'deepest = min-core' / most-degenerate fact), NOT a gauge chart at v. So #56's Part 1 (gauge chart) is
for the VALUE at deepest (#44 sub-3); D1 (a)'s domination is a SEPARATE rlctAtOn_mono that does NOT
chart v — it compares the raw losses. So D1 (a) does NOT need the non-rank-exact gauge chart!
""")
print("RECONCILE VERDICT: #56 Part 1 (rank-exact gauge chart) is for #44 sub-3 (the deepest VALUE) — it does")
print("NOT need to extend to non-rank-exact v. D1 (a)'s domination (Part 3) is rlctAtOn_mono comparing the")
print("RAW losses dlnLoss H B at deepest vs v — NO gauge chart at v needed. So crux2's non-rank-exact")
print("concern is REAL for 'charting v' but MOOT for D1 (a) IF D1 (a) routes via raw-loss domination (Part 3)")
print("not via charting v (Part 1 at v). The Part-1-at-v framing (my g155) was the WRONG route for D1 (a);")
print("the RIGHT route is raw-loss rlctAtOn_mono. ⟹ #56 Part 1 = #44 sub-3 only; D1 (a) = Part 3 raw-mono.")
