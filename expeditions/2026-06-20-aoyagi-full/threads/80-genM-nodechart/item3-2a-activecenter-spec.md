# (a) active-center genBlkFlatLive — design spec (before deep-fill)

Branch genm-interior @2f856e0d. Owning (a) in RouteMFlatLive.lean (hands OFF RouteMBudget.lean — fresh
agent owns the budget cast-assist). Spec-first because the active-center dispatch over opaque widths is a
fresh design dimension with a known cast-thrash history.

## What the DET actually needs (the minimal (a))
The cov target: |det Dφ| = u^{minAdm−1}·(u-free monomial). The radsep mechanism (genm-budget, position-
agnostic): Phi affine in u; the minAdm−1 angular columns each carry factor u (the free R-block entries
scaled by u·Rmat / u·Rfin); the chainA shear is unipotent; one coord = u (radial), one angular fixed = 1
(FREE GAUGE). So the DET needs, in the chart:
1. u SHARED across all R-blocks — ALREADY TRUE: Cgen has `C_k = Bmat·chainQ + u·Rmat_k`, `C_L = u·Rfin`
   (the single scalar u = x p threads every residual). genBlkFlatLive inherits this.
2. The free angular R-block coords = minAdm−1 (after one pivot fixed). genBlkFlatLive has free interior E
   (Rmat = rmatPad(readE)) + free leaf Rfin — spanning both families (controller confirmed reading (a)).
3. The fixed pivot + radial-u placement at a NONEMPTY active block.

## The active-center dispatch (the (a) refinement) — TWO candidate realizations
The "degenerate for 71" (Text(L)=0, empty leaf Rfin) issue: where do the pivot+u sit?
- **(R1) decoder-level pivot placement**: fix one R-entry = 1 IN the decoder at the active center p* (the
  witness's deepest-drop p*, RouteMAchieverWitnessInterior — ALREADY computes p* for ALL interior M incl
  the 71). This mirrors B_det3333 (Rmat 1 = e_{33}). Parameterize genBlkFlatLive's fixed-pivot block by p*.
- **(R2) blow-up-level pivot placement**: the decoder keeps ALL R-blocks free (no fixed pivot); the radial
  blow-up chart `pivotBlowupOn active p` (2b-i) sets the pivot coord = u, scales the active set. The "fix
  one to 1" is then the blow-up's pivot coord (the free gauge). The active set = the minAdm coords (the
  R-block slots). This needs the active set + pivot to land on NONEMPTY blocks per M (the dispatch).

## OPEN QUESTION for the controller (avoid building the wrong realization)
Per genm-budget's (2,2,4): "active center = A₀ = u·[[1,h₁],[h₂,h₃]], fixed pivot = the 1, 3 free angular,
det=u³". The "fixed pivot = the 1" reads as a DECODER-level fix (R1) — the leading factor A₀ has a literal
1 in the pivot slot. So genBlkFlatLive should place a FIXED `1` pivot at the active-center block (the
witness's p*), and the radial u multiplies it (u·1 = the u-front). This is R1.

BUT: my current genBlkFlatLive takes `rfin` as a free PARAMETER (decoder-agnostic, for the rate). For the
DET it must instead (i) read the leaf/active-center blocks from x (the Fin N flat coords, the squareness),
and (ii) place the fixed `1` pivot at p*. Q: is (a) = parameterize genBlkFlatLive by p* (the active center,
from the witness's deepest-drop) + fix the pivot=1 there + read the rest free? Or is the squareness/Fin-N
budget (genm-budget's slot-rerouting) part of (a), or is that the parallel budget-agent's RouteMBudget
theorem? I read the controller's framing as: (a) = the pivot+u DISPATCH (R1, reusing the witness's p*);
the squareness/budget-cardinality = genm-budget's theorem (not mine). Confirming before I build R1.

## PLAN (R1, pending confirmation)
- reuse `InteriorDrop`'s deepest-p* (witness) as the active center; place fixed `1` pivot there.
- genBlkFlatLive reads Rfin (ρ≥1) or the p*-interior Rmat (ρ=0) as the active-center fixed-pivot block;
  free angular elsewhere. Dispatch on ρ=Text(L) via the witness's p* (handles leaf vs interior uniformly).
- the rate (decoder-agnostic) is unchanged; the det (2b-i) blows up the p* pivot to u.
