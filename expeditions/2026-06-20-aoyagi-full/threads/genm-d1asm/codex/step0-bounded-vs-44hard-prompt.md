# STEP-0 verify-first: is the L=2 D1 second-peel minor non-degeneracy `hminor₂` bounded, or secretly #44-hard?

Context: formalising RLCT of deep linear network square-Frobenius loss (Lehalleur-Rimanyi / Aoyagi). L=2 means a 3-layer factorization B = A1·A0 (widths H0,H1,H2). At an optimal v with prod(v)=B and rank(B)=r, we want a lower bound rlctAt(deepest) <= rlctAt(v) ("D1 >=-leg"). The route is a TWO-PEEL IFT chart reduction.

## Established (sorry-free Lean theorems, I verified):
- FIRST peel `dln_hchart_residual`: charts the loss at v into `sum_{nReg} s^2 + ||q||^2` where nReg = r(H0+H2-r), q a C^1 residual vector (the loss entries (i,j)). This is FULLY PROVEN. Its only input is `hminor`: an invertible nReg x nReg minor of the flat Jacobian `jacFlatL2 H v` (rows = loss entries Fin H0 x Fin H2, cols = flat coords).
- `exists_jacFlatL2_minor`: FULLY PROVEN — the first-peel minor EXISTS at a general optimal v. Mechanism: a RANK LOWER BOUND `nReg <= rank(jacFlatL2)` (theorem `nReg_le_finrank_range_jointDiffL2`), then the banked determinantal engine `exists_submatrix_det_ne_zero_of_le_rank` extracts the minor. The rank bound is proved by an explicit GAUGE-FIXED LINEAR INJECTION: with B = U·V (rank factorization), embed `(ker ΛL) × Mat(r×H2)` into range(jointDiffL2) via Ψ:(X,Y)↦X·V+U·Y, dim = r(H0-r)+r·H2 = nReg. This is pure linear algebra — NO constant-rank gauge-slice geometry, NO inter-layer diffeo.
- SECOND peel `secondPeel_hchart_residual`: FULLY PROVEN, network-free. Takes a C^2 residual VECTOR h = q(0,·) : (Fin Nslice → ℝ) → EuclideanSpace(Fin n), with h(t0)=0, plus `hminor₂`: an invertible `extra x extra` minor of the Jacobian D h(t0), where extra = extraCount m a b = m(a+b)-ab. Produces the second-peel chart `hchart₂`. The minor is selected from the residual VECTOR's Jacobian (a Jacobian-rank condition), NOT from a Hessian of the scalar ||h||^2.

## The separate wall (#44 / #120):
`DeepestGaugeChart` — the DEEPEST-point chart needs rank-r-EXACT pivots and a grouped inter-layer diffeo (constant-rank gauge slice). That feeds the deepest-side equality #44 (`hDeepest`), a SEPARATE hypothesis, and the general-L #120 wall. The two-peel >=-leg producers take `hDeepest` as a named hyp — they do NOT rebuild it.

## The open piece:
`hminor₂` is consumed as a HYPOTHESIS. There is NO second-peel rank lemma yet (no analog of `nReg_le_jacFlatL2_rank` for the extra block). So to DISCHARGE `hminor₂` as a theorem I'd need: `extraCount m a b <= rank(D h(t0))` where h is the first-peel slice residual at the middle-stratum optimal v, then reuse the SAME determinantal engine.

## THE QUESTION (decision-critical):
Is the rank lower bound `extraCount m a b <= rank(D h(t0))` (hence `hminor₂`) dischargeable by the SAME KIND of gauge-fixed linear injection as the first peel (BOUNDED) — i.e. an explicit linear embedding of an extraCount-dimensional space into range(D h(t0)) using the middle-stratum block structure (layer ranks at v exceed deepest rank r by a,b in the two layers; degraded core M'=(m-a,m-a-b,m-b))?

OR does the slice residual h's Jacobian rank at the basepoint SECRETLY require the constant-rank gauge-slice split / inter-layer diffeo (#44-hard / #120-wall), so that D1>= is NOT R1-independent and collapses onto the gauge wall?

Key sub-question: the first peel already straightened nReg directions to coordinates; the slice residual h carries the REMAINING regular directions of the middle stratum (extraCount of them). Is the "remaining regular directions form a rank-extraCount Jacobian block" fact (a) a direct corollary of the same range/finrank gauge-injection argument applied to the residual, or (b) does it need to know the deepest-point normal form (the #44 geometry)?

Please give a crisp BOUNDED vs #44-HARD verdict with reasoning. I want to know if I should proceed to BUILD the extraCount rank bound + hminor₂ discharge as the de-risk, or STOP and report that D1>= waits on #44.
