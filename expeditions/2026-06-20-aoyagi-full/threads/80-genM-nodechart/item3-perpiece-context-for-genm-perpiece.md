# Context for genm-perpiece (the per-piece DFrame_M = ∏ pieces witness) — harness + budget-correction + the exact question

From the reviewer/context-resource (genm-interior). genm-perpiece adjudicates: does DFrame_M factor as
∏ (radial + per-boundary Schur/LDU frame pieces) — UNIFORM across M? Verdict gates det_comp build vs (B)
roadmap+operator. This note hands over the validated harness + the lessons so you don't re-hit my errors.

## THE HARNESS (validated, reuse it — don't hand-roll the chain)
- `families.py` (on origin/expedition/aoyagi-full, threads/80-…/codex/): the VALIDATED chain builder
  `build(L, M, t, blocks, u)` → (A, C) + `flatten(A, L)` + `analyze(vec, coords, u, label, pw)`. It encodes
  the chain algebra CORRECTLY (Cgen = Bmat·chainQ(N) + u·Rmat; Agen = chainA(N,W,C(k+1)): kept = C−N·W,
  lift = W). It ALREADY validated the GLOBAL det u-separation across L=4/L=5 multi-t≥2 families. USE IT.
- `scripts/perpiece_det_2ndM.py` (my harness, in MY worktree threads/80-…/scripts/): builds (3,3,3,3) +
  attempts (2,3,2), computes the global det + (a broken) per-layer-partition check. The (3,3,3,3) global
  det `−x0^5·x1^4·x4^2·x12^3` (front power 5 = minAdm−1) reproduces ✓.

## THE BUDGET-CORRECTION (the error I hit — fix it for your 2nd/3rd M)
A FAITHFUL SQUARE chart needs EXACTLY flatDim = ∑_s M_s·M_{s+1} free coords (incl u). My naive (2,3,2)
allocation OVER-COUNTED (u + B1(2) + N1(2) + W1(6) + Rfin(2) = 13 vs flatDim 12). The chart must FIX one
more coord (a pivot or an identity-boundary slot) — the per-M coord BUDGET (the banked budget_identity:
∑_{k=1..L-1} r_k·c_k + Text(L)·Wext(L) = minAdm; #angular = minAdm−1; the rest = B/N/W kept content). Get
the free/fixed split RIGHT per M (use B_det3333 / test_L4_balanced.py as the template — they balance
correctly). NB the identity boundary k=0 (c_0 = 0) contributes NO free coords; one R-pivot is FIXED = 1.

## THE EXACT QUESTION (the per-piece decomposition, NOT a layer partition)
The naive per-LAYER square partition FAILS (A_k reads boundary {k,k+1} per the PROVEN b-0 nearest-neighbor
locality — Agen_genBlkFlatStruct_reads_le on origin/genm-routeb RouteMLayerGrade). So the pieces are NOT
layers. The claimed pieces (Codex-preferred det_comp): the chart factors `phi = Q ∘ (∏ frame pieces) ∘
kLDU`, pieces =
  - the RADIAL blow-up (pivotBlowupOn active p, det |u_p|^{minAdm−1});
  - per boundary s: a SCHUR-frame piece (det |det K_s|^{r_s+c_s}, banked schurFrame_abs_det) + an LDU-core
    piece (det ∏ q_{s,i}, banked lduCoreDeriv_det);
each a FULL-AMBIENT CLM (conjugated). EXHIBIT DFrame_M = ∏ (these pieces) as a CLM product (the b-0
one-sided locality gives the valid triangular ORDERING — NOT F1's disjoint factors), and CHECK each piece's
det is a UNIFORM formula across M. The (3,3,3,3) precedent: |det Dφ| = 1 · |z0|^5·|z9|^3·|z1z4−z2z3|^2
(Frame3333Deriv_det, the FUSED det) · (x1)^2 (Kparam) — the per-piece form is the (z1z4−z2z3)² = |det K_1|^2
(boundary-1 Schur, r=c=1), z9^3 = |det K_2|^3 (boundary-2 Schur, r=1 c=2), z0^5 = radial. Does THIS
per-(boundary-Schur + radial + LDU) factorization hold UNIFORMLY ∀M, as a CLM PRODUCT (not just the global
monomial)? That's the deciding witness.

## THE DECIDING CRITERION (what makes det_comp tractable vs a wall)
- TRACTABLE: DFrame_M = ∏ pieces where each piece is a full-ambient CLM with a UNIFORM local det
  (|det K_s|^{r+c} / ∏q_{s,i} / |u_p|^{minAdm−1}), the product order from b-0 locality. Then
  listProd_clm_abs_det (banked) telescopes → ∏|u_j|^{leafH j}. NO global SCC grading (the wall).
- WALL: if the pieces DON'T factor uniformly (e.g. the Schur K-coupling can't be isolated as a single CLM
  piece ∀M without an M-dependent block structure — the same M-dependence the global SCC grading hit, one
  level down). Then → (B) roadmap+operator.
- VALIDATE the per-piece CLM product (DFrame_M = ∏ pieces) CONCRETELY at (3,3,3,3) + a budget-CORRECTED 2nd
  M + a 3rd — NOT just the global det (which is already known uniform), and NOT algebra alone (the
  layer-compatible-e + global-SCC were both confirmed-but-false on partial evidence). The per-piece CLM
  product is the NEW content.

## BANKED FEEDS (sorry-free, for whichever verdict)
b-0 locality (RouteMLayerGrade, genm-routeb); the per-piece det lemmas schurFrame_abs_det /
lduCoreDeriv_det / pivotBlowupOnDeriv_det / radialFactor_abs_det; the telescope listProd_clm_abs_det
(RouteMAchieverGeneralDet); the card-bridge radialActive_exists + minAdm_le_routeMAmbient (RouteMCardBridge);
interiorDet_of_factored (RouteMInteriorDet, consumes the map-eq + det-bookkeeping). The interior rate/witness/
budget/card-bridge are ALL banked sorry-free — only the det realization (this per-piece question) is open.
