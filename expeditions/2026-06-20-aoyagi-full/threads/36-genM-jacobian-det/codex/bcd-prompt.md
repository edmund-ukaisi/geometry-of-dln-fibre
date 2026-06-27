# Lean 4 / Mathlib — bricks (b)/(c)/(d): the MINIMAL factor decomposition of phiParamsStruct + its det

## Banked (ARCH-1 spine + per-role CLE engine)
- `bridgeCLE M := (paramsEquivFlatCLE M).symm : (Fin N → ℝ) ≃L Params M`.
- `composeFold_bridge_eq`: any `gs : List (Params M → Params M)` whose `cleConjMap (bridgeCLE M)` factors
  are `fs` gives `composeFold fs = paramsEquivFlat ∘ (gs.foldr (·∘·) id) ∘ paramsEquivFlat.symm`.
- `phiParamsStruct M t ha hN P := chartParamsGen (radialParams P) M t (genBlkParamsStruct P) hle`, and
  `phiParamsStruct (bridgeCLE x) = chartParamsGen (x p) M t (genBlkFlatStruct x) hle`. So the bridge
  `composeFold fs = phiFlatStructV` reduces to `(gs.foldr id) = phiParamsStruct` (Params-level funext).
- `paramsBlockSplitCLE ρ : Params M ≃L (Block → ℝ) × (Rest → ℝ)` (parametric in ρ : ChartIdx ≃ Block⊕Rest).
- det bricks: `cleConjFactor (bridgeCLE M) (conjBlockMap S g) … : ChartFactor N`, det `|det gD ((S(bridgeCLE
  u)).1)|` via conjBlock_abs_det; banked block maps schurFrameMap/lduCoreMap/chainVarMap/radial; banked dets
  schurFrameD_abs_det (|K|^{r+c}), lduCoreD_abs_det (∏|q_i|^{2(t-1-i)}), chainVarD_abs_det (1).
- `phiTarget_abs_det_of_factored phi fs hmap leafH u hdet : |det Dphi| = ∏|u_j|^{leafH j}` (closes cov).

## The structure of phiParamsStruct (= the map I must factor)
`chartParamsGen (u) layer s = reindex (chainA(N_s)(W_s)(C_{s+1}))`, `Params M := ∀ s:Fin L, Matrix(M_s)(M_{s+1})`.
- `chainA N W C = [C − N·W ; W]` (vertical row-stack, LINEAR in (C, W)).
- `C_k = Bmat_k · chainQ(N_k) + u · Rmat_k` (interior), `Bmat_{k+1} = bmatStack(K,X) = [K ; X·K]`,
  `Rmat_{k+1} = rmatPad(E) = [[0,0],[0,E]]`. So `C_{k+1} = [[K, K·N],[X·K, X·K·N + u·E]]` (Schur frame).
- KEY: the radial scalar `u = x p` enters ONLY as `u · Rmat` (linearly, into the bottom-right E-block of C).
- The achiever det target is `|det Dphi| = |x p|^{minAdm-1} · (spectator LDU/Schur monomials)`, threshold-
  relevant entry `leafH p = minAdm-1` only.

## The CONFUSION I must resolve (Q1, the make-or-break)
In the (4,4,2,2)/(3,3,4) anchors the chart was an explicit `pivotBlowupOn` (coords multiplied by u_p), giving
det `|u_p|^{minAdm-1}` cleanly. But `phiParamsStruct` has `u = x p` entering LINEARLY (u·Rmat), NOT as a
coordinate blow-up. How does `|det Dphi| = |x p|^{minAdm-1}` arise?
- The loss is `(x p)²·U` ⟹ `prod = (x p)·H` (one power per entry). But the DETERMINANT of the chart map
  Dphi w.r.t. ALL flat coords (incl x p) — how many powers of x p does it carry?
- Hypothesis A: the E-block has `minAdm` entries; `C`'s bottom-right is `X·K·N + (x p)·E`, so ∂C/∂E = (x p)·I
  on the E-slots — i.e. the map SCALES the E-coordinates by `x p` (a blow-up in disguise), contributing
  `|x p|^{#E entries}` = `|x p|^{minAdm}`?? But target is `minAdm-1`. The pivot coord x p ITSELF is one of
  the slots (the radial), so the Jacobian row/col for x p is special → `minAdm-1` net. Is that right?
- Hypothesis B: x p is a SEPARATE coordinate (not one of the E-slots); the E-slots are scaled by x p, and the
  x p coordinate maps to itself somewhere → `minAdm` from E minus overcounting?

QUESTION 1: derive EXACTLY how `|det Dphi| = |x p|^{minAdm-1}·(spectators)` arises from `phiParamsStruct`'s
structure (the u·Rmat linear entry). Which coordinates does the Jacobian scale by x p, and what is the net
power? Is the radial pivot x p a DISTINCT slot from the E-block, or IS it (one of) the E-slot(s)? (In
genBlkFlatStruct the E-block is read from frame slots via readE; the radial pivot p = ⟨0,hN⟩ is flat coord 0
— is flat coord 0 one of the readE slots, or separate? This determines minAdm vs minAdm-1.)

## Q2: the MINIMAL factor decomposition for the det
Given Q1, what is the cleanest factor list `gs` (deepest-first foldr) such that (i) `gs.foldr = phiParamsStruct`
(bridge, provable funext-s on (2,2,2)) AND (ii) the per-factor dets multiply to `|x p|^{minAdm-1}·spectators`?
Options:
- A single "radial blow-up" factor scaling the E-slots by x p (det |x p|^{minAdm-1}) + a LINEAR reshape factor
  (det = spectator monomial / ±1) assembling chainA from the scaled blocks? Is the reshape LINEAR (so its det
  is constant = a spectator monomial)? Note chainA is linear in (C,W) but C = Schur frame is NONLINEAR in
  (K,X,N) via products K·N, X·K — so the assembly is NOT linear. Does that force separate Schur/LDU factors,
  or can the products be folded into the "spectator unit" (det ≠ x p, irrelevant to threshold)?
- Concretely for (2,2,2) (Text=[2,2,1,1], Wext=[2,2,2], K/X/N/E all 1×1, W 1×2, minAdm=3): write the minimal
  gs and each factor's det. Is minAdm=3 ⟹ leafH p = 2?

## Q3: the funext-s bridge (c), the riskiest sublemma
The bridge `(gs.foldr id)(P) = phiParamsStruct(P)` by funext s i j. Codex earlier said the riskiest sublemma
is the layer source/target split: `C_{s+1} ⊕ W_s` = top/bottom row split of Params layer s (chainA_apply_
castAdd/natAdd). On (2,2,2): give the cleanest Lean proof shape for ONE layer (s=0): `(gs.foldr P) 0 i j =
(reindex (chainA(N_0)(W_0)(C_1))) i j`, reducing via finSplit/chainA_apply laws. What's the single hardest
cast?

OUTPUT: (1) the exact det derivation (Q1, minAdm vs minAdm-1, which coords scaled); (2) the minimal gs +
per-factor dets (Q2); (3) the (2,2,2) funext-s proof shape + hardest cast (Q3). Flag inference vs fact;
be concrete and Lean-level. This decides whether (b)/(c)/(d) is days or a wall.
