<task>
Lean 4 / Mathlib v4.29 (DLNFibre RLCT). I must prove `product_reduction` (L2) — the regular/core split of
the deep-linear-network learning coefficient at the deepest singular point. ROUTE-FIRST: I want the
cleanest PROOF STRUCTURE (the decomposition + which green lemma discharges each step) before grinding.
This is a substantial r>0 lift; flag the hardest sub-step + whether to factor it.

THE GOAL (Skeleton:951, currently sorry):
  theorem product_reduction (H : Fin (L+1) → ℕ) (r : ℕ)
      (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
      (hr : ∀ s, r ≤ H s) (hL : 1 ≤ L) :
      rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL) = ENNReal.ofReal (aoyagiLambda H r)

KEY DEFS:
- dlnLoss H B A = ∑ᵢⱼ ((prod H A − B) i j)²  (squared Frobenius of the layer product minus B).
- aoyagiLambda H r = (−r² + r(H 0 + H last))/2 + lambdaCore (fun s => H s − r).   [ℚ, cast via ofReal]
  So the target = [regular shift nReg/2, nReg = r(H 0 + H last) − r² = r(H 0+H last−r)] + lambdaCore(M), M = H−r.
- lambdaCore M = ½·(Adm M).inf' Mval  (the singular-core value on reduced widths).
- deepestPoint = a Classical.choice witness of IsDeepLayers: w ∈ optimalSet (fibre, prod w = B) ∧ ∀ s, (w s).rank = r (EVERY layer has rank exactly r).

GREEN INGREDIENTS (verified present):
- rlct_additive_smooth_block {n} (G : Y → ℝ) (y0) (hGmeas) (hGne) :
    rlctAtOn (fun p : (Fin n → ℝ) × Y => (∑ i, p.1 i ^2) + G p.2 ^2) (0, y0) = n/2 + rlctAtOn (G²) y0.
    [the n/2 additive Fubini shift — the regular block split]
- block_elimination (H r B hB) : ∃ P Q units, P·B·Q = diag(E_r, 0)  [L1, green — B to rank-r normal form]
- paramsEquivFlat (H) : Params H ≃ᵐ (Fin (flatDim H) → ℝ), measurePreserving + continuous both ways (ParamsFlat.lean). [the Params↔flat bridge]
- rlctAtOn_comp_homeomorph (e : M ≃ₜ M') (he : MeasurePreserving e) (hemb) (F) (w0) : rlctAtOn (F∘e) w0 = rlctAtOn F (e w0). [RLCT transport]
- rlctAtOn_eq_rlctAt (H F w) : rlctAtOn F w = rlctAt H F w  [on Params]
- THE CORE (mine, proven given a RouteMAtlas): routeM_rlctAtOn_eq_lambdaCore : rlctAtOn (dlnLoss M 0) 0 = ofReal(lambdaCore M)  — but this is on the REDUCED widths M = H−r at the all-zero point. [I can take this as a hypothesis / it's the rung below.]

THE MATH (Aoyagi 2013 Thm 3): at the deepest point every layer has rank r. Locally, the rank-r constraint
splits the parameter space into (a) the r-dimensional "regular" gauge directions where the loss is a
nondegenerate quadratic (∑ of nReg = r(H0+Hlast−r) squares — the regular shift nReg/2 via Fubini) and (b)
the reduced (H−r)-width singular core ‖∏ C'‖² whose RLCT is lambdaCore(M). The split is the L2 product
reduction. B of rank r is block-eliminated to diag(E_r,0); near the deepest point the loss ≈ (regular
quadratic block in the r gauge dirs) + (core on the reduced chain). The regular block contributes nReg/2
(rlct_additive_smooth_block), the core contributes lambdaCore (the rung below / my core).
</task>

<output_contract>
  1. The cleanest PROOF STRUCTURE for product_reduction: the chain of steps (change of coords at the
     deepest point → regular/core product form → rlct_additive_smooth_block for nReg/2 → core for
     lambdaCore → ofReal arithmetic), naming which green lemma discharges each. Be concrete about the
     change-of-coordinates that exhibits the (regular quadratic) × (reduced core) product form at the
     deepest point (what is the homeomorphism? the rank-r gauge slice + the reduced chart?).
  2. The HARDEST sub-step (likely: exhibiting the regular/core product form — the local normal form at a
     rank-r deepest point). Is it: (a) a clean change of vars (the gauge slice), or (b) does it need its
     own resolution/blow-up? How hard, and should it factor into a named lemma?
  3. The nReg count: confirm nReg = r(H0 + Hlast − r) = the regular generators, and how it lands as the
     `n` in rlct_additive_smooth_block. Any subtlety (the regular block is r·H0 + r·Hlast − r² — a sum of
     two gauge blocks minus the overlap?).
  4. Is there a SHORTCUT: can product_reduction reduce to the core (routeM_rlctAtOn_eq_lambdaCore on M=H−r)
     + a single regular-shift lemma, or is the r>0 deepest-point normal form genuinely separate heavy work?
  5. Realistic scope: line-count estimate + whether a Codex-2nd-pass / pp-hall consult on the gauge-slice
     normal form is warranted before I grind.
  Under ~550 words. Mark inference vs. fact; don't invent Mathlib lemma names (flag "verify").
</output_contract>

<grounding_rules>
  The green ingredients (signatures as given) are FACT. The math (Aoyagi Thm 3, the rank-r split) is the
  paper's claim — treat as the target to formalise, flag where the Lean lift is non-obvious. Distinguish
  "this composes from green lemmas" from "this needs a new heavy normal-form lemma".
</grounding_rules>
