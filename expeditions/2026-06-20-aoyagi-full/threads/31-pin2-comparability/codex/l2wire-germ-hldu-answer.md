**GOAL 1**

No real obstruction. The support point is available: `0 ∈ tsupport` follows from `ContDiffBump.tsupport_eq` and `Metric.mem_closedBall_self`.

```lean
have h0supp :
    (0 : DeepestSplit H r (deepestNGauge H r)) ∈
      tsupport (fun y => ((cutoffBumpSplit H r hr hL) y : ℝ)) := by
  rw [(cutoffBumpSplit H r hr hL).tsupport_eq]
  exact Metric.mem_closedBall_self
    (le_of_lt (cutoffBumpSplit H r hr hL).rOut_pos)

have hraw_at0 : ContinuousAt (psiSplitRawL2 H r hr hL)
    (0 : DeepestSplit H r (deepestNGauge H r)) := by
  have hδ := contDiffAt_psiSplitDeltaL2_of_mem_tsupport H r hr hL 0 h0supp
  have hcd : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => psiSplitDeltaL2 H r hr hL q + q) 0 :=
    hδ.add contDiffAt_id
  have heq : (fun q => psiSplitDeltaL2 H r hr hL q + q)
      = psiSplitRawL2 H r hr hL := by
    funext q
    rw [psiSplitDeltaL2, sub_add_cancel]
  rw [heq] at hcd
  exact hcd.continuousAt
```

Then the germ membership itself:

```lean
have hcomp : ContinuousAt (fun x => psiSplitRawL2 H r hr hL (split x)) wstar0 := by
  have hs : ContinuousAt split wstar0 := split.continuous.continuousAt
  have hraw_at_split : ContinuousAt (psiSplitRawL2 H r hr hL) (split wstar0) := by
    simpa [hsplit_base] using hraw_at0
  exact hraw_at_split.comp hs

have htend : Filter.Tendsto (fun x => psiSplitRawL2 H r hr hL (split x))
    (nhds wstar0) (nhds (0 : DeepestSplit H r (deepestNGauge H r))) := by
  simpa [hsplit_base, psiSplitRawL2_zero H r hr hL] using hcomp

exact htend.eventually_mem
  (Metric.closedBall_mem_nhds 0 (cutoffBump H r hr hL).rIn_pos)
```

For the `l2ExtraRadius` event:

```lean
have hsplit_tend : Filter.Tendsto split (nhds wstar0)
    (nhds (0 : DeepestSplit H r (deepestNGauge H r))) := by
  simpa [hsplit_base] using (split.continuous.continuousAt : ContinuousAt split wstar0)

exact hsplit_tend.eventually_mem
  (Metric.ball_mem_nhds 0 (l2ExtraRadius_pos H r hr hL hL2))
```

Names verified locally: `ContinuousAt.comp`, `ContDiffAt.continuousAt`, `ContDiffAt.add`, `contDiffAt_id`, `Filter.Tendsto.eventually_mem`, `Metric.closedBall_mem_nhds`, `Metric.ball_mem_nhds`, `ContDiffBump.tsupport_eq`, `Metric.mem_closedBall_self`.

**GOAL 2**

Composition order:

1. Define `C := Function.update ... lastLayer ((1 - l2K ...) * l2S1 ...)`.
2. Use `prod_deepestM_eq_two_of_L2` on `C`, then clean casts with:
   ```lean
   rw [prod_deepestM_eq_two_of_L2]
   rw [show finCongr _ = Equiv.refl _ from finCongr_refl _]
   erw [Matrix.reindex_refl_refl]
   ```
   following the `RouteMFrontPeel` pattern.
3. Build the framed Schur side:
   ```lean
   let Mw := endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm x) - B) * endpointQL H hL Qf
   let Mhat := prod H (framedParamsPivot H r hr hL J Pf Qf q)
   ```
   get `hsplit` from `framedReindexProd_corner_split ... hframe hinterface hS3b`.
4. Get `hGG : Mhat = G0 * G1` from the L=2 full-product peel of `framedParamsPivot`.
5. Install the three local `[Invertible ...]` instances, e.g. from `M.invertibleOfIsUnitDet` / existing unit facts.
6. Apply:
   ```lean
   have hR :=
     rcore_schur_factor_of_corner_split Mw Mhat eR eMid eC G0 G1 hGG hsplit
   ```
7. Finish by a readback equality identifying the two factors from `prod_deepestM_eq_two_of_L2` with the two Schur factors on the RHS of `hR`, then `rw [← Matrix.mul_assoc]` as needed.

Precise obstruction if not already banked: you need a single readback-tie lemma of the shape

```lean
prod (deepestM H r) C =
  SchurFactor0(eR,eMid,G0) * (1 - Khat) * SchurFactor1(eMid,eC,G1)
```

in exactly the same `G0 G1 eR eMid eC` dictionary as `rcore_schur_factor_of_corner_split`. Without that, GOAL 2 is not just lemma composition. The likeliest snag is this cleaned-tuple-vs-framed-Schur-factor alignment, with `Fin 2`/`deepestM` reindex casts as the local type-level pain. Also, if endpoint triangularity only gives off-diagonal zero, `schur_frame_transform` leaves bottom-right factors `D_P * _ * D_Q`; you need those factors to be identity/cancelled or absorbed in the readback lemma.

**Rank:** GOAL 1 is much lower risk and should land first.