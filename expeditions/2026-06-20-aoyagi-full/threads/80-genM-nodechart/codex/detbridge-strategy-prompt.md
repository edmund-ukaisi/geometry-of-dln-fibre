<task>
I am formalising in Lean 4 + Mathlib (v4.29 pin) the last piece of an "interior determinant headline" for
deep linear networks. The target theorem, on a fixed flat space `Fin N → ℝ` (`N = routeMAmbient M`), is:

  |det Dφ_M| = |u_p|^{minAdm M − 1} · ∏_{s : Fin L} ( |det K_s|^{r_s+c_s} · ∏_i |q_{s,i}|^{2(t_s−1−i)} )

where φ_M is the achiever chart `phiGen u M t B hle = paramsEquivFlat M ∘ chartParamsGen u M t B hle`.

KEY STRUCTURE (all confirmed; the linear algebra is fully de-risked and banked):
- `chartParamsGen u M t B hle : Params M` is `fun s ↦ reindex (Agen u M t B hle s.val)`, where
  `Agen … s = chainA (genWidthEq …) (B.Nblk s) (B.Wblk s) (Cgen … (s+1))`.
- `chainA h N W C : Matrix (Fin M') (Fin m') 𝕜` reindexes the vertical block `[ C − N·W ; W ]` (over
  `Fin t ⊕ Fin (M'−t)` via `finSplit`) onto `Fin M'` rows. Entry laws are banked:
  `chainA_apply_castAdd : chainA h N W C (cast (castAdd i)) j = (C − N·W) i j`,
  `chainA_apply_natAdd  : chainA h N W C (cast (natAdd a)) j = W a j`.
- `Cgen u … k = B.Bmat k * chainQ (B.Nblk k) + u • B.Rmat k` (interior), `= u • B.Rfin k` (leaf).
- The chart factors (validated, confirmed realizing at the (2,2,2) and (3,3,3,3) anchors):
    T_M = bsubst_M ∘ shear_M ∘ pb_M
  where pb_M = radial pivot blow-up (det = u^{minAdm−1}), shear_M = a det-1 unitriangular Schur shear
  (the bilinear −dN_s·W_s + Schur KEPT terms, which under a {modified}/{kept} grading land strictly off
  the diagonal block), bsubst_M = the spectator/Schur-frame + LDU-core blow-up. And
    pack_M ∘ T_M = chartParamsGen   (the (2,2,2) anchor `chartParams222_eq_pack_T` is ~200 lines, explicit
    8-vector over Fin 8).

BANKED BRICKS I CONSUME (all sorry-free, axiom-clean):
- `fderiv_det_one_of_shear D b htri hdiag : |det D| = 1` — block-tri + identity-diagonal-blocks ⟹ det 1.
- `lowerTri_det f g h : det (lowerTri f g h) = f.det * g.det` (2-block, linear-map level, in/out bases may
  differ); `lowerTri3_det` (3-block).
- engine dets: `schurFrame_abs_det : |det (schurFrameDeriv X K N)| = |K.det|^{r+c}`,
  `lduCoreDeriv_abs_det : |det (lduCoreDeriv l q u)| = ∏_i |q_i|^{2(t−1−i)}`,
  `radial_abs_det_minAdm`.
- `fderiv_abs_det_eq_prod_diagBlocks` (value-locality ⟹ det = ∏ diag blocks, via toDual∘bLayer grading).
- `chainUnit_det : det (chainUnitMap N) = 1` (the FROZEN-N chaining `(W,C)↦(W,C−N·W)`).

THE OBSTRUCTION ALREADY PROVEN (so I do NOT re-attempt it): a single-grading `Matrix.BlockTriangular`
route is BLOCKED — the INPUT partition (chartIdxEquiv boundary counts schurDim+liftDim) and the OUTPUT
partition (paramsEquivFlat/FlatIdx layer counts M_s·M_{s+1}) genuinely differ (e.g. (6,2) vs (4,4) at
(2,2,2), same total 8). So the det MUST be taken at the LINEAR-MAP level via iterated `lowerTri_det`
(the prodEquivOfIsCompl gluing), NOT via Mathlib `Matrix.BlockTriangular` over a single Fin N grading.

THE RESIDUAL (the cast-heavy zone): define `shear_M` over opaque `chainA`/`Agen`/`Text`/`Wext` widths,
prove it det-1, and build the bridge `pack_M ∘ T_M = chartParamsGen` (the opaque-M generalization of the
explicit (2,2,2) bridge). Then a det_comp assembly. The prior handoff flags this as a "genuine multi-tide
construction, not a ≤4-attempt closure," with a warning about dependent-Fin reindex thrash.

The controller offered an ENGINE-ROUTE ALTERNATIVE: instead of the explicit `Agen`/width expansion in the
bridge, route the per-layer block dets through the abstract `schurFrameD`/`lduCoreD` ENGINE det values.
</task>

<output_contract>
Be concrete and Lean-aware. Sections, in order:

1. RANKED PLAN. Rank the two routes — (A) explicit `shear_M`/`pack_M ∘ T_M = chartParamsGen` bridge over
   opaque widths, vs (B) the engine-route (telescope `det Dφ = ∏ per-layer factor dets` via
   `lowerTri_det`/`listProd_det` on linear-map-level factors, identifying each diagonal block with an
   engine det WITHOUT the explicit width-expansion bridge). For each: what exactly must be constructed,
   where the dependent-Fin casts bite, and the single biggest risk.

2. THE CHEAPEST SOUND DECOMPOSITION. Given that the determinant is necessarily taken at the linear-map
   level (lowerTri / prodEquivOfIsCompl), is there a way to AVOID ever building the explicit `pack_M ∘ T_M
   = chartParamsGen` map-equality bridge — e.g. by computing `det (fderiv φ_M)` directly as a product over
   the chain layers, where each layer's contribution is read off `chainA`'s entry laws + the engine det,
   WITHOUT an intermediate `T_M`/`pack_M`? If the bridge is genuinely unavoidable, say so and explain why
   the (3,3,3,3) `Frame3333Deriv` route (a single hand-built `frameB` grading) does NOT generalize.

3. THE FIRST BANKABLE INCREMENT. What is the single smallest, network-free, sorry-free lemma I should bank
   FIRST that makes real progress and de-risks the cast zone — stated abstractly (over generic
   finite-dim spaces or generic opaque `Fin` widths), so it is reviewer-checkable independent of the
   downstream wiring. Give its Lean signature.

4. CAST-ZONE TACTICS. The specific Mathlib-v4.29 idioms for the dependent-`Fin` reindex zone
   (`finSplit`/`finCongr`/`Fin.cast`/`reindex`/`Matrix.of`), given that entrywise `simp` "no-progress"es
   at opaque widths but fires at explicit `⟨_, by decide⟩` indices.
</output_contract>

<grounding_rules>
You are reasoning about a Lean formalisation you cannot run. Mark any specific lemma name or tactic you
are not certain exists in Mathlib v4.29 as "verify exists". Distinguish a structural recommendation (high
confidence) from a guessed lemma name (low confidence). Do not invent Mathlib API; if unsure whether
something exists, say what to grep for.
</grounding_rules>
