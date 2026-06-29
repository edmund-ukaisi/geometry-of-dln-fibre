# #159 HANDOFF SPEC — the smeared `phi_sm_M` chart + F=z²U (for genm-smeared2)

**For:** a fresh hand (genm-smeared2), off `origin/genm-smeared-perfamily @38c5df40` (my banked base).
**Gate:** controller spec-validates the construction + cast plan + the M-dependence (stratum) scope BEFORE spawn.
**I (genm-assemble) am the context-resource after** (the coreSet wiring, the (2,3,1) precedent, the telescoping).

## 0. SCOPE — which stratum the smeared chart covers (the M-dependence, RESOLVED)

The R1-LOWER achiever box-divergence splits by stratum:
- `deepRank M = deepRows M` (CLEAN): **ALREADY DONE** — `routeMCore_box_diverges_clean`
  (`RouteMBoundaryCleanChartFull:217`), ∀M, via `cleanPhi = pivotBlowupOn` (PURE radial, NO shear) +
  `cleanNodeChart` + `routeMCore_box_diverges_of_nodeChart`. Hyps: `NoInteriorBothDrop M`,
  `deepRank = deepRows`, `1 ≤ minAdm M`, `hMpos`.
- `deepRank M ≠ deepRows M` (SMEARED, the genuine `Λ₀`-shear case): **THIS TASK.** The front-bottleneck `r =
  deepRank < deepRows`, so the deepest factor's top rows route through `Λ₀ = (P₁ᵀP₁)⁻¹P₁ᵀP₂` (rational) —
  the radial blow-up alone doesn't telescope; the shear is required.

So `phi_sm_M = (the cleanPhi radial blow-up) ∘ (the Λ₀-shear)` — i.e. the clean chart's radial pivot PLUS
the smeared shear on the kept rows. M-DEPENDENCE FLAG: the stratum split is `deepRank = vs ≠ deepRows` (the
clean condition); the smeared chart's coreSet (kept-row flat-indices) is determined by `deepRank` — pin it
against `deepestCoords`/`deepestPivot` (the clean lineage's coreSet) + the `r = deepRank` top rows.

## 1. The construction `phi_sm_M` (mirror `cleanPhi` + add the shear)

`cleanPhi M = pivotBlowupOn (deepestCoords M) (deepestPivot M)` (RouteMBoundaryCleanChartFull:16) is the
radial half — REUSE it as `R_M`. The smeared chart adds the shear:
`phi_sm_M := paramsEquivFlat ∘ packM ∘ shearM ∘ (the radial reshape)`, where `shearM` = my landed
`measurePreserving_shearM` (`splitOfCoreSet.symm ∘ coreShear[−Λ₀·S_bot] ∘ splitOfCoreSet`, the coreSet =
the `r=deepRank` kept-row flat-indices). The (2,3,1) `chartParams231`/`phi231sm` is the concrete precedent
to generalize (chartA0/chartA1 block reads → opaque widths via the dependent-Fin-cast plan §3).

## 2. The F=z²U factorization (mirror `RouteMBoundaryCleanRate`)

`routeMCore M (cleanPhi u) = (u p)²·U` is DONE for the clean class (`RouteMBoundaryCleanRate:182`,
`cleanLeaf_integrand` RouteMBoundaryCleanChartFull:132). The smeared analog `routeMCore M (phi_sm_M u) =
(u p)²·U(u)` follows the SAME telescoping `P·A^{L−1} = z·P₁H̄` — but with the `Λ₀`-shear absorbing the
`P₂·S_bot` term (the (2,3,1) `prod_chartParams231_entry`:145 is the precedent: `P₁(zH̄ − Λ₀S_bot) + P₂S_bot
= z·P₁H̄`). So the rate is the clean rate's structure + the shear-cancellation `(P₂ − P₁Λ₀)·S_bot = 0`
(needs `P₁Λ₀ = P₂`, the normal-equations identity — genm-splitm/the (1,1)-front-fact precedent
`scalarGram_cancel`). KEY new lemma: `P₁ · ((P₁ᵀP₁)⁻¹P₁ᵀP₂) = P₂` on `{det(P₁ᵀP₁) ≠ 0}` (the projection
identity — Mathlib `Matrix.mul_nonsing_inv` chain).

## 3. The dependent-Fin-cast plan (the [HIGH] opaque-width risk)

The chartA0/chartA1 block reads + the telescoping over opaque `Fin (M k)` widths are the cast-heavy part
(CLAUDE.md's chainA/GenBlk dependent-width trap). Plan: (a) reuse `cleanPhi`/`deepestCoords`/`deepestPivot`
(opaque-width-general already) for the radial half; (b) the shear half rides my `measurePreserving_shearM`
(opaque-width-general, coreSet-driven); (c) the rate's telescoping reuses the clean `cleanLeaf_integrand`
pattern + the projection identity §2. The genuinely-new cast: the `P₁Λ₀ = P₂` block-identity at opaque
widths + threading it through the rate. ≤4 attempts/cast + decorrelated Codex, then report the exact goal.

## 4. The 2 contract fields (the deliverable)

- A (containment): `smearedSubBox p δ ⊆ phi_sm_M⁻¹(cubeBox ε)` — MIRROR `cleanPhi_image_subset_cubeBox`
  (RouteMBoundaryCleanChartFull:100) + the shear's box-enlargement (my `stepShearP_r`/`morseBox` precedent).
- B (hSdiv): the weighted divergence — consume `cleanUbound` (U>0 a.e., DONE) + the monomial atom + the
  F=z²U rate (§2). MIRROR the clean `cleanLeaf_integrand` + `routeMCore_box_diverges_of_nodeChart` assembly.

## 5. The banked base (instantiate, do NOT rebuild)

On @38c5df40: my spine — the matrix-algebra entry-measurability toolkit, `measurable_lamEntry` (Λ₀ ∀width),
`measurePreserving_shearM` (the shear MP, consumes genm-splitm's `splitOfCoreSet`), `smearedSubBox` +
measurableSet. PLUS the clean lineage (sibling, network-free): `cleanPhi`/`cleanPhi_abs_det`/`_hasFDerivAt`/
`_image_subset_cubeBox`/`cleanLeaf_integrand`/`cleanUbound` + `routeMCore_box_diverges_of_nodeChart` (the
M-agnostic assembly) + `RouteMBoundaryCleanRate` (the rate precedent). The fresh hand WIRES these + builds
the §2 projection identity + the smeared rate + the 2 fields. Target: `routeMCore_box_diverges_smeared M
(hsmear : deepRank M ≠ deepRows M) …` = the smeared-stratum analog of `routeMCore_box_diverges_clean`.

## 6. The headline assembly

With A+B, build a smeared `NodeAchieverChart M` (mirror `cleanNodeChart`) → feed
`routeMCore_box_diverges_of_nodeChart` → `routeMCore_box_diverges_smeared`. Together with
`routeMCore_box_diverges_clean` (the other stratum), this completes the R1-LOWER achiever box-divergence ∀M
(both strata). Clean-three or +monomial_rlct (the atom enters hSdiv only). In-repo memory only.
