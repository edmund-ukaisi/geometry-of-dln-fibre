# Sub-hand brief #4 — `continuous_kLDU` + `Ubound`/`Umeas`/`image` (the analytic chart facts)

**Base:** branch off `origin/expedition/genm-r1lower` (tip `481d8352` — has merged H2a/H3 + my
`BchartLDU`). Isolated worktree.

**MODULE BOUNDARY:** prove your results as **named atoms in your OWN new file** (suggested
`lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLDUAnalytic.lean`), importing `RouteMInteriorLDUContract`
(for `interiorLDUphi`, `interiorLDUunit`, `structPivot`) + `RouteMKLens` (for `kLDU`). Do NOT edit
`RouteMInteriorLDUContract.lean` or my `BchartLDU` defs. Hand genm-r1lower the named atoms; I wire them
into the contract's `Ubound`/`Umeas`/`image_subset` slots at assembly.

## Prerequisite atom (build FIRST — it unblocks the other three)
### `continuous_kLDU` — the kLDU lens is continuous (∀M)
```
theorem continuous_kLDU (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) :
    Continuous (kLDU M (tach M) ha) := …
```
Building blocks (easy): `kLens K = matrixSplit.symm (lduCoreMap (matrixSplit K))` is continuous —
`matrixSplit`/`.symm` are finite-dim linear (`LinearMap.continuous_of_finiteDimensional`), `lduCoreMap`
is continuous from `lduCoreMap_hasFDerivAt` (RouteMFactorMaps). Then `kLDU` is continuous coordinatewise
(`continuous_pi`).
**THE FRICTION (I hit it, reverted to keep green — flag if it walls):** reducing `kLDU`'s `match` on
`chartIdxEquiv … q` — plain `rw [kLDU, hq, hframe]` does NOT fire (can't rewrite the `match` scrutinee).
The FIX: use the banked `read*_kLDU` pattern — `simp only [kLDU, Equiv.apply_symm_apply]` per-coordinate
+ case-split the `frameSplitEquiv` summand (K-branch → `kLens` entry; X/N/E/lift → `x q`). Or prove a
per-role `kLDU_apply_*` pointwise lemma set first (mirroring `readK_kLDU`/`readX_kLDU` in RouteMKLens),
then `continuous_pi`. Bounded; it's a `match`-reduction tactic issue, not a math obstruction.

## Your three atoms (EXACT signatures — match my contract's frozen `sorry`s verbatim)
```
theorem ldu_Umeas (M …) (ha …) (hN …) : Measurable (interiorLDUunit M ha hN) := …
-- interiorLDUunit = UvalLDU … (kLDU …); = VvalGen ∘ genBlkFlatStruct ∘ kLDU, a polynomial-in-x map
-- (continuous_kLDU + the banked achieverUfun_measurable-style VvalGen continuity). hence measurable.

theorem ldu_Ubound (M …) (ha …) (hN …) (hL : 0 < L) (hInt : InteriorDrop M) :
    ∀ δ : ℝ, ∃ B : ℝ, 0 < B ∧
      (∀ u ∈ Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0:ℝ) δ),
        interiorLDUunit M ha hN u ≤ B) ∧
      ∀ᵐ u ∂(volume.restrict (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0:ℝ) δ))),
        0 < interiorLDUunit M ha hN u := …

theorem ldu_image (M …) (ha …) (hN …) : ∀ ε : ℝ, 0 < ε →
    ∃ δ > 0, interiorLDUphi M ha hN '' (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0:ℝ) δ))
      ⊆ cubeBox (routeMAmbient M) ε := …
```
(Read `RouteMInteriorLDUContract.lean` lines ~184/196/216 for the EXACT `interiorLDU_Ubound`/`_Umeas`/
`_image` signatures and match them so the wire `interiorLDU_Ubound := ldu_Ubound …` is a one-liner.)

- `ldu_Umeas`: `interiorLDUunit = UvalLDU … kLDU`; reduce to a polynomial-in-`x` map (the chain readers
  + `kLens` are polynomial) → measurable. Mirror `RouteMAchieverVvalPoly.achieverUfun_measurable`
  (eval-of-poly continuity) composed through `continuous_kLDU`.
- `ldu_Ubound`: ⚠️ **SOUNDNESS PIN (PROVE positivity, don't assert).** a.e.-positivity of
  `interiorLDUunit` on the box. The interior-drop witness `achieverUfun_wInt_ne_zero`
  (RouteMAchieverWitnessInterior) gives `UvalStructV(wInt) ≠ 0`; transfer it through the `kLDU` lens
  (kLDU is a pivot-fixing reparam — confirm the lensed unit's witness genuinely hits the same nonzero
  `Hmat 0` entry; the unit is a nonzero polynomial so `MvPolynomial.ae_eval_ne_zero` gives a.e.>0). The
  box-bound `≤ B` is continuity on a compact box (`continuous` ⟹ `IsCompact.exists_isMaxOn`, like
  `Uval4422_le_on_box`). Do NOT assume positivity — derive the nonzero-polynomial witness.
- `ldu_image`: continuity of `interiorLDUphi` (from `continuous_kLDU` + the chart chain) + `interiorLDUphi
  0 = 0` ⟹ a small `[0,δ]^N` box maps into `cubeBox ε`. Mirror `phi4422_image_subset_cubeBox` /
  `phi334_image_subset_cubeBox`.

## flag-if-walls
If `continuous_kLDU`'s `match`-reduction or the `Ubound` witness-transfer-through-kLDU fights past ~2
cycles, flag the precise gap (don't grind silently). The `Ubound` positivity is the soundness pin —
flag rather than assert if the witness doesn't transfer.

## Discipline
Sorry-free, honest. Zero new axioms; `#print axioms` clean-three on all four (no S2). Green-gate the
full `lake build DLNFibre`. Build from your WORKTREE `lean/` (`lake env lean` on warm oleans if the
`scripts/lb` semaphore contends). Hand genm-r1lower the four named atoms
(`continuous_kLDU`, `ldu_Umeas`, `ldu_Ubound`, `ldu_image`).
