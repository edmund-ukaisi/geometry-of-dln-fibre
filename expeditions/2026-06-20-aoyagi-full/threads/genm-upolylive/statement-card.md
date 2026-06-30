# Statement card — LEAF-1 a.e.-positivity atom (genm-upolylive)

> **Claim.** The LIVE-leaf interior unit `interiorLiveUnit ha h0r h0c` is almost-everywhere
> strictly positive on `Fin (routeMAmbient M) → ℝ`, for `M : Fin (2+1) → ℕ` with `ha : StructAdm M (tach M)`,
> `h0r : 0 < Text M (tach M) 2`, `h0c : 0 < Wext M 2`, and the interior-drop hypothesis `hInt : InteriorDrop M`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.interiorLiveUnit_ae_pos`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMUPolyLive.lean` @ `d22df4ba`)
> - **Gloss.** `∀ᵐ (u : Fin (routeMAmbient M) → ℝ), 0 < interiorLiveUnit ha h0r h0c u` — w.r.t. the
>   product Lebesgue `volume`. The interior unit is the radial-quotient factor
>   `VvalGen (u leafPivot) (genBlkFlatLive ha (rfinFixedPivot ha (kLDU u)) (kLDU u))` of the LIVE-leaf ∘ kLDU
>   interior achiever chart; "a.e. positive" means its zero set is Lebesgue-null.
> - **Proved.** Unconditionally (modulo `hInt`): the zero set of `interiorLiveUnit` is null. Route:
>   `interiorLiveUnit u = eval u UPolyLive` for a NAMED `UPolyLive : MvPolynomial (Fin (routeMAmbient M)) ℝ`
>   (`eval_UPolyLive`, sorry-free); `UPolyLive ≠ 0` exhibited at the interior-drop witness `wInt p`
>   (`UPolyLive_ne_zero` via `interiorLiveUnit_wInt_ne_zero`); then `MvPolynomial.ae_eval_ne_zero`
>   (banked `Core.MeasureTheory.PolynomialZeroSet`) + `interiorLiveUnit_nonneg` (banked, sum of squares).
> - **Assumed.** `hInt : InteriorDrop M` — supplies the active interior pivot `p` (`1 ≤ p < 2`, the strict
>   row-drop, the tail column-drops, the leaf `0 < Wext M 2`) at which the nonzero witness lives. This is
>   the same hypothesis the contract's `interiorLive_Ubound` already carries. `M : Fin (2+1)` (the L2 case).
> - **Cited.** none new. Builds only on banked DLNFibre infra (`MvPolynomial.ae_eval_ne_zero`,
>   `VvalGen_nonneg`, `achieverUfun_wInt_ne_zero`'s generic survival machinery `Hmat_pivot`/`Hmat_row_thread`/
>   `suffix_carrier`, the chain `map`-naturality `Cgen_map`/`Agen_map`/`chainOfMt_map`/`Hmat_zero_map`).
>   NO S2 axiom; the nullity is the elementary `MvPolynomial.volume_zeroSet_eq_zero`.
> - **Deferred.** none for this atom. (The downstream `interiorLive_Ubound` ALSO needs a box-bound + `Umeas`
>   + `image_subset` — those are genm-ubound-live's slots, NOT this atom; the wirer assembles
>   `interiorLive_Ubound` = its box-bound ∧ `ae_restrict_of_ae` of this atom.)
> - **Route.** `interiorLiveUnit = eval · UPolyLive` (the MvPolynomial encoding), then
>   `ae_eval_ne_zero` + nonneg. The encoding needed the generic kLens/kLDU-over-`CommRing` infra
>   (`kLensGen` via the explicit `(1+lowMat)·diag·(1+upMat)` formula, bypassing `matrixSplit`'s ℝ-only
>   `LinearEquiv`/`FiniteDimensional`; `kLensGen_map` naturality; `kLDUGen_eval`; `genBlkFlatLiveGen` + its
>   `GenBlkMap`; `sqSumHmat0_map`). The witness: `kLDU` fixes `wInt` (`kLDU_wInt`, since `readK wInt = I`
>   and `kLens 1 = 1`), then the generic survival entry `Hmat 0 (ρ,0) = 1` for the live decoder
>   (scalar- and `Rfin-L`-agnostic: the surviving entry reads only `Bmat/Nblk/Wblk/Rmat`, all
>   definitionally shared with `genBlkFlatStruct ha wInt`).
> - **Status.** sorry-free + reviewed. Forced `#print axioms` = `[propext, Classical.choice, Quot.sound]`
>   (no S2, no `sorryAx`, no `native_decide`). Reviewer fidelity check SURVIVED (all 5 points PASS,
>   axioms independently re-verified, Codex-decorrelated on the scalar/`Rfin`-independence).

## Reviewer note — the scalar/`Rfin`-independence keystone

The load-bearing soundness fact (why the dead-leaf survival transfers to the live decoder): the surviving
entry `Hmat 0 (ρ,0) = 1` never reads `Rfin L` (`= C L`) nor the radial scalar `u`. The decisive lemma is
`chainA_apply_natAdd` (`RouteMGenChainBridge.lean`): the LIFT rows of `chainA h N W C` equal `W a j` with
provably NO dependence on the kept block `C`. So `suffix` (via `suffix_carrier`) reads `A` only through
lift rows (`= Wblk`) and bottoms out at `suffix L = I` (never `C L = u·Rfin L`); `Hmat_pivot`'s value is
`Rmat p · suffix p` (both `u`-free); `Hmat_row_thread` threads `p→0` via `Bmat`-identity rows + `E s = 0`,
never evaluating `Hmat L = Rfin L`. The live decoder's `Bmat/Nblk/Wblk/Rmat` are definitionally the
struct's (`rfl`), and `Rfin` is the only differing field — never touched. (Reviewer + Codex confirmed.)

## Reusable infra delivered (route-independent)

The generic kLens/kLDU-over-`CommRing` layer is the part genm-ubound deferred; it serves both leaves:

- `kLensGen` / `kLensGen_map` / `kLensGen_eq_kLens` / `kLensGen_one` / `kLens_one`
- `kLDUGen` / `kLDUGen_eval` (`eval u (kLDUGen (Xvec) q) = kLDU u q`)
- `genBlkFlatStruct_genBlkMap_of` (the `Xvec`-free generalization of `genBlkFlatStruct_genBlkMap`)
- `genBlkFlatLiveGen` / `genBlkFlatLiveGen_eq_live` / `genBlkFlatLiveGen_genBlkMap_of`
- `rfinFixedPivotGen` / `rfinFixedPivotGen_map` / `rfinFixedPivotGen_eq`
- `sqSumHmat0_map` (ring hom through `∑∑·²` + `Hmat_zero_map` — the clean bridge that avoids the
  `convert`/`▸` dependent-`Hmat`-proof timeout)
- `kLDU_wInt`
