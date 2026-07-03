# Statement card — general-`L` SMEARED flat DECODE + rate + box-divergence assembly + `hSmeared` ∀L

*Modules: `lean/DLNFibre/DLN/RLCT/Validate/RouteMSmearedDecodeGen.lean` (the decode + rate) and
`RouteMSmearedAssembleGen.lean` (the assembly), on `origin/genm-smearcont` (branched off
`origin/genm-smeargen` @ `7f257b56`). Axiom-clean `[propext, Classical.choice, Quot.sound]`; zero
sorries in both modules. Continues the `RouteMSmearedGenAtom` foundations (companion card).*

Goal context: close the general-`L` SMEARED branch of the achiever-dispatch spine's last caller
obligation `hSmeared : ∀ _ : 2 ≤ L, BoundarySmeared M → BoxDiverges M c' ε` (`RouteMAchieverDispatch`).
The companion card banked the chart-eval collapse (`prod_chartGen_collapse`) + the rank-`r` bottleneck
cancellation (`staircase_cancel`); this card banks the three obstruction pieces (1 decode, 2 rate/det,
3 assembly) that consumed them.

---

## De-risk verdict (reported first): `deepest_slot_split_spec` THREADS

The riskiest cast — the `deepWidthEquiv` row-split at layer `L−1` in the general-`L` FlatIdx — is
CONFIRMED. `deepLayer_castSucc_width`/`deepLayer_succ_width` prove the width equalities
`M (deepLayer hL).castSucc = M (⟨L−1⟩:Fin(L+1))` and `M (deepLayer hL).succ = M (last L)` (the atom's
`e1`/`e2`); the deep FlatIdx slot `topSlotG a j = ⟨⟨deepLayer hL, deepWidthEquiv hrs (inl a)⟩, j⟩`
typechecks at the FlatIdx-natural `hrs : r+s = M (deepLayer hL).castSucc`, and
`flatEquivOf_symm_coord` reads it back exactly as the L=2 `packM_shear_entry`. The atom↔FlatIdx split
conversion is `finCongr_e1_deepWidthEquiv` / `deepWidthEquiv_symm_finCongr_e1` (val-preserving).

---

> **Claim 1 (the general-`L` flat DECODE, ∀ `L ≥ 1`).** `genDecode_params`:
> `(flatEquivOf (slotEquivG)).symm (shearMBody (topCoordsG) (shiftCoreG) (RmapG u))
> = chartGenParams M (frontTupleG u) hL (hrsAtom_of_hrs hL hrs) (zuG u) (H̄ cast) (S_bot cast) (Λ₀ u)`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.genDecode_params` (`RouteMSmearedDecodeGen.lean`).
> - **Gloss.** The `Fin (L+1)`-layer generalization of the `Fin 3`-hardcoded L=2 `decode_params`. Per-layer
>   dispatch by `layer = deepLayer hL?` (NOT `fin_cases` — `layer : Fin L` is opaque): the FRONT layers
>   (`≠ deepLayer`) are the identity readoff `frontTupleG` (coords `∉ topCoordsG`, so
>   `shearMBody_apply_of_not_mem`/`RmapG_spectator` leave them untouched — the interior `carry_r`
>   staircase falls out for free); the deep layer `L−1` is the `deepWidthEquiv` row split (top `r` rows
>   the radial-minus-shear `z·H̄_unit − Λ₀·S_bot`, bottom `s` rows the free residual `S_bot`).
> - **Proved.** Sorry-free, ∀ `L ≥ 1`.
> - **Status.** sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`.

> **Claim 2 (the general-`L` peeled rate + box-divergence assembly).** `routeMCore_psiMapG_RmapG` gives
> `routeMCore M (psiMapG (RmapG u)) = (zuG u)²·‖P₁·H̄_unit‖²` off `P₁·Λ₀ = P₂`; `routeMCore_smearedGen`
> assembles the conditioned-box divergence `∫⁻_{cubeBox N ε} |routeMCore M|^{−c'} = ⊤`.
>
> - **Lean:** `routeMCore_psiMapG_RmapG` / `routeMCore_smearedGen` (`RouteMSmearedDecodeGen` /
>   `RouteMSmearedAssembleGen`).
> - **Gloss.** The rate bridge = DECODE (claim 1) + the atom's `prod_chartGen_collapse` (off `hcancel`) +
>   the banked ∀L `routeMCore_rate_of_prod_collapsed`. `routeMCore_smearedGen` feeds the general-`L`
>   radial machinery (`psiMapG` MP + a measurable embedding; `RmapG`/`DmapG` fderiv/injOn/det, exponent
>   `r·M(deepLayer).succ − 1`) into the M-agnostic ∀L engine `routeMCore_box_diverges_smearedL2`, with the
>   mechanical `z`/`U` peel (`zuG = z`, `UunitG` z-free) folded in. `DmapG_abs_det` gives det
>   `|u pivot|^{r·c − 1}`; with `r·c = minAdm` (banked `minAdm_eq_deepRank_mul_last`), `h = minAdm − 1` —
>   FIDELITY: exactly the `r·c` deepest-top coords are radial-active, `K`'s coords are FREE spectators.
> - **Proved.** Both, sorry-free, ∀ `L`. `ψ` MP + a measurable embedding, and every chart component's
>   measurability (`measurable_prodAux_entry` by induction → `frontProd`/`P1uG`/`Lam0uG`/`UunitG`/
>   `shiftCoreG`), are DISCHARGED.
> - **Assumed (per-family, on the conditioned box).** the shear cancellation `P₁·Λ₀ = P₂` (off the pole —
>   supplied by `staircase_cancel` off `det(CᵀC)≠0`); `U`-positivity; FIELD-A containment; the box radius.
> - **Status.** sorry-free, axiom-clean.

> **Claim 3 (the `SmearedAchieverChart M` builder + `hSmeared` ∀L).** `smearedChartGen` builds a
> `SmearedAchieverChart M` for arbitrary `L`; `hSmeared_smearedGen` feeds it into the already-∀L
> `hSmeared_of_smearedChart`, giving the spine's `hSmeared` for `M`.
>
> - **Lean:** `smearedChartDataGen` / `smearedChartGen` / `hSmeared_smearedGen` (`RouteMSmearedAssembleGen`).
> - **Gloss.** `smearedChartDataGen` builds the per-ε `SmearedChartData` (`hRate` discharged from the rate
>   bridge + peel; `Uy := UunitG (hN ▸ insertNth p 0 ·)` z-free + measurable; `hRdet` from `DmapG_abs_det`)
>   from a supplied conditioned box + its analytic inputs. `smearedChartGen` bundles the general-`L` maps +
>   the exponent (`hexp` via `hminadm : r·M(deepLayer).succ = minAdm M`, `1 ≤ minAdm M`, giving `−1 ≤ −1`)
>   + the per-ε data supplier. `hSmeared_smearedGen` chains to `hSmeared_of_smearedChart`.
> - **Proved.** Sorry-free, ∀ `L`. Axiom-clean `[propext, Classical.choice, Quot.sound]` (measure theory
>   only — NO `monomial_rlct`).
> - **Assumed (the honest remaining residue).** the per-ε conditioned-box-data supplier `dataGen`
>   (the box radius `δ`, FIELD-A containment, `RmapG` injectivity on the box, the cancellation, `U`>0, box
>   measurability/positivity) + `hrs`/`hr`/`hc`/`hp`/`hminadm`/`hminpos`. These are exactly the
>   `SmearedChartData` fields the worked L=2 `smearedChartData231` supplies — the family-specific
>   conditioned box (the opaque-general-`L` analog of `box231`/`subBox231_det_ne`).
> - **Status.** sorry-free, axiom-clean.

## Ceiling / remaining residue (precise)

The whole network-generic + measure-theoretic + cast machinery is DONE sorry-free: decode, rate,
box-divergence assembly, MP/embedding, every component's measurability, the `SmearedAchieverChart`
builder, and the `hSmeared` ∀L consumer form. What the `hSmeared_smearedGen` caller still supplies (the
`dataGen` argument): the **general-`L` conditioned box** with (a) `det(CᵀC)≠0` (general-`r` free-block
diagonal dominance — the L2 `subBox231_det_ne` is `det_fin_two`-specific), giving the cancellation via
`staircase_cancel`; (b) `UunitG > 0`; (c) FIELD-A containment `condBox ⊆ (ψ∘R)⁻¹(cubeBox ε)`; (d)
`RmapG` injectivity on the box. This is the family-specific box construction (a substantial build at
opaque widths), NOT the network-generic engine — the engine is complete and consumes it verbatim.
