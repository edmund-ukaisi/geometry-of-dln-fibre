# RouteMBData222 — landed state + the precise `BData` residual (DB/hasDB/hdet)

Branch `genm-bdata222` (off `genm-detfderiv`). File `lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean`,
724 LoC, sorry-free, builds green, axiom-clean `[propext, Classical.choice, Quot.sound]` (forced
`#print axioms` on `hmap_222`, `Agen0_Glr_eq`, `Agen1_Glr_eq`, `active222_card`).

## LANDED (the load-bearing fidelity + the genuine-hard map identity)

1. **`Agen0_Glr_eq` / `Agen1_Glr_eq`** — the FIDELITY: the two chain layers of `genBlkFlatLiveR1 M222`
   (reindexed to M-widths) ARE the Codex-verified explicit matrices
   - `Agen0 = [[a, a·n],[a·b, a·b·n + u]]` (the `+u` = the fixed pivot coord `u·E(0,0)`),
   - `Agen1 = [[u·lf0 − n·w0, u·lf1 − n·w1],[w0,w1]]` (`u = x structPivot`, readers a/b/n/w0/w1, leaf
     `rfin222 x = !![x lf0, x lf1]`).
   Machine-checked against the actual fixed-pivot/live-leaf decoder.

2. **R2 slot-wall resolution** (the opaque `chartIdxEquiv`): `readerSlotK/X/N/W0/W1`, `forbiddenSlots`
   (`card ≤ 6`, `forbiddenSlots_card_le`), `free_card_ge_two` (complement ≥ 2), `lf0/lf1`
   (`Classical.choose` from the complement → `lf ≠ structPivot`, `lf ∉ readerSet` for free),
   `active222 = {structPivot, lf0, lf1}` with `active222_card : = minAdm M222`, `structPivot_mem_active222`,
   the pbo facts `pbo_pivot/pbo_lf0/pbo_lf1/pbo_reader`, reader-stability `*_pbo`.

3. **`hmap_222`** (the BData obligation (1), the genuine hard piece):
   `phiFlatLiveR1 M222 tach222 structAdm_tach222 hN_M222 1 hp1_222 hp2_222 rfin222
      = Bchart ∘ pivotBlowupOn active222 (structPivot M222 hN_M222)`.
   Via `chartParamsGen_Glr_eq` (per-layer: `Agen{0,1}_Glr_eq` + pbo facts). `Bchart y = paramsEquivFlat
   M222 (Bparams y)`, `Bparams` = the faithful boundary chart reading the pivot as the ORDINARY coord
   `y structPivot` (NOT `phiGen 1 (genBlkFlatLiveR1)`, the superseded wrong B).

## RESIDUAL (mechanical-but-large; the `Bparams` Jacobian determinant)

The `BData M222 tach222 structAdm_tach222 hN_M222 1 hp1_222 hp2_222 rfin222 u` term needs three more
fields, all about `Bchart`'s derivative (NOT the map identity, which is done):

- **`DB`** — `Bchart`'s fderiv as a CLM at `pivotBlowupOn active222 structPivot u`. `Bchart =
  paramsEquivFlat ∘ Bparams`; `Bparams` is polynomial (each entry a poly in the 8 coords), so
  `DB = paramsEquivFlatCLE ∘L (fderiv Bparams)`, built like `phi222Deriv`/`phi222_hasFDerivAt` in
  `RouteM222Det` (chain rule, `HasFDerivAt`).
- **`hasDB : HasFDerivAt Bchart DB (pbo ... u)`** — mechanical via the chain rule + per-entry
  `HasFDerivAt` (the `pack222_hasFDerivAt`/`T222_hasFDerivAt` pattern).
- **`engine : Fin 2 → ℝ`** = `![|aRead u|², 1]` (or `fun s => if s = 0 then |aRead u|² else 1`),
  product `= |aRead u|²`.
- **`hdet : |det DB.toLinearMap| = ∏ engine = |aRead u|²`** — THE substantive computation: the
  `Bparams` Jacobian determinant = `a²` (the engine `|K|^{r+c}`, `r=c=1`). Codex-verified sympy-exact.
  This is the de-radialized analog of `T222Deriv_abs_det = |u0|²·|u4|`; here `det = a²` (NO radial
  factor — `B` is radial-free). ~120-150 lines: build the `Bparams` fderiv CLM, compute its 8×8 det
  via the Schur-frame `BlockTriangular`/shear structure (the pivot reads as an ordinary coord, det = a²).

## Assembly (trivial once DB/hasDB/hdet land)

```lean
noncomputable def bData222 (u : Fin (routeMAmbient M222) → ℝ) :
    BData M222 tach222 structAdm_tach222 hN_M222 1 hp1_222 hp2_222 rfin222 u where
  active := active222
  hp_mem := structPivot_mem_active222
  hcard := active222_card
  B := Bchart
  DB := <DB at (pbo active222 structPivot u)>
  hasDB := <hasDB>
  hmap := hmap_222
  engine := fun s => if s = 0 then |aRead u| ^ 2 else 1   -- ∏ = |aRead u|²
  hdet := <hdet>

theorem interiorDet_headline_222 (u) :
    |LinearMap.det (fderiv ℝ (phiFlatLiveR1 M222 tach222 structAdm_tach222 hN_M222 1 hp1_222 hp2_222
        rfin222) u).toLinearMap|
      = |u (structPivot M222 hN_M222)| ^ (minAdm M222 - 1) * ∏ s, (bData222 u).engine s :=
  interiorDet_headline_of_BData M222 tach222 structAdm_tach222 hN_M222 1 hp1_222 hp2_222 rfin222 u
    (bData222 u)
```
giving `= |u_p|² · |aRead u|²` = the bridge's `det Dφ = a²·u²`.
