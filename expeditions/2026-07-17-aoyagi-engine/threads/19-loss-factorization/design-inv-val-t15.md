# Design note — `Inv_val` (the 3b prod-diagonalization invariant) build plan (loss-t15)

*Seat: `lean-formaliser` (loss-t15). Prep/comprehension note for PHASE 3b — building
`leafDiagFrob_geoAtlasNorm` (the one remaining `sorry` in `GeoAlphaGauge.lean`). Grounded in
pnp-fold's §7 (`threads/18-fold-regroup/cert-ledger-accumulation.md` + `value_vs_det_delta.py`) and
`cert-loss-factorization.md`. **BUILD BLOCKED on t14's det-walk (`geoAtlas_fold_det`, task #43)
landing — it is the shared-driver template.** This note fixes the stable design so the build is fast
once the template exists.*

---

## The target and the already-proven reduction

The one open `sorry` is `leafDiagFrob_geoAtlasNorm : l ∈ geoAtlasNorm alphaGauge (buildTree…) →
LeafDiagFrob l`. Everything downstream of `LeafDiagFrob` is PROVEN this seat:
`LeafDiagFrob l → l.resRank = 0 → LeafPullback l` (`leafPullback_of_diagFrob`), and the `resRank = 0`
transfer (`geoAtlasNorm_resRank_zero`). So 3b = supply `LeafDiagFrob` from the geometry.

`LeafDiagFrob l` (recall): `∃ m (r : Params M → Fin m → ℝ) hi, ∀ w ∈ srcBox,`
`frobSq(prod(chartMap w)) = Σᵢ ((∏_k z_{divCoord k}(w)) · r w i)² ∧ (∃ i, r w i = 1) ∧ Σᵢ (r w i)² ≤ hi`.

## The invariant (§7)

`Inv_val(acc, s) : prod M (acc w) = diag(b(s)(w)) · [[E_J, O],[O, D_J(w)]]` (Aoyagi's state invariant),
acc-threaded, base `prod M (id w) = ∏ C^{(s)}` at `conRoot`. **Same skeleton as t14's det walk**
(tree walk over `tGeoG`/`geometricLeafPaths`, per-`stepUpdate`-case dispatch, `conRoot` base,
`DivBirthInv` threading, the `geoChartMap_flat_{pivot,center,spectator}` + `flatSwapCLE_apply_flat`
coordinate-action reads). **Value delta (det never sees):** (1) the residual block `D_J`; (2) `b` is
the power-1 squarefree chain `b₁ = ∏_{t̃=0} u`, `bᵢ/bᵢ₋₁ = ∏_{born at level i−1} u` (NOT `divExp`
powers); (3) the α gauge is IN the maintenance (the Jacobian is det-1-blind to α; the value is not —
`Inv_val`'s case-1(2)/case-2 steps apply `residualSchurShear` to clear `D_J` toward
`[[1,O],[O,D_{J+1}]]`); (4) `resRank`/`resCoord` match the leaf residual shape (here `resRank = 0`).

## The leaf discharge (`Inv_val` leaf case → `LeafDiagFrob`) — the bridge

At a spine leaf the construction is FULLY monomialized and `resRank = 0` (`leaves_resRank_zero`,
already transferred): `D_J` is cleared, so `Inv_val` gives `prod M (chartMap w) = diag(b(w))`
(rectangular diagonal, the `b`-chain). Then:

- `frobSq(diag(b)) = Σⱼ (b_j(w))²` (a diagonal matrix's Frobenius square is the sum of squared
  diagonal entries — a small `frobSq`-of-diagonal lemma to add).
- `b_j(w) = (∏_k z_{divCoord k}(w)) · ρ_j(w)` where `b₁ = ∏_{t̃=0} u = ∏_k z_{divCoord k}` (the terminal
  product `D`) and `ρ_j = b_j/b₁` is a **power-1 monomial** (well-defined by the `bChain` divisibility
  `b₁ | b_j`, already a TYPED field `LeafData.bChain`). `ρ` at the `b₁`-index is `1`.
- Instantiate `LeafDiagFrob` with `m := numB`, `r w := ρ(w)`, `hi := ` the ratio bound on the flat
  cube `srcBox`. The three clauses: factorization = `frobSq = Σⱼ (D·ρ_j)²`; `∃ i, r i = 1` = the
  `b₁`-index ratio; `Σ ρ² ≤ hi` = ratios are bounded monomials on the bounded `srcBox`.

So `LeafDiagFrob` reads off the leaf's own `bExp`/`bChain` once `Inv_val` supplies `prod = diag(b)`.
The `b`-chain ↔ `divCoord` tie (b₁ = ∏ divCoord) is the value-side analog of t14's `divExp` read and
is cert-settled (`cert-loss-factorization` (a): `b₁` squarefree = each terminal divisor once).

## Build sequence (once t14's walk lands)

1. **Consume t14's shared driver.** Per §7's recommendation, t14's walk should be factored into a
   reusable induction driver (tree-walk + per-case dispatch + `DivBirthInv` + `geoChartMap_flat_*`
   reads). Instantiate it with the VALUE payload (matrix `diag(b)·[[E_J,O],[O,D_J]]` + α). If t14 did
   NOT factor a driver, MIRROR its walk structure (same skeleton, value motive). Decide mirror-vs-
   instantiate from t14's landed code.
2. **The four per-case value-maintenance identities** (mirror t14 §3, add the α/D_J payload):
   case-1(1) re-merge (b-power stays 1, α = id since pivot = diagonal); case-1(2) split + α Schur
   clears one residual column; case-2 birth + α Schur clears the block toward `D_{J+1}`; rollover
   (relabel, `localSub = id`). The α steps reuse `residualSchurShear` + the flat-read/fixed/at_a
   lemmas already PROVEN here (`residualSchur_flat_read`, `elemShearFold_fixed`, `elemShearFold_at_a`).
3. **The leaf discharge** above (`frobSq`-of-diagonal lemma + the `bExp`/`bChain` → `ρ` instantiation).
4. **Wire** `leafDiagFrob_geoAtlasNorm` = the leaf case of `Inv_val` at `conRoot`; `LeafPullback`
   end-to-end closes via the already-proven `leafPullback_of_diagFrob`.

## Reuse ledger (what's already banked in `GeoAlphaGauge.lean`)

The α maintenance is fully supported: `alphaGauge`/`residualSchurShear` (def), `residualSchur_flat_read`
(conjugation-of-fold), `elemShearFold_fixed`/`_at_a` (per-coordinate action), `schurCells_*`
(distinctness), det-1 + srcBox bounds. The value build supplies only the `prod`-tracking maintenance
(the matrix payload) on t14's skeleton + the leaf `frobSq`-of-diagonal read.
