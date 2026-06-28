# Certificate — the ∀M-(1,1)-smeared lift: ARCHITECTURE finding + the cancellation sub-target

**Seat:** lean-formaliser (architecture decision + first sub-target, pre-full-build). **Date:** 2026-06-28.
**Gate:** decorrelated local-Codex consult (`codex/genM11-arch-{prompt,answer}.md`, LANDED) + the
exhaustive `(1,1)`-family structure extraction + a numerically-validated cancellation. The architecture
finding RESHAPES STEP 2's premise; the first sub-target is BANKED sorry-free.

## 0. Headline — the validate-small architecture does NOT generalize; the ∀M lift needs the CLEAN Option-A substrate

The coordinator's STEP-2 framing ("parametrize the `(1,2,1)` template's pivot + dims — mechanical-within-
fixed-shape, charge through") MATERIALLY under-estimates the lift. The `(1,1)` family (34 cases) has
**L ∈ {2,3,4}** (only 2 cases L=2; 8 at L=3; **24 at L=4**), **varying pivot location** (bottleneck front
layer at `k ∈ {0,1,2}`), and **varying flatDim** (4..15). For `L ≥ 3` the front `P = A⁰·A¹·…` is a MATRIX
PRODUCT, so `P₁` (its first column) is a degree-`(L−1)` polynomial in the front coords.

The three validate-smalls (`RouteM121/231/132Smeared`) use a PER-M explicit reshape (`packNNN` +
`finNEquivFlatIdxNNN` hand-coded `match` + `splitN` peel) — this is **scaffolding, NOT the ∀M substrate**
(Codex). It cannot generalize over varying L/flatDim (the explicit `Fin N ≃ FlatIdx M` is per-fixed-width).

**The ∀M-smeared lift MUST adopt the BOUNDARY-CLEAN "Option A" flat-coordinate architecture**
(`RouteMBoundaryCleanRate.lean`): the chart is a GENERIC flat→flat self-map keyed on `deepestCoords M`/
`deepestPivot M`, the rate decoded ONCE via `paramsEquivFlat_symm_decode` (`=rfl`) +
`flatCoordOf_mem_deepestCoords_iff` + the "deepest layer = pivot-scaled, prefix untouched" smul-pull
(`prod_cleanParams_eq_smul`), with the front product `prefix·M̄` carried ABSTRACTLY (never expanded).
Reuses: `deepestCoords`/`deepestPivot`/`Text`/`minAdm`, `paramsEquivFlat_symm_decode`, `LossHomogeneity`,
the generic `pivotBlowupOn` det/cov (`S1G5Charts`).

## 1. What is genuinely NEW vs the CLEAN lift (and the biggest risk)

CLEAN has `r = m1` (NO smear) ⟹ a PURE radial, NO shear, NO cancellation. The SMEARED `(1,1)` lift adds:
- a GENERIC flat SCALAR-SHEAR (the `Λ₀`-shear at the deepest-pivot coord, reading the front coords);
  measure-preserving via a GENERIC one-coord shear (Codex: promote the banked `measurePreserving_shearAt`
  in `Case222Lemma2.lean` for arbitrary `p : Fin N` — NO per-M `splitN`);
- **the GENERIC scalar-shear cancellation `P₁·Λ₀ = P₂`** — Codex's flagged BIGGEST RISK (without exposing
  it cleanly, Lean forces degree-`(L−1)` coordinate expansion + dependent-width product casts). The
  load-bearing structural fact: the front-bottleneck `r = 1` gives RANK-ONE columns (every column of `P`
  is a scalar multiple of column 0) + `‖col 0‖² ≠ 0` off the pole. BOTH hypotheses load-bearing (scalar
  Gram alone is NOT sufficient).
- `minAdm = 1` ⟹ NO radial (weight 1) ⟹ the assembly is `routeMCore_box_diverges_of_MPChart`.

## 2. FIRST SUB-TARGET — LANDED (the architecture-proving cancellation)

`RouteMSmearedGenRate.lean` (sorry-free; `#print axioms scalarGram_cancel_of_rankOneColumns` =
`[propext, Classical.choice, Quot.sound]`, S2-free):

  scalarGram_cancel_of_rankOneColumns (c₀ : rows → ℝ) (μ : s → ℝ) (hc : (∑ i, (c₀ i)²) ≠ 0)
    (P₁ : Matrix rows (Fin 1) ℝ) (P₂ : Matrix rows s ℝ)
    (hP₁ : ∀ i, P₁ i 0 = c₀ i) (hP₂ : ∀ i j, P₂ i j = μ j * c₀ i) :
    P₁ * ((P₁ᵀ * P₁)⁻¹ * P₁ᵀ * P₂) = P₂

The generic version of the validate-smalls' per-M scalar cancellation (`a00·(a01/a00)=a01`), proven once
for ALL rank-one-column front products: `P₁ᵀP₁ = ‖c₀‖²` (1×1, `inv_def`/`det_fin_one`/`adjugate_fin_one`),
`Λ₀ 0 j = μ j`, so `(P₁·Λ₀) i j = c₀ i·μ j = P₂ i j`. Network-free pure linear algebra. Cancellation
validated symbolically across shapes (`scalargram_cancel.py`, 5/5).

## 3. Residual (the rest of the ∀M-(1,1) lift) + the rest point

To finish the `(1,1)`-family atom on the Option-A substrate:
1. **The front-bottleneck → rank-one bridge**: specialize §2 to `P = frontProd M` (`= prodAux M A (L−1)`),
   proving every column is a scalar multiple of column 0 from `Text(L) = r = 1` (the front bottleneck).
   This needs the generic front-product first-column structure — a SEPARATE generic lemma (no banked
   front-product/`P₁`-rank infra exists yet). This is where the degree-`(L−1)` product lives.
2. **The generic flat scalar-shear** + its MP (promote `measurePreserving_shearAt` to arbitrary `p`).
3. **The generic rate** `routeMCore (shearedFlatPhi u) = (u_p)²·U` (reuse the CLEAN decode + §1 cancel).
4. **`subBox` + containment + `MPChart` assembly** → the `(1,1)`-family atom ∀ such M.

REST POINT (FIRM REST-VALVE recalibrated by the coordinator to "charge through"): I charged the
architecture decision (decorrelated) + the first sub-target. But sub-target 1 (the front-bottleneck →
rank-one bridge over the degree-`(L−1)` matrix product) is a GENUINE design subtlety the `(1,2,1)`
template does not cover (the coordinator's named genuine-wall trigger) — it is fresh generic
front-product infrastructure, NOT a parametrization of the template. Reporting this for a sequencing
decision (build the front-product bridge here, or decorrelate it to pen-and-paper, or re-scope) rather
than silently sink a large fresh-infrastructure build under a "charge through" framing that assumed the
template generalizes.
