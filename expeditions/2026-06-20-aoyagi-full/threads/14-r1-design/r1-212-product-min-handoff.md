# (2,1,2) product-MIN — fm hand-off (the ladder's cheapest immediate rung, NO G5)

- **Seat:** `pp` (design). For `fm`. The (2,1,2) headline instance: lighter than (2,2,2), no blow-up,
  no cover, no G5 dependency — the next ladder rung fm can take in parallel with fm-2's #52.
- **What it validates:** the PRODUCT-separation machinery (distinct from (1,1,1) monomial / (2,2,2)
  cover). One new reusable lemma (product-MIN) + two applications of the existing `smoothBlockND_rlct`.

## The core (why it separates)

For `M=(2,1,2)`: `C^(1)` is `2×1` (`a₁,a₂`), `C^(2)` is `1×2` (`b₁,b₂`), product `P_ij = aᵢbⱼ` (2×2).
`F = ‖P‖² = ∑_{ij} aᵢ²bⱼ² = (a₁²+a₂²)(b₁²+b₂²)` — a PRODUCT of two smooth blocks in DISJOINT variables
`a=(a₁,a₂)`, `b=(b₁,b₂)`. (Contrast (2,2,2): `P_ik=∑_j a_ij b_jk` couples a,b — no separation.)

## The new reusable lemma: product-MIN

> **product_min_rlct** (FINAL form, agreed with fm-2 #56). For `G : ℝ^p → ℝ`, `H : ℝ^q → ℝ`, both
> `≥ 0`, measurable, with the a.e.-nonvanishing guards `hGne : G ≠ 0 a.e.`, `hHne : H ≠ 0 a.e.`, and
> `F(x,y) = G(x)·H(y)` on `ℝ^p × ℝ^q`:
> `rlctAtOn F 0 = min (rlctAtOn G 0) (rlctAtOn H 0)`.

**HYPOTHESIS (the guard, FINAL — `hGne : G ≠ 0 a.e.`):** the guard is the a.e.-nonvanishing `hGne`/`hHne`
(fm-2's form, S1.5-`hHne`-consistent), NOT "vanishes only at 0" (over-strong — excludes monomials) and
NOT the nbhd-form `0 < ∫⁻_U G^{-c}` (the right content, but `hGne` is the cleaner statement). `hGne` is:
- EQUIVALENT-GIVING (not too weak): `hGne` + `μ(U)>0` ⟹ `0 < ∫⁻_U |G|^{-c}` (via `setLIntegral_pos_iff`)
  — supplies the positivity the 0·∞ step needs.
- DISCHARGED BY BOTH CONSUMERS (not too strong): (2,1,2) block `Σy²` zero-set `{0}` (null); (2,2,2)
  δ-leaf monomial `x²s²` zero-set = coordinate hyperplanes (null). Both ⟹ `≠0 a.e.`
With `hGne`, ONE lemma covers block×block (2,1,2), monomial×block (δ-leaf), monomial×monomial — the
unification. (The earlier "vanishes only at 0" was over-strong; `hGne` is the right altitude.)
See `/tmp/hgne_check.py`, `/tmp/product_min_general.py`.

### Proof (ℝ≥0∞ / lintegral — fm-tractable)
`∫⁻_{U×V} (G(x)H(y))^{-c} d(x,y) = (∫⁻_U G^{-c} dx)·(∫⁻_V H^{-c} dy)` — Tonelli product-split
(`lintegral_prod_mul`) after `(G·H)^{-c} = G^{-c}·H^{-c}` (`ENNReal.coe_mul_rpow` / `mul_rpow` on the
nonneg factors). The product is finite ⟺ both factors finite ⟺ `c < rlctAtOn G ∧ c < rlctAtOn H` ⟺
`c < min`. So `sSup{c : finite} = min(rlctAtOn G, rlctAtOn H)`.

### THE 0·∞ STEP (load-bearing — discharged by `hGne`/`hHne`)
In ℝ≥0∞, `a·b < ⊤ ⟺ a<⊤ ∧ b<⊤` is FALSE when one factor is `0` (then `0·∞=0<⊤`; Lean:
`ENNReal.mul_lt_top_iff` needs the both-`≠0` branch). The "product finite ⟺ both finite" step needs
BOTH block integrals strictly positive. `hGne : G ≠ 0 a.e.` supplies it: `G ≠ 0 a.e.` ⟹ `|G|^{-c} > 0`
a.e., and `μ(U) > 0` (U a nbhd of 0) ⟹ `0 < ∫⁻_U |G|^{-c}` (`setLIntegral_pos_iff`). So the lemma
CARRIES `hGne`/`hHne` and discharges the 0·∞ corner from them. (fm-2 verified the atoms:
`ENNReal.mul_lt_top_iff` both>0, `setLIntegral_pos_iff` for positivity-from-`hGne`. Logged to
lessons.md — the ℝ≥0∞ product gotcha.)

## CERTIFICATE — the rule is MIN, not SUM (exact-rational, rules out additive)

Discriminating test at `c=3/2` (between `min=1` and `sum=2`): the 2D block factor `∫_0^1 r^{1-2c} dr`
at `c=3/2` is `∫_0^1 r^{-2} dr = ∞` (DIVERGENT). So `∫ F^{-3/2} = ∞` ⟹ `rlct ≤ 3/2 < 2` — this RULES
OUT the additive rule (which would give `1+1=2`) and confirms `rlct = 1 = min`. (`/tmp/r212_certify.py`,
exact via sympy.) The product-MIN rule is CERTIFIED for (2,1,2), not assumed — the min-vs-sum separation
is the load-bearing distinction and it's witnessed. (Contrast: additivity S1.5 is for `F²+G²` SUMS; this
is a `F·G` PRODUCT ⟹ MIN. Don't conflate.)

## The (2,1,2) instance (applies product-MIN to two smoothBlockND blocks)

- `G(a) = a₁²+a₂² = ∑ᵢ aᵢ²` on `ℝ²`; `rlctAtOn G 0 = 2/2 = 1` by `smoothBlockND_rlct 1`
  (`m=1`, `n=m+1=2`, RHS `(m+1)/2 = 1`). DONE lemma (fm-2 #38, `S1SmoothBlock.lean`).
- `H(b) = b₁²+b₂²` likewise: `rlctAtOn H 0 = 1`.
- `product_min_rlct` ⟹ `rlctAtOn F 0 = min(1,1) = 1`.
- Arithmetic: `½·Mval(2,1,2; deepest) = ½·2 = 1`. So `rlctAtOn F 0 = lambdaCore(2,1,2)` ✓.
  (θ = 2 here: BOTH blocks hit the threshold simultaneously ⟹ pole orders add. Note for A2/θ-seam;
  the (2,1,2) θ is the product-of-two-equal-rlct case, distinct from (2,2,2)'s θ=1.)

## Exact Mathlib anchors (CHECKED)

- `lintegral_prod_mul` (`MeasureTheory`) — `∫⁻_{α×β} f(x)g(y) = (∫⁻ f)(∫⁻ g)` (Tonelli product-split).
- `ENNReal.coe_mul_rpow` / `mul_rpow` — `(G·H)^{-c} = G^{-c}·H^{-c}` on nonneg factors.
- `smoothBlockND_rlct (m : ℕ) : rlctAtOn (fun x : EuclideanSpace ℝ (Fin (m+1)) => ∑ i, x i^2) 0 = ((m+1)/2 : ℝ≥0∞)` — `S1SmoothBlock.lean:164`, DONE/axiom-free.
- `min`-sSup: standard order argument on the admissible-`c` set (`sSup` of an intersection of two
  half-lines `{c<α}∩{c<β} = {c<min α β}`).

## Dependency / coordinate note (one wrinkle for fm)

`smoothBlockND_rlct` is on `EuclideanSpace ℝ (Fin n)`; the (2,1,2) core lives on `Params M`. The
coordinate identification is NOT a free "`Params ≃ ℝ²×ℝ²`" — be honest about the chain:

- `paramsEquivFlat (2,1,2) : Params ≃ᵐ (Fin (flatDim) → ℝ)` gives a SINGLE FLAT vector `Fin 4 → ℝ`
  (NOT a product), `flatDim = 2·1 + 1·2 = 4`. The flat index `FlatIdx` PARTITIONS by layer `s`:
  layer `s=0` = `C^(1)` entries (2 coords = the `a`-block), layer `s=1` = `C^(2)` entries (2 coords =
  the `b`-block).
- To feed `product_min_rlct` (which wants a PRODUCT domain), re-index `Fin 4 ≃ Fin 2 ⊕ Fin 2` by the
  layer partition, then `(Fin 2 ⊕ Fin 2 → ℝ) ≃ᵐ (Fin 2 → ℝ) × (Fin 2 → ℝ)` via Mathlib's
  `MeasurableEquiv.sumArrowEquivProdArrow` (measure-preserving — `sumArrowIsometryEquivProdArrow` / the
  `sumPiEquivProdPi` family, all in Mathlib, CHECKED).
- Under this composite equiv, `dlnLoss (2,1,2) 0 ↦ (∑_{a-coords} ·²)·(∑_{b-coords} ·²) = G(a)·H(b)`.

So the concrete fm chain: (i) `paramsEquivFlat` [DONE, measure-preserving] → (ii) `Fin 4 ≃ Fin 2 ⊕ Fin 2`
layer re-index → (iii) `sumArrowEquivProdArrow` to the product → (iv) `dlnLoss ↦ G·H` → (v)
`product_min_rlct` + 2×`smoothBlockND_rlct 1`. Steps (ii)-(iii) are the genuine GLUE (a finite
re-indexing + the sum-arrow product equiv) — both Mathlib lemmas, NO new infra, but MORE than
"ParamsFlat supplies it directly." This is the only non-mechanical step; flag it so fm budgets the
re-index/product-equiv plumbing (the rest — product-MIN + smoothBlockND + arithmetic — is direct).

## Summary for fm

1. `product_min_rlct` (the new lemma, Tonelli + mul_rpow + positivity + min-sSup) — reusable.
2. `Params (2,1,2) ≃ᵐ (Fin 2 → ℝ)×(Fin 2 → ℝ)` splitting `dlnLoss` to `(a₁²+a₂²)(b₁²+b₂²)` — the chain
   `paramsEquivFlat` → `Fin 4 ≃ Fin 2 ⊕ Fin 2` (layer partition) → `sumArrowEquivProdArrow` (the GLUE).
3. two `smoothBlockND_rlct 1` (each block rlct = 1).
4. arithmetic `min(1,1) = 1 = ½·Mval = lambdaCore(2,1,2)`.
No blow-up, no cover, no G5 — the cheapest immediate ladder rung.
