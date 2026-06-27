# DLN (2,2,2) achiever-chart `|det Dφ| = |x0|²·|x4|`: factorization obstruction, best route?

Lean 4 / Mathlib formalisation. I have a polynomial chart `chartParams222 : (Fin 8 → ℝ) → Params M222`
(then `phi := paramsEquivFlat ∘ chartParams222 : (Fin 8 → ℝ) → (Fin 8 → ℝ)`), with two 2×2 layers:
- `chartA0 = !![x4, x4·x1; x5, x5·x1 + x6·x0]`
- `chartA1 = !![x0 − x1·x2, x0·x7 − x1·x3; x2, x3]`
Flat Jacobian det = EXACTLY `−x0²·x4` (sympy-verified). I need `|det Dφ| = |x0|²·|x4|` in Lean.

The existing discharged anchors prove `|det Dφ|` by FACTORING the chart as `pack ∘ T` where `T` is a
composite of `pivotBlowupOn` factors (each det `|pivot|^{card−1}`) ∘ a det-1 unitriangular shear, and
`pack` is a measure-preserving coordinate reshape (`|det|=1`). E.g. (3,3,4): `T = bsubst ∘ shear ∘ pb`,
det `u₀⁷·u₁²` (`pb` det `u₀⁷`, `bsubst` det `u₁²`, shear det 1).

THE OBSTRUCTION for (2,2,2): the det `|x0|²·|x4|` does NOT factor cleanly this way. `det(bsub∘pb) = x0²·x4`
where `pb = pivotBlowupOn {x0,x6,x7}(x0)` (det x0²) and `bsub = pivotBlowupOn {x1,x4}(x4)` (det x4, i.e.
x1↦x4·x1). BUT: the coord `x1` appears in the target BOTH as `x4·x1` (chartA0_01) AND as BARE `x1`
(chartA1_00 = x0 − x1·x2). A blow-up `x1 ↦ x4·x1` is GLOBAL, so it can't produce both `x4·x1` and bare
`x1` from the same input coord. Also `x4·x1` and `x5·x1` are products of two FREE (kept) coords, which a
det-1 nilpotent shear cannot produce as a single entry. So the clean `pack ∘ pivotBlowup ∘ shear`
factorization (the proven template) seems unavailable.

This chart comes from the genuine DLN "Route 2a" engine (a Schur-coupled decoder `B_det222`); a pure
radial blow-up is RULED OUT here because (2,2,2) is a genuine MULTI-boundary node (rank drops at two
boundaries) — a pure radial chart fails the RATE `F = u²·V` (the Schur coupling is load-bearing). So I
cannot just swap in a (2,2,1)/(4,4,2,2)-style pure-radial chart.

QUESTIONS:
1. Is there a `pack ∘ (pivotBlowup factors) ∘ (det-1 shear)` factorization I'm missing? Specifically: can
   the `x4·x1` / `x5·x1` (free×free products) be produced by a CLEVER choice of which coords are
   "blown up" vs "kept", or by a NON-unitriangular but still det-1 (or det = clean monomial) map?
   (E.g. treat `x1` as the bsub-pivot and `x4` as blown, so `x4 ↦ x1·x4`? Then chartA0_00 = x4 becomes
   x1·x4 — wrong. Hmm.) Is there ANY composite of axis-aligned blow-ups + a triangular shear giving the
   target, perhaps with a different pack permutation?
2. If no clean factorization: what is the cleanest Lean route to `|det (fderiv phi u)| = |x0|²·|x4|`
   DIRECTLY? The fderiv is an explicit 8×8 Jacobian with simple polynomial entries. Options:
   (a) Build the fderiv as an explicit `Matrix (Fin 8) (Fin 8) ℝ` (via `HasFDerivAt` of each polynomial
       entry + `ContinuousLinearMap` assembly), then compute `Matrix.det` of the 8×8 symbolically
       (`Matrix.det_fin_succ` expansion, or row operations). Is an 8×8 symbolic det tractable, given the
       Jacobian is sparse (each row has ≤ 3 nonzero entries)?
   (b) A cofactor / block decomposition exploiting sparsity (the Jacobian has a block/triangular
       structure after a row-column permutation?).
   (c) Express the chart as `phi = L ∘ g` where `L` is linear (measure-preserving, det 1) and `g` has a
       det I can compute via `LinearMap.det_comp` + a partial blow-up.
3. Given the difficulty, is the RIGHT MOVE to bank the chart-equality bridge (`chartParamsGen = chartParams222`,
   DONE) + the rate, and treat the FULL `cov`/atom-discharge as a separate scoped sub-build (multi-tide),
   rather than force it now? Or is route (a)/(b) genuinely a bounded ~1-tide build?

The Jacobian (columns = ∂/∂x0..x7, rows = the 8 entries A0_00,A0_01,A0_10,A0_11,A1_00,A1_01,A1_10,A1_11):
```
row A0_00 (x4):        [0,0,0,0,1,0,0,0]
row A0_01 (x4 x1):     [0,x4,0,0,x1,0,0,0]
row A0_10 (x5):        [0,0,0,0,0,1,0,0]
row A0_11 (x5 x1+x6 x0):[x6,x5,0,0,0,x1,x0,0]
row A1_00 (x0-x1 x2):  [1,-x2,-x1,0,0,0,0,0]
row A1_01 (x0 x7-x1 x3):[x7,-x3,0,-x1,0,0,0,x0]
row A1_10 (x2):        [0,0,1,0,0,0,0,0]
row A1_11 (x3):        [0,0,0,1,0,0,0,0]
```
det = −x0²·x4.

Give a crisp recommendation + concrete Lean approach.
