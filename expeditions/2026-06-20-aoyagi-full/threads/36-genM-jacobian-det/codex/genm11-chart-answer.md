**Recommendation: C Hybrid**

Use the CLEAN flat-coordinate substrate, but not literal `cleanPhi` or `routeMCore_cleanPhi`.

Define `phiSm` as a flat self-map: a single coordinate update at the canonical deepest `(row 0, col 0)` slot:
```lean
phiSm u := Function.update u p (u p - smearShift u)
```
where `smearShift u = ∑ r, Λ₀ 0 r * S r`, with `Λ₀` computed from the front product and `S` the deepest residual rows.

Then define:
```lean
smParams M ... u := (paramsEquivFlat M).symm (phiSm M ... u)
```

This keeps the MP proof cheapest: `phiSm` is exactly one det-1 shear. The rate proof is direct through `prodAux_frontScalarShear_cancel`.

Do not route through `cleanParams_eq_scaleLayer`, `prod_scaleLayer`, or `dlnLoss_homogeneous_layer`: the smeared deepest layer is not a whole-layer scalar multiple. Reuse only the CLEAN flat decode infrastructure: `paramsEquivFlat_symm_decode`, `flatCoordOf`, `deepLayer`, and the style of coordinate lemmas.

**Lemma Order**

1. Canonical indices, not `hne.choose`:
```lean
def smPivotRow ... : Fin (M (deepLayer M hL).castSucc) := 0
def smDeepCol ... : Fin (M (deepLayer M hL).succ) := 0
def smPivotCoord ... : Fin (routeMAmbient M) :=
  flatCoordOf M ⟨⟨deepLayer M hL, smPivotRow ...⟩, smDeepCol ...⟩
```
This must match column `0` in `prodAux_frontScalarShear_cancel`.

2. Front/residual blocks:
```lean
def baseParams u := (paramsEquivFlat M).symm u
def frontProd u := prodAux M (baseParams u) (L - 1) ...

def P₁ u : Matrix (Fin (M 0)) (Fin 1) ℝ := ...
def P₂ u : Matrix (Fin (M 0)) Resid ℝ := ...
def Λ₀ u := (P₁ u).transpose * P₁ u ⁻¹ * (P₁ u).transpose * P₂ u
def Sbot u : Resid → ℝ := ...
def smearShift u := ∑ r, Λ₀ u 0 r * Sbot u r
def smU u := ∑ i, (frontProd u i 0)^2
```
Use explicit `Fin 1` inverse algebra for measurability; generic `Matrix.inv` measurability is `verify`.

3. Chart and decode:
```lean
def phiSm u := Function.update u smPivotCoord (u smPivotCoord - smearShift u)
def smParams u := (paramsEquivFlat M).symm (phiSm u)

lemma smParams_front_eq ...
lemma smParams_pivot_eq ...
lemma smParams_residual_eq ...
```
These reuse `paramsEquivFlat_symm_decode`.

4. Prefix unaffected:
```lean
lemma prodAux_eq_of_eq_on_prefix
  (h : ∀ s, (s : ℕ) < k → A s = B s) :
  prodAux M A k hk = prodAux M B k hk
```
Then:
```lean
lemma frontProd_smParams_eq :
  prodAux M (smParams u) (L - 1) ... = frontProd u
```

5. Plug in Substrate B:
```lean
lemma front_cancel_offpole (hpole : smU u ≠ 0) :
  P₁ u * (((P₁ u).transpose * P₁ u)⁻¹ * (P₁ u).transpose * P₂ u) = P₂ u
```
This is exactly `prodAux_frontScalarShear_cancel`.

6. Final product telescope:
```lean
lemma prod_smParams_eq_pivot_front (hpole : smU u ≠ 0) :
  prod M (smParams u) = (u smPivotCoord) • frontCol0Matrix u
```
Use `prodAux_succ`, `Fin.sum_univ_succAbove`, and the cancellation lemma. Then:
```lean
lemma routeMCore_phiSm_offpole (hpole : smU u ≠ 0) :
  routeMCore M (phiSm u) = (u smPivotCoord)^2 * smU u
```
`smU_nonneg` is by sum of squares. `measurable_smU` follows from `continuous_prodAux`.

**Measure Preserving**

A single shear is enough. Do not use one shear per residual coordinate.

State a wrapper around the existing repo lemma:
```lean
theorem measurePreserving_shearAt_fin {N : ℕ} (p : Fin N)
    (g : (Fin (N - 1) → ℝ) → ℝ) (hg : Measurable g) :
    MeasurePreserving
      (fun x : Fin N → ℝ =>
        Function.update x p (x p + g (fun k => x (p.succAbove k))))
      volume volume
```
Implement by matching `N, p` as in `measurePreserving_rowShear`, then call existing `measurePreserving_shearAt`.

For `phiSm`, set `g := - smearShift` transported through `succAbove`; prove it does not read `p`.

**Biggest Risk**

The main wall is not MP and not the front product expansion. It is the generic index alignment of the final-layer split:

- `smPivotCoord` must be the canonical deepest `(row 0, col 0)` slot, not `deepestPivot := hne.choose`.
- residual rows must be represented as the complement of that row and matched to the `σ` used in `prodAux_frontScalarShear_cancel`.
- the proof that `P * A_last = u_p • P₁` needs a reusable `Fin.sum_univ_succAbove` split over arbitrary `m1`, which `(1,2,1)` hid with `Fin.sum_univ_two`.

Surface that first. If this alignment is wrong, the front fact cannot plug in cleanly.