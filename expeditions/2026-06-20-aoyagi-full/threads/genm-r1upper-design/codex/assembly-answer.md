**1. Finding**

Yes. On a fixed `t`-pivot chart, after the Schur shear the corank variable appears as

```text
frobSq(A0 Q) ~ pivot_part(Q) + frobSq(Γ Q_b),
```

not as `pivot_part(Q) + frobSq Γ`.

For `p = M0 - t`, `q = M1 - t`, `a = pq`, and `rank Q_b = q`, the map

```text
Γ ↦ Γ Q_b
```

has Jacobian factor

```text
det(Q_b Q_bᵀ)^(p/2),
```

so the atom produces

```text
det(Q_b Q_bᵀ)^(-p/2) · P_tail^(-(c' - a/2)).
```

That is the honest residual. It is not bounded above by a constant times `P_full^(-a/2)`. For instance, take `q = 1`, `P_tail ≃ 1`, and `‖Q_b‖ = ε`; then the Gram residual is `ε^(-p)` while `P_full^(-a/2) ≃ 1`. So this is a real structural problem for the current `jointPeelIntegral` target, not a constant-factor repair.

**2. Recommendation**

Choose **A**: keep `Γ` explicit in `sjBoundaryPeel`.

Define the piece-3 target chartwise as something like

```text
gammaPeelIntegral κ t c' :=
  ∫ A' ∫ Γ (P_tailκ(Q(A')) + frobSq(Γ Q_bκ(A')))^(-c')
```

and prove

```text
routeMLayerBoxIntegral M c' 1
  ≤ ∑_{t,κ} C_{t,κ} · gammaPeelIntegral κ t c'.
```

This is cleaner in Lean because piece 3 then uses only the closed MP/front-split, Schur shear, chart cover, and integrated block/radial reduction. The rank condition on `Q_b`, the Gram determinant Jacobian, and the null exceptional set all belong to the later finiteness/isotropization pieces.

Option **B** is honest only if `jointPeelIntegral` is redefined with the Gram determinant. But it mixes the hard a.e. determinant change-of-variables into `sjBoundaryPeel`, and it still does not recover the currently defined `P_full^(-a/2)` target.

**3. Lemma Sequence**

1. `pivotChartCover_lintegral_le_sum` — plumbing.  
   Use `pivotLocus_eq_iUnion` and finite subadditivity to bound the `A0` integral by a sum over `t` and pivot charts `κ`.

2. `schurShear_chart_lintegral` — load-bearing.  
   On chart `κ`, apply `measurePreserving_shearSub` and `schur_cov` to rewrite the chart contribution with `Γ = D - C A⁻¹B`.

3. `chartRadialBlock_to_gammaPeel` — load-bearing.  
   Integrated over `A'` and chart variables, prove the per-chart blow-up bound

   ```text
   chartContribution κ
     ≤ Cκ ∫ A' ∫ Γ
          (P_tailκ(Q(A')) + frobSq(Γ Q_bκ(A')))^(-c').
   ```

   This must be integrated, not a fixed-`Q` pointwise inner estimate.

4. `sjBoundaryPeel_explicitGamma` — plumbing theorem.  
   Assemble 1–3:

   ```text
   routeMLayerBoxIntegral M c' 1
     ≤ ∑_{t,κ} C_{t,κ} · gammaPeelIntegral κ t c'.
   ```

5. `rightMul_gramJacobian` — load-bearing.  
   If `rank Q_b = q`, prove the Jacobian for `Γ ↦ Γ Q_b` is `det(Q_b Q_bᵀ)^(p/2)`. Handle `p = 0` or `q = 0` as trivial edge cases.

6. `gammaAtom_fullRank_gramResidual` — load-bearing.  
   For `0 < w`, `rank Q_b = q`, and `c' > pq/2`:

   ```text
   ∫ Γ (w + frobSq(Γ Q_b))^(-c')
     ≤ C · det(Q_b Q_bᵀ)^(-p/2) · w^(-(c' - pq/2)).
   ```

7. `gammaPeel_le_gramPeel_ae` — load-bearing.  
   Per chart, prove `{det(Q_b Q_bᵀ)=0}` is null, also handle `{P_tail=0}` if the atom needs `w>0`, then apply 6 by `lintegral_congr_ae` before summing over charts.

**4. Biggest Risk**

The biggest risk is the a.e. full-row-rank proof for the actual tail product map, not for an abstract matrix `Q`. If `det(Q_b Q_bᵀ)` is identically zero for some chart because of a dimension bottleneck or tail architecture constraint, the Gram atom is unavailable.

Cheapest exact check: for every `(t, κ)`, exhibit one tail configuration inside the box with `rank Q_bκ = M1 - t` and `P_tailκ > 0`. That proves the determinant and tail-loss polynomials are not identically zero, so their zero loci are null.