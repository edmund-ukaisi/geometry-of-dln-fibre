**Step List**

Core assumption: add `hc2 : 2 < c'`; handle `c' ≤ 2` separately by exponent bump to `3`.

1. **Normalize the pivot first.**  
   Define the 3x3 analogue of `Rmat334norm`:
   ```lean
   Rnorm p z r c :=
     Rmat3 p (e.symm (0, z))
       ((Equiv.swap (e3.symm p).1 0) r)
       ((Equiv.swap (e3.symm p).2 0) c)
   ```
   Prove/copy local atoms:
   `frobSq_rmatMul_perm3`, `matBox34_rowperm_lintegral T`, then
   ```lean
   innerS3 ... = ∫⁻ S in matBox 3 4 T,
     ofReal ((frobSq (rmatMul (Rnorm p z) S)) ^ (-c'))
   ```
   This is verifiably the same pattern as `RouteM334Ratiofin.frobSq_rmatMul_perm` and `matBox34_rowperm_lintegral`, but you need the `T`-general version.

2. **Get uniform N2b constants once.**
   ```lean
   obtain ⟨c₀, c₁, hc₀, hc₁, hN2⟩ :=
     schur_minorPivot_split (r := 3) (p := 4) 1 (by norm_num)
   ```
   Keep `c₀` outside all `z`/`S` binders.

3. **For fixed `z` in the cube, apply N2b to `Rnorm p z`.**  
   Prove:
   `Rnorm p z 0 0 = 1`, `∀ i j, |Rnorm p z i j| ≤ 1`.  
   The `j=1` max-minor hypothesis is just:
   ```lean
   |R.submatrix I J).det| ≤ |R00| = 1
   ```
   using `Matrix.det_fin_one` and the entry bound. Nonzero minor follows from `R00 = 1`.

4. **Pin one explicit Schur complement.**  
   Define
   ```lean
   ScExp z a b :=
     Rnorm p z a.succ b.succ - Rnorm p z a.succ 0 * Rnorm p z 0 b.succ
   ```
   Use `hN2 R (fun _ _ => 0) ...` to obtain a witness `Sc`, then prove `Sc = ScExp z`. For every `S`, reapply `hN2 R S ...`; use the structural `Sc = ...` equality to rewrite the per-`S` witness back to this same `ScExp`.

5. **Apply `schurSplit_lintegral_le` pointwise in `z`.**  
   Let
   ```lean
   F S := frobSq (rmatMul (Rnorm p z) S)
   D S := frobSq (fun a : Fin 1 => rmatMul (Rnorm p z) S ⟨a, by omega⟩)
        + frobSq (rmatMul (ScExp z) (fun a : Fin 2 => S a.succ))
   ```
   Then:
   ```lean
   ∫⁻ S in matBox 3 4 T, ofReal ((F S)^(-c'))
     ≤ ofReal (c₀^(-c')) *
       ∫⁻ S in matBox 3 4 T, ofReal ((D S)^(-c'))
   ```
   Banked lemma: `schurSplit_lintegral_le`.

6. **Integrate over `z`.**  
   Use `setLIntegral_mono_ae'` on the cube and `lintegral_const_mul'` to reduce to proving finiteness of
   ```lean
   ∫⁻ z in cube8, ∫⁻ S in matBox 3 4 T, ofReal ((D z S)^(-c'))
   ```

7. **Split `S = row0 × Sbot`, then shear `row0`.**  
   Use
   ```lean
   eS := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => Fin 4 → ℝ) 0
   ```
   with `volume_preserving_piFinSuccAbove`, `setLIntegral_prod`, and `lintegral_lintegral_swap`.  
   Translate
   ```lean
   row0 ↦ row0 + fun j => Rnorm p z 0 1 * Sbot 0 j
                         + Rnorm p z 0 2 * Sbot 1 j
   ```
   and enlarge to a common radius
   ```lean
   K := 1 + 3 * T
   ```
   since `row0 ∈ [-T,T]^4`, `|shift| ≤ 2T`, so translated row is in `morseBox 4 (3*T) ⊆ morseBox 4 K`; also `matBox 2 4 T ⊆ matBox 2 4 K`.

8. **Split the normalized `z` coordinates.**  
   Use the `RouteM334Ratiofin` pattern:
   ```lean
   cellOf : (Fin 2 × Fin 2) ⊕ Fin 4 → Fin 3 × Fin 3
   -- inl (i,k) ↦ (i.succ,k.succ)
   -- inr 0,1 ↦ (1,0),(2,0)
   -- inr 2,3 ↦ (0,1),(0,2)

   zσ p : Fin 8 ≃ (Fin 2 × Fin 2) ⊕ Fin 4

   zE p : (Fin 8 → ℝ) ≃ᵐ
     ((Fin 2 × Fin 2 → ℝ) × (Fin 4 → ℝ))
   ```
   Prove the readback:
   ```lean
   ScExp z = matOf ((zE p z).1) - bgShift ((zE p z).2)
   ```
   where `bgShift v = !![v 0 * v 2, v 0 * v 3; v 1 * v 2, v 1 * v 3]`.

9. **Change variables in `z` and Tonelli.**  
   Use `zE_measurePreserving`, the preimage identity
   ```lean
   cube8 = zE p ⁻¹' (boxP 1 ×ˢ vbox)
   ```
   and then `Measure.volume_eq_prod`, `setLIntegral_prod`, `lintegral_lintegral_swap`. You should arrive at:
   ```lean
   ∫⁻ v in vbox, ∫⁻ M in boxP 1,
     ∫⁻ S in matBox 2 4 K, ∫⁻ U in morseBox 4 K,
       ofReal ((∑ i, U i^2
         + frobSq (rmatMul (matOf M - bgShift v) S)) ^ (-c'))
   ```

10. **Feed `resolvedShiftR2c3_le` per boundary `v`.**  
    For `v ∈ vbox`, set `Sh := bgShift v`, `B := 1`. Prove `∀ i j, |Sh i j| ≤ 1`.  
    Convert `M : Fin 2 × Fin 2 → ℝ` to a matrix via `matOfEquiv`, enlarge `boxP 1` to `matBox 2 2 K`, then apply:
    ```lean
    resolvedShiftR2c3_le Sh 1 hB K hK c' hc2 hc'
    ```
    This gives a bound independent of `v`.

11. **Finish the boundary volume.**
    ```lean
    ∫⁻ _v in vbox, C = C * volume vbox < ⊤
    ```
    Use compactness of `[-1,1]^4`, `coreSchur2Val_lt_top (c'-2)` with `0 < c'-2` and `c'-2 < 2`, and `ENNReal.mul_lt_top`.

**Answers**

Q1: choose **(a)**. The clean equiv is the `zσ/zE` pattern, not raw `Fin 8` arithmetic and not `Fin 4 × Fin 4` first. Use `(Fin 2 × Fin 2) ⊕ Fin 4`, then `sumPiEquivProdPi`. This keeps the raw `M22` block matrix-shaped and the boundary vector ordered as `(g0,g1,b0,b1)`. You cannot avoid identifying the four raw coordinates; the mitigation is to identify them abstractly by `zslot`, not by numerals.

Q2: use **`resolvedShiftR2c3_le`**. Do the row0 shear yourself, then feed the shifted resolved lemma. Do not bypass to `core_T_peel_le_ae_c3`; that would re-open the a.e. positivity and residual translation work already banked. The new lemma is exactly the right granularity because it keeps `raw M22` free and absorbs `Sh = M21*M12`.

Q3: yes, the permutation to `(0,0)` is required. N2b’s pivot minor is the top-left `j×j` block. Do it before the `z` split. It does not interact badly with `z`; define the split on the normalized off-pivot entries. This is precisely why `zslot p` is p-dependent.

**Thrash Rank**

1. **`z` coordinate split after pivot normalization.**  
   Mitigation: copy the `cellOf/zslot/zσ/zE/readback` architecture from `RouteM334Ratiofin`, with new c3-specific names. Do not hand-simp raw `Fin 8` indices.

2. **N2b witness `Sc` matching `raw - bgShift`.**  
   Mitigation: prove two small lemmas before integrals: fixed-witness uniqueness from N2b’s structural `Sc = ...`, and the `j=1`, `R00=1` simplification of the Schur complement. Do not inline this inside `schurSplit_lintegral_le`.