# Consult: cleanest Lean 4 / Mathlib (v4.29) architecture for a matrix-integral bound

You are a Lean 4 + Mathlib (pinned v4.29) formalisation design reviewer. I need the CLEANEST route
(fewest fiddly measure-theory obstructions) for one theorem. Give a decorrelated architecture opinion +
name the exact Mathlib lemmas + flag pitfalls. NO need to write full proofs; I want the route + the
lemma names + the traps.

## The theorem (all real matrices)

For `a b n p : ℕ`, `b ≤ n`, `a + b ≤ p`:
```
∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ Acor : Fin b → Fin n → ℝ,
  (∫⁻ S in matBox n p 1, ENNReal.ofReal ((chargeGramDet Acor S) ^ (-(a:ℝ)/2)))
    ≤ C * ENNReal.ofReal (((Matrix.of Acor * (Matrix.of Acor)ᵀ).det) ^ (-(a:ℝ)/2))
```
where:
- `matBox n p 1 = {S : Fin n → Fin p → ℝ | ∀ i k, S i k ∈ [-1,1]}` (n×p entries free in [-1,1]).
- `chargeGramDet Acor S = det((Acor·S)·(Acor·S)ᵀ)` = the b×b Gram det of `Acor·S` (Acor is b×n, S is n×p,
  so Acor·S is b×p). It equals `det(Acor·(S·Sᵀ)·Acorᵀ)` (banked `chargeGramDet_eq_conj`).
- Integral is `lintegral` (`∫⁻`, ENNReal), Tonelli applies freely.

## Chosen math route (verified on paper + numerically; NON-SPECTRAL, avoids matrix sqrt)

1. **Rank-deficient `Acor`** (`det(Acor Acorᵀ)=0`): `chargeGramDet = 0` pointwise (banked
   `chargeGramDet_eq_zero_of_corank_singular`). For `a ≥ 1` both sides 0. Handle `a=0` as a global trivial
   branch (integrand ≡ 1, C = vol(matBox)).

2. **Full-row-rank `Acor`**: enclose the box in the "column-ball" `{S | ∀ k, ‖S_{·k}‖ ≤ √n}` (each column
   S_{·k} = fun i => S i k ∈ ℝ^n has ‖·‖ ≤ √n on the box). Integrand ≥ 0 so `lintegral_mono_set`.

3. **O(n)-invariance of the column-ball integral.** For any orthogonal `O` (n×n), the map `S ↦ (O applied to
   each column of S)` (i.e. `Matrix.of S ↦ O * Matrix.of S`) is measure-preserving and preserves the
   column-ball. Under it `chargeGramDet(Acor, O·S) = chargeGramDet(Acor·O, S)`. So
   `∫_{ball} chargeGramDet(Acor,·)^{-a/2} = ∫_{ball} chargeGramDet(Acor·O,·)^{-a/2}`.

4. **Rotate to canonical form.** Full-rank Acor ⟹ ∃ orthogonal O with `Acor·O = [L | 0]` (L invertible b×b;
   last n-b columns land in ker(Acor)). Construct via an orthonormal basis of `ker(Acor)` (dim n-b) extended
   to ℝ^n (`Orthonormal.exists_orthonormalBasis_extension`), O's last n-b columns = that ker basis.
   Then `det(L·Lᵀ) = det(Acor·Acorᵀ)` (O orthogonal), and `[L|0]·S = L·S'` where `S'` = first b rows of S,
   so `chargeGramDet([L|0], S) = (det L)²·det(S'·S'ᵀ) = det(Acor Acorᵀ)·det(S'·S'ᵀ)`.

5. **Residual integral.** `∫_{ball} det(S'·S'ᵀ)^{-a/2} dS` (S' = first b rows). Split S = (S', S'') (first b /
   last n-b rows); the column-ball domain `{∀k, ‖S'_{·k}‖²+‖S''_{·k}‖² ≤ n}` ⊆ product
   `{cols S' in ball_b(√n)} × {cols S'' in ball_{n-b}(√n)}`; integrand indep of S''; Fubini gives a finite
   `vol(ball_{n-b}(√n))^p` factor times `∫_{cols S' in ball_b(√n)} det(S'S'ᵀ)^{-a/2}`. And
   `{cols in ball_b(√n)} ⊆ {rows in ball_p(√(pn))}`, so bounded by the banked
   `qbox_lintegral_lt_top` (b rows in EuclideanSpace ℝ (Fin p), radius √(pn), finite iff a < p-b+1 ⟺ a+b≤p).
   The constant `L₀` is uniform in Acor.

## Banked pieces I can call
- `qbox_lintegral_lt_top {q a} (b) (b≤q) (a<q-b+1) (R) : ∫⁻ Q in (ball 0 R)^b (Fin q Euclidean), ofReal((gram ℝ Q).det^(-a/2)) < ⊤`
- `detGram_lintegral_lt_top {r n} (r≤n) (a<n-r+1) : ∫⁻ X in matBox r n 1, ofReal((of X * (of X)ᵀ).det^(-a/2)) < ⊤`
- `mulLeftₚ c K : (Fin c → Fin t → ℝ) →ₗ[ℝ] _`, `(mulLeftₚ c K Y) k = K.mulVec (Y k)`; `det_mulLeftₚ = (det K)^c`;
  `lintegral_comp_mulLeftₚ c K (det K≠0) g meas : ∫⁻ Y, g (fun k => K.mulVec (Y k)) = ofReal(|det K|^c)⁻¹ · ∫⁻ Y, g Y`.
  (This is a full-space CoV over `Fin c → Fin t → ℝ`, K applied to the INNER Fin t index.)
- `matToFlatRect`/`measurePreserving_matToFlatRect` (piCurry + arrowCongr' reindex recipe).
- `LinearIsometryEquiv.measurePreserving (f : E ≃ₗᵢ[ℝ] F) : MeasurePreserving f` (E,F fin-dim real inner prod).
- `Orthonormal.exists_orthonormalBasis_extension`, `OrthonormalBasis`, `volume_preserving_pi`,
  `volume_preserving_arrowCongr'`, `measurePreserving_piCurry`.

## Mathlib v4.29 trap I already know
Matrix-space measure CoV hits a MODULE DIAMOND (`Matrix.module` vs `NormedSpace.toModule`):
`map_linearMap_addHaar_eq_smul_addHaar` won't unify for a LinearMap built over `Matrix.module` (e.g. left-mult
`X ↦ O*X` on n×p matrices). The banked `mulLeftₚ` DODGES this by transcribing over the raw pi type with K
applied to the INNER index — but my O acts on the COLUMN (n) index which is the OUTER index of
`S : Fin n → Fin p → ℝ`. So `mulLeftₚ` needs the TRANSPOSED orientation `Fin p → Fin n → ℝ`.

## My questions

Q1. **Step 3 (the O(n) column CoV)**: which is cleaner —
  (route A) transpose `S : Fin n → Fin p → ℝ ≃ᵐ Fin p → Fin n → ℝ` (measure-preserving, via piCurry +
    arrowCongr' with `prodComm`, following `matToFlatRect`), then `mulLeftₚ p O` (|det O|^p = 1); or
  (route B) represent S columns in `Fin p → EuclideanSpace ℝ (Fin n)` via one measure-preserving equiv, act
    by the isometry `f : E ≃ₗᵢ E` componentwise (`volume_preserving_pi` of `f.measurePreserving`), balls
    preserved by isometry?
  Which has fewer defeq/instance traps at v4.29? Any obstruction with `mulLeftₚ`'s full-space CoV vs my
  needing a SET (ball) integral — do I enclose in the ball THEN CoV on full space, or CoV then restrict?
  (Note `mulLeftₚ`'s CoV is full-space; for O with |det|=1 the constant is 1, and the ball is O-invariant.)

Q2. **Step 4 canonical form**: cleanest way to get `O` orthogonal with `Acor·O = [L|0]` and
  `det(L Lᵀ) = det(Acor Acorᵀ)` from `Orthonormal.exists_orthonormalBasis_extension` on a ker(Acor) basis?
  Is it cleaner to (i) construct the orthonormal basis matrix O and prove `Acor·O` has zero last columns via
  `Acor·(ker vector)=0`, or (ii) avoid the explicit block form and directly manipulate the integral? Which
  Mathlib API for "matrix of an orthonormal basis is orthogonal" (`OrthonormalBasis.toMatrix`,
  `Matrix.mem_orthogonalGroup`, `OrthonormalBasis.toBasis` ...)?

Q3. Do you see a MATERIALLY simpler overall route than steps 3-5 (e.g. one that avoids constructing O
  entirely, or avoids the transpose)? I considered the symmetric matrix square root R with Acor = R·Q,
  Q orthonormal — but Mathlib v4.29 has no ready PSD matrix sqrt (LDL deprecated, CFC heavy). Is there a
  slicker non-spectral factorization, or a Cauchy–Binet identity that collapses this?

Q4. Any pitfalls in the Fubini split (step 5) — bounding a coupled ball region `{‖α‖²+‖β‖²≤n}` by the
  product of balls, in `lintegral` form? Best Mathlib lemmas (`lintegral_mono_set`, `setLIntegral`, product
  measure / `Measure.prod`, `lintegral_prod`)?

Be concrete and terse. Name lemmas. Flag anything in my route that will NOT work at v4.29.
