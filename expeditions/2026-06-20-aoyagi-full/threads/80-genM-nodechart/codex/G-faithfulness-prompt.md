# G-definition faithfulness check — the radial/boundary det split (Lean 4 / Mathlib v4.29)

## Setup
Deep-linear-network achiever chart `φ = phiFlatLiveR1 : (Fin N → ℝ) → (Fin N → ℝ)`, N = flatDim M, opaque
in `M : Fin (L+1) → ℕ`. Goal (sorry-free ∀M): `|det (fderiv φ u)| = |u_p|^{minAdm M − 1} · ∏_{s:Fin L}
(|det K_s|^{r_s+c_s}·∏_i|q_{s,i}|^{2(t_s−1−i)})`, where `u_p = u(structPivot)`.

A pen-and-paper cert (exact at (2,2,2)/(3,3,3,3)/(2,3,2)/(4,3,3,2)/(3,4,3,3)) PINNED the radial model:
the radial blow-up `pivotBlowupOn(active, p)` with `active = {p} ∪ {free entries of the u-scaled
Rmat_k(k≥1)/Rfin_L}`, `active.card = minAdm`, det `u_p^{minAdm−1}`. Every chart output is `h_j(z)` or
`h_j(z) + u_p·r_i` (the r_i = the u-scaled R/leaf free coords, disjoint from K/X/N/W; u_p LINEAR).

## The architecture I was about to build (Route A, det-level)
`J := toMatrix' (fderiv φ u)`. Lemma (banked, general): `|det (of fun i j => (if j∈S then u else 1)·G i j)|
= |u|^{S.card}·|det G|` (`Matrix.det_mul_row`). Then claim `J = scaledColumns Rcols u_p G` with
`Rcols = active \ {p}` (card minAdm−1) and `G` u-free ⟹ headline.

## MY FINDING (sympy-exact, the reason for this check) — the naive G is WRONG

I tested two candidate `G`s against the exact Jacobian:

1. **`G = Jacobian(φ̃)` where `φ̃` = φ with the radial scalar set to 1 (strip u from the u·R terms):**
   - At (2,2,2): `det J = -x0²·x4`, `det G = -x4`, and `det J = x0²·det G` ✓ (coincidence).
   - At (3,3,3,3): **`det G = 0`** (the radial=1 chart DEGENERATES), so `det J = x0⁵·det G` FAILS.
   ⟹ `G = Jacobian(radial=1 chart)` is WRONG in general.

2. **The pure scaled-columns form `J i j = (if j∈Rcols then u_p else 1)·G i j` is FALSE entrywise**, even
   at (2,2,2): the PIVOT column (j = p) of `J` carries the values `r_i` (since `∂(u_p·r_i)/∂u_p = r_i`),
   but a scaled-columns `G` has `0` there. Exact discrepancy: entries `(3,0)` and `(5,0)` (the pivot column
   j=0): `J = x6, x7` (the r_i values) vs scaledColumns `= 0`.
   ⟹ Codex's clean `det_mul_row`-style scaled-columns lemma does NOT model the real Jacobian. The radial
   blow-up's fderiv is an "arrow" (pivot column carries the actives), NOT a diagonal column-scaling.

3. **The genuine factorization is `det J = det(Prad)·det(Prad⁻¹·J)`** where `Prad =
   pivotBlowupOnDeriv(active,p)` (det `u_p^{minAdm−1}`). `Prad⁻¹·J` has `1/u_p` entries (cancel in det,
   but NOT polynomial). `bnd := det(Prad⁻¹·J)` is u-free, and EQUALS the engine product directly:
   verified at (3,3,3,3) `bnd = y1⁴y4²y9³ = |K_1|²·|q_0|²·|K_2|³` (the LDU q-product supplies the extra y1²).

## Questions

1. **Is the right Lean spine `det J = det(Prad)·det(Prad⁻¹·J)` via `Matrix.det_mul` on `J = Prad·(Prad⁻¹·J)`,
   for `u_p ≠ 0`, then a separate `u_p = 0` argument (both sides 0 when minAdm−1 ≥ 1)?** The `Prad⁻¹·J`
   has `1/u_p` entries — is `LinearMap.det_comp`/`Matrix.det_mul` with `Prad` the invertible radial CLM
   (`pivotBlowupOnDeriv` is invertible iff `u_p ≠ 0`) the clean route, accepting the `u_p=0` case split?
   OR is there a division-free factorization I'm missing?

2. **Better: skip the intermediate `G` matrix entirely.** Since `bnd = det(Prad⁻¹·J)` EQUALS the engine
   product `∏_s engine_s` directly (no clean polynomial `G`), should the spine be:
   `|det J| = |det Prad| · |det(Prad⁻¹·J)| = |u_p|^{minAdm−1} · (the engine product)`,
   where the SECOND factor is identified with the engine via the per-boundary block structure of
   `Prad⁻¹·J` (or of `φ` composed with the radial blow-up's inverse)? Does composing `φ` with the radial
   chart's inverse (a genuine map, the "de-blown-up" chart) give a clean u-free map whose Jacobian IS the
   boundary frames — i.e. `φ = (radial blow-up) ∘ ψ` with `ψ` u-free, then `det Dφ = det(radial)·det(Dψ)`
   by the chain rule (composition, not matrix inverse)? Is `ψ := pivotBlowupOn(active,p).symm ∘ φ`
   well-defined and u-free (the cert says u only multiplies the r_i, which the blow-up inverse divides out
   — but at the MAP level, is the blow-up invertible/does this compose cleanly)?

3. **Faithfulness vs the pinned radial model:** the radial model is `V 0 = ℝ^minAdm`, `f 0 =
   pivotBlowupOn(active, structPivot)`. My finding says the pivot column of `Dφ` carries the r_i — is that
   CONSISTENT with the radial blow-up being `f 0` (the blow-up's fderiv IS the arrow with the pivot column
   carrying actives)? I.e. is the genuine decomposition `Dφ = (radial arrow) · (boundary)` where the radial
   arrow is exactly `pivotBlowupOnDeriv`, confirming the cert's model and just requiring the
   composition/`det_mul` route rather than scaled-columns? Confirm or refute that the radial-arrow
   factorization (not scaled-columns) is the faithful one.

4. **What is the cleanest division-free Lean statement of `det J = u_p^{minAdm−1} · bnd`** given `bnd` is
   only definable as `det(Prad⁻¹·J)` (rational) or as the engine product (the target)? Prove `det J =
   u_p^{minAdm−1}·E` directly where `E := ∏_s engine_s` (a known polynomial), via the
   composition/chain-rule route, sidestepping any intermediate `G` matrix?

Be concrete, skeptical, Lean-v4.29-specific. The key correction: the naive scaled-columns/radial=1 `G` is
WRONG; what is the faithful, division-free spine?
