## 1. FEASIBILITY

**BOUNDED labour**, provided the pen proof supplies explicit pivot/blow-up coordinates—not merely rank-stratum codimensions. Mathlib already has the needed finite-dimensional CoV theorem, `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul`; no general resolution framework is required.

Caveat: “polynomial and generically rank \(u\)” alone is insufficient—high-order polynomial parametrizations can worsen integrability. The concrete \(z\mapsto(U,W)\) charts must be formalized.

## 2. DECOMPOSITION

1. **[new] `qb_maxMinor_aeCover`** — up to a polynomial-null set, the \(Q_b\)-box is covered by finitely many tie-broken maximal \(b\)-minor cells; on each, \(Q_b=D[I\mid X]\), \(D\in GL_b\), and \(X\) is uniformly bounded.

2. **[new] `qbMinor_changeVariables`** — on each cell, \((D,X)\mapsto D[I\mid X]\) is injective and differentiable with Jacobian \(|\det D|^d\), and  
   \(\det(Q_bQ_b^\top)=\det(D)^2\det(I+XX^\top)\).

3. **[new] `deep_UW_chart`** — expose \(Q_p=[U\mid UX+W]\) from the concrete deep parameters, with its actual Jacobian and bounded spectators; this cannot follow from generic rank alone.

4. **[new] `schur_outputShear_normalForm`** — prove the transverse-Schur comparison and perform \(B\mapsto H=PU+BD\), with Jacobian \(|\det D|^{-u}\), retaining the \(D\)-dependent image of the \(H\)-box.

5. **[new, hardest] `incidenceCell_lintegral_le`** — finite \((\ell,s)\)-pivot atlas giving each cell  
   \[
   I_{\ell,s}\le K_{\ell,s}\int_{\text{cube }\mathbb R^{C_{\ell,s}}}\|v\|^{-2q}\,dv,
   \]
   including the determinant weight and the shrinking \(H\)-domain.

6. **[banked] `matBox_frobSq_neg_lintegral_lt_top`** — the normal integral is finite when \(q<C_{\ell,s}/2\); `detGram_lintegral_box_lt_top` discharges any genuinely separated Gram spectator.

7. **[new] `incidenceCodim_gate`** — from  
   \(\min_{\ell,s}C_{\ell,s}/2=T_1-ab/2\) and \(c'<T_1\), derive \(q<C_{\ell,s}/2\) for every admissible pair.

8. **[new] `G_lt_top`** — delete null loci, apply `lintegral_le_sum_finCover`, and conclude from the finite sum of finite cell integrals.

`uniformWenn_proj_le` and `shell_corankPivot_coupled_le` are upstream of \(G\); the cheapest proof starting at \(G\) does not reapply them.

## 3. HARDEST SUB-STEP

The hardest lemma is **`incidenceCell_lintegral_le`**, specifically the finite measurable pivot-neighbourhood/blow-up atlas—not the radial integral or the first minor-chart Jacobian.

Mathlib has no determinantal-stratification or tubular-neighbourhood API. One must explicitly prove coverage, measurability, injectivity, Jacobians, and uniform energy comparison for the \(W/Y\) pivot charts while preserving the coupled \(D\)-dependent \(H\)-domain. Lower-rank strata themselves are null sets; the integration pieces must be neighbourhood/blow-up cells, not merely `{rank W = ℓ}`.

This is substantial labour, but not a Lean wall if the explicit chart formulas are known. If the paper proof stops at “codimension \(C_{\ell,s}\) and \(\asymp\),” then the missing stratified-CoV theorem becomes a genuine wall.

## 4. CHEAPER ALTERNATIVE

Not under the full stated scope. Writing \(\kappa=n-b-a-u\), scope permits \(\kappa\le-1\). Enlarging the transformed \(H\)-domain to a fixed box produces a factor \(|\det D|^\kappa\); its integral already diverges near a smooth rank-\((b-1)\) matrix, even where the remaining energy is bounded away from zero. The lost shrinking \(H\)-volume is essential.

In the special regime \(\kappa\ge0\), a cheaper route exists: separate \(D\), peel the \(ub\)-dimensional \(H\)-block, and reduce \(YW\) to the banked depth-two theorem `routeMBoxThresholdFinite_mnp M0 u d` (with an \(\varepsilon\)-interpolation at the borderline \(q=ub/2\)). This avoids exposing \((\ell,s)\) at the call site, but does not cover the general scope.