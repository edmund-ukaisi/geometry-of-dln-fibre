<task>
Lean 4 + Mathlib v4.29. I must realize the "diagonal-normalization source swap S" for a blow-up chart,
and compose it into an existing `geoChartMap`, WITHOUT breaking an existing cover proof. This is the last
wall of an expedition; correctness of the geometry is paramount. Advise the CLEANEST correct realization.

CONTEXT (definitions confirmed by reading the code):

- `Params M` ≃L[ℝ] `(Fin (flatDim M) → ℝ)` via `paramsEquivFlatCLE M` (a ContinuousLinearEquiv; its coe =
  `paramsEquivFlat M`). Write `z_c(w) = paramsEquivFlat M w c` for flat coord `c : Fin (flatDim M)`.

- `qNodeOf M node hd : Params M ≃ₜ (Fin (dCN node) → ℝ) × (Fin (flatDim M - dCN node) → ℝ)` splits off the
  node's center coords `C(node) = cNodeOf M node hd` (an injective `Fin (dCN node) → Fin (flatDim M)`).
  Fact I proved: `(qOfCenterCLE M c hinj w).1 i = paramsEquivFlat M w (c i)` (first component reads center
  cell `c i`). `qNodeOf` is LINEAR (fderiv = fixed CLE `qOfCenterCLE`).

- `geoChartMap … g w = (qNodeOf node hd).symm (Prod.map (pivotChart ⟨g.pivot,hp⟩) id (qNodeOf node hd w))`
  on-cone (`pivotChart i u = fun k => if k=i then u i else u i * u k`), `id` off-cone. So it blows up the
  center coord `cNodeOf node ⟨g.pivot⟩` (the exceptional divisor of chart `g`).

- BANKED per-edge det atom: `|det D(geoChartMap g) w| = |z_{cNodeOf node ⟨pivot⟩}(w)|^{dCN node − 1}`.
- BANKED det-neutrality atoms: `clm_involutive_abs_det_one` (an involutive CLM has |det|=1);
  `abs_det_fderiv_comp_det_one_gauge` (for any det-1 `g`, `|det D(C∘g) w| = |det DC (g w)|`);
  `clm_det_comp` (CLM det multiplicative under comp); `abs_det_fderiv_elemShear` (a Schur shear |det|=1).

THE PROBLEM (cert-established kill-condition, `threads/18-fold-regroup/cert-fold-regroup.md` §4):
The ledger references a divisor by its `divBirthCoord` DIAGONAL cell `d = flatCoordOf(layer,cleared,cleared)`,
but the geometric fan-out births it at the (possibly OFF-diagonal) pivot cell `p = cNodeOf node ⟨pivot⟩`.
So `|det Dβ| = |z_p|^{…}` names the wrong cell; the ledger monomial names `z_d`. Fix (elder fork 15,
"diagonal-normalization"): compose a CUBE-INVARIANT, det-1 SOURCE swap `S = (p ↔ d)` into the chart so it
blows up `z_d` instead of `z_p`. The chart becomes `(β ∘ S) ∘ g` with `g` a det-1 gauge slot (`g = id` now).

CONSTRAINTS that the realization must satisfy:
(C1) `|det D(β∘S) w| = |z_d(w)|^{dCN−1}` (the atom now reads the DIAGONAL cell d) — must follow from the
     banked atoms.
(C2) COVER PRESERVED: the existing cover proof shows `⋃ pivots (geoChartMap g) '' srcBox ⊇ zero-locus`
     via `(pivotChart i) '' cube` tiling the cube. Composing S must NOT break it — ideally `S` is
     cube-invariant (`S '' cube = cube`) so `(β∘S) '' cube = β '' cube` (image unchanged).
(C3) `srcBox` stays the cube at `g = id` (`g⁻¹(cube) = cube`).

MY QUESTION: which of these is the cleanest CORRECT realization, and what breaks?

Option A: S = a flat-coordinate transposition on Params M, `S = paramsEquivFlatCLE.symm ∘ (precompose by
  Equiv.swap p d) ∘ paramsEquivFlatCLE`. Then β∘S reads z_d. But does β (which blows up cNodeOf ⟨pivot⟩ = p)
  composed with S (swap p,d) actually give |z_d|^{…}? Concern: S swaps p↔d in the SOURCE, β reads position
  p — so β∘S reads S's output at p = original d. Confirm the direction gives z_d, not z_p.

Option B: S = a CENTER permutation (swap the two `Fin (dCN)` indices whose cNodeOf images are p and d),
  composed inside the q-split: `q.symm ∘ (pivotChart pivot) ∘ (centerSwap) ∘ q`. Requires d ∈ range(cNodeOf)
  (is the diagonal always a center cell? for case-1 the u-corner IS divBirthCoord=d, in the center; for
  case-2 the block's (0,0) corner is d, in the center — CONFIRM).

Option C: change cNodeOf to select d directly for the pivot (no swap) — REJECTED by the elder because the
  pivots must tile the center for the cover; relocating cNodeOf breaks the tiling. Confirm this reasoning.

For the chosen option, give: (i) the exact composition order so β∘S reads z_d; (ii) how (C1) follows from
which banked atoms; (iii) how (C2) cube-invariance is proved (a coord transposition preserves the symmetric
cube [-R,R]^d — but does the CENTER-swap option preserve the cover's per-pivot tiling, or only the union?);
(iv) the single biggest correctness risk.
</task>

<output_contract>
Four sections, terse:
1. RECOMMENDED OPTION (A/B/C) + the one-line why.
2. COMPOSITION ORDER — the exact `β ∘ S` (or q-split) expression, and confirm it reads `z_d`.
3. (C1)/(C2)/(C3) DISCHARGE — for each, which banked atom / argument, and any GAP.
4. BIGGEST CORRECTNESS RISK — the one thing most likely to make the last wall subtly wrong.
</output_contract>

<grounding_rules>
Reason from the definitions given, not a recalled paper. Distinguish what FOLLOWS from the banked atoms vs
what needs a NEW lemma. If Option B needs "d ∈ range(cNodeOf)", say so as a precondition to verify, don't
assume it. Flag any place where the swap direction (source vs target) could silently give z_p instead of z_d.
</grounding_rules>
