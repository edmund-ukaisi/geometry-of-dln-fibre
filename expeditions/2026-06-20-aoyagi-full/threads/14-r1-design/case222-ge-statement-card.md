# (2,2,2) RLCT value — statement card (≥-mountain + the `=` value)

The deep-linear `(2,2,2)` square-Frobenius loss at the deepest point has real log-canonical threshold
`3/2`: `rlctAtOn myF222 0 = 3/2`. `myF222 (x : Fin 8 → ℝ) = ‖A·B‖²_Frob` for `2×2` matrices
`A = [[x0,x1],[x2,x3]]`, `B = [[x4,x5],[x6,x7]]` (the multiplication-map loss at `B = 0`, the deepest
rank-1 stratum). The **new content is the ≥-direction** (the geometric cover); the `≤`-direction rests
on the cited weighted-monomial threshold (Aoyagi/Watanabe). Modules:
`lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGE.lean` (≥-foundation),
`Case222CoverGETail.lean` (the cover assembly + headline), `Case222Resolution.lean` (the ≤-half).

Seat: `fm-2` (formalisation). Task #86 (≥) + #80 (the `=` value). Verifications: rv-2 build+axiom
gate @`8bf0c19` (PASS), pp G3-geometry fidelity #103 + 4-layer soundness audit (PASS).

---

> **Claim (≥-direction — the new geometric content).** For every `c' < 3/2`, the threshold integral
> `∫⁻_{(−1,1)^8} |myF222|^{−c'} dx` is finite (a *bounded* local witness — the `univ` integral
> diverges), hence `rlctAtOn myF222 0 ≥ 3/2`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.rlctAtOn_myF222_ge'`
>   (`lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGETail.lean` @ `8bf0c19`)
> - **Gloss.** `(3 : ℝ≥0∞) / 2 ≤ rlctAtOn myF222 0`. Via `rlctAtOn_ge_of_integral_lt` on the **bounded**
>   open box `openBox = (−1,1)^8 ∋ 0`: `myF222_threshold_lt_top'` supplies
>   `∀ c' : NNReal, (c':ℝ) < 3/2 → ∫⁻_{openBox} ofReal(|myF222 x|^{−c'}) < ⊤`.
> - **Proved.** Unconditionally, axiom-clean (`#print axioms` = `[propext, Classical.choice, Quot.sound]`
>   — **no `sorryAx`, no `monomial_rlct`**: the ≥-content carries **no** cited analytic bound). The
>   threshold integral is split by the route-R recursion and every leaf shown finite below `3/2`:
>   - **Cover (route R, the recursion).** `recStep` re-covers a chart-domain integral as the finite sum
>     over the next blow-up's active cells, via `∫⁻_L h = ∫⁻_univ L.indicator h`
>     (`setLIntegral_indicator`) + `g5_pivotNode active univ` with the always-true `univ_ae_cover`
>     (`univ =ᵐ ⋃_{q∈active} argmaxCellOn active q`; the uncovered `{∀q∈active, x q=0}` slice is
>     codim-≥1 null via `coordZero_null`). The cover charts are the gated `pivotBlowupOn`
>     (C¹ `pivotBlowupOn_hasFDerivWithinAt`, injective off the pivot-zero locus `pivotBlowupOn_injOn`,
>     `|det| = (x p)^{card−1}` `pivotBlowupOnDeriv_det`); the cells tile up-to-null (`argmaxCellOn_cover`
>     + `argmaxCellOn_aedisjoint` — the **max-region** `argmaxCellOn = {y | y p≠0 ∧ ∀j∈active |y j|≤|y p|}`,
>     not the naive `{pivot≠0}` image, so siblings do not double-count).
>   - **p = 0 chain (`p0_summand_via_tail`).** cube-domination (`p0_summand_le_cube`: the `openBox`
>     support sits in `cube8 = [−1,1]^8`) → drop the cutoff → factor a.e. off `{x0=0}`
>     (`myF222_step1A'`: `myF222(step1A x) = x0²·step1Residual(tail x)`) → **Tonelli pivot-peel**
>     (`cube8_tonelli_peel`, the measure-preserving `finPeel 7`) into `(∫_{[−1,1]} |x0|^{3−2c'}) ×
>     (∫_{box7} |step1Residual|^{−c'})`. The `x0`-factor is finite (`3−2c' > −1 ⟺ c' < 2`).
>   - **Lemma-2 splice (the soundness boundary).** `step1Residual = resolvedForm ∘ lemma2Fwd`;
>     `lemma2Fwd` is a det-`±1` **measure-preserving** map (`measurePreserving_lemma2`), so the tail
>     transports by `setLIntegral_comp_emb` (no Jacobian) — `tail_residual_lt_top` — NOT an
>     `rlctAtOn`-homeomorph transport and NOT a chart-image chaining.
>   - **δ-branch — smooth 4-D block, no step-3 RLCT lift.** The δ-cell residual `block =
>     z1²+z2²+(z4z1+z5)²+(z4z2+z6)²` is, under the det-`1` shear `(z5,z6)↦(z4z1+z5,z4z2+z6)`
>     (`shearΦ`, measure-preserving), a clean `Σ⁴` of squares (RLCT `2 > 3/2`); finiteness via the
>     EuclideanSpace radial bound (`sumSq4_box_lt_top`: `(Fin 4→ℝ)≃ᵐ EuclideanSpace` `PiLp.volume_preserving_toLp`
>     + `radial_ball_iff`, `−4 < −2c' ⟺ c' < 2`) + spectator-peel (`boxT_peel_spectator` ×3).
>   - **A-pivots `p ∈ {1,2,3}` — coordinate-conjugation symmetry.** Each closes by reduction to the
>     proven `p=0` summand under a coordinate permutation `σp` (`σ1/σ2/σ3` = the A-block row/column
>     swaps + the matching B-row swaps) that fixes `myF222` (`myF222 ∘ σp = myF222`, by `ring`):
>     `aPivotSummand_conj` (the blow-up conjugation `pivotBlowupOn Aact p (x∘σ) = (pivotBlowupOn Aact 0 x)∘σ`
>     `pivotBlowup_conj`, the chart-domain/pivot-zero/`openBox` preimages, `det_conj`, and
>     `measurePreserving_perm8`).
> - **Assumed.** none beyond the ambient `Fin 8 → ℝ` Lebesgue measure space.
> - **Cited.** **none** for the ≥-direction (the per-leaf threshold values `case222_unit_leaf_threshold`,
>   `case222_block_leaf_threshold` are themselves proved in-repo from S2 arithmetic; the ≥-cover does not
>   invoke `monomial_rlct`).
> - **Deferred.** none for the ≥-statement.
> - **Status.** sorry-free; rv-2 build+axiom-audited @`8bf0c19` (PASS, clean-three); pp G3-fidelity (#103,
>   PASS). → **`reviewed`**.

---

> **Claim (the `=` value, #80).** `rlctAtOn myF222 0 = 3/2`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.rlctAtOn_myF222_eq`
>   (`lean/DLNFibre/DLN/RLCT/Validate/Case222CoverGETail.lean` @ `8bf0c19`)
> - **Gloss.** `rlctAtOn myF222 0 = 3 / 2`. `le_antisymm rlctAtOn_myF222_le rlctAtOn_myF222_ge'`. Every
>   resolution leaf has `monomialThreshold = 3/2` (`Case222Value`: 8 unit `d=2 (1,1)(3,2)`, 16 block
>   `d=3 (1,1,1)(3,2,3)`), so `3/2 = ⨅_i monomialThreshold_i`.
> - **Proved.** The value `3/2`, unconditionally modulo the cited ≤-bound.
> - **Cited.** `rlctAtOn_myF222_le` (the `≤`-half, `Case222Resolution` @`dd40c45`, rv-2 #90) carries
>   `monomial_rlct` — the single permitted S2 citation (the bare weighted-monomial-integral threshold,
>   Aoyagi/Watanabe). So `rlctAtOn_myF222_eq` `#print axioms` = `[propext, Classical.choice, Quot.sound,
>   monomial_rlct]` (no `sorryAx`). **The geometric ≥-content is citation-free; the analytic ≤-bound is
>   Cited** — this is the precision separation: the new content is the codimension/cover, the
>   `rlct = ½·codim`-style reading rests on the cited bound.
> - **Deferred.** The transport to the network loss `rlctAt (dlnLoss H222) deepest222 = 3/2` is the
>   gated seam (`rlctAtOn_dlnLoss222_transport` #66/#72 + `dlnLoss222_eq_myF222` #83), wired by the
>   `case222_rlct` wrapper (`resolution_charts_case222`, `Case222Algebra`, fm) — not in this card.
> - **Status.** sorry-free; the `≥`-half reviewed (above); `=` finalize at the wrapper-PR merge.

---

## Kill-conditions (what would falsify this)

- **A `σp` that does not fix `myF222`.** If any of `σ1/σ2/σ3` were not a genuine Frobenius symmetry of
  `‖A·B‖²`, the conjugation reduction `aPivotSummand_conj` would be unsound. *Guard:* `myF222 ∘ σp =
  myF222` is `ring`/`decide`-checked in Lean (self-verifying), and rv-2 sympy-confirmed the three
  permutations are the row/column-swap symmetries. **Held.**
- **The cover missing a leaf (incomplete `=ᵐ` cover).** If `univ_ae_cover` covered less than `univ`
  up-to-null at any level, the recStep sum would under-count and the finiteness would not transfer.
  *Guard:* the uncovered slice `{∀q∈active, x q=0}` is a codim-≥1 null subspace (`coordZero_null`); the
  max-region cells tile (`argmaxCellOn_cover` + `argmaxCellOn_aedisjoint`).
- **`openBox` locality wrong / `univ`-divergence.** RLCT is local at `0`; the witness MUST be a
  *bounded* neighbourhood — `∫⁻_{univ} |myF222|^{−c'} = ⊤` (the integrand is bounded below away from the
  zero locus, over infinite measure). Using `univ` would be unsound (a flat-`univ` witness was the bug
  caught during route selection). *Guard:* the headline uses `openBox = (−1,1)^8`; `p0_support_subset_cube`
  bounds the effective support; `rlctAtOn_ge_of_integral_lt` only needs *some* bounded open `U ∋ 0`.
- **A leaf threshold `≠ 3/2`.** If any of the 24 leaves had `monomialThreshold ≠ 3/2`, the `⨅` (and the
  value) would move. *Guard:* `case222_unit_leaf_threshold = 3/2`, `case222_block_leaf_threshold = 3/2`
  (the binding `(k,h)=(1,2)` axis realises `3/2`; deeper axes have ratio `2 > 3/2`, so they never lower
  the `⨅` — codim-ordering). The δ-block being smooth 4-D (RLCT 2) rather than a deeper stratum is the
  same codim-ordering fact.
- **The δ-block not actually smooth (shear unsound).** If the shear `(z5,z6)↦(z4z1+z5,z4z2+z6)` did not
  turn `block` into `Σ⁴` of squares, the EuclideanSpace radial bound would not apply. *Guard:*
  `block_eq_shear` (`ring`) + `shearΦ`'s measure-preservation (`shearΦ_mp`, two `measurePreserving_shearAt`).

## Verification ledger

- **rv-2 (formal gate, @`8bf0c19`):** build green; `rlctAtOn_myF222_ge'` clean-three (S2-free, no
  `sorryAx`); `rlctAtOn_myF222_eq` `+monomial_rlct` only; conjugation σ sympy-confirmed; spectator-
  separation sound; non-vacuous with correct `openBox` locality; `scripts/sorries = 0` both ≥-files. **PASS.**
- **pp (G3-geometry fidelity #103 + 4-layer soundness):** data-level (φ/Jac/(d,k,h)/Lemma-2 slot-for-slot),
  soundness (max-region / cover / a.e.-disjoint / codim-ordering cover-completeness), host-space
  (`Fin 8→ℝ`, instance-wall avoided), lane-split (no `equivFin` in the ≥-build) — all closed. **PASS.**
- **Codex (`xhigh`, chart-conjugation decorrelation):** the blow-up conjugation verified per coordinate
  slot (pivot/active/spectator); spectator B-swaps commute. Artifact: `codex/chart-conjugation-{prompt,answer}.md`.
