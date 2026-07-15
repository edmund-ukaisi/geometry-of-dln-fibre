# Brick D piece (ii) — chart (4)/(5) CoV spec (two-hand branch-point)

**Purpose.** The target statements + banked-reuse map for the two file-disjoint chart modules, so a second
hand can build chart (5) on `genm-sj5-chart5` off this commit while I take chart (4) to green. Delivered as a
spec (not a committed `sorry`-stub) to honor the zero-`sorry`-in-committed-files gate; the second hand creates
`RouteMSJIncidenceChart5BigCell.lean` from §"Chart (5)" below and builds it green on their branch.

**Status of each chart w.r.t. the `genm-bltj` gate:** each chart, as an INDIVIDUAL CoV lemma, is TRUE
regardless of bltj (same status as piece (iv)'s per-stratum gate). bltj only bites the ASSEMBLY (does the
finite atlas COVER the `b<j`/`Q_p`-degeneration locus). So build both charts now; the assembly
(`incidenceCell_lintegral_le`) stays parked on bltj.

**Guards (hold in the per-chart lemmas too):** JOINT resolution (no per-`z` pointwise); scope `a+b ≤ M₂`
(threaded as the exponent/dimension constraints); det-Gram COUPLED (the chart tube indicator rides inside).

**File structure (file-disjoint → clean merge at the Brick D unit):**
- `RouteMSJIncidenceChart4Polar.lean` — chart (4), MINE (this branch).
- `RouteMSJIncidenceChart5BigCell.lean` — chart (5), SECOND HAND (`genm-sj5-chart5`).
- assembly `incidenceCell_lintegral_le` → its own file later (consumes 4 + 5 + piece (iv)); bltj-gated.
- Shared defs: NONE strictly required at the per-chart level — the `H̃` (front, `ℝ^{ub}`) and `W` (transverse)
  blocks are independent objects; each chart is self-contained. (The split `F ≍ ‖H̃‖²+‖YW‖²` is the assembly's
  concern, cert §3b(3).) So no shared header needed; avoids single-home coupling.

---

## Chart (4) — the `H̃`-fibre polar (cert §3b(4))

**Math.** `∫_{H̃ ∈ ℝ^{ub}} (‖H̃‖²_F + τ²)^{−q} dH̃ ≍ τ^{ub−2q}` for `τ > 0`. Exact via the scaling
`H̃ = τ·V` (`dH̃ = τ^{ub} dV`): `∫ = τ^{ub−2q} · K`, `K = ∫_{V∈ℝ^{ub}} (‖V‖²+1)^{−q} dV`, finite iff `2q > ub`.

**Target statement (primary — the scaling identity; `ub =: N`):**
```
theorem chart4_polar_scaling {N : ℕ} [NeZero N] {τ : ℝ} (hτ : 0 < τ) (q : ℝ) :
    ∫⁻ H : Fin N → ℝ, ENNReal.ofReal ((‖(WithLp.toLp 2 H : EuclideanSpace ℝ (Fin N))‖ ^ 2 + τ ^ 2) ^ (-q))
      = ENNReal.ofReal (τ ^ ((N : ℝ) - 2*q))
          * ∫⁻ V : Fin N → ℝ, ENNReal.ofReal ((‖(WithLp.toLp 2 V : EuclideanSpace ℝ (Fin N))‖ ^ 2 + 1) ^ (-q))
```
(Refine the norm encoding to match how `‖H̃‖²_F` appears downstream — `frobSq` or `EuclideanSpace` norm; use
whatever the assembly's integrand uses. The load-bearing content is the `τ^{N−2q}` extraction.)

**Finiteness corollary (what the assembly consumes):**
```
theorem chart4_polar_lt_top {N : ℕ} [NeZero N] {τ : ℝ} (hτ : 0 < τ) {q : ℝ} (hq : (N : ℝ) < 2*q) :
    ∫⁻ H : Fin N → ℝ, ENNReal.ofReal ((‖…‖^2 + τ^2)^(-q)) < ⊤
```
i.e. the `H̃`-fibre integral is `< ⊤` exactly when `2q > ub` (the `ub`-dim block's threshold), with the
`τ^{ub−2q}` scale exposed for the outer `τ = ‖YW‖` integration.

**Banked reuse (`RouteMSJRadialPolar.lean`):**
- `lintegral_pi_radial_polar_factor` (l.76): for degree-2-homogeneous `g` on `Fin N → ℝ`, whole-space
  `∫⁻ φ(g x) = ∫_sphere ∫_{r>0} r^{N-1}·φ(r²·g ω)`. Use `g = ‖·‖²` (homogeneous), `φ t = (t+τ²)^{−q}`.
- Radial `∫_{r>0} r^{N-1}(r²+τ²)^{−q} dr`: substitute `r = τ s` → `τ^{N−2q} ∫ s^{N-1}(s²+1)^{−q} ds`.
  Cross-check `lintegral_Ioc_rpow_lt_top` (l.157: `∫ r^e, −1<e`) / `RadialResidualPower.integral_core_full_eq`.
- Simpler alternative: a direct scaling CoV `x ↦ τ•x` on `Fin N → ℝ` (Haar scaling, Jacobian `τ^N`) avoids the
  sphere and gives the identity in one step — likely the cleanest. Check `MeasureTheory` `addHaar` scaling
  (`Measure.addHaar_smul` / `lintegral_comp_smul`), pattern per lean/CLAUDE.md pi-diamond note.

---

## Chart (5) — the determinantal big-cell of `W` (cert §3b(5)) — SECOND HAND

**Math.** On `{det W₁₁ ≠ 0}` for a size-`ℓ` minor `W₁₁` (`W : u×d`, block `[[W₁₁,W₁₂],[W₂₁,W₂₂]]`,
`W₁₁ : ℓ×ℓ`, `W₂₂ : (u−ℓ)×(d−ℓ)`):

    W ↦ (W₁₁, W₁₂, W₂₁, E),   E := W₂₂ − W₂₁ · W₁₁⁻¹ · W₁₂   ((u−ℓ)×(d−ℓ)).

- **Jacobian ≡ 1** — the map is a TRANSLATION in the `W₂₂` block (`W₂₂ = E + W₂₁ W₁₁⁻¹ W₁₂`, the other blocks
  fixed), block-triangular unit-diagonal; `C^∞`/rational on `{det W₁₁≠0}`, injective, image `{det W₁₁≠0}` open.
- **`rank W = ℓ + rank E`** (block-LU / Schur complement): `W = L · blockdiag(W₁₁, E) · U` with `L,U`
  unipotent, so `{rank W ≤ ℓ} ∩ chart = {E = 0}`. `E` is the transverse-Schur normal coordinate.
- Polar in the `E`-block (dim `(u−ℓ)(d−ℓ)`) + residual `Y`-directions → radial `r^{C_{ℓ,s}−1} dr`; with the
  loss `r^{−2q}` this is `∫₀^δ r^{C_{ℓ,s}−1−2q} dr` (piece (iv)'s `clsCodim` exponent).

**Target statements (two, file-disjoint from chart 4):**
```
-- the block-LU rank identity (network-free linear algebra; the genuinely-new content)
theorem chart5_rank_eq {u d ℓ : ℕ}
    (W11 : Matrix (Fin ℓ) (Fin ℓ) ℝ) (W12 : Matrix (Fin ℓ) (Fin (d-ℓ)) ℝ)
    (W21 : Matrix (Fin (u-ℓ)) (Fin ℓ) ℝ) (W22 : Matrix (Fin (u-ℓ)) (Fin (d-ℓ)) ℝ)
    (h11 : IsUnit W11.det) :
    (Matrix.fromBlocks W11 W12 W21 W22).rank = ℓ + (W22 - W21 * W11⁻¹ * W12).rank
-- (and {E = 0} ↔ rank W ≤ ℓ as its corollary)

-- the measure CoV (Jacobian ≡ 1), via lintegral_image_eq_lintegral_abs_det_fderiv_mul
theorem chart5_bigcell_cov … :   -- ∫ over {det W₁₁≠0} of f(W) = ∫ over (W₁₁,W₁₂,W₂₁,E) of f(reassemble)
```

**Banked reuse (self-recon `genm-chart5-recon` maps the exact lemmas):**
- CoV engine `lintegral_image_eq_lintegral_abs_det_fderiv_mul` — pattern in `RouteMInteriorLDUCov`,
  `RouteMNullSliceCov`, `RouteMBoundaryCleanChartFull`, `RouteMInteriorLDUCov` (~10 files). Pi-diamond
  workaround per lean/CLAUDE.md (transcribe over the raw pi type, `det_pi`).
- block-LU / Schur: `Matrix.fromBlocks`, `Matrix.fromBlocks_eq_of_…` / Schur-complement det lemmas;
  `rank` under unit multiplication (`Matrix.rank_mul_eq_…`, `rank_of_isUnit`, `rank_submatrix`). brickdbuild's
  banked algebra (`chartGram_congr`, `pushThrough`) is the same block-inverse toolkit.
- radial finiteness: `RouteMSJRadialPolar.lintegral_Ioc_rpow_lt_top`, `RadialResidualPower.*`.

**Exponent hook:** the radial exponent is `C_{ℓ,s}` from piece (iv) `DLNFibre.DLN.RLCT.clsCodim`
(`RouteMSJIncidenceExponent.lean`); the per-stratum gate `clsCodim_gate` gives `q < T1_q ⟹ 2q < C_{ℓ,s}`,
so each big-cell radial integral converges below `T1`.
