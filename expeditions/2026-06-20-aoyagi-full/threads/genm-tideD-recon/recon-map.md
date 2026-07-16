# recon-map — TIDE-D banked-state map + build spec (the native `(□)` per-stratum finiteness)

**Seat:** self-recon (read-only INTERNAL reconnaissance), aoyagi-full Stage 2, `genm-tideD-recon`.
**Date:** 2026-07-15. **NO Lean edits, NO build.** Read via `git show` on `origin/genm-deepatlas`
(@346884e86), `genm-seamrlct` (@71330a256), the `genm-routeverify` cert (working tree), the
`genm-deepatlas` statement cards.

Purpose: so the tide-D build spec names banked pieces, not blind. The controller framed tide-D as
"discharge `hfin` in `deepRankLE_lintegral_lt_top` at `f =` loss". **That framing conflates two parallel
finiteness architectures** (§0) — the recon resolves which one the mint is actually wired to, and finds the
same radial engine discharges both. **Headline for Q3: BANKED-RADIAL-REUSE. The rlct calculus is NOT to be
formalized; per-stratum finiteness is already native via the banked radial blow-up
`corner_block_cube_lintegral_lt_top` + its wrapper `stratum_corner_lt_top` (both sorry-free, axiom-clean).
Tide-D's real labor is the chart-CoV assembly (construct the degree-2-homogeneous `g` + prove its unit-sphere
lower bound `hlb`) + the finite-cover gluing + the a.e. genericity discharge.**

---

## 0. ★ KEY DESIGN FINDING — two finiteness architectures; the mint is wired to Arch-1, not to `deepRankLE`

There are TWO parallel routes to the capstone finiteness, sharing one analytic engine:

**Arch-1 (mint-wired, the critical path).** `(□) = RouteMBoxThresholdFinite M` — the **parameter-box**
integral `∫_{paramsBoxM M 1} frobSq(prod M A)^{−c'} < ⊤` for `c' < ½·minAdm M`
(`RouteMBoxReduction.lean:165`). Closed by the **decorated recursion** `DecoratedDescent`
(`RouteMSJDecoratedRec.lean:206`) → `routeMBoxThresholdFinite_of_decoratedDescent` → the mint
`aoyagi_learning_coefficient_gen_of_descent` (`RouteMSJMint`). `DecoratedDescent`'s only open analytic
component is `DecoratedStepHyp` (the decorated peel step), whose **per-shell heart is `deeperFlag_shell_le`**.

**Arch-2 (deepatlas coverage, STANDALONE, NOT wired to the mint).** `deepRankLE_lintegral_lt_top`
(`RouteMSJDeepCoverage.lean:175`) glues per-cell finiteness `hfin` over the CR-path `deepCell` atlas of the
**rank locus** `{A | (prod H A).rank ≤ s}`. Its docstring says verbatim "Standalone (NOT aggregator-wired)".
**Grep-confirmed: `deepRankLE` / `deepCell` / `deepCover` appear NOWHERE on the mint / descent / capstone
path** — only inside the `RouteMSJDeepCov*` modules themselves. The deepatlas statement cards
(`threads/genm-deepatlas/statement-cards.md`) label the coverage "Tide B" and `hfin` an explicit
"TIDE-D hypothesis (the loss tide discharges it)".

**Resolution.** The controller's "`hfin` at `f =` loss (the shell/box integrand `deeperFlag_shell_le`
needs)" mixes Arch-2's *hfin discharge* with Arch-1's *shell integrand*. The two are the same obligation
viewed through different top-level glue: on **both**, the per-cell / per-shell integral of the DLN loss —
after the pivot-Schur unit-Jacobian CoV — is a degree-2-homogeneous residual on a codim-`C` normal block,
whose finiteness is the banked radial `∫ r^{C−1−2q}dr < ⊤`.

**Recommendation (surfaced, not decided — needs controller).**
- **Target Arch-1**: complete `deeperFlag_shell_le` DIRECTLY via the incidence charts (routeverify §6). This
  discharges `DecoratedStepHyp → DecoratedDescent → (□) → capstone` with **zero new top-level wiring** — the
  mint pre-stage already exists. Steps 1/2/3-entry/gate/corner are **already banked** (§4); the remainder is
  the chart-CoV assembly of `frontLossIntegrand` + gluing + genericity.
- **Arch-2 would additionally require** wiring `deepRankLE_lintegral_lt_top` into the capstone (replacing
  `DecoratedDescent`) — a re-architecture the mint pre-stage does not reflect. Not recommended as tide-D
  unless the controller wants to retire the decorated recursion.

Either way the **Q3 answer is identical and decisive** (banked radial, §3). The recon-map is written for
Arch-1 (the smaller, mint-wired delta) and notes where Arch-2 diverges.

---

## 1. Coverage interface — `deepCell`, `hfin`, and the integrand `f` (Q1)

`RouteMSJDeepCoverage.lean` (origin/genm-deepatlas), sorry-free, axiom-clean.

- **`deepCell H s j hj q path Q`** (`:69`): recurses on a CR-path threading the effective right-factor `Q`.
  A descent node is the **pivot chart** intersected with the reduced-factor tail:
  `{A | IsUnit ((effLayer·Q A).submatrix ρ κ) ∧ (effLayer·Q A).rank ≤ r} ∩ deepCell … (reduced Q)`; the
  terminal cell is `{A | (Q A).rank ≤ s}`. **Invariant-free** — the rank constraint lives in the terminal
  cell. The transverse `E`-block coords the seam-cert names arise from the Schur complement of the pivot
  submatrix `(effLayer·Q).submatrix ρ κ`.
- **`deepRankLE_eq_iUnion_cells`** (`:158`): `{A | (prod H A).rank ≤ s} = ⋃ i : CRIndex H, deepCell … i 1`.
- **`deepRankLE_lintegral_lt_top`** (`:175`): the gluing wrapper. Signature:
  `(H) (s) {μ : Measure (Params H)} (f : Params H → ENNReal) (hfin : ∀ i : CRIndex H, ∫⁻ A in deepCell … i 1, f A ∂μ < ⊤) : ∫⁻ A in {A | (prod H A).rank ≤ s}, f A ∂μ < ⊤`. `f`, `μ` **generic**; ONE application
  of the banked `lintegral_lt_top_of_finite_cover`; needs no measurability.
- **`hfin` exact shape**: `∀ i : CRIndex H, ∫⁻ A in deepCell H s L le_rfl (H (Fin.last L)) i (fun _ ↦ 1), f A ∂μ < ⊤`.

**What `deeperFlag_shell_le` actually passes (Arch-1) — NOT a `deepCell` integral.** `deeperFlag_shell_le`
(`RouteMSJDeeperFlagCore.lean:757`) operates on the **`shellSpineIntegrand`** — a box×shell integral
`∫_{A' ∈ paramsBoxM(tailChain M) ∩ singularShell} ∫_x ∫_Γ freedSchurLoss^{−c'}` (`:447`) — and produces a
**DOMINATION** onto the shorter chain's comparator, not a bare finiteness:

    shellSpineIntegrand M (t+j) κ ε r ⟨j⟩ c'  ≤  C · (cornerComparator (redChain (t+j) M) k jc).integral (c' − peelCharge M (t+j)/2),   C < ⊤,  adm (redChain (t+j) M) (cornerComparator …).

Finiteness of the RHS `cornerComparator.integral` is closed by the **decorated IH on the strictly shorter
chain** `redChain u M` (one fewer layer), the threshold reproduced by `minAdm(M) ≤ ab + minAdm(redChain u M)`
(routeverify CHECK 3c, 0/75 411 fails). `cornerComparator.integral` is a **monomial-weighted** box integral
`∫_z ∫_u (∏ℓ|u ℓ|^{jac ℓ})·(decLoss u z)^{−c'}` (`SJDecoration.integral`, `RouteMSJDecorated.lean:139`), NOT
the plain single-block corner — its finiteness rides the `adm`/`monomialThreshold` β-clause, not the radial.

---

## 2. seamrlct's cert — what formalizes, and how (Q2)

`genm-seamrlct/seamrlct-cert.md` (branch `genm-seamrlct`). The native `rlct = codim/2` argument and its
formalization footprint:

- **§1 proof calculus** `[T-sum]/[T-prod]/[T-sos]/[T-inf]/[T-inv]` + the **homogeneity lemma** `rlct_0(F) =
  rlct(F)` for homogeneous `F`. These are **NOT formalized as theorems** in the codebase and **need not be**
  (§3 below) — they are the pen-and-paper certification that the seam is benign. The Lean realization of
  "`rlct = codim/2` for a Morse-Bott / degree-2-homogeneous loss" is the **radial blow-up** `∫₀^δ r^{C−1−2q}dr
  < ⊤ ⟺ q < C/2` — i.e. `corner_block_cube_lintegral_lt_top`, which IS banked.
- **§6 binding stratum** `k=1`, charge-inert (`γ_{ρ−1}=0`, `κ_1=1`), Morse-Bott ⟹ `rlct = C_1/2 =
  (minAdm−ab)/2` (the target). The Lean gate arithmetic is `clsCodim_gate_genL` (§4).
- **§10 carry-the-Jacobian guard.** The odd-cycle "deficit" is a coordinate artifact of a **non-unit-Jacobian
  (radialising) chart**; in the atlas's **unit-Jacobian Schur charts** the seam incidence is balanced and
  `rlct = codim/2` natively (no cited Aoyagi). **The Lean charts honor this**: `chart5_bigcell_cov`
  (`RouteMSJIncidenceChart5BigCell.lean:110`) is a **unit-Jacobian shear** (Haar translation-invariance, Jac
  ≡ 1), and `corner_block_cube_lintegral_lt_top` carries the honest `r^{N−1}` polar Jacobian explicitly. So
  the seam-cert's one binding requirement ("atomic Schur coordinates, carry the Jacobian, never radialize-and-
  drop") is **already met by the banked charts** — tide-D must not introduce a radialising chart that drops
  its `|det J|`.
- **§9 axiom footprint.** The lower bound `rlct_x ≥ (minAdm−ab)/2` is native on the binding stratum + all
  bipartite/acyclic charts (König `τ=τ*`). The radial route (`RouteMSJRadialPolar`) is **axiom-clean
  `[propext, Classical.choice, Quot.sound]`, NO `cited_aoyagi_dln`** (grep-confirmed, docstring `:31`).

---

## 3. ★ THE KEY DESIGN QUESTION — banked-radial-reuse (a), decisively (Q3)

**ANSWER: (a). The per-stratum finiteness is banked. No rlct-calculus / no `monomial_rlct` to formalize.**

The engine is banked and proven sorry-free / axiom-clean:

    -- RouteMSJRadialPolar.lean:257
    theorem corner_block_cube_lintegral_lt_top {n : ℕ} [NeZero n]
        (g : (Fin n → ℝ) → ℝ) (hg : Measurable g)
        (hom : ∀ (r : ℝ) (x : Fin n → ℝ), g (r • x) = r ^ 2 * g x)      -- degree-2-homogeneous
        (c' : ℝ) (hc0 : 0 ≤ c') (hc' : c' < (n : ℝ) / 2)                -- exponent gate q < N/2
        (a : ℝ) (ha : 0 < a)
        (hlb : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1, a ≤ g (WithLp.ofLp ω)) :  -- unit-sphere floor
        ∫⁻ z in Set.univ.pi (fun _ : Fin n => Set.Icc (-1:ℝ) 1), ENNReal.ofReal ((g z)^(-c')) < ⊤

It is the radial blow-up `r^{N−1}` × `(r²·g ω)^{−c'}` dominated by `a^{−c'}·r^{(N−1)−2c'}`, finite iff
`c' < N/2` — **this IS `rlct = codim/2` realized analytically**, with the honest Jacobian carried. It
already ships a non-vacuity `example` (pure `∑ zᵢ²`, `a=1`).

The DLN-shaped wrapper is also banked and proven (no sorry):

    -- RouteMSJIncidenceAssembly.lean:767
    theorem stratum_corner_lt_top (M : Fin (L+1+1+1) → ℕ) (u ℓ s : ℕ) (c' : ℝ)
        (hu hs hℓs hbℓ) (hN : 0 < clsCodim ![M 0, M 1, M 2] u ℓ s)
        (hc' : ((M 0 - u) * (M 1 - u) : ℕ) / 2 < c') (hcT : c' < carrierThreshold M)
        (g : (Fin (clsCodim ![M 0,M 1,M 2] u ℓ s) → ℝ) → ℝ) (hg : Measurable g)
        (hom : ∀ r x, g (r • x) = r ^ 2 * g x) (a : ℝ) (ha : 0 < a) (hlb : …) :
        ∫⁻ z in [-1,1]^{clsCodim …}, ENNReal.ofReal ((g z)^(-(c' - (…ab…)/2))) < ⊤

It **already discharges the exponent gate internally** (`q = c'−ab/2 < ½(minAdm M − ab) ≤ ½·clsCodim` via
`clsCodim_gate_genL` + `hcT`), feeding `corner_block_cube_lintegral_lt_top`. It takes `g` (the transverse
loss) **abstract** with `hom`/`hlb` as hypotheses.

**Bilinear/two-radius corner also banked.** A stratum retaining the `‖Y·W‖²` coupling (the `ℓ=0` two-radius
corner, incidence-cert §2/§3b) uses `twoBlock_radial_le` / `twoBlock_radial_scale_le`
(`RouteMSJ*`; AxCheck `:1071`, clean-three; consumed in `RouteMSJFrontFirst.lean:326`). So both the
single-block and the two-block regimes have banked radial finiteness.

**`monomial_rlct` is NOT needed for finiteness.** No general `monomial_rlct` theorem exists or is required;
`monomialThreshold` (`Skeleton.lean:88`) is a **separate** object — the decorated comparator's β/axisRatio
admissibility clause, not the radial. The finiteness is native via the blow-up.

**So tide-D does NOT formalize [T-sum]/[T-prod]/[T-sos] or a monomial-rlct theorem (route (b) is avoided).**
What tide-D must SUPPLY, per stratum, to *use* the banked engine:
1. the concrete `g` = the transverse loss in the `(ℓ,s)`-chart coordinates (from the chart CoVs, §4);
2. **`hom`** — that `g` is degree-2-homogeneous (structural, `frobSq` of a linear-in-block map);
3. **`hlb`** — a **positive lower bound on the unit sphere** (the Morse-Bott / "vanishes to order exactly 2,
   bounded below" content). **This is the genuine analytic core of tide-D** and where real work lives.

---

## 4. Chart CoV for `deepCell` / the front-loss residual (Q4)

The incidence-assembly reduction chain — **steps 1, 2, 3-entry, gate, corner all BANKED sorry-free** on
`origin/genm-deepatlas` (given the a.e. genericity hyps as inputs). Exact signatures:

1. **Step 1 — row-split + shell → coupled box** (`RouteMSJIncidenceAssembly.lean:436/610`):
   `shellSpine_le_coupledBox`, `shellSpine_le_frontCharge`. Drop the shell indicator (a-fortiori) + the
   measure-preserving head/row split `hsSplit` (`measurePreserving_hsSplit`, `prod_headSplit` exposing
   `Q_b = A_cor · deeperFlagZdeep z`). Bypasses the FALSE route-B `shellSpine_le_hsQ_box` (routefork).
2. **Step 2 — coupled Γ-peel → corank charge** (`:493` `freedSchurLoss_gammaPeel_le`, `:583`
   `coupledBox_le_frontCharge`): produces `det(Q_b Q_bᵀ)^{−a/2}·Cresid(ab)c'` and shifts `c' → q = c'−ab/2`.
   Underlying banked atom: `corankBlock_morsePeel_setLE` (`RouteMSJCorankPeel.lean:88`). Corank stays
   COUPLED (no `sup_{A_cor}` pull-out — the route-B error).
3. **Step 3-entry** (`:668` `frontCharge_factor`, `:688` `frontLoss_pivotPoly_eq`): factor the `x`-independent
   charge out; put the pivot energy `E_top = frobSq([P|B₁₂]·hsQ)` in **polynomial** form (`pivotEnergy_stack_eq`,
   `:533`, clears `P⁻¹` on `IsUnit P`).
4. **Chart 5 — big-cell CoV, unit Jacobian** (`RouteMSJIncidenceChart5BigCell.lean:110` `chart5_bigcell_cov`):
   the `W₂₂ ↦ E`-shear is Lebesgue-preserving (Haar); `chart5_rank_le_iff_reassembled` (`:145`) puts the
   rank-drop locus at the transverse Schur coordinate origin `{E=0}`. **This is the unit-Jacobian Schur chart
   the seam-cert §10 mandates.**
5. **Chart 4 — front (pivot / H̃) fibre finiteness** (`RouteMSJIncidenceChart4Polar.lean:105`
   `chart4_Htilde_fibre_lt_top`): `∫ (‖H‖²+τ²)^{−q} dH̃ < ⊤` for `2q > N` (Mathlib
   `integrable_rpow_neg_one_add_norm_sq`).
6. **Corner — per-stratum transverse radial** (`stratum_corner_lt_top`, §3) → `corner_block_cube_lintegral_lt_top`.

The **codim/gate** (`RouteMSJIncidenceExponent.lean` + `RouteMSJIncidenceAssembly.lean`):
`clsCodim (M : Fin 3 → ℕ) u ℓ s = u·(M₁−u) + M₀·ℓ + (M₀−s)(u−ℓ−s) + s·((M₂−(M₁−u))−ℓ)` (`:45`);
`clsCodim_add_ab_eq` (`:51`, the `ℓ`-independence ring identity); `clsCodim_gate_genL`
(`RouteMSJIncidenceAssembly.lean:723`, the **general-`L`** gate `minAdm M ≤ clsCodim + ab` — routeverify
brick B is DONE, not `Fin 3`-only).

**`RouteMSJRadialPolar` extras**: `lintegral_ball_radial_polar_factor` (`:112`), `corner_block_lintegral_lt_top`
(EuclideanSpace form, `:185`), `lintegral_Ioc_rpow_lt_top` (`:157`).

---

## 5. ℝ/ℂ codim-source probe — RESOLVED, ℝ-native, no bridge (Q5)

**The per-cell / per-stratum codim is a pure `ℕ` block-dimension count from the widths, computed over ℝ.
`(α)`'s ℂ `codimRepCanonical` is NOT imported and NOT load-bearing.**

- `clsCodim ![M 0, M 1, M 2] u ℓ s` (`RouteMSJIncidenceExponent.lean:45`) is a `Nat` arithmetic expression in
  the **widths and stratum indices** — a block-dimension count, field-agnostic.
- It enters `corner_block_cube_lintegral_lt_top` as the dimension `N` of a **real** block `Fin N → ℝ`; the
  whole finiteness lives over ℝ.
- The deepgate Nat gate is stated over exactly this real-block codim: `clsCodim_gate_genL` gives
  `minAdm M ≤ clsCodim + (M₀−u)(M₁−u)` as a `Nat` inequality, cast to ℝ inside `stratum_corner_lt_top`
  (`hgateR`). `carrierThreshold M = (minAdm M : ℝ)/2` (`RouteMSJDecorated.lean:64`).
- **No ℝ/ℂ bridge is on the tide-D path.** (The deepatlas cards note "the ℝ/ℂ codim bridge for (α) is a
  separate lane" — confirmed separate.)

---

## 6. Gaps / pitfalls / dead-ends (Q6)

**GENUINE REMAINING BRICKS for tide-D (Arch-1, routeverify §6, updated for post-cert progress):**
- **(A) Top-level assembly of `frontLossIntegrand`'s `∫_x` — the single largest, genuinely-analytic piece.**
  Wire the (grep-confirmed **orphaned**) charts (chart4, chart5, `det_chartGram`, `transverseSchurGram`,
  `chartProjComplement`) into a finite `(ℓ-minor × s-minor × b-minor)` determinantal atlas of the front block
  `x = (P, B₁₂, C)`, with per-chart CoVs (Jacobians `|det D|^{n−b−a−u}`, `det(I+XXᵀ)^{−a/2}` a unit, big-cell
  `|det|≡1`), then per-stratum: construct `g` + prove **`hom`/`hlb`** and call `stratum_corner_lt_top`
  (single-block) or `twoBlock_radial_le` (bilinear ℓ=0). **`hlb` (positive unit-sphere floor of the transverse
  loss) is the analytic crux** — it is the Morse-Bott non-degeneracy, per stratum.
- **(B) General-`L` exponent gate — DONE since the routeverify cert.** `clsCodim_gate_genL` is proven for
  general `M : Fin (L+1+1+1) → ℕ` (via `minAdm_le_peelCharge_add_redChain` → `minAdm_redChain_le_deepTailMin`
  → `deepTailMin_le_M2` → `clsCodim_add_ab_eq`). No longer `Fin 3`-only.
- **(C) Finite-cover gluing + per-stratum ratio sum (step 5).** Banked skeleton
  `lintegral_lt_top_of_finset_cover` / `lintegral_lt_top_of_finite_cover` (`RouteMSJIncidenceGluing`); the
  `(ℓ,s)`-index-completeness (every point in some chart, incl. `b<j`) is Lean labor — the math is
  bltj-closed (routeverify §4b, decorrelated).
- **(D) a.e. genericity re-route obligations (the `hGae`/`hEtopae` inputs).** `shellSpine_le_frontCharge`
  threads two a.e. hyps that tide-D must discharge in the assembly:
  - `hGae` — corank Gram `Q_b Q_bᵀ` PosDef a.e. in `(z, A_cor)`: from the threaded deep-factor rank
    `b ≤ (Z_deep z).rank` + banked `corank_survival_ae` (`RouteMSJCorankGeneric`, AxCheck `:1150`) — the
    **rankgen** deliverable.
  - `hEtopae` — pivot energy `E_top > 0` a.e. in `x`: from `pivotEnergy_stack_eq` (polynomial form) +
    polynomial nonvanishing (à la `deeperFlagCore_decLoss_pos_ae`, `RouteMSJDeeperFlagCore.lean:557`).
  - The `hpiv`/`hcvg`/`hrange`/`hcT` (`c' < carrierThreshold M`)/`hc'` (`ab/2 < c'`) scope threading: `hpiv`
    derived on the GOOD branch at every cut (`minAdm_redChain_le_deepTailMin`, unconditional); the `a+b≤M₂`
    scope (via `hcvg`/`hrange`) holds at every strict-shell good cut (routeverify §4b, 0 fails).
- **(E) Base cases outside the incidence route.** `j=0` shell-0 (`headSplit_pivotDom`/`pivotPeel_domination`,
  sound), `j=r` saturated shell — kept as-is; only `1≤j<r` uses the incidence route.

**PITFALLS / DEAD-ENDS (do NOT):**
- **Do NOT fill route B** (`headSplit_domination` via `headSplit_pivotDom` / `shell_corankOffSector_le_unif`
  with a constant `w`): routeverify CHECK 2 = a **genuine type error** — the blow-up pivot energy
  `frobSq(P̂·hsQ)` is `A_cor`-affine with **no `A_cor`-free lower bound** over the box (in-box cancellation on
  the rank-drop locus). This is the tracked sorry **D** on `deeperFlag_shell_le`/`deeperFlag_spineToCore`; its
  intended fill is DEAD. Bypass it — prove `deeperFlag_shell_le` directly via the incidence charts.
- **Do NOT fill `shellSpine_le_hsQ_box`** (FALSE on narrow tail, routefork refuter `(3,3,3)`, t=j=1, c'=4).
- **Do NOT drop `hcT` / the shell / the `a+b≤M₂` scope** (dropping `hcT` is what let the false box lemma be
  stated on `c'∈[7/2,9/2)`).
- **Do NOT radialize-and-drop the Jacobian** (seam-cert §10): keep the Schur charts atomic (unit-Jac,
  `chart5_bigcell_cov`) — the odd-cycle "deficit" is a coordinate artifact of dropping `|det J|`. If a
  radialising chart is unavoidable, carry its `|det J|` weight.
- **Brick F may DROP OFF the incidence path** (routeverify §5D): `exists_headSplitFrame`/`hfloor`/`U_sf` frame
  was introduced for `shell_corankOffSector_le_unif` (route B). The incidence route keeps the det-Gram
  coupled and works on the already-shell-restricted spine, so it likely does not need the Loewner floor.
  **Scope this at build start** — a probable simplification, not a required brick.
- **The WAIST branch** (`deepTailMin M > M₁`, incl. `(2,2,3)/(3,3,7)/(3,3,4,4)`) is a SEPARATE, still-open
  build (SVD-qPeel holes (c)/(e)); the dispatch quarantines it soundly. **Not** the incidence route, **not**
  tide-D-via-incidence.

**BANKED PIECES THAT FIT (consume, don't re-derive):** `corner_block_cube_lintegral_lt_top`,
`stratum_corner_lt_top`, `twoBlock_radial_le`, `clsCodim_gate_genL`, `chart5_bigcell_cov`,
`chart5_rank_le_iff_reassembled`, `chart4_Htilde_fibre_lt_top`, `freedSchurLoss_gammaPeel_le`,
`corankBlock_morsePeel_setLE`, `shellSpine_le_frontCharge`, `frontCharge_factor`, `frontLoss_pivotPoly_eq`,
`corank_survival_ae`, `pivotEnergy_stack_eq`, `lintegral_lt_top_of_finite_cover`, `cornerComparator_adm`,
`deepRankLE_lintegral_lt_top` (only if Arch-2 is chosen).

---

## Tide-D build shape + size estimate

**Shape (Arch-1, recommended).** Prove `deeperFlag_shell_le` DIRECTLY through the incidence charts,
discharging `DecoratedStepHyp` → `DecoratedDescent` → `(□)` → capstone (no new top-level wiring; the mint
pre-stage exists).

    shellSpineIntegrand  --step1(banked)-->  ∫_p coupledBoxIntegrand
                         --step2(banked)-->  ∫_p frontChargeIntegrand         [needs hGae, hEtopae]
                         --step3-entry(banked)-->  charge · frontLossIntegrand (polynomial pivot form)
     frontLossIntegrand (∫_x)  --STEP 3 CHARTS (BUILD)-->  Σ_{(ℓ,s) strata} per-chart CoV
                         --chart4(banked)-->  front/pivot fibre finite
                         --chart5(banked) + stratum_corner_lt_top(banked)-->  transverse radial finite
                                                        [BUILD: construct g, prove hom + hlb per stratum]
                         --step5 gluing(banked skeleton)-->  ≤ K · cornerComparator(redChain u M).integral(c'−ab/2)
     RHS finite by the DECORATED IH on the shorter chain (threshold reproduced by minAdm(M) ≤ ab + minAdm(redChain u M)).

**Size.** Medium-large, but **the analytic engine is entirely banked** — no rlct-calculus, no monomial-rlct,
no ℝ/ℂ bridge, no new radial theorem. The remaining labor is concentrated in:
- **(A) the front-block determinantal chart atlas + per-stratum `g`/`hom`/`hlb` construction** — the single
  biggest and genuinely-analytic piece (the `hlb` unit-sphere floor is the Morse-Bott crux);
- **(C) the finite-cover gluing / `(ℓ,s)` index-completeness** — Lean labor over banked math;
- **(D) the a.e. genericity discharge** (`hGae` from rankgen/`corank_survival_ae`, `hEtopae` from polynomial
  nonvanishing).
Bricks (B) gate and the radial corner (§3) are DONE. Brick F is likely droppable (probe first). The waist
branch is out of scope.

**One decision the controller must make before commissioning:** Arch-1 (complete `deeperFlag_shell_le`
directly, mint-wired) vs Arch-2 (discharge `hfin` per-`deepCell` and wire `deepRankLE` into the capstone).
Arch-1 is the smaller, mint-ready delta; both share the §3 radial engine. seamrlct is available for an
rlct-calculus consult if the `hlb` construction needs the elementary-calculus framing.
