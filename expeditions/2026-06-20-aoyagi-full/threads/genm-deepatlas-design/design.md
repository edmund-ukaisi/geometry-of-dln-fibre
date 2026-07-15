# deepatlas — the DEEP STRATIFIED-RESOLUTION ATLAS: explicit telescoping-Schur charts (spec for the Route-B deepgate formaliser tide)

**Seat:** pen-and-paper (DESIGN, decorrelated), aoyagi-full Stage 2, `genm-deepatlas-design`. **Date:**
2026-07-15. **NO Lean edits, NO build.** Exact algebra (composite-rank recursion, block-Schur factorization,
change-of-variables Jacobians, model-loss RLCT); MC only as a noise-limited guide. Decorrelated
`local-codex-consult` (gpt-5.x, xhigh, my conclusion WITHHELD; prompt framed "argue whichever way / say if my
telescoping picture is wrong"): `codex/deepatlas-{prompt,answer}.md`, `codex/deepatlas-run.log`. Verification
scripts (this thread, `scripts/`): `deep_atlas_verify.py`, `deep_fact.py`, `deep_profile.py`, `deep_gate.py`,
`deep_cov.py`, `deep_tube.py`, `seam_rlct.py`, `seam_mechanism.py`.

**Consumed / verified (signatures, not paraphrased):** `genm-deepgate/deepgate-cert.md` §1(A) (the CR recursion =
the atlas index), §1(B/C) (`γ_s`, `C_k`), §6/§7 (the Route-B gate + the stratified-resolution obligation) +
`scripts/composite_rank_codim.py` (the `κ_k` recursion, 3-way validated — re-ran here, reproduced); the front-atlas
Lean on `origin/genm-sj5-capbase` — `RouteMSJIncidenceChart5BigCell.lean` (`chart5_bigcell_cov` Jac≡1,
`chart5_rank_eq`, `chart5Shift` raw-pi diamond dodge), `RouteMSJIncidenceChart.lean` (`det_chartGram`, the
`Q_b=D[I|X]` minor chart, `pushThrough`), `RouteMSJIncidenceChart4Polar.lean` (`chart4_polar_scaling`,
`chart4_Htilde_fibre_lt_top`), `RouteMSJIncidenceExponent.lean` (`clsCodim`, `clsCodim_gate`, `minAdm_arity3`),
`RouteMSJIncidenceGluing.lean` (`lintegral_lt_top_of_finite_cover` / `_finset_cover`), `Core.SchurChartIff`
(`rank_fromBlocks_invertible₁₁`, `rank_le_iff_schur_eq` — the block-LU rank identity, banked sorry-free);
`genm-rankgen/rankgen-cert.md` (binding-cut scope `a+b ≤ deepTailMin−1`, route (c) generic-rank a.e.);
`genm-couplingfin/coupling-verdict-cert.md` (corank charge coupled); `genm-incidencepp/incidence-cert.md`
§3b (the FRONT-atlas template).

---

## ★ VERDICT — two layers, kept apart

1. **The GEOMETRIC atlas is explicit and buildable by a bounded induction on chain length, reusing the
   banked single-block pieces.** The deep degeneration `{rank Z_deep = ρ−k}` in the deep parameter space is
   resolved by a **telescoping sequence of chart-5 block-Schur big-cells**, one per recursion level, indexed by
   the CR-recursion tree (rank `r` of the current last layer × a size-`r` pivot minor, down to termination).
   The one genuinely-new piece vs the front's single block — the **product-layer reduction** (the reduced
   chain's last layer is the product `L_{p-2}·A`, not a free coordinate) — has a **clean unit-Jacobian
   change of variables** (§2.2, Codex-improved: normalise the pivot columns and the completion is
   unitriangular, `|det| ≡ 1`). Charts, Jacobians, and set-theoretic coverage are all explicit and
   exact-verified. This is the deliverable the formaliser consumes.

2. **The ANALYTIC gate — that these charts monomialise the LOSS so that per-stratum `rlct = C_k/2`, i.e.
   `∫₀^δ r^{C_k−1−2q}dr < ⊤` for `2q < minAdm(M)−ab` — does NOT follow from the geometric atlas alone, and
   is the load-bearing remaining obligation.** Decorrelated Codex caught the confound my first pass missed:
   the telescoping creates a **product seam** `F·E` in the loss (already at `(2,2,2)`, `s=0`, the `r=1`
   chart: `Z = (HΔ, HU + FE)`, zero-locus `{H=0,E=0} ∪ {H=0,F=0}`, loss `≍ ‖H‖² + ‖FE‖²`), so the loss is
   **not normal-crossing on a single chart**, and **`codim = CR` does NOT imply `rlct = CR/2` for free**
   (Codex's clean caution: `x²+y⁴` has zero-set codim 2 but threshold `3/4 < 1`). **I checked the base
   multi-layer case `(2,2,2)` both by hand and numerically: the seam is benign there — `rlct = 3/2 = CR/2`
   exactly (§4.2).** But the general statement needs a **one-peel local-zeta recursion** (each stratum's
   transverse loss is quadratic-nondegenerate; the exponent minimises over `r` as CR does, uniformly across
   pivot-collapse seams and the coupled det-charge). **This RESHAPES deepgate §7-Next**: the CHARTS are
   "explicit determinantal big-cells, not a wall" (true), but the LOSS-monomialisation at the seams is the
   substantive analytic content, and it is not size-predictable from the 687-LoC front atlas until the
   one-peel recursion is in hand.

**Recommendation to the controller: do NOT launch the full multi-tide deep-atlas build until the one-peel
local-zeta recursion (§4.4) is established pen-and-paper.** The geometric-atlas tides (§7 tides A–C) are
safe to build now and are reusable regardless; the analytic gate (tide D) is where the risk lives.

---

## 1. Objects and scope

Deep layers `L₀,…,L_{p-1}`, `L_i : ℝ^{v_i × v_{i+1}}`, `v_i = M_{i+2}` (`i = 0..p`, `p = last−2`). The deep
product `Z_deep = L₀·L₁·⋯·L_{p-1} : ℝ^{v₀ × v_p} = ℝ^{M₂ × M_last}`; `ρ := deepTailMin M = min(v₀,…,v_p) =
min(M₂,…,M_last)`. Target strata `S_s := { (L_i) : rank Z_deep ≤ s }` in the parameter space
`P := ∏_i ℝ^{v_i × v_{i+1}}`, `s = ρ−k`, `k = 1,…,ρ`.

**Codim (parameter-space, NOT determinantal — the GUARD).** `κ_k := CR((M₂,…,M_last), ρ−k)`, the
composite-rank recursion (deepgate §1(A), re-verified here):

    CR((v₀,…,v_p), s) = min_{0≤r≤min(v_{p-1},v_p)} [ (v_{p-1}−r)(v_p−r) + CR((v₀,…,v_{p-2}, r), s) ],
    base CR((v₀,v₁), s) = (v₀−s)₊(v₁−s)₊ ,   inner = 0 when r ≤ s.

For `p = 1` (arity-4 chains: deep = `(M₂, M₃)`, ONE layer) `CR = (v₀−s)(v₁−s)` **is** the determinantal codim
and the deep atlas **is the front single-matrix big-cell verbatim** (chart 5). The genuinely-new multi-layer
content starts at **arity ≥ 5** (`p ≥ 2`). `deep_atlas_verify.py`: the naive "make one layer rank ≤ s"
over-counts (1463 mismatches vs CR over widths 1..6, arity ≤ 4) — the recursion is essential
(smallest witness `(1,2,1), s=0`: `CR=1`, single-bottleneck says 2).

**Binding-cut scope (rankgen).** At a binding cut `u = t★+j`, strict shell `1 ≤ j < r`, `a = M₀−u`, `b = M₁−u`:
`a+b ≤ ρ−1`, so `d := ρ−b ≥ a+1 ≥ 2`, `b ≤ ρ−2`. The corank charge sits strictly inside the convergent
regime. Keep the corank charge over the **effective `ρ`-dimensional** row space of `Z_deep`, NOT `M₂` (rankgen §5).

---

## 2. The explicit charts (DELIVER 1)

The resolution is an **induction on chain length `p`**, peeling the last layer. The atlas cell for a rank
profile `(r_{p-1}, r_{p-2}, …)` is the composition of per-level charts, each a chart-5 block-Schur big-cell +
(when the level's rank exceeds `s`) a product-layer reduction. Two per-level maps.

### 2.1 The per-level block-Schur big-cell (REUSE — `Core.SchurChartIff` + `chart5_bigcell_cov`)

At a level with current effective last layer `M ∈ ℝ^{n×d}` (initially `L_{p-1}`, `n=v_{p-1}`, `d=v_p`), fix
`r ≤ min(n,d)` and size-`r` row/column pivot sets `(I,J)`; permute them first (Jacobian `±1`). Block
`M = [[Δ, U],[V, W]]`, `Δ ∈ GL_r`, and set the **transverse Schur coordinate**

    E := W − V·Δ⁻¹·U  ∈ ℝ^{(n−r)×(d−r)} .

The coordinate map `(Δ,U,V,E) ↦ [[Δ,U],[V, V Δ⁻¹ U + E]]` is a **translation in the `W`-block**, Jacobian
`≡ 1` (this IS `chart5_bigcell_cov`), and `rank M = r + rank E` (this IS `rank_fromBlocks_invertible₁₁` /
`chart5_rank_eq`), so `{rank M ≤ r} = {E = 0}`, codim `(n−r)(d−r)`. **No change from the front — direct reuse.**

At the **generic rank** `r = min(n,d)` the E-block is empty (dim 0, `deep_fact.py` §Q3): no transverse
condition, the layer stays full-rank and the codim is pushed entirely down the recursion. This is why CR can be
`< ` determinantal (`(1,2,1),s=0`: `L₁` at generic rank 1, all codim on the reduced head).

### 2.2 The product-layer reduction (THE NEW PIECE — unit-Jacobian CoV)

The reduced chain's last layer is `L_{p-2}·A` where `A =` the pivot COLUMNS of `M` — a **product**, not a free
coordinate. Resolve it by a right-multiplication CoV on the free layer `L := L_{p-2} ∈ ℝ^{m×n}` (`m = v_{p-2}`).
**Codex-improved, unit-Jacobian form (normalise the pivot columns first):**

    A₀ := A·Δ⁻¹ = [ I_r ; V Δ⁻¹ ]  (n×r),      G₀ := [ A₀ | K ] = [[ I_r, 0 ],[ V Δ⁻¹, I_{n−r} ]]  (n×n),
    det G₀ = 1,      M = G₀ · [[ Δ, U ],[ 0, E ]] .

Split `L·G₀ = (H, F)`, `H := L A Δ⁻¹ ∈ ℝ^{m×r}` (the **reduced last layer**, now a free coordinate), `F := L K
∈ ℝ^{m×(n−r)}` (a **spectator**). Then

    L·M = ( H Δ ,  H U + F E ) ,     and on {E = 0}:  L·M = H·[Δ | U],  with [Δ | U] full row rank r,

so `rank(B·L·M) = rank(B·H)` for any preceding head `B` (verified `deep_cov.py`, 0 mismatches). **The joint
coordinate map `(Δ,U,V,E,H,F) ↔ (M,L)` has absolute Jacobian ≡ 1** (Schur map Jac 1, `det G₀ = 1`,
cross-derivatives off-diagonal) — the cleanest Lean-facing form.

> **Variant (my original, also valid).** The *raw* completion `G = [[Δ,0],[V,I]]`, `det G = det Δ`, gives the
> reduced layer as exactly `L·A` (no `Δ⁻¹` twist) at Jacobian `|det Δ|^m` (`deep_cov.py`: 0 mismatches). Use the
> normalised `A₀=AΔ⁻¹` for a **unit-Jacobian** atlas (recommended, matches chart 5's `|det|≡1`); use the raw
> one if a downstream lemma wants exactly `L·A` and can carry the monomial `|det Δ|^m` (the deep analog of the
> front's `|det D|^{n−b−a−u}` power). Either is a bounded, explicit CoV.

After the reduction, recurse on the shorter chain `(v₀,…,v_{p-2}, r)` with free last layer `H`; base case
`p = 1` is the single-matrix chart-5 big-cell (all exact ranks `0 ≤ r ≤ s`).

### 2.3 The per-cell transverse coordinate and its codim (DELIVER 1, exponent side)

A cell = a root-to-leaf **path** in the CR tree with effective ranks `r_j` and effective output widths
`w_p = v_p`, `w_{j+1} = r_{j+1}`. Its transverse (normal) coordinate is the tuple of Schur blocks

    E_j ∈ ℝ^{(v_j − r_j) × (w_{j+1} − r_j)} ,    total codim  C_path = Σ_j (v_j − r_j)(w_{j+1} − r_j) ,

and `min over paths C_path = CR(deep, s) = κ_k` (this IS the CR recursion; `deep_profile.py` exhibits the
minimiser's per-level drops, e.g. `(2,2,2),s=0`: `E`-codim 1 at `L₁→`rank 1, then `E`-codim 2 at the reduced
head `(2,1)→`rank 0, total 3 = CR). The rank-drop locus on a cell is `⋂_j {E_j = 0}` (the **conjunction** of
the per-level Schur vanishings).

---

## 3. The big-cell selectors, the atlas index, and gluing (DELIVER 2, 3-coverage)

### 3.1 The finite index (the CR-recursion tree — ALL ranks, ALL pivots)

    𝓘_p(v₀,…,v_p; s) = ⨆_{r=0}^{min(v_{p-1},v_p)}  C(v_{p-1}, r) × C(v_p, r) ×
                         { {∗}                              if r ≤ s
                         { 𝓘_{p-1}(v₀,…,v_{p-2}, r; s)     if r > s

(`C(n,r)` = size-`r` subsets = pivot minors). A **finite** tree: bounded branching (finitely many ranks ×
finitely many minors per node), depth `≤ p`. The measurable big-cell selectors are the pivot-minor charts
`{det M_{I,J} ≠ 0}` at each level — exactly the front's `{det Q_b|_J ≠ 0}` selectors, one per recursion level.

> **Coverage subtlety (Codex Q1, load-bearing).** Take the FULL tree, NOT just the CR-minimising branch: a
> minimiser computes the codim, but lower-rank branches are needed for coverage (their centres are measure-zero,
> but the integrability argument sees their neighbourhoods). And at a terminal node exact coverage of
> `{rank ≤ s}` needs **all ranks `0,…,s`** (a size-`s` pivot chart covers only rank-exactly-`s`).

### 3.2 Set-theoretic completeness (DELIVER 3)

**[FACT] The rank/pivot index is set-theoretically complete:** every `(L_i) ∈ S_s` lies on some cell — at
each level take the actual rank of the current effective layer and a nonzero maximal minor, recurse while the
rank exceeds `s`. The open chart domains `{det M_{I,J} ≠ 0}` (per level) form a finite open cover of a
neighbourhood of `S_s`; overlaps are lower-rank loci (measure-zero within each stratum), null as in the front.

### 3.3 Null-overlap gluing (DELIVER 3 — DIRECT REUSE)

The banked `RouteMSJIncidenceGluing.lintegral_lt_top_of_finite_cover` / `_finset_cover` is **atlas-parameterised**
(cells + up-to-null coverage as hypotheses) — it consumes the deep atlas with **no change**: supply the finite
cell family (§3.1) + the coverage null-set (§3.2) + per-cell finiteness (§4), get `∫_{S_s-nbhd} f < ⊤`. This
piece is done and robust to any atlas reshape.

---

## 4. The per-chart radial exponent → the C_k gate (DELIVER 4) — the LOAD-BEARING OPEN PART

### 4.1 What the gate needs

Per-stratum finiteness `∫₀^δ r^{C_k−1−2q} dr < ⊤` for `2q < minAdm(M)−ab`, where (deepgate §1(C))

    C_k = min( u·ρ ,  u·(ρ−k) + κ_k − γ_{ρ−k} ) ,   γ_s = max_{max(0,b−s)≤h≤b} h(a+b−s−h) .

The Nat gate `C_k ≥ minAdm(M)−ab` is **proven arithmetic** — re-verified here 0 violations over 1416 binding
strict-shell cuts, arity 4–6 (`deep_gate.py`); `κ_k ≥ binom(k+1,2)` and `minAdm(deep) ≥ minAdm(M)` also 0
violations. **This is banked** (deepgate + the front `clsCodim_gate` pattern). The gate ARITHMETIC is not the
risk; the risk is whether the atlas actually **realises** the deep-measure exponent `κ_k` so that the radial
integral has the claimed exponent.

### 4.2 The seam — codim = CR does NOT auto-give rlct = CR/2 (Codex, confirmed)

On a cell the loss `‖W·Z_deep‖²` (composed through the reduction) is `‖H Δ‖²` + higher-order + the `F E`
product from §2.2. At `(2,2,2)`, `s=0`, `r=1`: `Z = (HΔ, HU + FE)` (`H,F ∈ ℝ^{2×1}`, `E ∈ ℝ`), so
`Z = 0 ⟺ H = 0 ∧ FE = 0`, and the zero-locus is the **union of two components** `{H=0,E=0}` (codim 3 = CR) and
`{H=0,F=0}` (codim 4), meeting along `{H=0,E=0,F=0}`. The loss model there is `‖H‖² + ‖F E‖²` — a **product
seam**, not normal-crossing. **`codim` alone does not determine the RLCT** (Codex's caution, exact: `x²+y⁴`
has zero-set codim 2 but `∫(x²+y⁴)^{−q}` threshold `3/4 < 1 = codim/2`, via the weight `x∼t², y∼t`).

**[FACT] But the `(2,2,2)` seam is BENIGN — `rlct = 3/2 = CR/2` exactly.** By hand: `∫ (‖H‖²+‖FE‖²)^{−q}`,
polar in `H` (`r_H dr_H`) and `F` (`s ds`), inner `∫ r_H(r_H²+A)^{−q}dr_H ≍ A^{1−q}` with `A = s²E²`, gives
`∫ s^{3−2q} E^{2−2q} ds dE`: finite ⟺ `q < 2` (the `s`/F-direction) **and** `q < 3/2` (the `E`-direction) ⟹
threshold `= 3/2 = CR/2`, the low-codim core binding. Numerically confirmed: tube RLCT of `‖H‖²+‖FE‖²` ≈ 1.45,
vs the normal-crossing control `‖H‖²+E²` ≈ 1.51 (`seam_mechanism.py`). **Mechanism:** each component's
transverse loss is a genuine sum of squares (quadratic-nondegenerate), so `rlct = min_component (codim/2) =
CR/2`; the seam does not create a `y⁴`-type higher-order vanishing.

### 4.3 The determinant charge rides along COUPLED (Codex Q3, reconciles couplingfin)

The corank charge `det(Q_b Q_bᵀ)^{−a/2}`, `Q_b = A_cor·Z_deep`, does **not** decouple. On `{E=0}` with
`Z = Z_red·D`, `D = [Δ | U]` (full row rank), `N = A_cor·Z_red`: `Q_b Q_bᵀ = N (D Dᵀ) Nᵀ`, `D Dᵀ ≻ 0`. On a
compact subchart `λI ≤ D Dᵀ ≤ ΛI`, `λ^b det(N Nᵀ) ≤ det(Q_b Q_bᵀ) ≤ Λ^b det(N Nᵀ)` — the charge has the SAME
local corank exponent as the reduced charge, up to a bounded factor. So the charge threads through the recursion
as a **bounded positive-definite right metric** `R = D Dᵀ`, NOT a harmless scalar; the inductive statement must
be **uniform under an arbitrary PD right metric**. Off `{E=0}` the `FE` term enters the charge too. This is the
concrete form of couplingfin's "keep `w` coupled" at the deep level, and it is why deepgate's Route A **bare**
comparator fails (`r^{−ab}`) while Route B (direct per-stratum gate) works — the charge `γ_s` is a fixed
monomial power on each stratum, absorbed by the gate `C_k ≥ minAdm−ab`.

### 4.4 The obligation — a one-peel local-zeta recursion (NOT settled by the geometry)

**[INFERENCE, Codex-concurred]** The geometric atlas (§2–3) does not by itself prove `rlct = C_k/2` per
stratum. The remaining obligation is a **one-peel analytic recursion**: directly from

    Z = Z_head·( H Δ ,  H U + F E ) ,

prove the local-zeta exponent (with the deep measure + the coupled charge `R = D Dᵀ`) minimises over `r` as CR
does, **uniformly** as `F` loses rank (the `FE` seam), as pivot minors approach lower-rank charts
(pivot-collapse seams), and across non-comparable sectors. The clean sufficient structure (from §4.2): each
stratum's transverse loss is **quadratic-nondegenerate** on each component, so `rlct = min_component (codim/2)`
and the min over paths is `CR/2`. **This is the "stratified-resolution / induction lemma" deepgate §4/§6/§7
named — now made precise: it is a loss-monomialisation fact, not a chart-existence fact.**

**Non-comparable scalings (DELIVER 3, analytic completeness).** [FACT] IF the uniform comparability
`c Σ_j ‖E_j‖² ≤ loss ≤ C Σ_j ‖E_j‖²` held, non-comparable scalings could not lower the exponent: with
`E_j ∼ t^{α_j}`, `min α_j = 1`, volume `t^{Σ c_j α_j}` with `Σ c_j α_j ≥ Σ c_j = C_path`, loss order `t²`, so
the min is at comparable scaling, threshold `C_path/2`. [FACT] **But that comparability does NOT follow from the
Schur atlas** (the `FE` seam is exactly its failure) — it must be re-established per stratum via §4.4. My
`(2,2,2)` check is one positive instance; the general claim is open.

---

## 5. Reuse vs genuinely-new (DELIVER 5)

**Reused verbatim / with a re-export (banked, sorry-free on `genm-sj5-capbase`):**
- `Core.SchurChartIff.rank_fromBlocks_invertible₁₁` / `rank_le_iff_schur_eq` — the block-LU rank identity
  (§2.1). Network-free, over any field. Direct.
- `RouteMSJIncidenceChart5BigCell.chart5_bigcell_cov` — the Jac≡1 Schur-block translation CoV (§2.1); the
  `chart5Shift` **raw-pi diamond dodge** (transcribe the shift over `Fin s → Fin t → ℝ`, not `Matrix`) applies
  identically to `V Δ⁻¹ U` and to the reduction shift `V Δ⁻¹`.
- `RouteMSJIncidenceChart4Polar.chart4_polar_scaling` / `chart4_Htilde_fibre_lt_top` — the polar/radial
  fibre scaling `∫(‖H̃‖²+τ²)^{−q}dH̃ = τ^{N−2q}·K`, `K<⊤` for `2q>N` (the per-stratum radial, §4.1). Reused
  once the loss is monomialised (§4.4).
- `RouteMSJIncidenceGluing.lintegral_lt_top_of_finite_cover` / `_finset_cover` — the atlas-parameterised
  null-overlap gluing (§3.3). Reused with the deep index; no change.
- `RouteMSJIncidenceExponent.clsCodim_gate` pattern + deepgate's `C_k ≥ minAdm−ab` — the Nat exponent gate
  (§4.1). Adapt `clsCodim` → `C_k` (the `min(uρ, u(ρ−k)+κ_k−γ)` form); the discharge is the deepgate §4 clean
  chain (`minAdm(M) ≤ κ_k + minAdm(M₀,M₁,ρ−k)` + the 3-chain front QIP + `minAdm(deep) ≥ minAdm(M)`).
- CoV engine `lintegral_image_eq_lintegral_abs_det_fderiv_mul` (Mathlib) — the per-chart CoV, exactly as the
  front used it; the reduction CoV (§2.2) is a `LinearMap` right-multiplication with `|det| ≡ 1` (normalised) or
  `|det Δ|^m` (raw), the same shape as the front `|det D|` charts.

**Genuinely-new content (the multi-layer telescoping vs the front's single block):**
- The **product-layer reduction CoV** (§2.2) — `L ↦ L·G₀`, `G₀` unitriangular, `|det|≡1`; the split into
  reduced layer `H = LAΔ⁻¹` (free) + spectator `F = LK`. New, but a bounded explicit CoV.
- The **recursive finite path/pivot index** (§3.1) + the induction-on-chain-length assembly (§2). New
  bookkeeping (dependent widths, pivot reindexing — the main Lean engineering cost per Codex Q5), not new theory.
- The **coupled PD-right-metric charge** threading (§4.3) — the inductive statement uniform under `R = D Dᵀ`.
- **THE WALL:** the **one-peel local-zeta / loss-monomialisation recursion** (§4.4) — genuinely new analytic
  content, NOT reducible to the front pieces or the gluing lemma. This is a stratified-integration argument.

---

## 6. GUARD compliance (CR, not determinantal)

Every codim in this design is the **parameter-space** `CR` recursion (§1, §2.3), never the determinantal
`(M₂−s)(M_last−s)`. The atlas index (§3.1) IS the CR tree; the transverse coordinate (§2.3) has total dim =
`CR` at the minimiser (`deep_profile.py`); the gate (§4.1) uses `κ_k = CR(deep, ρ−k)` (`deep_gate.py`, 0
violations). The determinantal codim is used **nowhere**. `deep_atlas_verify.py` confirms the naive
single-bottleneck (determinantal-flavoured) over-counts (1463 mismatches).

---

## 7. Size estimate + sub-tide plan (DELIVER 6)

Front atlas (measured on `genm-sj5-capbase`): 5 files, **687 LoC** (Chart 258 / Chart4Polar 110 / Chart5BigCell
169 / Exponent 97 / Gluing 53), all 5 chart files **sorry-free** (the brief's "2 open sorries" are at the
Brick-D *assembly* level, not the charts). The deep atlas is harder (multi-layer). Plan:

- **Tide A — the reduction CoV + block-Schur step (geometric, safe now).** `RouteMSJDeepChartSchur` (per-level
  big-cell, re-export `SchurChartIff` + `chart5_bigcell_cov`) + `RouteMSJDeepChartReduce` (the `L↦L·G₀`
  unit-Jacobian CoV, §2.2, with `rank(B·L·M)=rank(B·H)` on `{E=0}`). ~250–350 LoC. Reuses the diamond dodge.
- **Tide B — the recursive index + set-theoretic coverage + gluing wiring (geometric, safe now).**
  `RouteMSJDeepAtlasIndex` (the finite CR-tree index §3.1, `Fintype`/`Finset`, dependent widths) +
  coverage null-set + wire `lintegral_lt_top_of_finset_cover`. ~200–300 LoC (pivot-reindexing is the cost).
- **Tide C — the C_k exponent-gate arithmetic (safe now, pure `ℕ`).** `RouteMSJDeepExponent`: `C_k`, `γ_s`,
  `κ_k` as `ℕ`, the gate `C_k ≥ minAdm−ab` via deepgate's clean chain. Mirrors `RouteMSJIncidenceExponent`.
  ~120–180 LoC.
- **Tide D — the one-peel local-zeta / loss-monomialisation recursion (THE WALL — gate on §4.4 first).** Per
  stratum: `rlct = C_k/2`, threading the `FE` seam + the coupled charge + non-comparable sectors, by chain-length
  induction with quadratic-nondegeneracy on each component. **Size not responsibly predictable** until the
  pen-and-paper one-peel recursion (§4.4) is proven — likely another atlas-sized tranche IF benign, a genuine
  stratified-integration module if not.

Tides A–C (geometric + arithmetic, ~570–830 LoC, ~3 sub-tides) are ready. **Tide D is held on the §4.4
pen-and-paper de-risk.**

---

## Close

- **Firmest result (certificate).** The deep degeneration `{rank Z_deep = ρ−k}` has an **explicit finite
  telescoping-Schur atlas**: per-level block-Schur big-cell (`E := W − VΔ⁻¹U`, Jac≡1, `{rank ≤ r}={E=0}`) +
  a **unit-Jacobian product-layer reduction** `L ↦ L·G₀` (`G₀ = [[I,0],[VΔ⁻¹,I]]`, `det=1`, reduced layer
  `H = LAΔ⁻¹` free, spectator `F = LK`, `rank(B·L·M) = rank(B·H)` on `{E=0}` — 0 mismatches `deep_cov.py`),
  indexed by the CR-recursion tree (all ranks × all pivots; all ranks `0..s` at leaves for exact coverage),
  glued by the banked atlas-parameterised finite-cover lemma. Total transverse codim = CR = κ_k (`deep_profile.py`).
  The GUARD holds (parameter-space CR, never determinantal). Geometric atlas = bounded induction on chain
  length reusing the 5 banked front pieces.
- **Most likely to break it (Codex decorrelated-caught, confirmed).** The **loss-monomialisation at the
  telescoping seams**: `codim = CR` does NOT imply per-stratum `rlct = CR/2` — the reduction creates a product
  seam `FE` (already at `(2,2,2)`), and `x²+y⁴`-type higher-order vanishing would push `rlct` below `codim/2`
  and break the `C_k` gate. The `(2,2,2)` base case is **benign** (`rlct = 3/2 = CR/2`, hand + numeric), by
  component-wise quadratic-nondegeneracy — but the general statement is the one un-discharged obligation.
- **Next construction/consult that would settle the open part.** The **one-peel local-zeta recursion** (§4.4):
  prove, from `Z = Z_head·(HΔ, HU+FE)`, that the local zeta exponent (with the deep measure + coupled charge
  `R = DDᵀ`) minimises over `r` as CR does, uniformly across the `FE`/pivot-collapse seams and non-comparable
  sectors — the clean sufficient form being "each stratum's transverse loss is quadratic-nondegenerate on each
  component, so `rlct = min_component(codim/2) = CR/2`." A pen-and-paper follow-on should verify this on a
  deeper telescope (e.g. `(2,2,2,2)`, `(2,3,3,3)` — two nested seams) and either prove the general
  quadratic-nondegeneracy or find the chain where a seam goes higher-order (which would weaken the BOUNDED
  verdict at the RLCT level, not the codim level). **Gate Tide D on this.**
