# Step 3 (`frontChargeIntegral < ⊤`) — the 3-module design + the general-L BOUNDED/WALL verdict

**Seat:** pen-and-paper (DESIGN, decorrelated), aoyagi-full Stage 2, `genm-stepdesign`. **Date:** 2026-07-15.
**NO Lean edits / build.** Exact linear algebra + a decorrelated `local-codex-consult` (gpt-5.6, xhigh, my
conclusion WITHHELD, prompt framed "argue whichever way"): `codex/crux-{prompt,answer,run.log}`. Numerics
(exact-algebra guide, MC only where flagged): `/tmp/tail_reduction_check.py` (leaf reduction EXACT),
`/tmp/minadm_check.py`, `/tmp/gap_scan.py`, `/tmp/tail_drop_scan.py`, `/tmp/local_model_conv.py`,
`/tmp/dh_tube_check*.py`.

**Consumed / verified (signatures, not paraphrased):**
`genm-incidencepp/incidence-cert.md` §0/§3/§3b/§Verdict (leaf charts + `C_{ℓ,s}` + the §3 controller
caveat on index-incompleteness); `genm-couplingfin/coupling-verdict-cert.md` (`A_cor→0` transverse,
shell-drop); `genm-rankgen/rankgen-cert.md` (`b ≤ deepTailMin−1` at binding cut, route (c), §5
effective-dimension); `genm-sj5-capstone` `RouteMSJIncidenceAssembly.lean`
(`frontChargeIntegrand` L389, `coupledBox_le_frontCharge`, `shellSpine_le_frontCharge`, `clsCodim_gate_genL`
L482, `deepTailMin` L57, `deeperFlagZdeep`), `RouteMSJIncidenceChart{,4Polar,5BigCell}.lean` (banked
charts `det_chartGram`, `transverseSchurGram`, `chartProjComplement`, `chart4_Htilde_fibre_lt_top`,
`chart5_bigcell_cov`), `genm-sj5-pradial` radial primitives (`corner_block_lintegral_lt_top`,
`twoBlock_radial_le`, `radial_morse_residual_power_le`), the capstone-peer covarch Codex
(`genm-sj5-capstone/codex/covarch-{prompt,answer}.md`).

---

## ★ VERDICT (the crux de-risk)

**BOUNDED — the general-`L` `frontChargeIntegral < ⊤` is TRUE for every `c' < T1` (`q < T1_q := (minAdm(M)−ab)/2`),
and this threshold is EXACTLY right (it is the geometric RLCT the capstone targets). There is NO general-`L`
wall.** But the crux de-risk surfaced one load-bearing **architecture correction**, decorrelated-confirmed and
matching incidencepp's own §3 controller caveat:

> **The banked leaf charts (incidencepp §3 / the `(ℓ,s)` atlas) do NOT, by themselves, close Step 3 for
> general `L`.** For a substantial fraction of arity-≥4 strict-shell binding cuts (65/476 ≈ 14 % in the
> width-≤6 sweep), the leaf gate `min_{ℓ,s} C_{ℓ,s}` **strictly over-estimates** the true codimension
> `minAdm(M)−ab = 2·T1_q`. The gap is filled by **deep-factor (tail-rank-drop) strata that live in the
> `z_tail` integration, not in the front `(ℓ,s)` atlas.** These strata are finite for `q < T1_q` (they bind
> exactly at `T1_q`, tight) — so no wall — but they are a **genuinely-missing part of the domain cover**, and
> Step 3 must charge the deep degeneration through the **reduced comparator + outer IH** (the recursion),
> NOT through the leaf charts. Trying to close `∫ frontChargeIntegrand < ⊤` with the `(ℓ,s)` atlas + a
> finite cover alone will either be unprovable or (worse) over-claim finiteness up to `½·min C_{ℓ,s} > T1_q`,
> which is FALSE.

The three modules split, with this correction, as:
- **(i-a) EXACT leaf reduction** — the whole integrand reduces EXACTLY to a `ρ = deepTailMin`-dimensional leaf
  in `(z0·S̃, A_cor·S̃)`; verified (`/tmp/tail_reduction_check.py`, all three of charge / `E_top` / `E_tr`).
  Not a wall; clean linear algebra.
- **(ii) THE CRUX — the joint `D–H` tube (the front `|det D|^{d−a−u}` coupling).** BOUNDED. Decorrelated Codex
  CONFIRMS finite and hands the **cleanest primitive**: keep `(U,B)` together, the covariance
  `L Lᵀ = I_b⊗PPᵀ + DᵀD⊗I_u` (eigenvalues `pᵢ²+σⱼ²`), density `∏(pᵢ²+σⱼ²)^{−1/2}`. `clsCodim_gate_genL`
  SUFFICES for this (front) part.
- **(iii) radial blow-up `r^{C_{ℓ,s}−1}`** — capstep3 building; decomposition-agnostic; primitives banked.
- **(i-b) THE DEEP-DEGENERATION (newly isolated as the real general-`L` content).** The `z_tail`-integration
  near `{rank Z_deep < ρ}`. This is where the missing tail-drop strata live; **must be charged via the
  comparator/IH**, and rests on rankgen's `deepTailMin`-effective-dimension corank facts.

---

## 0. The object and the reduction map

At a binding cut `u = t★+j` (`1 ≤ j < r`), with `a = M₀−u`, `b = M₁−u`, `ρ := deepTailMin M = min(M₂,…,M_last)`,
`n := M_last`, the Step-1/2 chain (`shellSpine_le_frontCharge`, already sorry-free) lands on

    frontChargeIntegral := ∫_{p ∈ paramsBoxM(redChain u M) ×ˢ matBox(M₁−u)(M₂)} frontChargeIntegrand M u c' p,

where `p = (z, A_cor)`, `z ∈ Params(redChain u M)` splits (head split) into the **head** `z0 : u×M₂` and the
**deep tail** `z_tail` building the deep factor `Z := deeperFlagZdeep M u z` (an `M₂×n` layer PRODUCT), and

    frontChargeIntegrand = ∫_{x=(P,B,C) ∈ outerDom, IsUnit P}
        det(Q_b Q_bᵀ)^{−a/2} · Cresid(ab,c') · (E_top + E_tr)^{−q},   q = c' − ab/2,

    Q_p = z0·Z (u×n),  Q_b = A_cor·Z (b×n),  hsQ = [Q_p; Q_b] = R·Z,  R = [z0; A_cor] ((u+b)×M₂),
    E_top = ‖P·Q_p + B·Q_b‖²_F,   E_tr = ‖C·(Q_p + P⁻¹ B Q_b)·(I_n − Π_b)‖²_F,   Π_b = Q_bᵀ(Q_bQ_bᵀ)⁻¹Q_b.

**GOAL: `frontChargeIntegral < ⊤` for `ab/2 < c' < T1`, i.e. `q < T1_q = (minAdm(M)−ab)/2`.** Only `< ⊤` is
needed (no sharp constant). The finiteness is genuinely JOINT: the inner `∫_x` is NOT uniformly finite in
`(z,A_cor)` (incidence cert §Verdict-1); it converges only after the `(z,A_cor)`-integration.

The reduction is a **fibration over `z_tail`**:

    frontChargeIntegral = ∫_{z_tail} [ ∫_{z0, A_cor, x} frontChargeIntegrand(fixed z_tail) ] dz_tail.

Modules (ii)+(iii) resolve the **inner** integral (front + corank, per fixed generic `z_tail`); module (i-b)
resolves the **outer** `z_tail` integration (the deep degeneration). Module (i-a) is the exact identity that
makes the inner integral a `ρ`-dimensional leaf.

---

## 1. Module (i-a): the EXACT leaf reduction to `ρ = deepTailMin` (VERIFIED)

**Claim (exact).** Write the rank factorization `Z = S̃·Õ`, `S̃ : M₂×ρ` of full column rank `ρ` (a.e.-`z_tail`,
`ρ = rank Z` by rankgen route (c)), `Õ : ρ×n` with `Õ Õᵀ = I_ρ`. Define the **effective leaf variables**

    Q̂_p := z0·S̃ (u×ρ),   Q̂_b := A_cor·S̃ (b×ρ).

Then the ENTIRE integrand equals the leaf integrand in dimension `ρ`:

    det(Q_b Q_bᵀ)  = det(Q̂_b Q̂_bᵀ),
    E_top          = ‖P·Q̂_p + B·Q̂_b‖²_F,
    E_tr           = ‖C·(Q̂_p + P⁻¹ B Q̂_b)·(I_ρ − Π̂_b)‖²_F,   Π̂_b = Q̂_bᵀ(Q̂_bQ̂_bᵀ)⁻¹Q̂_b.

**Status: VERIFIED numerically-exact** (`/tmp/tail_reduction_check.py`, `M₂=5, n=6, ρ=3<M₂`, all three
identities match to machine precision). Codex CONCURS (Q-B1 [FACT]), with the load-bearing key step
`Q̃ₚ(I_n−Π_b) = (Q̂_p+P⁻¹BQ̂_b)(I_ρ−Π̂_b)·Õ` and `‖·Õ‖_F = ‖·‖_F` (right-mult by the orthonormal-row `Õ`).

**Why this matters (two corrections to the covarch leaf reduction).**
1. **The leaf dimension is `ρ = deepTailMin`, NOT `M₂`.** The covarch answer's polar `Z = S·O` (`S = G^{1/2}`,
   `M₂×M₂`) and its dominant-`M₂`-minor variant BOTH presume `rank Z = M₂`. For deep chains `rank Z = ρ` can
   be `< M₂` (rankgen: e.g. narrow interior layer). Then `G = ZZᵀ` is SINGULAR and the `M₂`-polar breaks; the
   correct object is the `ρ`-dim rank factor `S̃`. The identities above hold at the true `ρ`.
2. This is EXACTLY the "effective column dimension is `deepTailMin`, not `M₂`" of rankgen §5 — now realized as
   a per-integrand identity, not just a scope note.

**Lean shape.** A pointwise (a.e.-`z_tail`) matrix identity: choose `S̃` measurably (SVD / a
`ρ`-dominant-minor selector on `Z`), prove the three `frobSq`/`det` identities by the block algebra
(`fromCols_mul_transpose` + the `Õ Õᵀ = I` cancellation, all Mathlib-level). No CoV, no measure — a rewrite
of the integrand. **Bounded labour; the substance is the measurable `S̃`-selector** (parallels Brick F's
frame selector, `RouteMSJDeeperFlagCore` `deeperFlag_spineToCore`).

> **Scope carried:** `a+b ≤ ρ = deepTailMin` (needed for `Q̂_b Q̂_bᵀ` PosDef a.e. + the corank charge). rankgen
> gives `a+b ≤ deepTailMin − 1` STRICT at binding cuts ⟹ `d := ρ−b ≥ a+1` (used throughout module (ii)).

---

## 2. Module (ii): THE CRUX — the joint `D–H` tube (front `|det D|^{d−a−u}`), BOUNDED

This is the "genuine (A) largest piece." It concerns the INNER (front + corank) integral of the `ρ`-leaf, per
fixed generic `z_tail`. Everything here is the LEAF case (module (i-a) done), `d := ρ − b ≥ a+1`.

### 2.1 The obstruction is REAL (the naive `chart4`-enlargement diverges)

The CoV atlas (incidence §3b): (1) `A_cor = D·[I_b|X]` (`dA = |det D|^d dD dX`), (2) charge
`det(Q̂_bQ̂_bᵀ)^{−a/2} = |det D|^{−a}·det(I+XXᵀ)^{−a/2}`, running weight `|det D|^{d−a}`; (3) pivot shear
`Q̂_p=[U|UX+W]`, `transverseSchurGram` ⟹ `E_tr ≍ ‖YW‖²`, `Y=(P;C)` (`M₀×u`); (4) front `B`-shear `H = PU+BD`
(`dB = |det D|^{−u} dH`), running weight **`|det D|^{d−a−u}`**; `H̃`-completion (measure-preserving).

Scope `d ≥ a+1` gives `d−a ≥ 1` but `d−a−u` can be `≤ −1` for `u ≥ 2` (borderline `d=a+1, u=2`: `d−a−u=−1`).
Applying `chart4_Htilde_fibre_lt_top` STANDALONE enlarges the `H̃`-image from the `D`-dependent parallelepiped
`R_D = PU + box·D` (volume `∝ |det D|^u`, SHRINKS as `D→0`) to all of `ℝ^{ub}`, leaving `|det D|^{d−a−u}`
whose `b×b` determinantal radial `∫|det D|^{d−a−u}dD` **DIVERGES** (`∫|det D|^β dD < ∞ ⟺ β > −1`; the raw
singular-value exponents `eᵢ = β + 2(i−1)`, binding at `i=1`: `β > −1` fails at `β = d−a−u ≤ −1`).
**Confirmed** numerically (`/tmp/dh_tube_check.py`: the `|det D|^{−1}` MC integral GROWS with sample size
393→437→659, a log divergence) and by Codex Q-A1 [FACT] (identical `eᵢ`, `β>−1` condition, borderline
`(e₁,e₂)=(−1,1)`).

**So `chart4` may NOT be applied standalone in the general scope.** This is the crux content — a real trap
(the covarch answer flagged it; a naive tide using `chart4_Htilde_fibre_lt_top` over `ℝ^{ub}` will thrash).

### 2.2 The resolution — the covariance handle (CLEANER than the tube), BOUNDED

Decorrelated Codex (Q-A2 FINITE, Q-A3 FINITE) confirms the integral is finite AND supplies a cleaner route
than a geometric tube. **Do not isolate `D`; keep the joint front map** `L_{P,D}(U,B) = PU + BD` (`u×b`). Its
Gram is a Kronecker sum:

    L Lᵀ  =  I_b ⊗ (P Pᵀ)  +  (Dᵀ D) ⊗ I_u,   eigenvalues  { pᵢ² + σⱼ² : i∈[u], j∈[b] },

`pᵢ = σ_i(P)`, `σⱼ = σ_j(D)`. The pushforward density of `(U,B) ↦ L` is bounded by `C·∏_{i,j}(pᵢ²+σⱼ²)^{−1/2}`,
so for `2q > ub`

    ∫_{U,B} (‖PU+BD‖² + τ²)^{−q}  ≲  τ^{ub−2q} · ∏_{i,j}(pᵢ²+σⱼ²)^{−1/2},   τ = ‖YW‖.

The `∏(pᵢ²+σⱼ²)^{−1/2}` factor is the honest joint weight: it **automatically interpolates** the two regimes
(`σⱼ ≲ τ` cancels the `|det D|^{−u}` → restores `|det D|^{d−a}` integrable; `σⱼ ≳ τ` the `pᵢ`/`σⱼ` provide the
decay), with NO enlargement. Codex's per-`k` singular-value split (`k = #{σⱼ ≤ τ}`) gives, at the borderline
`(d−a,u,b)=(1,2,2)`, the `τ`-orders `k=0: τ^{ub−2q}\log`, `k=1: τ^{ub−2q}`, `k=2: τ^{6−2q}` — worst order the
DESIRED `τ^{ub−2q}` up to one log. **The full `ub` codimension is recovered.**

> **Correction (Codex, honest):** my originally-sketched two-region argument ("on `‖D‖≳τ`, `|det D|` bounded
> below") is FALSE as stated — on `{‖D‖≳τ}` only ONE singular value need exceed `τ`; the split must be
> singular-value-wise (`k`), as above. Conclusion (FINITE) unchanged; the argument shape changes.

### 2.3 The gate closes it — `clsCodim_gate_genL` SUFFICES (for the front)

Codex verifies the joint rank-stratum exponent (over `s = rank Y`, `p = rank P`, `k = b − rank D`):

    T_{s,p,k} = C_{s} + (s−p)(u−p) + k(k + (d−a) − u + p)   ≥   min_r C_r   (a clean case split, Codex Q-A2).

So the strict gate `2q < min_r C_r` (which `clsCodim_gate_genL` delivers for general `L`, `min C_{ℓ,s} ≥
minAdm(M) − ab ≥ 2q`) makes EVERY joint front radial converge: `I_leaf < ∞`. **`clsCodim_gate_genL` is
sufficient for module (ii); no stronger front gate is needed.** [Confirmed: `clsCodim_gate_genL` in
`RouteMSJIncidenceAssembly.lean` L482 is sorry-free and general-`L`.]

### 2.4 Module (ii) exact Lean boundary

**Consumes:** `det_chartGram`, `transverseSchurGram`, `chartProjComplement` (all sorry-free),
`clsCodim_gate_genL`, the module-(iii) radial primitives.
**Genuinely-new content (bounded, well-scoped):**
- (a) The **covariance lemma** `(PU+BD)(PU+BD)ᵀ = I_b⊗PPᵀ + DᵀD⊗I_u` and its eigenvalues `pᵢ²+σⱼ²` — a clean
  Kronecker/`kroneckerₓ` identity + `Matrix.PosSemidef` eigenvalue algebra. **This is the recommended
  primitive to build for module (ii)** (replaces a fragile geometric-tube construction).
- (b) The pushforward-density bound `∫_{U,B}(‖PU+BD‖²+τ²)^{−q} ≲ τ^{ub−2q}∏(pᵢ²+σⱼ²)^{−1/2}` for `2q>ub`
  (and the `2q≤ub` box-cutoff variant, needed since `q < T1_q` can be `< ub/2` — chart4's `2q>ub` is NOT
  always in force). Feeds the `D`-radial with the CORRECT weight `∏(pᵢ²+σⱼ²)^{−1/2}` (no `|det D|^{−u}`).
- (c) The per-stratum exponent bookkeeping `T_{s,p,k} ≥ min_r C_r` (a `ring`+cases fact; Codex's split).

`chart4_Htilde_fibre_lt_top` and `chart5_bigcell_cov` remain USED (the `H̃`-fibre when `2q>ub` on the
`σⱼ≳τ` cells; the `W`/`Y` big-cell Schur CoV), but as INGREDIENTS inside the covariance-weighted resolution,
never standalone over `ℝ^{ub}`.

---

## 3. Module (iii): the radial blow-up `r^{C_{ℓ,s}−1}` (capstep3 — decomposition-agnostic)

Turns the joint normal blocks into radial variables so each stratum is `∫₀^δ r^{C_{ℓ,s}−1−2q}dr < ∞` (gate).
capstep3 is building this; the primitives are banked / in-progress on `genm-sj5-pradial`:
`corner_block_lintegral_lt_top` (single block `∫r^{N−1}(r²g)^{−c'} <⊤` for `c'<N/2`), `twoBlock_radial_le`
(`∫(κ²‖u‖²+σ²‖v‖²)^{−c'}`, the two-radial corner form), `radial_morse_residual_power_le`. **Design note:** the
radial family must accept the covariance weight `∏(pᵢ²+σⱼ²)^{−1/2}` of module (ii) as part of the per-cell
integrand (the `D`-block radii are `σⱼ`), not only the `‖YW‖`-block. This is the only coupling between (ii)
and (iii); otherwise (iii) is independent. **Not a wall.**

---

## 4. Module (i-b): THE DEEP-DEGENERATION — the general-`L` content (comparator/IH route)

This is the newly-isolated crux output. Modules (ii)+(iii) resolve the inner integral **per fixed generic
`z_tail`** (`rank Z = ρ`), yielding `∫_{z0,A_cor,x} frontChargeIntegrand(z_tail) ≤ K(z_tail)·(monomial in the
singular values of `S̃`)`. The OUTER `∫_{z_tail}` integrates this over the deep-parameter box, INCLUDING the
neighbourhood of `{rank Z < ρ}`. `K(z_tail)` blows up there — it carries the effective tail Jacobian
`≈ (det S̃ᵀS̃)^{−(u+b)/2}` (module (i)'s `(det G)^{−(u+b)/2}` on the `ρ`-space). This is the tail coupling.

### 4.1 The tail-rank-drop strata are REAL and NOT in the front `(ℓ,s)` atlas

Near `{rank Z = ρ−1}` (one deep singular value `σ_ρ(Z) = t → 0`), the leaf loss degenerates as (Codex Q-B3,
independently re-derived; I verified the local RLCT):

    loss  ≈  |y|²  +  t² · ‖W_lost‖²,   y = (H, W_surviving) ∈ ℝ^{ub + u(d−1)},  t ∈ ℝ^{κ},  W_lost ∈ ℝ^{u},

`κ = codim{rank Z = ρ−1}` in `z_tail` (`= 1` for a square bottleneck — the WORST case). The zero locus has TWO
components `{y=0,t=0}` (codim `ub+u(d−1)+κ`) and `{y=0,W_lost=0}` (codim `ub+u(d−1)+u`); RLCT `=
½(ub+u(d−1)+min(κ,u)) = ½(u(ρ−1)+κ) = ½(C_{s=u}(ρ) − u + κ)`. This is a **new stratum** — the deep-factor
degeneration lives in `z_tail`, orthogonal to the front `(ℓ,s) = (rank W, rank Y)` atlas of incidence §3.
**This is precisely incidencepp's §3 controller caveat (index-incompleteness, `genm-bltj`) and the operator's
`b<j` flag, here decorrelated-confirmed via a clean local model.**

### 4.2 The strata bind EXACTLY at `T1_q` — TIGHT, no wall (the decisive check)

The leaf gate over-counts: across arity-≥4 strict-shell cuts (width ≤6, `/tmp/gap_scan.py`, `/tmp/verify_strict.py`),
`gap := min C_{ℓ,s} − (minAdm(M)−ab) ≥ 0` always, but `gap > 0` for **65/476 (~14 %)** of GENUINE strict-shell
cuts (`1≤j<r`, `r≥2`; up to `gap = 4` for wide/deep chains). Where `gap > 0`, the true floor `minAdm−ab = 2T1_q`
is BELOW the leaf min, so the binding stratum is a deep-degeneration one. **These strata bind exactly at
`minAdm−ab`, never below** (FORCED: `minAdm(M)` is the paper's geometric codimension — the RLCT the capstone
targets — so nothing can undercut it; the tail-drop is the mechanism that realizes it).

**Canonical genuine-strict-shell example — `M=(4,4,4,4)`, `t★=2`, `r=2`, cut `u=3` (strict shell `j=1`),
`a=b=1`, `ρ=4`:** `minAdm=11`, so the leaf gate `min C_{ℓ,s}=11` would (falsely) suggest finiteness up to
`q<11/2=5.5`, but the TRUE bound is `T1_q=(minAdm−ab)/2=(11−1)/2=5`; the integral DIVERGES for `q∈(5,5.5)`
via the tail-drop, and the capstone needs only `q<5` (`c'<T1=5.5`). So finiteness holds in scope (BOUNDED),
but a leaf-chart-only proof would over-claim to `5.5`. Confirmed on the tightest probe:
- `M=(3,3,3,3)`, cut `(u=2,a=b=1,ρ=3)`: leaf `min C_{ℓ,s}=6`, but `minAdm=6`, `minAdm−ab=5`. Tail-drop-`1`
  codim `= C_{s=u}(ρ)−u+κ = 6−2+1 = 5 = minAdm−ab` (tight). Local model RLCT `= 5/2 = T1_q`: verified
  (`/tmp/local_model_conv.py`, `q=2.3` finite/stable, `q=2.7` divergent — onset at `2.5 = T1_q`).
- **Codex's "counterexample" `q=11/4` dissolves:** it lies in `(T1_q, ½·min C_{ℓ,s}) = (2.5, 3)`, i.e. ABOVE
  the true bound `T1_q = 2.5` (Codex conflated the leaf gate `min C_{ℓ,s}/2 = 3` with the actual constraint
  `c' < T1 ⟹ q < T1 − ab/2 = 2.5`). Its own tail-drop gate `q < 2.5` COINCIDES with `T1_q`. And `M=(3,3,3,3)`
  has `t★=2, r=1` ⟹ **no strict shell** (`1≤j<r` empty), so the front-charge route is never even invoked
  there (`/tmp/minadm_check.py`). So: **no in-scope counterexample; the divergence onset equals `T1_q`.**

### 4.3 The route: charge the deep degeneration through the comparator + outer IH

Because the tail-drop strata are outside the front atlas, they CANNOT be closed by the `(ℓ,s)` charts + a
finite cover of the front/`A_cor` variables. The `z_tail`-degeneration is charged by the **reduced comparator
`cornerComparator.integral(q)`** whose finiteness is the **outer IH** on `redChain u M` (arity `L`, threshold
`minAdm(redChain u M)/2`). The comparator's loss `commonDivisor²·frobSq(Q_p)`, `Q_p = z0·Z`, degenerates at
the SAME `{rank Z < ρ}`, so the domination must be **coupled/integrated** (incidence §Verdict-1 / §4), never
pointwise-uniform in `z_tail`:

    frontChargeIntegrand(z_tail, ·)  ≤  K_{j,c'} · cornerComparatorIntegrand(z_tail, ·)   (integrated over z),

with `K_{j,c'} < ⊤` per-exponent (`∼ 1/(T1−c')`), then `∫_{z_tail,…} cornerComparatorIntegrand < ⊤` by the IH
(`q < T1_q ≤ uM₂/2`, incidence §"exact lemma"). **This link (frontCharge ≤ K·comparator) is what the current
`shellSpine_le_frontCharge` does NOT yet have** — it lands on `∫ frontChargeIntegrand` standalone. Step 3's
honest closure needs it (or an equivalent explicit deep-degeneration resolution, which would re-derive the
recursion — the comparator route is cleaner).

### 4.4 Module (i-b) exact Lean boundary

**Consumes:** rankgen route (c) (`b ≤ deepTailMin ⟹ a.e. `rank(A_cor·Z) = b`, corank Gram PosDef) + the
`deepTailMin`-effective-dimension corank facts (rankgen §5), `cornerComparator.integral` finiteness (outer IH),
the `commonDivisor`/`genMonomial` ledger.
**Genuinely-new content:** the coupled domination `frontChargeIntegrand ≤ K·cornerComparatorIntegrand`
integrated over the deep factor — the `S̃`-degeneration of the front (modules ii,iii output) matched to the
comparator's `Q_p = z0·Z` degeneration. This is the "INTEGRATED, not pointwise, per-exponent `K`" of the
incidence cert, realized as the deep coupling. **This is the substantive general-`L` labour** (more than the
front charts). It is BOUNDED (the comparator is finite by IH; the tail-drop codim is `≥ minAdm−ab = 2T1_q`,
so the matched ratio converges for `q < T1_q`), but it is NOT the leaf-chart finite-cover the covarch answer
assumed.

---

## 5. BOUNDED-vs-WALL verdict (DELIVER item 3)

**BOUNDED — provable — but the route is the comparator/IH, not leaf-charts-alone.**

1. **The threshold `T1_q = (minAdm(M)−ab)/2` is exactly right for general `L`** — it is the geometric RLCT the
   capstone targets, and the front-charge integral converges for every `q < T1_q` (Codex Part A FINITE + the
   deep-degeneration strata binding tight at `T1_q`, §4.2). **No general-`L` wall.**
2. **incidencepp's exponent gate extends to general `L`** — `clsCodim_gate_genL` (sorry-free) proves
   `min C_{ℓ,s} ≥ minAdm−ab = 2T1_q` for general `L` (NOT arity-3/332-scoped: the 332-sweep was the numeric
   check; the Lean proof is the closed-form `ring` chain via `minAdm_le_peelCharge_add_redChain` +
   `minAdm_redChain_le_deepTailMin` + `deepTailMin_le_M2`). It SUFFICES for the FRONT (module ii, §2.3).
3. **The general-`L` completeness gap (the one real finding):** the leaf `(ℓ,s)` charts do NOT cover the
   deep-factor degeneration. For ~14 % of arity-≥4 strict-shell cuts the leaf gate strictly over-counts, and
   the true binding strata are the tail-drops (§4.1–4.2). A leaf-chart-only Step 3 either fails to close or
   over-claims to `½·min C_{ℓ,s} > T1_q` (false). **The deep degeneration must route through the comparator +
   outer IH** (§4.3). This is bounded multi-tide labour, not a wall — but it is a **route correction** the
   multi-tide build must adopt.
4. **Does incidencepp's terminal estimate extend to general `L` with the tail coupling (i)?** The FRONT part
   (the `C_{ℓ,s}` resolution) YES (module ii + gate). The estimate's `G ≤ K·comparator` closure requires the
   deep coupling (i-b), which incidencepp's cert scoped to the leaf/generic-`z` charts and its §3 caveat
   flagged as open. So: **the estimate extends, but only via the comparator/IH for the deep factor** — the
   incidence charts alone are the arity-3 (trivial-`Z`) shadow.

**Most likely to break the BUILD (not the math):** a tide that (a) uses `chart4_Htilde_fibre_lt_top` standalone
over `ℝ^{ub}` (false `|det D|^{d−a−u}` divergence, §2.1); (b) claims Step 3 finiteness from the `(ℓ,s)`
finite-cover alone (misses the tail-drop strata — provably incomplete for the `gap>0` cuts); (c) states an
endpoint-uniform `K` (must be per-exponent `∼1/(T1−c')`); or (d) works at the leaf dimension `M₂` instead of
`ρ = deepTailMin` (module (i-a), the covarch trap for `ρ < M₂`).

---

## 6. Module (i) tail-coupling effective dimension (DELIVER item 4)

The `(det G)^{−(u+b)/2}` Jacobian (covarch Q1) is, correctly, on the **effective `ρ = deepTailMin` row space**,
NOT `M₂` (module (i-a): the leaf variables are `z0·S̃, A_cor·S̃`, and `G_eff = S̃ᵀS̃ = ` the `ρ×ρ` Gram of the
rank factor). Its integrability near `{rank Z < ρ}`:
- **Is it the SAME `deepTailMin` fact rankgen banked?** Partly. rankgen banks `b ≤ deepTailMin` (so the corank
  Gram is PosDef a.e. — the charge is DEFINED) and the effective-dimension re-scoping (§5: corank
  survival/weight on the `deepTailMin`-space, not `M₂`). Module (i-a)'s reduction USES exactly that: the
  charge `det(Q̂_bQ̂_bᵀ)^{−a/2}` on the `ρ`-space is finite in `A_cor` iff `a+b ≤ ρ` (Wishart), which rankgen's
  `a+b ≤ deepTailMin−1` delivers strictly.
- **What is ADDITIONAL:** the `(det G_eff)^{−(u+b)/2}` INTEGRABILITY over `z_tail` near the rank-drop — the
  deep-factor degeneration itself (module (i-b), §4). rankgen's facts make the charge well-defined a.e.; the
  `z_tail`-integrability of the blown-up `K(z_tail)` is the coupled-domination-to-comparator (§4.3), which
  rankgen did NOT bank (it explicitly left the a.e. lift + the comparator coupling to the build). So:
  **`b ≤ deepTailMin` and the effective dimension are rankgen's; the tail Jacobian's `z_tail`-integrability is
  additional (module i-b, comparator/IH).**

Concretely, on the tail cell `{G_eff ⪰ εI}` (the good set) `K(z_tail)` is a bounded unit and the leaf charts
apply directly; OFF it (`{rank Z → ρ−1}`) the `(det G_eff)^{−(u+b)/2}` blow-up is matched by the comparator's
`Q_p`-degeneration — the tail-drop strata of §4.

---

## 7. Decorrelated Codex (conclusion WITHHELD; prompt "argue whichever way")

`codex/crux-{prompt,answer,run.log}` (gpt-5.6, xhigh). Independent; it CONTRIBUTED two things and mis-scoped
one (which I caught and reconciled):
- **CONTRIBUTED [FACT]** the crux-(ii) resolution is FINITE and the **cleanest primitive** is the covariance
  `L Lᵀ = I⊗PPᵀ + DᵀD⊗I`, density `∏(pᵢ²+σⱼ²)^{−1/2}`, and the exact rank-stratum bound `T_{s,p,k} ≥ min C_r`
  (§2.2–2.3). Also caught that my two-region argument was false as stated (§2.2 correction).
- **CONTRIBUTED [FACT]** the deep-factor tail-rank-drop is a REAL new stratum (local model `|y|²+t²‖W_lost‖²`,
  codim `C_{s=u}(ρ)−u+κ`), independently confirming incidencepp's index-incompleteness caveat (§4.1).
- **MIS-SCOPED (reconciled):** Codex called this a general-`L` WALL with counterexample `q=11/4` for
  `M=(3,3,3,3)`. It conflated the leaf gate `min C_{ℓ,s}/2 = 3` with the actual constraint `q < T1_q = 2.5`;
  `q=11/4` is out of scope, and `M=(3,3,3,3)` has no strict shell (§4.2). Its OWN tail-drop gate `q<2.5`
  EQUALS `T1_q` — confirming BOUNDED (tail-drop tight, no undercut), not a wall. The genuine content of its
  finding is the completeness gap (§4.3), not a wall.

---

## Close

- **Firmest result.** Step 3 (`frontChargeIntegral < ⊤` for `q < T1_q`) is **BOUNDED / provable for general
  `L`**, threshold `T1_q = (minAdm(M)−ab)/2` exactly right. Decomposition: **(i-a)** exact `ρ=deepTailMin` leaf
  reduction (VERIFIED); **(ii)** the `D–H` covariance resolution (BOUNDED, `clsCodim_gate_genL` suffices for
  the front, Codex-confirmed, cleaner than the geometric tube); **(iii)** radial blow-up (capstep3);
  **(i-b)** the deep-factor degeneration, charged via the comparator + outer IH.
- **The decorrelated-confirmed correction (surface to controller).** The banked leaf `(ℓ,s)` charts are
  **incomplete for general `L`** — they miss the tail-rank-drop strata (14 % of arity-≥4 strict-shell cuts,
  where `min C_{ℓ,s} > minAdm−ab`). These bind EXACTLY at `T1_q` (tight, no wall) but are outside the front
  atlas; Step 3 must route the deep factor through the comparator/IH. This upgrades incidencepp's §3 caveat
  from "flagged" to "confirmed + the route fix identified."
- **Most likely to break the BUILD.** Standalone `chart4` (§2.1 divergence); leaf-cover-only Step 3 (§4.3
  incompleteness); endpoint-uniform `K`; leaf dimension `M₂` instead of `ρ`.
- **Next construction/consult that would settle the open part.** (1) Build the module-(ii) covariance lemma
  `(PU+BD)(PU+BD)ᵀ = I⊗PPᵀ+DᵀD⊗I` + density bound (the clean primitive) — a small self-contained tide,
  de-risks the crux. (2) The module-(i-b) coupled domination `frontChargeIntegrand ≤ K·cornerComparator`
  (integrated over `z_tail`) — the substantive general-`L` link; a decorrelated consult on whether the
  matched ratio `K ∼ 1/(T1−c')` is uniform over the deep-degeneration would fully close it. (3) `hbind`
  discharge of `b ≤ deepTailMin` at the `t★` call site (rankgen route b′) — orthogonal, already scoped.
