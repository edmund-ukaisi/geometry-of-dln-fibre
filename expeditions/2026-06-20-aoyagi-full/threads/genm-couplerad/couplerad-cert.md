# genm-couplerad — a Lean-friendly monomial resolution for the coupled per-cell finiteness (the ONE substantive analytic build of (□) at arity ≥ 4)

**Seat:** pen-and-paper (design-space, DESIGN-primary — the constructive native realization; the TRUTH is
settled and NOT re-adjudicated). aoyagi-full Stage 2/3a, `genm-couplerad`. **Date:** 2026-07-16. **NO Lean
edits, NO build.** Exact-rational vertex LP + exact `ℕ` `minAdm`/`CR` recursions (`fractions.Fraction`),
decorrelated reimplementation of the deephier LP (my scripts share none of deephier's code — they share only
the standard `minAdm` recursion). MC not used. Decorrelated `local-codex-consult` fired (`codex/couplerad-{prompt,answer}.md`).

**Consumed / verified (signatures, not paraphrased):**
- `genm-deephier/deephier-cert.md` @`origin/worktree-agent-a9fa628dc1a919710` — the settled TRUTH: honest
  per-cell coupled RLCT-codim `≥ minAdm((u,)+deep) ≥ 2T1q`; the SVD ray LP (§2), the Vandermonde measure
  `∏_{i<j}|σᵢ²−σⱼ²|·∏σᵢ^{p−k}dσ`, the closed form `C_k^{hier,loss} = u(ρ−k)+Σᵢmin(βᵢ,u)`, `βᵢ=(p−k+1)+2(k−i)`,
  the charge ray-exponent `γ^{hier}(e)=max_h[a(e₁+..+e_h)−h(s−b+h)]`, and ★4 (charge inert).
- `RouteMSJDeepCoverage.lean` (`origin/genm-arch1build`) — the hfin interface: `deepRankLE_lintegral_lt_top`
  glues per-cell finiteness `hfin : ∀ i : CRIndex H, ∫⁻ A in deepCell … i, f A < ⊤` over the CR-path cover
  (`deepCover_aux`, set-equality, banked sorry-free); terminal cell `deepCell … 0 … Q = {A | (Q A).rank ≤ s}`.
- `RouteMSJIncidenceAssembly.lean` `frontChargeIntegrand` (`origin/genm-arch1build`) — the actual coupled+charged
  `f`: `det(Q_bQ_bᵀ)^{−a/2}·Cresid(ab)c'·(E_top+E_tr)^{−(c'−ab/2)}`, `Q_eff = Q_top + P⁻¹·B·Q_bot`,
  `Q_b = A_cor·Z_deep`, `E_tr` = the transverse-projected part `(1 − Q_botᵀ(Q_botQ_botᵀ)⁻¹Q_bot)`.
- `RadialResidualPower.lean` `radial_morse_residual_power_le` (banked, S2-free, axiom-clean): the additivity
  atom `∫_{[−T,T]^{m+1}}(ΣᵢPᵢ²+w)^{−c'} ≤ Cresid(m+1)c'·w^{−(c'−(m+1)/2)}` for `c'>(m+1)/2`, `w>0`.
- `MatMulFibre.lean` `fibre_lintegral_mul_le` (banked, S2-free): `∫_X frobSq(X·Y)^{−c'} ≤ C·frobSq(Y)^{−c'}`
  for `c' < p/2` (X is `p×n`), EXPONENT-PRESERVING, `Y`-black-box (one column).
- `RouteMSchurGeneral.lean` `SchurCore`/`SchurRecStep`/`core_schurGen_lt_top`; `RouteMBoxThresholdRRP.lean`
  `routeMBoxThresholdFinite_rrp` — the square-first-factor corank recursion `∫∫ frobSq(Δ·S)^{−c'}`
  (Δ `r×r` SQUARE, S `r×p`), reaching `c'<½minAdm(r,r,p)`; CLOSED sorry-free axiom-clean for the `(r,r,p)` family.
- `RouteM4422Hfin.lean` (arity-4 `(4,4,2,2)` closed via iterated fibre); `iterfibre-route-cert.md`,
  `r1upper-wall-review.md` — the iterated-fibre peel is EXPONENT-PRESERVING and UNDERSHOOTS `½minAdm` by a
  factor of 2 on corank-≥2 binding cores (the `(3,3,3,3)` wall) — it does NOT see the residual's rank; the
  rank-stratified resolution is what reaches the floor.
- `lean/CLAUDE.md` traps — the D-C spectral friction (`IsHermitian.eigenvalues`/`eigenvectorUnitary` whnf
  timeouts; abstract-`Aux`-over-abstract-eigen), the `Matrix.module` diamond → raw-pi CoV, `real_inner_smul_right`,
  the EuclideanSpace/finrank friction.

Scripts (this thread, `scripts/`): `couplerad_resolution.py` (the coupled-codim LP + atom decomposition +
charge + nested-peel accounting + every-chart-≥-floor, on the witnesses), `couplerad_leanmech.py`
(the SVD-free raw-bilinear reachability: atom-sum = `minAdm(u,p,k)`, deepest-cell = floor, square vs non-square).

---

## ★ VERDICT — a covering native monomial resolution reaching the floor EXISTS; it is a CONSTRUCTION, not a native wall. KILL-condition NOT triggered.

**The honest per-cell coupled RLCT-codim is `≥ minAdm((u,)+deep) = minAdm(redChain u M) ≥ 2T1q` and this is
realized by an EXPLICIT covering monomial resolution whose every chart has radial exponent `≥ floor`, with
the Jacobian (Vandermonde + `σ^{p−k}` measure + every CoV determinant) carried at every step, and the charge
`det(Q_bQ_bᵀ)^{−a/2}` dominated.** No stratum's honest exponent falls below the floor (0 cases, exact LP over
the witnesses + scan). **The `rlct = ½·codim` equality (`cited_aoyagi_dln`) is NOT needed** — only the native
codim LOWER bound is used (elementary `∫r^{c−1−2q}dr<∞` per chart), so the axiom footprint is NATIVE.

**★1 — Two atlases; the honest one is Lean-hostile, so the design is the Lean-friendly re-realization.**
- **The SVD singular-value ray atlas (GROUND TRUTH).** Diagonalize the reduced deep factor's normal slice
  by SVD, exposing `σ₁≥…≥σ_k`; the coupled loss becomes `|y|² + Σᵢσᵢ²|Wᵢ|²` (a SUM in disjoint variable
  groups), the measure is `∏|σᵢ²−σⱼ²|·∏σᵢ^{p−k}dσ`, and the toric charts of the Newton fan give per-chart
  exponents whose MINIMUM is `C_k^{hier}` (the LP value). **This atlas is COMPLETE and every chart `≥ floor`
  (verified exactly).** But SVD invokes `IsHermitian.eigenvalues`/`eigenvectorUnitary` — the documented D-C
  whnf/isDefEq-timeout minefield. **Do NOT build the resolution as an SVD.**
- **The raw-coordinate pivot/Schur + fibre + residual-power atlas (LEAN-FRIENDLY, the recommendation).**
  Realize the SAME floor WITHOUT producing individual `σᵢ`: resolve the reduced deep factor's rank flag by
  a raw pivot/Schur corank recursion, peel the front weights by the bilinear fibre atom, and peel the
  surviving block by the residual-power atom. Stays in raw entries / raw-pi. §2.

**★2 — The coupled codim is ADDITIVE over disjoint variable groups; each group is a BANKED-atom peel.**
`(|y|² + Σᵢσᵢ²|Wᵢ|²)^{−q}` with disjoint groups `(y),(σ₁,W₁),…,(σ_k,W_k)` has codim `= u(ρ−k) + Σᵢmin(βᵢ,u)`,
realized by the residual-power peel (each peel removes a group, shifts `q → q − ½·codim(group)`, leaves a
residual power of the rest). The half-codims sum to `C_k/2` **exactly** and the descent stays feasible across
the full `0<2q<C_k` range (peel groups with `½codim<q` by residual-power, crude-dominate by one leaf with
`½codim≥q`) — the pattern already banked in `RouteM334Hfin.core_T_peel_le`. (verified `couplerad_resolution.py`)

**★3 — The lost-block resolution IS a `minAdm` recursion (SVD-free).** The coupled atom-sum has a closed
form `Σᵢmin(βᵢ,u) = minAdm(u, p, k)` (p=k+exc) — verified equal for EVERY stratum k on all witnesses. So the
lost k-block, coupled to the u front rows, is resolved by the SAME QIP/`minAdm` corank recursion the paper
already carries — a raw pivot/Schur split of a bilinear `frobSq(W·E)`, NOT a spectral decomposition. The
deepest cell (k=ρ) reaches exactly `minAdm(u,M₂,n) = floor` (arity-4; 0 mismatches over 351 cuts).

**★4 — The charge is dominated and single-layer; it needs no SVD and no 2-deep-layer composite LP.** With
the charge exponent `γ^{hier}(e)` subtracted from every ray, the LP minimum is UNCHANGED (`C_k^{hier}(charge)
= C_k^{hier}(loss-only)`, 0 cases below floor, all witnesses) — the charge exponent is dominated at the
binding ray. Structurally `det(Q_bQ_bᵀ)^{−a/2}` reads only `Q_b = A_cor·Z_deep`'s `b×b` Gram (a SINGLE
corank matrix `A_cor` against the deep product `Z_deep`), so it is single-layer in `A_cor`; the multi-layer
deep product enters only through `Z_deep`'s rank, which the CR-path cover handles. The charge is carried
through the raw Schur complement as a positive determinantal weight and never forces a spectral treatment.

**★5 — The load-bearing constructive content (NOT a native wall): the general NON-SQUARE bilinear corank
recursion (the rank-stratified `{V=0}` resolution).** After the front fibre-peel + surviving residual-power
peel, the binding (deepest) cell reduces to the reduced bilinear `frobSq(Front·Z_deep)^{−q'}·det(Q_bQ_bᵀ)^{−a/2}`
= the arity-3 (3-width) RRR-with-charge for the sub-chain `(u, M₂, n)`, whose floor `minAdm(u,M₂,n) =
minAdm((u,)+deep)` must be reached exactly (no slack at the binding cell). **This is reachable by the banked
`(r,r,p)` `SchurCore` ONLY when the first factor is SQUARE (`u=M₂` and `M₂=n`)** — e.g. `(4,4,4,4)`,
`(5,5,5,5)`, `(3,3,4,4)`. When `exc>0` (`M₂≠n`) or `u≠M₂` the reduced bilinear is NON-square, and I verified
(`couplerad_reducedreach.py`) that **NEITHER the exponent-preserving fibre-peel NOR the banked square
`SchurCore` reaches the floor** (630 arity-4 cuts, INCLUDING the dispatch witness `(3,4,5,4)`: reduced chain
`(2,5,4)`, floor 8, fibre reach 4, square-SchurCore N/A — the same factor-of-2 undershoot as the `(3,3,3,3)`
wall). So the general **non-square corank recursion** (the rank-stratified `{V=0}` resolution — the genuine
Aoyagi blow-up along the full rank flag, feasibility-validated S2-only in `iterfibre-route-cert.md` §4 /
thread-27) is the load-bearing new build for these cuts. **This is NOT a native wall** — the SVD ground-truth
proves every chart `≥ floor`, and the SVD atlas is an always-available (Lean-costly) fallback; the non-square
corank recursion is the Lean-friendly realization, bounded but substantive (more than one lemma).

---

## 1. The objects and the target

At a binding cut `u = t★+j` (`1≤j<r`): `a = M₀−u`, `b = M₁−u` (rankgen `a+b ≤ ρ−1`), `ρ = deepTailMin M =
min(M₂,…,M_last)`, `n = M_last`, `exc = |M₂−n|`. The deep product `Z_deep` is `M₂×n`, generic rank `ρ`.

**The CR-path cover (banked, `RouteMSJDeepCoverage.deepCover_aux`)** partitions `{rank(prod) ≤ s}` into cells
indexed by `CRIndex = CRPath` (a rank + pivot choice at each deep layer). Each descent node cuts to a pivot
chart `{IsUnit((effLayer·Q).submatrix ρ κ) ∧ rank ≤ r}` and reduces `Q → Q' = (effLayer·Q).submatrix id κ ·
((effLayer·Q).submatrix ρ κ)⁻¹`; the **terminal cell** is `{A | (Q A).rank ≤ s}`, `s = ρ−k`. This is
FLOOR-AGNOSTIC and set-equality-complete — the cross-layer hierarchical corners (deephier ★5) are separated
here; the floor lives entirely in the per-cell `hfin`.

**The target (per-cell, the coupled loss·charge — `frontChargeIntegrand` on the terminal cell):**
```
∀ i : CRIndex,  ∫_{terminal cell i}  det(Q_bQ_bᵀ)^{−a/2}  ·  (E_top + E_tr)^{−q}  ·  dμ   <  ⊤     for q < T1q,
```
via **per-cell RLCT-codim `≥ minAdm(redChain u M) = minAdm((u,)+deep) ≥ minAdm(M)−ab = 2T1q`** (the last
`≥` is the banked `ℕ` `t=u` term `minAdm_le_peelCharge_add_redChain`). Here `E_top+E_tr ≍ frobSq(Front·Q_eff)`
is the front↔deep COUPLED biquadratic (`Q_eff = Q_top + P⁻¹·B·Q_bot`, `P` the front pivot), `q = c'−ab/2`.

---

## 2. The explicit resolution atlas (charts + change-of-variables + Jacobian carried)

Three levels. Level 0 is banked (cross-layer); Levels 1–2 are the design (within a terminal cell).

### 2.0  Cross-layer (BANKED) — the CR-path cover
`deepCover_aux` reduces the multi-layer `{rank(deep product) ≤ ρ−k}` to a single reduced factor `Q` with
`{rank Q ≤ s}`, `s = ρ−k`, pinning per-layer ranks by pivot charts. NO rework; floor-agnostic. All Jacobians
here are pivot-submatrix inverses already handled in the banked descent.

### 2.1  Within-cell Stage A — the surviving/lost pivot split (raw coordinates)
On the chart where an `s×s` minor `P` of the reduced factor `Q` is invertible (index the charts by the
`⟨rows σ, cols κ⟩` pivot choice; these EXHAUST `{rank Q = s}` — the `exists_nonsingular_submatrix_of_le_rank`
leaf, already used in `deepCover_aux`), Schur-split
```
Q = [[P, B],[C, D]]  →  (P, B, C, E),   E := D − C·P⁻¹·B   (the p×k normal slice, p = k+exc).
```
- **Jacobian:** the map `D ↦ E` at fixed `(P,B,C)` is a TRANSLATION — Jacobian `1` (measure-preserving; no
  `det P` from this step). The rank identity `rank Q = s + rank E` turns the constraint `{rank Q ≤ s}` into
  `{E = 0}` on this chart — the lost block is `E`.
- **Front split:** the front weights `Front` (u rows) split under the same pivot into `Front_surv` (hitting
  the `s` surviving directions, order-1) and `Front_lost` (hitting `E`). The pivot `P` (bounded away from `0`
  on the chart, `|det P| ≥ δ`) gives the bounded comparability `c₁|Front_surv|² ≤ (surviving loss) ≤
  c₂|Front_surv|²` — a **Morse block** in `y := Front_surv ∈ ℝ^{u·s} = ℝ^{u(ρ−k)}` up to bounded factors.

### 2.2  Within-cell Stage B — the additive peel of the coupled loss
The loss is `frobSq(Front·Q_eff) = |y|²·(1+O) + frobSq(Front_lost·E) + …` — the disjoint-group sum
`|y|² ⊕ frobSq(Front_lost·E)` (up to bounded comparability). Peel in two moves, carrying the Jacobian:

- **Move 1 — the surviving `y`-Morse peel (BANKED atom A).** `∫_{y∈ℝ^{u(ρ−k)}} (|y|² + core)^{−q} dy ≤
  Cresid(u(ρ−k))q · core^{−(q − u(ρ−k)/2)}` for `q > u(ρ−k)/2` — `radial_morse_residual_power_le`. Removes
  codim `u(ρ−k)`, shifts `q → q − u(ρ−k)/2`, leaves a residual power of the lost-block core. (For `q ≤
  u(ρ−k)/2` crude-dominate by the core — finite since then `q < ½·(lost-block codim)`.)

- **Move 2 — the lost-block bilinear corank recursion (the NEW content; ★3, ★5).** The core is
  `frobSq(Front_lost·E)^{−q'}·det(Q_bQ_bᵀ)^{−a/2}` (`q' = q − u(ρ−k)/2`), a bilinear `W·E` with `W = Front_lost`
  `u×k`, `E` `p×k`, charge on `E`'s bottom block. Its codim is `Σᵢmin(βᵢ,u) = minAdm(u,p,k)` (★3, verified),
  and the resolution is the QIP/`minAdm` corank recursion of the reduced sub-chain `(u, p, k)`:
  - pivot/Schur split of `E`'s rank flag (raw entries, as Stage A, one corank at a time),
  - fibre-peel the front `W` against the current corank block (BANKED atom B, `fibre_lintegral_mul_le`,
    threshold = the current row-count / 2),
  - shifted-exponent Morse peel of the freed block (BANKED atom A),
  - recurse on the reduced corank (the `SchurRecStep` skeleton `core_schurGen_lt_top`, BANKED wrapper).
  **Where it bites (★5):** this recursion is BANKED only for the SQUARE-first-factor `(r,r,p)` family
  (`routeMBoxThresholdFinite_rrp`). When `exc > 0` or `u ≠ M₂` (non-square) it needs the general non-square
  corank recursion — a fibre-peel-to-square does NOT rescue it (refuted, §3): 630 arity-4 cuts reach the
  floor by NEITHER fibre-peel NOR square-`SchurCore` (incl. `(3,4,5,4)`). This is buildable detail-at-scale
  (the rank-stratified `{V=0}` resolution, feasibility-validated), not a monument and not a native wall.

### 2.3  The charge and the Jacobian — carried, never dropped (the tide-D KILL guard)
- **Vandermonde + measure (SVD form).** In the ground-truth SVD atlas the measure is `∏_{i<j}|σᵢ²−σⱼ²| ·
  ∏σᵢ^{p−k}dσ`; on the ordered ray it is the exact monomial `∏σᵢ^{βᵢ−1}` (`βᵢ = (p−k+1)+2(k−i)`) — this IS
  the codim-lowering factor that makes `C_k^{hier} < C_k^{single}`. In the raw atlas this measure factor is
  the Schur-complement Jacobian of the corank recursion (already in the `SchurRecStep` accounting). **Dropping
  it (radialize-and-drop) would spuriously raise the exponent and is the ONLY way native finiteness fails —
  it is a formalization slip, not a DLN phenomenon.**
- **Charge.** `det(Q_bQ_bᵀ)^{−a/2}` is carried as a positive weight through the raw Schur complement of the
  bottom block; its ray exponent `γ^{hier}(e)` is DOMINATED at every optimum (★4, exact). It reads only the
  `b×b` Gram of `Q_b = A_cor·Z_deep` (single-layer in `A_cor`) — clean, no 2-deep-layer composite LP.
- **CoV Jacobians.** Stage-A `D↦E` translation (Jac 1); the front pivot `P` comparability (bounded, `|det P|≥δ`);
  the fibre/residual-power atoms carry their own `Cresid`/`fibreConst` constants (finite below threshold). Every
  determinant is finite and bounded on its chart; none is dropped.

---

## 3. Per-chart exponent verification (≥ floor), on the witnesses (`couplerad_resolution.py`, exact)

For each cell `k`, the honest per-chart radial exponent = the LP ray value; the **minimum over all charts**
(the LP optimum) is `C_k^{hier}`, and `min_k C_k^{hier} = floor`. So EVERY chart of EVERY cell has exponent
`≥ floor`. Charge included; charge inert everywhere.

| witness | u (a,b) | floor = minAdm((u,)+deep) | 2T1q | per-cell `C_k^{hier}` (k=1..ρ, charge) | min_k = floor? | every chart ≥ floor? |
|---|---|---|---|---|---|---|
| **(4,4,4,4)** | 3 (1,1) | **10** | 10 | 10,10,10,10 | ✓ | ✓ |
| **(3,4,5,4)** | 2 (1,2) | **8** | 8 | 8,8,8,8 | ✓ | ✓ |
| **(5,5,5,5)** unif | 4 (1,1) | **16** | 16 | 17,16,16,16,16 | ✓ | ✓ |
| (3,3,4,4) | 2 (1,1) | 7 | 7 | 7,7,7,7 | ✓ | ✓ |
| (4,5,6,5) exc>0 | 3 (1,2) | 14 | 14 | 14,14,14,14,14 | ✓ | ✓ |

`(4,4,4,4)@u=3`, deepest cell k=4 (`s=0`, `β=[7,5,3,1]`): `Σmin(βᵢ,3)=3+3+3+1=10`, `u(ρ−k)=0` ⟹ `C_4=10=floor`
(matches dispatch "coupled=10=floor"). Atom-decomposition `C_k^{hier} = u(ρ−k)+Σᵢmin(βᵢ,u)` matches the LP
for every k (closed form == loss-only LP, all witnesses); nested-peel half-codims sum to `C_k/2` exactly;
every cut has `floor ≥ 2T1q` (tight, margin 0).

**The SVD-free reachability (`couplerad_reducedreach.py`).** The deepest cell's reduced bilinear is the
3-width `(u, M₂, n)` RRR (floor `minAdm(u,M₂,n) = minAdm((u,)+deep)`, arity-4, 0 mismatches). It is reached
by the banked square `SchurCore` iff `u=M₂` **and** `M₂=n` (e.g. `(4,4,4,4)`,`(5,5,5,5)`,`(3,3,4,4)`).
Otherwise (630/… arity-4 cuts, incl. `(3,4,5,4)`→`(2,5,4)`) the floor is reached by NEITHER the
exponent-preserving fibre-peel (undershoots by ~×2 — the `(3,3,3,3)`-wall mechanism) NOR the square
`SchurCore` — so the general non-square corank recursion is required there (★5).

**Why single-scale over-shoots (do not use it).** `deepGate_branch`'s `C_k^{single} = min(uρ, u(ρ−k)+κ_k−γ)`
is the SEPARABLE sum; it is `≥ C_k^{hier}` (STRICT at deep strata — `(4,4,4,4)@u=3`: `k=3,4` give
`C_single=12` but `C_hier=10`). "true codim `≥ C_single`" is the WRONG direction. The sound per-cell floor is
`minAdm((u,)+deep)`, reached by the coupled resolution above.

---

## 4. The Lean-mechanism map (feasibility — banked / new / trap-avoidance)

*I hold no Mathlib-feasibility model and prescribe no proof route; below is which banked pieces the math
consumes and where the genuine new content sits, for the controller to synthesize.*

**Banked pieces to consume:**
- Cross-layer cover: `deepRankLE_lintegral_lt_top` + `deepCover_aux` (the CR-path atlas, floor-agnostic; the
  per-cell `hfin` is exactly this build's obligation).
- Additivity: `radial_morse_residual_power_le` (S2-free, axiom-clean) — Move 1 and the shifted-exponent Morse
  peels inside Move 2. The pattern `core_T_peel_le`(`_ae`) shows the `w := core(z)` composition under the
  outer integral.
- Bilinear front peel: `fibre_lintegral_mul_le` (S2-free) — the `W`-fibre in Move 2.
- Corank recursion skeleton: `core_schurGen_lt_top` (the WellFounded-on-corank wrapper, sorry-free) +
  `routeMBoxThresholdFinite_rrp` (the CLOSED `(r,r,p)` square instance). The reduced lost-block bilinear
  plugs into `SchurCore` when square.
- The `ℕ` `t=u` term: `minAdm_le_peelCharge_add_redChain` (banked); the codim value `minAdm((u,)+deep) =
  cCodim` via `codimRepCanonical_productRankLocusLE_eq_minAdmRec` at the dimension vector `redChain u M`
  (NOT `κ_k = cCodim(deep, ρ−k)` — a DIFFERENT object; deephier §7 Q1b).

**New lemmas needed (the genuine content):**
1. **The Stage-A within-cell pivot split of the reduced factor + the front comparability** — the raw
   Schur-complement CoV isolating the lost block `E` and the surviving `y`-Morse, carrying the charge weight
   (Jac-1 translation `D↦E`; the `|det P|≥δ` comparability on the chart).
2. **The general (NON-SQUARE) bilinear corank recursion** — the `SchurRecStep`-analog for the rectangular
   `frobSq(Front·Z_deep)` = the 3-width `(u, M₂, n)` RRR (the rank-stratified `{V=0}` resolution). Needed for
   `exc>0` or `u≠M₂` (630 arity-4 cuts, incl. `(3,4,5,4)`); a fibre-peel-to-square does NOT reach the floor
   there (§3, refuted). This is the load-bearing new build — detail-at-scale, feasibility-validated
   (`iterfibre-route-cert.md` §4), not a monument.
3. **The charge carried through the raw corank recursion** — that `det(Q_bQ_bᵀ)^{−a/2}` stays dominated
   through Move 2 (the `γ^{hier}` domination, ★4; single-layer in `A_cor`).

**Trap-avoidance (from `lean/CLAUDE.md`):**
- **Do NOT SVD the reduced factor.** The ground-truth resolution is an SVD, but building it as one invokes
  `IsHermitian.eigenvalues`/`eigenvectorUnitary` → the D-C whnf/isDefEq timeouts. Use the RAW pivot/Schur
  corank recursion (Stage A + Move 2) — it reaches the SAME floor (★3). If any spectral term is unavoidable
  in a comparability, factor it as a bound argument (the abstract-`Aux`-over-abstract-eigen pattern) and use
  `real_inner_smul_right` for any Rayleigh step; never let `λᵢ•bᵢ` sit as a bare vector `smul` a later step
  must defeq-close.
- **Matrix-space CoV → raw-pi.** Any measure CoV on the front/reduced-factor matrix (Stage A, the fibre peel)
  hits the `Matrix.module` vs `NormedSpace.toModule` diamond — transcribe over the RAW pi type `Fin c → Fin t
  → ℝ`, column-indexed (as `RouteMSJDecoratedPeelMeas.mulLeftₚ` / the `eParams4422` reshape do).
- **`⅟` → `⁻¹` inside `∫⁻`.** Any banked `[Invertible]`-stated pivot identity used pointwise a.e. must be
  converted `invOf_eq_nonsing_inv` first (the `P⁻¹` form is integrand-usable).
- **EuclideanSpace finrank.** The residual-power atom lives on `EuclideanSpace ℝ (Fin n)`; do not annotate
  `Module.finrank` explicitly (instance-synthesis failure) — take `Submodule.finrank_le` with RHS inferred
  and rewrite via `WithLp.linearEquiv`.

**SVD / Vandermonde Mathlib support (`scripts/lean-search` / rg over mathlib, at v4.29):** there is NO
off-the-shelf matrix SVD, no singular-value measure, no Vandermonde-of-eigenvalues Jacobian at this pin (the
`FibreNormalForm` note already flags "no rank-normal-form / equal-rank⟹equivalent-matrices"). Building the
SVD atlas would mean building all of that — a strong reason to take the raw-coordinate route, where the
"Vandermonde × `σ^{p−k}`" measure is REPLACED by the raw Schur-complement Jacobian of the corank recursion
(already in the `SchurRecStep` accounting), needing no spectral Mathlib support.

---

## 5. Decorrelated Codex

Fired `local-codex-consult` (gpt-5.x, `xhigh`, read-only), my conclusion WITHHELD (prompt gives the objects +
the 4 sub-questions + the banked atoms, asks it to "reason it out and DECIDE"; `codex/couplerad-{prompt,answer}.md`).
[ANSWER pending at write time — fold the verdict in when it lands; the exact-algebra certificate above is
self-standing (the LP + closed form + atom-sum = minAdm are exact rational, not model-dependent).]

---

## 6. Scoped conditions (where each ingredient bites)

- **Rankgen scope `a+b ≤ ρ−1`** (strict binding shells): keeps the charge non-integrable wall `a+b ≥ ρ+1`
  outside; `k=1` charge-inert.
- **The floor is `minAdm((u,)+deep) = minAdm(redChain u M)`** — the RRR codim of the SUB-CHAIN with the
  front cut-width `u` prepended, NOT `minAdm(deep)` and NOT the deep-measure `κ_k = cCodim(deep,ρ−k)`.
- **Tightness.** `floor = 2T1q` (margin 0) at every in-scope strict-shell cut on the witnesses — the gate is
  TIGHT, not slack. The honest binding stratum is the deepest cell (`k=ρ`, `s=0`), at exactly the floor.
- **Square vs non-square (★5).** The banked `SchurCore` covers the square-first-factor reduced bilinear
  (`u=M₂` and `M₂=n`); the non-square case (`exc>0` or `u≠M₂`; 630 arity-4 cuts, reached by neither fibre
  nor square-`SchurCore`) needs the general non-square corank recursion.
- **Arity.** For arity-4 (single deep matrix) the deepest cell is the 3-chain `(u,M₂,n)`; for arity≥5 the
  deep sub-chain is longer and resolved layer-by-layer by the CR-path (Level 0), with the terminal single-matrix
  coupling handled by Stages A/B.

---

## 7. Levels kept apart

- **Quiver/orbit & codim `(C,θ)`:** consumed only via `minAdm`/`cCodim` (the geometric codim VALUE); the
  `t=u` term, the atom-sum `= minAdm(u,p,k)`, and the floor identity are `ℕ` facts.
- **RLCT cap:** this cert works at the per-cell **finiteness / RLCT-codim** level — the coupled per-cell
  RLCT-codim `≥ floor`, needing only the codim LOWER bound `rlct(cell) ≥ floor/2` (native, `∫r^{c−1−2q}dr<∞`
  per chart). **The `rlct = ½·codim` equality (`cited_aoyagi_dln`) is NOT used** — payoff-only. `(□)` stays TRUE.
- **The single-scale `C_k^{single}` is a strict OVER-estimate** of the honest per-cell RLCT-codim at deep
  strata — do NOT wire the per-cell radial with `κ_k`/`C_k^{single}` (the wrong direction; ★ §3).

---

## 8. Close

- **Firmest result.** The coupled per-cell finiteness is realized by an EXPLICIT covering monomial resolution
  (§2) whose every chart has radial exponent `≥ minAdm((u,)+deep) ≥ 2T1q`, with the Vandermonde/`σ^{p−k}`
  measure and every CoV Jacobian carried and the charge `det(Q_bQ_bᵀ)^{−a/2}` dominated. **NO native wall;
  KILL-condition NOT triggered** (0 strata below floor, exact LP + scan). The honest floor is reached WITHOUT
  SVD by the raw pivot/Schur + fibre + residual-power atlas, because the lost-block resolution is a `minAdm`
  corank recursion (`Σᵢmin(βᵢ,u)=minAdm(u,p,k)`) — Lean-friendly (raw-pi, banked atoms). Axiom footprint
  NATIVE (no `cited_aoyagi_dln`).
- **Most likely to break it (the load-bearing constructive content, ★5).** The general NON-SQUARE bilinear
  corank recursion for the reduced `(u, M₂, n)` RRR (the rank-stratified `{V=0}` resolution) — needed for
  `exc>0` or `u≠M₂` (630 arity-4 cuts, incl. the dispatch witness `(3,4,5,4)`); the banked `SchurCore` is
  square-only, and a fibre-peel-to-square does NOT reach the floor (§3, refuted — the factor-of-2 undershoot).
  NOT a native wall (the SVD ground truth proves every chart `≥ floor`, and the SVD atlas is a Lean-costly
  always-available fallback), but the substantive new build. Secondary: carrying the charge through the raw
  corank recursion (the `γ^{hier}` domination is exact, ★4, but must be threaded not dropped — a bounded
  `INFERENCE`).
- **Next construction/consult.** (a) The formaliser builds the general non-square 3-width RRR corank
  recursion (the rank-stratified `{V=0}` cover of `frobSq(Front·Z_deep)`), reusing the `core_schurGen_lt_top`
  WellFounded wrapper with a NON-square per-corank `SchurRecStep`; the reduced object is the arity-3
  (□)-with-charge, one arity down — a chain-length-IH structure worth weighing against the from-scratch build.
  (b) The square sub-family (`u=M₂=n`: `(4,4,4,4)`, `(5,5,5,5)`, `(3,3,4,4)`) lands immediately on the banked
  `routeMBoxThresholdFinite_rrp` + the y-Morse/front peels. (c) Fold in the Codex verdict when it lands.

---

**Files (absolute):**
- `…/genm-couplerad/couplerad-cert.md` (this cert)
- `…/genm-couplerad/scripts/couplerad_resolution.py` (LP + atom decomposition + charge + nested-peel + every-chart-≥-floor)
- `…/genm-couplerad/scripts/couplerad_leanmech.py` (atom-sum = minAdm(u,p,k); deepest-cell = floor; square vs non-square)
- `…/genm-couplerad/scripts/couplerad_reducedreach.py` (reduced bilinear reach: fibre / square-SchurCore / need-non-square — the ★5 gap)
- `…/genm-couplerad/codex/couplerad-{prompt,answer}.md` (decorrelated consult)
