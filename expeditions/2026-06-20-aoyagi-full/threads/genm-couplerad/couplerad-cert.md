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
`det(Q_bQ_bᵀ)^{−a/2}` dominated on the binding-shell scope.** No stratum's honest exponent falls below the
floor on the gate's actual scope (**0 cases over 4386 in-scope cells** — binding strict shells `u=t★+j`,
`1≤j<r`, rankgen `a+b≤ρ−1`, arity-4 widths 1..8; exact LP). **The `rlct = ½·codim` equality
(`cited_aoyagi_dln`) is NOT needed** — only the native codim LOWER bound is used (elementary
`∫r^{c−1−2q}dr<∞` per chart), so the axiom footprint is NATIVE. **The scope is LOAD-BEARING** (decorrelated
Codex red-team): the charge is NOT universally dominated — at NON-binding cuts (e.g. `(6,8,5,5) u=5`, which
has no strict shell) it lowers the codim below the floor; the binding-shell + rankgen scope is exactly what
keeps it dominated.

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
- Charge pull-out: `frontCharge_factor` (banked, IncidenceAssembly) — factors `frontChargeIntegrand` into the
  charge `det(Q_bQ_bᵀ)^{−a/2}` × `frontLossIntegrand`; `frontLoss_pivotPoly_eq` gives `E_top`'s polynomial form.

⚠ **These are ATOMS and ENDPOINTS — the CONNECTIVE REDUCTION `frontChargeIntegrand → SchurCore` is NEW
plumbing, substantial EVEN in the square case** (corankrec-confirmed): the Fubini `∫_p∫_x` split, the `∫_x`
peel composing (A)+(B) to leave a residual power of the deep bilinear (the `core_T_peel_le` pattern
generalized to `(E_top+E_tr)`), landing on `SchurCore`, and the charge-domination lemma. No banked lemma does
`frontLoss → (residual-power × fibre)` — it is new (no analytic wall; the atoms exist).

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

## 5. Decorrelated Codex (gpt-5.x `xhigh`, self-contained, my conclusion WITHHELD)

`codex/couplerad-{prompt,answer}.md`. Codex CONFIRMS the load-bearing structure and SHARPENS the scope —
it is a genuine red-team, not a rubber stamp.

**CONFIRMED (decorrelated):**
- **Uncharged additivity + closed form** — Codex independently derived `C_k^{(0)} = u(ρ−k) + Σ_{j=0}^{k−1}
  min(u, p−k+1+2j)` (= my `u(ρ−k)+Σᵢmin(βᵢ,u)`, reindexed) with the exact key inequality `βᵢeᵢ+ugᵢ ≥
  min(βᵢ,u)(eᵢ+gᵢ) ≥ ½min(βᵢ,u)`, and equality at `eᵢ=0` (βᵢ>u) / `eᵢ=½` (βᵢ<u), the ordering respected
  since `βᵢ` decreases. So ★2/★3 are decorrelated-confirmed.
- **Both dispatch examples reach the floor exactly** (`(4,4,4,4)@u=3`: all k → 10; `(3,4,5,4)@u=2`: all k →
  8); "no analytic obstruction; a chartwise lower bound `C_chart ≥ FLOOR` suffices — exact RLCT equality
  unnecessary" (confirms the NATIVE axiom footprint, no `cited_aoyagi_dln`).
- **The non-square gap** — Codex's "precise problematic set" (`FLOOR−u(ρ−k)>u`, `M₂≠n`, `u≠M₂−(ρ−k)`) matches
  my ★5: for `(3,4,5,4)` k=2,3,4 "a rectangular corank step is required." It confirms atom (B) alone
  certifies at most `u` units (the fibre undershoot) and (C) needs the square condition `u=r` or `r=c`
  (`r=M₂−s, c=n−s`).
- **The Jacobian warnings** — Codex flags the SAME critical factors that must not be dropped: the Vandermonde
  `2(k−i)`, the `σᵢ^{p−k}` measure, `dWᵢ=σᵢ^{−u}d(σᵢWᵢ)`, the `w^{us/2}` Morse-shift Jacobian, every pivot
  power (the tide-D KILL guard, §2.3).

**SHARPENED (Codex red-team — I verified each against the gate scope, `couplerad_chargescope.py`):**
- **The charge is NOT universally dominated.** Codex exhibits `(6,8,5,5) u=5`: charged `C_5 = 18 < FLOOR =
  minAdm(5,5,5) = 19` (my LP reproduces `18` exactly — Codex is arithmetically right). **BUT this is a
  NON-binding cut:** `(6,8,5,5)` has `t★=6`, `r=0`, so it has NO strict binding shell — `u=5` is outside the
  gate scope. **My exact scan confirms 0 charged-below-floor over all 4386 in-scope cells** (binding strict
  shells `u=t★+j, 1≤j<r`, rankgen `a+b≤ρ−1`, arity-4 widths 1..8; including the endpoint `j=r`). So ★4
  (charge inert) HOLDS on the gate's actual scope, and **the scope restriction (binding shell + rankgen) is
  LOAD-BEARING** — the formaliser must carry `u = t★+j` (a binding shell), not invoke the per-cell floor at
  an arbitrary cut. Codex's floor-domination criterion (its inequality (4) + recession conditions) is exactly
  what the binding-shell scope satisfies.
- **The single-matrix SVD model is ARITY-4-specific.** Codex's `(4,4,10,3,10) u=3` (arity 5, `ρ=3 <
  min(M₂,n)`) shows the single normal-slice `p=k+exc` measure under-counts the deep-stratum codim for
  arity≥5. This confirms the scope in §6: the explicit SVD-ray model + reduced-bilinear analysis is ARITY 4
  (single deep matrix); arity≥5 uses the banked CR-path multi-layer descent to the terminal single-matrix
  coupling (the multi-layer codim accumulates across CR-path cells — deephier's cross-layer LP §4, NOT the
  single-matrix formula).
- **The charge needs NO SVD — but the Cauchy–Binet route is NOT Mathlib-banked.** `det(Q_bQ_bᵀ) = Σ_{|I|=b}
  det(Q_{b,I})²` (a sum of squared `b×b` minors) is the SVD-free MATH route — but **Mathlib v4.29 LACKS a
  rectangular Cauchy–Binet** (confirmed in-repo: `Core/CommonPivotL2.lean`, `DLN/…/D1GeCommonPivot.lean` both
  state it and route around it). So do not plan on Cauchy–Binet. The Lean-buildable SVD-free charge handling:
  use the banked a.e.-PosDef `hGae` (arch1build Card 2, `deepFactor_hZrank`) ⟹ `det(Q_bQ_bᵀ) > 0` a.e. (charge
  bounded on the generic locus), then the `−a/2` power is dominated by the loss+measure exponent at the
  binding ray (★4, exact-algebra) — a NEW domination lemma, no spectral term, every pivot Jacobian kept.

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
- **Arity (Codex-sharpened).** The explicit SVD-ray model + reduced-bilinear analysis is **ARITY 4** (single
  deep matrix, all dispatch witnesses) — the single normal-slice `p=k+exc` measure is arity-4-specific and
  UNDER-counts for arity≥5 (Codex CE#1 `(4,4,10,3,10) u=3`, `ρ<min(M₂,n)`). For arity≥5 the banked CR-path
  multi-layer descent (Level 0) reduces to the terminal single-matrix coupling (Stages A/B), and the
  multi-layer deep-stratum codim accumulates ACROSS CR-path cells (deephier's cross-layer LP §4), NOT via the
  single-matrix formula.
- **The binding-shell + rankgen scope is LOAD-BEARING for charge-domination.** Off the binding shells (e.g.
  `t★` at the front-collapse endpoint, `r=0`) the charge can lower the codim below the floor (Codex CE#2
  `(6,8,5,5) u=5`). The per-cell floor may be invoked ONLY for `u=t★+j`, `1≤j<r`, which the upstream
  shell-restriction supplies; the formaliser must carry this hypothesis.
- **WAIST (`M₁ < deepTailMin`) is covered by the same coupled route — NO separate branch** (confirms
  arch1build's waist verdict, decorrelated). The charge-domination holds identically in the waist: **0
  charged-below-floor over 14828 in-scope waist cells** (binding strict shells + rankgen, `M₁<ρ`;
  `couplerad_chargescope.py`). This stresses the charge in its worst regime — waist shells run asymmetric
  with `a>b` (e.g. `(5,3,6,6) u=2`: `a=3,b=1`, `min_k C=11=floor`; `(6,4,8,8) u=2`: `a=4,b=2`, `C=15=floor`),
  the large-`a` case where `det(Q_bQ_bᵀ)^{−a/2}` most plausibly bites — and it stays dominated (tight, margin
  0). Some waist configs simply have no in-scope shell (narrow `M₁` collapses fully, `r=0`, e.g. `(6,2,5,5)`).

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

## w3 — the EXACT charge-domination input for the formaliser (corankrec Q3/Q4)

*The last new-math input for the terminal mountain build. The precise, Lean-relevant answer — including a
correction to the assumed shape.*

**The exact charge.** `det(Q_bQ_bᵀ)^{−a/2}`, `Q_b = A_cor·Z_deep ∈ ℝ^{b×n}`, `a = M₀−u`, `b = M₁−u`. In the
**square-first dispatch case `u=M₂=n` all four witnesses have `a=b=1`**, so `b=1` ⟹ `Q_b` is a `1×n` row and
the charge is concretely `det(Q_bQ_bᵀ)^{−1/2} = ‖A_cor·Z_deep‖^{−1}` (`A_cor ∈ ℝ^{1×M₂}` a row) — an
inverse-norm singularity on `{A_cor·Z_deep = 0}`.

**★4 exact (the domination, ray form).** On a resolution ray, `N_charged(e) = N_loss(e) − γ^{hier}(e)`,
`γ^{hier}(e) = max_h [a(e₁+…+e_h) − h(s−b+h)]`, and
`min_e 2·N_charged/D = min_e 2·N_loss/D = floor` — the charge exponent `γ^{hier}` is DOMINATED at the binding
ray, so the charged per-cell RLCT-codim EQUALS the uncharged one. **Exponent shift `δ = 0`** (verified
`0/4386` in-scope, `0/14828` waist). This is the exact inequality: `N_loss(e) − γ^{hier}(e) ≥ floor/2` for
every ray `e` (equivalently, the charge is absorbed into the freed measure at each corank).

**⚠ CORRECTION to the assumed shape — there is NO Gram-vs-frobSq FOLD onto the uncharged `mnp` at a shifted
`c'` on the tight shells.** A fold `det(Q_bQ_bᵀ)^{−a/2}·frobSq^{−q'} ≤ C·frobSq^{−(q'+δ)}` with `δ>0` shifts
the loss threshold from `½·floor` down to `½·floor − δ`, which **UNDER-proves whenever the shell is TIGHT**
(`floor = 2·T1q` ⟹ `½·floor = T1q` exactly, ZERO exponent slack). **396/761 in-scope arity-4 shells are
tight — INCLUDING ALL FOUR DISPATCH WITNESSES** (`(4,4,4,4)@u=3`, `(3,4,5,4)@u=2`, `(5,5,5,5)@u=4`,
`(3,3,4,4)@u=2`: each `½·floor = T1q`). And the pointwise form `det(Q_bQ_bᵀ)^{a/2} ≥ c·frobSq^δ` is FALSE
(`Front ⊥ A_cor`: the charge `→ ∞` on `{A_cor·Z_deep rank-deficient}` while the loss stays order 1 — disproof:
`A_cor` in the left-kernel of `Z_deep`, `Front` generic). So **w3 CANNOT be a bolt-on fold on the uncharged
`routeMBoxThresholdFinite_mnp`** on the tight shells; the `Front`-vs-`A_cor` independence means the charge and
loss vanish on different loci, so no loss power dominates the charge.

**The correct w3 — thread the charge THROUGH the corank recursion (δ=0): a CHARGED RectSchurCore.** The charge
must be carried INSIDE `routeMBoxThresholdFinite_mnp`'s per-corank step, not bolted on top. The per-corank
inequality to prove: at each corank step (`Z_deep` drops one rank, a singular direction `e_h` freed), the
charge factor's exponent `a·e_h` is `≤` the loss+measure exponent freed at that step — i.e. `γ^{hier}(e) ≤`
(the Jacobian/measure the corank step already carries), so the charge is absorbed at `δ=0`. This is the exact
input; it makes w3 a modest EXTENSION of schurrec's `mnp` proof (charge threaded per-corank), NOT a separate
bolt-on lemma.

**Cauchy–Binet-free realization (the sub-question for schurrec).** v4.29 lacks rectangular Cauchy–Binet, so
`det(Q_bQ_bᵀ) = Σ_{|I|=b} det(Q_{b,I})²` is unavailable. Two Lean-friendly options: (a) the **Gram
Schur-complement det identity** (`Matrix.det_fromBlocks`-based) applied along the SAME pivots the corank
recursion uses — `det(Q_bQ_bᵀ)` factors in lockstep with `Z_deep`'s resolution, each factor's `−a/2` power
`≤` the corresponding loss-codim gain; (b) a determinant-monotonicity bound — but the crude `det(A_cor G
A_corᵀ) ≥ det(A_cor A_corᵀ)·λ_min(G)^b` REINTRODUCES a `det(Z_deep Z_deepᵀ)`-charge (option-2 compounding) and
is spectral (avoid). Route (a) is the target. **Banked consumed:** `hGae` (Card 2, `Q_bQ_bᵀ` PosDef a.e. ⟹
`det > 0`, charge finite a.e.), schurrec's `mnp` recursion (extended charged), `Matrix.det_fromBlocks`.
**Exponent shift: `δ = 0`** — that the charge costs the loss NOTHING is the whole content, and is exactly why
it must live in the recursion rather than a fold.

**Slack shells (365/761, `floor > 2·T1q`).** There a fold with `δ ≤ ½·floor − T1q > 0` IS admissible — but
since the tight shells (incl. all witnesses) force `δ=0`, build the charged-recursion route uniformly.

---

## w3-percorank — the EXACT per-corank charge-absorption inequality (schurrec's charged RectSchurCore step-4)

*schurrec's rect split: pivot `t×t` minor of `Δ=Front`, residual `Sc`; `S=Z_deep` row-split `S_top`(t) +
`S_bot`(M₂−t); `A_cor=[A_top|A_bot]` col-split, so `Q_b = A_cor·S = A_top·S_top + A_bot·S_bot` (a SUM).
schurrec asks (1) how `det_fromBlocks` factors `det(Q_bQ_bᵀ)` in lockstep, and (2) which variable's measure
absorbs `a·e_h`. Exact answers (`/tmp` per-corank check + `couplerad_chargescope.py`):*

**A1 — `det_fromBlocks` does NOT apply to `Q_b` (schurrec is right: `Q_b` is a SUM, not a block matrix). The
right tool is det-MONOTONICITY on the PSD Gram.** Do not chase a `Q_b` block-factorization. Instead use
`det(Q_bQ_bᵀ) = det(A_cor·G·A_corᵀ)` with `G := Z_deep·Z_deepᵀ ⪰ 0` (`M₂×M₂`, PSD; `G` IS block under the
`S_top/S_bot` split, `det_fromBlocks` applies to `G`, and `G/G_tt = S_bot·Π_⊥·S_botᵀ` is the transverse-Schur
= `E_tr`). The domination is a LOWER bound on `det(Q_bQ_bᵀ)`:
- split `G = G₁ + G₀` into the σ-**order-1** part `G₁` (the directions the resolution keeps at scale `τ⁰`)
  and the small part `G₀` (both `⪰ 0`); then `A_cor·G·A_corᵀ = A_cor·G₁·A_corᵀ + A_cor·G₀·A_corᵀ` (both `⪰ 0`),
  so by **det-monotonicity on PSD** (`det(X+Y) ≥ det X` for `X,Y ⪰ 0` symmetric),
  `det(Q_bQ_bᵀ) ≥ det(A_cor·G₁·A_corᵀ)`.
- On the pivot chart the order-1 block `G₁` has rank `= #{e_i = 0}`, and **along the binding ray this is `≥ b`**
  (see A2), so `det(A_cor·G₁·A_corᵀ) > 0` and is order-1 a.e. (this is exactly `hGae`/corank-survival: `A_cor`
  sees `b` order-1 directions). Hence `det(Q_bQ_bᵀ)^{−a/2} ≤ C` — the charge is **BOUNDED** on the chart.
  No Cauchy–Binet, no `det_fromBlocks` on `Q_b`, no spectral eigen-term needed for the bound itself — only
  `det`-monotone-on-PSD + `G₁ ⪯ G` PSD + `hGae`.

**A2 — which measure absorbs `a·e_h`: Z_deep's, via the FRONT-peel keeping σ order-1 — and at the binding
ray the charge exponent is `γ = 0` (EXACT, verified all cells).** At the charged-LP binding vertex, `γ^{hier}(e)
= 0` for EVERY cell `k=1..ρ` including the deepest `s=0` (`/tmp` check: `(4,4,4,4)`, `(5,5,5,5)`, `(3,3,4,4)`,
`(3,4,5,4)` all `γ=0` at binding). Mechanism: the binding (cheapest) ray peels the charge-relevant LARGE
singular values via the FRONT weights (`g_i=½, e_i=0`), leaving those `σ_i` at scale `τ⁰` = order 1 — so
`Q_b` sees `≥ b` order-1 directions and the charge stays order 1 (`γ=0`). The charge only excites (`γ>0`)
along NON-binding rays that peel those large `σ` in the `σ`-direction (`e_i>0`), and there the LOSS codim is
correspondingly larger. **The exact per-corank inequality: `γ^{hier}(e) ≤ N_loss(e) − floor/2` for EVERY ray
`e`** (equality, both `=floor/2`, at the binding ray). So the charge exponent is absorbed by **Z_deep's
loss+measure at δ=0** — NOT `A_cor`'s blow-up (A_cor only supplies the a.e.-positivity `hGae`), NOT `Front`'s.

**A=b=1 concrete (the square-first dispatch case).** `det(Q_bQ_bᵀ) = ‖A_cor·Z_deep‖² = A_cor·G·A_corᵀ`
(scalar). det-monotonicity ⟹ `‖A_cor·Z_deep‖² ≥ A_cor·G₁·A_corᵀ ≥ λ·(A_cor·v)²` for `v` an order-1
direction (`λ` order 1) `> 0` a.e. (hGae) ⟹ charge `= ‖A_cor·Z_deep‖^{−1} ≤ C` on the chart. Bolt-on
`charge·loss ≤ C·loss` closes via uncharged `mnp`. The full-collapse leaf is handled by the same order-1
count (`≥ b=1` front-peeled direction along the binding ray).

**Banked / needed.** CONSUMES: `det`-monotone-on-PSD (`det(X) ≤ det(X+Y)`, `Y ⪰ 0` — CONFIRM in Mathlib
v4.29 or a small proof via `PosSemidef` order + `det` on the Loewner order; schurrec has `PosSemidef`
Gram), `G₁ ⪯ G` (the order-1 block `⪯ G`, PSD), `hGae` (Card 2, `A_cor` sees `b` order-1 directions a.e.),
uncharged `routeMBoxThresholdFinite_mnp`. Does NOT need: Cauchy–Binet (unavailable), `det_fromBlocks` on `Q_b`
(wrong — sum form), spectral eigenvalues. `det_fromBlocks` on `G` is optional (only to exhibit the
transverse-Schur `E_tr`). **Exponent shift `δ = 0`.** The one thing to nail in Lean: the order-1 block `G₁`
in raw coordinates (it is the pivot block the loss recursion already keeps order-1 — reuse that pivot, don't
re-derive spectrally).

---

## 8. Route recommendation (controller Q) — RECOMMEND the non-square corank recursion (Route A) over the chain-length-IH (Route B)

**RECOMMENDATION: Route A (the general non-square corank recursion on the reduced bilinear), NOT Route B
(chain-length-IH).** Route A is lower-risk-to-build.

**Why Route B (chain-length-IH) re-hits the option-2 failure.** The reduced object IS the arity-3
(□)-with-charge for `(u, M₂, n)`, one arity down — but the "one arity down" does NOT rescue a length
induction, because the *charge* is what breaks it, not the arity. The front-peel decorates the sub-chain with
`det(Q_bQ_bᵀ)^{−a/2}`; under a chain-LENGTH induction, each recursive peel of the sub-chain generates ANOTHER
determinantal decoration, and they COMPOUND (do not telescope) — precisely diagbfix's dead option-2. The
arity-3-(□)-with-charge does not avoid this: a clean `(□)` IH is uncharged, and the charge cannot be dropped
(it is a negative power, the wrong direction for an upper bound), so the IH must carry a growing product of
charges. So Route B inherits the parked-Route-B obstruction.

**Why Route A carries the charge cleanly.** Route A resolves the SINGLE reduced bilinear `frobSq(Front·Z_deep)`
directly by a corank recursion (recursion on the CORANK of one bilinear, not on chain length). The charge is
ONE decoration (`a=M₀−u` fixed), carried through the corank steps and dominated at EACH step (★4, verified
inert per-corank on the binding-shell scope, `couplerad_chargescope.py`; SVD-free via the banked a.e.-PosDef
`hGae` + the ★4 exponent domination — NOT via Cauchy–Binet, which Mathlib v4.29 lacks). No compounding. Route A also REUSES the banked
`core_schurGen_lt_top` WellFounded-on-corank wrapper — only the per-corank `SchurRecStep` needs the non-square
generalization (analogous to the banked square `routeMBoxThresholdFinite_rrp`), and its floor-reach is the
atom-sum `= minAdm(u,p,k)` (exact), matching the QIP recursion the corank step implements.

**Build order suggestion (bank a real win first).** The square sub-family `u=M₂=n` (`(4,4,4,4)`, `(5,5,5,5)`,
`(3,3,4,4)`) needs **no new CORANK lemma and no new analytic ATOM/wall** — but it is NOT zero new work.
⚠ **The reduction plumbing `frontChargeIntegrand → SchurCore` is itself substantial NEW work even square**
(corankrec pinned this; my earlier "lands immediately" was an overclaim). What is banked: `frontCharge_factor`
(charge pull-out → `frontLossIntegrand`), the atoms `radial_morse_residual_power_le` (A) +
`fibre_lintegral_mul_le` (B), and `routeMBoxThresholdFinite_rrp` (the SchurCore endpoint). What is NEW
plumbing: (i) the Fubini `∫_p ∫_x` split; (ii) the `∫_x` peel = front-fibre (B) + surviving y-Morse (A)
leaving a RESIDUAL POWER of the deep bilinear — the `RouteM334Hfin.core_T_peel_le` pattern (with `w :=` the
deep bilinear under the outer `∫_p`) generalized to `frontLossIntegrand`'s transverse-Schur `(E_top+E_tr)`;
(iii) landing the deep residual on `SchurCore`; (iv) the charge-domination lemma (§2.3). So: build the arity-4
square case first (closes `(4,4,4,4)`, `(5,5,5,5)`, `(3,3,4,4)`) as the plumbing + banked endpoints, THEN add
the non-square per-corank `SchurRecStep` for `exc>0`/`u≠M₂` (closes `(3,4,5,4)`). Always-available fallback if
the non-square corank step stalls: the SVD ray atlas (Lean-costly — needs the spectral + Vandermonde-measure
Mathlib build; a valid native route, so no wall either way).

**Residual risk on Route A (name it):** the non-square per-corank step is genuinely new (square is banked),
and the charge must be threaded through it (dominated per ★4, but not dropped). Both are detail-at-scale
(feasibility-validated in `iterfibre-route-cert.md` §4), not monuments.

---

## 9. Close

- **Firmest result.** The coupled per-cell finiteness is realized by an EXPLICIT covering monomial resolution
  (§2) whose every chart has radial exponent `≥ minAdm((u,)+deep) ≥ 2T1q`, with the Vandermonde/`σ^{p−k}`
  measure and every CoV Jacobian carried and the charge `det(Q_bQ_bᵀ)^{−a/2}` dominated. **NO native wall;
  KILL-condition NOT triggered** (0 strata below floor over 4386 in-scope binding-shell cells, exact LP scan;
  the charge-domination is scoped to the binding shells — Codex-red-teamed, §5). The honest floor is reached WITHOUT
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
- **Next construction (route: §8, Route A recommended).** (a) Build the arity-4 SQUARE sub-family first
  (`u=M₂=n`: `(4,4,4,4)`, `(5,5,5,5)`, `(3,3,4,4)`): the reduction plumbing (Fubini + y-Morse (A) / front (B)
  atom composition + charge domination) onto the banked `routeMBoxThresholdFinite_rrp` — NO new corank lemma /
  atom, but the plumbing IS substantial new work (§8, corankrec-confirmed). (b) Then the general non-square
  per-corank `SchurRecStep` (reusing `core_schurGen_lt_top`) for `exc>0`/`u≠M₂` (closes `(3,4,5,4)`), carrying
  the charge (dominated per ★4; SVD-free via banked a.e.-PosDef `hGae`, NOT Cauchy–Binet which Mathlib v4.29
  lacks). Prefer this over the chain-length-IH (Route B re-hits option-2, §8). (c) Carry the binding-shell scope hypothesis (`u=t★+j, 1≤j<r`) — off it the charge is not dominated
  (Codex CE, §5). Codex verdict FOLDED IN (§5) — CONFIRMS structure + additivity + no-`cited_aoyagi_dln`,
  SHARPENS the scope.

---

**Files (absolute):**
- `…/genm-couplerad/couplerad-cert.md` (this cert)
- `…/genm-couplerad/scripts/couplerad_resolution.py` (LP + atom decomposition + charge + nested-peel + every-chart-≥-floor)
- `…/genm-couplerad/scripts/couplerad_leanmech.py` (atom-sum = minAdm(u,p,k); deepest-cell = floor; square vs non-square)
- `…/genm-couplerad/scripts/couplerad_reducedreach.py` (reduced bilinear reach: fibre / square-SchurCore / need-non-square — the ★5 gap)
- `…/genm-couplerad/scripts/couplerad_chargescope.py` (the Codex red-team response: charge-below-floor is 0/4386 IN-scope; the CE at a non-binding cut)
- `…/genm-couplerad/codex/couplerad-{prompt,answer}.md` (decorrelated consult — CONFIRMS structure, SHARPENS scope)
