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
- **`G₁` must be the FULL order-1 rank-`ρ` block** (`ρ = deepTailMin`, the generic rank of `Z_deep`), NOT a
  rank-`b` piece. `det(Q_bQ_bᵀ) ≥ det(A_cor·G₁·A_corᵀ)` gives the UNIFORM chart bound: `G₁` is fixed
  (`S`-independent, order-1), so `∫_{A_cor} det(A_cor·G₁·A_corᵀ)^{−a/2} =: C` is a CONSTANT, finite iff
  `a < ρ − b + 1` — which rankgen `a+b ≤ ρ−1` guarantees (`⟹ a+b ≤ ρ−1 < ρ+1`; this is deephier §5's
  "non-integrable wall `a+b ≥ ρ+1`"). Then `∫_S W(S)·L(S) ≤ C·(uncharged mnp) < ⊤`, `δ=0`. **⚠ Do NOT reduce
  `G₁` to a rank-`b` minor for this bound** — the charge integral `∫_{A_cor}` uses the FULL rank-`ρ` Gram; a
  rank-`b` reduction over-bounds and DIVERGES (`a≥1` vs the rank-`b` wall `a<1`) — this is a real trap
  (schurrec-caught). Consumes only `det`-monotone-on-PSD + `G₁ ⪯ G` PSD + `hGae` (no Cauchy–Binet, no
  `det_fromBlocks`-on-`Q_b`, no spectrum). *(A rank-`b` minor `M` with `det M ≠ 0` a.e. is a SEPARATE, weaker
  fact — good only for the a.e.-nonzero genericity, not the `∫_{A_cor}` integrability; see the addendum.)*

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

### w3-percorank addendum — the `b≥2` det-monotone, NON-SPECTRALLY (schurrec's snag)

*The Loewner det-monotone `0 ⪯ Y ⪯ X ⟹ det Y ≤ det X` is not in Mathlib v4.29, and its textbook proof is
spectral (`det = ∏ eigenvalues`), hitting the D-C `IsHermitian.eigenvalues` whnf trap. A non-spectral proof
+ a cleaner reduction, so `b≥2` (e.g. `(3,4,5,4)`, `b=2`) dodges the trap.*

**⚠ Two DIFFERENT bounds — do not conflate them (schurrec-caught).**
1. **a.e.-NONZERO (genericity only):** drop columns. `Q_bQ_bᵀ = Σ_c q_c q_cᵀ ⪰ M·Mᵀ` for `M = Q_b[:,κ']` a
   `b×b` column-minor (`Q_bQ_bᵀ − MMᵀ = Σ_{c∉κ'} q_c q_cᵀ ⪰ 0`, elementary), so det-monotone ⟹
   `det(Q_bQ_bᵀ) ≥ det(M)²`, and `det M ≠ 0` a.e. (hGae). This shows the charge is FINITE a.e. — nothing more.
2. **UNIFORM INTEGRABILITY bound (the one that closes the integral):** det-monotone with `G₁ =` the FULL
   order-1 **rank-`ρ`** block (`⪯ G`), giving `det(Q_bQ_bᵀ) ≥ det(A_cor·G₁·A_corᵀ)` with `G₁` fixed, so
   `∫_{A_cor} det(A_cor·G₁·A_corᵀ)^{−a/2} = C < ⊤` iff `a < ρ−b+1` (rankgen).
**Do NOT use bound 1 for the integral:** `∫_{A_cor} |det M|^{−a}` with `M` a `b×b` (rank-`b`) minor DIVERGES
for `a ≥ 1` (its zero locus is codim `< ρ`), whereas the true charge integral uses the FULL rank-`ρ` Gram
`Σ_c q_c q_cᵀ` (zero locus codim `ρ`, finite for `a < ρ−b+1`). Reducing to a rank-`b` minor over-bounds. So
`G₁` for the integrability bound is the rank-`ρ` order-1 block, NOT a `b×b` minor.

**The det-monotone, non-spectrally (induction on `b` via the Schur complement).** `0 ⪯ Y ⪯ X` (`b×b` sym) ⟹
`det Y ≤ det X`:
- `b=1`: scalars `0 ≤ y ≤ x`. ✓ (this is all `b=1` needs — no det lemma at all).
- `b→`: if `det Y = 0`, done (`det X ≥ 0`). Else `Y ≻ 0` (so `X ≻ 0`, `X',Y' ≻ 0`). Block on the last
  coordinate `X = [[X',p],[pᵀ,α]]`, `Y = [[Y',q],[qᵀ,β]]`. Then (a) `X' ⪰ Y' ⪰ 0` (principal submatrix:
  `vᵀX'v = [v;0]ᵀX[v;0] ≥ [v;0]ᵀY[v;0]`); (b) `det_fromBlocks₁₁`: `det X = det X'·(α − pᵀX'⁻¹p)`,
  `det Y = det Y'·(β − qᵀY'⁻¹q)`; (c) the Schur complements are monotone by the VARIATIONAL identity
  `α − pᵀX'⁻¹p = min_{w} [w;1]ᵀ X [w;1]` (complete the square; minimiser `w=−X'⁻¹p`), and `[w;1]ᵀX[w;1] ≥
  [w;1]ᵀY[w;1] ∀w` (Loewner pointwise) ⟹ `min_w(X) ≥ min_w(Y)` (min of a pointwise-larger function:
  `min f_X = f_X(w_X^*) ≥ f_Y(w_X^*) ≥ min f_Y`); (d) induction `det X' ≥ det Y'`, all factors `≥ 0` ⟹
  `det X = det X'·Schur(X) ≥ det Y'·Schur(Y) = det Y`. ∎
  Consumes: `Matrix.det_fromBlocks₁₁` (banked), completing-the-square min (elementary), principal-submatrix
  Loewner (elementary), induction. **NO eigenvalues** — dodges the whnf trap. (Equivalent packaging: this IS
  Minkowski's determinant inequality proved via Schur complements rather than majorisation.)

**So for schurrec:** `b=1` is fully elementary — the charge integral `∫_{A_cor} ‖A_cor·Z_deep‖^{−a}` uses the
FULL rank-`ρ` Gram `Z_deep·Z_deepᵀ` (a rank-`ρ` quadratic form), finite for `a < ρ` (⟸ rankgen), and the
UNIFORM chart bound replaces the `S`-varying Gram by the fixed order-1 rank-`ρ` block (det-monotone, `b=1`
= trivial scalar monotonicity) — NO det lemma, NO reduction to a single column. Banks `(4,4,4,4)`,
`(5,5,5,5)`, `(3,3,4,4)`. For `b≥2`, prove the non-spectral det-monotone ONCE (reusable) and apply it with
`G₁ =` the order-1 rank-`ρ` block for the integrability bound (drop-columns to a `b×b` minor is ONLY the
a.e.-nonzero step, not the integral — see the ⚠ above). The plan (b=1 first, then b≥2) is SOUND.

### w3-atlas — the charged-core COVER structure (schurrec's Holes 1 & 2)

*schurrec found: (H1) a carried-charge WF recursion at fixed `(a,b)` is uninhabitable — the charge weight
`∫_{A_cor} det((A_cor·S)(A_cor·S)ᵀ)^{−a/2}` needs `a < rank(S)−b+1`, and a shared-dim-dropping recursion
sends `rank(S)` below `a+b`, diverging; (H2) the charge needs an `S=Z_deep`-rank floor the loss's
Front-driven charts don't supply. Both are correct. The exact structure:*

**(a) YES — resolve `Z_deep = S` by its OWN rank flag as the PRIMARY (outer) cover** (the Hole-2 fix). The
loss's Front-driven `mnp` charts do NOT stratify `S`'s rank, so the `S`-rank flag is the outer atlas; the
uncharged `mnp` is applied to the Front-loss PER `S`-cell.

**(b)/(c) — ONE atlas (`S`-rank flag), but the charge is RE-EXPRESSED per rank-drop, not carried (the Hole-1
fix), and it is bolt-on ONLY on the shallow cells.** ⚠ **CORRECTED THRESHOLD (schurrec-caught off-by-one):**
the Wishart weight `∫_{A_cor} det((A_cor·S)(A_cor·S)ᵀ)^{−a/2}` is finite iff `a < rank(S) − b + 1`, i.e.
**`rank S ≥ a+b`** (integers) — NOT `≥ a+b−1`. Split the `S`-cells by `rank S`:
- **SHALLOW cells `rank S ≥ a+b`:** the charge is Wishart-BOUNDED. Cover `{rank S ≥ a+b}` by pivot-charts
  (which `(a+b)×(a+b)` minor of `SSᵀ` is `≥ δ`); on each, det-monotone (A) against the FIXED order-1
  rank-`(a+b)` pivot block `G₁` (`⪯ SSᵀ`, `hGae` floor) gives `charge ≤ det(A_cor·G₁·A_corᵀ)^{−a/2}`, whose
  `∫_{A_cor}` over the `a+b` effective directions is a fixed Wishart const (finite: `a < (a+b)−b+1 = a+1`,
  trivially). So **charge ≤ C × uncharged `mnp`** — bolt-on PER PIVOT-CHART (reading (ii)), with a
  **rank-`(a+b)` floor, NOT the full rank-`n` floor** (so `corankWeight_lt_top`'s `SSᵀ ⪰ c₀²I_n` is TOO
  STRONG for the mid shallow cells `rank S ∈ {a+b,…,n−1}`; it covers only the top cell `rank S = n`).
- **DEEP cells `rank S ≤ a+b−1`:** the Wishart weight DIVERGES (Hole 1). Charge RE-EXPRESSED on the
  Schur-complement `E`; `E`'s MEASURE (`σ^{p−k}`·Vandermonde) PAYS the increment (`δ=0`, per-ray
  `γ^{hier}(e) ≤` freed measure). WELL-FOUNDED recursion on `E` (strictly smaller). Hole 1 dodged because
  re-expressed-with-measure, not carried at fixed `(a,b)`.

**Scope (the actionable part) — CORRECTED:**
- **`b=1` (the 3 square dispatch witnesses `(4,4,4,4)`,`(5,5,5,5)`,`(3,3,4,4)`): deep = `{rank S ≤ 1}`**
  (`a+b−1 = 1`), which is POSITIVE-codim (the rank-`1` locus), **NOT `{S=0}` only**. *(My earlier
  "`b=1` all-shallow / pure bolt-on" was the off-by-one error — WRONG.)* So `b=1` is NOT a freebie: shallow
  `{rank S ≥ 2}` is per-chart bolt-on (rank-`2` floor), but `{rank S ≤ 1}` needs the coupled re-expression
  (a SHORT 2-level recursion: rank `1` then `0`). `corankWeight_lt_top` (full-rank-`n`) applies only to the
  top cell `rank S = n` (needs `ρ = n`; holds for `(4,4,4,4)→(3,4,4)`, `n=4=ρ`).
- **`b≥2` (e.g. `(3,4,5,4)`,`b=2`: deep `rank S ≤ 2`; `(4,5,6,5)`,`b=2`: deep `rank S ≤ 2`):** deeper
  coupled region, longer `E`-recursion. Same structure as `b=1`, more levels.

**Smallest correct decomposition:** `S`-rank-flag cover; per shallow cell `charge(Wishart const) ×
uncharged mnp`; per deep cell recurse on the Schur-complement `E` with its measure. NOT a Front-driven cover
(H2), NOT a fixed-`(a,b)` carried recursion (H1). The deep-cell per-step charge re-expression (Gram Schur
complement `det(SSᵀ) = det(surviving)·det(E-Schur)` via `det_fromBlocks` on `G=SSᵀ`, + the measure accounting)
is the technical heart for `b≥2`; the `δ=0` per-ray inequality guarantees it closes.

### w3-deep — the EXACT deep-cell inequality, b=1 (corneradj-VALIDATED: LOGARITHMIC, not power)

*corneradj (decorrelated) confirmed the interior deep-locus `∫_S` converges and CORRECTED my mechanism: the
charge weight is `Ch(S) ~ ln(1/σ)` (LOGARITHMIC), the `S`-measure (codim ≥ 1) pays, `γ=0`; and the
`A_cor⊥frame`/`σ` directions are COUPLED (`σ→0` supplies the transverse direction taming `A_cor·u→0`
off-stratum; the residual log is absorbed by the `S`-measure). `(□)` is SAFE. Exact-verified here
(`couplerad_deeplog.py`, sympy).*

**The exact per-stratum accounting (b=1, a=1 — all three b=1 dispatch witnesses).** Near the rank-drop, `S`
has one order-1 singular value `σ₁~1` and the next `σ₂ = σ → 0`; with `x = A_cor·u₁`, `y = A_cor·u₂`:
- **charge weight is LOGARITHMIC** (NOT a power — corrects my earlier power-preview):
  `W(S) = ∫_{A_cor} ‖A_cor·S‖^{−1} ~ ∫∫(x²+σ²y²)^{−1/2}dx dy = ∫ arcsinh(1/(σy)) dy ~ ln(1/σ) + const`
  (exact: inner `∫_0^1(x²+σ²y²)^{−1/2}dx = arcsinh(1/(σy)) → ln(2/(σy))`, outer `∫_0^1 ln(1/(σy))dy = 1−ln σ`).
- **the S-measure pays:** with `σ`-measure `σ^{c−1}dσ` (`c = codim of the rank-drop ≥ 1`),
  `∫_0^δ (1+ln(1/σ))·σ^{c−1}dσ < ∞` for every `c ≥ 1` (even `c=1`: `= δ(2−ln δ)`). **`δ = 0`** — the log is
  SUB-power, no codim shift; `γ = 0`.
- **Lean-buildable form (two options):** (I) explicit `arcsinh → log` bound + the measure integral; (II)
  Lean-friendlier — bound the log crudely by a small power `ln(1/σ) ≤ C_ε·σ^{−ε}` (`σ∈(0,1)`, any `ε>0`),
  so `W(S) ≤ C_ε σ^{−ε}` and `∫_0^δ σ^{−ε}·σ^{c−1}dσ < ∞` for `ε < c` (pick `ε∈(0,1)`, `c≥1`). Option (II)
  avoids `arcsinh` entirely — just `japaneseBracket`/`σ^{−ε}`-integrability against the codim-≥1 measure.

**⚠ SCOPE — the LOG is `a=1`-specific.** For `a≥2` (`b=1`) the inner integral is a POWER `~ σ^{−(a−1)}` and
the `y`-integral `∫y^{−(a−1)}dy` needs `a≥2` handled by the deeper (`b≥2`-style) measure — a DIFFERENT
(power) case. **All three `b=1` dispatch witnesses have `a=1`**, so the LOG form is exactly what schurrec's
`b=1` build needs. The `b≥2` deep cells (and `a≥2`) are the power case = the general `E`-recursion (§w3-atlas),
to be pinned when schurrec reaches them.

**Net for the `b=1` deep cell:** it is NOT a power-recursion — it is a LOG weight killed by the codim-≥1
`S`-measure (one clean step, `δ=0`), plus the `A_cor⊥frame`/`σ` coupling that corneradj confirmed closes.
Much milder than my preview implied.

### w3-shellint — the interior free-box SHELL-INTEGRATION design (deliverable (ii), for schurB)

*The interior free-box bound `∫∫_box det((A_cor·S)(A_cor·S)ᵀ)^{−a/2} dA_cor dS < ⊤` for `a+b ≤ ρ`
(`ρ = deepTailMin = rank S generic`). corankrec/schurB routed the shell-integration to me; schurB's
`chargedWishartWeight_lt_top` is the per-shell atom. Lean-friendly design + the interface answers +
the ONE flag (`couplerad_shellint.py`).*

**Shell decomposition (by `σ_ρ(S)`, the smallest singular value).** `{S-box} = {σ_ρ ≥ δ₀}` (BULK) `∪
⋃_ε {σ_ρ ∈ [ε,2ε)}` (INTERIOR, `ε ↓ 0`). Equivalently by `|det P|` for `P` the `ρ×ρ` pivot block (on the
pivot chart `|det P| ~ σ_ρ` × order-1). This is the deepCover_aux/`rankEqLocus` pivot cover refined to a
uniform-`ε` shell (the charts give only pointwise `IsUnit(P)`; the shell adds `|det P| ∈ [ε,2ε)`).

**σ-measure CoV (the ladder step-2 Jacobian).** Co-area for `σ_ρ` (equivalently `det P`): the shell
`{σ_ρ ∈ [ε,2ε)}` has S-measure `~ ε^{c−1}dε`, `c = codim{rank S ≤ ρ−1} = (M₂−ρ+1)(n−ρ+1) ≥ 1`. So the
shell-integration is `∫_S = ∫_0^{δ₀} C(ε)·ε^{c−1}dε` (× the transverse order-1 directions), `C(ε) =` the
per-shell charge bound.

**BULK `{σ_ρ ≥ δ₀}`:** schurB's `chargedWishartWeight_lt_top` at fixed `δ₀` — charge `≤ C(δ₀)` uniform,
`∫_S` over the finite-volume bulk `< ⊤`. schurB's atom IS the bulk consumer (with the rank-`ρ` lift, below).

**⚠ INTERIOR — the ONE FLAG: schurB's UNIFORM-`δ` atom is TOO CRUDE for the shell-integration; it needs the
TIGHT (graded) per-shell bound.** schurB's atom, via the isotropic reduction `charge ≥ (δ²)^b·det(A_cor
A_corᵀ)`, gives `C(ε) ~ ε^{−ab}` — and `∫_0 ε^{−ab}·ε^{c−1}dε` DIVERGES when `c ≤ ab`. **`c ≤ ab` for EVERY
dispatch witness** (`c=1=ab` for the three square `a=b=1` cases `(4,4,4,4)`,`(5,5,5,5)`,`(3,3,4,4)`;
`c=2=ab` for `(3,4,5,4)`). The uniform-`ε²` floor over-charges — it treats ALL `ρ` singular values as `~ε`,
but only `σ_ρ ~ ε` (the top `ρ−1` are order-1). The TIGHT bound uses the GRADED structure: on `{σ_ρ ~ ε}`,
`C(ε) ~ log(1/ε)` (b=1,a=1; exact §w3-deep / `couplerad_deeplog`), and `∫_0 log(1/ε)·ε^{c−1}dε < ⊤` for
`c ≥ 1` (even `c=1`: `= δ₀(2−ln δ₀)`). So the interior is the **§w3-deep graded/log estimate**, NOT the
crude uniform atom integrated.

**Two routes for the tight interior (schurB picks):**
- **(a) graded-floor Wishart atom:** extend `chargedWishartWeight_lt_top` from the uniform floor
  `SSᵀ ⪰ δ²·P_J` to the GRADED floor `SSᵀ ⪰ δ₀²·P_{top(ρ−1)} + ε²·P_{last}` (top `ρ−1` at order-1, the
  `ρ`-th at `ε²`), which exposes `C(ε) ~ log(1/ε)` [b=1,a=1] directly. Then shell-integrate.
- **(b) wire the §w3-deep log directly:** the per-shell bound `W(S) ≤ C·(1+log(1/σ_ρ))` (b=1,a=1, ready)
  + the `σ_ρ`-measure CoV. Recommended for the 3 square witnesses (ready now).

**Interface answers (schurB's Q1/Q2) — CORRECTED (a coordinate-`P_J` subtlety at `ρ<n`).** `ρ = min(M₂,
n_last)` (S = Z_deep `M₂×n_last`, schurB's inner dim `n = M₂`).
- **FULL-RANK case `ρ = M₂ = n` (S square — ALL 3 square dispatch witnesses `(3,4,4)`,`(4,5,5)`,`(2,4,4)`):**
  `P_J = I_n`, floor `SSᵀ ⪰ δ²·I_n`. **Q2 bridge is CLEAN here:** `|det S| ≥ ε ∧ σ_max(S) ≤ M ⟹ σ_min(S) ≥
  ε/M^{n−1} ⟹ SSᵀ ⪰ (ε/M^{n−1})²·I_n` (`det S = ∏σ_i`, `σ_i ≤ M`; then `σ_min` floor ⟹ Loewner over ALL `n`
  directions). `σ_max(S) ≤ M = √(M₂·n_last)` on the box. So I hand `(|det S| ≥ ε, σ_max ≤ M)`; schurB writes
  the `det→σ_min→SSᵀ⪰δ²I` bridge (~15-25 lines). **This is the immediate build (3 square witnesses).**
- **⚠ RANK-`ρ` lift `ρ < n` (`M₂ > n_last`, e.g. `(2,5,4)`): the COORDINATE-`P_J` floor `SSᵀ ⪰ δ²·P_J` is
  NOT bridgeable — FLAG.** When `SSᵀ` is rank-deficient (`ρ < n`), `SSᵀ ⪰ δ²·(rank-ρ COORDINATE projection)`
  can FAIL even with an invertible `ρ×ρ` pivot minor (exact counterexample: `S = [[1,0],[2,0]]` rank-1,
  pivot `S[0,0]=1`, yet `SSᵀ − δ²·diag(1,0)` has a negative eigenvalue — the `Jᶜ`-rows are dependent on the
  `J`-row, so no coordinate floor). So the coordinate-`P_J` lift does NOT work for `ρ<n`; the correct floor
  is `SSᵀ ⪰ δ²·P_{rowspace(S)}` (the ACTUAL `ρ`-dim row-space projection, NON-coordinate) or the
  drop-columns route (`(A_cor S)(A_cor S)ᵀ ⪰ (A_cor S[:,K])(A_cor S[:,K])ᵀ`, det-monotone, `K` = pivot
  COLUMNS). Both are heavier than the coordinate lift. **Defer `ρ<n` (only `(2,5,4)` among the witnesses); I
  pin the correct `ρ<n` lift when schurB reaches it.** `Q1`: `P_J = I` (full-rank, immediate); `P_J` for `ρ<n`
  is NOT a coordinate `range e` — that's the flag.
  `J`/pivot from `exists_nonsingular_submatrix_of_le_rank` gives the `ρ` pivot rows (coordinate subset,
  `range` of the injective row-embedding) — but the coordinate floor on it fails for `ρ<n` (above).

**Net:** bulk = schurB's uniform atom (rank-`ρ` lift); interior = the graded/log tight bound (route a or b) +
the `σ_ρ`-measure CoV (`c = (M₂−ρ+1)(n−ρ+1)`). The MINIMAL GAP is the tight (graded) per-shell bound — the
crude uniform atom's `ε^{−ab}` fails at `c ≤ ab` (all witnesses). Log-integrability is standard/sound: **NO
WALL** (the graded bound is a build, not an obstruction). General `(a,b)`: the tight interior form is the
§w3 general estimate (log for b=1,a=1, verified; the `(3,4,5,4)` a=1,b=2 tight form I pin when reached).

### w3-routeC — the S-FIRST Tonelli route (intmtn's (C)): closes the WHOLE b=1 charge free-box in one step

*intmtn's route (C) — integrate `S` FIRST — is VALID and SUBSUMES the bulk-atom + shell-integration for the
b=1 charge free-box `∫∫_box ‖A_cor·S‖^{−1} dA_cor dS` (a=b=1). It sidesteps my arcsinh (route b), the
det-pushforward anti-concentration (route a), schurB's uniform atom + bridge, AND the shell decomposition —
all replaced by one Tonelli + a linear-form slab bound. It also sidesteps the ρ<n coordinate-P_J issue for b=1.*

**Validity (intmtn's Q1).** The interior charge object is `∫∫_box ‖A_cor·S‖^{−1} dA_cor dS` over the FULL
positive-measure box (corankrec's "free-box", the `a+b ≤ ρ` regime — NO rank restriction; `{rank S ≤ ρ−1}` is
measure-zero WITHIN the box where the charge blows up, but the integral is over all of it). So Tonelli / S-first
applies. NOT a lower-dim rank-stratum chart. ✓

**The bound (exact, elementary).** Tonelli: `∫∫ = ∫_A [∫_S ‖A·S‖^{−1} dS] dA`. Inner: `‖A·S‖² = Σ_{j=1}^{n}
⟨A, s_j⟩²` (`s_j` = columns of S, independent over the box); so `∫_S ‖A·S‖^{−1} dS = ‖A‖^{−1}·J(â)`,
`J(â) = ∫(Σ_j⟨â,s_j⟩²)^{−1/2}∏ds_j ≤ C_slab^{n}·∫_{ball}‖g‖^{−1}dg < ∞` **uniformly** over unit `â` (`n ≥ 2`
⟹ `‖g‖^{−1}` integrable; the `g_j = ⟨â,s_j⟩` have bounded density by the SLAB bound). Outer: `∫_A C·‖A‖^{−1}
dA < ∞` (`M₂ ≥ 2`, corank). So finite for `M₂ ≥ 2 ∧ n ≥ 2 = a+b ≤ ρ` (a=b=1) — exactly the free-box threshold.
(Verified: inner `J(â)` bounded+uniform for `n≥2`, diverges `n=1`; `couplerad` MC guide.)

**The ONE new fact (elementary):** the LINEAR-FORM SLAB `vol{s ∈ [−1,1]^{M₂} : |⟨â,s⟩| < ε} ≤ C·ε` uniform over
unit `â`. Proof: `max_k|â_k| ≥ 1/√M₂`; fix that coordinate, the interval has length `≤ 2ε/|â_k| ≤ 2ε√M₂`;
Fubini over the rest. NO SVD, NO det-polynomial anti-concentration, NO co-area. Banked-adjacent: `‖g‖^{−1}`
integrability (Japanese-bracket / corank), `∫_A ‖A‖^{−1}` (corankWeight-style).

**Route (C) SUBSUMES (for the b=1 charge free-box):** the bulk/interior split, schurB's `chargedWishartWeight`
atom + the Loewner bridge, my §w3-deep graded log + §w3-shellint σ_ρ-shells + intmtn's shell-integration — ALL
replaced by one Tonelli. **RECOMMEND adopting (C)** for the b=1 charge free-box (cheapest by far). The
non-spectral det-monotone stays foundational (used elsewhere); schurB's bridge may be reusable for `b≥2`.

**BONUS — (C) sidesteps ρ<n for b=1.** (C) needs only `M₂ ≥ 2` (outer) and `n ≥ 2` (inner) — NO rank-flag,
NO pivot, NO coordinate-P_J. So it closes b=1 `ρ<n` (`M₂ > n_last`) cases too, sidestepping the
coordinate-floor obstruction entirely. **The ρ<n deferred regime shrinks to `b≥2` only** (e.g. `(2,5,4)`,
b=2 — NOT covered by (C), still the general (D)). *(The 3 square dispatch witnesses are `ρ=n` anyway.)*

**⚠ ONE architectural CHECK (for corankrec/schurrec):** (C) closes the CHARGE free-box `∫∫ ‖A_cor·S‖^{−1}`
(charge alone, L¹) — corankrec's stated interior object. IF the interior closure needs the COUPLED
`∫∫ loss·charge` (loss and charge both functions of S, coupled near `{rank S low}`), then (C) gives the charge
piece and the coupling needs the per-S bound (my §w3-deep `W(S) ≤ C(1+log(1/|det S|))` × loss, then `∫_S`).
Per corankrec's reduction (loss absorbed → charge free-box), (C) is COMPLETE; confirm the loss is absorbed
upstream (not re-coupled in the interior). If it IS coupled, keep the §w3-deep per-S bound as the tool.

**Route (C) is `b=1`-specific** (charge `= ‖A_cor·S‖^{−1}`). For `b≥2` (matrix charge `det((A_cor S)(A_cor
S)ᵀ)^{−a/2}`) the S-first Tonelli inner is a matrix-variate integral — but schurB's banked `det_gram_cons`
(`det(gram(cons w u)) = det(gram u)·‖P⊥w‖²`) row-peels it to `charge = ∏_i ‖P⊥_i(A_i·S)‖^{−a}`, then a
per-residual slab — so the **S-first slab route LIFTS to b≥2 (= (D))**, same rank-flag-free structure. So:
b=1 → (C); b≥2 → (D)-via-S-first. The 3 square witnesses are all b=1,a=1 → (C).

**⟹ The ρ<n DEFERRED REGIME DISSOLVES.** The S-first slab route (C for b=1, D-via-`det_gram_cons` for b≥2)
sidesteps the rank-flag/rowspace floor for BOTH b=1 and b≥2 — the slab is on the LINEAR forms `⟨A_i,s_j⟩`,
no rank stratification of `S`. So the ρ<n coordinate-P_J obstruction (which was specific to the BULK-ATOM /
uniform-floor route) is OBVIATED everywhere; there is **NO separate ρ<n rowspace-floor build**. `(2,5,4)`
(b=2, ρ<n) is just the general (D)-via-S-first, closed by `a+b ≤ ρ` (corankrec-verified threshold, general b;
guide-confirmed jointly integrable). And the square uniform-I det-shell bridge (`loewner_floor_of_abs_det_ge`)
has **NO consumer post-(C)** — left banked as-is (correct, reusable), not gilded. Net architecture: ONE
S-first slab route closes the entire charge free-box (all b, all `a+b ≤ ρ` incl ρ<n); the bulk-atom + shells +
graded-log + coordinate/rowspace floors are all obviated.

---

### w3-Drec — the (D) b≥2 charge free-box: a CLEAN TWO-STEP (the coupling DISSOLVES; = (C) generalized)

*RESOLVED. (D) `∫∫_box det((A·S)(A·S)ᵀ)^{−a/2} dA dS`, `a+b ≤ ρ`, one witness `(2,5,4)`. My earlier "coupled
E-recursion" was an artifact of the WRONG decomposition (the A-ROW-peel via `det_gram_cons` IS coupled). The
**S-FIRST route dissolves the coupling** — (D) is a clean two-step, exactly (C) generalized from `‖A‖^{−1}` to
`det(A·Aᵀ)^{−a/2}`. NO E-recursion, NO pseudo-det, NO log, NO Cauchy–Binet, NO SVD. `couplerad_Dclean.py`.*

**The clean two-step (the recipe for schurB):**
- **INNER (the key per-step, exact scaling):** for full-row-rank `A` (`b×M₂`),
  `∫_{S ∈ box} det((A·S)(A·S)ᵀ)^{−a/2} dS  =  C(Q)·det(A·Aᵀ)^{−a/2}`, and `≤ C·det(A·Aᵀ)^{−a/2}` (`C` uniform).
  **Proof (non-spectral):** LQ-factor `A = R·Q` (`R` invertible `b×b`, `Q` `b×M₂` with orthonormal rows,
  `QQᵀ=I_b`; via Gram–Schmidt / Cholesky of `AAᵀ`, NO eigenvalues). Then `det(A·SSᵀ·Aᵀ) =
  det(R)²·det((Q·S)(Q·S)ᵀ)` and `det(R)² = det(RRᵀ) = det(A·Aᵀ)` (since `QQᵀ=I_b`), so
  `det((A·S)(A·S)ᵀ)^{−a/2} = det(A·Aᵀ)^{−a/2}·det((Q·S)(Q·S)ᵀ)^{−a/2}`. Integrate `S`:
  `= det(A·Aᵀ)^{−a/2}·C(Q)`, `C(Q) = ∫_S det((Q·S)(Q·S)ᵀ)^{−a/2} dS`. **`C(Q)` is FINITE iff `a+b ≤ n`** (the
  `b`-row Wishart on the box; `Q·S` is `b×n`) and **uniformly BOUNDED (two-sided) over orthonormal-row `Q`**.
  ⚠ `C(Q)` is **NOT a single `Q`-independent constant** — Codex (decorrelated) exhibits `b=1,M₂=2,n=2,a=1`:
  `C(q₁)=32 log(1+√2)≈28.20` vs `C(q₂)≈33.64` (the box is not rotation-invariant). What holds (and suffices)
  is `ℓ^n·K_{1/2} ≤ C(Q) ≤ L^n·K_{√M₂}` via the **projected-box DENSITY bound**: the pushforward density
  `f_Q(x) = 𝓗^{M₂−b}([−1,1]^{M₂} ∩ {s : Qs = x})` satisfies `f_Q ≤ L_{M₂,b} = ω_{M₂−b}·M₂^{(M₂−b)/2}` uniformly
  over `Q` (each fibre lies in a `(M₂−b)`-ball of radius `√M₂`; `√det(QQᵀ)=1`), and `≥ ℓ_{M₂,b}` near `0`.
  This DENSITY estimate — NOT Stiefel-compactness — is the Lean route to uniformity. (Verified numerically:
  `I(A)·det(AAᵀ)^{a/2}` bounded across well- and ill-conditioned `A`, spread = the `Q`-dependence,
  `couplerad_Dclean.py`.) So the `g`-scaling schurB asked for is exactly **`det(A·Aᵀ)^{−a/2}`** — clean, NOT
  the pseudo-det/`Z`-charge (the row-peel artifact); the `C(Q)` factor is a bounded orientation constant.
- **OUTER:** `∫_{A ∈ box} det(A·Aᵀ)^{−a/2} dA < ⊤` iff `a+b ≤ M₂` — this IS **schurB's `detGram_lintegral`**
  (the corank / `∫ det(XXᵀ)^{−a/2}` weight).
- **COMBINED:** `a+b ≤ n` (inner) ∧ `a+b ≤ M₂` (outer) ⟺ `a+b ≤ min(M₂,n) = ρ`. Sharp (verified: in-scope
  bounded, `a+b=ρ+1` diverges). **CLEAN — uniform inner × finite outer, no recursion.**

**Why the row-peel looked coupled (resolved):** `det_gram_cons` peels the `b` ROWS of `A·S`, and the per-row
residual `∫_{A_i}‖P⊥_{<i}(A_i·S)‖^{−a}` genuinely couples through `S` (grows as `S` degenerates). But that's
the wrong order — integrating **all of `S` first** (fixed `A`) gives the clean `det(A·Aᵀ)^{−a/2}` via the LQ
factorization, because the `S`-integral only sees `A` through `det(A·Aᵀ)` (the `R` factor), and the `Q`-part
integrates to a uniform constant. The nested-double-charge worry was wrong: the inner `S`-integral's
`A`-dependence is EXACTLY `det(A·Aᵀ)^{−a/2}`, which the outer absorbs (`a+b ≤ M₂`). The det-monotone
drop-samples shortcut is still too lossy (do not use); but it is not needed — the LQ route is clean.

**Lean recipe for schurB (all non-spectral, banked-adjacent):** (1) LQ / Cholesky of `A` (`A = R·Q`,
Gram–Schmidt of rows — Mathlib `gramSchmidt`); (2) `det(A·SSᵀ·Aᵀ) = det(R)²·det((Q·S)(Q·S)ᵀ)` (`det_mul` +
`det(RXRᵀ)=det(R)²det X`); (3) `det(R)² = det(A·Aᵀ)`; (4) the uniform inner `C(Q) = ∫_S det((Q·S)(Q·S)ᵀ)^{−a/2}
dS ≤ C` (a `Q`-uniform `b`-row Wishart-on-box bound — schurB's `det_gram_cons` + the b=1 slab, with the
projected-box density bound for uniformity); (5) OUTER = `detGram_lintegral` (banked). This closes `(2,5,4)`
and all b≥2 `a+b ≤ ρ`. **(D) is NOT a hard coupled recursion — it's (C) with `det(AAᵀ)^{−a/2}` for `‖A‖^{−1}`.**

**Decorrelated Codex (`codex/couplerad2-{prompt,answer}.md`, self-contained, my conclusion withheld) — CONCURS,
"all statements proved, not conjectured": VERDICT CLEAN two-step, no singular-value coupling, no recursion.**
Independently derived the identity `det((AS)(AS)ᵀ) = det(AAᵀ)·det((QS)(QS)ᵀ)`, `I(A)=det(AAᵀ)^{−a/2}C(Q)`
("all singular values enter only through `det(AAᵀ)`; no condition-number dependence"), the density-bound
uniformity (the `C(Q)`-nonconstant counterexample is Codex's), the `det_gram_cons`/Gram–Schmidt integrability
lemma (`det(YYᵀ)=∏dist², a<N−b+1`, no Cauchy–Binet), and the **`iff`** threshold `a+b ≤ min(M₂,n)` WITH
NECESSITY (inner fails ⟹ `I(A)=∞ ∀` full-rank `A`; outer fails ⟹ the uniform `C(Q)` lower bound blocks
compensation). So `a+b ≤ ρ` is sharp both ways.

---

### w3-deep-spec — Lean-ready tight-interior spec for the formaliser (intmtn), SQUARE witnesses (b=1,a=1)
*(SUPERSEDED for the b=1 charge free-box by §w3-routeC above — kept as the per-S bound in case the interior
needs the coupled loss·charge, or for cross-checking.)*

*The interior closure `∫_S W(S)·[S-measure] < ⊤` (charge free-box; the loss is the separate banked `mnp`
factor, finite). For the 3 square witnesses `S = Z_deep` is `M₂×M₂` square, `ρ = M₂`, `a=b=1`. NO SVD needed
— everything via `det S` (the det-minor) + the box. Exact-verified `couplerad_deeplog.py`.*

1. **The charge weight `W(S)` (exact) + the tight bound.** `W(S) = ∫_{A_cor ∈ matBox 1 M₂ 1} ‖A_cor·S‖^{−1}
   dA_cor` (b=1,a=1: `A_cor` a `1×M₂` row, charge `= det((A_cor S)(A_cor S)ᵀ)^{−1/2} = ‖A_cor·S‖^{−1}`).
   **Tight bound:** `W(S) ≤ C·(1 + log(1/|det S|))`, with `C = C(M₂)` from the `arcsinh` integral (`C =
   2·(∏ over the M₂−1 order-1 directions) · vol`, a fixed box constant; explicitly the `Cresid`-analog of the
   `∫∫(x²+σ²y²)^{−1/2}` computation). σ_ρ is expressed via the det-minor: `σ_min(S) ≥ |det S|/M^{M₂−1}` on the
   box (`M = σ_max ≤ M₂`), so `log(1/σ_min) ≤ (M₂−1)log M + log(1/|det S|)` — hence the `log(1/|det S|)` form,
   NO singular values.
2. **The `σ_ρ`-measure CoV — direct via the `det S` pushforward (NO co-area formula).** For the square case
   `c = (M₂−ρ+1)(n−ρ+1) = 1`, so use the pushforward of `t = det S` under the box: `∫_S g(|det S|) dS =
   ∫_ℝ g(|t|)·ν(t) dt`, `ν(t) =` the density of `det S` under the uniform box measure, **BOUNDED near `t=0`**
   (`det S` is a polynomial with a.e.-nondegenerate gradient on `{det S = 0}`; `ν(0) < ∞`). So the shell
   Jacobian is just `ν(t)` bounded — no `ε^{c−1}` weight beyond the (trivial, `c=1`) constant. (For `ρ<n`,
   `c>1` and `ν(t) ~ |t|^{c−1}`, even more convergent — but that's the `ρ<n` case, deferred.)
3. **Convergence.** `∫_S W(S) dS ≤ C·∫_{|t|≤δ₀}(1 + log(1/|t|))·ν(t) dt < ⊤` since `ν` bounded and
   `∫_0^{δ₀}(1+log(1/t)) dt = δ₀(2−log δ₀) < ∞`. **Recommended Mathlib route:** the `σ^{−κ}` domination
   (`log(1/t) ≤ C_κ·t^{−κ}` for `t∈(0,1)`, any `κ∈(0,1)`) → `∫_0^{δ₀} t^{−κ} dt < ∞` via
   `integrableOn_rpow`/`intervalIntegrable_rpow` (`κ<1`), avoiding `Real.log`-integrability API entirely. (If
   you prefer `Real.log`: Mathlib has `integrableOn` of `log` on bounded intervals — either works; the
   `t^{−κ}` route is more uniform across `c`.)

**Doc/branch:** cert `§w3-deep` + `§w3-shellint` + this `§w3-deep-spec`; scripts `couplerad_deeplog.py`
(the exact `arcsinh→log`), `couplerad_shellint.py` (the shell accounting), on
`origin/worktree-agent-a0bd7f4f9aa5ce4f8`. The exact `arcsinh` computation: `∫_0^1(x²+σ²y²)^{−1/2}dx =
arcsinh(1/(σy)) → ln(2/(σy))`, `∫_0^1 ln(1/(σy))dy = 1−ln σ` ⟹ `W ~ ln(1/σ)`. The `(3,4,5,4)` a=1,b=2 tight
form (and the `ρ<n` cases) I pin when reached.

---

### w3-interior — the interior loss integral: the coupled loss DECOUPLES + is a pure box-RLCT (per-p finiteness)

> **CORRECTION (see §w3-boundary).** ★2 below gives the correct PER-P finiteness (∫_x < ∞ iff 2q < ρ,
> generic z0). But ★5's "p-UNIFORM bound over interior cells" is UNSOUND: arch1build/intloss measured
> `frontLossIntegral(p) ~ σ_min(L_p)^{−2q} → ∞` at the loss-degeneracy locus (z0→0), so there is NO
> p-independent bound `D`. The interior closes as the COUPLED integral `∫_p charge(p)·frontLossIntegral(p)`
> in §w3-boundary. The proven arithmetic `minAdm M ≤ M₀·min(M₁,ρ_d)` (★5) stands as a QIP fact; it just is
> not the interior's closure.

**Object.** After arch1build's front-charge factorization, the interior closes iff
`I_loss(p) = ∫_x (E_top + E_tr)^{−q}` is uniformly bounded over interior cells (`a+b ≤ ρ_d = deepTailMin`),
`q = c' − ab/2`, `x = (P,B₁₂,C) ∈ outerDom` — the BOUNDED box `[−1,1]^{u×u}×[−1,1]^{u×b}×[−1,1]^{a×u} ∩
{IsUnit P}` (`T=1`; corankrec-verified verbatim `RouteMSJChartShear:185`). corankrec's forms:
`E_top = frobSq(P·Q_inl + B₁₂·Q_b)`, `E_tr = frobSq(C·Q̃ₚ·Π)`, `Q̃ₚ = Q_inl + P⁻¹B₁₂Q_b`,
`Π = 1 − Q_bᵀ(Q_bQ_bᵀ)⁻¹Q_b`. `Q_inl=(z0)·Z_deep` (u×n), `Q_b=A_cor·Z_deep` (b×n), `Z_deep` rank `ρ_d`.

**★1 The loss DECOUPLES (E_tr is pure-C).** Since `Q_b·Π = 0`, `Q̃ₚ·Π = Q_inl·Π` (the `P⁻¹B₁₂Q_b·Π` term
vanishes), so **`E_tr = frobSq(C·Q_inl·Π)`** — independent of `(P,B₁₂)`. Verified to machine ε (corankrec +
`couplerad_interior.py`). [Equivalent M/D derivation: `E_tr = frobSq(D·M·Π)`, `M=W_top·Z_deep`, `D=C·P⁻¹`,
`M·Π = P·Q_inl·Π` ⟹ `E_tr = frobSq(C·Q_inl·Π)`.] So `f := E_top + E_tr` splits: `E_top` on the `(P,B₁₂)`
block, `E_tr` on the `C` block.

**★2 f is a PSD quadratic on the box; the integral is a pure RLCT threshold.**
`E_top = ‖[P|B₁₂]‖²_{G_stack}` (`G_stack = [Q_inl;Q_b][Q_inl;Q_b]ᵀ`), `E_tr = ‖C‖²_{KKᵀ}` (`K = Q_inl·Π`).
As a quadratic in `vec(P,B₁₂,C)`, `f = zᵀHz`, `H ⪰ 0`, `rank H = u·r_stack + a·r_K` (`r_stack =
rank[Q_inl;Q_b]`, `r_K = rank K`; via `vec(XS)=(Sᵀ⊗I)vec X`, `rank(AᵀA)=rank A`). **On the BOUNDED box there
is NO decay/∞ constraint — the sole condition is near-zero-set (RLCT) integrability:**
> `I_loss(p) < ∞  ⟺  2q < u·r_stack + a·r_K`   (RLCT of a rank-ρ PSD quadratic = ρ/2).

NO lower q-window. (The earlier `q > au/2` was an unbounded-`C` artifact of the Gaussian β-formula; `C` is
BOXED, so no `∞`-tail.) Excluding `{det P=0}` (IsUnit P) is measure-zero, does not move the threshold
(Codex Q1(d)).

**★3 The ranks on the interior cell.** `r_stack = min(u+b, ρ_d) = min(M₁, deepTailMin)` (since `u+b = M₁`);
`r_K = r_stack − b` (`Q_b` full rank `b` ⟹ `rank(Q_inl·Π) = rank[Q_inl;Q_b] − rank Q_b`). Both verified
(`couplerad_interior.py`, machine ε). So `u·r_stack + a·r_K = (a+u)·r_stack − ab = M₀·r_stack − ab`, and
`2q < M₀·r_stack − ab` with `q = c'−ab/2` collapses to
> **`I_loss(p) < ∞  ⟺  c' < M₀·min(M₁, deepTailMin)/2`.**

**★4 E_top is load-bearing exactly on the gap `a·r_K/2 ≤ q < (a·r_K+u·r_stack)/2`** (Codex Q1(c); matches
corankrec's S2 + Codex's earlier `∫E_tr^{−q}=∞` counterexample): the `C`-only integral
`∫_box frobSq(C·K)^{−q}` diverges for `q ≥ a·r_K/2` (on `ker(C↦CK)`), but `E_top` floors it there. Drop
`E_top` → divergence.

**★5 The uniform bound — NO WALL, ∀-M PROVEN.** `c'` is capped by `carrierThreshold M = ½·minAdm M`. So the
uniform bound over interior cells holds iff `½minAdm M ≤ M₀·min(M₁,ρ_d)/2`, i.e.
> **`minAdm M ≤ M₀·min(M₁, deepTailMin)`.**

PROVEN ∀-M constructively (`couplerad_minadm_proof.py`; verified exact, 0/7536 interior cases). `minAdm M =
min_{T∈Adm} Mval`; exhibit an admissible `T` with `Mval(M,T) ≤ M₀·min(M₁,ρ_d)`. Let `ρ = M_{k*}`, `k*` least
in `{2..L}` with `M_{k*}=ρ`. **Easy half (`M₁ ≤ ρ`):** `T≡0` ⟹ `Mval = M₀·M₁ = M₀·min(M₁,ρ)`. **Hard half
(`M₁ > ρ`):** the running-min-then-drop `T*`: `t^j = min(M₀,…,M_{j+1})` for `j ≤ k*−2`, `t^j = 0` for
`j ≥ k*−1`. Admissible (running-min weakly decreasing, `≤ admBound`, last `=0`). Telescoping: every term
`j ≤ k*−2` is `0` (consecutive running-mins equal, or the width factor `0`); `j > k*−1` all-zero; only
`j = k*−1` survives `= t^{k*−2}·ρ = min(M₀,…,M_{k*−1})·ρ ≤ M₀·ρ = M₀·min(M₁,ρ)`. ∎ Tight in 295 cases
(arity 3-4) but never violated; both bounds STRICT-`<`, so tight still converges (open window).

**LANDED (corankrec @e9e262341, `RouteMSJCorankRec`):** `minAdm_le_head_mul_min_deepTailMin (M) : minAdm M ≤
M 0 * min (M 1) (deepTailMin M)`, green + native (`[propext, Classical.choice, Quot.sound]`). It went via the
banked `minAdm_le_head_mul_tailInf` (`minAdm M ≤ M₀·⨅_{i≥1}Mᵢ`, proven by permutation-invariance moving the
argmin tail width to position 1) reformulated `⨅_{i≥1}Mᵢ = min(M₁, deepTailMin M)` — 6 lines, no T* fold.
The interior arithmetic was already a banked minAdm property. My constructive T* (running-min-then-drop,
`Mval(T*) = min(M₀,…,M_{k*−1})·ρ`, actually SHARPER) is the DECORRELATED confirmation — both routes + two
independent scans (mine 1292 interior cells arity 3-4; corankrec's 19551 cells arity 3-5 widths 1-7) agree,
0-failure. So (A)'s uniform bound rests on a PROVEN ∀-M inequality.

**Decorrelated Codex (Q1, `xhigh`, self-contained, conclusion WITHHELD): CONCURS** — rank
`ρ = u·r_S + a·r_K`, threshold `q < ρ/2`, load-bearing gap `a·r_K/2 ≤ q < (a·r_K+u·r_S)/2` nonempty iff
`r_S>0`, singular-X irrelevant (`codex/couplerad-interior-{prompt,answer}.md`).

**Lean-mechanism map.** `I_loss(p)` is ONE-SHOT (does NOT interact with satred's `a≥u` charge recursion — it
is the loss-side, pulled out). Formaliser needs: (i) decoupling `E_tr = frobSq(C·Q_inl·Π)` (algebraic,
`Q_b·Π=0`); (ii) `f = ‖[P|B₁₂]‖²_{G_stack} + ‖C‖²_{KKᵀ}` PSD quadratic, `rank = u·r_stack + a·r_K`
(Kronecker + `rank(AᵀA)=rank A`); (iii) box-RLCT of a PSD quadratic (`∫_box q^{−s}<∞ iff s<rank/2`) — a
Morse/monomial-normal-form or a direct radial bound on the `ρ` nondegenerate directions; (iv) the rank
formulas `r_stack=min(M₁,ρ_d)`, `r_K=r_stack−b` on the cell-generic locus (corankrec's atlas); (v) the QIP
arithmetic `minAdm M ≤ M₀·min(M₁,ρ_d)` (★5, corankrec). **Trap:** keep the box bounded — do NOT extend `C`
to ℝ and invoke the β-formula (it spuriously introduces a lower q-window). **Owner:** corankrec / schurrec
(the `ρ=n` resolved-chart consumer).

---

### w3-edgeR3 — the b≥2 edge (`a+b=ρ_d+1`): R3 DISSOLVES = (b−1)-Γ-column peel [(D)-boundary] + b=1 coupled leaf (NO new measure theory)

**Object (edgered's COUPLED route, no explicit charge factor).**
`coupledBoxIntegrand = ∫_x∫_Γ (freedSchurLoss)^{−c'}`, `freedSchurLoss = W + frobSq(C·Q̃ₚ + Γ·Q_b)`,
`W = frobSq(P·Q̃ₚ)` (pivot energy, `C,Γ`-free), `Q_b = A_cor·Z_deep` (`b` corank rows), `Γ` the freed `a×b`
variable. The edge is `a+b = ρ_d+1`; the FULL `b`-block charge `det(Q_bQ_bᵀ)^{−a/2}` diverges there
(`a+b > ρ_d`).

**★1 The Γ-integral IS the charge pull-out (unifies (A)/(B)).**
`∫_Γ (W + frobSq(C·Q̃ₚ + Γ·Q_b))^{−c'} dΓ = det(Q_bQ_bᵀ)^{−a/2}·β(ab,c')·(W + frobSq(C·Q̃ₚ·Π))^{−(c'−ab/2)}`
[`Γ↦ΓQ_b` onto `a×rowspace(Q_b)`, Jac `det(Q_bQ_bᵀ)^{a/2}`, Π-split via `Q_bΠ=0`]. With `q = c'−ab/2`,
`W = E_top`, `frobSq(C·Q̃ₚ·Π) = E_tr`, this IS arch1build's factorization
`= det(Q_bQ_bᵀ)^{−a/2}·β·I_loss(p)`. So the coupled route and the (A) interior are the SAME computation; the
full `b`-pull's charge is the divergent trap.

**★2 R3 = peel only `b−1` Γ-columns (the SAFE rows).** Split `Γ = [Γ' | γ_last]`, `Q_b = [Q_b'; q_last]`
(`Q_b'` = top `b−1` rows, full rank `b−1`). `Γ·Q_b = Γ'·Q_b' + γ_last·q_last`.
- STEP 1 (exact Gaussian, EQUALITY): `∫_{Γ'} (W + frobSq(C·Q̃ₚ + Γ'Q_b' + γ_last q_last))^{−c'} dΓ' =
  det(Q_b'Q_b'ᵀ)^{−a/2}·β(a(b−1),c')·(W + frobSq((C·Q̃ₚ+γ_last q_last)·Π'))^{−c''}`, `Π'` = ⊥-proj off
  `rowspace(Q_b')`, `c'' = c' − a(b−1)/2`.
- STEP 2 (edgered's a-fortiori, ≤): fragile direction `q̃_last := q_last·Π'` (`q_last` ⊥ the `b−1` peeled
  rows), `σ = ‖q̃_last‖`, `ω = q̃_last/σ`. Project onto `ω`: `frobSq((C·Q̃ₚ+γ_last q_last)Π') ≥ ‖C·v' +
  σ·γ_last‖²`, `v' = Q̃ₚ·Π'·ω` — EXACTLY edgered's `corank_afortiori` b=1 form (`v→v'`, `γ→γ_last`,
  `c'→c''`).
> `coupledBoxIntegrand(b) ≤ det(Q_b'Q_b'ᵀ)^{−a/2}·β(a(b−1),c')·[edgered's LANDED b=1 leaf at exponent c'']`.

**★3 WHY NO WALL.** `det(Q_b'Q_b'ᵀ)^{−a/2}` is the (D) charge at `(a, b−1)`; in the deep integral it is
FINITE iff `a+(b−1) ≤ ρ_d ⟺ a+b ≤ ρ_d+1 = the IMMEDIATE EDGE` (the (D) BOUNDARY — slabD's
`corankSlabD_charge_sint_le` @aa4319774 closes exactly this). The last (would-be-divergent) row is NOT
charged — it is edgered's `b=1` coupled leaf where `W` floors the fragile `v'`-direction. edgered confirmed
the arithmetic: the edge window `c' > ab/2` gives `c'' = c'−a(b−1)/2 > a/2`, i.e. `a < 2c''` STRICTLY —
exactly the `b=1` leaf's finiteness threshold (`scaledRadialEuclid_lt_top`, open window). So **R3 =
(D)-at-boundary [(b−1) block] + edgered's b=1 leaf [last row]**, no new measure theory; the `a_b↔C` coupling
survives cleanly into `v'`.

**Decorrelated Codex (Q2, `xhigh`): CONCURS** — the `(b−1)`-Γ Gaussian identity, `det(BBᵀ)^{−a/2}` Jacobian,
the exact `Cst = π^{a(b−1)/2}Γ(c'−a(b−1)/2)/Γ(c')`, convergence `c' > a(b−1)/2`, and `c'' = c' − a(b−1)/2`
(`codex/couplerad-interior-{prompt,answer}.md` Q2). **Owner:** edgered (b=1 leaf, LANDED) + slabD/arch1build
((b−1)-block detGram at boundary). **Scope (corankrec binding-cut scan):** the b≥2 strict-edge IS reached
(witness `(3,3,3,4)@t=1`, 110 witnesses) but the deep-corank tower is EMPTY — R3 is the immediate-edge
(single-level `(b−1)` peel) case ONLY.

---

### w3-boundary — the interior COUPLED ∫_p estimate (loss-degeneracy): the CORRECTED interior closure

**Object.** `frontCharge = ∫_{z0} charge(z0)·frontLossIntegral(z0) dz0` (a COUPLED integral over the deep var
`z0`, NOT a factored `D·chargeFreeBox`). `frontLossIntegral(z0) = ∫_x (E_top+E_tr)^{−q}dx` (the §w3-interior
box-RLCT, finite per generic z0, BLOWS UP at z0→0). `charge(z0) = det(Q_inr Q_inrᵀ)^{−a/2}` (bounded near
z0=0). `z0` = the u×M₂ leading-deep block, `dim z = u·M₂`.

**★1 The blow-up pole (EXACT, eigenvalue-scaling).** As `z0 = δg → 0`, the loss quadratic `H(z0)` (rank
`ρ = u·r_stack + a·r_K`, `r_stack = min(M₁,ρ_d)`, `r_K = r_stack − b`) has `k` eigenvalues scaling as `δ²`:
E_top contributes `u·r_K` (the Q_inl-block, via the Schur complement `δ²·Q_inl'ΠQ_inl'ᵀ` off the `b` O(1)
Q_b-directions); E_tr contributes `a·r_K` (all of `KK ~ δ²`). So `k = (u+a)·r_K = M₀·r_K`, and
> `frontLossIntegral(z0) ~ ‖z0‖^{−P}`,  **`P = 2q − ρ + k = 2q − u·b`**  (`r_stack − r_K = b`).

Matches the witness `(4,4,4,4)@u3, a=b=1, c'=4.9` EXACTLY: `2q=8.8`, `ub=3` ⟹ `P=5.8`
(`couplerad_boundary.py`: `2q−ρ+k == 2q−ub` verified across cells). The pole is UNIFORM over all radial
directions `g` (any rank — `couplerad_boundary_strata.py`). [This is the `ℓ=u` deep stratum; the actual
binder is stratified — see ★2.]

The full-degeneration locus is `{Q_inl·Π = z0·Z_deep·Π = 0}` (⊇ both `{z0=0}` and `{z0·Z_deep=0}`), codim
`u·d`, `d := rank(Z_deep·Π) = ρ_d − b`. The clean route (★6) resolves the whole `∫_p` via the arity-3 base
case, giving the condition directly; ★2's hand-stratification was an intermediate step (error-prone — see the
caveat).

**★2 The condition — `2q < u·b + minAdm((u+a, u, d))`** (via the arity-3 reduction ★6; `d = ρ_d − b`). The
`B̃`-decoupling (`B̃ = B₁₂ + P·Ã_z`, `Ã_z = Q_inl·Q_bᵀ(Q_bQ_bᵀ)⁻¹`) gives `E_top = frobSq(P·Y) +
frobSq(B̃·Q_b)`, `E_tr = frobSq(C·Y)`, `Y := Q_inl·Π = z0·Z_deepΠ` (u×n, rank ≤ d) — verified machine ε
(`couplerad_verify_strata.py`). So `∫_p` reduces (★6) to the arity-3 (□) of chain `(u+a,u,d)` + a free
`ub`-Gaussian, finite iff:
> **`2q < u·b + minAdm((u+a, u, d))`**  (`= u·b + Λ`, `Λ` = the two-layer RLCT-numerator of `(u+a,u,d)`).

Codex-confirmed `Λ = minAdm((u+a,u,d)) = min_{0≤r≤min(u,d)} {u·d + r² + (a−d)r}` (0 mismatch / all configs).
[CAVEAT — a corrected error: my earlier hand-stratification `2q < min_ℓ φ(ℓ)`, `φ(ℓ)=ρ₀+ℓ²+(d−2u−a)ℓ`, used
`c_ℓ = ℓ(d−u+ℓ)` WITHOUT the absolute value; it agrees with `u·b+Λ` only for `d ≥ u` and is WRONG for
`d < u` (Codex counterexample `u=3,a=0,d=1`: `φ`-min `−1` vs `Λ=3`). The correct determinantal codim is
`ℓ(|u−d|+ℓ)`, and the clean arity-3 route ★6 avoids the hand-stratification entirely. The scripts
`couplerad_truecond/peelfamily/reduce3.py` used `|u−d|` and are correct.]

**★3 The ∀-cell condition — interior CONVERGES, NO obstruction; QIP CLOSED (landed).** With the cap
`c' < ½·minAdm M`, `∫_p<⊤` at every interior cell iff
> **`minAdm M ≤ a·b + u·b + minAdm((u+a, u, d))`** — VERIFIED 0 fails / 12720 interior cells
> (`couplerad_final.py`); tight (margin 0) in some cells but STRICT-safe.

CERTIFIED by corankrec's LANDED full-min corollary `minAdm_le_inf_pivot_qip` @a070b639a:
`minAdm M ≤ ⨅_{u'≤min(M₀,M₁)} [(M₀−u')(M₁−u') + u'·ρ_d] ≤ a·b + u·b + minAdm((u+a,u,d))` (the second `≤`
verified 0-fails / 12720). So the entire interior arithmetic is closed by the landed QIP — no new lemma.

**★4 intloss's crude σ_min bound is NOT p-integrable (why the joint route).** `frontLossIntegral(p) ≤
σ_min(L_p)^{−2q}·C` is tight per-p, but `σ_min(L_p)` vanishes on the codim-1 locus `{rank[Q_inl;Q_b]<u+b}`
(`σ_min ~ dist`), so `∫_p σ_min^{−2q}` DIVERGES for `2q ≥ 1` — a FALSE divergence (the TRUE `∫_p` converges;
at a generic corank-1 point `pole′ = 2q−ρ₀+(u+a)`, integrable over codim 1 iff `pole′ < 1`, and `<0` for the
dispatch cells). So the coupled `∫_p` does NOT bolt on a sharp per-p bound (route (c), avoided); it is the
**JOINT monomial resolution** over `(z0,x)` (via the M/D CoV `f = frobSq(M) + frobSq(D·M·Π)`), fed by
intloss's per-p FINITENESS + rank lemma. Confirmed with intloss (its (a)+(b) are the right scope).

**★5 Opens (mostly closed).** dim `z0 = u·M₂` CONFIRMED (corankrec — z0 fully integrated; the pivot `P` is a
separate front-block var, not a sub-block of z0). charge `z0`-INDEPENDENT CONFIRMED (`Q_inr = Q_b =
A_cor·Z_deep`, `Z_deep` = deeper layers, no z0 → `det(Q_bQ_bᵀ)^{−a/2}` constant, no competing pole).
width-caveat RESOLVED (single width `d`, Codex B̃-decoupling). QIP CLOSED (★3, multi-pivot form A — no new
lemma). And the transverse-stratum criterion REDUCES TO THE ARITY-3 (□) BASE CASE — see ★6.

**★6 The transverse-stratum criterion = the arity-3 (□) base case (NOT a new monument).** Via the
B̃-decoupling, the loss depends on `z0` ONLY through `Y := z0·Z_deep·Π` (u×d): `E_top = frobSq(P·Y) +
frobSq(B̃·Q_b)`, `E_tr = frobSq(C·Y)`. The map `z0 ↦ Y = z0·(Z_deepΠ)` is a linear surjection onto u×d
(Jacobian const; the u·(M₂−d) kernel directions integrate freely over the box). So `∫_p` reduces to
`∫_{Y,P,C,B̃} (frobSq(E·Y) + frobSq(B̃·Q_b))^{−q}`, `E := [P;C]` ((u+a)×u) — this is the **arity-3 (□)
loss-integral** of the reduced 2-layer chain `(u+a, u, d)` (product `E·Y`, (u+a)×d through the middle dim u)
× a free ub-dim Gaussian block `‖B̃Q_b‖²`. Its RLCT-numerator is `u·b + minAdm((u+a, u, d))`. So the interior
"loss-degeneracy" is the recursion peeling `z0` (the leading deep layer M₁→M₂) and BOTTOMING INTO the
arity-3 (□) base — no separate determinantal-RLCT monument.

**Codex CONFIRMS the reduction (consult 4, `codex/reduce-{prompt,answer}.md`), with two domain caveats it
resolves.** R1 (`B̃`-orthogonal split): correct (cross term `tr(P·Y·Q_bᵀ·B̃ᵀ)=0` via `Π·Q_bᵀ=0`); the
integrand factors through `Y`, though the shifted `B̃`-domain depends on `z0`. R2 (surjection): correct; the
`z0`-box image is a zonotope, NOT a literal product box. R4 (suspension): free block adds `ub/2` to the RLCT.
**These caveats do NOT break finiteness:** the transformed domain is contained in a bounded product box AND
contains a product neighborhood of `(Y,K,B̃)=0`, with constant Jacobian, so by INNER/OUTER comparison the
`∫_p` has EXACTLY the same finiteness threshold as the rectangular arity-3 loss integral (`0` is an interior
point → the `Y`-image boundary adds no singularity). And `min_ℓ φ − ub = Λ` for `d ≥ u`; for `d < u` my
hand-`φ` was wrong (★2 caveat) but `Λ = minAdm((u+a,u,d))` is right for all `d` (0 mismatch). So the
reduction dissolves the stratification, is valid for FINITENESS via bounded-domain comparison, and the
strata-independence question is SUBSUMED into the (banked) arity-3 (□) closure — Codex-verified.

**Lean target (corankrec-mapped from the code, all pieces banked/landed):** `∫_p` = [R1 Frobenius-orthogonal
split (`Q_b·Π=0` + E_top/E_tr forms, banked)] + [R2 linear CoV, unit-Jac, free kernel + `rank(Z_deepΠ)=ρ_d−b`
(cellRank/atlas)] + [**R3/R4 = the residual-power +ub chaining** (below)] + [threshold via
`minAdm_le_inf_pivot_qip`]. Composes with `frontCharge_cell_lt_top_of_freebox` + `hGae_cell_interior`.

**R3/R4 in detail (corankrec's code-level sharpening — the `+ub` is the real content, NOT the scale).** The
free `ub`-Gaussian `‖B̃Q_b‖²` is LOAD-BEARING: dropping it (`(‖EY‖²+‖B̃Q_b‖²)^{−q} ≤ (‖EY‖²)^{−q}`) gives only
`2q < minAdm(![u+a,u,d])`, MISSING the `+ub` — and `ab + minAdm(![u+a,u,d])` alone can fall short of `minAdm M`
(the QIP needs `ab+ub+minAdm`). The `+ub` comes from a RESIDUAL-POWER shift on the B̃-Gaussian:
`∫_{B̃∈box}(c+‖B̃Q_b‖²)^{−q}dB̃ ≤ C·c^{−(q−ub/2)}` for `2q>ub` (and `≤ C` bounded for `2q≤ub`), `c=frobSq(EY)`,
`C` uniform in `(E,Y)` (verified `couplerad_residual.py`: slope `= ub/2−q` exactly for `2q>ub`, `~0` for
`2q≤ub`). By Tonelli this `= C·(RectSchurCore integrand at exponent q−ub/2)`, so it plugs straight into
`rectCore_schurGen_lt_top (u+a) u d (q−ub/2) … T (max radii)` (finite iff `q−ub/2 < ½·minAdm(![u+a,u,d])` — by
`rectSchurLambda d = ½·minAdm(![·]) by rfl`). So **R3/R4 = residual-power-atom (`radial_morse_residual_power_le`,
the `−ub/2` shift) ∘ `rectCore_schurGen_lt_top`(q−ub/2) ∘ Tonelli**, with the `2q≤ub` (bounded) vs `2q>ub`
(residual-power) split; union = `2q < ub + minAdm(![u+a,u,d])`. Both endpoints banked; the genuine analytic
wiring is the Tonelli interchange + the uniform-in-(E,Y) residual bound + the 2-case split.

**★7 The inner/outer bounded-domain comparison (CORRECTED TWICE — the domain/scale step is FREE; the real analytic step is R3/R4).**

⚠️ SELF-CORRECTION. An earlier draft of ★7 claimed a trivial "germ at `{0}`" lemma (`h` loc-bounded off the
single point `0`). That is WRONG: the singular locus of the reduced integrand is the DETERMINANTAL CONE
`Σ = {loss=0} = {E·Y=0, B̃=0}` (positive-dimensional), and the inner integral `h(Y) =
∫_x(‖EY‖²+‖B̃Q_b‖²)^{−q}dx` is `+∞` on the whole locus `{rank Y < u}` (numerically: for `2q ∈
[(u+a)(u−1)+ub, (u+a)u+ub)`, `h=+∞` on `{rank Y<u}` — `couplerad_domain.py`). So `h` is NOT loc-bounded off a
point; the point-germ lemma does not apply.

*The correct reduction* (Φ-Fubini + box-sandwich; scale is FREE — corankrec code-check):
- **Φ-Fubini.** `z0 = v ⊕ k` (`v∈V≅ℝ^{ud}`, `Φ|_V` iso `|det|=J`; `k∈ker Φ`, dim `u(M₂−d)`). The integrand
  `H(z0,x)` depends only on `(Y=Φ|_V(v), x)`, so `∫_{z0-box×x-box}H = ∫_{k}[∫_{v,x}H(Φ|_V(v),x)]` — the `k`
  directions integrate to a FINITE volume (bounded box), leaving `J⁻¹·∫_{Y∈𝒫, x-box}H(Y,x)` over a `Y`-PARALLELEPIPED
  `𝒫 = Φ|_V(v-box)`.
- **Box-sandwich, and SCALE IS FREE.** `[−c₁,c₁]^{ud} ⊆ 𝒫 ⊆ [−c₂,c₂]^{ud}` (`𝒫` bounded, `0` interior); then
  `lintegral_mono_set` sandwiches `∫_𝒫` between the two box integrals. And the box RADIUS is FREE: corankrec
  verified in the code (`RouteMSchurRect:119-120`) that `rectCore_schurGen_lt_top` concludes `RectSchurCore m n p
  c' T` for **∀ T>0** (the `1 one_pos` in `routeMBoxThresholdFinite_mnp` is the ONLY place `T=1` enters — swap it
  for `T hT`). So the arity-3 (□) finiteness holds at any box radius; NO scale-independence lemma is needed. (My
  earlier draft mislocated the substantive step here — scale is a non-issue.)

*Net:* `∫_p < ∞ ⟺` the rectangular arity-3 (□) integral `< ∞`, via Φ-Fubini + `lintegral_mono_set` box-sandwich
+ `rectCore_schurGen_lt_top ∀T`. **HONEST STATUS (corrected twice):** the domain/scale step is NOW FREE (not the
point-germ of draft 1, not the scale-independence lemma of draft 2 — both superseded). The ONE genuine analytic
step is NOT here but in **R3/R4 (the `+ub` residual-power chaining, see the R3/R4-detail block above)**: the
Tonelli interchange + the uniform-in-(E,Y) residual-power bound `∫_{B̃}(c+‖B̃Q_b‖²)^{−q}dB̃ ≤ C·c^{−(q−ub/2)}` +
the `2q≤ub` vs `>ub` split. That chaining (composing `radial_morse_residual_power_le` with
`rectCore_schurGen_lt_top(q−ub/2)`) is where Finding-7's premise review should aim — NOT the scale.

**Owner:** intloss (rank lemma + per-p finiteness) + me (the joint `∫_p` reduction, Codex-confirmed) +
corankrec (QIP landed + the Lean assembly). The interior CONVERGES ∀-cell (no obstruction); the Lean closure
is the assembly of banked pieces above + the bounded-domain comparison. This completes the interior design.

**Decorrelated Codex (4 consults total, `xhigh`, conclusion WITHHELD): CONCUR + SHARPEN.** (1)
`boundary-*`: pole `P=2q−ub`, crude-σ_min NON-integrable. (2) `strata-*`: the stratified structure +
width-caveat resolution via B̃-decoupling (also surfaced the intermediate-ℓ binding — later subsumed by the
reduction). (3) `couplerad-interior-*` (Q1/Q2): the per-cell RLCT + the edge (b−1)-Gaussian. (4) `reduce-*`:
the arity-3 reduction CONFIRMED (with the bounded-domain caveats + the `d<u` correction of my hand-`φ`).

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
