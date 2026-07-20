# Cert — the LeafPullback loss-factorization kill-condition (pnp-loss)

*Seat: `pen-and-paper` (pnp-loss, adjudication direction), expedition 2026-07-17-aoyagi-engine.
Paper certificate only — NO Lean edits (reading Lean statements is fine). Exact `sympy` /
exact rational; MC never used. Batteries in `scripts/*.py` (all exit-0). Decorrelated Codex leg
(`codex/loss-factorization-{prompt,answer}.md`, xhigh, hypothesis WITHHELD — frame-in/facts-in/
hypothesis-out; both its witnesses re-verified exactly in my battery, `scripts/verify_codex_witnesses.py`).
Pinned to Aoyagi pp.15–22 (the diag(b) invariant, the u/d pivot charts, the Q/P normalization),
`EngineDefs.lean:43–48` (LeafPullback), `cert-psi-mix.md` §R-b (the source gauge α),
`verify-r1-shortcut.md` (the §8 refutation / depth-recursion), `ShearReconcile.lean:23–28,93–120`.*

---

## VERDICT: **HOLDS-WITH-CONDITIONS** — equivalently, **FALSE for the present `chartMap`, TRUE for the diagonal-normalized (fork-15) *and* incidence/Q,P-normalized composite.**

**Scope (elder charge-2 re-point).** The primary target is the **diagonal-normalized** construction
(fork-15: the cube-invariant source swap `S_pivot = (cNodeOf(pivot) ↔ divBirthCoord diagonal)`, so every
chart births its divisor at the state-level `divBirthCoord` diagonal). The residualCore-leak hunt below
is adjudicated on those corrected charts (my chart model's u-scaling coordinate = the divisor's
`divBirthCoord` cell = birth = reference, in every copy). **§6 is the appendix confirming the
off-diagonal loss contagion on the *current* charts** (corroborating the ruling). **Headline of the
re-point: the loss needs BOTH normalizations — fork-15 (fixes the coordinate-naming contagion) AND the
incidence/Q,P Schur (fixes the determinantal-residual leak); "one fix serves both" = NO** — the
det-1-blind Jacobian needs only fork-15, but the loss is not det-1-blind (§6).

The loss factorization

    frobSq(prod M (chartMap w)) = (∏ₖ divCoord_k(w)²) · residualCore(w),
    0 < lo · baseForm(w) ≤ residualCore(w) ≤ hi · baseForm(w)   on the source box,

holds at a fully-monomialized leaf of a DEPTH-≥2 tree **provided `chartMap` carries the incidence/
Q,P normalization** (the R-b source gauge `α`, a det-1 shear on the ratio coordinates). Under that
condition all three kill-hunts come back **clean**:
- **(a) power ≥2 in the product — CLEAN.** Each terminal (`t̃=0`) divisor factors out of the product
  at valuation **exactly 1** (loss valuation exactly 2). A Case-1(1) *re-merge* accumulates in the
  **Jacobian exponent `divExp`**, NOT in the loss power. This is precisely t11's picture.
- **(b) divisor trapped in the residual — CLEAN.** All terminal divisors sit in `b₁`; the residual
  `1 + Σ(bᵢ/b₁)²` (resRank=0) or the Morse core (resRank>0) contains no terminal divisor and never
  vanishes on a divisor hyperplane.
- **(c) residual lower bound degenerates — CLEAN on the bounded ratio box.** `residualCore ≥ lo·baseForm`
  with `lo>0` as long as the Q,P normalization is uniformly conditioned on `srcBox` (σ_min bounded away
  from 0) — which the polynomial unipotent shears satisfy for `|ratio| ≤ 1`.

**The single load-bearing condition is that the normalization is IN the chart.** The present
`geoAtlas` `chartMap` is the **pure-β fold** (max-modulus `pivotChart`s conjugated by the *linear*
`qNodeOf`, with the source gauge only *planned* to be "composed in at the LeafPullback stage",
`GeoChart.lean:53`). For that pure-β chart the residual **retains the fresh determinantal singularity
and vanishes on the srcBox** — the lower squeeze `0<lo` **FAILS**. This is the exact defect the
retired `ShearReconcile` docstring warned of ("`det Dψ = 1` … the `LeafPullback` squeeze cannot absorb
it"). It confirms task #35 / **fork-15's "diagonal-normalization swap in `geoChartMap`" is not
optional — it is load-bearing for LeafPullback**, and is needed at **every** depth (already at L=2),
not only at depth ≥2.

---

## The factorization derivation (the mechanism)

**Object.** `F(C) = ‖C¹·…·Cᴸ‖²_F` at the deepest point (B=0). Aoyagi's recursion monomialises `F` by
a sequence of **max-modulus pivot-chart blow-ups** `β` (`pivotChart i u = (uᵢ if k=i else uᵢ·u_k)`)
**interleaved with regular Q/P (Schur/incidence) normalizations** that reduce the residual block to
`[[1,0],[0,D_next]]`. At a fully-monomialized leaf the invariant is (pp.15–22)

    Q · prod · P = diag(b₁,…,b_m),   b₁ = ∏_{t̃(u)=0} u,   b₁ | b₂ | … | b_m,
    bᵢ / bᵢ₋₁ = ∏_{divisors born at level i−1} u.

**Divisor power (kill a).** `b₁` is a product over *distinct* exceptional coordinates (each terminal
divisor once) ⟹ `b₁` is **squarefree**. `frobSq = Σbᵢ² = b₁²·(1 + Σ_{i≥2}(bᵢ/b₁)²)`, so each terminal
divisor is **exactly power 2** in the loss. The Case-1(1) re-merge changes the *Jacobian* exponent
`M_{s,k}` (the divisor is re-used across blow-up steps, so its `du` appears with higher power in the
change-of-variables determinant) but adds **no second copy** to `b₁`. Enumerate the terminal divisor
**once** in `divCoord`; put the accumulation in `divExp`. [`scripts/l3_product_divisor_power.py`,
`scripts/l3_compose_and_diagb.py` §II — decorrelated Codex §1 identical.]

**Residual bound (kill b,c).** After extracting `b₁²`, the leading residual term is `1` (or the Morse
core), and the residual is `(bounded-invertible Q,P unit)·(1 + Σ(non-terminal monomials)²)`. On a
box with `|ratio| ≤ R` the Q,P unipotent shear has bounded condition number, so `residualCore` is
squeezed between positive multiples of `baseForm`. [`scripts/l2_baseline.py`,
`scripts/l3_compose_and_diagb.py` §I.]

**Exact squeeze constants (L=2 / the recurring 2×2 residual).** The residual `‖(I+lower b')·Z‖²` is
controlled by the Gram matrix `G(b')=[[1+b'²,b'],[b',1]]`, eigenvalues `λ±(b')=(2+b'²±|b'|√(b'²+4))/2`.
For the unit ratio box `|b'|≤1`:  **`lo = (3−√5)/2 ≈ 0.382`, `hi = (3+√5)/2 ≈ 2.618`.** Both my
battery (`l2_baseline.py`) and the decorrelated Codex leg (§3) produce these identical constants.

---

## Why the normalization is load-bearing — the witnesses

**W0 (my battery, L=3 (2,2,2,2)).** Pure-β fold: one max-modulus blow-up of the fresh core leaves an
order-2 degenerate residual; a *second* pure blow-up gives `Fresh = p²·pp²·core_final` with
`core_final = ‖[[1,q₁],[q₂,q₃]]·[[1,cc₁],[cc₂,cc₃]]‖²` that **vanishes at 18 points of the `{−1,0,1}⁶`
box** (e.g. `q₁=1, cc₂=−1`, rest 0) — a genuine loss zero with divisors `p,pp ≠ 0`. So the residual is
**not bounded below** → `0<lo` fails. [`scripts/l3_leak_and_rb.py` §1.] WITH the incidence
normalization at both layers: `F = α²ρ²·α'²ρ'²·(Morse)`, residual `≥ 0.382·baseForm`, 0 box violations
on 20000 samples. [`scripts/l3_recursion.py`, `scripts/l3_compose_and_diagb.py` §I.]

**W1 (Codex, re-verified — sharper: fails already at L=2).** Pure-pivot `C¹=α[[1,a],[b,ρ]]`,
`C²=[[ρξ,ρη],[r,s]]` gives `F|_{ρ=0} = α²a²(r²+s²) ≠ 0` — the claimed `α²ρ²` factor is **false**
(witness `α=a=r=½`: `F=1/64`, claimed RHS = 0). The `ab`-shear in Aoyagi's incidence `α[[1,a],[b,ab+ρ]]`
is exactly what cancels this; it **is** the R-b source gauge `α_d` (`z ↦ ab+δ`, det-1, ratio-only —
`scripts/l3_leak_and_rb.py` §2). [`scripts/verify_codex_witnesses.py` W1.]

**W2 (Codex, re-verified — the re-merge trap made concrete).** Naive pure-pivot re-use `x=u·r, r=u·s`
gives `x=u²s`; extracting `u²` from `x²` leaves `u²s²`, vanishing on `u=0`. The construction AVOIDS
this exactly by the `b₁`-squarefree enumeration (one `divCoord` per terminal divisor, accumulation to
`divExp`). [`scripts/verify_codex_witnesses.py` W2.]

**W3 (Codex, re-verified — the determinantal box zero).** `[[1,1],[0,0]]·[[1,0],[−1,0]] = 0` with all
ratios in `[−1,1]`: the fresh core after a peel is a **determinantal** singularity whose singular
locus is a *nonlinear* hypersurface. A coordinate-subspace (linear-center) blow-up cannot separate it;
the non-toric incidence chart is required (matches PivotCover's "provably NON-TORIC at the tree level"
and the `verify-r1-shortcut` §8 refutation: one blow-up leaves a fresh depth-(L−1) core, order 4).
[`scripts/verify_codex_witnesses.py` W3, `scripts/l3_leak_and_rb.py` §3.]

---

## Exact conditions LeafPullback's `chartMap` must satisfy (what to assume / build)

The **statement** of `LeafPullback` (`EngineDefs.lean:43–48`) needs **no restatement** — it existentially
quantifies `residualCore, lo, hi` and reads `l.srcBox` (bounded in the flat cube). The factorization is
a **property the `chartMap` must satisfy**, and the pure-β chart does not. To make it TRUE:

1. **The normalization is IN the chart.** `chartMap = β ∘ α` (source gauge) — equivalently `ψ ∘ β`
   (target) — with the Q,P/incidence Schur shear composed in. It is **not** absorbable by the
   `residualCore` squeeze. (Fork-15 / task #35 "diagonal-normalization swap in `geoChartMap`" is the
   right fix; my finding says it is mandatory and needed from L=2 up.)
2. **Coherent per-edge composition across the depth-≥2 fold.** The per-edge source gauges must compose
   coherently — `chartMap`, `srcBox`, AND the Morse-coordinate (`resCoord`) assignment must all
   incorporate them together. The single-node R-b verification (`cert-psi-mix`) is **not** by itself the
   depth-≥2 statement; the composition holds (verified L=3, `l3_compose_and_diagb.py` §I) but only when
   the source domain is transformed too: `(β∘g⁻¹)(g(D)) = β(D)`, not `β(D)` with `D` left unchanged
   (Codex §4, closing note).
3. **`divCoord` injective ⟹ `b₁` squarefree ⟹ loss-power exactly 2.** (Already a `ChartBridge` clause.)
4. **Uniform conditioning of Q,P on `srcBox` (⟹ `lo>0`).** `inf_{srcBox} σ_min(Q^{±1}), σ_min(P^{±1}) > 0`
   with finite upper bounds. Polynomial unipotent shears satisfy this on `|ratio| ≤ R`. **Caveat
   (Codex):** for a merely *locally* regular normalization the box closure must stay inside its regular
   domain — nondegeneracy only at the origin does NOT give a whole-box bound.
5. **`resRank`/`resCoord` must match the ACTUAL residual structure** (see below).

---

## Structure / ideas observed (data, not a route)

- **Mechanism (the load-bearing invariant):** the loss power is governed by `b₁ = ∏_{t̃=0}u` (squarefree),
  which is a **loss-level, power-2-uniform** object, DECOUPLED from the Jacobian-level accumulated
  `divExp`. The two ledgers (`divCoord`/loss-power-2 vs `divExp`/Jacobian) are genuinely different reads
  of the same tree — the construction is right to carry them separately (t11's finding-2/finding-3
  co-design). LeafPullback (power-2) and LeafJacobian (accumulated) do **not** share the fold induction.
- **`resRank` — a caveat for elder R5b / task #42 (Speculation).** There are TWO leaf residual shapes,
  and LeafPullback covers both ONLY if `resRank`/`resCoord` name the right thing:
  - *Aoyagi fully-diagonalized* leaf → `resRank=0`, `baseForm=1`, `residualCore = 1+Σ(non-terminal
    monomials)² ∈ [1,hi]` (a bounded unit). This is the resRank=0 case the elder expects.
  - *Morse-residual* leaf (e.g. the L=2 RRR peel, `verify-r1-shortcut`) → `resRank>0`,
    `baseForm = ‖z‖²` Morse, squeezed `[lo,hi]·baseForm`.
  **A `resRank=0` assumption is FALSE if the construction's leaf keeps a Morse residual** — then the
  leaf DATA must set `resRank` to the Morse dimension and `resCoord` to those directions, or the squeeze
  against `baseForm=1` fails (a Morse form is not bounded below by a constant). Which shape the spine's
  `IsFullMonomialization` leaves is a construction question I did not settle here; flag it before
  freezing `resRank=0`. [My L=2 baseline leaves resRank=4; the diag(b) picture reaches resRank=0.]
- **Idea (connection):** the whole load-bearing point is that `{prod = 0}` is **non-toric** (the
  bilinear product), so pure (toric) coordinate blow-ups cannot resolve it — the incidence/Q,P chart is
  the non-toric ingredient. This is the same fact PivotCover states at the tree level and the §8-shortcut
  refutation states at the layer level; LeafPullback inherits it at the loss level.

---

## §6 Off-diagonal contagion in the LOSS (elder charge-2 re-point) — pairs with pnp-fold cert-fold-regroup §4

pnp-fold's binding kill-condition (Jacobian side): a fan-out copy that births a NON-terminal divisor at
an OFF-diagonal pivot cell `z_pivot` has its merge/split power land on the state-level `divBirthCoord`
DIAGONAL cell `z_diag` that descendants reference — `J_Φ = L · (z_diag/z_pivot)^{runLen·resCols}`. I
adjudicated whether the **loss** monomial `∏ z_{divCoord}²` suffers the same contagion.

**Mechanism (from the chart model, fold cert §0).** A max-modulus blow-up with pivot `P` scales every
*other* center cell by `z_P` (`z_c ↦ z_P·z_c`), so the whole residual block = `z_P·D'` and the product
carries `z_P` once ⟹ **`frobSq = z_P²·(unit)`: the loss vanishes order-2 along the ACTUAL pivot cell
`z_P`.** [`scripts/l4_diagonal_contagion.py`, "leaked z_P? False".]

**(A) CURRENT charts — the loss contagion is REAL and breaks BOTH bounds.** If the ledger's `divCoord`
names the DIAGONAL `z_D` (state-level `divBirthCoord`, `D ≠ P`) while the chart blows up the off-diagonal
`P`, then

    residualCore = frobSq / z_D²  =  (z_P / z_D)² · unit,

which **vanishes at `z_P=0, z_D≠0`** (`residualCore = 0` ⟹ `0<lo` FAILS — a divisor trapped in the
residual, kill-b/c) **and is unbounded at `z_D=0, z_P≠0`** (`residualCore = zoo` ⟹ `hi` FAILS). So the
loss inherits the contagion *identically* to the Jacobian — confirming the elder's ruling. [`l4_diagonal_contagion.py` (A).]

**(B) DIAGONAL-NORMALIZED charts (fork-15) — contagion GONE.** With the source swap making the blow-up
pivot the diagonal cell (`birth = reference = D`), `frobSq = z_D²·unit`, `divCoord = z_D` matches, and
`residualCore = unit` (value `1` at the deepest residual point). [`l4_diagonal_contagion.py` (B).] This
is exactly the setting the rest of this cert adjudicates in (my chart model used the divisor coord AS the
u-scaling pivot throughout), so the §1–§5 verdict is already the diagonal-normalized one.

**Two DISTINCT normalizations — "one fix serves both" = NO.**
- **fork-15** (a cube-invariant coordinate SWAP `pivot ↔ diagonal`, det ±1) fixes the *coordinate-naming
  contagion* — which cell the loss vanishes along vs which cell `divCoord` names.
- **The incidence/Q,P Schur** (a ratio SHEAR `z ↦ z − r_ip·r_pj`, det 1) fixes the *determinantal-residual
  leak* (§1–§5, `l3_leak_and_rb.py`) — a SEPARATE cross-layer issue: the fresh core after a peel is a
  determinantal singularity a coordinate blow-up cannot resolve.

These are different operations addressing different leaks. The **Jacobian is det-1-BLIND to the Schur**
(`ShearReconcile`: `det Dψ = 1`), so the Jacobian side needs ONLY fork-15. The **loss is NOT det-1-blind**
(Frobenius norm changes under `Q,P`), so LeafPullback needs **BOTH** fork-15 AND the Schur/incidence
normalization. Deciding whether one construction change serves both sides: it does not — the loss requires
the extra Schur normalization the Jacobian does not.

---

## Close

- **Firmest (Proved / battery + decorrelated-Codex-convergent):** at a fully-monomialized leaf, with the
  incidence/Q,P normalization in the chart, each terminal divisor is loss-power **exactly 2** (kill a),
  no terminal divisor in the residual (kill b), residual squeezed `0<lo·baseForm ≤ residualCore` on the
  bounded ratio box (kill c). The re-merge accumulates in `divExp`, not the loss. **The factorization
  HOLDS.**
- **Equally firm (witnessed):** the **pure-β `chartMap`** currently in `geoAtlas` does **NOT** satisfy
  the squeeze — the residual retains the fresh determinantal singularity and vanishes on `srcBox` (kill
  c fires), already at L=2. The normalization is load-bearing at every depth.
- **Most likely to bite the builder:** (i) forgetting to transform `srcBox`/`resCoord` when the source
  gauge is composed in (Codex §4); (ii) freezing `resRank=0` when the leaf residual is actually Morse;
  (iii) a normalization that is only locally regular, so `lo→0` at the box boundary.
- **Off-diagonal contagion (§6, elder charge-2):** the loss suffers it *identically* to the Jacobian on
  the CURRENT charts — `residualCore = (z_P/z_D)²·unit` breaks both `0<lo` and `hi`. Diagonal-normalization
  (fork-15) removes it. But fork-15 alone is **not** enough for the loss: the determinantal-residual leak
  (§1–§5) needs the *separate* Schur/incidence normalization the det-1-blind Jacobian does not. **One fix
  does not serve both sides.**
- **Next construction step this points to:** BOTH normalizations in `geoChartMap` — fork-15's diagonal
  swap (task #35) AND the incidence/Q,P Schur source gauge — with the composition coherent with
  `srcBox`/`resCoord`. After both, LeafPullback is provable as stated. No paper adjudication is owed
  before that build.
