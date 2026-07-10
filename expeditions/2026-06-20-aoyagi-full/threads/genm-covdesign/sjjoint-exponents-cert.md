# `(S,J)` exponent bookkeeping — the charges the `sjJointResolution` monomial resolution must reproduce

**Seat:** pen-and-paper (witness). **Task #111.** **Date:** 2026-07-10. **NO Lean.**
**Charge:** (1) confirm box-Morse's brick (ii) is Lean-intractable in v4.29 ⟹ `(S,J)` is the cheaper lift;
(2) pivot the route cert to the EXACT exponent bookkeeping the `(S,J)` build (`sjJointResolution:803`)
must reproduce. **Supersedes** `box-morse-cert.md` (which stays as the record of *why* the front-peel
cannot cheaply close in Lean). **Decorrelated:** `forkreview`'s Lean-tractability assessment + my
independent confirmation (below) + the prior neutral Codex (`fork-neutral-answer.md`).

---

## 1. CONFIRM — box-Morse's brick (ii) is intractable / a disguised flag in v4.29. `(S,J)` is cheaper.

**I AGREE with `forkreview`.** Independent reasoning (not a rubber-stamp — the reciprocal of my catching
its earlier θ-error by measurement):

The box-Morse route (`box-morse-cert.md` §4) reduces to the outer integral `∫_{A'} Π_J(A')^{−p} w^{−e}`,
which converges near `{rank Q_b ≤ q−1}` (codim `D`) iff the **sublevel/tube measure**
`vol{rank Q_b ≤ q−1 within ρ} ≲ ρ^D` holds. The gap:
- The banked `cCodim` (RlctPayoffGeneral Brick A / `SigmaCodim`) gives the **algebraic codim** (ideal
  height / Krull dim) of `{rank ≤ q−1}` — **NOT** the measure-theoretic ρ-tube bound. Bridging them
  (codim-`D` real variety ⟹ Lebesgue ρ-tube `≲ ρ^D`) needs Łojasiewicz / a tube (Weyl) formula / Federer
  coarea / semialgebraic measure theory — **NONE in Mathlib v4.29** (only `Layercake`).
- **Elementary cofactor/Fubini slicing STALLS at `t¹`**: it sees `det B` as ONE polynomial (a codim-1
  hypersurface), giving `vol{|det B|≤t} ≲ t¹`, hence convergence only for `θ < 1` — but `θ_true` can be
  up to `D > 1`. Verified exact (`/tmp/sublevel.py`): `vol{σ_min(Q_b) ≤ t} ~ t^D` (`D = m−q+1`: measured
  `t^{0.94, 1.93, 2.92}` for `D = 1,2,3`) — the SHARP exponent needs `σ_min` = distance-to-the-
  determinantal-variety, i.e. the simultaneous vanishing of the WHOLE `q`-minor ideal.
- **That whole-minor-ideal vanishing IS the rank-flag structure.** So the sharp brick (ii) is either a
  from-scratch GMT build (unsupported) OR a disguised rank-flag resolution. Structural clincher
  (`forkreview`): box-Morse's corank-`q` boundary is exactly `{rank = q−1}` = the next flag level — closed
  by (ii) [unsupported] or by recursing [= the flag]. Either way, no cheap escape from the flag.

**Verdict:** `(S,J)` — already scaffolded to ONE sorry (`sjJointResolution:803`), Aoyagi-guided, doing
the flag DIRECTLY — is the cheaper Lean lift. The front-peel/box-Morse route is retired (its content
survives as the exponent targets below).

**DECISIVE — triple-confirmed (2026-07-10, `sublevel-bridge-answer.md`).** A FRESH NEUTRAL Codex (xhigh,
withholding BOTH the controller's and my lean) independently answers **(b) NO**: in Mathlib v4.29 there
is no route from `Ideal.height(vanishingIdeal V) = D` to `volume{dist ≤ t} ≲ t^D` or `IntegrableOn
f^{−α} (α<D)`. It grounds this in the repo — `codimRep` is *literally* `Ideal.height` (`OrbitCodim:117`);
the only bridge is Krull/catenary (`NullstellensatzCodim:111`), which "stays algebraic — does not produce
Hausdorff dimension, Minkowski content, Lebesgue tube estimates, or sublevel estimates";
`PolynomialZeroSet` is a *null-set* theorem only, "not a tube-volume theorem." The missing statement
`algebraic-height-D + semialgebraic geometry ⟹ Euclidean tube exponent D` is a from-scratch GMT build
(coarea / Whitney stratification / Łojasiewicz+semialgebraic-dim / Hironaka normal-crossings). **This is
WHY `(S,J)` wins: it CONSTRUCTS the normal-crossings resolution explicitly (Aoyagi-guided, one sorry),
supplying exactly the regularity box-Morse would have to IMPORT as a black-box GMT theorem.** Three
decorrelated passes (me, via the algebraic-vs-measure gap + `/tmp/sublevel.py`; `forkreview`; the neutral
Codex) agree. **No more rounds — build `(S,J)`.**

---

## 2. THE EXPONENT BOOKKEEPING (the payoff of the refutation-detour — what the monomial resolution lands on)

Aoyagi's `(S,J)` resolution monomialises `frobSq(A₀·prod) = (unit)·∏_j ρ_j^{2κ_j}` with Jacobian
`(unit)·∏_j ρ_j^{h_j−1}`; finiteness of `∫ (∏ρ_j^{2κ_j})^{−c'}∏ρ_j^{h_j−1}` below `½·minAdm` is the
`sjJointResolution` obligation. The detour pins the exponents the flag charges must land on:

### 2a. Per rank-flag level (the charge at the `q → q−1` transition)
Peeling the corank-`q` block charges the **Morse budget `m₀(q−1)`** (the `A₀`-image-annihilation on the
`(q−1)`-dim image), and the residual singularity sits on the reduced determinantal locus. The box (not
whole-space) exponent — verified in `box-morse-cert.md` §1 and by the neutral Codex — is
> **`θ_true(q) = max{0, 2c' − m₀(q−1)}`**  (log-borderline at `2c' = m₀(q−1)`).

This is the coordinate charge the monomial resolution's `{rank=q−1}` blow-up must reproduce: the
collapsing direction contributes `O(1)` (box-bounded), NOT a `det^{−m₀}` pole — the resolution's
exceptional-divisor exponent encodes `θ_true`, not the lossy whole-space `θ_lossy = m₀(q+1)−2c'`.

### 2b. The codim `D` at each level (banked)
> **`D_q = codim{rank(tail prod) ≤ q−1} = cCodim (tailChain M) (q−1)`** — BANKED (RlctPayoffGeneral
> Brick A / `SigmaCodim`; `codimRepCanonical Σ̄^r = cCodim d r`, via Voigt, char-0).

(My earlier single-bottleneck PROXY for `D` was WRONG — it under-counted and produced the retracted false
divergence; the correct `cCodim` is the sharp determinantal codim.)

### 2c. The linchpin (banked precedent)
> **`minAdm(M) ≤ D_q + m₀(q−1)`** — via `Y = {rank Q_b ≤ q−1} ∩ {A₀ kills image} ⊆ Z` (zero-product,
> `codim Z = minAdm`), codim monotone. Banked PRECEDENT: `minAdm_rrp_subadd` (`RouteMSchurThresholdP:104`,
> the stratum-lift codim sub-additivity `minAdm(![r,r,p]) ≤ jp + minAdm(![r−j,r−j,p])`) — the same
> stratum-lift mechanism, to be generalised. Verified **0 violations / 546** single-matrix
> (`/tmp/linchpin.py`).

### 2d. The integrability target (the log-borderline — NOT a literal `t^D`)
From 2a + 2c: for `c' < ½minAdm`, `θ_true(q) = 2c' − m₀(q−1) < minAdm − m₀(q−1) ≤ D_q`, so
> **`θ_true(q) < D_q` STRICT** — the target is **integrability** (the tube integral `∫ ρ^{D−1−θ} dρ`
> converges), NOT a literal `vol ≲ t^D`. At `c' = ½minAdm` exactly, `θ_true = D` (the **log-borderline**):
> `∫₀^ε ρ^{−1}·(log)^? dρ` — the monomial endpoint must handle the `θ = D` case with a **logarithmic**
> factor (as `minAdm_le_flatDim`-style borderlines do elsewhere), correctly EXCLUDED by the strict
> `c' < ½minAdm`. The RLCT is `½·minAdm = min over the flag` of the per-level budgets (each level's
> `(D_q + m₀(q−1))/2 ≥ ½minAdm`, min attained at the achiever `t★`).

---

## 3. HOW THIS ARMS THE `(S,J)` BUILD (`sjJointResolution:803`)

The `(S,J)` double-induction charge-accounting must reproduce §2:
- **`sjChargeUpdate_accum` / the `diag(b)` ledger** (piece 5): the accumulated charge at flag level `q`
  must be the Morse budget `m₀(q−1)` + the reduced; the run should land on `θ_true(q)`, not `θ_lossy`.
  The box-vs-whole-space distinction (2a) is the ledger's invariant: the collapsing direction stays
  `O(1)` (a bounded exceptional coordinate), never a `det^{−m₀}` charge.
- **`sjSubordination`** (`a/2 ≤ ½·minAdm(tailChain M)`): the coupling exponents stay ≤ threshold — this
  is the `c' < ½minAdm ⟹ θ_true < D` condition (2d) at each level, keeping the monomial exponents
  integrable.
- **`sjRunMin_antitone`** (piece 4 invariant): the flag `rank ≤ q ⊃ rank ≤ q−1 ⊃ …` with the run-min
  block dimension antitone — this is the flag `D_q` sequence (2b), decreasing as the resolution descends.
- **The monomial endpoint `monomialIntegrand_integrable_of_lt`** (piece 7): must accept the
  **log-borderline** at `θ = D` (2d) — confirm it handles the `= threshold` case (log factor) or that the
  strict `c' < ½minAdm` keeps every monomial strictly integrable (the `179/546` borderline-equality cases
  are all at `c' = ½minAdm`, excluded).
- **Achiever** (`RouteMAchieverPath` / `Mval M (tStar M) = minAdm M`): the flag level `t★` attaining the
  min is where the RLCT `= ½minAdm` is realised — the monomial resolution's binding coordinate.

**Net for the build:** `sjJointResolution` monomialises per flag level; at level `q` the charge is
`m₀(q−1)` (Morse) against codim `D_q = cCodim(q−1)` (banked), threshold `θ_true(q) = 2c'−m₀(q−1) < D_q`
(linchpin, banked precedent `minAdm_rrp_subadd`), integrability strict below `½minAdm` with a log at the
sup. These are the exact exponents the double-induction must land on — the payoff of the detour.

---

## 4. RESIDUALS for the `(S,J)` build + a reviewer
- **`C = minAdm` bridge** (`cCodim d 0 = minAdm M`, and `codim Z = minAdm`): confirm banked or land it
  (the linchpin's `codim Z = minAdm` input). Likely via the two RLCT-payoff routes agreeing.
- **`minAdm ≤ D_q + m₀(q−1)` general** (2c): generalise the banked `minAdm_rrp_subadd` stratum-lift from
  `![r,r,p]` to general `M` and general flag level; 0/546 single-matrix verified.
- **The log-borderline** in `monomialIntegrand_integrable_of_lt` (2d): confirm the `θ = D` case (strict
  `c' < ½minAdm` should suffice; watch the log).
- **NOT needed:** the box sublevel/tube measure (brick ii — the intractable GMT), total-width induction,
  `reducedMorseFront`. All retired.

## 5. Artifacts
`/tmp/sublevel.py` (t¹-vs-t^D confirmation of (ii) intractability), `/tmp/linchpin.py` (0/546),
`/tmp/box_scaling.py` (θ_true MC), `/tmp/fork_*.py` (retracted lossy analysis, record). Codex:
`fork-neutral-answer.md` (θ_true), `boxatom-answer.md` (box-atom shape, now superseded but records the
soft-direction O(1) mechanism). Prior: `cert.md` §CONCESSION, `box-morse-cert.md` (retired route record).
