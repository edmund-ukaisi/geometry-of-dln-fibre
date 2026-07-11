# Pivot-charge dyadic-shell finiteness — verdict (task #115, gates B5a/B2 + (3,3,3,4) vslice)

**Seat:** pen-and-paper (obstruction-adversarial). **Date:** 2026-07-10. **NO Lean.**
**Charge:** does the dyadic `|det α|`-shell spending of the loss-layer det-inverse `|det α|^{−m₀}`
CONVERGE, or hide a divergence? **Exact algebra:** `/tmp/pivchg_shell.py`, `pivchg_box.py`,
`pivchg_exp3.py` (Beta reduction), `pivchg_domchart2.py`. **Decorrelated:** `codex/shell-{prompt,answer}.md`
(gpt-5.x xhigh; my conclusion withheld — it independently reached the same verdict + sharpened §4).

---

## ONE-LINE VERDICT

**The true chart integral `J` CONVERGES exactly on `c' < ½·minAdm` (no hidden divergence in `J`) — but
the dyadic `|det α|`-shell mechanism AS CITED (charge `|det α|^{−m₀}`, codim-1 shell measure,
shift-independent per-shell rest) DIVERGES: `Σ_k 2^{k(m₀−1)}`, a real Beta-boundary divergence at
`{det α→0} ⊇ {rank P ≤ q−1}`. It is a divergence of the BOUND, not of `J`. Finiteness is delivered by
the box-bound / front-first integration (charge exponent `α = max{0, 2c'−m₀(q−1)}`, NOT `m₀`), already
banked as covdesign's §CONCESSION — the shells are the WRONG mechanism and should be dropped from the
carrier-skeleton §8-i / normalslice-cert correction.**

The pivot charge is NOT an extra analytic obligation (no shells, no Anderson needed for it); it
dissolves into the front-first box integral. `α` (the det-inverse block) is `q×q`; the charge exponent
is `m₀ = M₀` (front-matrix rows), not an `m₀×m₀` block.

---

## 1. The three-part adversarial finding (all exact / MC-confirmed, Codex-concurred)

### (a) Shell measure — codim-1, `~2^{−k}` [`pivchg_shell.py` Part 1; Codex Q1]
`vol{α ∈ [−1,1]^{q²} : |det α| ≤ t} = C_q·t + o(t)` (leading power `t¹`, **log power 0**). n=1 exact
(`2t`); n=2 numeric `vol/t → 2.0` (no log); Codex's clean derivation (condition on the first `q−1`
rows, `det` linear in the last with cofactor `w`, strip `≍ t/|w|`, `∫|w|^{−1}<∞` since the transverse
radius has 2 real dims) gives log-power 0 for all `q`. (My n=3 MC showed a mild `vol/t` drift — a
finite-`t`/MC artifact, not a genuine log; irrelevant to the verdict.) **Shell_k measure `~ C_q·2^{−k}`.**

### (b) Raw charge non-integrable — `∫|det α|^{−s}<∞ ⟺ s<1` [`pivchg_shell.py` Part 2; Codex Q2]
Reduces to `∫₀^ε u^{−s}du` (`u=|det|`), converges iff `s<1`; at `s=1` log-divergent. **So the pivot
charge `|det α|^{−m₀}` is NEVER integrable on its own for integer `m₀ ≥ 1`.** This is the seed of the
divergence.

### (c) THE HIDDEN DIVERGENCE — naive shell sum `Σ_k 2^{k(m₀−1)}` [`pivchg_shell.py` Part 3; Codex Q3]
With shift-independent rest, `term_k ≍ vol(Shell_k)·2^{k·m₀} = 2^{−k}·2^{k m₀} = 2^{k(m₀−1)}`:
- **`m₀=1`:** `term_k ≍ 1` ⟹ `Σ 1` **log-divergent in the det cutoff** — the exact **Beta-boundary**
  the brief feared. (The `q`-log factor, if any, only worsens it.)
- **`m₀≥2`:** `term_k ≍ 2^{k(m₀−1)}` ⟹ **geometric divergence.**

**Location:** `{det α = 0}`. On the square case `q×q` (`P=α`) this is the genuine `{rank P ≤ q−1}`;
on wider `P` most of `{det(selected minor)=0}` still has `rank ≥ q` (another minor survives) — a pure
pivot-chart artifact. **Either way the divergence is of the BOUND, not of `J`** (Codex: "divergence of
this upper bound does not imply divergence of `J`").

## 2. Why the coupling does NOT rescue the factorized shells [`covdesign` §5; Codex Q4]
The steelman "on Shell_k, `Z ~ α⁻¹ ~ 2^k` blows up so the rest decays `~2^{−2ks}`" **does not factorize**:
- A det-shell does **not** fix `‖α⁻¹‖` (Codex: `diag(t,1)` and `diag(√t,√t)` share `det=t` but have
  `‖α⁻¹‖ = t^{−1}` vs `t^{−1/2}`); `Z=δ−γα⁻¹β` can stay bounded when `β,γ` are small.
- Extending the sheared `R`-domain to an `α`-independent box **discards exactly the Jacobian
  compensation**. There is no inequality replacing `∫|det α|^{−m₀}·H` by `[∫charge]·[∫rest]`: "if `H`
  is any positive `α`-independent constant, the determinant integral is infinite by Q2." **The large
  charge and the decay live in the SAME variables — no factorized shell bound closes it.**

## 3. The CONVERGENT mechanism — front-first box-bound [`pivchg_box.py` (A), `pivchg_exp3.py`; Codex Q5]
Integrate `A₀` FIRST (do not clean-then-shell). The box keeps the collapsing singular direction `O(1)`:

> **1-D squeeze [exact]:** `∫_{−1}^1 (σ²z²+w)^{−c'} dz → 2·w^{−c'}` as `σ→0` — **NO `σ^{−1}`.** (Verified
> `c'∈{0.8,1.5}`, `w∈{1,¼}`, to 5 digits.) The `σ^{−m₀}` blow-up is a **whole-line** artifact.

Hence `g(P) := ∫_{A₀ box} frobSq(A₀P)^{−c'} dA₀`, as `σ_q(P)→0` (`P→{rank q−1}`), scales with the
**box exponent** (`d_S = m₀(q−1)` stable dirs, `d_T = m₀` collapsing):

> **`g(P) ≍ σ_q^{−α}`, `α = max{0, 2c'−m₀(q−1)}`** (log at `2c'=d_S`; `g≡∞` iff `2c'≥m₀q`).

**Proved EXACT** via the Beta reduction `∫₀¹(ρ²+a)^{−c'}ρ^{d_S−1}dρ ≍ ½·a^{d_S/2−c'}·B(d_S/2, c'−d_S/2)`
(`I_exact/I_beta → 1` to 4 digits, `pivchg_exp3.py`), then the `τ`-integral `∫τ^{d_S−2c'+d_T−1}dτ` finite
iff `2c'<m₀q`. Codex derived the identical `β = max{0,2c'−m₀(q−1)}` independently ("in the finite
rank-`q` regime `β<m₀`; it is NOT the raw `σ^{−m₀}` pivot charge"). **The effective charge exponent is
`α`, not `m₀`** — the naive shell used the wrong (whole-line) exponent.

## 4. Interaction with the `minAdm` budget — the charge lands EXACTLY at ½·minAdm, never past [`pivchg_box.py` (C,D); Codex Q5]
`∫_P g(P) dP` over the rank-`(q−1)` tube (radial measure `σ^{D−1}dσ`, `D = codim{rank P ≤ q−1}`)
converges iff `α < D`, i.e.

> **rank-sector threshold: `2c' < m₀(q−1) + D`.**

The **linchpin** `minAdm(M) ≤ D + m₀(q−1)` holds with **0 violations / 120** single-matrix chains
(widths ≤4, all coranks; `minAdmRec` exact) and is **TIGHT** at the binding sector (**51 equality
cases**). Therefore:
- for `c' < ½·minAdm`: `α = 2c'−m₀(q−1) < minAdm − m₀(q−1) ≤ D` ⟹ **CONVERGES**;
- at `c' = ½·minAdm`: `α = D` (log-borderline, correctly excluded by strictness).

**The charge does NOT push past ½·minAdm** — the `m₀(q−1)` Morse charge plus the deeper-stratum codim
`D` exactly reconstitute `minAdm` (the tightness IS the min-over-`q` of `frontCharge`). Codex derived the
global threshold independently via Mellin/Gamma: `J<∞ ⟺ c' < ½·min_{0≤j≤d}[m₀j+(m₁−j)(m_L−j)] = ½·minAdm`,
and confirmed the worked `(2,2,2)@q=2`: `J<∞ ⟺ c'<3/2 = ½·minAdm`, "yet Q3 produces terms `~2^k` for every
`c'`, demonstrating its divergence is an artifact." The full chart integral MC (`pivchg_box.py` (D)) shows
the relative-SE blow-up tracking `½·minAdm` on `(1,1,1),(2,2,2),(1,2,2),(2,1,2)`.

## 5. WATCH — the one exponent that is single-matrix-verified but only PROXIED for product tails
`g(P)` as a function of `P` is unchanged for a product tail, **but the measure on `P` is no longer
Lebesgue** — the tube codim `D` must be the **product-map rank-tube exponent** (`{rank(A₁···A_{L−1})≤q−1}`),
possibly with logs / multiscale rank strata (Codex Q5; covdesign's flagged loose end). My dominant-minor
MC (`pivchg_domchart2.py`) confirms `{|det B_largest|≤t}` for a PRODUCT is **not** codim-1: sublevel
exponent `0.71 (D=1) → 7.48 (D=4) → unsamplable (D=9)` — it scales with the product-rank codim. **This is
the (3,3,3,4) vslice's actual regime.** The linchpin was checked EXACT for single-matrix tails; for
product tails it needs the exact product-rank `D` (the covdesign `D`-proxy sharpening, still open). **This
is the most likely thing to break the clean threshold — not the shells (already refuted), but the exact
product-rank tube codim.**

---

## Consequence for the build (gates B5a/B2, (3,3,3,4) vslice)

- **DROP the dyadic-`|det α|`-shell (and Anderson) framing** for the pivot charge from carrier-skeleton
  §8-i and the normalslice-cert CORRECTION. As literally stated ("spend `|det α|^{−m₀}` via disjoint
  dyadic shells"), it **hides a divergence** and cannot close per-chart finiteness. It is one of the
  session's over-claims (wtint/catint/crnrt/subred pattern), now caught.
- **USE the front-first box-bound** = covdesign's §CONCESSION (front-peel CLOSES; `g ≍ σ_q^{−α}`,
  `α=max{0,2c'−m₀(q−1)}`, integrate against the rank-tube codim `D` via the linchpin
  `minAdm ≤ D+m₀(q−1)`). This is the banked route; B5a/B2 do NOT owe a shell/Anderson finiteness lemma
  for the pivot charge.
- **The load-bearing OPEN piece** is not the pivot charge but the **exact product-rank tube codim `D`**
  for the product tails (single-matrix `D` is exact and tight; product `D` is proxied) — the covdesign
  follow-up-4 linchpin `minAdm(M) ≤ D + m₀(q−1)` must be re-verified with the product-rank `D`, not the
  free-matrix determinantal `D`.

---

## Firmest / most-likely-to-break / next

- **Firmest.** (i) The naive shell bound diverges `Σ 2^{k(m₀−1)}` (Beta-boundary `m₀=1`, geometric
  `m₀≥2`), exactly at `{det α→0}` — a BOUND divergence, `J` itself finite. (ii) `g(P) ≍ σ_q^{−α}`,
  `α=max{0,2c'−m₀(q−1)}`, EXACT (Beta reduction, Codex-independent). (iii) `J<∞ ⟺ c'<½·minAdm`; charge
  lands exactly at budget (linchpin tight, 0/120 violations). Two independent derivations (mine + Codex
  Mellin) agree term-for-term.
- **Most likely to break.** The **product-tail rank-tube codim `D`** (measure not Lebesgue; possible
  logs/multiscale strata). Single-matrix linchpin is exact; product-tail is proxied. This — not the
  shells — is where a `< ½·codim` stratum, if any, would hide.
- **Next.** Compute the EXACT `codim{rank(A₁···A_{L−1}) ≤ q−1}` (product-rank tube exponent) for the
  (3,3,3,4) tails and re-verify `minAdm ≤ D + m₀(q−1)` with that `D`; this closes the last exponent the
  box-bound rides on. (Feeds the same open the covdesign `D`-proxy flagged.)

---

# §SEAM ADDENDUM — the finite dominant-minor cover assembles with NO divergent boundary term

**Scope update (team-lead, 2026-07-10):** the BULK det-inverse math is settled by `subred` (the
shrinking-image cancellation is Gaussian/Bartlett-EXACT — a genuine cancellation, not a divergence; the
`[free-core·J]` factorization is invalid precisely BECAUSE the cancellation is real). Residual narrowed
to: **Lean cover-assembly finiteness + no-Beta-divergence ON THE SEAM** (the chart boundary where the
dominant `q`-minor switches). **Exact/MC:** `/tmp/pivchg_seam.py`. **Decorrelated:** `codex/seam-{prompt,answer}.md`.

## SEAM VERDICT: no Beta/boundary divergence on the seam. The finite dominant-minor cover assembles finitely.

The front integrand `g(P) = ∫_{A₀ box} frobSq(A₀P)^{−c'} dA₀` depends on `P` only through the Gram
matrix `PP^T` (`g(P) = G(PP^T)`, right-orthogonal-invariant: `g(PV)=g(P)`), so it carries **no
pivot-chart / minor label**, and its only possible singularity is the geometric `{σ_q → 0}`:

- **FACT 1 — `g` is minor-structure-blind and `O(1)` off `{σ_q small}`** [`pivchg_seam.py`]. Fixing
  `σ_q = 1` and sweeping the singular-vector frame (minor spread `1.9×…11.4×`), `g ≈ 17.1` (varies only
  `17.086…17.224`). `g` sees the full Gram matrix but no chart label. **Caveat (Codex Q1):** on a *box*
  `g` is NOT a function of the singular values *alone* — a LEFT rotation changes the quadratic form's
  orientation relative to the cube (singular-value-only invariance would need a ball/Gaussian). That
  residual dependence is the `17.086↔17.224` wobble — bounded and irrelevant: `g` is **uniformly
  `O(1)` whenever `σ_q ≥ ε`** (`sup g < ∞ ⟺ c' < m₀q/2`, the transverse `A₀`-origin being the only
  singularity off `{σ_q=0}`).
- **FACT 2 — the seam sits at `σ_q = O(1)`, NOT on the deep stratum** [`pivchg_seam.py`]. On the
  near-seam band (top-2 minors within 2%), `σ_q` mean `0.59` ≈ overall `0.58`; only `0.41%` of seam
  points have `σ_q < 0.05`. So `g` is `O(1)` on the seam — **no non-integrable singularity sits on a
  seam.** (A finite sum of finite terms is finite; the only way a boundary term could diverge is a
  non-integrable singularity ON a seam, which FACT 2 rules out.)
- **FACT 3 — at the corner `{σ_q→0}` all competing minors vanish at the SAME rate `≍ σ_q`, no chart
  over-charges** [`pivchg_seam.py`]. As `σ_q→0`: `(max minor)/(2nd max) → ~1.5` (`O(1)`) and
  `(max minor)/σ_q → ~1.0` down to `σ_q ∈ (0.008, 0.012)`. Every chart sees its dominant pivot
  `|det B| ≍ σ_q` — the TRUE geometric rate — so the deep corner is approached symmetrically; no
  single chart's bound blows up faster than `σ_q^{−α}`.

**Assembly.** Finitely many charts (`C(m₁,q)·C(m_L,q)`), dominant-minor regions are an a.e. partition
(ties = measure-zero seams), so `∫_{box} g = Σ_charts ∫_{chart^dom} g` **exactly** (no double-count, no
seam term); each `∫_{chart^dom} g ≤ ∫_{box} σ_q^{−α} < ∞` for `α<D` (`c'<½·minAdm`). **The seam
contributes nothing** — it is a measure-zero set at `O(1)` integrand.

## The load-bearing Lean caveat (what the cover-assembly must ensure)

The dominant-minor restriction `|det B| ≥ |det B'|` is **load-bearing — for the CONDITIONING of the
per-chart bound, not for finiteness of `g`**:
- On the **dominant** chart, `|det B| ≍ σ_q` (FACT 3), so the shear normal form's pivot vanishes at the
  TRUE geometric rate; the coupled per-chart bound (subred's Gaussian/Bartlett-exact estimate) is
  `≍ σ_q^{−α}` and finite.
- On a **bare-invertibility** chart `{det B ≠ 0}` where `B` is NOT dominant, `|det B|` can be `≪ σ_q`
  (another minor carries the rank), so a `|det B|`-based / whole-space-peel bound **over-charges** the
  codim-1 locus `{det B=0, rank P=q}` — a **spurious** pole where `g` is `O(1)` (FACT 1). This is the
  same lossiness covdesign §5/fork flagged. Concrete witness (Codex Q3): `P(t) = [[1,0,0],[0,t,t²]]`
  has minors `t, t², 0` with `σ₁σ₂ ≍ t`; the `t²`-pivot vanishes faster than `σ_q` and over-charges,
  while the `t`-pivot (dominant) rides the true rate. The exact bracket is `σ₁···σ_q/√(RC) ≤ M_q(P) ≤
  σ₁···σ_q` (`R=C(m₁,q), C=C(m_L,q)`): every DOMINANT pivot `≍ σ₁···σ_q ≍ σ_q`. **⟹ Lean must (i)
  restrict each chart to its dominance region `{|det B| ≥ others}` (so the sheared bound rides the true
  `σ_q` rate), OR (ii) bound `g` geometrically via `σ_q` directly.** Do NOT assemble bare-invertibility
  charts with a `|det B|`-peel bound — each such term is `+∞` and subadditivity is vacuous.
- Note: even on the dominance chart, the shear coefficient `K = γα⁻¹ ≍ σ_q^{−1}` is unbounded at the
  corner (the CoV maps to a shifted/growing box) — this is exactly the shrinking-image the subred /
  Anderson cancellation handles; the dominance restriction pins the singularity RATE, it does not bound
  `K`.

## Product-tail note (unchanged from §5)
For a product tail the measure on `P` is the pushforward, not Lebesgue; FACTs 1–3 are about `g(P)` and
`σ_q(P)` and are measure-independent, so the SEAM conclusion is unchanged — but the tube codim `D` that
sets the threshold `α<D` must be the product-rank codim (task #116). The seam is clean regardless of `D`.

## Codex (decorrelated, xhigh; my conclusion withheld) — CONCUR + 3 refinements
`codex/seam-{prompt,answer}.md`. Codex independently: (Q1) `g(P)=G(PP^T)` right-invariant, `sup g<∞ ⟺
c'<m₀q/2` off `{σ_q=0}` — and CORRECTED my over-strong "singular-value-only" phrasing (box retains a
bounded left-frame dependence); (Q2) seams are "ordinary angular hypersurfaces meeting rank-`q` with
`σ_q=O(1)`; the deep stratum is merely contained in every seam" — witness `[[1,0,1],[0,1,1]]` (all
minors `1`, `σ_2=1`); (Q3) the Cauchy–Binet SVD bracket `σ₁···σ_q/√(RC) ≤ M_q ≤ σ₁···σ_q` + the
`P(t)=[[1,0,0],[0,t,t²]]` over-charge witness; (Q4) "no surface or boundary term is created by
restricting a Lebesgue integral to finitely many measurable cells… intrinsic `g` contains no inverse
minor-gap, so a seam with nonzero pivots creates no singularity"; (Q5) partition is measure-independent,
but product-tail per-chart finiteness must be proved w.r.t. the **pulled-back factor measure**, and for
free factors with every bottleneck `≥ q` the seam preimages are polynomial zero-sets (factor-measure
zero). **Bottom line (Codex): "No genuine Beta/boundary divergence can hide at dominant-minor cover
seams; under the assumed per-chart integrability the finite assembly is automatically finite."** Two
independent derivations agree; the one correction (box vs singular-value-only) strengthens the record.

## Lean cover-assembly checklist (what to state at commission)
1. **Finite measurable cover**, ties assigned by a **least-index-argmax partition** (disjoint a.e.).
2. **Chosen pivot dominant + nonzero** on the rank-`≥q` cell (`|det B| ≥ others`), so `|det B| ≍ σ_q`.
3. Each per-chart majorant holds **a.e. on the entire cell**, integrable **up to both the seams AND
   `σ_q→0`** — i.e. the coupled/geometric `σ_q^{−α}` bound, NOT a bare `|det B|`-peel.
4. **No inverse-gap factor** `(|det B_i| − |det B_j|)^{−1}` (there is none in `g`; do not introduce one).
5. **Product tails:** state per-chart integrability under the **pulled-back factor measure**, not `dP`
   (task #116 must supply the product-rank tube codim `D` under that measure).

## Seam close
- **Firmest.** No Beta/boundary divergence on the cover seams: `g` right-invariant + `O(1)` on the seam
  (`σ_q` bounded there, Codex-concurred), corner approached symmetrically (`|det B|≍σ_q` all dominant
  charts, Cauchy–Binet bracket). Finite a.e.-partition cover assembles exactly. **The Lean assembly is
  sound IFF charts are dominance-restricted (or `g` is bounded geometrically) — the one caveat to state
  at commission.**
- **Watch.** A `|det B|`-peel bound on bare-invertibility charts over-charges the codim-1
  `{det B=0,rank=q}` seam-interior locus (spurious, `g` is `O(1)` there) — this is the ONLY way the
  assembly breaks, and it is a bound-choice error, not an integral divergence.
- **Next.** (unchanged) product-rank `D` (task #116); + a formaliser should confirm the banked
  `pivotChartCover_matBox_le_sum` is over dominance regions (or re-shape it to be), and that the
  per-chart bound consumed is the coupled/geometric one, not a bare `|det B|`-peel.

---

# §PRODUCT-D — the product-tail rank-tube codim D + the linchpin (task #116, gates the (3,3,3,4) vslice)

**Charge (team-lead):** the box-bound's exponent rides on `D = codim{rank(tail product) ≤ q−1}`;
single-matrix `D` is exact+tight, but for PRODUCT tails the measure on `P` is the pushforward (not
Lebesgue). Compute the exact product-rank `D` for the (3,3,3,4) tails and re-verify
`minAdm ≤ D + M₀(q−1)`. **Exact algebra:** `/tmp/pivchg_prodD.py` (combinatorial + tautology),
`pivchg_tube.py` + `pivchg_q1jac.py` + `pivchg_L4.py` (Jacobian codim + tube MC). **Decorrelated:**
`codex/prodD-{prompt,answer}.md` (xhigh, my conclusion withheld — CONCUR term-for-term, + the log-tie
refinement).

## PRODUCT-D VERDICT

**The linchpin holds with the PRODUCT `D` and is TAUTOLOGICAL: it is exactly the `j=(q−1)` term of the
banked front-peel identity `minAdm(M) = min_{j≥0}[M₀·j + minAdm(M₁−j,…,M_L−j)]`. The product-rank codim
is `D_prod(q) = minAdm(M₁−(q−1),…,M_L−(q−1))` (the reduced-tail zero-product codim, = normalSlice's
`Σ⁰(reduced)` under the unit-Jacobian CoV), STRICTLY BELOW the free-matrix determinantal codim
`(M₁−q+1)(M_L−q+1)` for contracting tails. So there is NO width-general threat: the box-bound closes on
`c' < ½·minAdm` with the honest product `D`.** The one caveat (Codex) is a possible LOG factor in the
tube at ties — it does not move the strict threshold.

## 1. The identity + the tautology [exact, `pivchg_prodD.py`]
- **Front-peel identity** (banked `minAdm_eq_frontPeel`, re-verified 0 failures / 6295 chains):
  `minAdm(M₀,…,M_L) = min_{j}[M₀·j + minAdm(M₁−j,…,M_L−j)]`.
- **Product-rank codim** (normalSlice §5, verified below): `codim{rank(A₁···A_{L−1}) ≤ s} =
  minAdm(M₁−s,…,M_L−s)`.
- **⟹ Linchpin** `minAdm(M) ≤ D_prod(q) + M₀(q−1)` with `D_prod(q) = minAdm(reduced by q−1)` is the
  `j=(q−1)` term of the front-peel min — **TAUTOLOGICAL** (0 violations / 6295 chains `L∈{2,3,4}`,
  widths ≤5; **3557 tight** = the front-peel minimiser). Codex Q4 concurs: "the desired inequality is
  precisely the `j=q−1` term."

## 2. (3,3,3,4): `D_prod` vs `D_free`, linchpin per corank [exact]
Tail `(M₁,M₂,M₃)=(3,3,4)`, `P=A₁·A₂` (`3×3 · 3×4`), `M₀=3`; `minAdm(3,3,3,4)=7`.

| corank `q` | deeper stratum | `D_prod = minAdm(reduced by q−1)` | `D_free = (3−s)(4−s)` | linchpin `7 ≤ D_prod+3(q−1)` |
|---|---|---|---|---|
| `q=1` | `rank≤0` (`P=0`) | `minAdm(3,3,4)=8` | `12` | `7 ≤ 8` ✓ |
| `q=2` | `rank≤1` | `minAdm(2,2,3)=4` | `6` | `7 ≤ 7` ✓ **tight** |
| `q=3` | `rank≤2` | `minAdm(1,1,2)=1` | `2` | `7 ≤ 7` ✓ **tight** |

`D_prod = (8,4,1)` is STRICTLY below `D_free = (12,6,2)` — the contracting-tail effect (middle
bottleneck `M₂=3` makes rank drops cheaper). Using `D_free` would OVER-estimate `D` and falsely admit
`c'` beyond `½·minAdm`; the honest product `D` binds tightly at `q=2,3` (the front-peel minimisers
`j=1,2`).

## 3. `D_prod` verified THREE ways [exact + Codex]
- **Exact Jacobian codim** (rank of the Jacobian of the `(s+1)`-minors of `P` at a point ON the
  dominant component): `q=1 → 8`, `q=2 → 4`, `q=3 → 1` (`pivchg_tube.py`, `pivchg_q1jac.py`). Matches
  `D_prod`, NOT `D_free`.
- **Component dimension count** (Codex Q1, independent): `C(a,b,r) = (3−a)² + (3−b)(4−b) + (b−r)(a−r)`
  (`a=rank A₁, b=rank A₂, r=rank P`, Grassmannian incidence term). Dominant components: `s=0 →
  (1,2,0)` geometric `im A₂=ker A₁`, codim 8; `s=1 →` TWO tied components `(1,3,1)` and `(2,2,1)`, codim
  4; `s=2 → (2,3,2)`, codim 1. `codim(V₀,V₁,V₂)=(8,4,1)`.
- **Tube-exponent MC** (`measure{σ_q(P)≤t} ~ t^D`): `q=3 → 0.96`, `q=2 → 3.24↑4`, `q=1 → 5.75↑8`
  (undershoot at finite `t` for high codim, consistent with `(1,4,8)`).
- **General-L** (`pivchg_L4.py`): the 3-factor tail `(2,2,2,2)`, `P=A₁A₂A₃`: Jacobian codim `{P=0}=3 =
  minAdm(2,2,2,2)` (vs `D_free=4`), `{rank≤1}=1`. Identity holds beyond 2 factors.

## 4. Tube exponent = codim (leading power); the LOG-tie caveat [Codex Q3, adopted]
The adversarial worry (a smaller tube exponent from multiplicity/multiscale, which would SHRINK `D` and
break the linchpin) is **NOT realised for (3,3,4)**: the leading power equals the codim `(8,4,1)`. BUT
at `q=2` (`s=1`) the **two dominant codim-4 components TIE**, producing a **log factor**: `measure{σ_2≤t}
~ C·t⁴·log(1/t)` (from the reduced normal model `X_{2×2}Y_{2×3}` whose two layer-minima `4,4` tie:
`t⁴∫_t^1 dα/α = t⁴log(1/t)`). **This does NOT move the strict threshold** — `∫ σ_q^{−α}` against a
`t^{D}log(1/t)` tube still converges iff `α < D` (the log only makes the borderline `α=D`, i.e.
`c'=½·minAdm`, diverge — correctly excluded by strictness). The tie/log is the **θ-count signature**
(≥2 top-dimensional components at the binding stratum) — a Level-B (RLCT-value / normal-crossing)
matter, not a Level-A (finiteness) threat.

## Firmest / watch / next
- **Firmest.** The linchpin with the product `D` is the `j=q−1` front-peel term — **tautological**, 0
  violations. `D_prod(q)=minAdm(reduced by q−1)`, verified 3 ways (exact Jacobian, component count,
  tube MC) + general-L; `(3,3,3,4): D_prod=(8,4,1)` strictly below `D_free=(12,6,2)`, tight at `q=2,3`.
  Box-bound closes on `c'<½·minAdm` with the honest product `D`. Codex decorrelated-concurs term-for-term.
- **Watch.** (i) The general-width identity `codim{rank(product)≤s}=minAdm(reduced by s)` is
  normalSlice's banked CoV-iso (codim CoV-invariant); Codex marks the closed formula "conjectural in
  this generality" — proven for the cases checked (`L=3,4` tails). (ii) Codex's general caveat:
  *codim alone does not rule out a smaller tube exponent; multiplicity must be checked per chain* — for
  (3,3,4) the leading power = codim (clean), but a width-general Level-A proof should confirm no stratum
  has a sub-codim tube power. The LOG at ties is harmless to the strict threshold (Level-A); it is the
  θ-multiplicity (Level-B).
- **Next.** For the Lean vslice: consume `D_prod = minAdm(reduced by q−1)` (the reduced-tail `minAdmRec`,
  banked) as the tube codim; the linchpin is then `minAdm_eq_frontPeel` at `j=q−1` (banked ℕ-lemma) —
  **no new analytic lemma**. The only width-general residual is the per-stratum multiplicity check
  (Level-A: leading tube power = codim; the log/tie is Level-B θ-count).
