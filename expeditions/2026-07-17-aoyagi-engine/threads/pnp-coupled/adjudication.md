# Adjudication — coupled corank≥2 monomialisation: monument or detail-at-scale?

Seat: pen-and-paper, obstruction-primary. Dispatch #122. Exact algebra + decorrelated Codex (xhigh).
Formed independently of both the render's optimism and the gate builder's pessimism (both were inputs).

## The question, restated sharply

Does turning `‖∏C‖²` into its RLCT value `½·min_t Mval(t)` at a **coupled corank≥2** minimiser (general
`d`, general `L`) require a **genuine monument** (a deep open fact, cite it) or is it **detail-at-scale**
(a patient, decomposable, general-`d` computation, build it)? Adjudicated per route P / V-upper / V-lower.

## Method / witnesses (exact, re-run this dispatch)

- `g-coupled-334-diagb.py` — `(3,3,4) t=(1,0)`, Mval 8, corank-(2,2) minimiser: peel + radial(‖T‖²) +
  radial(‖ΔS‖²) + JOIN → E-divisor, `F∘g = E²·unit`, unit(0)=1, Jac `E⁷`, ratio `(7+1)/2 = 4 = ½·8`. PASS.
- `g-coupled-3322-shareddepth.py` — coupled branch `t=(2,1,0)`, coupling **raises** `3/2 → 2` (the shared
  `C⁽³⁾` divides both terms); naive max-of-parts undershoots. PASS.
- `g-coupled-444-twoblock.py` — two corank-2 blocks, JOIN → single principal chain, ratio `12/2 = 6`. PASS.
- `g-coupled-33322-separated.py` — `L=4` mixed, two separated shared factors, rlct `2 = ½·4`; single chain
  survives. **Anti-check (d):** with NO kept pivot row (all-δ-weighted) the local unit is ABSENT — this is
  the escape mechanism, exhibited.

## The structural spine I established (independent of the renders)

**(S1) The lower bound cannot be obtained on the original space, nor by a global from-below monomial.**
`{F=0}` (the zero-product locus) contains **cancellation points where every matrix entry is nonzero**
(the product vanishes by rank/alignment, not by a coordinate vanishing). So no nonzero
original-coordinate monomial `H` satisfies `F ≥ H` near 0, and `⟨∏C⟩` is **not** a monomial ideal in any
original-space coordinates (the charter-§3 "no det-1 chart diagonalises" fact). Object A (ideal-invariance)
lets you change generators, not bypass a resolution. Decorrelated Codex reached the same obstruction
independently (its Q1 [FACT]). ⟹ **A blow-up resolution is genuinely required for the lower bound.**

**(S2) A single favourable chart is not a lower bound; the cover is load-bearing.** `rlct = min` over ALL
divisors of a resolution. To conclude `rlct ≥ ½·min` you must (a) resolve `F∘g` to normal crossings on a
family of charts that **cover a punctured nbhd of 0** and (b) bound EVERY divisor's ratio `≥ ½·min`. A
pruned chart family gives a WRONG (too-high) lower bound — the `F = x²+y⁴` witness (omit the `y`-direction).
The `(3,3,3,2,2)` anti-check (d) is the DLN instance of the same phenomenon: drop the kept-pivot-row chart
and the local unit disappears.

**(S3) The per-divisor F-multiplicity for the lower bound is read directly off the entries — no ideal
identity, no principality.** `a_E = ord_E(F∘g)/2 = min_{ij} ord_E((∏C)_{ij}∘g)` (sum of real squares ⟹ no
cancellation of the vanishing order). To UPPER-bound `a_E` (so ratio is bounded BELOW) exhibit ONE entry of
small `ord_E`. This needs **only the entries' pullbacks + the Jacobian + the cover** — NOT `⟨∏C⟩=⟨diag b⟩`
both-ways, NOT the terminal single-chain `⟨diag b⟩=⟨b₁⟩`. This is the genuine sense in which V-lower is
lighter than P **on the algebra** — and the render's §155-165 reduction is right about *this* part.

**(S4) The threshold-raise is realised by the JOIN, not by an inequality.** At a coupled minimiser the
right (raised) value comes from blowing up the intersection `{q=u=0}` of the pivot-chain exceptional `q`
and the residual-block exceptional `u`; the discrepancies ADD (`(3,3,4)`: `3+3+1=7`; `(4,4,4)`: `7+3+1=11`).
The from-below unit `≥1` is supplied by the KEPT PIVOT ROW (`U_T = 1 + Σ(·)²`), so the coupling only ADDS
positive squares and cannot lower the floor — "coupling assists `≥`" is a THEOREM of the join geometry, not
an elementary sum-bound (which undershoots, and which Codex Q3 confirms is too coarse: `x²y² ≥ dist⁴` gives
`1/4 < ½`).

## Why the resolution is NOT a monument (the obstruction hunt came up empty — that is the green signal)

I hunted for the reason it is open. The candidates and why each fails to be a monument:

1. **Existence of a resolution** — would be Hironaka (a monument) IF abstract. But Aoyagi's tree is an
   EXPLICIT finite sequence of blow-ups of smooth (coordinate / radial) centres. No Hironaka cite.
2. **The ideal-algebra maintenance across the `(S,J)` recursion** (the historic "coupled corank≥2 wall").
   This was a **substitution-encoding artifact**, now dissolved at the math level: with pivot ≡ 1 in the
   chart the clearing `Q₁,Q₂` are **unipotent polynomial** (no `1/monomial`), and the block-elim cross-term
   `(b'ᵢ/b'_{J+1})·[b'_{J+1}·(D''C')_{J+1}]` lies in the ideal because the **`b`-chain divisibility**
   `b'_{J+1}|b'ᵢ` makes the cofactor polynomial. General corank, any `r`. This is detail-at-scale — the
   gate measured L-A GREEN/cheap with zero Mathlib ideal-membership tax, and rev-render+Codex confirmed the
   maintenance general. **The gate's "principal collapse monument" is a mis-location:** `⟨diag b⟩=⟨b₁⟩` is
   the one-line L-C (every `bᵢ∈⟨b₁⟩` since `b₁|bᵢ`), trivial once the chain exists; the gate saw a Lean
   encoding where the chain wasn't yet wired, not a deep fact.
3. **The cover (L7) at coupled corank≥2.** The one un-probed piece. It is properness bookkeeping for a
   finite composition of (proper) blow-ups interleaved with (proper, because polynomial-automorphism)
   unipotent shears, truncated to compact boxes with R-dependent inflation through the shears. Codex,
   decorrelated, classifies this **BOUNDED-REPRODUCE**: "no new properness failure once both join charts and
   pivot-boundary branches are present." Coupling adds bookkeeping (independent `q/u` rates, larger shears)
   but no new escape MECHANISM. The residual risk is **completeness of the chart family** (does the built
   tree include every projective chart / both join charts / the pivot-boundary branch), not a monument.
4. **The deepest-point / homogeneity step (Theorem 4).** For the CORE it is the all-variables homogeneity
   (`r=0`, `∏C` degree-`L`), landed + wired. The general sub-block form is not needed for the core close-out.

No genuine monument survives the hunt. The only monument in the *destination* is the cited
`rlct = ½·codim` equality — which is precisely what building A + B-spine + cover DELETES.

## Per-route verdict

### P (atlas: `⟨(∏C)∘g⟩=⟨diag b⟩`, every chart, both directions) — DETAIL-AT-SCALE (split)
- **Algebraic spine (L-A block-elim, L-B `(S,J)` maintenance, L-C principality):** general, sound; a large
  but combinatorial reproduce of Aoyagi's Cases 1/2. Confidence HIGH.
- **Geometric half (L6 dom-wide Jacobian, L7 cover, L8 minimizer-realization):** detail-at-scale, but the
  **coupled L7 cover is un-probed** — the one residual risk (a bounded completeness-bookkeeping risk, not a
  monument). Confidence MEDIUM-HIGH it is buildable.
- A full `Resolution` needs BOTH halves. Not a monument; genuine labour.

### V-upper (minimising chart value `= ½Mval(min)`) — DETAIL-AT-SCALE
Does it "secretly need full monomialisation/principality"? **It avoids ALL-charts and both-directions.** It
needs ONE chart — the minimising branch's blow-up sequence (the coupled peel + join) — and, for the UPPER
bound, that chart's `F∘g = b²·unit` with `unit(0)≠0` (order exactly 2), giving one divisor of ratio
`½Mval(min)` ⟹ `rlct ≤ ½Mval(min)`. That IS a single-chart (minimiser) normal form — a *local* principality
on one chart — NOT the flagged all-charts/deep-mixed open end. The `(3,3,4)/(4,4,4)` joins exhibit it
exactly (unit from the kept pivot row). Buildable general-`L`. Confidence MEDIUM-HIGH. NOT a monument.

### V-lower (coupled value-floor `rlct(coupled) ≥ ½Mval`, coupling-assisted, no single-chain collapse) — SPLIT; does NOT dodge the coupled frontier — it relocates it to the cover
- **Lighter than P on the algebra:** by (S3) the per-divisor F-multiplicity is read off the entries; no
  both-directions ideal identity, no terminal `⟨diag b⟩=⟨b₁⟩`. TRUE and worth having.
- **NOT lighter on the cover:** by (S1)+(S2) the lower bound REQUIRES the full coupled cover L7 (no
  from-below/original-space shortcut; the render's PHASE-2 finding #1 retraction is correct on *this*, and
  Codex Q1 agrees). The "value-floor, no principality" framing conflates "no terminal principality" (true)
  with "no cover" (false). V-lower's true crux = the coupled cover L7 = the SAME object as P's geometric
  half.
- So V-lower is buildable iff the coupled cover is (it is, per §3 above — bounded-reproduce, un-probed).
  NOT a monument; the coupled frontier is the cover, and it is detail-at-scale.

## One live ALTERNATIVE to the explicit cover (Codex Q3, unproven — a research bet, not a shortcut)
`rlct_ℝ(∑fᵢ²) ≥ ½·lct_ℂ(⟨fᵢ⟩)`; lower-bound `lct_ℂ` by a monomial DEGENERATION `I₀` with
`lct_ℂ(I₀)=M_min` + semicontinuity. This trades the explicit real cover for a universal valuation
inequality `A(v) ≥ M_min·v(I)` over the relevant (toric) valuations — a "cover" in valuation-theoretic
clothing. Possibly lighter in Lean-labour, but unproven here; do not bank it as a dodge.

## Bottom line
The expedition **CAN close cite-free** — there is no genuine monument in the coupled resolution; the cited
`rlct=½codim` is exactly what the build replaces. But cite-free **requires building the coupled GEOMETRIC
COVER (L7) at corank≥2, general-`d`** — un-probed, detail-at-scale (bounded-reproduce), with a bounded
completeness-bookkeeping risk that must be **probed before committing** (Codex's sharpest test: the
`u`-dominant / pivot-boundary join chart is present and compact-coverable). **Neither V nor P dodges the
cover.** V is lighter than P only on the ideal-algebra (skips both-directions-per-chart + principality), NOT
on the cover. If the operator wants an honest close *without* the cover: (a) objects-only — bank
A/B-spine/C/D as the reusable engine, cite Aoyagi for the RLCT-lower assembly; or (b) pursue the
complex-lct-degeneration route as a distinct bet (unproven).

## Confidence + what moves it
- Cover is necessary for the lower bound (no shortcut): **HIGH** (S1/S2 + Codex Q1 + `x²+y⁴`). Moved DOWN
  only by a worked complex-lct-degeneration proof (b).
- Cover is detail-at-scale not monument: **MEDIUM-HIGH** (Codex BOUNDED-REPRODUCE + polynomial-automorphism
  properness + the value being correct). Moved DOWN by a coupled corank≥2 instance where the tree provably
  misses a direction not fixable by adding the standard omitted chart; UP by a successful
  box-inflation-through-shears bound at a corank≥2 instance.
- Algebraic spine general (P, V-upper): **HIGH** (b-chain divisibility maintenance; gate L-A green).
- No genuine monument: **MEDIUM-HIGH** (Theorem 4 general sub-block form is the only thing that could turn
  into an analytic atom; not needed for the core).

## ADDENDUM — the per-block radial collapse joint (controller mid-flight pointer; independently adjudicated)

Controller pointed at a specific joint: the peel is ideal-preserving but NOT norm-preserving (`334`
finding (D)), so monomialising the coupled residual `Δ` runs through a RADIAL resolution `Δ = u·D̄` + JOIN
that "collapses a coupled block to a single monomial (per-block principality)". Is THAT collapse
detail-at-scale or does it inherit the terminal open-ness? Adjudicated with fresh exact algebra
(`/tmp/radial_collapse_general.py`, coranks `k=2,3`, pivots `t₁=1,2`) + a second decorrelated Codex
(`codex/collapse-answer.md`). The two converge.

**(i) The radial step `Δ = u·D̄` is GENERAL, corank-agnostic — and is NOT a "collapse".** It is the
blow-up of the smooth coordinate subspace `{Δ=0}` (the Δ-entries are FREE coordinates after block-elim,
because `m_ij = C22_ij` vary freely). In each radial chart every entry factors `Δ_ij = u·D̄_ij` for ANY
block size `k`; the load-bearing hypothesis is the **freeness of the `k²` entries, NOT any rank property
of `D̄S`** (Codex Q1 [FACT], matching my probe). But it does **NOT** collapse the block: `‖ΔS‖² = u²·G`
with `G = ‖D̄S‖²` a **non-unit** (`G(0)=0`, verified all coranks) — a genuinely deeper core that RECURSES.
The "single monomial × unit" appears only on the **terminal PIVOT chart** of the full recursion, and the
leading unit is supplied by the **retained-rank pivot's leading `1`** (`U_T(0)=1`), NOT by any collapse of
`Δ`. So the per-block collapse is a route-P *normal-form* artifact; the radial STEP itself is a trivial
general blow-up and does **not inherit** the terminal single-chain open-ness (worked.tex:651-664). What is
open is the ITERATION/assembly across deep-mixed layers + the cover — not this step.

**(ii) Route V does NOT need the collapse; it reads the value off the divisor ratio.** Decisive, and now
exact:
- **V-upper** (`rlct ≤ ½Mval`, one divisor): `a_E = min_{ij} ord_E((∏C)_{ij}∘g) = 1`, read directly off
  the **pivot entry's pullback** (`q=E` ⟹ order 1), with NO block normal form; and `h_E = Mval−1` from the
  resolution's discrepancy telescoping (`Mval = n·t₁ + k² = (pivot codim) + (Δ codim)`, and
  `h_E = (n·t₁−1)+(k²−1)+1 = Mval−1` — a GENERAL identity, verified `k=2,3`, `t₁=1,2`). ⟹ ratio
  `(Mval−1+1)/(2·1) = Mval/2`. So V-upper reads the value off ONE divisor's `(a_E, h_E)` without the
  collapse. Complete general for the upper bound (modulo constructing the blow-up sequence for `h_E`; for
  `t₁>1` the pivot part is multi-step, but the discrepancy telescopes to `Mval−1` regardless).
- **V-lower** (`rlct ≥ ½min`, ALL divisors): reads each divisor's `(a_E from entries, h_E from resolution)`
  WITHOUT the collapse — BUT the deeper core `G` (living in the `u`-dominant charts) **may create
  lower-ratio divisors**, so an **exhaustive recursive cover controlling every divisor** is required
  (Codex Q3 [FACT]). The normal-form/collapse "merely supplies local principality and easy integration" —
  a convenience, not a necessity.

**Verdict on the joint:** the per-block radial collapse is **DETAIL-AT-SCALE and, more precisely, is not
the frontier at all** — it is a general coordinate-subspace blow-up that neither collapses the block nor
inherits the terminal open-ness, and route V dodges it entirely (reads ratios off entries + discrepancies).
The frontier is unchanged: the **exhaustive recursive COVER** that controls the divisors born from the
deeper cores `G` in the non-pivot charts. This corroborates and sharpens the main verdict below.

## Most likely thing to break it
The coupled L7 cover at general-`d` hides a **completeness gap** (a rank-drop direction whose chart the
built tree omits), turning "bounded bookkeeping" into a re-architecture of the tree. Next construction to
settle the open part: run Codex's sharpest test on `(3,3,4)` — send `q_n/u_n→0` through the coupled shear
and exhibit the compact `u`-dominant leaf with shear-inverse + Jacobian-unit uniformly bounded (the
pivot-boundary branch present). If that leaf exists and is compact-coverable at corank≥2, the cover is
bounded-reproduce and the expedition closes cite-free.
