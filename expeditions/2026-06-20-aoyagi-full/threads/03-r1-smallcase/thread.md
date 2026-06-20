# Thread 03 — R1 blueprint + spine-risk probe (pp, parallel/read-only)

- **Seat:** `pp` (pen-and-paper). **Read-only on repo + /tmp scratch**; controller integrates (this doc).
- **Status:** rounds 1 (L=2) + 2 (L=3 / general L) done. Spine fully de-risked. Lean-pending.

## Verdict: the spine is SOUND; design-spec §9.3 (set-bijection) was mis-stated

The strong claim "R1's chart exponents = Adm" is **FALSE** — charts vastly outnumber T-vectors
((2,2,2): 24 charts vs 3 T's). The **value-match** holds: resolution's min chart-ratio
`= ½·min_{T∈Adm} Mval(T) = λ_core` = ground truth. Confirmed by pp + decorrelated Codex, independently.

## What `T` indexes (the structural finding, now proven at general L)

`T = (t_1,…,t_{L-1},0)` (weakly-decreasing) indexes the **nested-rank-incidence stratum**
`S(t) = { (C^1,…,C^L) : rank(C^1···C^j) = t_j for all j }`, and
> `codim S(t) = (M^1 − t_1)(M^2 − t_1) + Σ_{j=2}^L (t_{j-1} − t_j)(M^{j+1} − t_j) = Mval(t)`  EXACTLY.

So `λ_core = ½ · min over admissible t of codim S(t)` — the `rlct = ½·codim` structure made concrete on
the singular core.

**Proof (general L), 3-way confirmed (pp hand + numeric + decorrelated Codex):** telescoping fibration —
at layer j, `P_{j-1} = U V` with V full row rank, so `C ↦ V C` is surjective and the residual `D = V C^j`
ranges freely; imposing `rank D = t_j` is a determinantal codim `(t_{j-1} − t_j)(M^{j+1} − t_j)`; the last
layer `t_L = 0` forces `C^L`'s columns into `ker P_{L-1}`, codim `t_{L-1} M^{L+1}`; telescopes to Mval.
Numeric check: the product-map differential rank = Mval at generic stratum points, all strata of L=3
(2,2,2,2) and L=4 (2,2,2,2,2). The "free D" step (the worry) is real (V surjective). **Established
pen-and-paper; the Lean proof is the A1/R1 obligation.**

## θ pinned exactly

`θ = a(ℓ−a)+1` always (the **deepest-point divisor multiplicity**, Aoyagi Lemma 4/5). `|argmin Adm| = θ`
only for `n = L+1 ≤ 4`; for `n ≥ 5` it **over-counts** (e.g. (2,2,2,2,2): |argmin|=6 but θ=5;
(2,2,2,2,2,2): 10 vs 7) — shallow strata can tie the minimal codim yet not be deepest-point divisor
types. ⇒ θ is NOT |argmin Adm| and NOT the chart count; it is the Lemma-4/5 multiplicity that rides
inside the S2 citation. (Sharpens the §3 θ-seam; confirms the earlier (2,2,2,2,2) 6-vs-5 catch.)

## The corrected R1 obligation + recommended architecture (supersedes design-spec §9.3 flag 3)

Hand the R1 rung the **value-match via stratum codimension**, not a set bijection:
> `λ_core = ½ · min_{t admissible} codim S(t)`, with `codim S(t) = Mval(t)` [proven, general L], and R1
> ACHIEVES the min.

**Recommended R1 architecture (cleaner than chart enumeration):** organize the resolution **by the
nested-rank strata**. Each stratum `S(t)` ⇒ an exceptional divisor with candidate ratio `½·codim S(t)`;
the cover is "the strata partition `{F=0}`"; min over divisor types = `λ_core`; deepest-point divisor
multiplicity = θ. The differential-rank = codim fact is the normal-bundle/transversality input R1 needs.
This replaces a false set-equality with a structural stratification statement — far more Lean-tractable.

> **CORRECTION 2026-06-20 (thread 14 R1-design, controller-integrated).** The phrasing above —
> "each stratum `S(t)` ⇒ AN exceptional divisor", read as a chart/divisor ↔ prefix-stratum
> correspondence — is **too strong** (Codex R1-design consult). A literal smooth-center normal-crossing
> atlas refines strata by the FULL rank-pattern `r_{ab} = rank(C^a···C^b)` + affine-minor (pivot)
> choices, NOT the prefix ranks `t_j`; the prefix `S(t)` partition is right for the codim-MINIMISATION
> (the value) but too coarse for the atlas. The R1↔Adm relationship is **VALUE-level only**:
> `min over charts of the ratios = ½·min_t Mval(t)`, with NO chart↔stratum bijection. Realisation: the
> minimizing branch's BINDING divisor (after iterated L1 exposes the residual block, codim = Mval(t))
> gives ratio `½·Mval(t)` — NOT a "telescoping" of single-rank-drop divisors (also corrected). Full
> architecture (value/atlas split; value via codim not bookkeeping; R3b one-citation route; the
> L1-reuse that shrinks the heavy lift): `threads/14-r1-design/r1-design.md`.

**Codex subtlety to carry:** the naive `{rank P_j ≤ t_j ∀j}` is a *union* of strata; its codim = MIN over
admissible lower rank-vectors (can be < the exact-stratum codim). Phrase R1/A1 via the **exact** strata
(or min over closure), never the naive ≤-conditions.

## Per-case chart blueprint (round 1, all symbolically verified)

- **(1,1,1)** `F=(c₁c₂)²` — already normal-crossing, NO blow-up. Identity chart k=(1,1), h=(0,0),
  min ratio = 1/2 = λ. → cleanest first end-to-end Lean validation.
- **(2,1,2)** `F=(a₁²+a₂²)(b₁²+b₂²)` — 4 product charts; each `F=x²z²(1+y²)(1+w²)`, `|det|=|xz|` ⇒ ratios
  (1,1), min=1=λ, θ=2.
- **(2,2,2)** `F=‖AB‖²` — 24 charts; minimizing chart `F=x²s²·unit`, `|det|=|x|³|s|²` ⇒ ratios (2, 3/2),
  min=3/2=λ, θ=1.

## Validate-small-first ordering (recommended)
`(1,1,1)` [no blow-up] → `(2,1,2)` [cone blow-ups, θ>1] → `(2,2,2)` [recursive resolution].

## Status
Arithmetic/geometry bridge fully de-risked at general L. Only R1's own *construction* (the mountain)
remains — with the clean stratification target above. Scratch: `/tmp/r1_*.py`, `/tmp/l3_*.py`,
`/tmp/l4_tangent.py`, `/tmp/theta_*.py`, `/tmp/codex-r1-*.md`, `/tmp/codex-l3-*.md`.
