# Thread 07 — Transfer-T route certificate (the geometric wall)

**Type:** pen-and-paper / scout. **No Lean written.** Output: proof-route certificate + feasibility
verdict for the T formaliser tide. Decorrelated Codex consult banked in `codex/`.

## The target (recap)

**T:** `codimRepCanonical (k:=ℝ) (fibre ℝ d B) = codimRepCanonical (k:=K) (fibre K d (B.map ι))`
for `[Field K][IsAlgClosed K][CharZero K]`, `ι:ℝ→+*K`, DLN scope (`0<N`, `B.rank=r≤min d`). Both
sides = `Ideal.height (vanishingIdeal · (real/complex points))`.

---

## VERDICT: (iii) — T must stay an explicitly CITED field at Mathlib v4.29.

T is **TRUE** (truth-value confirmed below by exact algebra) but **not provable in a bounded tide**;
the honest route is to carry the real↔complex passage as a **named, exposed** cited hypothesis — never
re-buried. Decorrelated Codex (xhigh, value-withheld) reached the same verdict (iii) independently and
corroborated every load-bearing step (`codex/transfer-T-answer.md`).

---

## The reformulation that ISOLATES the wall (Observation 1 — load-bearing)

The catenary identity `codimRepCanonical Z + varietyDim Z = card` is **field-generic** — proved in
`Core.RadicalCatenary.codimRepCanonical_add_varietyDim_eq_card_of_nonempty` for **any** `[Field k]` and
any nonempty `Z` (no `[IsAlgClosed]`; it rests on `MvPolynomial σ k` catenary + Krull-dim = `card`,
which hold over ℝ and over K identically). `card` = `Nat.card (RepCoord d)` = number of matrix entries
= field-independent.

Therefore, with both fibres nonempty (the rational realizer base-changes onto both — banked
`fibre_normalForm_nonempty`):

> **T  ⟺  T′ :** `varietyDim_ℝ(fibre ℝ d B) = varietyDim_K(fibre K d (B.map ι))`
> — i.e. **the real dimension equals the complex dimension** of the (base-changed) fibre.

The dimension form `T′` is the cleaner geometric core; the codimension form `T` follows by left-cancel
of the finite `card`. **The wall is `T′`, not the catenary.**

## Why the wall is genuine — the `x²+y²=0` trap (the crux)

`codimRepCanonical (k:=ℝ) Z = height (vanishingIdeal_ℝ Z)` is the height of the **real radical** of the
defining ideal — the vanishing ideal of the real *point set*. This is strictly larger than the radical
of the generator ideal exactly when the real points fail to fill the complex variety:

- `I = (x²+y²)` over ℝ: `V_ℝ(I) = {0}`, so `vanishingIdeal_ℝ = (x,y)`, height **2**.
- over K: `(x²+y²) = (x+iy)(x−iy)`, radical itself, height **1**.
- The complex variety has two components, **each containing the rational point (0,0)**.

So `codim_ℝ = 2 ≠ 1 = codim_K`: **T fails for this ideal.** A rational point on every top component is
NOT enough (banked F3 alone does not give T). The escape requires the real points to be Zariski-dense
in the top complex components — concretely, a **smooth real point of full local dimension** on each.

## Truth-value of T for DLN — CONFIRMED TRUE (exact algebra, deliverable 1)

The DLN fibre escapes the trap. Exact-rational Jacobian computations (sympy, `decide`-grade integer
points; not float):

- **`(2,2,2)` r=0**, ambient dim 8, complex codim `C = 3` (LR Ex 4.3) ⟹ complex dim 5.
  - The **interval-direct-sum realizer** `A₁ = E₂₂ = [[0,0],[0,1]]`, `A₂ = E₁₁ = [[1,0],[0,0]]`
    (`A₂A₁ = 0`, disjoint interval supports): **Jacobian rank 3 = codim, real local dim 5 = complex
    dim.** SMOOTH, full-dimensional real point. ✓
  - Contrast — other 0/1 rank-0 points are NOT smooth full-dim: `A₁=0,A₂=I` and `A₁=I,A₂=0` both give
    **Jacobian rank 4 ≠ 3, real local dim 4 < 5** (they sit at a *component crossing* / lower stratum).
  - ⟹ **the disjoint-interval-support structure of `realizerD` is exactly what lands it in the smooth
    interior of one top component** — not a generic 0/1 tuple. This is a real structural certificate.
- **`(2,3,2)` r=1** (odd width, rank > 0), ambient 12. Interval-staircase realizer
  `A₁=[[1,0],[0,0],[0,0]]`, `A₂=[[1,0,0],[0,0,0]]` (`A₂A₁ = E₁₁ = B`): **Jacobian rank 3, real local
  dim 9.** A search over rational fibre points found **max real local dim = 9 = the complex dim** ⟹
  `dim_ℝ = dim_K` here too. ✓

**Mechanism (the math-level why):** the fibre over the normal form is, after the banked base-change /
sweep, an orbit closure `Ō_M` bundled over `GL_{d_N}×GL_{d_0}`, with `M = realizerD` and the whole
construction defined over ℚ. `GL·M` is the image of the ℚ-rational map `g ↦ g·M` (an open of affine
space); orbit closures are **ℚ-unirational**, and ℝ-points of ℚ-rational affine space are Zariski-dense
(ℝ infinite). Hence real points are dense in each top component ⟹ `dim_ℝ = dim_K`. The interval-block
realizer's disjoint-support structure is the concrete witness that it is a smooth, full-dimensional
real point of a single component (not a crossing).

## Route adjudication (deliverable 2) — all three blocked in a bounded tide

- **(a) dim/trdeg route** (`height = card − dim`, then `dim_ℝ = dim_K` via a field-independent invariant
  like trdeg): the catenary half is banked & field-generic, BUT the engine `ringKrullDim (R⧸p) = trdeg`
  for a finitely-generated algebra (the AG dimension theorem) is **ABSENT** in v4.29, as is any
  scalar-extension invariance of `ringKrullDim` or `trdeg`. Mathlib has `trdeg`/`IsTranscendenceBasis`
  and `AlgebraicIndependent.restrictScalars/extendScalars`, but not the bridge. From-scratch, multi-file.
- **(b) chain-of-primes from the realizer:** the rational realizer is a single closed point, not a
  prime chain; pinning full local real dimension from it needs the smooth-point ⟹ regular-local-ring
  dimension theory **over ℝ**, plus "the real vanishing ideal sees the top component." Not bounded.
- **(c) direct `vanishingIdeal` base-change `ℝ→K` via comap/map:** the SHARP trap. The map
  `Φ : MvPolynomial σ ℝ → MvPolynomial σ K` (apply `ι` to coefficients) is faithfully flat, so a height
  base-change lemma for the **generator** ideal `IF_ℝ` vs `IF_K = IF_ℝ.map Φ` may be boundedly provable
  (going-down). **But that is not T.** T compares `height(vanishingIdeal_ℝ) = height(√_ℝ IF_ℝ)` with
  `height(vanishingIdeal_K) = height(√ IF_K)`; the **real-radical-vs-radical gap is the entire content**
  and is precisely where `x²+y²` breaks. A working height-base-change lemma would give the WRONG
  equality. (Codex independently flagged this exact point.)

## Mathlib v4.29 inventory (deliverable 3)

- **HAS:** `Ideal.height`, `RingEquiv.height_comap/_map`, `IsLocalization.height_comap`,
  `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`; the catenary `height p + ringKrullDim(R⧸p)
  = card` (repo `NullstellensatzCodim`); `MvPolynomial.ringKrullDim_of_isNoetherianRing`;
  `ringKrullDim_quotient_comap_ringEquiv`; `trdeg`, `IsTranscendenceBasis`, `AlgebraicIndependent`
  (+`restrictScalars`/`extendScalars`); `IsRealClosed` (purely field-theoretic: squares/signs/odd roots
  — `FieldTheory/IsRealClosed/Basic.lean`).
- **ABSENT (confirmed by grep over the pinned tree):** any `ringKrullDim` base-change / tensor lemma;
  any `height` base-change under a field extension; any `ringKrullDim = trdeg` (AG dimension theorem);
  any scalar-extension invariance of `ringKrullDim`/`trdeg`; any semialgebraic-dimension theory; any
  **real Nullstellensatz / real radical**; any `vanishingIdeal` base-change for `MvPolynomial`.
- **Repo:** the ENTIRE `codim_K(fibre) = C+δ` chain + all smoothness (`isSmoothAt_sweepFibre_*`,
  `dense_smoothLocus_of_perfectField`) require `[IsAlgClosed k][CharZero k]`. There is **nothing** over
  ℝ. T is the only bridge from the honest real codim to the computable complex one.

## The honest fallback (the deliverable, not a retreat)

The connector `zeroLocus_lossDLN_eq_fibre` (banked) makes the rlct an invariant of the **real** loss
whose zero-set is `fibre ℝ B`, so the honest seam is `rlct = ½·codim_ℝ(fibre ℝ B)` and **T transports
to the computable `codim_K`.** Two equivalent honest shapes for the tide (controller picks):

1. State the cited interface over `codim_ℝ(fibre ℝ B)` and carry **T** as a separate named cited field
   `cited_real_complex_codim_transfer` (the real↔complex passage, exposed, with the `x²+y²` caveat in
   its docstring). T is part of what Aoyagi/Watanabe Cite (real-analytic resolution over ℝ).
2. Keep the interface stating `½·codim_K(fibre K (B.map ι))` directly **but** rename/re-docstring it so
   the swallowed real↔complex step is named (the current docstring at `RlctPayoff.lean:267–272` —
   *"No from-scratch real↔complex base-change lemma is needed"* — is the trap; it hides T).

**NAME-GATE:** whichever shape, T (= `dim_ℝ = dim_K`, the real-radical density fact) must be a *named,
visible* cited hypothesis, never an implicit consequence of an `…codim…` lemma.

## If the operator wants T PROVED (scope of the build — deliverable 4(ii))

A genuine real-algebraic-geometry build, roughly: (1) a `varietyDim_ℝ` matching `height(vanishingIdeal_ℝ)`
[banked]; (2) "smooth real point of full local dim ⟹ real local dim = complex dim there" — needs
regular-local-ring dimension over ℝ + a real-points-dense argument; (3) "the interval-direct-sum
realizer is a smooth full-dim real point of a top component, for all `d,r`" — generalize the exact-
algebra certificate above (Jacobian rank = codim at `realizerD`, disjoint-support ⟹ single component);
(4) glue per-component to `dim_ℝ = dim_K`. Multi-file; the regular-local-dimension-over-ℝ and
density steps are the heavy parts. **Not a bounded tide.** Recommendation: cite T now; roadmap the
build as a future expedition (it is the same wall the `rlct-runway-target` memo names — a singular-locus
/ real-dimension lower bound).

## Structure & ideas observed (data, not a Lean route — registered as Speculation/Question)

- **[Speculation] `realizerD` smoothness is certifiable per-instance** but the general theorem
  ("`realizerD m` is a smooth full-dim real point of one top component, all `d,r`") is the unbuilt
  brick. The disjoint-interval-support is the structural reason; a Jacobian-rank-`=codim`-at-`realizerD`
  lemma is the concrete target if the build is ever scoped.
- **[Speculation] ℚ-unirationality** of the orbit closure / sweep is the clean sufficient hypothesis for
  density; if Mathlib ever gains "unirational over an infinite field ⟹ rational points Zariski-dense",
  that single theorem + the banked sweep would discharge T. Worth a Mathlib-watch.
- **[Question]** Does the `δ`-shift (the GL-bundle factor) ever introduce a real-vs-complex dimension
  drop? The `(2,3,2)` r=1 check (δ>0) says no — the GL factor is `GL_n`, whose ℝ-points are dense — but
  this was not exhaustively certified across odd ranks. (Confidence high; the GL factor is unirational.)

## Codex (decorrelated) — `codex/transfer-T-prompt.md` + `transfer-T-answer.md`

Value-withheld prompt (frame in, facts in, hypothesis out). Codex independently returned **(iii)**,
identified the catenary as field-generic / not-the-obstruction, ruled out (a)/(b)/(c) with the same
real-radical reasoning, flagged `x²+y²` as decisive, and named the same sufficient condition (smooth
real point of full local dim per top component). Full decorrelation — converged on the verdict.
