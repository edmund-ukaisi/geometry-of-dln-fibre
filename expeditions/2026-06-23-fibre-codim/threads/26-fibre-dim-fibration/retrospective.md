# Thread 26 — H4 fibre-dimension count: retrospective + precise routing

**Type:** formalisation (tide). **Status:** SPECIFY complete + one substantive brick landed; the
**full identity `codim(fibre E) = C + δ` is a controller route-commitment decision** (expedition-scale
hard direction). Banked: the SPECIFY probe (pinned handles + Codex verdict) and the base-stratum Krull
dimension brick. Branch `expedition/fibre-codimension`.

## What landed (green, sorry-free, axiom-clean substrate)

1. **`Core.FibreDimFibrationProbe`** (un-aggregated, probe convention) — every engine handle the count
   consumes, pinned as compiling `example` contracts: `codim Σ̄^r = C`, the δ thermometer, H1 retarget,
   the `FibreCodim` one-sided bound, the primality-gated catenary closer, affine-domain
   equidimensionality, the no-going-down height inequality (Stacks 00OM), base-stratum primality.

2. **`Core.FibreDimFibration.ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta`** —
   `ringKrullDim O(Mat^{≤r}_{m×n}) = δ = r(n+m−r)` (`[IsAlgClosed][CharZero]`, `r≤n`, `r≤m`). Lifts the
   LANDED thermometer `varietyDim = δ` (an `unbotD`-of-`ringKrullDim`) to the genuine `WithBot ℕ∞`
   Krull dimension, using primality (nontrivial domain quotient ⟹ `ringKrullDim ≠ ⊥`). Flatness-free.
   The base-dimension input both the going-down/00OM route and any height-additivity route consume.

3. **`Core.FibreDimFibration.height_maximal_quotient_vanishingIdeal_stratum_eq_delta`** — every maximal
   ideal of the irreducible base `O(Mat^{≤r})` has height `δ`. Equidimensionality at a closed point
   (reusing the `Fintype`-indexed `OrbitTangentCotangent.height_eq_ringKrullDim_of_isMaximal_fintype`)
   with brick 2. The base-side `height(m_E) = δ` the 00OM easy direction consumes. Flatness-free.

4. **`Core.FibreDimEasyProbe.sigmaQuotComap`** (un-aggregated) — the descended base→total algebra map
   `O(Mat^{≤r}) →ₐ[k] O(Σ̄^r)` (`deepBaseComap` through both `sigmaIdeal`s via the LANDED
   `deepBaseComap_sigmaIdeal_le` + `Ideal.quotientMapₐ`). Foundation of the 00OM easy direction.

5. **`Core.FibreDimFibration.affine_domain_height_add_ringKrullDim_quotient_eq_fintype`** — the
   `Fintype`-indexed affine-domain equidim (transport of the `Fin n` engine lemma via `renameEquiv`).
   The nested-catenary / per-component `height ↔ dim` engine.

6. **`Core.FibreDimEasyProbe.height_eq_of_minimalPrimes_bounds`** (un-aggregated) — the **H5
   min-over-components closer**, interface-agnostic: `height I = v` from a uniform lower bound (every
   minimal prime `height ≥ v`) + one witness (`height ≤ v`). Pure `ℕ∞` lattice over `Ideal.height =
   ⨅ minimalPrimes primeHeight`.

7. **`Core.FibreDimHeadlineProbe.codimRepCanonical_fibre_eq_of_minimalPrimes_height_bounds`**
   (un-aggregated) — **the pre-staged headline**, with thread 27's per-component facts as explicit
   hypotheses: given every minimal prime of `fibreGenIdeal d B` has `height ≥ v` and one has
   `height ≤ v`, then `codimRepCanonical (fibre d B) = v`. With `v = C+δ` this IS the headline. Proved
   by wiring H1 + the H5 closer. So the final tide is a **thin substitution** of thread 27's facts;
   every other step is machine-checked. Axiom-clean.

**The assembly skeleton is COMPLETE on the engine side.** The full `codimRepCanonical(fibre E) = C+δ`
factors as: **bridge** `height P + dim(R⧸P) = card` (LANDED `NullstellensatzCodim.height_add_
ringKrullDim_quotient_eq_card`) — converts per-component dim to height; **closer**
`height_eq_of_minimalPrimes_bounds` (landed) — `⨅` collapse to `C+δ`; **retarget** H1 (landed). The
**only open input** is thread 27's per-minimal-prime facts: `dim(R⧸P) ≤ card−C−δ` for every component
(⟹ `height P ≥ C+δ`) and `= card−C−δ` for the top (⟹ `height P ≤ C+δ`), i.e. `rank(fibreJacobian) ≥
C+δ` generically on every component (the no-jump residual). When thread 27 lands that, the headline
closes by wiring these landed bricks — no further engine work.

**Aggregation:** `Core.FibreDimFibration` (bricks 2,3,5) is reusable bedrock and wants the aggregator
import line `import DLNFibre.Core.FibreDimFibration` (controller's single-writer call). The two probes
(`FibreDimFibrationProbe`, `FibreDimEasyProbe`) stay un-aggregated (probe convention) — though the H5
closer (brick 6) and `sigmaQuotComap` could promote into `FibreDimFibration` once the headline wires.

## The decorrelated Codex verdict (xhigh, `codex/answer-realization.md`) — the load-bearing finding

The thread spec's premise was: the fibration `mult|_{Σ̄^r} ↠ Mat^{≤r}` + generic-fibre-dimension via
the trdeg toolkit gives `dim(fibre E) = dim Σ̄^r − dim Mat^{≤r} = card−C−δ`, sidestepping the
thread-20 flatness wall. **Codex (and an independent grep) refute the "sidestep" for the CLOSED fibre:**

- `trdeg_add_eq` computes only the **GENERIC fibre** (fibre over the generic point of `Spec O(base)`).
  Connecting it to the **closed** fibre over `E` (a closed, rank-exactly-`r` point) needs a **no-jump**
  statement = local flatness / going-down / product-triviality on the exact-rank chart.
- **Mathlib v4.29 has NO packaged generic-flatness theorem** (grep-confirmed). The only height-
  additivity *equality* `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` (Stacks 00ON) needs
  `Algebra.HasGoingDown ⟸` flatness — and `mult` is **not** globally flat (the fibre dimension *jumps*
  as the rank drops: `(2,2,2)` rank-1 fibre dim 4 vs rank-0 fibre `Σ̄^0` dim 5). So the closed-fibre
  count routes through the **same** flatness wall threads 09/14/20 hit.

So the thread's stated route ("fibration sidesteps thread-20") is **only half-true**: it sidesteps the
wall for the *generic* fibre, not the *closed* fibre over `E`.

## The two directions, precisely located

- **Easy `codim(fibre E) ≤ C+δ` — FLATNESS-FREE, reachable.** Via the no-going-down inequality
  `Ideal.height_le_height_add_of_liesOver` (Stacks 00OM, present, no flatness). Descend `deepBaseComap`
  to `O(Mat^{≤r}) →ₐ[k] O(Σ̄^r)` (via the LANDED `deepBaseComap_sigmaIdeal_le` + `Ideal.quotientMapₐ`);
  for a fibre component `P` minimal over `m_E·(O Σ̄^r)`, lying over the maximal `m_E`:
  `height_{O Σ̄^r} P ≤ height(m_E) + 0 = δ`; catenary through a top component `W` of Σ̄^r (codim `C`)
  ⟹ `codim(that component) ≤ C+δ` ⟹ `min ≤ C+δ`. A multi-lemma build (~5–7 lemmas: descended algebra,
  `m_E` maximal + `height = δ`, lies-over, relative-height-0, catenary-through-`W`, reindex), but every
  step is reachable from landed engines. This is the half worth landing if the controller opts for
  land-the-half.

- **Hard `codim(fibre E) ≥ C+δ` — the genuine no-jump residual.** Needs *every* fibre component to
  have dim ≤ card−C−δ. By upper-semicontinuity of fibre *dimension*, the fibre over a *special* point
  can be larger (codim smaller); that `E` (rank-exactly-`r`, dense-open stratum) lies in the good
  locus is exactly **generic flatness / Chevalley** — absent from Mathlib v4.29. The flatness-free
  substitute is route B (generic smoothness, engine substrate present: `SmoothPointRegular`,
  `SmoothLocalRelativeDimension.ringKrullDim_localizationAtPrime_eq_of_isSmoothAt`, `FibreJacobian`
  H3a): show `rank(fibreJacobian) ≥ C+δ` at a generic point of *every* component ⟹ every component dim
  ≤ card−C−δ. The H3 cert's "lower-dim components carry HIGHER rank" is consistent with a **uniform**
  Jacobian-rank lower bound `≥ C+δ` over the whole fibre — a potentially clean, component-free claim,
  but unproven and the hard rung. This is dimension-dependent and multi-rung — **expedition-scale**,
  the same wall threads 01/09/14/20 located, now pinned to the uniform-Jacobian-rank / generic-flatness
  statement.

## Recommendation (controller decision)

The full `codim = C+δ` is not one-tide reachable at v4.29 (the hard direction = the recurring wall).
Options, mirroring the prior gate contracts:
- **(a) Land the easy half** `codim(fibre E) ≤ C+δ` (flatness-free, the ~5–7-lemma build above) +
  the base-δ brick, name the hard direction as the precisely-located certified-true residual. Pairs
  with the LANDED `FibreCodim` `codim ≥ C` to bracket `C ≤ codim ≤ C+δ`.
- **(b) Commit route B** (generic-smoothness uniform-Jacobian-rank) as a multi-rung sub-build for the
  hard direction `≥ C+δ`. Residual risk on the uniform `rank ≥ C+δ` lemma; needs a dedicated probe.
- **(c) Keep `BundleShiftInterface` Cited**, bank the base-δ brick + SPECIFY routing as the deliverable.

No result here discharges `BundleShiftInterface`. The `+C` (catenary, Brick A) and `+δ` (this brick)
are both in hand on the *base* side; only the closed-fibre no-jump (`≥`) blocks the full identity.

## Codex consult

`codex/prompt-realization.md` + `codex/answer-realization.md` (gpt-5.5, xhigh, read-only). Verdict:
Route B (per-component height) over Route A (global varietyDim); the fibration count is NOT carried by
`trdeg_add_eq` to the closed fibre; build the no-jump explicitly or name it the hard rung.
