# Statement card — R7 sum-of-squares RLCT kernel

The canonical RLCT of a nondegenerate quadratic (sum of squares) in `C` variables, cite-free and
sorry-free. The reusable analytic bedrock under the DLN `rlct = ½·codim` payoff.

## Main result

> **Claim.** For `C ≥ 1`, with `Q y = ∑ i, (y i)²` on `ℝ^C` (the squared ℓ²-norm), the local RLCT
> at `0` is `rlctAt Q 0 = C/2`.
>
> - **Lean:** `RLCT.rlctAt_sumSq`
>   (`lean/DLNFibre/Core/Analysis/RLCT/SumSq.lean` @ `c34fa3ec`)
> - **Gloss.** With `sumSq C : (Fin C → ℝ) → ℝ := fun y ↦ ∑ i, (y i)^2` and the cite-free local RLCT
>   `rlctAt K x = sSup (localAdmissibleExponents K x)` (Local.lean), the hypothesis `1 ≤ C` gives
>   `rlctAt (sumSq C) 0 = (C : ℝ) / 2`.
> - **Proved.** Unconditionally (modulo `1 ≤ C`), sorry-free and cite-free. `#print axioms
>   RLCT.rlctAt_sumSq = [propext, Classical.choice, Quot.sound]` — no `@[cited]` axiom, no `sorryAx`.
> - **Assumed.** `1 ≤ C` (load-bearing: at `C = 0`, `Q ≡ 0` so *every* `c ≥ 0` is admissible and the
>   admissible set is unbounded — the value would not be `C/2 = 0`). Carried in the statement.
> - **Cited.** none. The two Mathlib analytic inputs (`integrable_fun_norm_addHaar` polar reduction,
>   `intervalIntegral.integrableOn_Ioo_rpow_iff` 1-D threshold) are Mathlib theorems, not `@[cited]`
>   axioms.
> - **Deferred.** The **bridge to the DLN germ `K_B = ‖mult − B‖²`** — that at a smooth codim-`C`
>   fibre point `K_B` is a nondegenerate sum of `C` squares in local coordinates — is NOT done here
>   (see the assessment below).
> - **Status.** sorry-free (awaiting fidelity review).

## Supporting results (all sorry-free, axiom-clean)

> **`RLCT.mem_localAdmissibleExponents_sumSq`** `(hC : 1 ≤ C) {c} :`
> `c ∈ localAdmissibleExponents (sumSq C) 0 ↔ (0 ≤ c ∧ 2 * c < C)`.
> The `name = content` characterization; the admissible set is `Set.Ico 0 (C/2)`.

> **`RLCT.integrableOn_ball_norm_rpow_iff`** `(hR : 0 < R) (hs : s < 0) :`
> `IntegrableOn (fun x : EuclideanSpace ℝ (Fin (m+1)) ↦ ‖x‖ ^ s) (ball 0 R) volume ↔ -(m+1) < s`.
> The reusable dimension-`(m+1)` polar/scaling **ball threshold**. Built from the global polar
> reduction + the 1-D `Ioo` threshold, glued by the indicator bridge (the cutoff radial function
> `(Ioo 0 R).indicator (·^s)` is *pointwise* equal to `(ball 0 R).indicator (‖·‖^s)` once `s < 0`).

> **`RLCT.integrableAtFilter_nhds_norm_rpow_iff`** `(hs : s < 0) :`
> `IntegrableAtFilter (fun x : EuclideanSpace ℝ (Fin (m+1)) ↦ ‖x‖ ^ s) (𝓝 0) volume ↔ -(m+1) < s`.
> The germ-at-`0` form (a nbhd contains a ball; the ball threshold reads off).

## Proof route (as built)

1. `Q^(-c)(y) = ‖y‖^(-2c)` is radial. Transport `Fin (m+1) → ℝ` → `EuclideanSpace ℝ (Fin (m+1))`
   via the volume-preserving homeomorphism `WithLp.ofLp` (`PiLp.volume_preserving_ofLp`,
   `map_nhds_eq` for the filter), so `IntegrableAtFilter … (𝓝 0)` transports (`ofLp` a
   `MeasurableEmbedding`, `integrableAtFilter_map_iff`).
2. On EuclideanSpace, the ball threshold: cutoff `f = (Ioo 0 R).indicator (·^s)`, then the global
   polar reduction `integrable_fun_norm_addHaar` turns `∫ f(‖x‖)` into `∫_{Ioi 0} t^m • f t`,
   collapsed to `∫_{Ioo 0 R} t^(m+s)`, thresholded by `integrableOn_Ioo_rpow_iff` (`-1 < m+s`).
3. `c = 0` handled separately (constant `1`, integrable on any finite-measure ball; `0 < m+1`).
4. Endgame: admissible set `= Set.Ico 0 (C/2)`, `sSup = C/2` by `csSup_Ico`.

## Secondary target — constant-rank bridge to `K_B` (ASSESSED, roadmapped, NOT built)

The brief asked to assess whether v4.29 Mathlib lets the sum-of-squares kernel connect to the DLN
germ at a smooth fibre point. Reach, honestly:

- **Bridge (a) — `rlctAt` invariance under a local `C¹` diffeomorphism.** *Buildable*, high reuse.
  Tool present: `MeasureTheory.integrableOn_image_iff_integrableOn_abs_det_fderiv_smul` (Jacobian
  change-of-variables). The lemma needs: `|det φ'|` locally bounded between positive constants near
  the point (so the Jacobian factor does not shift the integrability *threshold*), plus transport of
  the `𝓝` filter through the nonlinear `φ` (an analogue of the linear `ofLp` transport built here).
  A separate module of comparable scale to this one — NOT within this thread's remaining budget.
  Precise target:
  `rlctAt K (φ x₀) = rlctAt (K ∘ φ) x₀` for `φ` a local diffeo at `x₀` with `HasFDerivAt` and
  `(fderiv ℝ φ x₀).det ≠ 0`.
- **Bridge (b) — constant-rank / Morse–Bott normal form.** *Genuine gap; monument-adjacent.*
  Mathlib v4.29 has the inverse and implicit function theorems (`Analysis/Calculus/Implicit`,
  `InverseFunctionTheorem/`) but **no constant-rank theorem and no Morse/Morse–Bott lemma** (the only
  `Morse` file is about Galois groups of polynomials). The claim "`K_B` is a nondegenerate sum of `C`
  squares in local coordinates at a smooth codim-`C` fibre point" needs one of these normal forms;
  building it is itself a substantial differential-geometry contribution, not detail-at-scale.
  Precise target (informal): a constant-rank normal form for `mult` near a smooth fibre point ⟹
  `K_B = ‖mult − B‖²` is, after a local diffeo, `∑_{i<C} (·)²`, whence `rlctAt K_B (pt) = C/2` by
  bridge (a) + `rlctAt_sumSq`.

Net: the model-quadratic kernel is landed as reusable bedrock; bridge (a) is a well-scoped next
build; bridge (b) is a named monument-adjacent gap for a future expedition (or a cite, if the
constant-rank theorem lands in Mathlib).
