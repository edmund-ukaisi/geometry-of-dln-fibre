# Thread 13 — close the (1,1,1) `rlctAt` bridge (baby-S1.1) — STOPPED on a precise obstruction

- **Seat:** `fm-2` (formaliser). MAIN, `expedition/aoyagi-full`. Work confined to `Case111Bridge.lean`
  (told to stay out of `Skeleton.lean` — the L1/L2 fix-loop runs there).
- **Goal:** prove `case111_rlct_eq_monomialThreshold` (`rlctAt ![1,1,1] (dlnLoss …) deepest111 =
  monomialThreshold 2 ![1,1] ![0,0]`) sorry-free ⇒ first fully axiom-free + sorry-free end-to-end.
- **Outcome:** NOT closed. Two of the three pieces built clean (banked); piece 1 (the `Params ≃ᵐ ℝ²`
  measure-preserving map) **blocked** by a `Params`-as-`def` type obstruction. Stopped per the
  controller's bounded/anti-thrash instruction for exactly this piece. Bridge `sorry` stands.

## Banked (sorry-free, axiom-clean, reusable S1.1 infra — in `Case111Bridge.lean`)

- `abs_rpow_integrableOn_Ioo_iff (s ε) (hε : 0 < ε) : IntegrableOn (|·|^s) (Ioo 0 ε) ↔ -1 < s`
  (piece 2, right half — `|x| = x` on the positive half, then the single-axis rpow iff). The
  two-sided `[-ε,ε]` version (the `𝓝 0` chart, crossing 0) just glues this with the reflected
  negative half — see "the neg-invariance snag" below.
- `measurePreserving_matrixEntry₁₁ : MeasurePreserving ((funUnique (Fin 1) (Fin 1→ℝ)).trans
  (funUnique (Fin 1) ℝ)) volume volume` — the per-layer `(Fin 1 → Fin 1 → ℝ) ≃ᵐ ℝ` is
  volume-preserving (twice-`funUnique`).

## THE OBSTRUCTION (piece 1 — `Params (1,1,1) ≃ᵐ (Fin 2 → ℝ)` measure-preserving)

The forward map `mkParams111 v = fun s _ _ ↦ v s : (Fin 2 → ℝ) → Params (1,1,1)` is the natural
inverse-direction map. Proving it measure-preserving via `volume_preserving_pi` (the right tool — it
turns per-layer MP maps into a pi-MP map) **fails**, and the root cause is uniform across three probes:

> `Params H = ∀ s : Fin L, Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ`. For `H = ![1,1,1]` the
> fiber at a **concrete** `s` reduces to `Fin 1 → Fin 1 → ℝ` (by `fin_cases s; rfl`), but **NOT
> uniformly in symbolic `s`** — `![1,1,1] s.castSucc` does not whnf-reduce. So:
> - `volume_preserving_pi` wants a uniform fiber `β' : Fin 2 → Type` with `[∀ i, MeasureSpace (β' i)]`;
>   the actual `Params` fiber gives **no `MeasurableSpace (Matrix (Fin (![1,1,1] s.castSucc)) … ℝ)`
>   instance** for symbolic `s` (Matrix-as-`def` + non-reducing width blocks synthesis);
> - `mkParams111` is **not even defeq** to the uniform-Pi form `fun a i _ _ ↦ a i`
>   (`(Fin 2 → ℝ) → (Fin 2 → Fin 1 → Fin 1 → ℝ)`): the codomain `Params (1,1,1)` ≠ `∀ _, Fin 1→Fin 1→ℝ`
>   syntactically (`rfl` fails; `volume`s have different types);
> - phrasing the fiber explicitly as `Matrix (Fin (![1,1,1] s.castSucc)) (Fin (![1,1,1] s.succ)) ℝ`
>   re-hits the missing `MeasurableSpace` instance.

This is exactly the "Matrix-unfold is fiddly" piece the controller flagged. The math is trivial; the
obstruction is Lean's dependent-fiber + `Matrix`-`def` plumbing.

### Candidate escapes (for `pp`/controller to pick)

1. **`Fin 2`-split via `finTwoArrow`/`piFinTwo`** (`measurePreserving_piFinTwo`): split the outer pi into
   the two **concrete** layers `0,1` (where the widths reduce), build a MP `Params (1,1,1) ≃ᵐ ℝ × ℝ`
   per-concrete-layer, then `≃ᵐ (Fin 2 → ℝ)` via `finTwoArrow.symm`. Avoids the symbolic-`s` fiber.
   **ATTEMPTED — hits the SAME wall + a diamond risk.** `MeasurableEquiv.piFinTwo`'s implicit
   `{m : ∀ i, MeasurableSpace (α i)}` cannot be synthesised for the symbolic `Params` fiber (same
   non-reduction), and `fin_cases`/`Fin.cases` cannot build a `MeasurableSpace` (data, not `Prop`) into
   that implicit slot. Supplying the `∀ i, MeasureSpace (pfib i)` by a `match i with | 0 | 1` term DOES
   typecheck, but it is a **separate instance path** from the one `Params`'s own `volume` (via
   `inferInstanceAs`) was built from — so the `piFinTwo` MP would not compose with `Params`'s `volume`
   without proving the two instance paths agree (instance-diamond reconciliation). Not a focused close.
2. **Define `Params` reductions up front**: a `simp`-lemma `Params (![1,1,1]) = (Fin 2 → Fin 1 → Fin 1 → ℝ)`
   (provable by `Params`-unfold + `Matrix`-unfold + width `decide`), then work on the uniform Pi and
   transport `rlctAt`/`dlnLoss` across the (now syntactic) equality. Cleanest if it holds as `rfl`-after-`simp`.
   UNTRIED — but `Params (![1,1,1]) = (∀ _ : Fin 2, Fin 1 → Fin 1 → ℝ)` failed by `rfl` (the type
   equality is NOT definitional for the same symbolic-`s` reason), so this needs a genuine type-`Eq`
   + `MeasurableEquiv.cast`/transport, not a `simp` rewrite — likely as fiddly as #1.
3. **Skip the equiv**: bespoke `IntegrableOn`-on-`Params`. `dlnLoss_case111` already gives the loss as a
   function of the two concrete entries `A 0 0 0, A 1 0 0` (no symbolic `s`!), so the *integrand* is
   expressible. BUT relating its `Params`-`volume` integral over a box-nbhd to the 2-D box integral still
   needs a measure-transport — i.e. it does NOT actually sidestep the equiv, only defers it.

**Recommendation:** the clean fix is a small reusable Mathlib-style helper —
`Params (![…]) ≃ᵐ EuclideanSpace ℝ (Fin N)` (or the flat pi) **measure-preserving**, built once for the
concrete width vector with the instance paths reconciled — which is a Core/Foundations design decision
above a leaf executor. Hand to `pp` for the blueprint or have the controller add the helper to
`Foundations`. The bridge is then a short assembly (banked piece 2 + `Case111Bridge`'s box machinery).

### The neg-invariance snag (piece 2, two-sided) — RESOLVED

The two-sided `[-ε,ε]` abs-rpow lemma needs `(volume : Measure ℝ).IsNegInvariant` for the reflected
negative half (`Measure.measurePreserving_neg`). The providing import is
**`Mathlib.MeasureTheory.Measure.Haar.Unique`** (bisected). With it, the full two-sided lemma
`abs_rpow_integrableOn_Icc_symm_iff` is banked (sorry-free): forward by restricting to the right half,
reverse by gluing the two halves with the negative half reflected through `x ↦ -x`
(`MeasurePreserving.integrableOn_comp_preimage`, `|·|` even). Piece 2 COMPLETE.

## Decision (controller): PARK the full bridge; piece 1 deferred to the general equiv

Per the controller: **park the `(1,1,1)` full bridge** — don't take escape #1 (the `finTwoArrow`
split is `(1,1,1)`-throwaway plumbing). The real obstacle, a **general `Params H ≃ᵐ ℝ^N`
measure-preserving equiv**, is needed at the S1.1 use-site and for R1; it will be built once there
(symbolic-`s`/Matrix-fiber handled properly — `MeasurableEquiv.piCongr` per layer +
`Matrix ≃ᵐ (Fin (a·b) → ℝ)`), and `(1,1,1)` closes as a byproduct. Recorded as a known S1.1 sub-task.

## Status

Full `lake build` green; `scripts/sorries`: **12 sorry, 0 #exit, 0 native_decide, 1 axiom** —
UNCHANGED (the bridge `sorry` stands by decision; the banked lemmas are sorry-free additions). Banked,
sorry-free + axiom-clean: `abs_rpow_integrableOn_Ioo_iff`, **`abs_rpow_integrableOn_Icc_symm_iff`**
(piece 2 complete), `measurePreserving_matrixEntry₁₁` (toward piece 1). The probe win
(`monomialThreshold_case111` axiom-free) remains the banked headline. Bridge waits on the general
`Params ≃ᵐ ℝ^N` equiv (comes with S1.1).
