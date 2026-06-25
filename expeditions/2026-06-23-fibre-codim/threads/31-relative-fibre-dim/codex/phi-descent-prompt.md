# Φ-descent evaluation lemma + zero-test (Lean 4 + Mathlib v4.29, DLNFibre)

Continuation of the seam-D build. The Ψ-direction (chartPsiLoc) is DONE. I'm building the Φ
direction. The remaining hard step is the **descent obligation**:

```lean
theorem chartPhi_vanishingIdeal_le [Infinite k] (d) (r) (hp) (hq) :
    vanishingIdeal k (sweepFibre k d r hp hq)
      ≤ RingHom.ker (chartPhiFibAeval k d r hp hq).toRingHom
```

i.e. a polynomial `p` vanishing on the FIBRE `F` maps to `0` under the Φ fibre comorphism
`chartPhiFibAeval : MvPolynomial (RepCoord d) k →ₐ[k] Localization.Away dsig`.

## The setup (all LANDED/built, sorry-free)

- `O(Σ) = MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Σ^r` (Σ^r = rank-EXACTLY-r product locus).
- `dsig = mk(vanishingIdeal Σ^r) ΔPdeep`, `ΔPdeep = det of the top-left r×r minor of M = mult`.
- `Away dsig = Localization.Away dsig`, which localizes the **vanishingIdeal-quotient** `O(Σ)`.
- `chartPhiTower := aevalTower schurToDsig sigmaCoordT : MvPolynomial (RepCoord d) SchurLoc →ₐ[k] Away dsig`.
  - `sigmaCoordT x = algebraMap O(Σ) (Away dsig) (mk_Σ (X x))` (source coord embedding).
  - `schurToDsig : SchurLoc →ₐ[k] Away dsig` = `liftAlgHom` of `aeval chartPhiVarSub`
    (`chartPhiVarSub : SchurVar → Away dsig` reads SchurVar generators off the product-matrix blocks).
- `chartPhiFibSub x = chartPhiTower (gaugeSub d endpointGauge x)`  (FORWARD gauge, not inverse).
- `chartPhiFibAeval = aeval chartPhiFibSub`.

The geometry: Φ is the comorphism of the FORWARD chart map `Φ(A) = (mult A, chartGauge(mult A) • A)`.
`endpointGauge` is the SchurLoc-valued gauge (H at vertex 0, L⁻¹ at last); `chartGauge M` is the
k-valued version. LANDED: `chartGauge_mem_fibre : chartGauge(mult A) • A ∈ fibre (normalForm)` for A in
the chart (`rank (mult A) ≤ r`, pivot block invertible). I.e. the forward chart map RETRACTS Σ^r onto F.

## What I have on the Σ side (the localized vanishingIdeal-quotient zero-test, LANDED)

```lean
theorem away_eq_zero_iff_exists_pow_mul_mem (Z : Set (σ → k)) (f₀ a : MvPolynomial σ k) :
    (IsLocalization.mk' (Localization.Away (mk (vanishingIdeal Z) f₀)) (mk (vanishingIdeal Z) a) 1 = 0)
      ↔ ∃ n : ℕ, f₀ ^ n * a ∈ vanishingIdeal Z
```

For comparison, the Ψ side (target localizes a POLYNOMIAL ring over O(F), not a vanishingIdeal-quotient)
used a DIFFERENT route: `mk'`-surjectivity + a general away zero-test
`away_mk'_eq_zero_iff_exists_pow_mul_eq_zero` + a coefficientwise zero-test
`mvpoly_eq_zero_of_forall_eval_fibre` (over `[Infinite k]`, via `MvPolynomial.funext`), evaluating
`chartPsiAeval p` at chart points realized as `baseChange P B` for fibre points B.

## The question

What is the cleanest route to discharge `chartPhi_vanishingIdeal_le`, exploiting that the target
`Away dsig` localizes the **vanishingIdeal-quotient** `O(Σ)` (so the Σ-side primitive
`away_eq_zero_iff_exists_pow_mul_mem` applies DIRECTLY)?

Candidate route I'm considering:
1. Write `chartPhiFibAeval p = mk'(mk_Σ a)(ΔPdeep^n)` for some RepCoord-poly numerator `a` and power n
   (via `IsLocalization.mk'_surjective` on `Away dsig`).
2. By `away_eq_zero_iff_exists_pow_mul_mem`, reduce to `ΔPdeep^m · a ∈ vanishingIdeal Σ^r` for some m,
   i.e. `ΔPdeep^m · a` vanishes on every chart point A ∈ Σ^r.
3. Build a chart-point evaluation `evalSigmaAway : Away dsig →ₐ[k] k` for each A ∈ Σ^r with ΔPdeep(A)≠0
   (via `IsLocalization.liftAlgHom (aeval (canonicalCoord A))`, ΔPdeep(A) a unit), and an evaluation
   lemma `evalSigmaAway A (chartPhiFibAeval p) = aeval (canonicalCoord (chartGauge(mult A) • A)) p`
   (the FORWARD-gauge translate, mirror of the Ψ side's `evalAway_chartPsiAeval`). Then `p` vanishes on
   F and `chartGauge(mult A)•A ∈ F` (LANDED `chartGauge_mem_fibre`), so the evaluation is 0.
4. Conclude `ΔPdeep^m · a` vanishes on Σ^r (the numerator vanishes wherever ΔPdeep ≠ 0, and the ΔPdeep^m
   factor kills the ΔPdeep = 0 locus — same split as the Ψ side's `δ(s)=0` branch).

QUESTIONS:
(A) Is route (1)-(4) the cleanest, or is there a more direct one exploiting the vanishingIdeal-quotient
    structure (e.g. work entirely with `away_eq_zero_iff_exists_pow_mul_mem` and a SINGLE point-vanishing
    argument, avoiding the `mk'`-surjective numerator extraction)?
(B) For the evaluation lemma (step 3): the Φ side's `chartPhiFibAeval` routes through `schurToDsig`
    (a LIFT, inverting detSchurS) and `sigmaCoordT`. To evaluate `evalSigmaAway A (chartPhiFibAeval p)`,
    I chain `evalSigmaAway ∘ chartPhiTower = aevalTower (schurEval at A's Schur data) (canonicalCoord A)`
    then `aevalTower_gaugeSub` (LANDED A.4 commute) at the FORWARD gauge. Does this mirror cleanly, and
    what is "A's Schur data" — i.e. how do I produce the SchurLoc-point `s` such that detSchurS(s) ≠ 0
    from a chart point A ∈ Σ^r? (On the Ψ side `s` was GIVEN; here `A` is given and `s` must be the
    Schur blocks of `mult A`.)
(C) Does the Φ descent need `[Infinite k]`? (The Σ-side primitive itself does not; but step 4's
    "vanishes wherever ΔPdeep≠0 ⟹ ΔPdeep^m·a ∈ vanishingIdeal" might, if it routes through funext.)
(D) The single most-likely-to-break step, and the cleanest Mathlib API for it (v4.29).

Be concrete and Lean-shaped. Verify cited API is plausibly at v4.29.
