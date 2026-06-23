**Verdicts**

**R1: ray-constancy + limit.** Mostly right, but the “limit” is unnecessary.

- [PROVABLE-FROM-LISTED + R3] For every `s > 0`,
  ```lean
  rlctAt K (s • w) = rlctAt K w
  ```
  follows from constant-Jacobian scaling plus `K (s • x) = s^d * K x` and `rlct_unit_invariant`.

- [PROVABLE-FROM-LISTED] To compare with `0`, do not take `s → 0`. Let `c` be admissible at `0`, witnessed by an open `U ∋ 0` with finite integral. For any fixed `w`, choose `0 < s ≤ 1` with `s • w ∈ U`. Then the same `U` witnesses admissibility of `c` at `s • w`. Ray-constancy gives
  ```lean
  c ≤ rlctAt K (s • w) = rlctAt K w
  ```
  hence every admissible `c` at `0` is bounded by `rlctAt K w`, so
  ```lean
  rlctAt K 0 ≤ rlctAt K w.
  ```

- Numeric ray-constancy alone would not imply anything about the value at the limiting point `0`. The extra input is the existential neighborhood witness in the RLCT definition, not lower semicontinuity and not really the down-set structure.

**R2: direct domination, no transport.** Fails as a general route.

- [PROVABLE-FROM-LISTED] `rlctAt_mono` compares two functions at one basepoint. Your desired inequality compares `K` at `0` with `K` at `w`.

- To make it same-point, one would recenter and compare germs at `0`:
  ```lean
  u ↦ K u
  u ↦ K (w + u)
  ```
  but that already uses translation transport if you want to identify `rlctAt (fun u ↦ K (w+u)) 0` with `rlctAt K w`.

- Worse, homogeneity gives scaling information, not translation domination. A local inequality like
  ```lean
  |K u| ≤ C * |K (w + u)|
  ```
  is false in general. Example:
  ```text
  K(x,y,z) = (y^2 - x*z)^2,    w = (1,0,0).
  ```
  Then for `u = (0, ε, ε^2)`, `w+u` lies on the zero cone, so `K(w+u)=0`, but `K(u)=ε^4 ≠ 0`. So no same-point domination can prove the result in this form.

**R3: constant-rescaled-measure invariance.** Correct, and this is the clean missing tool.

- [NEEDS-STANDARD-MATHLIB] Multiplying a measure by a finite positive constant preserves finiteness of nonnegative integrals:
  ```text
  ∫ f d(λ μ) < ∞  ↔  ∫ f dμ < ∞     for 0 < λ < ∞.
  ```

- Therefore a homeomorphism whose pushforward measure is a positive finite constant multiple of the target measure preserves RLCT exactly.

Precise informal lemma:

```lean
rlctAt_comp_homeomorph_const_smul_measure

Given:
  e : V ≃ₜ V'
  MeasurableEmbedding e
  μ, ν measures
  Measure.map e μ = a • ν
  0 < a, a ≠ ∞
Then:
  rlctAt μ (fun x ↦ F (e x)) x0
    =
  rlctAt ν F (e x0)
```

Specialized to volume on `ℝ^N`, for `σ_s x = s • x`, Mathlib gives

```lean
Measure.map σ_s volume = ENNReal.ofReal |s^N|⁻¹ • volume
```

for `s ≠ 0`, and this scalar is finite positive.

**Cleanest Route**

Use R3 to prove scaling invariance, then use the local witness argument from R1.

Minimal new lemma:

```lean
rlctAt_comp_homeomorph_const_smul_measure
```

This is not new analytic input. It is measure theory plus the RLCT definition.

Then derive:

```lean
rlctAt_homogeneous_smul_eq
  (hs : 0 < s)
  (hhom : ∀ x, K (s • x) = s^d * K x)
  :
  rlctAt K (s • w) = rlctAt K w
```

using the constant-measure homeomorphism lemma and `rlct_unit_invariant` with the constant unit `s^d`.

Everything after that is elementary topology/locality:

```text
If c is admissible at 0 with witness U ∋ 0,
choose 0 < s ≤ 1 with s • w ∈ U.
Then c is admissible at s • w.
By scaling invariance, c ≤ rlctAt K w.
Take sSup over c.
```

**Limit Issue**

If you literally try to prove the result by taking `s → 0` in the numeric equality

```lean
rlctAt K (s • w) = rlctAt K w,
```

then yes, you are asking for lower semicontinuity of `p ↦ rlctAt K p` at `0`.

That is a known hard analytic/semi-continuity type statement for log-canonical thresholds/RLCTs, and it is not something to expect from basic Mathlib measure theory. It may require serious analytic or resolution machinery.

But for this homogeneous inequality, it is completely sidestepped. No RLCT lower semicontinuity is needed.