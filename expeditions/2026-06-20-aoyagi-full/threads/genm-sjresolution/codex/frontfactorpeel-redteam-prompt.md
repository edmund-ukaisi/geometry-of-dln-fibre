# Red-team a Lean 4 / Mathlib inequality statement — is it TRUE, or is there a counterexample?

You are an adversarial reviewer. I have a Lean statement (currently a `sorry`) and I want to know
whether it is actually PROVABLE, or whether it is FALSE (has a counterexample). Do not assume it is
true. Hunt for a counterexample first.

## Definitions (all real-valued; `^` on reals is `Real.rpow`, so `(0:ℝ)^y = 0` for `y ≠ 0`, `0^0 = 1`)

- `frobSq (X : Fin m → Fin n → ℝ) : ℝ := ∑_i ∑_j (X i j)^2`   (squared Frobenius norm)
- `rmatMul (A : Fin p → Fin n → ℝ) (Q : Fin n → Fin q → ℝ) : Fin p → Fin q → ℝ`
  `:= fun i j => ∑_k A i k * Q k j`   (ordinary matrix product)
- `matBox p n (1:ℝ) : Set (Fin p → Fin n → ℝ) := { X | ∀ i k, X i k ∈ [-1, 1] }`
- `frobSqTopRows (t : ℕ) (P : Fin m → Fin n → ℝ) : ℝ := ∑_i ∑_j (if (i:ℕ) < t then (P i j)^2 else 0)`
  (squared Frobenius norm of the TOP `t` ROWS of P — rows with index `< t`)
- `peelExp M t := (M 0 - t) * (M 1 - t)`   (natural-number subtraction, then cast to ℝ)
- `minAdm M` : a combinatorial nonneg integer; for a width vector `M = (M0, M1, M2)` it is
  `min over t in {0..min(M0,M1)} of [ (M0−t)(M1−t) + minAdm(t, M2) ]`, with `minAdm(a,b) = a*b`.
  Example: `minAdm(1,2,1) = min( (1)(2)+minAdm(0,1), (0)(1)+minAdm(1,1) ) = min(2+0, 0+1) = 1`.

## The statement under review (`M : Fin 3 → ℕ`, i.e. widths `(M0, M1, M2)`)

For all `c' : ℝ` with `0 ≤ c'` and `c' < minAdm M / 2`:

  ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (q : ℕ) (Q : Fin (M 1) → Fin q → ℝ),
    ( ∫⁻ A0 in matBox (M 0) (M 1) 1, ENNReal.ofReal ( (frobSq (rmatMul A0 Q)) ^ (-c') ) )
      ≤ ∑ t in Finset.range (min (M 0) (M 1) + 1),
          C * ENNReal.ofReal ( (frobSqTopRows t Q) ^ (-(c' - (peelExp M t)/2))
                               * (frobSq Q) ^ (-((peelExp M t)/2)) )

(The `∫⁻` is a Lebesgue integral over the box `[-1,1]^{M0×M1}` w.r.t. Lebesgue measure. Note the
constant `C` is chosen ONCE and must work for EVERY `q` and EVERY `Q` — it is a single uniform
constant, quantified OUTSIDE the `∀ Q`. Note also the whole RHS is `ENNReal.ofReal` of a REAL number
computed with `Real.rpow`.)

## Your task

1. Is this TRUE (a single finite `C` exists making the inequality hold for all `Q`), or FALSE?
2. Consider degenerate `Q` — in particular `Q` whose TOP rows are zero but lower rows nonzero.
   What is `frobSqTopRows t Q` then, and what does `(that)^{negative}` evaluate to under `Real.rpow`?
   Does the RHS collapse? Meanwhile is the LHS integral positive?
3. Give a concrete `(M, c', q, Q)` witness if you find the statement false, with the LHS and RHS
   both evaluated numerically. Try `M = (1,2,1)`.
4. If false, is it a `Real.rpow` `0^{negative}=0` (should-be-+∞) artifact, or a deeper error? What
   minimal change to the STATEMENT would make it true (e.g. restrict `Q`, use `ENNReal.rpow` so the
   singular factor is `+∞`, hold a.e. rather than pointwise, etc.)?

Be terse and concrete. Numbers, not vibes.
