**Verdict: (iii)** for the bounded-effort question. T should stay an explicitly cited external fact at Mathlib v4.29.

The obstruction is not the catenary identity. That part is present: `codim + varietyDim = card` is field-generic in this repo via `codimRepCanonical_add_varietyDim_eq_card_of_nonempty` and the definitions of `codimRepCanonical` as vanishing-ideal height [OrbitCodim.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/theta-components/lean/DLNFibre/Core/OrbitCodim.lean:125). The missing step is the real/complex no-dimension-drop assertion:
```lean
ringKrullDim (MvPolynomial σ ℝ ⧸ I_real)
=
ringKrullDim (MvPolynomial σ K ⧸ I_complex)
```
for the actual vanishing ideals of real points and complex points.

Route assessment:

- **(a) dimension/trdeg route:** not bounded. It needs `ringKrullDim = trdeg` for finitely generated algebras, reduction over minimal primes, and scalar-extension invariance of that dimension. Mathlib v4.29 and the repo have trdeg and useful differential tools, but not this dimension theorem.

- **(b) chain-of-primes route:** not bounded. Contracting a top complex prime to `ℝ[x]` would need height preservation under field extension, plus a proof that the real vanishing ideal sees that top component. The rational realizer gives a real closed point, not a prime chain or full local dimension.

- **(c) direct vanishing-ideal base change:** blocked by a false general lemma. One can likely prove boundedly that the **generator ideal** of the K-fibre is the scalar extension of the real generator ideal, and over K the vanishing ideal is its radical. But over ℝ,
  ```lean
  vanishingIdeal ℝ (real points)
  ```
  is not generally the radical of the generator ideal. It is a real-radical/density issue. Mathlib has no real Nullstellensatz or vanishingIdeal base-change theorem here.

The `x² + y² = 0` example is exactly decisive: over ℝ the real locus is one point, so codim is `2`; over ℂ the variety has dimension `1`, so codim is `1`. Both complex top components contain the rational point `(0,0)`. Thus “a rational point on every top component” is not enough.

A sufficient hypothesis for T is: at least one top-dimensional complex component of the K-fibre has Zariski-dense real points. A standard stronger condition is a smooth real point of full local dimension on a top complex component. For equality component-by-component, require this for every top component.

For the DLN fibre, F3 alone does not establish that. You would need an additional theorem that the rational realizer lies in a smooth full-dimensional real chart, or that the relevant real `GL`-orbit/chart is Zariski dense in the top complex component. That is a substantial real-algebraic-geometry/base-change build, not a one-lemma Lean tide.