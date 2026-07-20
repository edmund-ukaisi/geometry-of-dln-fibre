**(1) DEF VERDICT**

Pick **C-vanishing-ℝ**, preferably named as real-locus/Zariski codimension:

```lean
noncomputable def codimRealLocus (Z : Set (Tuple ℝ d)) : ℕ∞ :=
  Ideal.height (vanishingIdeal ℝ (canonicalCoord '' Z))
```

This is honest because it depends on the actual real fibre, not the residual ideal over ℝ and not the complex fibre. The `x² + y²` test kills **C-alg-ideal** for (a): `(x² + y²)` has height `1`, but its real zero set `{0}` has real codim `2`, so Watanabe/Aoyagi’s analytic RHS is real zero-locus codim, not generator-ideal height. For the DLN fibre, the intended equality with complex codim is true only because the top-dimensional complex components have rational/real smooth generic points, e.g. the `realizerD m`; that gives real top-dimensional pieces, hence real codim = complex codim. Ordinary radicality over ℝ or over `K` is not enough.

**(2) TRANSFER T**

Not provable in one tide from Mathlib v4.29 plus `realizerD` rationality alone.

Precise missing lemma:

```lean
-- schematic
theorem height_realVanishing_eq_complex_height_of_smooth_real_top_components
    (I : Ideal (MvPolynomial σ ℝ))
    (h :
      every top-dimensional irreducible component of V(I ⊗ℝ ℂ)
      is defined over ℝ and contains a smooth ℝ-point) :
    Ideal.height (vanishingIdeal ℝ (realZeroLocus I))
      =
    Ideal.height ((I.map (baseChange ℝ ℂ)).radical) := by
  -- missing real algebraic geometry
```

Mathematically standard content: a complex irreducible component defined over ℝ with a smooth real point has Zariski-dense real points, and its real locus has real dimension equal to the complex dimension. Lean gap: Mathlib lacks the real-density / semialgebraic-dimension / real-locus-dim = complex-dim bridge. So T should be the named hole this tide, not buried in the definition.

**(3) HONEST STATEMENTS**

```lean
noncomputable def codimRealLocus (Z : Set (Tuple ℝ d)) : ℕ∞ :=
  Ideal.height (vanishingIdeal ℝ (canonicalCoord '' Z))

abbrev realFibreCodim (d) (B : Matrix m n ℝ) : ℕ∞ :=
  codimRealLocus (d := d) (fibre ℝ d B)
```

Analytic citation attaches only to this:

```lean
axiom aoyagi_rlct_eq_half_realCodim
    (d) (B : Matrix m n ℝ) :
    rlct (squareFrobeniusDLNLoss d B)
      =
    halfCodim (realFibreCodim d B)
```

Visible transfer hole:

```lean
axiom codimReal_fibre_eq_complex_fibre
    (d) (B : Matrix m n ℝ) :
    realFibreCodim d B
      =
    codimRepCanonical
      (k := ℂ)
      (fibre ℂ d (B.map Complex.ofReal))
```

Then the final chain is honest:

```lean
calc
  rlct (squareFrobeniusDLNLoss d B)
      = halfCodim (realFibreCodim d B) :=
          aoyagi_rlct_eq_half_realCodim d B
  _   = halfCodim
          (codimRepCanonical
            (k := ℂ)
            (fibre ℂ d (B.map Complex.ofReal))) := by
          rw [codimReal_fibre_eq_complex_fibre]
  _   = halfCodim (complexCodimFormula d B.rank) := by
          -- existing proved geometry chain
          ...
```

Use `ℂ`, or require `[Algebra ℝ K]`; do not state this for arbitrary algebraically closed char-0 `K`, since such a `K` need not come with an ℝ-embedding.

**(4) TRAPS**

1. Do not define `codimReal` as `height (fibreGenIdeal ℝ B)`. That makes `x² + y²` wrong for the analytic theorem.

2. Do not define `codimReal` by complex codim and then prove T. That makes T vacuous and hides the real-to-complex passage.

3. A rational point is not enough by itself. The transfer needs a real point in the smooth/generic top-dimensional locus of each top component, or an equivalent density/dimension statement.