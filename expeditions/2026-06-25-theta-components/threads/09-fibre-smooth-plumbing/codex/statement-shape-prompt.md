<task>
Lean 4 + Mathlib v4.29. I am building a REUSABLE conditional building block:
"a presentation of a k-algebra whose chosen square sub-Jacobian becomes a UNIT
is smooth (and standard-smooth of the right relative dimension)".

Mathlib API I have verified in situ (Mathlib/RingTheory/Extension/Presentation/Submersive.lean
and Mathlib/RingTheory/Smooth/StandardSmooth.lean + StandardSmoothCotangent.lean):

- `structure Algebra.PreSubmersivePresentation R S ι σ extends Presentation R S ι σ` where
  ι = generators/variables, σ = relations, plus `map : σ → ι` injective and `map_inj`.
- `Presentation.dimension P = Nat.card ι - Nat.card σ`.
- `PreSubmersivePresentation.jacobiMatrix : Matrix σ σ P.Ring`, entry (i,j) = pderiv (map i) (relation j);
  `jacobian : S = algebraMap P.Ring S jacobiMatrix.det`.
- `structure SubmersivePresentation R S ι σ extends PreSubmersivePresentation` with the SINGLE field
  `jacobian_isUnit : IsUnit toPreSubmersivePresentation.jacobian`. (No Reduced/Flat/Noetherian/IsDomain.)
- Constructor `PreSubmersivePresentation.naive {v : ι → MvPolynomial σ R} (a : ι → σ) (ha : Injective a)`
  builds a PreSubmersivePresentation of `MvPolynomial σ R ⧸ (Ideal.span (Set.range v))` indexed
  `PreSubmersivePresentation R (MvPolynomial σ R ⧸ span(range v)) σ ι`.  NOTE the SWAP: in `naive`'s
  output the GENERATORS slot is `σ` (the MvPolynomial variable index) and the RELATIONS slot is `ι`
  (the relation index). `jacobiMatrix_naive a ha i j = (v j).pderiv (a i)`, a Matrix ι ι.
- `SubmersivePresentation.isStandardSmoothOfRelativeDimension P (hP : P.dimension = n)
  : IsStandardSmoothOfRelativeDimension n R S` (needs Finite on both index types).
- `IsStandardSmoothOfRelativeDimension.isStandardSmooth`, and `instance [IsStandardSmooth R S] : Smooth R S`
  (side-condition-free).

DOWNSTREAM REUSE (this is the crux of the design): the lemma will be applied TWICE by a fibre-smoothness
atlas. The chart algebra in both cases is a LOCALIZATION S_g of a finite-type k-algebra. The minor-unit
hypothesis is "the chosen c×c sub-Jacobian determinant is a unit in S_g". I will NOT discharge that
hypothesis here (separate tide). I want the building block stated at the level of generality that lets a
caller plug in: n variables, c relations v : Fin c → MvPolynomial (Fin n) k, an injective column-selector
a : Fin c → Fin n, and the unit hypothesis, and get out `Smooth k (chart)` and
`IsStandardSmoothOfRelativeDimension (n - c) k (chart)`.

The open design question: should the building block be stated
 (A) CONCRETELY on `S := MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range v)` (i.e. exactly the `naive`
     quotient), letting callers transport to their S_g via an `AlgEquiv` + `IsStandardSmoothOfRelativeDimension.of_algEquiv`
     / a Smooth-transport-along-AlgEquiv lemma; OR
 (B) ABSTRACTLY on an arbitrary k-algebra `S` plus a hypothesis packaging it as such a quotient
     (e.g. take `S` with `[Algebra k S]` and a given `AlgEquiv S (MvPolynomial (Fin n) k ⧸ span(range v))`,
     or take a full `Algebra.Presentation k S (Fin n) (Fin c)` + `map` + unit hypothesis as the input).
</task>

<output_contract>
1. Recommend (A) or (B) (or a precise hybrid) for MAXIMUM downstream reuse by a localization-chart atlas,
   in <=8 lines. State the single most important reason.
2. Give the exact Lean theorem SIGNATURE(S) you recommend landing (statement only, body sorry), using the
   real Mathlib names above. If a Smooth-transport-along-AlgEquiv lemma is needed for callers, name it
   (does Mathlib have `Algebra.Smooth.of_equiv` / `Smooth.of_algEquiv` at v4.29? if unsure, say so and give
   the via-IsStandardSmooth route).
3. Flag any indexing trap in the σ/ι swap of `naive` that would make `dimension = n - c` come out as
   `c - n` or otherwise wrong, and how to state the relative-dimension conclusion so it is `n - c`.
4. Anything that would make this SILENTLY VACUOUS or wrong (e.g. a Finite/Fintype/DecidableEq instance gap,
   a Nat-subtraction truncation issue when c > n, the unit hypothesis being about the wrong ring).
</output_contract>

<grounding_rules>
Distinguish what you KNOW about Mathlib v4.29 from what you INFER. If you are not sure a named lemma exists
at this pin, say "verify" rather than asserting it. Do not invent lemma names.
</grounding_rules>
