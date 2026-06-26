# Statement card — minor-unit ⟹ smooth chart (conditional plumbing, rungs S2+S3)

> **Claim.** Let `k` be a field, `v : Fin c → MvPolynomial (Fin n) k` a finite relation family, and
> `a : Fin c → Fin n` an injective column-selector. If the `c × c` sub-Jacobian determinant
> `det (i j ↦ pderiv (a i) (v j))`, viewed in the chart algebra
> `S = MvPolynomial (Fin n) k ⧸ span(range v)`, is a **unit** in `S`, then `S` is `Smooth k`, and
> sharper, `IsStandardSmoothOfRelativeDimension (n − c) k S`. The conclusions transport along any
> `k`-algebra iso `e : S ≃ₐ[k] S'` (so the chart need not be `S` on the nose).

- **Lean (headlines):**
  - `DLNFibre.Core.isSmooth_chart_of_isUnit_subJacobian`
  - `DLNFibre.Core.isStandardSmoothOfRelativeDimension_chart_of_isUnit_subJacobian`
  - `DLNFibre.Core.isSmooth_of_algEquiv_chart_of_isUnit_subJacobian` (transport wrapper)
  - `DLNFibre.Core.isStandardSmoothOfRelativeDimension_of_algEquiv_chart_of_isUnit_subJacobian`
  - supporting: `chartPreSubmersive`, `subJacobian`, `subJacobian_eq`, `chartSubmersive`
  - (`lean/DLNFibre/Core/FibreSmoothPlumbing.lean` @ `d46e667b`)

- **Gloss.** `ChartAlg v := MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range v)`. `subJacobian v a ha`
  is the `c × c` minor determinant `det (fun i j ↦ pderiv (a i) (v j))` pushed into `ChartAlg v` (the
  closed form is `subJacobian_eq`: it is `Ideal.Quotient.mk … (Matrix.det …)`). The headline
  `isSmooth_chart_of_isUnit_subJacobian` says: given `Function.Injective a` and
  `IsUnit (subJacobian v a ha)`, `Smooth k (ChartAlg v)` holds. The `…StandardSmoothOfRelativeDimension…`
  headline upgrades the conclusion to relative dimension `n − c`. The two `…of_algEquiv…` wrappers take
  an extra `e : ChartAlg v ≃ₐ[k] S` and the unit hypothesis stated in `S` (`IsUnit (e (subJacobian …))`)
  and conclude `Smooth k S` / `IsStandardSmoothOfRelativeDimension (n − c) k S`.

- **Proved.** The full chain, unconditionally: the minor-unit hypothesis is exactly the
  `jacobian_isUnit` field of `Algebra.SubmersivePresentation` built by `PreSubmersivePresentation.naive`;
  `SubmersivePresentation.isStandardSmoothOfRelativeDimension` (with `dimension = n − c`) and
  `.isStandardSmooth` then `instance [IsStandardSmooth] : Smooth` give the conclusions. Transport via
  `Algebra.Smooth.of_equiv` and `IsStandardSmoothOfRelativeDimension.of_algEquiv`.

- **Assumed (clean hypotheses of the lemma, not discharged here).**
  - `IsUnit (subJacobian v a ha)` — the minor-unit hypothesis. This is the deliberate clean input;
    discharging it (the **rank = C+δ** obligation) is the NEXT tide (task #108).
  - `Function.Injective a` — needed for a submersive presentation (≤ relations than variables);
    forces `c ≤ n` so `n − c` is the honest dimension (not truncated). Vacuous if `c > n`, correctly.

- **Cited.** none. The route is **reducedness-free** — `SubmersivePresentation` carries no
  `Reduced`/`Flat`/`Noetherian`/`IsDomain` field, and `IsStandardSmooth ⟹ Smooth` is side-condition-free.
  Confirmed by reading `Mathlib/RingTheory/Extension/Presentation/Submersive.lean` and
  `Mathlib/RingTheory/Smooth/StandardSmoothCotangent.lean` in situ.

- **Deferred.** The discharge of `IsUnit (subJacobian v a ha)` for the actual DLN fibre charts (the
  rank=C+δ value left as a hole by `FibreJacobian`'s "H3b"). NOT in scope of this card.

- **Non-vacuity.** Witnessed in-file by an `example`: `n=1, c=1, v = (X 0), a = 0` gives
  `subJacobian = pderiv x x = 1`, a unit; chart `≅ k`, relative dimension `1 − 1 = 0`.

- **Axioms.** All six results: `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.

- **Status.** sorry-free (awaiting reviewer fidelity check).
