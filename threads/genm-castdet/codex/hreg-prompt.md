<task>
Lean 4 + Mathlib v4.29. I must prove an absolute-determinant = 1 fact for a self-composite of two
LinearEquivs over opaque (variable) finite dimensions. I want the CLEANEST proof strategy that avoids
a 30+-line funext coordinate chase if possible.

CONTEXT — the target theorem (`hreg`):
  theorem eihd_hreg (ha : StructAdm M (tach M)) :
    |LinearMap.det (((eihdOut ha).symm : StairProd (eihdV M) 2 →ₗ[ℝ] (Fin (flatDim M) → ℝ))
        ∘ₗ ((eIn ha) : (Fin (flatDim M) → ℝ) →ₗ[ℝ] StairProd (eihdV M) 2))| = 1

Here:
- `flatDim M : ℕ` is OPAQUE (a sum of products of variable matrix widths; not a literal).
- `StairProd (eihdV M) 2 = eihdV M 0 × (eihdV M 1 × PUnit)` where
    eihdV M 0 = SchurInc (schurT1 M) (schurR1 M) (schurC1 M)   -- a 4-tuple of ℝ-matrices
    eihdV M 1 = Matrix (Fin (schurC1 M)) (Fin (Wext M 2)) ℝ × Matrix (Fin (schurT1 M)) (Fin (Wext M 2)) ℝ
  None of SchurInc / StairProd / the matrix-product spaces has a MeasureSpace instance.
- `eIn ha : (Fin (flatDim M) → ℝ) ≃ₗ[ℝ] StairProd (eihdV M) 2` and
  `eihdOut ha : (Fin (flatDim M) → ℝ) ≃ₗ[ℝ] StairProd (eihdV M) 2` are both built ENTIRELY from
  coordinate-bijection LinearEquivs on `→ℝ` spaces:
    LinearEquiv.funCongrLeft (precomposition by an Equiv on the index type),
    LinearEquiv.piCurry, LinearEquiv.piFinTwo,
    LinearEquiv.sumArrowLequivProdArrow, LinearEquiv.curry, Matrix.ofLinearEquiv,
    Matrix.reindexLinearEquiv, LinearEquiv.prodComm, LinearEquiv.prodCongr,
    LinearEquiv.prodUnique, plus two hand-rolled `LinearEquiv`s (roleReorderLE, eInRearrange)
    that just shuffle the components of a nested product of `→ℝ`/matrix spaces.
  EVERY constituent sends a standard basis vector to a standard basis vector (no scaling): the maps are
  pure coordinate permutations / reshapes. So the composite `(eihdOut ha).symm ∘ₗ (eIn ha)` is a
  coordinate permutation of `(Fin (flatDim M) → ℝ)`, hence |det| = 1.

BANKED helper available:
  hreg_of_measurePreserving_comp (V) (eIn eOut : (Fin N → ℝ) ≃ₗ StairProd V n)
    (hMP : MeasurePreserving ((eOut.symm ∘ₗ eIn) : (Fin N → ℝ) → (Fin N → ℝ)) volume volume)
    : |det (eOut.symm ∘ₗ eIn)| = 1
  i.e. it suffices to show the COMPOSITE (a self-map of the flat ℝ^N space, which DOES have volume) is
  measure-preserving. The intermediate StairProd never needs a measure.

WHAT I ALREADY TRIED / KNOW:
- The naive route "chain MeasurePreserving through each constituent" is BLOCKED: StairProd / SchurInc /
  the matrix-pair spaces have no MeasureSpace, so I cannot speak of `MeasurePreserving (eIn ha)`.
- The fixed-dimension precedent (a (3,3,3,3) case) enumerates an explicit `Fin 27 ≃ FlatIdx` permutation
  by hand and uses `measurePreserving_paramsPack_of_flatIdxEquiv`. That does NOT generalize to opaque
  widths — I cannot enumerate.

OPEN QUESTION: what is the cleanest way to discharge this for OPAQUE widths? Candidate routes:
  (A) Prove `(eihdOut ha).symm ∘ₗ (eIn ha) = LinearEquiv.funCongrLeft ℝ ℝ σ` for an explicit
      `σ : Fin (flatDim M) ≃ Fin (flatDim M)`, then |det (funCongrLeft σ)| = 1. PROBLEM: extracting σ
      explicitly is a ~10-reshape funext chase, and the intermediate index types are Sigma/Sum/Fin-product
      over opaque widths — σ would be a horrendous nested Equiv. How bad is this really? Is there a way
      to get the funCongrLeft form WITHOUT naming σ (e.g. by a structural lemma that the composite of these
      specific equivs is some funCongrLeft)?
  (B) Show the composite map is measure-preserving DIRECTLY (feed hreg_of_measurePreserving_comp) by
      proving it equals `funLeft ℝ ℝ σ` for SOME equiv σ (existence, not explicit) and using
      `volume_measurePreserving_piCongrLeft`/`MeasurePreserving` of a coordinate permutation. Does Mathlib
      have "a LinearEquiv that permutes a basis is measure-preserving / has |det|=1" as a clean lemma?
  (C) A determinant-multiplicativity route: |det(eOut.symm ∘ eIn)| = |det(eOut.symm)|·|det(eIn)|? NO — det
      is only defined for endomorphisms; eIn/eOut are between DIFFERENT spaces. But is there a
      `LinearEquiv.det`-style trick: pick a basis on StairProd, both eIn and eOut map the flat std basis to
      that same basis-up-to-permutation, so the change-of-basis matrices are permutation matrices and the
      composite's matrix is a product of two permutation matrices? Concretely: is there a Mathlib lemma
      `|det e| = 1` when a LinearEquiv `e : M ≃ₗ M'` sends a basis `b` of M to a permutation/reindex of a
      basis `b'` of M'? (Something like det via `LinearMap.toMatrix b' b e` being a permutation matrix.)
  (D) Anything cleaner I'm missing — e.g. proving each constituent has "abs det 1 relative to chosen
      bases" and composing those, where the abs-det-relative-to-bases of a basis-permuting equiv is
      provably 1 by a single reusable lemma.

I want a strategy where the OPAQUE-width casework is bounded (ideally one reusable lemma applied to each
of ~10 constituents), NOT a giant explicit σ.
</task>

<output_contract>
1. RANK routes A/B/C/D (and any you add) by total Lean effort for OPAQUE widths. State the single best.
2. For the best route: the exact Mathlib v4.29 lemma names it rests on (det / measure-preserving /
   permutation-matrix / change-of-basis), and whether each is confirmed to exist in v4.29 or is a guess.
3. The KEY reusable lemma I should prove once (statement in Lean), and how each of the ~10 constituents
   discharges it. If it's "each constituent is measure-preserving", say precisely which Mathlib MP lemma
   covers funCongrLeft, sumArrowLequivProdArrow, curry, ofLinearEquiv, reindexLinearEquiv, prodComm,
   prodCongr, prodUnique — and which have NO MP lemma (the gap I'd have to fill).
4. A blunt verdict: is this BOUNDED (~80-150 lines, one reusable lemma + 10 applications) or a WALL
   (giant explicit σ unavoidable)? If a wall, say which specific constituent forces it.
</output_contract>

<grounding_rules>
- Mark each lemma name as CONFIRMED (you are sure it is in Mathlib v4.29 with that signature) or GUESS.
- Distinguish "this lemma exists" from "this lemma's hypotheses are dischargeable here".
- If a route needs a MeasureSpace on an intermediate space, flag it as BLOCKED (I cannot add one cheaply
  to SchurInc / StairProd).
</grounding_rules>
