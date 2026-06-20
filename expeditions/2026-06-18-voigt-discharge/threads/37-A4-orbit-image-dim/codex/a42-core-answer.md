**Q1**

Absent. I searched local Mathlib v4.29 for `KaehlerDifferential` with `AlgebraicIndependent`, `IsTranscendenceBasis`, `LinearIndependent`, `trdeg`, `rank/finrank Ω`, plus `separatingTranscendenceBasis` / `SeparablyGenerated`.

There is no direct lemma of the form:

```lean
AlgebraicIndependent k x →
LinearIndependent K (fun i => KaehlerDifferential.D k K (x i))
```

**Q2**

(a) Yes, the separating-basis existence theorem is:

```lean
exists_isTranscendenceBasis_and_isSeparable_of_perfectField
```

with shape:

```lean
[Field k] [Field K] [Algebra k K]
[PerfectField k] [Algebra.EssFiniteType k K] :
∃ s : Finset K,
  IsTranscendenceBasis k ((↑) : s → K) ∧
  Algebra.IsSeparable (IntermediateField.adjoin k (s : Set K)) K
```

For char zero use:

```lean
PerfectField.ofCharZero
```

(b) No packaged theorem says “Ω is free with basis `D` of a separating transcendence basis.” The pieces exist:

```lean
KaehlerDifferential.mvPolynomialBasis
AlgebraicIndependent.aevalEquivField
KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap
Algebra.FormallyEtale.of_isSeparable
```

but the basis theorem must be assembled.

(c) I did not find a field-extension theorem:

```lean
finrank K Ω[K⁄k] = (Algebra.trdeg k K).toNat
```

There are smooth/standard-smooth rank results, but not this packaged field/trdeg statement. Also, as you noted, that equality alone would not control the span of the specific `D f_i`.

**Q3**

`Algebra.IsSeparable E K` is algebraic-only at v4.29. The source docstring explicitly says it means every element has separable minimal polynomial and therefore implies algebraicity; the theorem names are:

```lean
IsSeparable.isIntegral
Algebra.IsSeparable.isIntegral
```

So for non-algebraic `K/E`, do not try to use `[Algebra.IsSeparable E K]`.

Also, `K/E` is not formally étale when it has transcendence degree > 0. The right condition for injectivity of base-change is formal smoothness, not formal étaleness:

```lean
[Algebra.FormallySmooth E K]
```

The helper proof is short from Jacobi-Zariski:

```lean
Algebra.H1Cotangent.exact_δ_mapBaseChange
```

because `[Algebra.FormallySmooth E K]` gives `Subsingleton (H1Cotangent E K)`. In words: exactness says `ker mapBaseChange = im δ`, and formal smoothness kills the source of `δ`.

How to get formal smoothness:

```lean
Algebra.FormallySmooth.of_perfectField
```

works from:

```lean
[PerfectField E] [Algebra.EssFiniteType E K]
```

For char zero, `E = k(g)` is char zero/perfect. If you want to avoid finite-type hypotheses, prove a helper “every char-zero field extension is formally smooth” using:

```lean
exists_isTranscendenceBasis
IsTranscendenceBasis.isAlgebraic_field
Algebra.IsAlgebraic.isSeparable_of_perfectField
Algebra.FormallySmooth.adjoin_of_algebraicIndependent
Algebra.FormallyEtale.of_isSeparable
Algebra.FormallySmooth.comp
```

**Q4**

Provable. Clean route:

1. Prove a reusable criterion:

```lean
lemma linearIndependent_D_of_algebraicIndependent_charZero
    [Field k] [Field K] [Algebra k K] [CharZero k]
    {η : Type*} {x : η → K}
    (hx : AlgebraicIndependent k x) :
    LinearIndependent K (fun i => KaehlerDifferential.D k K (x i))
```

2. Prove it via `MvPolynomial`: use `KaehlerDifferential.mvPolynomialBasis`; base-change the basis to `K`; map through `KaehlerDifferential.mapBaseChange`; identify images using:

```lean
KaehlerDifferential.mapBaseChange_tmul
KaehlerDifferential.map_D
KaehlerDifferential.mvPolynomialBasis_apply
```

3. The required injectivity of `mapBaseChange` comes from `[Algebra.FormallySmooth _ K]`, not `[Algebra.FormallyEtale _ K]`.

4. For the final lemma, let `A := Algebra.adjoin k (Set.range f)`. Use `exists_isTranscendenceBasis_subset` to choose a transcendence basis contained in the finite generating range. Its cardinal is `Algebra.trdeg k A` by:

```lean
IsTranscendenceBasis.cardinalMk_eq_trdeg
```

5. Map that basis into `K`; apply the criterion; since each basis element is one of the `f_i`, its differential lies in your span. Finish with:

```lean
LinearIndependent.fintype_card_le_finrank
```

on the span submodule.

If scoping is needed, scope only the criterion in step 1; everything after it is routine finite-basis/rank bookkeeping.

VERDICT: PROVABLE via formal-smooth `mapBaseChange` injectivity, not via `Algebra.IsSeparable E K` or formal étaleness.