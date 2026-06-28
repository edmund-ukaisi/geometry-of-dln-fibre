<task>
Lean 4 + Mathlib v4.29. I am relaxing a vestigial `[IsAlgClosed k]` typeclass to `[PerfectField k]`
(+ `[Infinite k]`) across a 6-file dependency chain, so a downstream squeeze theorem green-builds
over k=ℝ. ℝ is `CharZero ⟹ PerfectField` (Mathlib instance `PerfectField.ofCharZero`) and `Infinite`.

I have already traced where alg-closedness is GENUINELY consumed. There are exactly TWO load-bearing
entry points, both relaxable to PerfectField:
  (A) `Algebra.FormallySmooth.of_perfectField [PerfectField K] [EssFiniteType K L] : FormallySmooth K L`
      — used in `SmoothPointRegular.finrank_cotangentSpace_le_of_isSmoothAt` to make the residue field
      formally smooth over k (line `haveI : Algebra.FormallySmooth k (ResidueField R) := inferInstance`).
  (B) `Scheme.Hom.dense_smoothLocus_of_perfectField [PerfectField K] [IsReduced X] [LocallyOfFinitePresentation f]`
      — used in `OrbitSmooth.exists_orbitPointIdeal_isSmoothAt`.
Everything else that is `[IsAlgClosed k]`-declared is vestigial (declared in `variable` blocks, used only
to transitively obtain the above, or to obtain orbit-ring primeness which actually only needs `[Infinite k]`
since its proof is `RingHom.ker_isPrime` of a kernel into a domain).

The dependency chain (leaf → root), with the typeclass each lemma's PROOF actually needs:
  - `OrbitVariety.isPrime_vanishingIdeal_orbitSet` : proof reads `vanishingIdeal_range_orbitMap_eq_ker [Infinite k]`
    + `RingHom.ker_isPrime`. → needs `[Infinite k]` only. (declared `[IsAlgClosed k]`)
  - `OrbitSmooth.orbitRing_isDomain` (instance) : `Ideal.Quotient.isDomain` of the prime orbitIdeal.
    → needs `[Infinite k]` (via primeness). (declared `[IsAlgClosed k]`)
  - `OrbitSmooth.dense_orbitSpecSet` : uses `IsReduced (orbitRing M)` (from the domain) + a generic
    zeroLocus/closure identity. → needs `[Infinite k]`. (declared `[IsAlgClosed k]`)
  - `OrbitSmooth` SpecModel `section` with `variable [IsAlgClosed k]`: contains
    `exists_orbitPointIdeal_isSmoothAt` (uses (B) + dense_orbitSpecSet + IsReduced orbitScheme),
    `isSmoothAt_normalFormIdeal`, `residueFieldNormalFormEquiv` (uses orbitEval surjectivity, no alg-closed).
    → needs `[PerfectField k] [Infinite k]`.
  - `SmoothPointRegular.{finrank_cotangentSpace_le_of_isSmoothAt, smooth_point_isRegularLocalRing,
    finrank_cotangentSpace_eq_of_isSmoothAt}` (declared `[IsAlgClosed k]`): the docstring at line 21
    says "`[IsAlgClosed k]` is used only to get `PerfectField k`". The only consumer is (A).
    → needs `[PerfectField k]`. NB this file's `variable` block is `{k : Type*} [Field k] {A ...}`,
    `[IsAlgClosed k]` is per-theorem, not in the variable block.
  - `OrbitTangentCotangent.{residueFieldAtPrimeNormalFormEquiv, finiteDimensional_cotangent_normalFormIdeal,
    finrank_range_deformationδ_le_finrank_cotangent, exists_ringKrullDim_orbitRing_eq,
    finrank_cotangent_eq_varietyDim, finrank_range_deformationδ_le_varietyDim}` (declared `[IsAlgClosed k]`)
    → inherit from above; need `[PerfectField k] [Infinite k]`.

The headline `finrank_range_deformationδ_le_varietyDim` must then green-build with k:=ℝ.

QUESTIONS (answer each, terse):
Q1. Is there any RISK that relaxing `[IsAlgClosed k] → [PerfectField k] [Infinite k]` breaks an
    INSTANCE-RESOLUTION that currently silently uses an `[IsAlgClosed k]`-only instance (e.g. a Jacobson,
    IsReduced, or k-points=closed-points instance) that does NOT have a PerfectField analogue? In particular:
    is `IsReduced (orbitScheme M)` resolved via `IsDomain (orbitRing M)`, and does anything need
    `IsAlgClosed` to make `orbitScheme` reduced beyond the domain instance?
Q2. `dense_smoothLocus_of_perfectField` requires `[IsReduced X]` where X = orbitScheme. With the domain
    instance relaxed to `[Infinite k]`, does `IsReduced (Spec (.of (orbitRing M)))` resolve from
    `IsDomain (orbitRing M)` automatically in Mathlib v4.29? (i.e. is there an instance chain
    IsDomain → IsReduced ring → IsReduced (Spec _) scheme?)
Q3. ORDER: should I relax bottom-up (OrbitVariety first, then OrbitSmooth, SmoothPointRegular,
    OrbitTangentCotangent) and green-build each? Any gotcha with `variable [IsAlgClosed k]` section blocks
    vs per-theorem hypotheses (e.g. a hidden `omit` or a downstream consumer outside this chain that still
    passes `[IsAlgClosed k]` and would now get a redundant-but-harmless instance, vs one that BREAKS)?
Q4. L7 base-change: `deformationδ M Nt : cochain0 →ₗ[k] cochain1`,
    `deformationδ M M φ i = φ(i.succ)·M_i − M_i·φ(i.castSucc)` (a `LinearMap`, NOT a bare Matrix). I want
    `finrank_ℝ(range (deformationδ_ℝ M)) = finrank_K(range (deformationδ_K (M.map ι)))` where M = realizerD
    has INTEGER (0/1) entries and ι : ℝ →+* K. cochain0/cochain1 are `∀ v, Matrix _ _ k` (Pi of matrices).
    Two candidate routes:
      (R1) `LinearMap.toMatrix'` (after Pi≃Fin→k flattening) to an integer structure matrix, then
           `Matrix.rank` field-independence over a ℤ-cast (the standard "largest nonvanishing minor" /
           `Matrix.rank_eq` argument).
      (R2) a direct base-change-of-range-finrank argument: deformationδ is, after the flattening iso, the
           same ℤ-matrix's mulVecLin; rank of A.map(ι) = rank A for an injective ring hom ι in char 0.
    Which route is cleaner at v4.29, and is L7 a PACKAGING exercise (no new math) or a real gap? Is there a
    Mathlib lemma `Matrix.rank_map_eq` / `Matrix.rank` invariance under an injective ring hom, or do I need
    to route through `Matrix.rank` = number of pivots / the `LinearIndependent` base-change?
</task>

<output_contract>
  Five short sections Q1..Q4 (Q4 covers L7). For each: a direct verdict (YES/NO/route name), then ≤3
  sentences of reasoning. For Q4 name the specific Mathlib v4.29 lemma(s) you believe exist (flag if unsure).
  End with a one-line GO/NO-GO on the relaxation being purely mechanical (no new math).
</output_contract>

<grounding_rules>
  Distinguish "I am confident this Mathlib lemma exists at v4.29" from "likely exists, verify the name".
  Do not invent lemma names; if unsure of an exact name, say so and give the search term.
</grounding_rules>
