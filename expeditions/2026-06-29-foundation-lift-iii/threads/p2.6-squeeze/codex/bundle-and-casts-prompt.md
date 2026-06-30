<task>
You are a decorrelated FIDELITY reviewer for a Lean 4 + Mathlib theorem, the Phase-2 capstone of a
formalisation expedition. The theorem is an ABSTRACT orbit-dimension "squeeze" headline. I want your
independent read on TWO questions only:

(Q1) HYPOTHESIS-BUNDLE HONESTY (name = content). Does the theorem's name + statement faithfully
denote what is proved, with the FULL hypothesis bundle carried explicitly and NONE hidden? Concern:
is any listed hypothesis actually a *consequence* smuggled in as an input, or a *cited monument*
renamed? Is the conclusion a genuine object-equality `varietyDim Z = ↑(finrank k (range δ))` in `ℕ∞`
(NOT a codimension, NOT an rlct)?

(Q2) THE ≤/≥ COMPOSITION + THE ℕ↔ℕ∞ CASTS. Verify each step of the `le_antisymm` cites the right
lemma and that the `ℕ → ℕ∞` coercions (`exact_mod_cast`) are honest — no off-by-cast, no silent
coercion, no direction error.

=== THE HEADLINE (Squeeze.lean) ===

theorem varietyDim_eq_finrank_range_δ
    [CharZero k] [PerfectField k]
    (G : AffineGVarietyDeformation k) [Finite G.ρ]
    (δAdj : G.C1 →ₗ[k] G.C0)
    (L : (FractionRing G.R ⊗[k] G.C0) →ₗ[FractionRing G.R] KaehlerDifferential k (FractionRing G.R))
    (hMC : G.DifferentialFactors δAdj L)
    (hRank : finrank k (LinearMap.range δAdj) = finrank k (LinearMap.range G.δ))
    (hcrit : DiffIndepCriterion k G.R)
    {I : Ideal (MvPolynomial G.ρ k)}
    (H : G.InfinitesimalAction I)
    [FiniteDimensional k (H.basePtIdeal).Cotangent]
    [hI : I.IsPrime]
    [hm : (H.basePtIdeal).IsMaximal] [Algebra.IsSmoothAt k (H.basePtIdeal)]
    (hrat : Ideal.ResidueField (H.basePtIdeal) ≃ₐ[k] k)
    {Z : Set (G.ρ → k)}
    (hZ : MvPolynomial.vanishingIdeal k Z = I)
    (hIker : I = RingHom.ker G.toAffineGVariety.pullback.toRingHom) :
    varietyDim Z = (finrank k (LinearMap.range G.δ) : ℕ∞) := by
  haveI : Fintype G.ρ := Fintype.ofFinite _
  set m := H.basePtIdeal
  set r : ℕ := finrank k (LinearMap.range G.δ) with hr
  have hB3 : r ≤ finrank k (m.Cotangent) := H.finrank_range_δ_le_finrank_cotangent
  have hB4 : (finrank k (m.Cotangent) : ℕ∞) = varietyDim Z :=
    finrank_cotangent_eq_varietyDim I m hrat hZ
  have hge : (r : ℕ∞) ≤ varietyDim Z := by
    rw [← hB4]; exact_mod_cast hB3
  have hA41 : varietyDim Z
      = ((Algebra.trdeg k G.toAffineGVariety.pullback.range).toNat : ℕ∞) :=
    G.toAffineGVariety.varietyDim_eq_trdeg_of_eq_ker (hZ.trans hIker)
  have htrdeg : (Algebra.trdeg k G.toAffineGVariety.pullback.range).toNat
      ≤ genericDifferentialRank k G.R G.fρ := by
    rw [G.toAffineGVariety.range_pullback]
    exact trdeg_adjoin_le_genericDifferentialRank k G.R G.fρ hcrit
  have hB1 : genericDifferentialRank k G.R G.fρ ≤ r :=
    G.genericRankBound δAdj L hMC hRank
  have hle : varietyDim Z ≤ (r : ℕ∞) := by
    rw [hA41]; exact_mod_cast htrdeg.trans hB1
  exact le_antisymm hle hge

=== THE FOUR BRICK SIGNATURES (each independently landed + reviewed; you may treat their CONCLUSIONS
as given, but check the theorem USES them correctly) ===

-- A4.1 anchor (returns an ℕ∞ object-equality):
AffineGVariety.varietyDim_eq_trdeg_of_eq_ker [Finite G.ρ] {Z : Set (G.ρ → k)}
  (hZ : vanishingIdeal k Z = RingHom.ker G.pullback.toRingHom) :
  varietyDim Z = ((Algebra.trdeg k G.pullback.range).toNat : ℕ∞)

-- Phase-1 trdeg bound (ℕ ≤ ℕ):
trdeg_adjoin_le_genericDifferentialRank (k B) {ι} [Field k][CommRing B][IsDomain B][Algebra k B][Fintype ι]
  (f : ι → B) (hcrit : DiffIndepCriterion k B) :
  (Algebra.trdeg k (Algebra.adjoin k (Set.range f))).toNat ≤ genericDifferentialRank k B f
-- and  range_pullback : G.pullback.range = Algebra.adjoin k (Set.range G.fρ)

-- B1 (ℕ ≤ ℕ):
AffineGVarietyDeformation.genericRankBound [Fintype G.ρ] (δAdj) (L) (hMC : DifferentialFactors δAdj L)
  (hRank : finrank k (range δAdj) = finrank k (range G.δ)) :
  genericDifferentialRank k G.R G.fρ ≤ finrank k (LinearMap.range G.δ)

-- B3 (ℕ ≤ ℕ):
InfinitesimalAction.finrank_range_δ_le_finrank_cotangent [FiniteDimensional k (H.basePtIdeal).Cotangent] :
  finrank k (LinearMap.range G.δ) ≤ finrank k ((H.basePtIdeal).Cotangent)

-- B4 (ℕ∞ object-equality):
finrank_cotangent_eq_varietyDim [PerfectField k] {σ} [Finite σ] (I : Ideal (MvPolynomial σ k)) [I.IsPrime]
  (m : Ideal (MvPolynomial σ k ⧸ I)) [m.IsMaximal] [Algebra.IsSmoothAt k m]
  (hrat : Ideal.ResidueField m ≃ₐ[k] k) {Z} (hZ : vanishingIdeal k Z = I) :
  (finrank k (m.Cotangent) : ℕ∞) = varietyDim Z

KEY FACTS you can rely on:
- `varietyDim Z : ℕ∞`. `finrank k _ : ℕ`. `Algebra.trdeg k _ : ℕ∞`, `.toNat : ℕ`.
- `genericDifferentialRank k B f : ℕ`.
- The DLN instance discharges this bundle; e.g. δAdj := a trace-transpose with a proven rank-tie,
  hcrit holds in char 0, H is a dual-number infinitesimal-action structure, the smooth k-rational
  point comes from a generic-smoothness density argument (NOT assumed-existence — the point IS smooth).
- No Aoyagi/RLCT axiom enters; #print axioms = [propext, Classical.choice, Quot.sound] (verified).
</task>

<output_contract>
Two sections, terse.

(Q1) HYPOTHESIS-BUNDLE HONESTY — verdict CLEAN or CONCERN. For each of these, one line: is it a
genuine input or a smuggled consequence/renamed monument? (a) hMC+hRank+δAdj+L; (b) hcrit+[CharZero];
(c) H+[FiniteDimensional Cotangent]; (d) [IsSmoothAt]+hrat+[PerfectField]+[IsMaximal]; (e) hZ+hIker.
Then: is the conclusion a true object-equality in ℕ∞ (not codim/rlct)? Flag any hypothesis that is
unused, redundant, or that could be derived from the others (which would mean the "name=content" claim
slightly overstates the minimal bundle — note it but don't treat as a break).

(Q2) COMPOSITION + CASTS — verdict SOUND or BROKEN-AT-STEP-N. Walk: hge (the ≥ side: rw ←hB4 then
exact_mod_cast hB3), and hle (the ≤ side: rw hA41 then exact_mod_cast (htrdeg.trans hB1)). Confirm
the trans chains type-check (trdeg.toNat ≤ genericDiffRank ≤ r are all ℕ), confirm the casts go the
right direction (ℕ→ℕ∞ is monotone/injective), and confirm le_antisymm hle hge closes
`varietyDim Z = ↑r`. Name the single place most likely to hide an error if any.
</output_contract>

<grounding_rules>
Distinguish what you can VERIFY from the given signatures (fact) vs what you INFER about the bricks'
internals (inference) — label inferences. You do NOT have the brick proof bodies, only their stated
conclusions; do not claim a brick is wrong, only whether the HEADLINE composes them soundly. If a step
is fine, say so plainly; do not invent problems.
</grounding_rules>
