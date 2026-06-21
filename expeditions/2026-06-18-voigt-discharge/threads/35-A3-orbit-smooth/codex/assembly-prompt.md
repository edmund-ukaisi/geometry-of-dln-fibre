<task>
Lean 4 / Mathlib v4.29 (pinned). I am assembling the final step (L3.4) of a smoothness proof and
want the CLEANEST tactic-level route through the scheme↔ring affine bookkeeping, to avoid thrashing.

CONTEXT (all LANDED, sorry-free, in my file `DLNFibre/Core/OrbitSmooth.lean`):
- `A := orbitRing M = MvPolynomial (RepCoord d) k ⧸ I`, a finitely-presented k-algebra, a DOMAIN,
  Jacobson, reduced. `[Field k] [IsAlgClosed k]`.
- Spec model: `X := orbitScheme M := Spec (.of A)`, structure morphism
  `f := orbitSchemeHom M := Spec.map (CommRingCat.ofHom (algebraMap k A)) : X ⟶ Spec (.of k)`.
  Instances LANDED: `IsReduced X`, `JacobsonSpace X`, `LocallyOfFinitePresentation f`,
  `LocallyOfFiniteType f`.
- For each `P : BaseChangeGroup d` I have a maximal ideal `orbitPointIdeal M P : Ideal A`
  (`.IsMaximal`, `.IsPrime` instances), the point ideal of the orbit k-point.
- `dense_orbitSpecSet : Dense (orbitSpecSet M)` where
  `orbitSpecSet M := { p : PrimeSpectrum A | ∃ P, p.asIdeal = orbitPointIdeal M P }`.
- `isSmoothAt_orbitPointIdeal_iff M P : Algebra.IsSmoothAt k (orbitPointIdeal M P) ↔
   Algebra.IsSmoothAt k (normalFormIdeal M)` (G-action transport, LANDED).

GOAL: `Algebra.IsSmoothAt k (normalFormIdeal M)` (≡ `FormallySmooth k (Localization.AtPrime m_M)`),
where `normalFormIdeal M := orbitPointIdeal M 1`.

KEY MATHLIB BRICKS (verified present at v4.29):
- `Scheme.Hom.dense_smoothLocus_of_perfectField (f) [PerfectField K][IsReduced X][LocallyOfFinitePresentation f] : Dense (f.smoothLocus : Set X)`
- `Scheme.Hom.smoothLocus (f) [LocallyOfFinitePresentation f] : X.Opens` (carries IsOpen)
- `Scheme.Hom.mem_smoothLocus {x} : x ∈ f.smoothLocus ↔ (f.stalkMap x).hom.FormallySmooth`
- `AlgebraicGeometry.formallySmooth_stalkMap_iff {f}{x} (U : Y.Opens)(hU : IsAffineOpen U)(V : X.Opens)(hV : IsAffineOpen V)(hVU : V ≤ f ⁻¹ᵁ U)(hx : x ∈ V) : (f.stalkMap x).hom.FormallySmooth ↔ hV.primeIdealOf ⟨x,hx⟩ ∈ Algebra.smoothLocus Γ(Y,U) Γ(X,V)`
- `nonempty_inter_closedPoints [JacobsonSpace X] {Z} (hZne : Z.Nonempty)(hZlc : IsLocallyClosed Z) : (Z ∩ closedPoints X).Nonempty`
- `Dense.inter_open_nonempty : Dense s → ∀ U, IsOpen U → U.Nonempty → (U ∩ s).Nonempty`
- `Spec.topObj_forget : ToType (Spec.topObj R) = PrimeSpectrum R` (the carrier of Spec(.of A) is PrimeSpectrum A)
- `Algebra.IsSmoothAt R (p : Ideal A) [p.IsPrime] := FormallySmooth R (Localization.AtPrime p)` (abbrev)

THE THORNY PART: bridging the SCHEME-side `f.smoothLocus` (a set of points of `X = Spec(.of A)`,
which is homeomorphic / defeq-carrier to `PrimeSpectrum A`) to the RING-side
`Algebra.IsSmoothAt k (orbitPointIdeal M P)`. The affine case has `U = V = ⊤`, `Γ(Spec(.of k), ⊤) ≅ k`,
`Γ(Spec(.of A), ⊤) ≅ A`, and the point identification `(IsAffineOpen.primeIdealOf ⊤ x)`. I want the
cleanest way to get, for a point `x : X` corresponding to prime `p : PrimeSpectrum A`:
   `x ∈ f.smoothLocus ↔ Algebra.IsSmoothAt k p.asIdeal`.

QUESTIONS (answer concretely with Mathlib lemma names + the cleanest tactic skeleton):
1. What is the cleanest way to turn a point `p : PrimeSpectrum A` into the point `x : X` of
   `Spec(.of A)` and back (the carrier identification), and to discharge `formallySmooth_stalkMap_iff`
   with `U = ⊤`, `V = ⊤`? Specifically how to handle `hV.primeIdealOf ⟨x, _⟩` and identify
   `Γ(Spec(.of A), ⊤)` with `A` and `Algebra.smoothLocus Γ(Spec(.of k),⊤) Γ(Spec(.of A),⊤)` with
   `Algebra.smoothLocus k A`. Is there an existing simp-normal lemma (e.g. `IsAffineOpen.primeIdealOf_top`,
   `ΓSpecIso`, `Scheme.toSpecΓ`, `StructureSheaf.stalkIso`, or a packaged
   `Algebra.smoothLocus`↔`f.smoothLocus` affine dictionary) I should use rather than hand-rolling?
2. Is there a SHORTER route that AVOIDS the full set-bridge: e.g. take a closed smooth point via
   `nonempty_inter_closedPoints (f.smoothLocus ∩ orbitSpecSet-as-X-set)`, then I only need the bridge
   at THAT ONE point. Or even better — does Mathlib have a ring-side `Algebra.smoothLocus`
   density/openness lemma I can use directly on `PrimeSpectrum A` (so I never go to schemes), given a
   perfect field + reduced fin-presented domain? (I believe ring-side generic smoothness is ABSENT at
   v4.29 — confirm or point me to it.)
3. Concretely: write the cleanest ~15-30 line Lean skeleton from `dense_smoothLocus_of_perfectField` +
   `dense_orbitSpecSet` to "there exists P with Algebra.IsSmoothAt k (orbitPointIdeal M P)", then I
   finish via `isSmoothAt_orbitPointIdeal_iff`. Flag every step that is likely to need defeq-massaging
   (`set_option backward.isDefEq.respectTransparency false`, `Scheme.Hom.preimage` etc).
</task>

<output_contract>
Three numbered sections matching Q1-Q3. For Q3 give an actual Lean tactic skeleton (may contain
`sorry` placeholders for genuinely separate sub-lemmas, but name the Mathlib lemma each non-sorry step
uses). Mark any lemma you are INFERRING exists vs KNOW exists at v4.29. Be concrete about the
`formallySmooth_stalkMap_iff` argument plumbing for the affine `⊤`-cover case. Prefer the shortest
route even if it means proving a small helper.
</output_contract>

<grounding_rules>
Only cite Mathlib lemmas you are reasonably confident exist at the v4.29 pin; for any you are unsure
of, say "INFER — verify name". Do not invent API. If the clean route needs a lemma that likely does
NOT exist, say so and give the hand-rolled alternative.
</grounding_rules>
