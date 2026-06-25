<task>
Lean 4 + Mathlib v4.29. I need the cleanest realization of ONE lemma — the localized
coordinate-ideal height. I have the un-localized version landed; I need it over a localization
of the coefficient ring. This is the last heavy-infrastructure piece of a determinantal-base
elimination; I want to commit to the lowest-friction Lean route before grinding.

LANDED (sorry-free, in DLNFibre.Core):
- graphIdeal (c : ι → R) := Ideal.span (Set.range fun i ↦ X i − C (c i))  [MvPolynomial ι R]
- ker_aeval_eq_graphIdeal, graphIdeal_isPrime [IsDomain R], graphIdealQuotientEquiv
  (MvPolynomial ι R ⧸ graphIdeal c ≃ₐ[R] R)
- height_graphIdeal_eq (c : σ → MvPolynomial τ k) : (graphIdeal c).height = Nat.card σ
  [k field, σ τ finite]  -- via the field catenary
- height_coordIdeal_eq : (Ideal.span (Set.range fun i ↦ X i) : Ideal (MvPolynomial σ (MvPolynomial τ k))).height
  = Nat.card σ   -- the coord ideal = graphIdeal 0

TARGET: with `Sd := Localization.Away (f)` for `f : MvPolynomial τ k`, `f ≠ 0` (it's a generic det,
nonzero), prove
  height (Ideal.span (Set.range fun b ↦ (X b : MvPolynomial σ Sd))) = Nat.card σ.

Available Mathlib facts (grep-confirmed v4.29):
- `MvPolynomial.isLocalization : IsLocalization (M.map C) (MvPolynomial σ S)` when
  `S` is `IsLocalization M R` (here R = MvPolynomial τ k, M = powers f, S = Sd). So
  `MvPolynomial σ Sd` is the localization of `B := MvPolynomial σ (MvPolynomial τ k)` at
  `(powers f).map (C : MvPolynomial τ k →+* B)`.
- `IsLocalization.height_map_of_disjoint (M) (p : Ideal R) [p.IsPrime]
  (h : Disjoint (M : Set R) (p : Set R)) : (p.map (algebraMap R S)).height = p.height`
- `Ideal.disjoint_powers_iff_notMem (a) (hp.isRadical) : Disjoint (powers a) p ↔ a ∉ p`
- `Submonoid.map_powers f a : Submonoid.map f (powers a) = powers (f a)`
- `det_mvPolynomialX_ne_zero` (the generic det is ≠ 0).
- The coord ideal K₀ in B is `graphIdeal (0 : σ → MvPolynomial τ k)`, prime, and
  `C g ∈ K₀ ↔ g = 0` (since K₀ = ker (aeval 0), aeval 0 (C g) = g).

THE PLAN I have in mind (validate or improve):
  K (in MvPolynomial σ Sd) = K₀.map (algebraMap B (MvPolynomial σ Sd))  -- IS THIS TRUE / how to prove?
  height K = height K₀  via height_map_of_disjoint at the monoid (powers f).map C, with
    disjointness from C f ∉ K₀ (⟸ f ≠ 0)
  height K₀ = Nat.card σ  (height_coordIdeal_eq, landed)

THE QUESTIONS:
1. Is `Ideal.span (range (X : σ → MvPolynomial σ Sd)) = K₀.map (algebraMap B (MvPolynomial σ Sd))`?
   i.e. does the coordinate ideal of the localized ring equal the MAP of the coordinate ideal? The
   subtlety: `algebraMap B (MvPolynomial σ Sd)` sends `X b ↦ X b` (the coord var), so map of
   span{X b} = span{algebraMap (X b)} = span{X b} = K. Is `algebraMap B (MvPolynomial σ Sd) (X b) = X b`
   provable cleanly (what lemma — `IsScalarTower`/`MvPolynomial.algebraMap_def`/`map_X`)? Any defeq trap
   with the `M.map C` localization instance's `algebraMap`?
2. Disjointness: cleanest way to get `Disjoint ((powers f).map C : Set B) (K₀ : Set B)` — is it
   `Ideal.disjoint_powers_iff_notMem (C f) hK₀.isRadical |>.2 (h : C f ∉ K₀)` after rewriting
   `(powers f).map C = powers (C f)` (Submonoid.map_powers)? And `C f ∉ K₀` from `f ≠ 0` via the
   aeval-0 characterization?
3. Is there a SIMPLER route I'm missing — e.g. a direct `height_graphIdeal_eq`-style field-catenary
   over Sd, or `MvPolynomial.ringKrullDim` + a localized catenary? Or is the height_map_of_disjoint
   transport genuinely the cleanest at v4.29?
4. The scalar-tower / instance setup to even STATE `height K₀.map = height K₀` with these exact rings:
   what `[Algebra]`/`[IsScalarTower]`/`[IsLocalization]` instances must I provide vs are automatic?
   The `MvPolynomial.isLocalization` instance is over `M.map C` — does `height_map_of_disjoint` accept
   that monoid directly?
</task>

<output_contract>
1. VALIDATE or correct the 3-step plan (K = K₀.map; height_map_of_disjoint; height_coordIdeal_eq).
2. For Q1: the exact lemma(s) for `Ideal.span(range X) = K₀.map (algebraMap)` over the localization,
   or a 3-5 line proof sketch. Flag any defeq trap.
3. For Q2: the exact disjointness lemma chain.
4. For Q3: is there a strictly simpler route? If yes, name it; if no, say so.
5. For Q4: the minimal instance list to make the statement typecheck.
Lemma names over prose; flag each (confident-v4.29) / (unsure).
</output_contract>

<grounding_rules>
Flag every Mathlib lemma (confident-exists-v4.29) or (unsure — verify). Distinguish "exists" from
"applies here". Don't invent plausible names. The MvPolynomial.isLocalization instance + the scalar
tower interplay is the likely friction — be concrete about it.
</grounding_rules>
