# Consult: Lean (Mathlib v4.29) reachability of the SMOOTHNESS/SUBMERSION route for a fibre-codimension residual

You are a second, decorrelated model. I want an independent read on whether a specific Lean-formalisation
route is reachable at Mathlib v4.29, reusing an existing engine. Be concrete about Mathlib lemma names;
flag what is ABSENT at v4.29; do not assume the latest Mathlib.

## Mathematical setting (deep linear networks; Lehalleur–Rimányi Lemma 4.6)

- `Rep_d` = tuples of composable matrices `A = (A_N, …, A_1)`, `A_i : Fin d_i × Fin d_{i-1}`. As a variety
  it is affine space with coordinate ring `R = MvPolynomial (RepCoord d) k`, `k` algebraically closed,
  char 0.
- `mult : Rep_d → Mat_{d_N × d_0}`, `A ↦ A_N ⋯ A_1`. There is a comorphism (already built):
  `multComap : MvPolynomial (Fin d_N × Fin d_0) k →ₐ[k] R`, `X(r,c) ↦ multPoly(r,c)` (the generic
  product entries). The fibre `mult⁻¹(B)` has image = `zeroLocus(fibreGenIdeal d B)`,
  `fibreGenIdeal = span{multPoly(r,c) − C(B r c)} = Ideal.map multComap (m_B)`.
- TARGET (the residual): for `B` of rank `r`, `r ≤ min d`, `N ≥ 1`,
  `codim_Rep(mult⁻¹ B) = C + δ`, where `C = cCodim d r = codim Σ̄^r` (LANDED) is the quiver
  codimension of the closed rank-≤r product locus `Σ̄^r = productRankLocusLE d r`, and
  `δ = r(d_0 + d_N − r)` is the rank-locus shift.
- `codim_Rep(Z) := height (vanishingIdeal (canonicalCoord '' Z))` (an `Ideal.height` in `R`).
- It suffices (a landed reduction G1) to prove it for the normal form `E = diag(I_r, 0)`.
- A NO-GO is established for: (a) global flatness of `mult` (fibre dim JUMPS as rank drops, so
  going-down `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` does NOT apply at the closed point B);
  (b) the determinantal-trivialization route walls at a CIRCULARITY — building the Schur product iso
  `e : Sred ≃ₐ[k] SchurLoc ⊗ FibreAlg E` is equivalent to proving `fibreGenIdeal E` is radical (the iso
  forces FibreAlg reduced). The radicality is certified TRUE on paper but its Lean proof needs a deep
  localized flat trivialization the engine lacks (N=1 graph/Schur trick does not port to N≥1; the deep
  rank ideal factors).

## The engine ALREADY built (for the ORBIT codimension — "Voigt discharge")

A full pipeline `IsSmoothAt ⟹ regular local ring + ringKrullDim = relative dim`, plus a cotangent/Jacobian
comparison and a dual-number directional-derivative tangent-space machine. Headlines (Lean, v4.29):

1. `SmoothPointRegular.smooth_point_isRegularLocalRing [IsAlgClosed k] (m : Ideal A) [m.IsMaximal]
   [IsSmoothAt k m] : IsRegularLocalRing (Localization.AtPrime m)` — for `A` finite-type over alg-closed `k`.
   Companion `finrank_cotangentSpace_eq_of_isSmoothAt`: `finrank κ(m) (CotangentSpace (AtPrime m)) =
   ringKrullDim (AtPrime m)`.
2. `SmoothLocalRelativeDimension.ringKrullDim_localizationAtPrime_eq_of_isSmoothAt`:
   `IsSmoothAt k m ⟹ ringKrullDim (AtPrime m) = relative dim n` (étale-over-affine route, NON-circular).
3. `CotangentJacobian.finrank_cotangentSpace_eq_finrank_ker_jacobian`: at a k-rational point `a` of
   `V(span g)`, `finrank k (CotangentSpace (AtPrime m_a)) = finrank k (ker (jacobian g a))`, where
   `jacobian g a` is the Jacobian matrix of the GENERATORS evaluated at `a` (rows=gens, cols=vars).
   This is a TANGENT-SPACE = JACOBIAN-KERNEL identity at a rational point — pure linear algebra, no smoothness.
4. `MatrixKaehler.derivMatrix_mul_apply` (entrywise matrix-product Leibniz through a `Derivation`),
   `derivMatrix_inv_apply` (`D(U⁻¹) = −U⁻¹ DU U⁻¹` entrywise).
5. The ORBIT smoothness `OrbitSmooth.isSmoothAt_normalFormIdeal [IsAlgClosed k]` is proved NOT by a
   Jacobian-rank computation but by GENERIC SMOOTHNESS over a perfect field
   (`Scheme.Hom.dense_smoothLocus_of_perfectField`, reduced scheme) INTERSECTED with a DENSE `G_d`-orbit
   (the orbit closure has a dense single orbit, density of orbit closed points → a smooth orbit point →
   transport smoothness along the group action to the normal-form point).
6. `OrbitTangentCotangent` builds, via DUAL NUMBERS, a directional-derivative functional, an injection
   `range δ⁰ ↪ m_M.Cotangent`, and chains `finrank(m_M.Cotangent) = varietyDim Z_M` using (1)+(2). This is
   the REVERSE (cotangent) bound. The FORWARD (submersion) bound `varietyDim Z_M ≤ finrank(range δ⁰)` comes
   separately from `OrbitDifferentialRank` (generic-Jacobian rank via the matrix-Kähler identity +
   transpose pairing + `JacobianTrdeg` char-0 differential criterion).

## KEY OBSTACLE I FOUND (please corroborate or refute)

At Mathlib v4.29, `Mathlib/RingTheory/RegularLocalRing/` contains ONLY `Defs.lean`. There is NO theorem
`IsRegularLocalRing R ⟹ IsDomain R` and NO `⟹ IsReduced R` (Stacks 00NP, "regular local ⟹ domain", is
absent). Only the converse-flavoured `[IsDomain R][IsPrincipalIdealRing R] ⟹ IsRegularLocalRing R` instance
exists. So the smooth-point pipeline gives a REGULAR LOCAL RING + its Krull dimension, but does NOT directly
give "reduced" / "domain" at v4.29.

## QUESTIONS (be specific, name Mathlib lemmas, flag ABSENT pieces)

1. **Does a clean Lean path exist** "fibre cut smoothly on a chart (Jacobian full rank at chart points)
   ⟹ reduced + the right Krull codimension `C+δ`", reusing `SmoothPointRegular` / `CotangentJacobian` /
   `SmoothLocalRelativeDimension` / `MatrixKaehler`? Specifically:
   (a) To get `IsSmoothAt k m` for the FIBRE's coordinate ring, the engine's orbit route used a dense
       single orbit. The fibre `mult⁻¹(E)` is NOT a single `G_d`-orbit (it is only `G_out = GL_{d_N} ×
       GL_{d_0}`-stable, and is generally reducible/non-equidimensional for low r). Can `IsSmoothAt` for the
       fibre be obtained by generic smoothness over a perfect field on the fibre's OWN reduced scheme — but
       that needs the fibre scheme to be REDUCED first (circular with the radicality?), AND a dense set of
       rational points one can transport smoothness to/across. Is there a non-circular way?
   (b) Alternatively: is there a Mathlib v4.29 lemma "Jacobian of generators has constant full rank `c` on a
       (dense/open) chart ⟹ the ring is smooth of relative dim (n−c) there" — i.e. a JACOBIAN CRITERION for
       smoothness, not just the tangent-space=ker-Jacobian identity at one point? Or must this be built from
       the cotangent finrank (`CotangentJacobian`) + a separate dimension lower bound + `iff_finrank_cotangentSpace`?
2. **The "reduced" payoff.** Granting `IsRegularLocalRing (AtPrime m)` at every closed point of the fibre
   chart: at v4.29, how does one conclude the fibre coordinate ring is REDUCED (needed to identify
   `fibreGenIdeal = vanishingIdeal`, dropping the `radical(...)`)? Options: (i) prove `IsRegularLocalRing ⟹
   IsDomain` from scratch (how many modules? Stacks 00NP via associated-graded is a PID/Cohen–Macaulay-free
   route, or the "regular ⟹ domain by gr is a polynomial ring" route); (ii) sidestep reducedness entirely by
   working with `height(fibreGenIdeal)` directly (height is radical-insensitive: `height I = height
   I.radical`) — does this dodge the need for reducedness AND for the iso `e`? If codim is just
   `height(fibreGenIdeal)`, do we still need smoothness/reducedness at all, or only a height computation?
3. **Submersion/relative-dimension for codim directly.** The cleanest target is
   `height(fibreGenIdeal E) = C + δ`. Is there a Lean-reachable route at v4.29 that computes this height via
   the SUBMERSION of `mult` restricted to the rank-r chart (regular fibre dimension = dim Rep − dim base − δ
   ... ) WITHOUT building the product iso `e` and WITHOUT proving radicality — e.g. by the dual-number
   tangent-space machine (`OrbitTangentCotangent`-style) applied to the fibre, squeezing
   `varietyDim(fibre) = finrank(tangent space of the fibre at a smooth point)` between a Jacobian-rank
   forward bound and a cotangent reverse bound, mirroring the orbit Voigt discharge but for the fibre? What
   are the obstacles (the fibre is not a homogeneous space; no dense single orbit; reducibility)?
4. **Module-count estimate.** For the most reachable route you identify, estimate the number of new Lean
   modules and pinpoint the single hardest rung. Also: is the `IsRegularLocalRing ⟹ IsDomain` gap (if needed)
   itself a multi-module sub-project at v4.29, or a short proof?

Give a ranked recommendation: which of (smoothness/submersion via generic smoothness), (Jacobian-criterion
smoothness), (height-direct dodging reducedness), or (type-A rank-locus reducedness from scratch) is the
single most reachable, and WHY, with the key reusable engine handles and the biggest gap named.
