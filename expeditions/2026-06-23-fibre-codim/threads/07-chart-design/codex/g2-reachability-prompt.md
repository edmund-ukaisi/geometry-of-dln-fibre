# Decorrelated design-review consult: formalizing a fibre-bundle dimension shift in Lean 4 / Mathlib v4.29

You are a decorrelated second opinion on a Lean 4 + Mathlib (v4.29 pin) formalization design.
I want your independent read, NOT confirmation. Be a red team. If the whole plan is likely to wall,
say so plainly. Math + Lean-reachability judgement both wanted.

## The mathematical target (Lehalleur–Rimányi 2024, Lemma 4.6)

Fix a dimension vector `d = (d_0,...,d_N) ∈ ℕ^{N+1}`, `N > 0`, field `k` alg-closed char 0.
`Rep_d = ∏_{i=1}^N Mat_{d_i × d_{i-1}}(k)` (composable matrix tuples). The map
`mult : Rep_d → Mat_{d_N × d_0}`, `(A_1,...,A_N) ↦ A_N ⋯ A_1`.
For `B` of rank `r` (`r ≤ min d_i`), the fibre `mult⁻¹(B)` and the closed rank-≤r locus
`Σ̄^r = {A : rank(mult A) ≤ r}`. The identity to prove:

    codim_{Rep_d} mult⁻¹(B) = codim_{Rep_d} Σ̄^r + r(d_0 + d_N − r).

Equivalently (catenary, ambient dim D = Σ_i d_i d_{i-1}):  dim mult⁻¹(B) = dim Σ̄^r − r(d_0+d_N−r).
Set δ := r(d_0+d_N−r) = dim of the rank-exactly-r determinantal variety Mat^{rk=r}_{d_N×d_0}.

Numeric anchor: `(d)=(2,2,2)`, `r=1`: D=8, dim Σ̄^1 = 7, δ=3, dim fibre = 4, codim fibre = 4 = C(=1)+δ(=3).

## The paper's proof (the part I must replace with something Lean-doable)

`mult|_{Σ^r} : Σ^r → Mat^{rk=r}` is a Zariski-locally-trivial fibre bundle, `G_out = GL_{d_N}×GL_{d_0}`
equivariant (`mult(P_N·A·... ) = P_N · mult(A) · P_0⁻¹`). `Mat^{rk=r}` is a single `G_out`-orbit of
`E = diag(I_r,0)`. Local sections of the smooth submersion `G_out → Mat^{rk=r}` give local
trivializations `mult⁻¹(U) ∩ Σ^r ≅ U × mult⁻¹(E)`. Then dim Σ^r = dim Mat^{rk=r} + dim mult⁻¹(E), shift follows.
This is a Lie-group submersion / differential-topology argument over ℂ. I cannot do Lie theory in Lean here.

## What I HAVE in the Lean engine (all landed, sorry-free, Mathlib v4.29)

The engine works with the POINT space `Tuple d := ∀ i, Mat_{d_{i+1}×d_i}(k)` and the canonical
coordinate flattening `canonicalCoord : Tuple d ≃ (RepCoord d → k)`. Geometric codimension is
`codimRepCanonical Z := Ideal.height (vanishingIdeal (canonicalCoord '' Z))`. There is NO scheme,
NO Spec, NO structure sheaf — everything is `MvPolynomial (RepCoord d) k`, vanishing ideals,
`Ideal.height`, `ringKrullDim`.

Landed bricks:
1. **Catenary bridge** (over alg-closed `k`): for an IRREDUCIBLE variety `Z` (i.e.
   `(vanishingIdeal (coord '' Z)).IsPrime`),
   `height (vanishingIdeal (coord''Z)) + varietyDim (coord''Z) = Nat.card (RepCoord d)`,
   where `varietyDim Z := (ringKrullDim (MvPolynomial ⧸ vanishingIdeal Z)).unbotD 0`. Additive form,
   no flatness. (`codimRep_add_varietyDim_eq_card`.)
2. **Affine-domain equidimensionality** (no flatness): for `A = MvPolynomial(Fin n) k ⧸ I` (`I` prime,
   finite-type domain) and a prime `p` of `A`, `height p + ringKrullDim(A⧸p) = ringKrullDim A`.
   Via Noether normalization + integral height transport. (`affine_domain_height_add_ringKrullDim_quotient_eq`.)
3. **Brick A**: `codimRepCanonical Σ̄^r = cCodim d r` (= the combinatorial C), GENERAL in r. Σ̄^r is
   `GL_d`-stable (a finite union of quiver-orbit closures `Ō_M`), so its minimal primes ARE the
   maximal orbit-closure vanishing ideals (`minimalPrimes_sigmaIdeal_eq`), and the codim is the min
   over components (each component's codim via a landed Voigt/Ext computation).
4. **Thermometer**: `varietyDim (Mat^{rk≤r}_{d_N×d_0}) = r(d_0+d_N−r) = δ`. Proved by the N=1
   specialisation of brick A + catenary, NOT by any morphism-dimension theorem.
5. **F1 comorphism**: `mult` is defined over any CommRing, so the generic product entries
   `multPoly d r c := (mult d genericTuple) r c ∈ MvPolynomial (RepCoord d) k`. The comorphism
   `multComap := aeval multPoly : MvPolynomial(Fin d_N × Fin d_0) k →ₐ MvPolynomial(RepCoord d) k`.
   Fibre over B = zeroLocus{multPoly r c − C(B r c)}; `vanishingIdeal(fibre) = radical(fibreGenIdeal)`;
   `fibreGenIdeal B = Ideal.map multComap (maxIdealOfPoint B)` (the "fibre coord ring = R_total ⧸ m_B·R_total" object).
6. **F2 NO-GO** (proved, documented): the naïve sandwich FAILS. Krull bounds height ABOVE by generator
   count d_N·d_0 (wrong direction, ≫ δ). And `mult` is NOT flat globally: fibre dim JUMPS as rank drops
   (rank-1 fibre dim 4, rank-0 fibre dim 5 for (2,2,2)). So going-down height-additivity
   `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` does NOT apply at the closed point B.
   Flatness only holds after restricting to the exact-rank chart. The landed reachable half:
   `codim Σ̄^r ≤ codim mult⁻¹(B)` (pure inclusion `mult⁻¹B ⊆ Σ̄^r`).
7. **Group action machinery** (`Orbit`): the rank pattern is a complete `G_d`-invariant; equal rank
   pattern ⟺ same orbit; mult-equivariance `mult(P•A) = P_N · mult(A) · P_0⁻¹`; codim invariance
   under the coordinate-ring algebra automorphism induced by a base change (`height_map_algEquiv`).
8. **Heavy orbit-image dim machinery** (`OrbitImageDim`/`JacobianTrdeg`): for a quiver orbit
   `orbitRankLocus M`, `varietyDim = trdeg of the orbit-pullback image = finrank(range of the
   deformation differential δ⁰)`, via a generic-point Jacobian / formal-smoothness argument in char 0.
   This is the route that computed the Voigt codim of orbit closures.

## The committed rung-ladder (what I'm probing)

- **G1** (separate, bankable): reduce to `E = diag(I_r,0)`:
  `codimRepCanonical(fibre B) = codimRepCanonical(fibre E)` via the `G_out` linear action on Rep_d
  (acts on end factors A_1, A_N) + mult-equivariance + codim-invariance under the induced algebra
  automorphism + rank-normal-form (any rank-r B = P_N E P_0⁻¹). INDEPENDENT of G2.
- **G2** (THE CRUX): chart trivialization `mult⁻¹(U) ∩ Σ^r ≅ U × mult⁻¹(E)` over pivot chart
  `U = {top-left r×r block of the target invertible}` via explicit section `D = C A⁻¹ B`
  (Schur-complement: a rank-r matrix with invertible top-left block is determined by its
  off-block data); → dim-additivity `dim Σ^r = δ + dim mult⁻¹(E)`.
- **G3** (assembly): dim Σ̄^r = δ + dim(fibre over E) + Brick A min-over-components → the identity.
- **G4**: thin DLN wiring.

## QUESTIONS — I want decorrelated judgement, not agreement

**Q1 (G2 reachability).** Without a general finite-type-morphism dimension theorem and without
schemes/Spec, can the product trivialization `mult⁻¹(U)∩Σ^r ≅ U × mult⁻¹(E)` be expressed and turned
into the DIMENSION statement `dim(mult⁻¹(U)∩Σ^r) = dim U + dim mult⁻¹(E)` on the
`MvPolynomial ⧸ vanishingIdeal` / `Ideal.height` / `ringKrullDim` substrate at Mathlib v4.29? Concretely:
  (a) Does the explicit Schur-complement section (`D = C A⁻¹ B`) give a genuine ISOMORPHISM OF
      COORDINATE RINGS (or a ring iso between the localizations at the pivot chart) that I can build
      as a concrete `AlgEquiv`? Is `dim of a product variety = sum of dims` available, or via
      `MvPolynomial`-tensor / `ringKrullDim` of a polynomial extension? What Mathlib lemmas
      (name them if you can) bound or compute `ringKrullDim (A ⊗ B)` or `ringKrullDim (A[x])`?
  (b) Is restricting to a principal-open chart `D(Δ)` (Δ = the r×r pivot minor) dimension-preserving
      for an irreducible variety in this substrate, and is that a landed/Mathlib-available fact
      (`ringKrullDim` of a localization at a single element of a domain = `ringKrullDim` of the domain)?
  (c) Estimate the module count + the single hardest sub-wall.

**Q2 (route choice for `dim mult⁻¹(E)`).** Compare:
  (a) the G2 chart-trivialization above;
  (b) an INNER-GROUP route: `mult⁻¹(E)` is stable under `H = (∏_{0<i<N} GL_{d_i}) × Stab_{G_out}(E)`.
      It is NOT a single H-orbit (for (2,2,2) the fibre over E has dim 4 but is acted on by a 9-dim H,
      not freely). BUT — could `dim mult⁻¹(E)` be computed directly via the heavy orbit-image /
      Jacobian-trdeg machinery (brick 8) applied to a MODIFIED quiver or a clever
      orbit-like-pullback presentation of `mult⁻¹(E)`? Or via a recursion on N (peel off the last
      factor A_N: condition on rank(A_N) and rank(A_{N-1}⋯A_1))? Is there a CHEAPER route that
      sidesteps building the product-variety isomorphism — analogous to how the thermometer dodged the
      feared morphism theorem via an N=1 specialisation?
  (c) Is there an even cheaper route to the FIBRE dimension via the
      `dim Σ̄^r = dim Mat^{rk=r} + dim fibre(E)` additivity that uses Brick A's component structure
      directly? E.g. is `mult⁻¹(E)` itself a union of (smaller) quiver-orbit closures for the
      "reduced" dimension vector d−r (the paper's `Σ^0_{d−r}` connection: dim Σ^0_{d−r} relates to
      fibre over E)? The paper (Lemma "rank_0" / 4.5) shows `Σ^r_d` relates to `Σ^0_{d−r}` by the
      same +δ; could the fibre over E be EXACTLY (isomorphic to) `Σ^0_{d−r}` = the zero-product locus
      of the reduced dimension vector, which the engine ALREADY handles (r=0 case is landed)?
      THIS is the lead I most want you to evaluate.

**Q3.** Anything in this plan that is subtly wrong, overclaimed, or that you'd attack first?

Answer in structured form: per-question verdict (reachable / hard / wall), the specific Mathlib
lemma names you'd reach for or flag as missing, and a final go/no-go with the single hardest sub-wall.
