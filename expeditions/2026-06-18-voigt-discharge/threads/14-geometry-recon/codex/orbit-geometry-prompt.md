<task>
Setting: Lean 4 + Mathlib (v4.29 pin), formalising the geometry of orbit closures for
equioriented type-A quiver representations (= "deep linear network" composable-matrix tuples).

Fixed data: a dimension vector d : Fin (N+1) → ℕ, and the representation space
  Rep_d = ∏_{i:Fin N} Matrix (Fin (d (i+1))) (Fin (d i)) k   (a tuple A = (A_0,…,A_{N-1})).
Group: G_d = ∏_{v:Fin(N+1)} GL_{d_v}(k), acting by (P • A)_i = P_{i+1} · A_i · P_i⁻¹.
Rank pattern: r_{ij}(A) = rank(A_{j-1}···A_i) = rank of the interval sub-product, for i ≤ j (r_{ii}=d_i).
Orbit ⟺ equal rank pattern is ALREADY PROVED (a complete G_d-invariant, Gabriel/Kostant normal form:
every tuple is G_d-conjugate to a reindexed interval-module direct sum ⊕ M_{ab}; this normal form
`baseChange_normalForm` is proved and available).

I have ALREADY BUILT (network-free Core, all green, axiom-clean):
- A catenary/dimension sub-library: for a finite-type DOMAIN A over a field k, height p + dim(A/p) = dim A;
  height m = dim A for maximal m; ringKrullDim(Localization.AtPrime m) = dim A (local↔global).
- The étale-route dimension bridge: for finite-type A/k, m maximal with IsSmoothAt k m
  (= Algebra.FormallySmooth k (Localization.AtPrime m)), ringKrullDim(AtPrime m) = n = rank Ω[AtPrime m / k].
- smooth_point_isRegularLocalRing: IsSmoothAt k m (k alg closed / perfect) ⟹ IsRegularLocalRing(AtPrime m),
  and finrank_cotangentSpace_eq_of_isSmoothAt: finrank_{κ(m)}(m/m²) = n = ringKrullDim(AtPrime m).
- A Nullstellensatz codim bridge: for an irreducible closed subset Z ⊆ kⁿ (k alg closed),
  height(vanishingIdeal Z) + ringKrullDim(k[x]/I(Z)) = n  (i.e. codim Z = n − dim Z), with dim Z := varietyDim.

The remaining obligation, stated against a concrete tuple M:
  the rank locus  Z_M := { A | ∀ i≤j, r_{ij}(A) ≤ r_{ij}(M) }  ⊆ Rep_d ≅ k^{Σ d_{i+1}d_i}
  has  varietyDim(Z_M) = finrank_k(range δ⁰)
where δ⁰ : ⊕_v Mat_{d_v} → ⊕_i Mat(d_{i+1},d_i), δ⁰(φ)_i = φ_{i+1}·M_i − M_i·φ_i, is the
action-orbit-map differential at P=1 (range δ⁰ = tangent-to-orbit; proved finrank Rep − finrank range δ⁰
= dim Ext¹(M,M)).

I have decomposed the obligation into four Lean pieces and want your INDEPENDENT route + difficulty read:
- (L6) the SET equality  Z_M = closure of the G_d-orbit O_M  (rank conditions cut out the orbit closure;
       the "degeneration" direction Z_M ⊆ Ō_M is the hard inclusion).
- (L1) Ō_M is irreducible, delivered as  (vanishingIdeal(image of Z_M)).IsPrime.
- (L3) M is a smooth point of Z_M (= Ō_M): IsSmoothAt k m_M for the local coordinate ring at M.
- (L2) the cotangent space  m_M/m_M²  at M has finrank_k = finrank_k(range δ⁰)  (identify the Zariski
       tangent space of Z_M at M with range δ⁰ = image of the orbit-map differential).
</task>

<output_contract>
Answer in five short sections, terse, Lean-aware (name the actual Mathlib v4.29 API you'd lean on):

1. DEGENERATION (L6, Z_M ⊆ Ō_M): cleanest route to "rank conditions cut out the orbit closure" for
   equioriented type A, GIVEN the proved normal form ⊕M_{ab} and orbit⟺equal-rank-pattern. Is there a route
   via explicit one-parameter degenerations of interval modules (a finite chain of "merge two bars"
   degenerations realising any r ≤ r(M) inside the closure), avoiding general orbit-closure theory? Or is
   topological-closure-in-kⁿ itself the bottleneck (needing a Zariski-closure/limit API Mathlib may lack)?
   Bounded module vs sub-library?

2. SMOOTH ORBIT + TANGENT = im(differential) (L3+L2): cleanest route to "the orbit is smooth and its
   Zariski tangent space at M = image of the action differential δ⁰". Concretely, how to PRODUCE the instance
   IsSmoothAt k m_M (= FormallySmooth k (AtPrime m_M)) for the orbit coordinate ring, given a transitive
   smooth group action — what is the minimal-friction Lean route to a *ring-side* smoothness/density fact
   WITHOUT modelling G_d as a Mathlib group-scheme? Is homogeneity (smooth locus is G-stable + dense ⟹ smooth
   everywhere) reachable on the ring side, or does it force a Spec/scheme detour?

3. The TANGENT identification (L2): Zariski tangent space of V(I) ⊆ kⁿ at a rational point = ker(Jacobian) of
   generators = (m/m²)^∨. What Mathlib API computes m_M/m_M² for an explicit affine coordinate ring as
   ker of a pderiv-Jacobian? Is identifying it with range δ⁰ a clean linear-algebra step or a sub-library?

4. RANKING: which 1–2 of L6/L1/L3/L2 are hardest, and which is most likely to be a multi-module sub-library
   (vs a bounded single module)?

5. ALTERNATIVE: is there a route that BYPASSES some of L1/L2/L3/L6 — e.g. computing varietyDim(Z_M) directly
   as a determinantal-variety dimension, or a normal-form chart (rational parametrisation of the orbit via the
   ⊕M_{ab} normal form) giving dim(orbit) = finrank(range δ⁰) without smoothness? Name the cleanest bypass if any.
</output_contract>

<grounding_rules>
Distinguish (i) standard math facts, (ii) what Mathlib v4.29 plausibly has API for vs what you're inferring,
(iii) genuine guesses. Flag any lemma name you are not confident exists as "(name uncertain)". Do not assume a
Mathlib group-scheme / orbit-scheme / algebraic-group library exists — I have checked, it does not. Prefer
routes that stay on the point-set / MvPolynomial / ringKrullDim(R/I) side, since my whole stack is there.
