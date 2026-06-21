<task>
Lean 4 + Mathlib (pin v4.29) formalisation architecture decision. I am red-teaming a route choice
BEFORE committing. Withhold agreeing with me; give your independent verdict first.

CONTEXT. I have, fully proved in Lean (call it "the engine"):
- A point-set affine setup: a finite coordinate index `sigma` (= matrix entries), the polynomial ring
  `R = MvPolynomial sigma k` over a field `k`, and for a Zariski-closed set `Z subset (sigma -> k)`:
  * `vanishingIdeal k Z : Ideal R` (Mathlib's `MvPolynomial.vanishingIdeal`);
  * `codimRep Z := Ideal.height (vanishingIdeal k Z)`  (an ENat);
  * `varietyDim Z := (ringKrullDim (R / vanishingIdeal Z)).unbotD 0`  (an ENat).
- A PROVED catenary bridge (over `[IsAlgClosed k]`, `Finite sigma`): if `vanishingIdeal Z` is PRIME then
  `codimRep Z + varietyDim Z = Nat.card sigma`. (This is L0, done. It needs primeness, i.e. irreducibility,
  fed as a hypothesis; `Spec(R/I)` irreducible <=> `R/I` domain <=> `I` prime is the only "topology" used.)
- The object of interest: `M` is a representation of an equioriented type-A quiver = a tuple of matrices
  `(M_0,...,M_{N-1})`, `M_i : k^{d_{i+1}} x k^{d_i}`. The group `G = prod_v GL_{d_v}` (the UNITS of the
  matrix rings) acts by `(P . M)_i = P_{i+1} M_i P_i^{-1}`. The orbit is `O_M`; its Zariski closure is the
  rank locus `Z = orbitRankLocus M` (closed, equals Obar_M, cited Thm 3.8).
- A PROVED 2-term deformation complex `delta : C0 -> C1`, `delta(phi)_i = phi_{i+1} M_i - M_i phi_i`, with
  `C0 = prod_v Mat(d_v,d_v)`, `C1 = prod_i Mat(d_{i+1},d_i)`, and `orbitLinearCodim M := finrank C1 -
  finrank (range delta) = finrank (coker delta) = dim Ext^1(M,M)` (all PROVED). NOTE `delta` IS exactly the
  differential of the orbit map `P -> P.M` at `P=1`; `range delta` = tangent-to-orbit at M.

THE ONE REMAINING GOAL (to discharge the last hypothesis `hVoigt`):
    varietyDim (orbitRankLocus M) = finrank (range delta).
Then `codimRep = Nat.card sigma - varietyDim = finrank C1 - finrank(range delta) = orbitLinearCodim`. Done.

THE FORK. Two candidate Lean architectures for that one dimension equality:

(S) SCHEMES. Model `G = prod GL`, the orbit, and the orbit map as Mathlib `AlgebraicGeometry` schemes;
    reuse `smooth_of_grpObj_of_isAlgClosed` (group scheme over alg-closed field is smooth) +
    `Scheme.Hom.dense_smoothLocus_of_perfectField` (generic smoothness). Then transport scheme
    smoothness/dimension back to `varietyDim` (= `ringKrullDim (R / I)`, a RING-side Krull dim).

(A) CONCRETE AFFINE. Stay in the point-set / MvPolynomial / ringKrullDim world. Build the Zariski tangent
    space of `V(I) subset k^n` at the point `M` directly (via `pderiv`/Jacobian, or
    `IsLocalRing.CotangentSpace` of `(R/I)` localized at the maximal ideal of M), prove the orbit tangent
    space = `range delta`, get orbit smoothness from HOMOGENEITY (smooth locus is dense -- generic
    smoothness -- and G-stable, transitive on the orbit => smooth everywhere on the orbit), then use
    `IsRegularLocalRing.iff_finrank_cotangentSpace` (regular local ring <=> finrank cotangent =
    ringKrullDim) at the smooth point M to conclude `varietyDim = finrank(tangent) = finrank(range delta)`.

WHAT I'VE VERIFIED IN MATHLIB v4.29:
- PRESENT: `IsRegularLocalRing.iff_finrank_cotangentSpace`, `IsLocalRing.CotangentSpace`,
  `MvPolynomial.pderiv` (bundled Derivation), `Ideal.Quotient.isDomain_iff_prime`,
  `PrimeSpectrum.irreducibleSpace [IsDomain R]`, `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`,
  `IsHomeomorph.topologicalKrullDim_eq`, scheme `smooth_of_grpObj_of_isAlgClosed`,
  `Scheme.Hom.dense_smoothLocus_of_perfectField`, `Algebra.smoothLocus`/`isOpen_smoothLocus`.
- ABSENT (0 hits): any notion of "dimension of a Scheme X" beyond `topologicalKrullDim` of its space; any
  GL-as-scheme / algebraic-group / orbit-as-scheme / orbit-map-of-schemes API; `ringKrullDim = trdeg` for
  f.g. domains (NOT assembled); any fibre-dimension theorem feeding ringKrullDim; any "smooth point =>
  IsRegularLocalRing" bridge; any algebraic Zariski-tangent-space-of-a-variety object (`Module.tangentSpace`
  is the manifold/normed-field tangent bundle, not this).
</task>

<questions>
1. Which route AVOIDS introducing a NEW scheme<->ringKrullDim dimension bridge? Be concrete about the exact
   glue route S forces (Scheme -> underlying space -> topologicalKrullDim -> via isoSpec homeomorphism ->
   PrimeSpectrum -> ringKrullDim of R/I, AND modelling G/orbit/orbit-map as schemes), versus what route A
   forces (smooth-point => IsRegularLocalRing; tangent = range delta; homogeneity smooth-everywhere).
2. For EACH route, what does Mathlib actually provide vs force me to build, by exact decl name where you can.
3. Is the homogeneity argument (generic smoothness gives a dense smooth point; G acts transitively on the
   orbit and preserves the smooth locus, so EVERY orbit point is smooth) cleanly expressible in the point-set
   world, or does generic smoothness itself only exist scheme-side at this pin (forcing me into schemes
   regardless)? This is the crux.
4. The "smooth point => IsRegularLocalRing (local ring of R/I at the maximal ideal of M)" bridge: how hard,
   and is there a Mathlib path (e.g. via `Algebra.smoothLocus` / formal smoothness of the localization =>
   regular)? Or is identifying `finrank CotangentSpace` with `finrank(range delta)` (Jacobian = differential
   of the orbit map) the cleaner load-bearing lemma to aim at?
5. Any THIRD route I'm missing that gets `varietyDim = finrank(range delta)` more cheaply (e.g. an
   orbit-map fibre-dimension / `dim O = dim G - dim Stab` argument, or computing `ringKrullDim(R/I)` directly
   from a rational parametrization of the orbit)? Cost it honestly against (A) and (S).
6. Net recommendation: (S), (A), or third, and the single hardest sub-lemma of your pick.
</questions>

<output_contract>
Answer the 6 questions in order, terse. For each route give a one-line "new bridge needed? YES/NO + what".
End with: RECOMMENDATION = (S|A|third), HARDEST = <one sub-lemma>, KILL = <the observation that would sink
your pick>. Distinguish what you KNOW (Mathlib decl exists / standard math) from what you INFER.
</output_contract>
