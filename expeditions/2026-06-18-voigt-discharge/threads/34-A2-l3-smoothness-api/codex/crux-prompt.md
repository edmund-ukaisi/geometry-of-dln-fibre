# Codex consult — the L3 smoothness crux: is `IsOpen O_M` reachable, or is there a route avoiding it?

## Context (Lean 4 + Mathlib v4.29, formalising a quiver/AG result)

Setting: equioriented type-A quiver. `d : Fin (N+1) → ℕ` a dimension vector. `Rep_d` =
composable matrix tuples ≅ `RepCoord d → k` (a finite-dim affine space over field `k`,
`[IsAlgClosed k]`). A reductive group `G = ∏ GL(d_v)` acts by base change. `M` a tuple
(orbit normal form). Landed Lean objects (all sorry-free):

- `orbitRankLocus M = {A | ∀ i≤j, rankPattern A i j ≤ rankPattern M i j}` — determinantal locus.
- `orbitSet M` (= O_M as a point set in `RepCoord d → k`) = `canonicalCoord '' {A | ∃ P:G, P•M = A}`.
- `rankPattern_eq_iff_orbit A B : (∀ i≤j, rankPattern A i j = rankPattern B i j) ↔ ∃ P:G, P•M=A`.
  (So O_M = {A | rankPattern A = rankPattern M} EXACTLY — orbit = equality of all interval ranks.)
- `vanishingIdeal (canonicalCoord '' orbitRankLocus M) = vanishingIdeal (orbitSet M)` (L6, the
  Abeasis–Del Fra ideal equality) ⟹ same Zariski closure: `Ō_M = orbitRankLocus M` as closed sets.
- `isPrime_vanishingIdeal_orbitRankLocus` ⟹ `A := MvPolynomial(RepCoord d) k / vanishingIdeal(Z_M)`
  is a DOMAIN; so `Spec A` is integral (hence irreducible + reduced), finite type / finite
  presentation over `k`. `Z_M = orbitRankLocus M` is its variety.
- `rankMinorSet M` cuts out `Z_M` set-theoretically (`zeroLocus (span rankMinorSet) = Z_M`).

GOAL: `IsSmoothAt k m_M` where `m_M` = the maximal ideal of the k-rational point M in A.
ROUTE (homogeneity): (i) Mathlib `Scheme.Hom.dense_smoothLocus_of_perfectField` gives the smooth
locus `S ⊆ Spec A` is dense-open (perfect field, reduced, finite presentation); (ii) the G-action
is by k-algebra automorphisms of A, so `S` is G-stable and transitively-acted on WITHIN O_M; (iii)
`rankPattern_eq_iff_orbit` = transitivity; (iv) the smooth closed k-point we extract from `S` must
lie in O_M so that translation carries smoothness to m_M.

In the Mathlib group-scheme precedent (`smooth_of_grpObj_of_isAlgClosed`), translation is transitive
on the WHOLE scheme so they prove smoothLocus = ⊤. We CANNOT: O_M ⊊ Z_M (Z_M has lower-rank
boundary orbits). We only get transitivity WITHIN O_M.

## THE QUESTIONS

1. **Is step (iv) — the smooth closed k-point lies in O_M — genuinely requiring `O_M` to be
   OPEN (equivalently locally closed) in `Spec A`?** My analysis: S is open-dense; O_M is dense
   (since Ō_M = Z_M). For `S ∩ O_M` nonempty-with-a-closed-point via Mathlib
   `nonempty_inter_closedPoints` (needs `IsLocallyClosed`), I need O_M locally closed. Two dense
   sets, one open: S ∩ O_M is locally closed iff O_M is. Is there a route that AVOIDS proving O_M
   locally closed? E.g. does the COMPLEMENT `Z_M \ O_M` (the lower-rank locus) being CLOSED already
   give O_M open for free?

2. **The rank-stratification idea.** `Z_M \ O_M = {A ∈ Z_M | rankPattern A < rankPattern M for some
   i≤j}` = `⋃_{i≤j} {A ∈ Z_M | rankPattern A i j ≤ rankPattern M i j − 1}` = a finite union of
   LOWER rank loci, each of which is itself an `orbitRankLocus` of a smaller tuple, hence Zariski
   CLOSED (determinantal). So `Z_M \ O_M` is closed in `Z_M`, hence `O_M` is OPEN in `Z_M`. Is this
   correct? Pitfall: "rank ≤ r−1" is closed (determinantal, fewer minors vanish... no: rank ≤ r−1
   means MORE minors vanish, so it IS closed — a determinantal locus). So O_M = Z_M minus a finite
   union of determinantal closed sets = open in Z_M. Does this hold, and does it transfer to
   `IsOpen (O_M : Set (Spec A))` cheaply, given Mathlib v4.29 has NO matrix-rank-lower-
   semicontinuity lemma and NO "rank ≥ r is open" lemma (I grepped: ABSENT)?

3. **Point-set vs scheme topology.** `O_M`/`Z_M` are defined as subsets of `RepCoord d → k` (a bare
   function type, NO topology in the Lean development). The smoothness argument lives in `Spec A`'s
   Zariski topology (primes of A). I need to transport "O_M is open as a subset of the k-points"
   to "the corresponding set of closed points / primes is open in Spec A". The k-points of Spec A
   (alg closed) ↔ closed points ↔ max ideals ↔ points of Z_M (Nullstellensatz). Is the cleanest
   move: define everything via the determinantal IDEALS on the ring side (the lower-rank loci as
   `zeroLocus` of bigger minor ideals in A), so `D(some minor) ∩ ...` gives an honest open in
   `Spec A` directly — bypassing the point-set topology entirely? Sketch the ring-side open: O_M's
   primes = those where the minors realizing rankPattern M = the target are NONzero (a basic open
   `D(minor)`) intersected with Z_M's closed conditions. Concretely: is `O_M = ⋃ (over choices of
   r×r submatrices that are the "pivots" of the normal form) D(det of that submatrix block)`
   inside Spec A? i.e. is the open orbit a FINITE UNION OF BASIC OPENS `D(f)`?

4. **Honest verdict.** Rank the difficulty: is `IsOpen O_M` (a) CHEAP (≤1 module) via the rank
   stratification / basic-open characterization, (b) MODERATE (2-3 modules — need to build the
   "rank ≥ r is a basic-open union" brick from scratch since Mathlib lacks it), or (c) the genuine
   multi-module crux requiring the Borel "orbit is locally closed" homogeneity theorem? Give the
   SINGLE hardest must-build lemma.

5. **Sanity check the whole L3 ladder** (5-7 modules claimed): L3.0 G-action as ring autos +
   m_{P•M} = α_P(m_M); L3.1 FormallySmooth.iff_of_equiv transfer; L3.2 Spec detour
   (dense_smoothLocus + jacobson closed point + StructureSheaf.stalkIso back to AtPrime); L3.3 the
   smooth point ∈ O_M (the crux above); L3.4 assemble. Is the count right? Is anything circular
   (e.g. does L3.2's "closed point exists" secretly need the SAME openness as L3.3)?

Be skeptical and concrete. If route 3 (ring-side basic-open characterization of O_M) collapses the
crux to a clean determinantal-ideal computation, say so and sketch the exact ideal-theoretic
statement. If it doesn't, say where it breaks.
