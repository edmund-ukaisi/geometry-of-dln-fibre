<task>
Adjudicate, as an independent algebraic geometer / commutative algebraist, a SHARP circularity
question about a Lean-4 + Mathlib (pin v4.29) formalization route. A ring-level construction was
CIRCULAR; a proposed SET-level reformulation claims to escape the circularity. Test that claim HARD —
is the set-level route genuinely free of the circularity, or does it smuggle the same gap back in?
Do NOT rubber-stamp; argue from the algebra.
</task>

<context>
Setup over an algebraically closed field k, char 0. Affine space Rep_d = ⊕ Mat (composable matrix
tuples, "deep linear network reps"), with the polynomial multiplication map mult : Rep_d → Mat_{p×q}
(p = d_N, q = d_0), the iterated product A_N···A_1. Loci:
- Σ̄^r := {A | rank(mult A) ≤ r}  (closed rank-≤r product locus, REDUCIBLE in general — it is a union
  ⋃_M of θ orbit closures, θ can be > 1).
- F := mult⁻¹(E), E a rank-r normal form (the fibre; also REDUCIBLE — (3,3,3),r=1 anchor: F-comps
  dims 10,9,9).
- δ := r(p + q − r) = dim Mat^{=r}.
TARGET (hSweep):  varietyDim Σ̄^r = δ + varietyDim F   [varietyDim Z := Krull dim of the SET-LEVEL
coordinate ring O(Z) = MvPolynomial(coords)/vanishingIdeal(Z); vanishingIdeal is radical by
construction, so varietyDim only sees the reduced closed set / Zariski closure.]

THE PIVOT-CHART GAUGE (already formalized, green):
On the pivot chart U = {detΔ ≠ 0} (Δ = top-left r×r minor of the generic product mult), there is an
explicit Schur normalization. For a block matrix M = [[Δ,B12],[B21,B22]] with Δ invertible and the
rank-r/fibre relation B22 = B21 Δ⁻¹ B12, the unitriangular conjugation
    L⁻¹ · M · H⁻¹ = diag(I_r, 0),   L = [[I,0],[B21Δ⁻¹,I]], H = [[Δ,B12],[0,I]].
The blocks L,H depend REGULARLY (as matrices over the localization SchurLoc = Localization.Away detΔ)
on the base point. This is realized as an ENDPOINT base-change `endpointGauge` ∈ BaseChangeGroup over
SchurLoc (H at source vertex, L⁻¹ at target vertex, 1 interior — inner units telescope away in mult).
`schurComplement_normal_form` (the matrix identity above) is LANDED, network-free.

ALSO LANDED:
- The sweep SET identity: Σ^r = ⋃_P (P•·)''F  (productRankLocus_eq_iUnion_smul_fibre), P over the
  endpoint base-change group H = GL_p × GL_q.
- vanishingIdeal transport WITHOUT generators: for a base-change (linear coordinate auto) P,
  vanishingIdeal((P•·)''Z) = comap(baseChangeAlgEquiv P)(vanishingIdeal Z), and
  RingEquiv.height_comap gives codim/dim invariance. (vanishingIdeal_image_smul + height_comap.)
- ringKrullDim_quotient_radical: ringKrullDim(R/I) = ringKrullDim(R/radical I) — varietyDim is
  radical-insensitive. So we never need an ideal to BE radical to compute varietyDim.

THE RING-LEVEL ROUTE THAT WAS CIRCULAR (R2-3b-4):
It built a localized chart RING Sred = Localization.Away(ΔPdeep) / IadDeep (IadDeep = the determinantal
base ideal sigmaIdeal pushed into the localization), gave Sred a SchurLoc-algebra structure, and tried
to build a RING isomorphism e : Sred ≃ₐ[k] SchurLoc ⊗_k FibreAlg (product iso). The FORWARD map of e
required the STRICT ideal inclusion sigmaIdeal ≤ ker(comorphism) — but only sigmaIdeal ≤ radical(ker)
was available, and proving the STRICT inclusion IS proving the chart cut is reduced — the very thing e
was meant to establish. CIRCULAR. (Both sides are also REDUCIBLE: (3,3,3) anchor Sred has components
10,9,9, so equal-height + equal-radical does NOT force equal radical ideals — a separate obstruction.)

THE PROPOSED SET-LEVEL ESCAPE (what we must adjudicate):
Claim: work entirely with POINT SETS and vanishingIdeal (radical-insensitive). The parameterized gauge
endpointGauge carries the gauge-image of (Σ̄^r ∩ chart U) onto a PRODUCT SET (base δ-coord directions)
× (fibre E), AT THE SET LEVEL — i.e. as an equality of point sets (or of their Zariski closures). Then
varietyDim of the chart = δ + varietyDim F by: (i) the gauge is a regular automorphism, so it preserves
varietyDim (height_comap); (ii) the product set's dimension splits; (iii) glue over the finite pivot
cover; (iv) the chart is dense in the top component so its dim = dim Σ̄^r. The claim is that because we
only ever take vanishingIdeal of point sets (automatically radical) and transport by comap of a regular
AUTOMORPHISM (not a non-injective comorphism), we NEVER need the strict inclusion sigmaIdeal ≤ ker, and
NEVER need any ideal to be radical — the circularity is structurally absent.
</context>

<questions>
1. THE CRUX. Is the set-level reformulation genuinely free of the R2-3b-4 circularity, or does it
   smuggle it back in? Specifically: the ring-level circularity was "the forward map of e needs the
   strict inclusion = reducedness of the cut." At the set level, the analogous step is "the gauge-image
   of (Σ̄^r ∩ U) EQUALS the product set (base × fibre) as point sets." Is establishing THAT set equality
   secretly equivalent to the strict ideal inclusion / reducedness? Or is it a genuinely weaker,
   directly-checkable statement about points (a point A is in Σ̄^r ∩ U iff its gauge-normalization has
   the block form [[Δ,B12],[B21, B21Δ⁻¹B12]] with the bottom-right block determined)? Distinguish: a
   set equality of points can be checked pointwise (membership iff membership) — does that pointwise
   check require any reducedness, or is it elementary linear algebra (rank ≤ r on the chart iff the
   Schur complement B22 − B21Δ⁻¹B12 = 0)?
2. THE PRODUCT-SET DIMENSION SPLIT. Even granting the set equality "chart-image = base-set × fibre-set",
   does varietyDim(X × Y) = varietyDim X + varietyDim Y hold for REDUCIBLE affine sets X, Y over alg-closed
   k at the SET/varietyDim level, and is it Lean-v4.29-reachable? Mathlib v4.29 LACKS ringKrullDim(A⊗B) =
   dim A + dim B and trdeg-of-tensor-product. Does the set-level product-dimension need that absent tensor
   theorem, or can it be gotten another way (e.g. each is a poly extension: O(base × fibre) = O(base)[fibre
   coords]/... )? Is this the REAL residual wall even after the circularity is dissolved?
3. THE LOCALIZATION-DIMENSION SUBLEMMA. "A non-empty Zariski-open subset (detΔ ≠ 0) of an irreducible
   variety has the variety's Krull dimension." ringKrullDim_localization is Mathlib-absent at v4.29. Is
   this sublemma reachable at v4.29 — via trdeg (a nonempty open of an irreducible affine variety has the
   same function field, hence same trdeg = dim), or via some height argument — or is it itself a wall?
   Sketch the cheapest route or name the absent piece.
4. THE GLUE + DENSITY. varietyDim(⋃ finite Zᵢ) = maxᵢ varietyDim Zᵢ (Spec-level union/minimal-prime
   facts) and "the chart is dense in the top component(s)". Reachable, or hidden cost?
</questions>

<output_contract>
- ONE-LINE VERDICT: "SET-LEVEL ESCAPES the circularity; the residual wall is [precise absent theorem],
  ~M modules" OR "SET-LEVEL DOES NOT ESCAPE: establishing [the set equality] is equivalent to [the strict
  inclusion / reducedness], so the circularity persists."
- For Q1: a CRISP yes/no on whether the set equality is pointwise-checkable elementary linear algebra
  (free of reducedness) vs secretly the strict-inclusion. This is the make-or-break — be decisive.
- For Q2: whether the product-set dimension split is the real residual wall, and whether it needs the
  Mathlib-absent tensor Krull-dim theorem or has a cheaper SET-level route.
- For Q3: localization-dim sublemma — reachable (sketch) or wall (name the piece).
- Distinguish FACT from INFERENCE. Name Mathlib lemmas where you assert presence/absence; flag guesses
  about v4.29 contents. Honest module-count for any residual sublibrary.
</output_contract>

<grounding_rules>
- The make-or-break is Q1: does the set-level membership equality require reducedness, or is it elementary
  pointwise linear algebra? Reason from what it takes to PROVE "A ∈ Σ̄^r ∩ U ⟺ gauge(A) ∈ product set."
- Do not paste Lean you have not type-checked; name Mathlib lemmas and describe shapes.
- If the circularity is escaped, the residual wall is likely Q2 (product dim) or Q3 (localization dim) —
  say which is tightest and its honest cost.
</grounding_rules>
