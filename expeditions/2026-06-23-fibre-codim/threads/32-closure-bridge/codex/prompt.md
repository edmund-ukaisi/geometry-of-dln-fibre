# Codex consult — closure/density bridge `hClosure`, cheapest PROVABLE route at Lean4/Mathlib v4.29

You are a decorrelated second opinion for a Lean 4 + Mathlib formalisation. I will NOT take your
answer as authority; I want your independent adjudication of one truth-value and a provability ranking.

## Setup (precise, self-contained)

Fix a base field `k` (assume algebraically closed, char 0, infinite where needed). Fix a dimension
vector `d = (d_0, …, d_N)`, `N ≥ 1`. `Rep_d = ∏_{i=1..N} Mat_{d_i × d_{i-1}}(k)` is an affine space
(point space `RepCoord d → k` via the entry-flattening bijection `canonicalCoord : Rep_d ≃ (RepCoord d → k)`).
`mult : Rep_d → Mat_{d_N × d_0}` is the ordered matrix product `A ↦ A_N ⋯ A_1`.

Two loci, as subsets of `Rep_d` (pushed to point space by `canonicalCoord`):
- `Σ^r = productRankLocus d r = {A | rank(mult A) = r}`   (EXACT rank r)
- `Σ̄^r = productRankLocusLE d r = {A | rank(mult A) ≤ r}` (rank ≤ r)

`varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal(Z'))).unbotD 0`,
where `Z' = canonicalCoord '' Z` is the flattened set and `vanishingIdeal` is over `k`.

### The target (a MUST-PROVE, zero-cite)
```
hClosure : varietyDim (canonicalCoord '' Σ^r) = varietyDim (canonicalCoord '' Σ̄^r).
```

### Engine facts already LANDED and available (verified in-repo)
1. `varietyDim` reads ONLY off `vanishingIdeal` of the flattened set, and `ringKrullDim` is
   radical-insensitive: `ringKrullDim_quotient_radical : ringKrullDim (R⧸I) = ringKrullDim (R⧸I.radical)`,
   and `ringKrullDim_quotient_eq_of_radical_eq`. (`Core.VarietyDimRadical`)
2. `vanishingIdeal_repClosure : vanishingIdeal (repClosure S) = vanishingIdeal S` where
   `repClosure S := zeroLocus (vanishingIdeal S)` is the Zariski closure operator — FIELD-CLOSURE-FREE,
   it is `u∘l∘u = u` of the Galois connection `zeroLocus ⊣ vanishingIdeal`. (`Core.OrbitClosure`)
3. `vanishingIdeal_anti_mono`, `zeroLocus_anti_mono`, `subset_repClosure`, `repClosure_mono`,
   `repClosure_idem`, `repClosure_subset_of_subset_repClosure`. (`Core.OrbitClosure`)
4. G2 stratification: `Σ̄^r = productRankLocusLE d r = ⋃_{M : rank(mult M) ≤ r} orbitRankLocus M`
   where `orbitRankLocus M` is the determinantal locus `{A | rankPattern A ≤ rankPattern M}` = the
   Zariski closure `Ō_M` of the orbit of M. Each `orbitRankLocus M` is Zariski-closed
   (`isZariskiClosed_orbitRankLocus`). (`Core.SigmaStratification`, `Core.RankLocusClosed`)
5. The H-sweep: `Σ^r = ⋃_{P : H} P • (fibre d E)` for any fixed rank-r target E (H = GL_{d_N}×GL_{d_0}
   acting on endpoints), `mult` is H-equivariant, `exists_baseChange_of_rank_eq`. (`Core.EndBaseChangeSweep`)
6. `codimRepCanonical Σ̄^r = C = cCodim d r` is LANDED (`Core.SigmaCodim`), computed as the MIN over
   orbit components of their codim. `codimRepCanonical_mono` (codim anti-monotone in set inclusion).
7. `varietyDim_eq_of_coordRingAlgEquiv` (transport across coordinate-ring AlgEquiv). (`Core.VarietyDimRadical`)
8. `Σ^r ⊆ Σ̄^r` trivially (`fibre_subset_productRankLocusLE` pattern; rank = r ⟹ rank ≤ r).

## The questions

(A) Is `hClosure` FREE the moment `vanishingIdeal(Σ^r) = vanishingIdeal(Σ̄^r)` (as flattened sets)?
    Confirm the radical-insensitive reduction: equal vanishingIdeals ⟹ equal varietyDim, full stop.

(B) The crux: is `vanishingIdeal(canonicalCoord '' Σ^r) = vanishingIdeal(canonicalCoord '' Σ̄^r)`
    provable cheaply? Equivalently `Σ̄^r = repClosure(Σ^r)` as flattened sets, equivalently
    `canonicalCoord '' Σ̄^r ⊆ repClosure(canonicalCoord '' Σ^r)` (the ⊇ direction `Σ^r ⊆ Σ̄^r` is free,
    and `Σ̄^r` is already closed). The subtlety: in general `closure(mult⁻¹ S) ⊆ mult⁻¹(closure S)` with
    equality NOT automatic without flatness/openness of `mult`. So `Σ̄^r = repClosure(Σ^r)` is NOT free
    from the matrix-stratum fact `Mat^{≤r} = closure(Mat^{=r})` alone. Does the H-orbit structure
    (fact 5) or the G2 orbit stratification (fact 4) make it provable? Specifically:
    - Route via G2: `Σ̄^r = ⋃_{corner ≤ r} Ō_M`. Is each `Ō_M` (corner s ≤ r) ⊆ `repClosure(Σ^r)`?
      For corner s = r this is plausible (Ō_M ⊆ closure of the exact-rank-r points it contains). For
      s < r, Ō_M is a SMALLER stratum — is it still in the closure of the rank-EXACTLY-r locus? This is
      the determinantal "smaller strata are in the closure of the top stratum" fact. Provable from the
      engine, or a wall?

(C) ALTERNATIVELY — a DIMENSION SANDWICH that SIDESTEPS the set-closure identity entirely:
    `Σ^r ⊆ Σ̄^r` gives `varietyDim Σ^r ≤ varietyDim Σ̄^r` IF `varietyDim` is monotone (is it? note
    `varietyDim` is the dim of the CLOSURE, so monotone under ⊆ should hold: bigger set ⟹ bigger or
    equal vanishingIdeal-closure ⟹ bigger or equal dim). For `≥`: can we get
    `varietyDim Σ̄^r ≤ varietyDim Σ^r` WITHOUT the set-closure identity? E.g. is `Σ̄^r` IRREDUCIBLE with
    `Σ^r` dense in it, at the level the engine proves — so that `dim Σ̄^r = dim(its top component) =
    dim Σ^r`? But Σ̄^r is a UNION of orbit closures of DIFFERENT dimensions; is its dimension the MAX
    (top stratum) which is exactly the closure of Σ^r? Does fact 6 (codim = MIN over components) plus
    catenary (codim + dim = card, needs PRIME/irreducible) help, or does the catenary bridge REQUIRE
    irreducibility that Σ̄^r lacks in general (multiple top components)?

(D) Rank THREE routes by provability-at-v4.29 + Lean module cost:
    1. Set-closure → free varietyDim (prove Σ̄^r = repClosure Σ^r, then vanishingIdeal equal).
    2. Dimension sandwich (monotone ≤ + a separate ≥).
    3. Orbit-image route (Σ^r = H·F, Σ̄^r = H·F̄, reduce to matrix-stratum closure pushed through sweep).
    Give the cheapest PROVABLE one, the precise reason it is provable (not hand-waved), the biggest
    risk / kill-condition, and a rough Lean lemma count.

(E) Non-vacuity sanity: d = (2,2,2), r = 1. δ = r(d_N + d_0 − r) = 1·(2+2−1) = 3. dim(fibre) should be
    4, dim Σ^r = δ + dim F = 7, dim Σ̄^r should = 7 = card − C where card = 8, C = 1. Does your route
    give 7 = 7 here? Any degenerate-r kill (r=0: Σ^0 = mult⁻¹(0) which is closed already, so
    Σ^0 = Σ̄^0 and hClosure is trivially refl; r = min(d): Σ̄^r = whole space?).

Be concrete and skeptical. If route (B) (preimage density) is a genuine wall needing a Mathlib-absent
theorem, NAME the theorem. If the dimension sandwich (C) is the cheap escape, say WHY the `≥` holds
without the set identity.
