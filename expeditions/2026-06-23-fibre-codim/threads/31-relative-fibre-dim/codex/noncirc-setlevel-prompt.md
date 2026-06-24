# Codex consult — does the SET-LEVEL chart trivialization dodge the R2-3b-4 reducedness circularity?

Lean 4 + Mathlib v4.29. I am building route (c) for the relative-fibre-dimension identity
`hSweep : varietyDim Σ^r = δ + varietyDim F`. Rung 1 = a single-chart trivialization. The DECISIVE
de-risk: is the SET-LEVEL / `varietyDim` version non-circular, given a PRIOR attempt (R2-3b-4) at a
SCHEME-level iso was circular?

## The prior circularity (R2-3b-4), precisely

Earlier the team tried to prove the fibre `F_E` is REDUCED by building a *scheme/ring* product iso
`e : S ≃ₐ[k] R ⊗_k F_E` (S = O(Σ̄^r ∩ pivot chart), R = O(base chart)), then descending reducedness
`S reduced ⟹ R⊗F_E reduced ⟹ F_E reduced`. This was CIRCULAR for reducedness: the forward map of `e`
needs the ideal inclusion `sigmaIdeal ≤ ker(comorphism)`, but only `sigmaIdeal ≤ radical(ker)` is
available — establishing the strict inclusion (= reducedness of the cut) is what `e` was meant to
prove. So `e` as a *ring iso proving reducedness* re-enters its own hypothesis.

Independently known (NOT circular): `deepBaseComap_sigmaIdeal_le` — the base `sigmaIdeal` maps INTO
the deep `sigmaIdeal` (a containment, proved by a point-chase `mult`-image argument), does NOT assume
the circular inclusion.

## My claim: the dimension version dodges it (need you to confirm or break)

For `hSweep` I do NOT need reducedness. `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`
and `vanishingIdeal Z` is ALREADY radical (it's a vanishing ideal). Krull dim is RADICAL-INSENSITIVE:
`ringKrullDim (R⧸I) = ringKrullDim (R⧸√I)`. So `varietyDim` reads only the REDUCED/variety structure;
I never need to know whether the *generator* ideal `fibreGenIdeal` equals its radical. The chart
trivialization I need is a **variety-level (set-level, reduced) isomorphism** `mult⁻¹(U) ∩ Σ^r ≅ U × F`,
not a scheme iso of (possibly non-reduced) coordinate rings.

The set-level pieces LANDED: the sweep `Σ^r = ⋃_P (P•·)''F` (`H = GL×GL` acts, `mult` equivariant,
all rank-r matrices `H`-equivalent); the gauge coordinate-change `AlgEquiv` `nEquiv d P` on the
polynomial ring (transports `multPoly`); the comorphism `multComap`.

## Questions (be adversarial — this is make-or-break)

1. **Is `varietyDim` genuinely radical-insensitive in Mathlib v4.29** — i.e. is `ringKrullDim (R⧸I) =
   ringKrullDim (R⧸ I.radical)` available (or `ringKrullDim` factors through `√`)? Name the lemma if
   so. This is the linchpin: if true, the dimension route NEVER touches the reducedness question.

2. **Does constructing the SET-LEVEL chart bijection `mult⁻¹(U) ∩ Σ^r ≅ U × F` re-enter the
   circularity?** The map is: on the pivot chart `U`, gauge-normalize the target to `E` (algebraic
   row/col ops, the `H`-action), giving `A ∈ mult⁻¹(B) ↦ (B, P_B • A) ∈ U × F` where `P_B` is the
   chart's normalizing gauge. This is a bijection of SETS / a `varietyDim`-preserving map. Does
   proving it require the radical inclusion (`sigmaIdeal ≤ ker`), or only: (i) the sweep set-identity
   (LANDED, non-circular), (ii) the gauge being an algebraic iso on the chart open (LANDED `nEquiv`),
   (iii) `mult ∘ gauge = const E` on the fibre (LANDED `nSub_mult`)? My read: it needs only set-level
   + gauge-algebraic facts, all radical-insensitive — but tell me if the dimension-additivity
   `varietyDim(U×F) = varietyDim U + varietyDim F` secretly needs flatness/reducedness.

3. **The product-dimension step `varietyDim(U × F) = varietyDim U + varietyDim F`.** For a product of
   affine varieties over an alg-closed field, `dim(X × Y) = dim X + dim Y`. Is this in Mathlib v4.29
   (as `ringKrullDim (A ⊗_k B) = ringKrullDim A + ringKrullDim B`, or a variety-dimension product)?
   If absent, is it provable WITHOUT the relative-Noether/`proof_wanted` machinery — e.g. via `trdeg`
   of the tensor product (trdeg IS additive for the tensor of two domains over a field) PLUS the
   reducible-case max-over-components bookkeeping? Note `F` is REDUCIBLE (comps 10,9,9 on (3,3,3)r1) —
   does the product-dim survive reducibility radical-insensitively (take max component on each side)?

4. **The glue over the finite pivot cover.** `varietyDim(⋃_i Z_i) = max_i varietyDim(Z_i)` for a
   finite cover — is that radical-insensitive and in Mathlib (or trivial from `ringKrullDim` of a
   product/finite-union of irreducibles)?

5. **Net verdict:** does the SET-LEVEL/`varietyDim` route (c) dodge the R2-3b-4 circularity? If YES,
   give the rung decomposition (single-chart triv → per-chart dim-additivity → glue) and which steps
   are Mathlib-present vs new. If NO (the set-level chart iso ALSO needs the radical inclusion or some
   reducedness), say so plainly — that triggers a fallback to citing `hSweep`.

The key thing I need from you: a clean YES/NO on whether radical-insensitivity of `varietyDim` lets
the chart trivialization avoid the `sigmaIdeal ≤ ker` inclusion that made the scheme iso circular.
