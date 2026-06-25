# Codex consult — cleanest Lean 4 + Mathlib v4.29 route to a fibre-dimension theorem

You are a Lean 4 / Mathlib v4.29 + commutative-algebra design reviewer. Decorrelated second opinion;
I have NOT told you my own preferred route. Be concrete about Mathlib v4.29 (pin: Lean 4.29.0, Mathlib
v4.29.0, late-2025 / early-2026 era; `RingTheory.KrullDimension.*`, `RingTheory.Ideal.GoingDown`,
`RingTheory.Spectrum.Prime.Chevalley`, `RingTheory.Smooth.StandardSmooth` all present).

## Setup (what we have built)
We work with affine varieties over an algebraically closed field `k` of characteristic 0, encoded as
Zariski-closed subsets `Z ⊆ (σ → k)` for a FINITE index `σ`. We have a landed `varietyDim` /
codimension stack:
- `varietyDim Z := (ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal Z)).unbotD 0` (an `ℕ∞`).
- A catenary bridge that holds *because the ambient ring is a polynomial ring*: for a PRIME
  `p = vanishingIdeal Z`, `Ideal.height p + varietyDim Z = Nat.card σ` (proven via Mathlib's
  `height_add_ringKrullDim_quotient_eq` for `MvPolynomial (Fin n) k`). We do NOT have a general
  catenary-ring theory; the bridge is special to the polynomial ambient.
- We already proved, via this bridge, `dim {m×n matrices of rank ≤ r} = r(n+m−r)` (a single
  irreducible determinantal variety; one catenary use).

## The target (the wall)
We want, in this engine, a dimension/codimension shift for a specific map. Concretely: `mult⁻¹(B) ⊆ V`
(total space `V` an affine variety of matrix-tuples) fibres over the rank-`r` matrix variety
`Mat^{rk=r}` (dimension `r(d_0+d_N−r)`), with the morphism being a Zariski-LOCALLY-trivial fibre
bundle (it is `G_out = GL×GL`-equivariant; `Mat^{rk=r}` is one `G_out`-orbit; local sections of the
submersion `G_out → Mat^{rk=r}` give local trivialisations — but the bundle is NOT globally trivial,
so there is no global `k[X] ≃ k[Y][t...]`). We need:

  `dim(total Σ^r) = dim(base Mat^{rk=r}) + dim(fibre mult⁻¹(B))`

i.e. a `dim(total) = dim(base) + dim(fibre)` theorem for a DOMINANT FINITE-TYPE morphism of affine
varieties that is a Zariski-locally-trivial fibre bundle.

## Questions (answer each concretely for Mathlib v4.29)
1. **Cleanest route.** Of these candidates, which is cleanest to FORMALISE at v4.29, and why do the
   others lose?
   (i) Flatness ⇒ fibre-dimension additivity (ring form: flat finite-type `A→B`, all fibres Krull
       dim `d` ⊢ `ringKrullDim B = ringKrullDim A + d`).
   (ii) Local trivialisation ⇒ cover the base by opens, `f⁻¹U ≃ U × F`, glue (`dim` local on an open
        cover; `dim(U×F)=dim U+dim F`; nonempty-open-of-irreducible has equal dim).
   (iii) Catenary on the three vanishing ideals (total / base / fibre) of `mult⁻¹(B) → Mat^{rk=r}`.
   (iv) A group-orbit route: a new group `G` acting on the TOTAL space whose orbit-image dimension
        the engine's existing trdeg / generic-Jacobian-rank machinery can compute.
2. **The two inequalities.** Mathlib v4.29 has `Module.Flat → Algebra.HasGoingDown` and
   `Ideal.exists_ltSeries_of_hasGoingDown` (lift a prime chain base→total). Does this give the
   `dim total ≥ dim base + dim fibre` LOWER bound cleanly? What carries the UPPER bound
   (`≤`)? Is the upper bound the genuine wall (equidimensionality / no jumping fibres)?
3. **The single hardest missing piece.** Name the one theorem most likely absent from Mathlib v4.29
   that the whole thing rests on. Is it (a) a flat-finite-type fibre-dimension `ringKrullDim`
   equality, (b) upper-semicontinuity of fibre dimension, (c) the affine-variety
   `dim local on an open cover` + `dim(U×F)` package, or (d) something else?
4. **A narrower target?** Do we actually need the full `dim total = dim base + fibre`, or would a
   one-sided codim INEQUALITY (each direction provable by a different cheap lever) suffice if we
   sandwich it with a separately-known value? In our case `dim(total Σ^r)` is *already known*
   (`= card − cCodim`, landed) and `dim(base) = r(d_0+d_N−r)` is *already known* (landed). So the
   ONLY unknown is `dim(fibre)`. Does that change the cleanest route — i.e. can we get
   `dim(fibre) = dim(total) − dim(base)` more cheaply than a general bundle theorem, given two of
   the three dimensions are already pinned?
5. **Module budget + risk.** Rough count of focused Lean modules for the cleanest route at v4.29, and
   where the residual risk concentrates. Be honest if it should be roadmapped rather than built.
