# Route consult — varietyDim of the rank-≤r matrix variety, Lean 4 + Mathlib v4.29

## Setting (concrete, decorrelated — give me your independent route + the single hardest piece)

I want to prove ONE theorem in Lean 4 (Mathlib v4.29 pin, char 0 / alg-closed field `k` available):

    dim Mat^{rk ≤ r}_{m × n}  =  r·(m + n − r)

i.e. the Krull dimension (transcendence degree) of the affine variety of `m × n` matrices of rank ≤ r.
Witness: `m=n=2, r=1 → 1·(2+2−1) = 3`.

In my engine the dimension is encoded as
    varietyDim Z := (ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal k Z)).unbotD 0
for `Z : Set (σ → k)`, σ finite (here σ = m·n matrix entries). I have LANDED, network-free:

- `varietyDim Z = ringKrullDim (MvPolynomial σ ⧸ vanishingIdeal Z)`, and a catenary bridge
  `height (vanishingIdeal Z) + varietyDim Z = card σ` for IRREDUCIBLE Z (prime vanishing ideal).
- `vanishingIdeal (range of a polynomial map φ) = ker(φ*)` PATTERN already proved for one map
  (a localization image): so for a genuine polynomial parametrisation φ (no denominators),
  `vanishingIdeal (image φ) = ker φ*` and `MvPolynomial σ ⧸ ker φ* ≅ range φ*` (a subalgebra of a
  polynomial domain `MvPolynomial τ k`).
- `ringKrullDim (R ⧸ p) = trdeg_k (R ⧸ p)` for any prime p of a f.g. polynomial ring over a field
  (`ringKrullDim_quotient_unbotD_eq_trdeg_toNat`), via Noether normalization
  (`trdeg_eq_of_integral_injective`: an integral injective `k[Fin s] ↪ B` domain forces trdeg = s).
- `affine_domain_height_add_ringKrullDim_quotient_eq`: full equidimensionality for any prime of any
  f.g. domain over a field.
- The char-0 differential criterion `trdeg ≤ generic Jacobian rank`
  (`trdeg_adjoin_le_genericDifferentialRank`, via Kähler differentials + formal smoothness of perfect
  fields), GENERAL in a finite family `f : ι → B` (domain B). This gives an UPPER bound on trdeg only.
- Lots of rank-locus support: `rank_le_iff_forall_submatrix_det_eq_zero` (rank ≤ r ⟺ all (r+1)-minors
  vanish), the rank-≤r locus is Zariski-closed.

So I can reduce `varietyDim (image φ)` to `trdeg_k (range φ*)` where `φ : (u,v) ↦ u·v`,
`u : Mat_{m×r}`, `v : Mat_{r×n}`, and `range φ* = k[ entries of u·v ] ⊆ k[u_entries, v_entries]`.
The remaining crux is the EXACT transcendence degree `trdeg_k k(entries of u·v) = r(m+n−r)`.

## Questions (be concrete and Mathlib-v4.29-specific)

1. **Route.** Of these, which gives the SHORTEST honest Lean proof of the exact trdeg `= r(m+n−r)`?
   (a) Direct parametrisation φ:(u,v)↦u·v, compute `trdeg k(image)` — needs BOTH an upper bound
       (Jacobian / the landed criterion) AND a matching lower bound (a transcendence basis of size
       r(m+n−r), or the generic-rank Jacobian being full so trdeg = rank). What's the cleanest lower
       bound — exhibiting an explicit r(m+n−r)-element algebraically-independent subfamily of the
       u·v entries, or computing the generic Jacobian rank both ways?
   (b) Orbit route: Mat^{rk=r} is one GL_m × GL_n orbit (of the block E_r); dim orbit = dim group −
       dim stabiliser = (m²+n²) − (m² + n² − r(m+n−r)) ... requires a stabiliser-dimension count.
   (c) Some other commutative-algebra route I'm missing (e.g. a known Mathlib determinantal-ring
       dimension, or a clean transcendence-basis-by-block argument).

2. **The lower bound is the crux.** For route (a): is there a clean explicit transcendence basis of
   `k(u·v entries)` of size r(m+n−r)? (Standard pen-and-paper: fix the top-left r×r block of u·v to be
   invertible; the r·r + r(n−r) + (m−r)·r "free" entries in the first r rows/cols form a basis, the
   rest are determined rationally.) How painful is that "the rest are determined" step in Lean v4.29 —
   does it need explicit rational formulas (the Schur-complement / `(M_remaining) = M_{21} M_{11}⁻¹ M_{12}`),
   or can it ride on a Jacobian-rank = r(m+n−r) computation at a generic point?

3. **Single hardest Lean piece** and a **module budget** (line-count, not wall-clock). Is this 1 focused
   module (~300 LoC) or a 3–5 module mini-build? Is the EXACT trdeg realistically reachable at v4.29, or
   only the `≤` half (so I'd have to settle for `dim ≤ r(m+n−r)` and cite the lower bound)?

Do NOT just agree with a framing — give your own decorrelated verdict on the cleanest route and whether
the exact equality is reachable.
