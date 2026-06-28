# Decorrelated consult — real↔complex variety-dimension transfer for an orbit-closure / determinantal locus

I am scoping a Lean 4 + Mathlib (v4.29) formalisation. I want your INDEPENDENT mathematical
adjudication of a proof route. Do not optimise for what you think I want; tell me what is true and
which route is cleanest. The truth-value of the target is NOT given — judge it.

## Setup (exact algebra)

- `k` a field, char 0. `ι : ℝ →+* K` with `K` algebraically closed, char 0 (e.g. `K = ℂ` or
  `AlgebraicClosure ℝ`). I have ℝ on one side and `K` on the other.
- `Z_M(k) ⊆ k^n` is a determinantal "orbit closure": the Zariski closure of the `GL`-orbit of a
  FIXED integer matrix tuple `M` (entries 0/1; `M` is an "interval direct sum", a block matrix of
  identity/zero blocks). The defining equations are integer (rank-≤ minors), the SAME polynomials
  over ℝ and over K.
- For a Zariski-closed `Z ⊆ k^n`, define `varietyDim_k(Z) := Krull dim (k[x_1..x_n] / I(Z))` where
  `I(Z)` is the **vanishing ideal of the point set** `Z ⊆ k^n` (the real point set over ℝ; the
  K-point set over K). Over ℝ this is the vanishing ideal of REAL points (so it is a "real radical"
  flavoured object — `x²+y²` over ℝ has vanishing ideal `(x,y)`, height 2, not the generator ideal).

## What I have BANKED in Lean (proved, field-generic where stated)

1. Catenary: `height(I(Z)) + varietyDim_k(Z) = n` for any field `k`, any nonempty closed `Z`,
   `n` field-independent. (So codim transfer ⟺ varietyDim transfer.)
2. For the orbit closure `Z_M`, over ANY **infinite char-0** field `k`:
   `varietyDim_k(Z_M) ≤ finrank_k (range δ⁰_M)` where `δ⁰_M : k^a →ₗ[k] k^b` is the orbit
   tangent map (a FIXED integer matrix depending only on the combinatorial M).
   [Route: varietyDim = trdeg of the orbit-pullback image ≤ generic differential rank ≤ finrank range δ⁰,
   the trdeg≤rank step is a char-0 Jacobi–Zariski / formal-smoothness argument, perfect base field.]
3. The REVERSE `finrank_k (range δ⁰_M) ≤ varietyDim_k(Z_M)`, currently stated over alg-closed `k`,
   but its proof's only use of alg-closedness is via: (a) "smooth point ⟹ regular local ring"
   (a theorem whose proof I can see uses only PerfectField, not alg-closedness), and (b) the orbit
   vanishing ideal is prime (orbit irreducible). The orbit closure is smooth at the rational point M
   (generic smoothness of a finite-type domain over a perfect field — Mathlib's
   `dense_smoothLocus_of_perfectField` needs only PerfectField + reduced).
4. So over alg-closed K: `varietyDim_K(Z_M) = finrank_K (range δ⁰_M)` (squeeze, EQUALITY).

## My questions

Q1. `finrank_k (range δ⁰_M)` is the rank of a FIXED integer matrix. Is it correct that this rank is
    the SAME over ℝ and over K (rank of an integer/rational matrix is invariant under field extension
    in char 0)? Any subtlety?

Q2. The reverse inequality (item 3) needs: M is a smooth point of `Z_M(ℝ)` AND the local real
    dimension there equals `varietyDim_ℝ(Z_M)`. Over ℝ, is "smooth point ⟹ regular local ring,
    local Krull dim = relative dim" genuinely PerfectField-only (no alg-closedness, no real-closed,
    no real Nullstellensatz)? The local ring is `(ℝ[x]/I(Z_M))` localized at the maximal ideal at M;
    M is a REAL point. Is the cotangent / Krull-dim machinery field-agnostic here?

Q3. THE TRAP. The orbit closure over ℝ: is `I_ℝ(Z_M)` (vanishing ideal of REAL points) equal to the
    extension/contraction of the generator (minor) ideal, or could the real point set be a
    lower-dimensional "real form" (like `x²+y²`)? Concretely: for a determinantal locus defined by
    integer minors, with M a rational smooth point of the full complex dimension, are the real points
    Zariski-dense in (the relevant top component of) the complex variety? Does the rational smooth
    point M of full local dim FORCE `varietyDim_ℝ = varietyDim_K` for the orbit closure? (Contrast
    `x²+y²`: no smooth real point of dim 1 — the only real point is the singular 0.)

Q4. The FIBRE (the actual target) is not the bare orbit closure but a determinantal "rank-≤r
    multiplication fibre" `mult⁻¹(B)`, whose top components are (orbit closure) × (affine space A^δ),
    δ = r(d_last+d_0−r) ≥ 0, with the affine factor defined over ℚ. Over ℝ, A^δ(ℝ) = ℝ^δ is full
    dimensional. Does the product-with-affine-space preserve the varietyDim transfer (i.e. if
    `varietyDim_ℝ(orbit) = varietyDim_K(orbit)` then the same for `orbit × A^δ`)? Any subtlety with
    the vanishing ideal of a product of real point sets?

Q5. ROUTE CHOICE. Two candidate routes to prove `varietyDim_ℝ(fibre) = varietyDim_K(fibre)`:
    - Route 1 (squeeze via δ⁰): relax the reverse-inequality `IsAlgClosed → PerfectField`, then
      BOTH `varietyDim_ℝ` and `varietyDim_K` equal `finrank(range δ⁰)` (a field-independent integer-
      matrix rank), so they're equal. This reuses the ENTIRE banked orbit-dimension chain over ℝ.
    - Route 2 (ℚ-unirationality / density): the orbit is the image of a ℚ-rational dominant map from
      affine space; ℝ-points of a ℚ-rational affine space are Zariski-dense; conclude real points
      dense ⟹ dims equal.
    Which is the cleaner / lower-risk Lean route at Mathlib v4.29? Is Route 1's "relax IsAlgClosed to
    PerfectField in the reverse inequality" sound (any HIDDEN use of alg-closedness — e.g.
    k-points = closed points of the spectrum, Nullstellensatz residue-field-is-k, the orbit being
    defined by its k-points)? Flag any place the squeeze secretly needs alg-closedness.

Be concrete and skeptical. If Route 1's "PerfectField suffices" is wrong somewhere, name exactly where.
