<task>
A bookkeeping / equivalence question between two quadratic-integer-program (QIP) formulations of the
same codimension `C` for type-A quiver / deep-linear-network zero-product loci, plus a real-vs-complex
codimension seam. Adjudicate exactly; flag anything that is NOT a clean identity.

Two formulations of `C(M)` for a width chain `M = (M_0,…,M_L)` (all M_i ≥ 1):

(AOYAGI, layer-peel) `minAdm(M)`: minimise `Mval(M,T)` over admissible rank-profiles `T=(T_0,…,T_{L−1})`
  (weakly-decreasing, `T_0 ≤ min(M_0,M_1)`, etc.), where
  `Mval(M,T) = (M_0−T_0)(M_1−T_0) + Σ_{j≥1}(T_{j−1}−T_j)(M_{j+1}−T_j)`. Equivalently the recursion
  `minAdm(M) = min_{0≤t≤min(M_0,M_1)} [ (M_0−t)(M_1−t) + minAdm(t,M_2,…,M_L) ]`.

(LEHALLEUR–RIMÁNYI, QIP) `qipMin(M) = min_{e} G(M,e)` over `e=(e_1,…,e_L)` nonneg with `Σ e_i = M_0`,
  `G(M,e) = Σ_i Σ_{j≤i} e_i (e_j + M_{j+1} − M_j)`. (This is the paper's quadratic integer program; it
  equals the geometric codimension `cCodim(M,0)` for WEAKLY-INCREASING `M` — a banked theorem.)

Numerics (mine, guide only): `minAdm(M) = qipMin(M)` for ALL weakly-increasing `M` tested (0 mismatches,
L≤4, widths ≤4); they DIFFER for non-monotone `M` (where `qipMin` even goes negative). And `minAdm` is
permutation-invariant (`minAdm(M) = minAdm(sort M)`, 3000/3000).

Answer, exactly:

Q1. Is `minAdm(M) = qipMin(M)` for all WEAKLY-INCREASING `M` a clean combinatorial identity? Give the
    cleanest proof route (e.g. a bijection/substitution between the admissible profiles `T` and the QIP
    variables `e`, matching `Mval` to `G`; or an induction via the layer-peel recursion against a QIP
    recursion). Is there a slick `T ↔ e` correspondence (e.g. `e_i = T_{i−1} − T_i` differences, or the
    reverse)? Prove the identity or pinpoint where it is non-obvious.

Q2. For NON-monotone `M`: `minAdm` is permutation-invariant (empirically). Is the cleanest route to
    `minAdm(M) = cCodim(M,0)` for general `M`: (a) prove `minAdm` perm-invariant directly (a symmetry of
    the layer-peel min), then reduce to the monotone case; or (b) go `minAdm(M) = minAdm(sort M) =
    qipMin(sort M) = cCodim(sort M,0) = cCodim(M,0)` using the banked perm-invariance of `cCodim`? Which
    is the shorter/cleaner ℕ argument? Any circularity risk in (a)?

Q3. THE REAL-vs-COMPLEX SEAM. `cCodim(M,0)` is the codimension of the zero-product / rank locus computed
    over an ALGEBRAICALLY CLOSED field of char 0 (via a quiver-Ext / Voigt argument). The analytic
    integral is over the REAL parameter space. State precisely what must be shown to use `cCodim` as the
    exponent of a REAL Lebesgue tube `vol{ dist to the real determinantal-product variety ≤ t } ~ t^D`:
    is `real codim = complex cCodim` for these determinantal-product varieties, and is it standard
    (same defining minors, irreducible components of equal dimension over ℝ and ℂ in char 0)? Are there
    edge cases (empty real locus, real components of lower dimension) that break `real codim = cCodim`
    for a determinantal / matrix-product variety?

Q4. Is the geometric `cCodim` even NEEDED for the analytic tube, if the tube exponent can be obtained
    ANALYTICALLY as the reduced chain's own box-integral finiteness threshold `minAdm(reduced)` (an
    induction on chain length, via a unit-Jacobian change of variables to the reduced zero-product
    locus)? I.e., is `minAdm` self-sufficient for the finiteness, with `cCodim` only needed to connect to
    the paper's geometric `C`?
</task>

<output_contract>
For each Q1-Q4: a PROVEN/DERIVED statement or a precise "non-obvious, here is the gap". The `T ↔ e`
correspondence if one exists. The cleaner perm-invariance route. A precise statement of the
real-vs-complex codim requirement + whether it is standard + any edge cases. A yes/no on whether the
analytic tube needs `cCodim` or is `minAdm`-self-sufficient.
</output_contract>

<grounding_rules>
Exact combinatorics / algebra. If `minAdm=qipMin` for monotone has a slick bijection, give it; if it
needs induction, give the inductive step. For the real-vs-complex seam, be precise about what theorem is
invoked (determinantal variety codim is field-independent in char 0) and any failure mode. Do not assume
the bridge is needed — assess Q4 honestly.
</grounding_rules>
