<task>
You are a Lean-4/Mathlib formalisation + measure-theory second opinion. I am pinning the EXACT shape of
a recursive measure-theoretic cover so a formaliser can build it without re-deriving the geometry. Give
your INDEPENDENT analysis of two specific design choices; attack them, do not rubber-stamp.
</task>

<grounding>
CONTEXT. I must show ∫_U ‖R·S‖²^{−c'} < ∞ for c' < λ_{r,p}, where R ranges over an r×r matrix block
(with one entry pinned = 1, so rank R ≥ 1) over a bounded box {|R_kl| ≤ 1}, S ranges over an r×p free
block, near the determinantal singularity {R·S = 0}. The threshold is
    λ_{r,p} = min( r²/2, min_{1≤j≤r}( jp/2 + λ_{r−j,p} ) ),  λ_{0,p}=0.
I want to RESOLVE the {R singular} locus by a recursive cover and reduce to Euclidean Morse leaves
(∫(∑x_i²)^{−c'} < ∞ ⟺ c' < dim/2, already formalised) plus monomial divisor axes.

The library has a generic "argmax-cell cover" on Fin N → ℝ:
  - argmaxCellOn(active, p) = {y | y_p ≠ 0 ∧ ∀ k ∈ active, |y_k| ≤ |y_p|};
  - {∃ k ∈ active, y_k ≠ 0} = ⋃_{p∈active} argmaxCellOn(active,p)  [via Finset.exists_max_image];
  - the cells are a.e.-disjoint; the complement {∀ active, y_k = 0} is null.
This was designed for COORDINATE pivots (active = a Finset of coordinate indices). I want to reuse it at
a different level: pivots = MINORS of R.

DESIGN CHOICE 1 (the nested minor-pivot cover). Cover the R-space by a NESTED atlas, descending the
"current minor size" k = r, r−1, …, 1:
  - Level k: on {some k×k minor of R has nonzero det}, run the argmax cover with `active` = the Finset
    of all k×k minor-index pairs (I,J), the "coordinate" being the minor determinant det(R[I,J]) (a
    polynomial in R). The argmax pivot (I*,J*) is a minor with MAXIMAL |det| that is nonzero ⟹ that
    k×k minor is INVERTIBLE on its cell. On the cell, the Schur complement Sc = M22 − M21 M11⁻¹ M12
    (M11 = the invertible minor, after a permutation to top-left) is an (r−k)×(r−k) block, and the
    Schur determinant identity det R = det(M11)·det(Sc) holds. Recurse the cover on Sc (size r−k).
  - The complement {all k×k minors = 0} is NOT dropped as null and is NOT asserted to equal {rank<k};
    it is simply the domain of Level k−1 (its own argmax over (k−1)-minors). Termination: the pinned
    entry forces rank ≥ 1, and each level's residual Schur block is STRICTLY smaller, so the descent
    reaches size 1 (R = col·row, terminal Morse) in ≤ r levels.
  - CLAIM: this needs ONLY (a) Finset.exists_max_image over the minor-index Finset, and (b) the Schur
    determinant identity — NOT the heavy theorem "rank R = max size of a nonzero minor" (which is not a
    single Mathlib lemma at this pin).

DESIGN CHOICE 2 (the per-cell split as a COMPARISON, not an equality). On the minor-pivot cell
{det M11 ≠ 0, |R_kl| ≤ 1, M11 the max minor}, det-1 row op L=[[I,0],[−M21 M11⁻¹,I]] and col op
U=[[I,−M11⁻¹M12],[0,I]] give L·R·U = blockdiag(M11, Sc) exactly (verified r=2,3). For the LOSS, I do
a det-1 reparam of S only (S = U·(P;Q), Lebesgue-preserving) and CLAIM a two-sided bounded comparison
    c0·(‖M11·P‖² + ‖Sc·Q‖²)  ≤  ‖R·S‖²  ≤  c1·(‖M11·P‖² + ‖Sc·Q‖²),   0 < c0 ≤ c1 < ∞,
with c0,c1 ABSOLUTE constants on the cell (because the minor-pivot argmax forces the shear coefficients
M21 M11⁻¹ to have modulus ≤ 1). The non-orthogonal row op L is absorbed into the comparison constants
(it does NOT preserve the Frobenius norm). I do NOT claim the clean equality ‖R·S‖² = unit·‖P‖²+‖BQ‖².
</grounding>

<questions>
1. NESTED COVER SOUNDNESS. Is DESIGN CHOICE 1 a valid measure-theoretic cover-up-to-null at each level,
   reusing the generic argmax-cell cover with `active` = minor-index Finset? In particular: is it correct
   that I avoid the "rank = max nonzero minor" theorem entirely by descending one minor-size at a time
   and treating {all k-minors = 0} as the (k−1)-level domain rather than a rank statement? Or is there a
   measure-theoretic gap (e.g. the union of levels not covering {R singular} up to null, or a level's
   complement having positive measure that escapes the descent)?
2. ARGMAX OVER MINORS. The generic argmax cover was proven for coordinate projections (the "coordinate"
   is y ↦ y_p, linear). Here the "coordinate" is R ↦ det(minor(I,J)), a POLYNOMIAL. Does
   Finset.exists_max_image still give the cover (it only needs a finite family of measurable real
   functions and picks the argmax)? Any subtlety in the a.e.-disjointness (the tie set {|det minor_I| =
   |det minor_J|} — is it still null, being a proper algebraic subvariety)?
3. COMPARISON vs EQUALITY. Is DESIGN CHOICE 2 correct that the per-cell split must be a two-sided BOUNDED
   COMPARISON (c0·D ≤ ‖RS‖² ≤ c1·D, D the disjoint form), NOT a raw equality — because the row op L is
   non-orthogonal? And is the threshold of ‖RS‖²^{−c'} genuinely preserved under such a bounded sandwich
   (so the disjoint-sum threshold jp/2 + λ_{r−j,p} transfers)? Are the constants c0,c1 really absolute on
   the minor-pivot cell (shear coeffs ≤ 1), or do they degrade as det M11 → 0 within the cell?
4. THE det M11 → 0 EDGE. Within a minor-pivot cell, det M11 ranges over (0, max]. As det M11 → 0, the
   shear M21 M11⁻¹ can blow up even if the ENTRIES of R are bounded. Does the argmax-over-minors pivot
   condition (|det M11| ≥ |det of every other k-minor|) actually bound M21 M11⁻¹, or is there a
   sub-locus inside the cell where det M11 is small but some (k−1)-minor is large, breaking the c1
   bound? If so, how should the cell be further subdivided?
5. FRAGILITY. Of these, which single step is most likely to be the real formalisation cost, and is there
   a cleaner alternative cover (e.g. a single global blow-up of the ideal of maximal minors) that a
   formaliser should prefer over the nested per-size descent?
</questions>

<output_contract>
For each question 1–5: a direct verdict (CORRECT / INCORRECT / NEEDS-CARE) with the precise reason. Mark
PROVEN vs INFERENCE. If you find a hole, give the smallest (r,p,k) where it bites and the fix. Be
concrete and adversarial. Question 4 is the one I am least sure about — scrutinise it hardest.
</output_contract>
