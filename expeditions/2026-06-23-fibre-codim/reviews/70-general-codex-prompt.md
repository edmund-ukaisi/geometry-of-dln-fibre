<task>
You are an independent Lean 4 / Mathlib + math-research reviewer. Audit the SOUNDNESS and NAMING
HONESTY of the final assembly of a central theorem (the geometric codimension of a deep-linear-network
multiplication-map fibre). I give you the EXACT Lean statements; do NOT trust prose, reason from the
statements. Flag inference vs observed-from-statement.

The central theorem (zero sorry, axioms = [propext, Classical.choice, Quot.sound], whole library green):

  theorem codimRepCanonical_fibre_eq_cCodim_add_shift [IsAlgClosed k] [CharZero k]
      (d : Fin (N + 2) → ℕ) (r : ℕ) (h : (kostantPartitions d r).Nonempty)
      (B : Matrix (Fin (d (Fin.last (N + 1)))) (Fin (d 0)) k) (hB : B.rank = r) :
      codimRepCanonical (fibre d B)
        = ((cCodim d r h).toNat : ℕ∞) + ((r * (d (Fin.last (N + 1)) + d 0 - r) : ℕ) : ℕ∞)

It is proved by: rank bounds hp:r≤d(last), hq:r≤d 0 are DERIVED from h via `corner_le_dim_of_mem
h.choose_spec`; hN:(0:Fin(N+2))≠last is proved by Fin.ext_iff/val_last; then rewrite via
`codimRepCanonical_fibre_eq_of_rank_eq` (same-rank ⟹ same fibre codim, needs N≥1) to the normal-form
fibre, then `codimRepCanonical_fibre_normalForm_eq_cCodim_add_shift`.

The normal-form theorem chains:
 (1) hSweep: varietyDim_sweepSigma_eq_shift = sweep_of_localizedChartAlgEquiv fed FOUR inputs:
     e = chartLocalizedAlgEquiv (an AlgEquiv O(Σ)[1/dsig] ≃ₐ O(F)⊗stratum[1/gF]),
     hsig: ringKrullDim(Away chartDsig) = ringKrullDim(sweepSigmaRing)  [source no-drop],
     hP:  ringKrullDim(Away chartGfib) = ringKrullDim(MvPolynomial SchurVar (sweepFibreRing))  [schur no-drop],
     hF:  vanishingIdeal(sweepFibre) ≠ ⊤  [fibre nonempty].
 (2) route-c assembly `codimRepCanonical_fibre_eq_cCodim_add_shift_of_sweep_closure`, which uses an
     IN-REPO PROVED closure bridge hClosure: varietyDim Σ^r = varietyDim Σ̄^r, proved by a codimension
     sandwich: codim Σ^r = codim Σ̄^r = C, where ≤ is anti-monotonicity on Σ^r⊆Σ̄^r and ≥ is ONE
     corner-exactly-r realizer orbit W⊆Σ^r with codim W = C; both loci satisfy an irreducibility-free
     catenary codim Z + varietyDim Z = card, left-cancel finite codim.

Concern A (soundness of the cancellation): the assembly cancels a finite varietyDim from ℕ∞ equations
(ENat.add_right_injective_of_ne_top), and derives dim-F finiteness from hCatFibre: codim F + dim F = card
(card finite). Is there any way card could be ⊤ or the cancellation be vacuous/ill-founded? Is the
catenary `codim Z + varietyDim Z = card` for ANY nonempty subset Z of affine space actually TRUE
(irreducibility-free), or does it secretly need Z irreducible/closed?

Concern B (the sandwich non-vacuity): the ≥ direction needs ONE corner-r orbit in Σ^r with codim = C.
If kostantPartitions d r is nonempty, is a corner-exactly-r realizer GUARANTEED to exist and land in
Σ^r (exact rank = r, not ≤ r)? Could the sandwich be vacuously closing two ⊤ codims?

Concern C (naming honesty): is calling this `codimRepCanonical_fibre_eq_cCodim_add_shift` (a CODIM claim)
honest, given the paper's headline is rlct = ½·codim? The PR keeps rlct=½codim as Cited (Aoyagi). Names
like `rlct_lossDLN_eq_half_cCodim_add_shift_via_aoyagi` carry an explicit `RlctInterface` hypothesis.
Is there any residual overclaim risk in the codim theorem's NAME or STATEMENT?

Concern D: the rank bounds hp,hq are derived from `corner_le_dim_of_mem h.choose_spec`. Is it sound to
use h.choose (an arbitrary chosen element of the nonempty Kostant set) to derive r≤d k at EVERY vertex?
A corner-r Kostant partition m has corner-sum r; does corner_le_dim genuinely force r≤d k for all k, or
only at the corner vertices 0 and last? (The theorem only USES it at last and 0.)
</task>

<output_contract>
Four sections A,B,C,D. For each: VERDICT (sound / suspicious / cannot-tell-from-given), then the single
sharpest reason. If you spot a genuine soundness gap or naming overclaim, give a minimal concrete
scenario. Be terse. Mark every claim as [from-statement] or [inference].
</output_contract>

<grounding_rules>
You have ONLY the statements above, not the full Lean source. Do not invent Mathlib lemma behavior;
if a step's soundness depends on a Mathlib lemma you cannot verify, say so and mark [inference].
</grounding_rules>
