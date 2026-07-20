<task>
Lean 4 / Mathlib v4.29 commutative-algebra formalisation review. I am re-homing a polynomial-ring
catenary library into a clean `Core.Dimension.Catenary` module. I want a decorrelated opinion on ONE crux
and ONE design choice.

CONTEXT — the mathematical content:
For R = MvPolynomial (Fin n) k, k ANY field, and a prime p of R, the catenary equality is
  height p + ringKrullDim (R ⧸ p) = n.
Mathlib v4.29 has only the `≤` half (via `Order.krullDim_eq_iSup_height_add_coheight_of_nonempty` +
`MvPolynomial.ringKrullDim_of_isNoetherianRing`). The `≥` half is proved by induction on n: pick a nonzero
f ∈ p, apply a monic-coordinate-positioning step (a k-algebra automorphism φ making φf monic in X₀ over
k[x₁,…,xₙ] after `finSuccEquiv`), then peel variable 0 via the additive height law on the tower A → A[X]
(`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`, A=k[Fin n] Noetherian/flat hence going-down).

THE CRUX — the `private` Noether-normalization substitution:
The monic-positioning step needs: "for nonzero f : MvPolynomial (Fin (n+1)) k over any field k, there is a
k-algebra automorphism ψ with IsUnit (finSuccEquiv k n (ψ f)).leadingCoeff". Mathlib proves EXACTLY this
inside `Mathlib/RingTheory/NoetherNormalization.lean` via the substitution
  T : Xᵢ ↦ Xᵢ + X₀^(N^i)  (i≠0, X₀↦X₀),  N = 2 + f.totalDegree,
but the whole construction (`T1`, `T`, `T_leadingcoeff_isUnit`, `degreeOf_zero_t`, `sum_r_mul_ne`,
`leadingCoeff_finSuccEquiv_t`, `degreeOf_t_ne_of_ne`) is `private`. I VERIFIED (grep) that NO public Mathlib
v4.29 lemma exposes this consequence: `exists_integral_inj_algHom_of_quotient` (public) gives Noether
normalization of the QUOTIENT directly but does NOT hand back the positioning automorphism / unit-leading-coeff
fact, which the peel-one-variable INDUCTION step needs (the induction needs the automorphism to transfer
height and quotient-dim from p to its image P in (k[Fin n])[X], then peel — the quotient-Noether-normalization
doesn't give the one-variable tower structure).

My current handling: RE-EXPOSE the private machinery in-repo (copy the substitution T1/T/degree-bookkeeping
verbatim from Mathlib, change `private`→ in-namespace, derive the one public consequence
`exists_algEquiv_finSuccEquiv_leadingCoeff_isUnit`). This is over ANY field (the substitution uses X₀-powers,
not generic linear combinations, so finite fields are fine — no Infinite/IsAlgClosed).

QUESTIONS:
1. Is re-exposing the private substitution the right call here, or is there a public route I am missing?
   Consider: (a) deriving the unit-leading-coeff automorphism from `exists_integral_inj_algHom_of_quotient`
   alone (I claim NO — it loses the tower); (b) a totally different proof of the catenary `≥` direction that
   avoids monic positioning entirely (e.g. dimension formula for affine algebras / transcendence-degree route)
   — is any such route cleanly available at v4.29 and would it be SHORTER/cleaner than re-exposing T?
2. Is there a subtlety in "any field" generality I should double-check? The substitution Xᵢ ↦ Xᵢ + X₀^(N^i)
   is char-free and field-size-free as far as I can tell. Confirm or flag.
3. Module-split sanity: I plan `Core.Dimension.Catenary` to hold the monic-positioning machinery + the FULL
   catenary equality + the `≤` half + the additive tower brick (`height_eq_height_under_add_height_map_quotient`,
   which is for A→A[X], A any Noetherian ring, NOT field-specific). I plan to LEAVE the Noether-RANK fact
   `ringKrullDim (R⧸p) = noetherRank` (dim of quotient = #algebraically-independent generators) in a residual
   `PolynomialDimension` module since it is NOT catenary content and is only consumed by a separate
   finite-type-domain module. Is putting the A→A[X] additive tower brick (ring-general, not field-specific)
   inside a module named `Catenary` a naming/altitude smell, or fine as load-bearing infrastructure for the
   field catenary equality?
</task>

<output_contract>
Three numbered sections matching the three questions. For Q1: a clear verdict (re-expose vs public route),
and if you assert a public route exists, name the EXACT v4.29 lemma. For Q2: confirm/flag with the specific
char or field-cardinality concern if any. For Q3: a one-paragraph verdict on the split + naming. Be terse.
</output_contract>

<grounding_rules>
You do NOT have the Mathlib source in front of you; distinguish clearly between (a) lemmas you are CONFIDENT
exist at v4.29 and (b) lemmas you THINK might exist but I must verify by grep. Do not invent lemma names —
if you are guessing a name, say "guess, verify". I have already verified no public
`exists_algEquiv_finSuccEquiv_leadingCoeff_isUnit`-style lemma exists.
</grounding_rules>
