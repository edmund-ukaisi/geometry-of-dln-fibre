<task>
You are an independent, decorrelated reviewer of a Lean 4 + Mathlib formalisation. I am auditing
whether a "capstone" theorem faithfully encodes a paper's lemma and whether its proof chain is
genuinely sound and free of hidden citations/axioms. Reason from the mathematics; do NOT trust my
framing — look for the gap I might be missing.

CONTEXT (paper): Lehalleur & Rimányi 2024, "Geometry of the fibers of the multiplication map of
deep linear neural networks". The relevant objects:
- Rep_d = composable matrix tuples for the equioriented type-A_N quiver (representation space).
- For a tuple M, O_M is its G_d = ∏ GL_{d_v} orbit; Ō_M its Zariski closure.
- The orbit closure Ō_M equals the determinantal RANK LOCUS {A | rank(A_{i..j}) ≤ rank(M_{i..j}) ∀ i≤j}
  (paper Thm 3.8, attributed to Abeasis–Del Fra for type A).
- "Voigt's lemma": codim Ō_M (geometric, inside Rep_d) = dim Ext¹(M,M) = c₁ − dim O_M, where
  c₁ = dim C¹ = the ambient deformation-cochain dimension and O_M is smooth so dim O_M = dim(tangent).
- Cor 3.5: codim Ō_M = Σ_{1≤i≤u≤j≤v≤N} m_{i-1,j-1} m_{uv} (a quadratic form in the multiplicities m).

THE LEAN ENCODING (the parts you must judge):

1. codimRep(coord, Z) := Ideal.height (vanishingIdeal (coord '' Z)) in MvPolynomial(RepCoord d) k.
   This is the height of the vanishing ideal of the image of Z under a coordinatisation
   coord : Rep_d ≃ (RepCoord d → k). The headline uses coord = canonicalCoord d, the ENTRY-FLATTENING
   (one polynomial variable per matrix entry, A ↦ (⟨i,r,c⟩ ↦ A_i r c)).
   varietyDim Z := (ringKrullDim (MvPolynomial(RepCoord d) k ⧸ vanishingIdeal (coord '' Z))).unbotD 0.

2. orbitLinearCodim M := finrank C¹ − finrank(range δ⁰), where
   δ⁰ = deformationδ M M : C⁰ → C¹, δ(φ)_i = φ_{i+1} M_i − M_i φ_i (Ringel/Voigt complex),
   C⁰ = ∏_v Mat(d_v × d_v), C¹ = ∏_i Mat(d_{i+1} × d_i). By rank-nullity = finrank(deformationExt1 M M)
   = finrank(C¹ ⧸ range δ⁰).

3. THE CHAIN proving codimRep(canonicalCoord, orbitRankLocus M) = orbitLinearCodim M (char 0, alg.closed):
   - L0 bridge (Nullstellensatz + catenary): for prime vanishingIdeal,
       codimRep + varietyDim Z_M = Nat.card(RepCoord d)      ... (A)
     where Z_M = canonicalCoord '' orbitRankLocus M. Card(RepCoord d) = finrank C¹ = c₁.   [GAP1]
   - SQUEEZE: varietyDim Z_M = finrank(range δ⁰), by le_antisymm of
       (A4, "≤"): varietyDim Z_M ≤ finrank(range δ⁰).  Proof route: the generic Jacobian of the orbit
           parametrisation has rank ≤ finrank(range δ⁰) [via a Kähler/Maurer-Cartan factorisation +
           trace-adjoint deltaT, rank(deltaT)=rank(δ⁰)]; trdeg(orbit image) ≤ genericDifferentialRank
           ≤ finrank(range δ⁰); varietyDim Z_M = ringKrullDim(orbit coordinate ring) [needs Z_M = Ō_M].
           Char 0 used for the differential-independence criterion.
       (A6.1, "≥"): finrank(range δ⁰) ≤ varietyDim Z_M. Proof route: orbit tangent directions δ⁰φ
           inject into the Zariski cotangent space m_M/m_M² at the (k-rational) point M
           [R2★: directional derivative D_{δ⁰φ} kills the orbit ideal to first order, via dual numbers
            P_ε = 1+εφ and orbitPullback M f = 0]; finrank(range δ⁰) ≤ finrank(cotangent);
           and finrank(cotangent) = varietyDim Z_M because M is a SMOOTH point of Ō_M
           [smooth ⟹ regular ⟹ dim cotangent = Krull dim local ring = dim Ō_M].
   - L7 (additive cancellation): from (A) [codimRep + r = c₁, r = finrank(range δ⁰)] and rank-nullity
       [orbitLinearCodim + r = c₁], cancel the finite r to get codimRep = orbitLinearCodim.
   The orbit closure = rank locus identity (Z_M = Ō_M) is PROVED via box-move degeneration
   (Abeasis–Del Fra hard inclusion orbitRankLocus ⊆ Ō_M), NOT cited.

QUESTIONS — answer each independently and adversarially:

Q1 (codimRep fidelity). Is Ideal.height(vanishingIdeal(canonicalCoord '' Z)) the correct encoding of
   the GEOMETRIC codimension of Z in affine Rep_d? Is the entry-flattening canonicalCoord the right
   choice (would a NON-linear set-bijection coord break this)? Is anything lost because codimRep is
   defined for arbitrary coord but only canonical is used?

Q2 (orbitLinearCodim fidelity). Is finrank C¹ − finrank(range δ⁰) = c₁ − dim O_M the paper's
   tangent/Ext codimension? Does this require dim O_M = finrank(range δ⁰) (orbit smoothness /
   surjectivity of the orbit differential onto B¹=range δ⁰)? Where in the chain is that justified, vs
   assumed by the *naming*?

Q3 (chain soundness). Is the squeeze genuinely a squeeze (two independent inequalities meeting), or is
   one side definitionally the other (circular)? In particular: A4 needs varietyDim = ringKrullDim(orbit
   ring), which needs Z_M = Ō_M; A6.1 needs finrank(cotangent) = varietyDim, which needs M SMOOTH and
   Z_M = Ō_M. Are these two uses of "Z_M = Ō_M" and of "the orbit ring" consistent and non-circular?
   Could the squeeze be vacuously true (both sides equal by construction)?

Q4 (smoothness / the AG bridge). The "≥" side rests on "M is a smooth point of Ō_M, so
   dim cotangent = dim local ring". Is that the correct direction (smooth ⟹ cotangent dim = Krull dim)?
   The orbit O_M is a smooth variety (homogeneous space, group orbit) — but M lies in O_M ⊆ Ō_M; is the
   relevant smoothness "M is a smooth point of Ō_M" (true, since M is in the OPEN orbit of its own
   closure) and does the formalisation need exactly this? Any subtlety about Ō_M being singular
   ELSEWHERE that could leak in?

Q5 (hidden citations / over-claim). Given the routes above, is there any step that MUST be an external
   citation (determinantal-ideal height, derived-Ext bridge, Aoyagi/Watanabe RLCT bound) being smuggled
   in as if proved? The claim is "ZERO cited mathematical interfaces in the chain". Is that plausible
   for this specific chain, or does one of A4/A6.1/L0/L6.4 inevitably need a cited theorem?

Q6 (hypotheses). Are [IsAlgClosed k] and [CharZero k] both genuinely necessary, and is the result
   NON-VACUOUS (some concrete M, e.g. dimension vector (2,2,2), satisfies the equation with both sides
   a specific finite number)?
</task>

<output_contract>
For each Q1..Q6: a verdict line (SOUND / SUSPECT / NEEDS-CHECK) + 2-5 sentences of mathematical
reasoning. Then a final PARAGRAPH: the single most likely place this chain is WRONG or OVER-CLAIMS, if
any, and what minimal check would settle it. Be concrete (name the lemma/dimension, give a number).
Distinguish what you can assert mathematically from what you'd need to read the Lean to confirm.
</output_contract>

<grounding_rules>
Reason from algebraic geometry and the deformation-theory facts. Do not assume the Lean is correct
because it compiles — compilation only rules out type errors and sorries, not mis-statements. If a
step seems to require a hard theorem (e.g. that determinantal varieties are normal/Cohen-Macaulay, or
that the orbit closure is reduced/irreducible), say so explicitly and flag it as a likely citation.
</grounding_rules>
