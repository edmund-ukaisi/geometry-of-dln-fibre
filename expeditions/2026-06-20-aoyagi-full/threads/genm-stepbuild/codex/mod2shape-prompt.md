<task>
Lean 4 + Mathlib (v4.29) formalisation planning. I am formalising the "D–H covariance
primitive" (module ii) of a change-of-variables finiteness argument for a family of
matrix integrals. I need your independent read on the CLEANEST, MOST TRACTABLE Lean
statement shape and on where the realistic single-thread boundary lies.

OBJECTS (all real matrices):
- P : u×u (invertible pivot), D : b×b (invertible), U, B : u×b free variables.
- The "front map" is L(U,B) = P·U + B·D  (a u×b matrix).
- Vectorising columns: vec(L) = (I_b ⊗ P)·vec(U) + (Dᵀ ⊗ I_u)·vec(B), so the covariance
  (Gram of the linear map (U,B) ↦ vec(L) with U,B iid standard) is
      Σ := (I_b ⊗ P)(I_b ⊗ P)ᵀ + (Dᵀ ⊗ I_u)(Dᵀ ⊗ I_u)ᵀ  =  I_b ⊗ (P Pᵀ) + (Dᵀ D) ⊗ I_u.
- KEY FACT I noticed: the two summands  A := I_b ⊗ (PPᵀ)  and  C := (DᵀD) ⊗ I_u  COMMUTE
  (both products equal (DᵀD) ⊗ (PPᵀ)). So Σ is a Kronecker SUM of two commuting PSD matrices.
  Its eigenvalues are {pᵢ² + σⱼ² : i∈[u], j∈[b]} with pᵢ = singular values of P, σⱼ = sing.
  values of D; det Σ = ∏_{i,j}(pᵢ²+σⱼ²).

WHY I need it (downstream, NOT to be built now): a pushforward-density bound
  ∫_{U,B} (‖P U + B D‖²_F + τ²)^{−q} dU dB  ≲  τ^{ub−2q} · (det Σ)^{−1/2}   (for 2q > ub),
and a box-cutoff variant for 2q ≤ ub, feeding a per-stratum exponent gate. The scalar
(det Σ)^{−1/2} = ∏(pᵢ²+σⱼ²)^{−1/2} is the honest joint weight.

Mathlib API I have confirmed at v4.29: Matrix.mul_kronecker_mul (mixed product
(A*B)⊗ₖ(A'*B') = (A⊗ₖA')*(B⊗ₖB')), kroneckerMap_transpose ((A⊗ₖB)ᵀ = Aᵀ⊗ₖBᵀ),
one_kronecker_one, det_kronecker (det(A⊗ₖB) = detA^card·detB^card),
Matrix.PosSemidef / PosDef, IsHermitian.eigenvalues, spectral theorem for Hermitian.
I do NOT know a Mathlib "vec" operator or a vec(AXB) = (Bᵀ⊗A)vec X lemma (I could not find one).

CONSTRAINTS: zero sorry/axiom; honest bedrock statements (no vacuous/overclaiming names);
each result must be a green Lean build. I want to bank ONE self-contained green module now.
</task>

<output_contract>
Four sections, terse:
1. STATEMENT SHAPE. The 1–3 Lean lemma statements you'd bank as module (ii)(a), in order,
   with the exact mathematical content (not Lean syntax necessarily). For each: is it
   self-contained and clearly true? Rank by value×tractability.
2. DET ROUTE. Is det Σ = ∏(pᵢ²+σⱼ²) worth proving now, or should the bankable primitive
   stop at (a) the covariance identity and (b) PosSemidef, deferring the eigenvalue/∏ form?
   If worth it: the cleanest Mathlib route (simultaneous diagonalisation of the two commuting
   PSD Kronecker factors vs. something simpler). If a vec(AXB)=(Bᵀ⊗A)vecX bridge is needed to
   make the covariance identity NON-vacuous (i.e. tie Σ to the actual map L=PU+BD), say so and
   give the cleanest way to establish that bridge (or argue it's not needed).
3. VACUITY CHECK. Is a bare Kronecker identity "(I⊗P)(I⊗P)ᵀ + (Dᵀ⊗I)(Dᵀ⊗I)ᵀ = I⊗PPᵀ + DᵀD⊗I"
   an honest bedrock primitive, or does it need the vec-connection to L to be non-vacuous?
4. PITFALLS. Top 2–3 Lean/Mathlib traps for this specific build at v4.29 (Kronecker index
   Prod types, transpose of kronecker, PosSemidef of a Kronecker product/sum, det powers).
</output_contract>

<grounding_rules>
Flag any Mathlib lemma name you are UNSURE exists at v4.29 as [UNVERIFIED] — I will grep for
it before use. Distinguish mathematical fact from Lean-tractability inference. Do not assume
API beyond what I listed without flagging it.
</grounding_rules>
