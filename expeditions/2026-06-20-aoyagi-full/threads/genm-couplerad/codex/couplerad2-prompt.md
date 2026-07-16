<task>
Determine the exact dependence on A of a matrix integral, and whether it makes a two-integral bound CLEAN
(uniform constant) or COUPLED. Reason from scratch with exact real-analysis; do not assume my framing.
</task>

<grounding_facts>
Fix integers b ≥ 1, a ≥ 1, and dimensions M₂ ≥ b, n ≥ 1. Let:
- A be a b×M₂ real matrix (full row rank b) — integrated over the box [−1,1]^{b×M₂}.
- S be an M₂×n real matrix — integrated over the box [−1,1]^{M₂×n}.
- The integrand is det((A·S)(A·S)ᵀ)^{−a/2}, where A·S is b×n and (A·S)(A·S)ᵀ is its b×b Gram matrix.

We want ∫∫_box det((A·S)(A·S)ᵀ)^{−a/2} dA dS < ∞, and the sharp threshold on (a,b,M₂,n).

Facts I have established (you may use or challenge):
- det((A·S)(A·S)ᵀ) = det(A (SSᵀ) Aᵀ).
- The det-monotone "drop columns of S to b" over-bounds and diverges (do not use it).
- Cauchy–Binet is unavailable in the target formal system (cannot expand det((AS)(AS)ᵀ) = Σ_K det(A S_{:,K})²).
</grounding_facts>

<questions>
1. Compute the exact dependence on A of the INNER integral I(A) := ∫_{S ∈ box} det((A·S)(A·S)ᵀ)^{−a/2} dS.
   Specifically: is I(A) = C · det(A·Aᵀ)^{−a/2} for a constant C that is UNIFORM (bounded) over all
   full-row-rank A in the box, OR does I(A) depend on A in a more coupled way (e.g. through A's full
   singular spectrum / condition number, not just det(A·Aᵀ))? Derive the A-dependence exactly. Consider the
   factorization A = R·Q with R a b×b invertible matrix and Q a b×M₂ matrix with orthonormal rows (QQᵀ = I_b).
2. If I(A) = C·det(A·Aᵀ)^{−a/2} with C uniform: (i) for which (a,b,n) is C finite? (ii) is the constant
   C = ∫_S det((Q·S)(Q·S)ᵀ)^{−a/2} dS genuinely bounded UNIFORMLY over all orthonormal-row Q (b×M₂)? Give
   the reason (compactness? a density bound on the projections Q·s_j?).
3. Then the OUTER integral ∫_{A ∈ box} det(A·Aᵀ)^{−a/2} dA: for which (a,b,M₂) is it finite?
4. Combine: the sharp threshold for ∫∫_box det((A·S)(A·S)ᵀ)^{−a/2} < ∞. Is it a+b ≤ min(M₂,n)? And crucially:
   is the whole thing a CLEAN two-step (uniform inner bound × finite outer), or is there an unavoidable
   COUPLING between the A- and S-integrals that forces a recursion? If clean, say so explicitly.
</questions>

<output_contract>
- The exact A-dependence of I(A) (derive it via A=R·Q), and whether it is exactly det(A·Aᵀ)^{−a/2} × (uniform C).
- Whether C is uniformly bounded over orthonormal-row Q, with the reason.
- The finiteness threshold for each of the inner (over S) and outer (over A) integrals, and the combined
  sharp threshold.
- A crisp verdict: CLEAN two-step (uniform inner × finite outer) vs COUPLED (needs a recursion). If clean,
  this is the key point.
- Distinguish PROVED-by-your-reasoning from CONJECTURED. Concrete worked case: b=2, a=1, M₂=n=4.
- Reason purely from the facts here; do NOT read or grep any files.
</output_contract>
