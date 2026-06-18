<task>
We are formalising, in Lean 4 + Mathlib, the invariants (C, θ) from Lehalleur–Rimányi "Geometry of the
fibers of the multiplication map of deep linear networks" (2024). Adjudicate the standard mathematical
route from a single proven quadratic form to (C, θ), and recommend the Lean-feasible target ordering.

PROVEN INPUT (already formalised, honest Lean, sorry-free):
  For a Kostant partition m = (m_{ij})_{0≤i≤j≤N} of a dimension vector d=(d_0,...,d_N)
  (i.e. m_{ij}∈ℕ with d_k = Σ_{i≤k≤j} m_{ij}), the orbit codimension equals the exact integer
      codim(m) = Σ_{1≤i≤u≤j≤v≤N} m_{i-1,j-1} · m_{uv}    (= dim Ext¹(M_m, M_m), Cor 3.5, verbatim).
DEFINITIONS:
  C := min over Kostant partitions m of d with m_{0N}=r of codim(m);   θ := number of minimizers.
GOAL LADDER (paper §§6–7):
  Thm 6.1 (QIP): for d' the weakly-increasing rearrangement of d,
      C = min over e∈ℕ^N, Σe_i=d'_0 of G_d(e) = Σ_{1≤j≤i≤N} e_i(e_j + d'_j − d'_{j-1});  θ = #minimizers.
  Thm 7.10 (explicit): closed form for C via a closest-lattice-point-in-a-simplex computation; θ a binomial.
  Cor 5.10 (permutation invariance): (C,θ) depend only on the multiset {d_0,...,d_N}.

We have established by exact computation:
  - The QIP substitution e ↦ m(e) (with M = Σ e_i(I_{0,i-1}+I_{iN}) + Σ f_j I_{jN}, f_j=d'_j−d'_{j-1})
    gives, for weakly-increasing d', codim(m(e)) = G_d(e) EXACTLY, and m(e) is a valid m_{0N}=0 Kostant
    partition. But the e-image is a STRICT subset of all Kostant partitions (e.g. 3 of 6 for (2,2,2)).
    So Thm 6.1 is NOT a bijection of feasible sets; it is: min over all KP = min over e-image, plus the
    minimizers all lie in the e-image (the paper's horizontal-lace Lemma 6.7).
  - The literal Thm 7.10 θ-formula (with tildeS = S − (m+1)r, m computed on the original sorted d')
    DISAGREES with the direct minimization exactly when m(d') ≠ m((d−r)') — the rank-shift changes which
    simplex prefix is truncated. Reducing to rank 0 on d−r first (recompute m on sorted d−r) agrees with
    direct enumeration in 100% of 400 random cases.
</task>

<output_contract>
1. The standard route to (C,θ) from a quadratic-form orbit-codimension: is "complete the square →
   closest-lattice-point in a coordinate simplex (Conway–Sloane Ch.20)" the canonical argument, or is
   there a more Lean-amenable standard derivation of the explicit formula?
2. For Lean: what is the load-bearing hard step in proving Thm 6.1 faithfully — the substitution identity
   (easy, we have it) or the "every minimizer is a horizontal-lace module / lies in the e-image" direction
   (Lemma 6.7)? How hard is that induction in a finite-combinatorics Lean setting?
3. Thm 7.10: is a from-scratch Lean proof of the closed-form C and the binomial θ whole-in-reach on top of
   the QIP, or its own hard tide? Which Mathlib pieces (lattice-point counting, floor/frac arithmetic,
   Conway–Sloane closest-point) are needed, and what is genuinely absent?
4. Permutation invariance (Cor 5.10): the paper proves it via the Poincaré series (Thm 5.5). Is there an
   INDEPENDENT combinatorial route from the QIP or the explicit formula (both of which already sort d), so
   we can avoid formalising the Poincaré series? Sketch it and name where it could fail.
5. Recommended Lean target ordering (define C,θ → ? → ?), with the single hardest step flagged.
</output_contract>

<grounding_rules>
Distinguish what is a theorem you are certain of from what is your inference. Do not assume Mathlib has
quiver/representation-theory or algebraic-geometry machinery — it does not (no path algebra, no algebraic
groups, no lattice-point enumeration beyond basic Finset). Treat the development as pure ℕ/ℤ finite
combinatorics on Finsets. If you think the literal Thm 7.10 statement is only conditionally correct, say so.
</grounding_rules>
