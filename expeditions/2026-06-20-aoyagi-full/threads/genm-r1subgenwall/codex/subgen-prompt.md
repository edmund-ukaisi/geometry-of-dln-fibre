<task>
I am formalising (Lean 4 + Mathlib) a real-log-canonical-threshold finiteness bound for deep linear
networks. I need an independent adjudication of ONE analytic sub-question about a change-of-variables.
Please reason from scratch; do NOT assume my framing is right or wrong.

SETUP (exact objects).
- A chain of widths M = (M_0, M_1, ..., M_N), N >= 3 (so at least 4 widths). Matrices A_0 (M_0 x M_1),
  A_1 (M_1 x M_2), ..., A_{N-1} (M_{N-1} x M_N), each ranging over a bounded box [-T,T]^{entries}.
- prod = A_0 · A_1 · ... · A_{N-1}, an M_0 x M_N matrix. frobSq = squared Frobenius norm.
- TARGET: show J := ∫_{all A_i in box} frobSq(A_0 · A_1 ··· A_{N-1})^{-c'} d(A) < ∞ for every
  real c' < (1/2)·minAdm(M), where minAdm(M) is a known integer given by the "layer-peel" recursion
  minAdm(M_0,...,M_N) = min_{0<=t<=min(M_0,M_1)} [ (M_0 - t)(M_1 - t) + minAdm(t, M_2, ..., M_N) ],
  minAdm(a,b) = a·b.  (This value is proven correct; treat it as given.)

THE PROVEN INDUCTIVE MACHINE (what I already have, sorry-free in Lean).
- Strong induction on the number of widths. The IH gives J' < ∞ (below (1/2)·minAdm) for EVERY chain
  with strictly fewer widths.
- A per-corank "Schur" engine for the TWO-matrix case: ∫∫ frobSq(Δ·S)^{-c'} dΔ dS < ∞ below its
  threshold, Δ square r×r free, S free r×p, by a WellFounded recursion on the corank of Δ (proven ∀r,p).

THE STEP I AM STUCK ON (the front-boundary peel).
- Fix a t×t invertible pivot minor of A_0 (rows ρ, cols κ). Block A_0 = [[A,B],[C,D]], A invertible t×t.
  Split the tail product P := A_1···A_{N-1} (an M_1 x M_N matrix) into its κ-rows Q_p (t rows) and
  the other rows Q_b ((M_1 - t) rows). The banked EXACT Schur identity rewrites the integrand as
  ( ‖A·Q̃_p‖² + ‖C·Q̃_p + Γ·Q_b‖² )^{-c'},  Q̃_p = Q_p + A⁻¹B·Q_b,  Γ = D − C A⁻¹ B free (M_0−t)×(M_1−t),
  after a measure-preserving shear D ↦ Γ.
- Integrating out the free block Γ: because Γ enters only through Γ·Q_b, and Q_b is a MATRIX PRODUCT
  (rows of A_1, times the deeper product A_2···A_{N-1}), the rank s' := rank(Q_b) can DROP below its
  generic value on a proper subvariety of the deeper matrices. Doing the Γ-integral by the Gram change
  Γ ↦ Γ·Q_b produces a Jacobian prefactor det(Q_b Q_bᵀ)^{-(M_0−t)/2} times a residual with exponent
  shifted by (M_0−t)·s'/2, and det(Q_b Q_bᵀ) → 0 as rank(Q_b) drops.

SUB-QUESTION (the ONE thing I need adjudicated).
Is there a route to finish this step — i.e. to prove J < ∞ below (1/2)·minAdm(M) at N>=3 — that stays
inside "concrete/elementary" measure theory: measure-preserving linear changes of variables, pivot
charts, the two-matrix Schur/corank engine above, Fubini, bounded-Jacobian substitutions, and the
strong IH on shorter chains — WITHOUT invoking an abstract "normal-slice / determinantal-locus
isomorphism" that identifies the product-rank-deficient locus {rank(A_1···A_{N-1}) <= q} (bounded-
Jacobian, measure-preserving) with the box of a SHIFTED chain (M_1 − q, M_2 − q, ..., M_N − q)?

Concretely, three candidate routes I want you to evaluate on their merits (accept, repair, or refute
each, with reasons):
 (i)  Cover {rank(product) = q} by pivot charts of the product and Schur-decompose the product itself,
      reducing det(Q_b Q_bᵀ)^{-…} concretely via a Schur complement — no abstract iso.
 (ii) A degree/structure argument: the det(Q_b Q_bᵀ)^{-(M_0−t)/2} prefactor and the residual core
      together form an integrand the shorter-chain IH already covers (i.e. the shifted chain arises
      "for free" from the concrete algebra, not from an abstract reparametrisation).
 (iii) Domination: the rank-deficient strata are higher codimension, so their contribution is dominated
      by the generic threshold and needs no separate charge (finiteness there is IMPLIED).

Also: is det(Q_b Q_bᵀ)^{-(M_0−t)/2} integrated over the deeper matrices a "clean" (elementary) integral,
or does its finiteness genuinely require resolving the determinantal ideal of a matrix PRODUCT (i.e.
computing the RLCT of a product-rank-deficiency locus)? A worked micro-example: M = (3,3,3,4), t=1, so
(M_0−t) = 2, and Q_b = W·A_2 with W a free 2×3 matrix (two rows of A_1) and A_2 a 3×4 matrix. What is
the exact convergence threshold of ∫ det(Q_b Q_bᵀ)^{-1} over that data, and does it sit strictly inside,
at, or outside the budget left by c' < (1/2)·minAdm(3,3,3,4) = 7/2?
</task>

<output_contract>
- A direct verdict on the SUB-QUESTION: is a concrete/elementary route plausible (sketch it), or does
  the step genuinely require the abstract product-rank normal-slice isomorphism (say why each of (i)/(ii)/(iii)
  fails or succeeds).
- For the micro-example: the exact integrability threshold of ∫ det(W A_2 (W A_2)ᵀ)^{-1} and whether it
  is inside / at / outside the c' < 7/2 budget. Show the computation.
- Separate what you can PROVE from what you conjecture. Flag anything you are unsure of.
- Do not write code to a repo; hand-reasoning + (if useful) a short standalone script I will run myself.
</output_contract>

<grounding_rules>
- These are real bounded-box Lebesgue integrals over real matrices; frobSq and det(·(·)ᵀ) are the real
  squared Frobenius norm and Gram determinant. "RLCT" = real log canonical threshold (the sup of c such
  that ∫ f^{-c} < ∞ locally). Integrability near a zero locus is governed by that locus's codimension
  weighted by the vanishing order.
- The two-matrix Schur/corank engine is proven ∀ corank; the OPEN part is composing it across the
  ≥3 layers (the arity recursion), specifically the product-rank-deficient strata of the deeper product.
- Be concrete and exact where you can (this is exact algebra, not heuristics).
</grounding_rules>
