<task>
Resolution-of-singularities / RLCT question about the DEEPER rank strata of a product block in an
Aoyagi-style DLN (deep linear network) real-log-canonical-threshold computation.

SETUP. Real matrices. A chain of widths M=(M₀,M₁,…,M_L). One "peel" at pivot cut t fixes a=M₀−t,
b=M₁−t, q=M_last. After a change of variables the per-chart loss is
   freed = ‖B₀‖²_F + ‖C′·B₀ + Γ·Q_b‖²_F,
where B₀ (t×q) is the reduced-chain product, Γ (a×b) is a free bounded-box block, C′ is bounded, and
Q_b (b×q) is the CORANK TAIL BLOCK. Crucially Q_b is itself a PRODUCT of the remaining layers:
   Q_b = Y · A₂ · A₃ ··· A_L,   Y (b×M₂) = corank rows of A₁,  A_i (M_{i-1}×M_i).
We integrate ∫ freed^{−c′} over all these matrices in the box [−1,1]^·. The known result (cited Aoyagi;
Monte-Carlo confirmed): the whole integral is finite exactly for c′ < ½·minAdm(M), where minAdm is the
zero-product-locus codimension, minAdm(M)=min_t[(M₀−t)(M₁−t)+minAdm(t,M₂,…)].

WHAT IS ALREADY UNDERSTOOD (do not re-derive):
- On {rank Q_b = b} (full row rank) the loss factors cleanly; reduced to a shorter-chain problem.
- On the TOP corank stratum {rank Q_b = b−1} (drop by one): near a rank-(b−1) point det/one singular
  value gives a single smooth coordinate z, the collapsing Γ-direction stays bounded (box), and the
  residual is a small bilinear model (a,1,D), D=q−b+1, with a clean Morse/zeta threshold. This CLOSES,
  even though Q_b is a product, because only ONE singular value vanishes.

THE OPEN PROBLEM — the DEEPER strata {rank Q_b ≤ b−2} for b≥2 (≥2 singular values of Q_b vanish):
Since Q_b = Y·A₂··· is a PRODUCT, {rank Q_b ≤ r} is a determinantal variety of a product, and (observed)
Y, A₂ can BOTH be full rank while Q_b drops rank (an interaction, not one factor collapsing). The single-z
coordinate CoV fails; multiple vanishing minors interact.

CONCRETE SMALLEST CASE to work: M=(2,3,2,2), pivot cut t=1 ⇒ a=1, b=2, q=2. Then Y is 2×2, A₂ is 2×2,
Q_b = Y·A₂ is a 2×2 product; the deepest stratum is {Q_b = 0} (rank 0). ½·minAdm(M) is a specific number
(compute it from the recursion). B₀ is the (1,2,2)-reduced product (t=1).

QUESTIONS (genuinely open — do NOT assume it works or that it walls; do NOT use any "codim ≥ minAdm ⇒
done" reasoning — a codim bound does NOT give RLCT=½codim, e.g. x⁴+y⁶ has codim 2 but RLCT 5/12):
(Q1) Resolve the deepest stratum {Q_b = Y·A₂ = 0} for M=(2,3,2,2), t=1, END TO END: give an explicit
     (nested) blow-up / monomialization of freed near {Q_b=0}, the per-divisor Jacobian weights and loss
     orders, and READ OFF the local RLCT. Is the local RLCT of the corner = ½·(its codimension)
     (normal-crossing / "as mild as its codim"), and is it ≥ ½·minAdm(M) (so the corner does not bind
     below the global threshold)? Show the exponent arithmetic.
(Q2) The product structure: does {rank(Y·A₂) ≤ r} resolve by a NESTED blow-up along the product's rank
     flag (rank b → b−1 → … → 0), and does the PRODUCT rank rank(Q_b) serve as a well-founded descent
     valuation (strictly decreasing along the flag), even though the FACTOR ranks rank(Y), rank(A₂) do
     not? Or is there a genuine obstruction to a well-founded descent here? Prove or refute.
(Q3) If this deeper-strata resolution genuinely requires the full Aoyagi §5 product-rank-flag machinery
     (no elementary closed form), say so explicitly and characterize precisely what must be imported.
</task>

<output_contract>
Answer Q1 (the explicit resolution + RLCT arithmetic for (2,3,2,2)), Q2 (the descent valuation:
prove/refute rank(Q_b) works), Q3 (wall-or-not) in order. Give exact exponent arithmetic where possible.
Separate exact from heuristic. Under ~600 words. Do not pad; do not hedge into vagueness.
</output_contract>

<grounding_rules>
Real Frobenius norm. minAdm is the integer recursion above (black box with that recursion). RLCT of f at 0
= the negative of the largest pole of ∫_{box} f^{−s} ds (equivalently sup{s : ∫ f^{−s} < ∞} for a single
monomial, ½·codim for a normal-crossing of that codim). Box = product of [−1,1]. Pen-and-paper math.
