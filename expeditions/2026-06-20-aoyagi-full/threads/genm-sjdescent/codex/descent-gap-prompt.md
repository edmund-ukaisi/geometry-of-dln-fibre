<task>
I am formalising (in Lean/Mathlib, but this question is PURE MATH) the finiteness of a
matrix-loss box integral arising in Aoyagi's RLCT computation for deep linear networks. I have
a pinned design for a "peel step" and I want an independent check on whether the pinned descent
actually closes, or whether it has a genuine hole on a specific locus.

SETUP (one pivot chart of one boundary peel).
- Widths: a chain M = (M0, M1, ..., ML). Fix a pivot rank t with 1 ≤ t ≤ min(M0,M1). Set
  a := M0 − t (extra output rows), b := M1 − t (extra input cols), pq := a·b (the block codim).
- The front factor A0 is an M0×M1 matrix whose t×t (ρ,κ)-pivot minor is invertible. Block it as
  A0 = [[A, B],[C, D]] with A : t×t invertible, B : t×b, C : a×t, D : a×b.
- A' is a "tail" parameter; the tail product P := prod(tailChain M)(A') is an M1×n matrix, where
  n is the "deeper width" reachable through the remaining layers. Split P by its M1 rows into the
  pivot rows Q_p (t×n) and the non-pivot rows Q_b (b×n).
- Loss integrand (exact, Schur block split, VERIFIED in Lean as `frobSq_schur_block_split`):
      frobSq(A0 · P) = frobSq(A · Q̃) + frobSq(C · Q̃ + Γ · Q_b),
  where Q̃ := Q_p + A⁻¹ B Q_b and Γ := D − C A⁻¹ B (the Schur complement, an a×b matrix).
- A measure-preserving shear D ↦ Γ (VERIFIED) makes Γ a free integration variable over an a×b box.
- Goal of ONE peel step: show the inner Γ-integral (A, B, C, A' held; then integrated over the
  chart) descends the exponent so that finiteness reduces to a STRICTLY SHORTER chain
  (redChain t M) at a shifted exponent c' − pq/2, feeding a strong induction hypothesis.

THE TWO BANKED "isotropic" bricks I am told to descend to (both VERIFIED in Lean):
  (Regime A, exponent shift) matBox_corank_residual_absZ_le: for p,q ≥ 1, c' > pq/2, and a
      STRICTLY POSITIVE core W(z) > 0,
        ∫_z ∫_{Δ ∈ box(p×q)} (frobSq(Δ) + W(z))^{−c'} dΔ dz ≤ Cresid(pq,c') · ∫_z W(z)^{−(c'−pq/2)} dz.
  (Regime B, terminal) matBox_corank_dominates_absZ_lt_top: for c' < pq/2 and W(z) ≥ 0, finite outer
      measure, the same double integral is finite.
  NOTE both bricks are ISOTROPIC: the block Δ enters ONLY through its own frobSq(Δ), UNCOUPLED to W.

THE PINNED DESCENT (what I am asked to build): use the PURE spherical blow-up
  lintegral_eq_polar (VERIFIED): ∫ h = ∫_{ω ∈ sphere} ∫_{r>0} r^{N−1} h(r·ω) dr dω  (N = pq),
  to blow up Γ = r·ω, and thereby descend the ANISOTROPIC inner integral
      ∫_{Γ ∈ box} ( frobSq(A·Q̃) + frobSq(C·Q̃ + Γ·Q_b) )^{−c'} dΓ
  to the isotropic brick matBox_corank_residual_absZ_le at the shifted exponent c' − pq/2.
  I am explicitly told NOT to form the Gram determinant det(Q_b Q_bᵀ) / NOT to integrate Γ out over
  full space (that is a KNOWN-DEAD "atom route" that diverges on rank-deficient Q_b).

MY CONCERN (the thing I want checked). The anisotropic term is frobSq(C·Q̃ + Γ·Q_b), where the
free block Γ (a×b) enters through the linear map Γ ↦ Γ·Q_b (Q_b is b×n). This is the ISOTROPIC
shape frobSq(Δ) + W ONLY IF the map Γ ↦ Γ·Q_b is (up to translation) an isometry-after-scaling of
the block — i.e. essentially only when Q_b has FULL ROW RANK b (b ≤ rank Q_b ≤ n), in which case
Δ := Γ·Q_b is a change of variables with Jacobian a power of det(Q_b Q_bᵀ)^{1/2} — but that IS the
forbidden Gram route. On the bottleneck charts where b = M1 − t exceeds the deeper reachable width
(so Q_b is RANK-DEFICIENT, row rank < b), the spherical blow-up Γ = r·ω has a nonempty locus of
sphere directions ω with ω·Q_b = 0; along those directions frobSq(C·Q̃ + r·ω·Q_b) does NOT grow with
r, so the radial integral ∫ r^{pq−1} (bounded)^{−c'} dr DIVERGES at r → ∞. Hence integrating over
the FULL sphere does not give the r^{−2c'} decay needed to land the pq/2 shift; the {ω·Q_b = 0}
directions seem to force a FURTHER blow-up / a deeper interleaved recursion, which no single banked
brick supplies. The design calls this "the irreducible pivot/corank interleaving (rank-deficient Q_b)"
and asserts it is "bounded, not a wall".

QUESTIONS.
1. Is my concern correct — that the pinned "pure spherical blow-up → matBox_corank_residual_absZ_le"
   descent does NOT close as a SINGLE peel step on the rank-deficient-Q_b locus, and genuinely
   requires an interleaved deeper recursion (splitting the sphere by ω·Q_b = 0)? Or is there a
   standard way the spherical blow-up + the two isotropic bricks compose to handle rank-deficient
   Q_b that I am missing?
2. If the interleaving is genuinely required: is the {ω·Q_b = 0} sub-locus itself a clean lower-
   dimensional matrix-box of the SAME shape (so the recursion is well-founded and bounded), or does
   it re-introduce a coupled/Gram-like object? Concretely: after restricting to ω with ω·Q_b = 0,
   what is the residual integral, and does it match "a shorter chain at a shifted exponent"?
3. Given all this, what is the SMALLEST genuinely-new, self-contained lemma that (a) makes real
   forward progress on this peel step, (b) composes the banked pieces above, and (c) is provable in
   isolation (exposing the Q_b-rank / core-positivity as hypotheses if needed) rather than requiring
   the whole recursion? I already have banked, with EXPOSED hypotheses: a "freed inner Γ-integral is
   finite given (0 < frobSq(A·Q̃) core positivity), (Q_b Q_bᵀ positive definite), (c' > ab/2)"
   lemma, and its bounded-branch companion (core positivity alone, any c' ≥ 0, finite domain). So
   the exposed-hypothesis inner lemma already exists — what remains is the OUTER measure statement
   that SUPPLIES those hypotheses a.e., which is where the rank-deficient locus bites.
</task>

<output_contract>
Four short sections, in this order:
  1. VERDICT on Q1 — one of {concern-correct / concern-wrong / partially}, then ≤6 sentences of why.
  2. Q2 — the residual on {ω·Q_b = 0}: what it is, whether it is a clean shorter-chain box, ≤6 sentences.
  3. Q3 — the smallest genuinely-new bankable lemma (name a precise statement), ≤6 sentences.
  4. One-paragraph BOTTOM LINE: is the pinned single-step descent sound as stated, or does the
     decomposition "peel_step (isolated) → recursion → close" need revising, and if so how.
Be terse and technical. No pleasantries.
</output_contract>

<grounding_rules>
This is a math-soundness question, not a literature lookup. Reason from the integral structure.
Explicitly flag any step that is an ASSUMPTION about my setup vs a MATHEMATICAL DEDUCTION. If a
claim depends on a fact about DLN products (e.g. the rank of Q_b as a function of the widths) that I
have not given you, say so and state the fact you are assuming. Do not invent Lean lemma names.
</grounding_rules>
