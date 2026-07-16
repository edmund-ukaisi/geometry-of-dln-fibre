<task>
You are a decorrelated second opinion on a real-analysis / RLCT (real log-canonical threshold)
design problem. Argue whichever direction the mathematics supports; my own conclusion is WITHHELD.
No repo access needed — this is self-contained. Be exact; flag inference vs. fact.

## The object (self-contained)

Fix integers u ≥ 1, a ≥ 0, b ≥ 1, and n ≥ u+b. Write p = u+a, r = u+b.

- Q_p is a fixed real u×n matrix (a "pivot" block). Treat it as generic of rank u (u ≤ n).
- Z is a fixed real matrix of shape (n₀ × n), with n₀ ≥ n, of rank ≥ b ("deep factor"),
  and it carries a Loewner FLOOR: there is an orthonormal m-frame U (m ≥ a+b) with
  Z Zᵀ ⪰ ε'²·U Uᵀ (ε' > 0 fixed). [In words: Z has an m-dimensional "strong" column subspace on
  which its singular values are ≥ ε'. This is the ONLY quantitative control on Z; the object does NOT
  restrict the stacked matrix below.]
- A_cor ranges over the unit box in real b×n₀ matrices. Set Q_b := A_cor · Z (shape b×n).
- hsQ := [ Q_p ; Q_b ] is the stacked r×n matrix (u pivot rows on top, b corank rows below).
- B ranges over the unit box in real p×r matrices.

The integral to bound (extended-nonnegative, c' > 0):

    I(c') := ∫_{A_cor box} ∫_{B box} ‖B · hsQ‖_F^{−2c'} dB dA_cor .

(‖·‖_F = Frobenius; the exponent is −2c' so a "codimension κ" divergence means finiteness iff c' < κ/2.)

GOAL: show I(c') is finite, and more sharply produce a domination of the form

    I(c') ≤ C · ∫_{z-box} ( commonDivisor(z)² · ‖Q_p(z)‖_F² )^{−(c' − ab/2)} dz      (D)

with C < ⊤, for all c' in the range 2c' < minAdm_red + ab, where the RHS z-integral (a "reduced
comparator" on a SHORTER chain, one matrix-factor fewer) is finite by an outer induction hypothesis iff
its exponent (c' − ab/2) < ½·minAdm_red, i.e. iff 2c' < minAdm_red + ab. Here minAdm_red is a fixed
positive integer (the reduced chain's combinatorial codimension), and Q_p above is itself the product
prod(reduced chain, z) integrated over z — i.e. the pivot block Q_p is not truly fixed but is the
reduced-chain product, and its z-box integral is the reduced comparator. The additive split of the
threshold is minAdm_full = ab + minAdm_red (peel-fold, given), so 2c' < minAdm_red + ab ⟺ c' < ½·minAdm_full.

## Spectral structure and the mechanism under review

Write G := hsQ hsQᵀ (r×r Gram), eigendecomposition G = V Λ Vᵀ, eigenvalues λ_1 ≤ … ≤ λ_r ≥ 0. Then
‖B·hsQ‖_F² = tr(B G Bᵀ) = Σ_i λ_i ‖(B V)_{·i}‖². After an orthogonal change of variables B ↦ B V (the
box is ball-symmetric, take balls), the inner integral is

    ∫_{B box} ( Σ_{i=1}^r λ_i ‖B_{·i}‖² )^{−c'} dB,   B_{·i} ∈ ℝ^p the i-th column.

On a stratum where exactly k eigenvalues are "weak" (small) and r−k are "strong" (≥ floor), the split is
d_strong = p(r−k), d_weak = p·k. A CORRECTED row-Gram floor (this is a fact I have verified):

    ‖B · W_strong‖_F² ≥ ε²·‖B · Π_strong‖_F²      (NOT ε²·‖B‖_F²),

where W_strong is the strong singular block and Π_strong the orthogonal projector onto the strong
subspace. So only the strong PROJECTION of B is floored; B·Π_weak is unconstrained and carries the weak
divergence.

Two candidate mechanisms are on the table:

(I) FRONT-B SPECTRAL PEEL. Bound the inner B-integral by a two-block radial estimate. A banked lemma gives:
    ∫_{ball_u × ball_v} (κ²‖x‖² + σ²‖y‖²)^{−c'} ≤ C·σ^{−α'},  C independent of σ, for max(0,2c'−d_u) < α' < d_v.
    For k=1 (single weak scale σ = √λ_1) this closes: bound ∫_B ≤ C·λ_1^{−α'/2}, α' < d_weak = p, then
    integrate λ_1(A_cor)^{−α'/2} over A_cor. For k>1 (multiple weak scales √λ_1 ≤ … ≤ √λ_k) collapsing ALL
    weak scales to the single smallest σ_min = √λ_1 is claimed to "lose the intermediate scales."

(II) ROW-SPLIT / SCHUR PEEL. Split B into blocks [[P (u×u), B₁₂ (u×b)], [C (a×u), D (a×b)]].
    ‖B·hsQ‖² = ‖P·Q_p + B₁₂·Q_b‖² + ‖C·Q_p + D·Q_b‖². On the chart {P invertible}, a shear
    Γ = D − C P⁻¹ B₁₂ frees the pivot corner; the D/Γ integral (a×b free corner) yields a determinant-Gram
    divisor det(Q_b Q_bᵀ)^{−a/2} times a Schur-complement residual
    ‖C·Q_p·(1 − Q_bᵀ(Q_b Q_bᵀ)⁻¹ Q_b)‖² and an exponent shift c' → c' − ab/2. A banked lemma establishes
    exactly this per fixed A_cor (any weight w>0):
      ∫_{A_cor}∫_Γ (w + ‖Ccross + Γ·Q_b‖²)^{−c'}
        ≤ ∫_{A_cor} det(Q_b Q_bᵀ)^{−a/2} · Cresid(ab,c') · (w + ‖Ccross·(1−proj)‖²)^{−(c'−ab/2)}
    and a second banked lemma gives ∫_{A_cor box} det(A_cor Z (A_cor Z)ᵀ)^{−a/2} dA_cor < ⊤ (b ≤ rank Z).

## Questions (answer each with a crisp verdict + the single load-bearing reason)

Q1. In mechanism (I), WHY exactly does collapsing k>1 weak scales to σ_min fail? Be concrete: with weak
scales √λ_1 ≤ … ≤ √λ_k and dimension p per column, compute the honest exponent of the multi-scale radial
integral ∫(Σλ_i‖x_i‖² + strong)^{−c'} as a function of (λ_1,…,λ_k), and contrast with the single-σ_min
bound λ_1^{−α'/2}, α'<p·k. Does the honest divergence factor as a PRODUCT ∏_i λ_i^{−a} (i.e. the weak
determinant to the power −a), and if so does the σ_min-collapse over-count or under-count?

Q2. Is the correct k>1 divergence exactly det(Q_b Q_bᵀ)^{−a/2} (the corank determinant-Gram, mechanism II),
and is ∏_{i weak} λ_i(G)^{−a/2} (the product of weak Gram eigenvalues of the FULL stacked Gram G) EQUAL to
det(Q_b Q_bᵀ)^{−a/2} up to a factor bounded above and below by the strong data? State the exact Schur
identity relating det(G) = det(hsQ hsQᵀ) to det(Q_p Q_pᵀ)·det(Schur complement) and identify which factor
is the honest weak-determinant.

Q3. Given Q1–Q2, is mechanism (II) (row-split + Schur, det-Gram divisor det(Q_bQ_bᵀ)^{−a/2}, shift c'→c'−ab/2,
then the reduced comparator absorbs the residual) a COMPLETE and NON-CIRCULAR route to (D) for ALL k
(1 ≤ k ≤ b), for every c' with 2c' < minAdm_red + ab? "Non-circular" = the argument must NOT assume the
stacked matrix hsQ has a lower singular-value floor (no σ_min(hsQ) ≥ ε hypothesis) and must NOT assume the
full integral finite; it may use only the deep floor Z Zᵀ ⪰ ε'²·U Uᵀ, corank survival (rank Q_b = b a.e.),
and the reduced-chain IH. If mechanism (II) is complete, is the front-B spectral peel (I) then UNNECESSARY?
Or is there a residual role for (I) at k=1 that (II) does not cover?

Q4. The Schur-complement residual ‖C·Q_p·(1 − Q_bᵀ(Q_bQ_bᵀ)⁻¹Q_b)‖² depends on A_cor (through Q_b's rowspace
projector) and on Q_p. For the reduced comparator (RHS of (D)) to absorb it, one integrates the C-block and
the z-block and must show this residual, integrated, is ≤ C·(reduced comparator) UNIFORMLY in A_cor. Identify
the single hardest sub-step in showing this uniform-in-A_cor absorption, and whether it genuinely couples the
corank integral to the pivot integral (i.e. whether the A_cor integral and the z integral can be separated by
Tonelli/Fubini or must be handled jointly). Is the uniform-C pull-out sup_{A_cor} C < ⊤ sound, or does it
diverge (e.g. as A_cor → 0)?

Q5. Two boundary regimes. (a) The log borderline c' = ab/2 (equivalently the shifted exponent c'−ab/2 = 0):
does radial integration of the corner produce a logarithm, and how should the sub-regime c' ≤ ab/2 be handled
(a coarser no-shift bound?) vs c' > ab/2? (b) The top level a = 0 (equivalently the flag level j = r, no free
corner, ab = 0): should this be handled as a separate base case rather than a limit of the a>0 argument? Give
the reason.

Q6. Overall verdict on building this in a proof assistant: is the cleanest route (I), (II), or a hybrid?
Name the SINGLE hardest lemma to formalize and whether it needs a global smooth SVD/eigendecomposition
(measurability hazard) or can be done with finitely many per-point algebraic minor charts.
</task>

<output_contract>
Answer Q1–Q6 in order, each a short paragraph: a one-word/one-phrase verdict first, then the single
load-bearing reason (with the exact exponent arithmetic where asked). Then one closing paragraph: the
single most likely thing that BREAKS the intended route, and the cheapest check to settle it. Mark every
claim [FACT] (you can derive it) or [INFERENCE] (plausible, unproven). Keep total under ~900 words.
</output_contract>

<grounding_rules>
This is a mathematics analysis problem, not a code review — you may compute freely. Do NOT invent
repo-specific lemma names or claim what "the code does"; reason from the stated object only. Where a claim
depends on genericity (e.g. rank Q_b = b), state that dependence explicitly. If a proposed exponent is
wrong, give the corrected one with the computation.
</grounding_rules>
