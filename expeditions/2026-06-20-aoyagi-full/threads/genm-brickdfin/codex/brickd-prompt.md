# Decorrelated design review: a reduced-comparator domination in a deep-linear-network RLCT induction

You are a decorrelated second opinion. Argue whichever direction the mathematics supports; I have
withheld my own conclusion. No repo access is needed — this is a self-contained analysis problem.
Please give a crisp verdict on each numbered question and flag any hidden subtlety.

## Setup (self-contained)

Fix real matrices multiplied in a chain of widths `M = (M_0, M_1, …, M_last)` (so there are `L+3`
widths, `L ≥ 0`). Let `prod(M, A)` be the product of the layer matrices `A = (A_0,…)`, an
`M_0 × M_last` matrix. The "box integral" is

    B(M, c') := ∫_{A ∈ unit box} ‖prod(M, A)‖_F^{-2c'} dA   (extended-nonneg valued).

It is a standard fact (take as given) that `B(M, c')` is finite iff `c' < ½·minAdm(M)`, where
`minAdm(M)` is a combinatorial codimension: `minAdm(M) = min_t codim Z_t`, `codim Z_t = (M_0−t)(M_1−t) + t·(deep width)` minimized over cut positions `t`; the minimizer is the "binding cut" `t★`. Write `T1(M) := ½·minAdm(M)`.

We want to prove `B(M, c') < ⊤ for all c' < T1(M)`, by induction on `L` (the number of layers).

## The head-split reduction, per flag level

Pick the binding cut `t★` and a flag level `j`, `0 ≤ j ≤ r := min(M_0−t★, M_1−t★)`; set the cut
`u = t★ + j`, `a = M_0 − u`, `b = M_1 − u`. Cover the box by the flag levels of the deep-tail
product `W`'s singular values: `shell-j = { exactly j singular values of W are < ε }` (ε a fixed
small floor; `j < r` are the genuine levels, `j = r` a lumped top shell). So
`B(M) = Σ_{j=0}^{r} shell-j(M)`.

A change of variables (row-split `A' ↔ (z, A_cor)`; a radial blow-up of the front pivot block
`P = commonDivisor(v)·P̂`; a shear `B₁₂ → Γ`) reduces each shell-j piece to

    shell-j(M, c') ≤ C_j · Comparator(redChain u M).integral(c' − ½·a·b),   C_j < ⊤,     (D_j)

where `redChain u M` is the SHORTER chain (one fewer width; arity `L+2`), and its comparator
integral is finite iff its exponent `< ½·minAdm(redChain u M)`, i.e. iff `c' < T2 := ½(minAdm(redChain u M) + a·b)`.

Two given facts:
- (peel-fold) `minAdm(M) ≤ a·b + minAdm(redChain u M)`, hence `T1(M) ≤ T2` always.
- (shell RLCT) the shell-j piece `shell-j(M, c')` is finite iff `c' < λ_j`, where
  `λ_j = ½·min_{s ≤ R_j} codim Z_s` with `R_j = min(M_0, M_1 − min(M_1,M_last) + j)` (a min over a
  SUBSET of the strata, since shell-j caps `rank W ≥ min(M_1,M_last) − j`). Hence `λ_j ≥ T1(M)`.

For `j ≥ 1` on shell-j, `W` has `k := min(M_1,M_last) − j` STRONG singular directions (σ ≥ ε) and
`j` WEAK directions (σ < ε).

## Questions

**Q1 (soundness of the FORM).** Is the domination (D_j) TRUE for every `1 ≤ j < r` and every
`c' < T1(M)`, with a per-exponent finite `C_j`? Note the trap: for `c'` in `[λ_j, T2)` (nonempty
exactly when `λ_j < T2`, i.e. `j > r/2` in square cases) the LHS is `+∞` but the RHS is finite, so
(D_j) as an inequality is FALSE there. Confirm that restricting to `c' < T1 (≤ λ_j)` removes this,
and that (D_j) then holds. Is there any `1 ≤ j < r` where the domination fails even below `T1`?

**Q2 (non-circularity of the induction).** The comparator is on the shorter chain `redChain u M`,
so `Comparator(redChain u M) < ⊤` is available from the induction hypothesis (fewer layers).
Combined with (D_j) and `B(M) = Σ_j shell-j`, we get `B(M) < ⊤` for `c' < T1(M)`. Is this a genuine
DESCENT, or is there hidden circularity? Specifically: to prove (D_j) one must NOT assume
`shell-j(M) < ⊤` (that would need the full-chain result we are proving). Consider the "ratio-trick"
packaging: `∃ C < ⊤, LHS ≤ C·RHS` deduced from "(RHS < ⊤ ⟹ LHS < ⊤) ∧ RHS ≠ 0". Is that packaging
sound and non-circular here, and does the burden then reduce to proving the finiteness IMPLICATION
"Comparator(reduced) < ⊤ ⟹ shell-j(M) < ⊤" directly by the change of variables (rather than
assuming shell-j finite)?

**Q3 (mechanism for j ≥ 1).** Proposed mechanism to produce (D_j) directly (not via the circular
subset bound shell-j ≤ B(M)): split `W = [W_strong | W_weak]`. The strong block (σ ≥ ε) carries a
row-Gram floor `‖B·W_strong‖_F² ≥ ε²·‖B‖_F²`; the `j` weak directions carry a ½·a·b corank charge
via a det-Gram divisor `det(W_weak W_weakᵀ)^{−a/2}` after a radial/Schur change of variables. Is
this "strong-minor-chart stratification" a correct and sufficient mechanism to obtain (D_j) with
`C_j < ⊤` at `c' < T1`? Watch for: (i) coupling between strong and weak blocks through the front
matrix `B` (does it obstruct the factorization?); (ii) whether a global smooth eigendecomposition is
needed (vs per-point algebraic charts); (iii) the boundary `j → r` (min(a,b) → 0). Identify the
single hardest sub-step.

Give a decisive verdict: SOUND-AND-NONCIRCULAR / SOUND-BUT-CIRCULAR / UNSOUND, plus the hardest
sub-step for Q3.
