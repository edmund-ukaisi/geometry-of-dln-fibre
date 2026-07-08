**1. VERDICT on Q1**

concern-correct. MATHEMATICAL DEDUCTION: if `s = rank Q_b < b`, then `Γ ↦ Γ Q_b` has rank `a s`, not `a b`, with kernel dimension `a(b-s)`. Thus the `ab/2` isotropic shift is false in general; the effective shift is at most `as/2`. The literal `r -> ∞` divergence is only if the box cutoff is dropped, but the same defect appears as failure of the `W^{-(c' - ab/2)}` bound as `W -> 0`. Counterexample: `Q_b = 0` and `C Q̃ = 0` gives inner integral `Vol(box) · W^{-c'}`, not `O(W^{-(c' - ab/2)})`.

**2. Q2**

On the exact kernel subspace `K(Q_b) = {Γ : Γ Q_b = 0}`, the residual integrand is
`(frobSq(A Q̃) + frobSq(C Q̃))^{-c'} = frobSq([A; C] Q̃)^{-c'}`.
This is a linear space isomorphic to `Mat_{a × (b-s)}` after choosing a basis of the left nullspace of `Q_b`; it is not canonically the original axis-aligned matrix box. No Gram term remains in the integrand on the exact kernel, but the coordinate split depends on `Q_b`. There is no `ab/2` shift from this kernel part. After quotienting by the active rank-`s` directions, the natural shifted exponent is `c' - as/2`. ASSUMPTION: it matches your shorter-chain loss only if `redChain t M` is represented by `frobSq([A; C] Q̃)` or is comparable to it.

**3. Q3**

Bank the statement: **rank-stratified right-multiplication box descent**. On a measurable outer chart where `rank Q_b = s` and a fixed `s`-row pivot of `Q_b` is full row rank, split `Γ` into active `a×s` variables and kernel `a×(b-s)` variables by a measure-preserving shear/linear chart. Then, for `c' > as/2` and core `W = frobSq(A Q̃) > 0`,
`∫_{Γ∈Box_{a×b}} (W + frobSq(C Q̃ + Γ Q_b))^{-c'} dΓ ≤ C · W^{-(c' - as/2)}`,
with a terminal finite branch for `c' < as/2` on finite outer measure. Constants must expose pivot-conditioning/box-enlargement hypotheses. This composes your banked full-row-rank inner lemma with `q = s`, plus bounded kernel volume. It does not require the whole DLN recursion, but it correctly exposes the rank branch the recursion must later handle.

**4. BOTTOM LINE**

The pinned isolated peel step is not sound as stated if it claims a uniform `ab/2` descent through rank-deficient `Q_b`. The correct decomposition is: peel, stratify the tail block by `rank Q_b = s`, apply the isotropic/full-rank brick only to the active `a×s` quotient variables, carry the bounded kernel variables separately, and recurse on the resulting shorter-chain obligation with exponent shifted by `as/2`, not `ab/2`. If a DLN width bottleneck forces `s < b` on positive-measure charts, this is a genuine interleaving requirement, not a removable technicality.