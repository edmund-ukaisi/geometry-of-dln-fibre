<task>
You are a decorrelated second opinion on two independent points. I am withholding my
own conclusions. Argue whichever way the mathematics supports; give crisp verdicts.
Exact measure theory / RLCT reasoning. Keep it short.

## Setup (self-contained)
Fix integers u ≥ 1, a ≥ 0, b ≥ 0. Fix a matrix hsQ of size (u+b) × N with N ≥ u+b,
built as hsQ = [ Q_p ; Q_b ] where Q_p (u × N) has full row rank u, and Q_b = A·Z
(b × N) with Z (a "deep factor") well-conditioned: Z·Zᵀ ⪰ ε'²·I (a Loewner floor),
so Z has full row rank. A ranges over the box [−1,1]^(b×(rows of Z)).
B ranges over the FULL box [−1,1]^((u+a)×(u+b)) — the "front block" matrix; write its
top-left u×u block as B₁₁ = toBlocks₁₁(B).
L(B,A) = ‖ B · hsQ ‖_F²  (squared Frobenius norm; degree-2 homogeneous in B).
c' > 0 is the exponent; the integrand is L(B,A)^(−c') = ‖B·hsQ‖_F^(−2c').

Define the FULL-box integral
    I_full(c') = ∫_{A ∈ box} ∫_{B ∈ FULL box} L(B,A)^(−c')  dB dA.
Define the RESTRICTED integral where B is confined so B₁₁ is invertible:
    I_unit(c') = ∫_{A ∈ box} ∫_{B ∈ box, det(B₁₁)≠0} L(B,A)^(−c')  dB dA.

## Question 1 (measure theory — the main one)
The locus {B : det(B₁₁) = 0} is the zero set of a nonzero polynomial (u ≥ 1), hence a
proper algebraic subvariety of the B-box, Lebesgue-measure-zero. The integrand
L(B,A)^(−c') is a finite real number for every (B,A) with L>0, and equals 0 where L=0
(convention x^(−c')=0 for x=0, c'>0). It can be LARGE (blow up) as B approaches the
locus det(B₁₁)=0.
CLAIM: I_full(c') = I_unit(c') exactly (both finite or both infinite), because the
region {det(B₁₁)=0} is null and the Lebesgue integral of a nonneg measurable function
over a null set is 0 — even though the integrand blows up approaching that null set.
Is this CLAIM correct? State any hypothesis it needs. In particular: does the integrand
possibly being +∞ (or unbounded) NEAR the null locus break "integral over a null set = 0"?
Distinguish clearly: (i) the integral of a nonneg function OVER a null set is 0
regardless of the function's values there; vs (ii) the integral over a full-measure
neighborhood can still diverge from accumulation — is that accumulation charged to the
null set or to the surrounding positive-measure region?

## Question 2 (RLCT threshold — decorrelated re-derivation)
Let m := "minAdm" be the RLCT/integrability exponent of the pivot-only block, i.e. the
threshold such that ∫_{B-box} ‖B·Q_p‖_F^(−2c') dB < ∞ iff c' < m/2 (Q_p fixed full-row-rank
u × N; m is the effective count for that block). Set ab := a·b.
CLAIM: sup{ c' : I_full(c') < ∞ } = (m + ab)/2, i.e. I_full(c') < ∞ iff 2c' < m + ab.
Independently derive (or refute) this. Near the rank-drop locus σ_min(hsQ) → 0 (codim 1
in A), give the inner B-integral scaling J(A) ~ g^(−β), g = σ_min(hsQ)², and the outer
A-integral convergence condition. Confirm or correct the threshold (m + ab)/2. Note the
CD-rows of B contribute strong directions to the drop too — does the full (u+a)×(u+b)
B-integral give the naive "pivot threshold + ab/2" or something larger?
</task>

<output_contract>
Two sections, "Q1" and "Q2". Each ≤ 8 lines.
Q1: VERDICT (claim correct / incorrect) + the one hypothesis that makes it work +
the single most likely error someone would make here.
Q2: the value of sup{c':I_full<∞} as a formula in m, ab; β(c'); one-line VERDICT
(threshold = (m+ab)/2, or the corrected value). Mark each key step FACT vs INFERENCE.
</output_contract>
