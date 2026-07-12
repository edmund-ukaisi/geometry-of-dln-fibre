<task>
A follow-up to a prior consult. In the prior one we established (you concurred): for a peel of the
front layer of a deep-linear-network chain, the banked measure lemma's output base
Base = w + frobSq(C·Q̃ₚ·(I−P_{Qb})) is RATIONAL (Gram inverse (QbQbᵀ)⁻¹), NOT a clean bilinear γ' loss;
but the peel CLOSES by DOMINATION on the units sector: drop the nonneg residual (Base^{-e} ≤ w^{-e})
and bound the Gram divisor det(QbQbᵀ)^{-a/2} by a constant, leaving the clean bilinear
w = frobSq(Γ'·A₃) (reduced-product loss, tail A₃ tied), which is a genuine γ'-admissible reduced
decoration. That analysis used the TRIVIAL parent (front = the literal first layer A₁, no radial).

Now verify the GENERAL γ'-resolved parent, where the front is NOT the trivial A₁ but a free block Γ_D.
Adjudicate two questions from the exact algebra. Do NOT assume my framing implies an answer.
</task>

<context — the general γ'-parent, exact>
Chain M=(3,3,2,2), binding cut t★=2, corank widths a=b=1, peelCharge=a·b=1, redChain=(2,2,2).
A γ'-RESOLVED (not trivial) parent decoration D over M has, by the landed tied-γ' clause:
  decLoss(u,z) = commonDivisor(u)² · frobSq(Γ_D · Z_tail,D),
where
  - Γ_D : a_D × M1 = a_D × 3 is a FREE front block (its entries are deeper/active coordinates in Z,
    integrated over the domain), a_D ≥ 2 by the dims clause minAdm ≤ a_D·M1;
  - Z_tail,D = prod(dropHead M) = A₂·A₃ (3×2), the TIED suffix layer product (A₂:3×2, A₃:2×2 free);
  - commonDivisor(u) = |u₀|^{k} (k = sharedDivisorExp), the shared radial monomial; jac = ![jac₀];
  - genuineCarrier pins ν = Fin(M0)×Fin(Mlast) = Fin3×Fin2, and residuals = entries of Γ_D·Z_tail,D
    (a_D × Mlast = a_D × 2), so representing the full (3×2) product forces a_D = M0 = 3.

The peel block-partitions the front Γ_D (rows M0=3 → t★+a=2+1, cols M1=3 → t★+b=2+1):
Γ_D = [[P,B₁₂],[C,D_D]], P:2×2 (invertible chart), B₁₂:2×1, C:1×2, D_D:1×1 corank corner.
Tail A₂A₃ (3×2) row-split → Qp:2×2 (pivot rows), Qb:1×2 (corank row). Shear D_D→Γ (free corner),
Q̃ₚ = Qp + P⁻¹·B₁₂·Qb. The freed-block (matrix Γ) integral gives, at shifted exponent -(c'-ab/2),
  det(QbQbᵀ)^{-a/2}·Cresid·Base^{-(c'-ab/2)},  Base = w + frobSq(C·Q̃ₚ·(I−P_{Qb})), w = frobSq(P·Q̃ₚ).

Exact-algebra facts I have verified (sympy exact) for this general parent:
  (G1) w = frobSq(P·Q̃ₚ) = frobSq([P|B₁₂]·A₂·A₃) = frobSq(Γ'·A₃), Γ' = [P|B₁₂]·A₂ (2×2), tail A₃; 
       polynomial (P⁻¹-free). So w is a clean bilinear γ' reduced-product loss with tied reduced tail
       A₃ = prod(dropHead(2,2,2)). The corank rows C appear ONLY in the residual term.
  (G2) residual frobSq(C·Q̃ₚ·(I−P_{Qb})) is rational in the tail (Gram denom ‖Qb‖²), droppable
       (Base ≥ w, exponent negative).
  (G3) commonDivisor(u)² = |u₀|^{2k} factors through the freed-block integral as a constant multiplier
       (independent of the freed matrix block Γ), so decLoss^{-c'} = |u₀|^{-2kc'}·freedSchurLoss^{-c'}.
  (G4) jac-carry: setting reduced jac'₀ = jac₀ − k·peelCharge reproduces the reduced threshold EXACTLY:
       axisRatio(h,k)=(h+1)/(2k); parent axisRatio(jac₀,k)=minAdm(M)/2 ⟹ reduced axisRatio(jac'₀,k)=
       minAdm(redChain)/2, with jac'₀ ≥ 0. Verified over several widths incl. deep-sharing.
</context>

<questions>
Q1 (clean-w comparator survives the free front block). Is the peel of the general γ'-parent (front =
   free block Γ_D, a_D=M0=3, with a shared radial commonDivisor² and accumulated jac) structurally the
   SAME domination as the trivial parent — i.e. does it still yield a genuine γ'-admissible reduced
   comparator D' with D'.decLoss = commonDivisor(u)²·frobSq(Γ'·A₃), Γ' = [P|B₁₂]·A₂, tail A₃ tied? Or
   does the fact that the front is a free block (not the literal layer A₁), and/or the shared radial /
   accumulated jac, introduce a genuine obstruction the trivial anchor could not see?

Q2 (absorption CoV with free Γ_D; C integrates out bounded). The reduced comparator front Γ' = [P|B₁₂]·A₂
   is a PRODUCT of the top pivot rows of Γ_D and A₂ (an absorption change of variables with a |det P|-type
   Jacobian, P invertible on the pivot chart). The corank rows C (⊂ the free block Γ_D) appear ONLY in the
   dropped residual, so after dropping they integrate over their box as a bounded factor. Does this
   absorption CoV work when the front is the free block Γ_D (rather than the literal A₁), with C
   integrating out as a bounded constant — so genuineCarrier D' is producible? Any way it fails at this
   generality that it did not for trivial?

Also assess (G3)+(G4): does the shared radial + accumulated jac carry through MONOMIALLY (no non-monomial
weight — Gram divisor, absorption Jacobian — sneaking into the reduced jac)?
</questions>

<output_contract>
For Q1 and Q2 each: VERDICT (survives / genuine new obstruction), the exact reason, inference vs fact.
Then: is the shared-radial+jac carry monomial and threshold-exact? State the single most likely way the
general-parent verdict is wrong that the trivial anchor could not reveal.
</output_contract>

<grounding_rules>
Reason from the exact algebra. The key difference from the trivial parent is: front = free block Γ_D
(entries are deeper coordinates) instead of the literal layer A₁; a shared radial commonDivisor²; an
accumulated jac. Check whether the block-partition + Schur shear + absorption CoV + drop-residual +
bound-Gram all go through with Γ_D free, and whether the radial/jac ride through as monomials. The
Gram divisor and |det P| Jacobian are bounded on the units/pivot chart, NOT monomials — check they do
NOT need to enter the reduced jac.
</grounding_rules>
