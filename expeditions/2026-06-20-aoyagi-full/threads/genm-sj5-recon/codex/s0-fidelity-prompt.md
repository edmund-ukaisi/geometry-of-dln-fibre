<task>
Adjudicate two exact-algebra fidelity questions in a formalisation of Aoyagi's RLCT computation
for deep linear networks. I give you the exact objects and ask whether an identity/producibility
holds. Do NOT assume my framing implies an answer; verify from the algebra.
</task>

<context — the objects, exact>
A "chain" M = (M0,M1,...,ML) of matrix widths; layers A^(s) of size M_{s-1} x M_s; product
prod(M) = A^(1)...A^(L). The RLCT analysis integrates frobSq(prod(M))^(-c') over a parameter box.

A "decoration" D over a chain M carries: exceptional coords u (count d), a jacobian exponent
vector jac (a MONOMIAL weight ∏_ℓ |u_ℓ|^{jac_ℓ}), a deeper parameter space Z with a domain, and a
"carrier" whose loss is
    decLoss(u,z) = ∑_i ( genMonomial_i(u) · residual_i(z) )^2 ,   residual_i(z) = ∑_v coeff_i,v(z)·x_v(z)
i.e. a sum over generators i of (monomial in u)·(linear residual). D.integral(c') =
∫_{dom} ∫_{unitBox} (∏_ℓ|u_ℓ|^{jac_ℓ}) · decLoss(u,z)^{-c'}.

Admissibility `adm M D` requires (when the binding-cut corank widths a,b of M are both > 0) a
"gamma-prime" (γ') resolved-corner form: there is a free front block Γ' (active variables = its
entries) and a TIED tail Z_tail' = prod(dropHead M) (the suffix layer product, a SPECIFIC matrix),
such that every residual is an entry of the matrix product  Γ'·Z_tail'  (bilinear), and
decLoss = commonDivisor(u)^2 · frobSq(Γ'·Z_tail'). The tail-tie (Z_tail' = prod(dropHead M),
not a free matrix) is known to be necessary for soundness.

A banked measure lemma `freedSchurLoss_inner_peel_le` performs ONE peel of the front layer at the
binding cut t★. Concretely, for the anchor chain M=(3,3,2,2), t★=2, corank widths a=b=1,
peelCharge=a·b=1, reducing to redChain=(2,2,2). It block-partitions the 3x3 front layer A1 as
[[P,B12],[C,D]] (P:2x2 pivot invertible, B12:2x1, C:1x2, D:1x1 corank corner) and writes the tail
Z_tail = A2·A3 (3x2) row-split into Qp (2x2 pivot rows) and Qb (1x2 corank row). Setting
Q̃ₚ = Qp + P⁻¹·B12·Qb and shearing D→Γ (free), the full product loss frobSq(A1·A2·A3) equals
    freedSchurLoss = frobSq(P·Q̃ₚ) + frobSq(C·Q̃ₚ + Γ·Qb).
Integrating the freed block Γ over a box (Morse), the lemma outputs, at shifted exponent -(c'-ab/2):
    det(Qb·Qbᵀ)^{-a/2} · Cresid(ab)(c') · Base^{-(c'-ab/2)},
    Base = w + frobSq( C·Q̃ₚ·(I − P_{Qb}) ),   w = frobSq(P·Q̃ₚ),  P_{Qb} = Qbᵀ(Qb·Qbᵀ)⁻¹Qb.

Exact-algebra facts I have verified (sympy, exact rationals) for the (3,3,2,2)→(2,2,2) anchor:
  (F1) freedSchurLoss = frobSq(A1·A2·A3) under D = Γ + C·P⁻¹·B12.  [TRUE]
  (F2) Base = min over Γ of freedSchurLoss (Γ free).  [TRUE — Base is the corner-minimised loss]
  (F3) w = frobSq(P·Q̃ₚ) is a POLYNOMIAL in the tail A3 (the P⁻¹ cancels; "P⁻¹-free pivot").
  (F4) The residual term frobSq(C·Q̃ₚ·(I−P_{Qb})) is a RATIONAL function of the tail A3, with
       denominator = Qb·Qbᵀ = ‖A2_cor·A3‖² (the corank-row Gram), which vanishes on the rank-drop
       locus. So Base is rational, not polynomial, in the deeper (tail) variables.
  (F5) redChain=(2,2,2) has binding-cut corank widths a'=b'=1 (both >0), so `adm (2,2,2) D'` REQUIRES
       the γ' form; dropHead(2,2,2)=(2,2) with single tail layer, so the TIED Z_tail' = A3 (=A2').
</context>

<questions>
Q1 (residual = reduced decLoss). Is Base = w + frobSq(C·Q̃ₚ·(I−P_{Qb})) equal to a genuine
   redChain=(2,2,2) decoration's decLoss `commonDivisor(u)²·frobSq(Γ'·Z_tail')` in the γ' form with
   the TIED tail Z_tail'=A3 (residuals bilinear entries of Γ'·A3)? If not literally, is there any
   legitimate reshape (change of variables on the deeper space; choice of active/spectator split;
   the arbitrary coeff of a generic carrier) that makes the peel output equal a γ'-form (2,2,2)
   decLoss D' satisfying `adm D'` — or does the Gram-inverse projection (I−P_{Qb}) obstruct it?

Q2 (reduced-adm producibility + the Gram divisor). The peel also emits the weight det(Qb·Qbᵀ)^{-a/2}
   which must be carried by the reduced decoration's MONOMIAL jac weight ∏|u|^{jac}. But det(Qb·Qbᵀ)
   is a polynomial in the tail (raised to -a/2 = -1/2), not a monomial in exceptional coords u. Can
   this Gram divisor legitimately become part of a reduced decoration's monomial jac weight at the
   point of handing D' to the induction hypothesis (which requires `adm D'` up front)? Or does it,
   like the residual, only make sense after a FURTHER resolution/CoV that is not part of this peel?

Consider carefully: (i) dropping the residual (Base ≥ w, exponent negative ⟹ Base^{-e} ≤ w^{-e})
   and bounding det(Qb·Qbᵀ)^{-a/2} by a constant on the units sector {Qb·Qbᵀ ≽ c·I} — does the
   resulting reduced object still satisfy `adm D'` (γ' resolved-corner, a'=b'=1>0)? (ii) whether the
   handoff to the decorated IH requires D'.decLoss to literally BE the γ' form, or merely to be
   finiteness-dominated by one.
</questions>

<output_contract>
For Q1 and Q2 each: VERDICT (holds literally / holds after reshape / does not hold), then the exact
algebraic reason. Mark clearly which statements are your inference vs. facts you re-derived.
State the single most likely way your verdict is wrong.
</output_contract>

<grounding_rules>
Reason from the exact algebra above. The Gram inverse (Qb·Qbᵀ)⁻¹ and the projection P_{Qb} are the
crux. Do not accept "it's the reduced loss" without checking the bilinear/tied-tail form. A generic
carrier's coeff may be arbitrary (rational allowed), but the γ' clause is rigid (bilinear Γ'·Z_tail',
tied tail). Distinguish "the integral is finite by domination" from "Base equals a γ'-form decLoss".
</grounding_rules>
