<task>
Exact-analysis question about matrix-product box integrals and whether an UNWEIGHTED
"reduced-chain" black-box bound can prove a threshold-tight finiteness for the parent chain.

Setup. Fix c' > 0. Over real matrices with entries in [-1,1] (Lebesgue), define for the
"square depth-3" chain (2,2,2,2):

    I(c') = ∫_{P ∈ [-1,1]^{2x2}, det P ≠ 0}  ∫_{Z ∈ [-1,1]^{2x2}}  ∫_{W ∈ [-1,1]^{2x2}}
                ‖ P · Z · W ‖_F^{-2c'}   dP dZ dW ,

where ‖·‖_F is Frobenius norm. (The {det P ≠ 0} restriction only removes a null set.)

Known fact A (do NOT re-derive; take as given): the real-log-canonical-threshold / exact
finiteness threshold of I is c' < 3/2, i.e. I(c') < ∞ iff c' < 3/2. (This is Aoyagi's DLN
result: threshold = ½·minAdm, minAdm(2,2,2,2)=3.)

Known fact B ("the plain reduced-chain IH", a black box you MAY use): for the reduced
depth-2 chain (2,2,2), the UNWEIGHTED product-box integral

    J(c'') = ∫_{Z ∈ [-1,1]^{2x2}} ∫_{W ∈ [-1,1]^{2x2}} ‖ Z · W ‖_F^{-2c''} dZ dW

is finite for all c'' < 3/2 (again threshold ½·minAdm(2,2,2)=3/2). You may invoke J at ANY
c'' < 3/2, with ANY finite multiplicative constant, over any sub-box.

The core questions:

(Q1) Compute/confirm the pushforward density ρ(Y) of the map (P,Z) ↦ Y := P·Z, where P,Z
are independent uniform on [-1,1]^{2x2}. Specifically its behaviour near the rank-drop locus
{det Y = 0}: is ρ bounded, log-divergent, or a genuine power dist(Y,{det=0})^{-A}? Give A.

(Q2) THE CRUX. Using ONLY black-box B (the unweighted reduced-chain bound J, at any c''<3/2,
any finite constant, any sub-box) — plus elementary pointwise inequalities, Tonelli/Fubini,
affine changes of variables, and domain enlargements — can you prove I(c') < ∞ for ALL
c' < 3/2 (matching the true threshold)? Or is there an unavoidable gap: a sub-interval of
c' ∈ (?, 3/2) where I is finite (by fact A) but NO argument built solely on B reaches it?
If there is a gap, quantify the threshold loss precisely.

(Q3) Consider the change of variables Y = P·Z at fixed P (Jacobian |det P|^{-2} for the 2x2
Z-block). If one enlarges the Y-domain to a fixed box to decouple, what happens to
∫_{[-1,1]^{2x2}} |det P|^{-2} dP ? Is the resulting bound on I useful or vacuous? Relatedly,
consider the pointwise fold ρ(Y) ≤ const · ‖Y·W‖_F^{-A} at the deep-generic locus: what
threshold does feeding this into B reach, and does it match 3/2?

(Q4) Scalar sanity model. Evaluate the large-N behaviour of
    ∫_{[-1,1]^2} e^{-N(1+c^2) z^2} dz dc
and say whether it is ~ N^{-1/2}, ~ N^{-1/2} log N, or other. Then comment: if one "extracts"
a pointwise weight |z|^{-1} (non-integrable) from a coupled integrand and feeds an UNWEIGHTED
1-D bound, is the resulting reduction sound or does it mis-predict the decay?

(Q5) General principle. State the precise condition under which a coupled matrix-product
integral ∫ ρ(Y)·f(Y)^{-c'} (ρ a pushforward density with a power singularity of order A on a
rank locus) CAN be bounded, up to the sharp threshold, by an UNWEIGHTED black-box bound on
∫ f(Y)^{-c''}. When does it FAIL and force either (a) charts pinned to σ_min(P) ≥ δ (with a
separate treatment of the {σ_min(P) < δ} complement) or (b) a black box that already carries
the weight/coupling (a "weighted IH")?
</task>

<output_contract>
Answer Q1–Q5 in order, each a short labelled section. For Q2 give a yes/no plus the exact
threshold reached by the best B-only argument, and the size of any gap. For Q3/Q4 give the
exact large-N / integrability verdict. For Q5 state the condition as a crisp criterion
(inequality in A vs the available headroom). Be quantitative; flag any step that is an
inference rather than a proof. ≤ 700 words.
</output_contract>

<grounding_rules>
Matrices are real, entries in [-1,1], Lebesgue. minAdm(2,2,2,2)=3, minAdm(2,2,2)=3 (given).
Do not question facts A and B; the question is purely whether B alone suffices to reach A's
threshold, and the mechanism (density order A vs headroom) behind any gap. Distinguish proven
from inferred. Do not write code you cannot run; reason analytically (a 2x2 product density is
classical).
</grounding_rules>
