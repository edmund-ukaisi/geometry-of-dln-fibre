<task>
Adjudicate the threshold soundness of a Lebesgue-integral finiteness argument (RLCT-flavoured). This is real analysis, not Lean. Decorrelate: I give BOTH directions; pick the correct one on the math.

SETUP (anchor chain (3,3,3), one layer peeled, u=2, corner dims a=b=1; all boxes are cubes [-1,1] unless noted).
Fixed "deep" data at reduced parameters z (which itself is integrated over a box):
  • Q_p : 2×3 real matrix ("pivot rows" of a matrix product; a nonzero polynomial in z, so ≠ 0 a.e.).
  • Zf(z) : 3×3 (rank ≥ 3 a.e.); corank rows Q_b := A_cor · Zf(z), where A_cor ∈ [-1,1]^{1×3} is integrated.
Front-block variables (integrated over cubes): P : 2×2 (invertible on domain), B₁₂ : 2×1, C : 1×2, Γ : 1×1.
Define Q̃_p := Q_p + P⁻¹·B₁₂·Q_b. The per-point loss (Frobenius sq):
  freedLoss = w + κ,   w := ‖P·Q_p + B₁₂·Q_b‖²  (PIVOT),   κ := ‖C·Q̃_p + Γ·Q_b‖²  (CORANK).
[Note w = ‖P·Q̃_p‖² for invertible P, so w carries the cross-term B₁₂·Q_b = B₁₂·A_cor·Zf(z).]

LHS := ∫_z ∫_{A_cor} ∫_{P,B₁₂,C} ∫_Γ (w+κ)^{-c'}   (c' ≥ 0 real, exponent).
Comparator RHS := ∫_z ∫_{v∈[0,1]} v^5 · [ ∫_{A_cor} ∫_Γ ( decLoss + ‖Γ·Q_b‖² )^{-c'} ] dv,   decLoss := v²·‖Q_p‖².

KEY QUANTITIES: ρ = min tail width = 3; uρ = 6; ab = 1; au = a·u = 2; minAdm(redChain)=6; minAdm(full)=7.
KNOWN (paper/pen-and-paper facts): LHS < ∞  ⟺  c' < minAdm(full)/2 = 3.5;  RHS < ∞  ⟺  c' < 3.5;  pure-pivot ∫_{P,B₁₂} w^{-c'} (corank dropped) < ∞ ⟺ c' < uρ/2 = 3. Hypothesis available: minAdm(redChain)=6 ≤ uρ=6 (so uρ/2 = minAdm(redChain)/2 = 3). GOAL to prove: RHS < ∞ ⟹ LHS < ∞. The delicate regime is c' ∈ (3, 3.5).

ADJUDICATE each (SOUND / UNSOUND / CONDITIONAL, with the exponent accounting):

(1) The move "integrate out the pivot block at exponent c' as a finite constant C_ang, i.e. bound the inner ∫_{A_cor,Γ}(w+κ)^{-c'} by C_ang · (a corank-only integral), where C_ang ~ ∫_{P,B₁₂} w^{-c'} or the blow-up-angular version": is C_ang < ∞ for c' ∈ (3,3.5)? My claim: NO — near {P·Q_p+B₁₂·Q_b = 0} (codim uρ=6) the pivot integral at exponent c'>3 diverges; the corank's regularization (the missing ab/2) is lost by pulling the pivot out at full c'. Confirm or refute.

(2) The full threshold 3.5 = (uρ+ab)/2 for the DOUBLE integral: does it arise from the JOINT zero-locus {pivot=0}∩{corank=0} of codim uρ+ab, and can it be realized as a squared-norm of a SINGLE linear map (so that a "∫_cube (‖Lx‖²)^{-c'} < ∞ ⟺ c' < rank(L)/2" lemma applies) in variables (P,B₁₂,C,Γ,A_cor,z)? Obstruction I see: B₁₂·Q_b = B₁₂·A_cor·Zf(z) is BILINEAR in (B₁₂, A_cor), and Q_p, Q_b depend nonlinearly on z; so freedLoss is NOT ‖linear‖² jointly. At FIXED (z, A_cor) the map (P,B₁₂,C,Γ)↦freedLoss IS ‖linear‖² but its rank is M0·rank(Q) = 3·3 = 9 (threshold 4.5), NOT uρ+ab=7. Confirm: is 7 (not 9) unreachable by any fixed-(z,A_cor) linear-image codim, i.e. does the reduction from 9 to 7 genuinely require the outer (z,A_cor) degeneracy (so a joint linear-codim lemma cannot deliver 3.5)?

(3) EXPONENT EXTRACTION "RHS < ∞ ⟹ c' < 3.5": lower-bound RHS by restricting the (A_cor,Γ) integral to {‖Γ·Q_b‖² ≤ decLoss}, on which (decLoss+‖Γ·Q_b‖²)^{-c'} ≥ (2·decLoss)^{-c'}, so RHS ≥ 2^{-c'} ∫_z∫_v v^5 · decLoss^{-c'} · μ{(A_cor,Γ): ‖Γ·Q_b‖² ≤ decLoss}. If μ{...} ≳ decLoss^{ab/2} (a corner sublevel-VOLUME LOWER bound: Γ in a ball of radius ~√decLoss/σ_max(Q_b), A_cor full-rank), then RHS ≳ ∫_z∫_v v^5·decLoss^{-(c'-ab/2)} = ‖Q_p‖^{...}∫_v v^{6-2c'}, which DIVERGES for c' ≥ 3.5. Is this a SOUND way to prove RHS = ∞ for c' ≥ 3.5 (hence RHS<∞ ⟹ c'<3.5)? Is the sublevel-volume lower bound μ ≳ decLoss^{ab/2} correct (any hidden dependence on σ_max(Q_b) that could vanish)?

(4) MY CANDIDATE "DROP" (pointwise-in-(z,v,A_cor,Γ) with UNIFORM constant, after blowing up P = v·P̂ with |det P̂|=1 and rescaling B̃₁₂=B₁₂/v): 
    ∫_{P̂,B̃₁₂,C} ( v²·‖P̂·Q_p+B̃₁₂·Q_b‖² + ‖C·Q̃_p+Γ·Q_b‖² )^{-c'}  ≤  C_abs · ( decLoss + ‖Γ·Q_b‖² )^{-c'}
with C_abs finite and UNIFORM in (z,v,A_cor,Γ); then ∫_z∫_v v^5 ∫_{A_cor}∫_Γ ⟹ LHS ≤ C_abs·RHS. Questions: (i) the pointwise (P̂,B̃₁₂,C)-integral has singularities of codim uρ (pivot) and au (corank-in-C); is its threshold (uρ+au)/2 (= 4 for anchor, > 3.5 ✓)? (ii) is C_abs genuinely UNIFORM (the "same-rate ratio bound" as decLoss→0 and ‖Γ·Q_b‖²→0)? (iii) does the C-absorption contributing au (not ab) break uniformity when b > u (au < ab), i.e. is there a regime where (uρ+au)/2 < c' < (uρ+ab)/2 so C_abs = ∞ while RHS still finite? If so this DROP is only conditionally valid (b ≤ u).

(5) Given all the above, what is the SINGLE cleanest SOUND route to "RHS<∞ ⟹ LHS<∞" covering c'∈(3,3.5), and what are the minimal genuinely-new sub-lemmas it needs?
</task>

<output_contract>
Five numbered verdicts (1)-(5). For (1)-(4): a one-word verdict [SOUND / UNSOUND / CONDITIONAL] then ≤5 lines of the exponent accounting that justifies it (give the codim/threshold arithmetic explicitly). For (5): name ONE route and list its ≤4 new sub-lemmas. Be terse. Mark every step as [FACT] (standard measure-theory/RLCT) or [INFERENCE].
</output_contract>

<grounding_rules>
This is pure math; you may use standard facts (blow-up/monomialization, ∫_{ℝ^k, |x|≤1}|x|^{-2c'}<∞ ⟺ c'<k/2, Fubini/Tonelli, sublevel-set volume ~ δ^{codim/2} for a nondegenerate quadratic form). Do NOT assume any Lean library. If a claimed threshold or sublevel bound is wrong, say so and give the correct value. Distinguish what you can prove from what is plausible-but-unchecked.
</grounding_rules>
