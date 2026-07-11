<task>
You are red-teaming a Lean-formalisation DESIGN for a change-of-variables / blow-up resolution. Find where it is WRONG, INCOMPLETE, or MIS-COUNTED. Do not rubber-stamp. The design is for one "peel" of a decorated (S,J) monomial descent that must prove a matrix integral is FINITE. Burden is on the design; hunt the failure.

## The object (the integral to prove < ∞)
Deep-linear-network chain M = (M₀,M₁,M₂,…,M_last), widths in ℕ, arity ≥ 3. Fix a "binding cut" t with 1 ≤ t ≤ min(M₀,M₁). Set a = M₀−t, b = M₁−t.
The integral (over real matrix boxes; c' a real exponent):
  I = ∫_{A'} ∫_{x=(P,B₁₂,C)} ∫_Γ ( freedSchurLoss )^{−c'}
where:
- A' ranges over a compact box of the TAIL layer matrices (chain (M₁,M₂,…,M_last), i.e. L+1 matrices); prod(A') = A'₁·A'₂···  is M₁×M_last. Write Z = A'₂··· (M₂×M_last); prod = A'₁·Z.
- Q̃ = prod(A') with its M₁ rows split by a fixed permutation into Q_p (t rows, pivot) and Q_b (b rows, corank), each ×M_last.
- P is t×t and INVERTIBLE (unit) on the domain; B₁₂ is t×b; C is a×t; Γ is a×b (free).
- freedSchurLoss = frobSq(P·Q̃ₚ) + frobSq(C·Q̃ₚ + Γ·Q_b), where Q̃ₚ = Q_p + P⁻¹·B₁₂·Q_b.
KEY simplification (verified): P·Q̃ₚ = P·Q_p + B₁₂·Q_b (the P⁻¹ cancels since P is a unit), so the pivot energy w = frobSq(P·Q̃ₚ) = frobSq([P|B₁₂]·Q̃) is BILINEAR, no inverse; {w=0} is a bilinear locus.

Target: I < ∞ for c' < ½·minAdm(M), where minAdm satisfies the banked layer-peel recursion
  minAdm(M) = min_{t≤min(M₀,M₁)} [ (M₀−t)(M₁−t) + minAdm(redChain t M) ],  redChain t M = (t, M₂,…,M_last).
At the binding cut: minAdm(M) = peelCharge + minAdm(redChain t M), peelCharge = (M₀−t)(M₁−t) = a·b.

## Banked pieces (assume proven, sorry-free) the design may consume
- Γ-atom (VALUE bound): for fixed (A',x) with Q_bQ_bᵀ positive-definite (rank Q_b = b), w>0, and c' > ab/2:
  ∫_Γ (freedSchurLoss)^{−c'} ≤ det(Q_bQ_bᵀ)^{−a/2} · Cresid(ab) · (w + frobSq(C·Q̃ₚ·(I−P_{Q_b})))^{−(c'−ab/2)},  P_{Q_b}=Q_bᵀ(Q_bQ_bᵀ)⁻¹Q_b.
- Bounded branch (VALUE bound): for w>0, 0≤c', any finite-measure Γ-domain s: ∫_Γ ≤ w^{−c'}·vol(s).
- sjLoss_terminal_lintegral_lt_top: the MONOMIAL endpoint — ∫_{unit box} (∑ᵢ (∏_ℓ|u_ℓ|^{e(i,ℓ)})²)^{−c'} · ∏_ℓ|u_ℓ|^{h_ℓ} < ∞ below an explicit "monomial threshold", given a dehomogenised generator (∃ i₀ whose residual support = the shared-divisor min).
- Carrier steps: radialStep (a fresh shared divisor u₀ multiplies loss by u₀², support gains a shared column) and gen_rowMix_const (det-1 unit block-elimination mixes generators row-by-row at constant support).
- Charge arithmetic: minAdm(M) ≤ peelCharge + minAdm(redChain t M); half_minAdm − half_peelCharge ≤ half_minAdm(redChain) (so c'<½minAdm ⟹ c'−½peelCharge < ½minAdm(redChain)).
- hIH: for EVERY one-shorter chain M', ∫_{box} frobSq(prod(M') A'')^{−c''} < ∞ for c'' < ½minAdm(M'). (Strong induction hypothesis.)
- Cauchy–Binet/Loewner: det(Q_bQ_bᵀ) ≥ det(Q_S Q_Sᵀ) for any b-column minor S (a TOOL for the det-Gram weight, NOT a closer).

## Verified corank-2 anchor ((3,3,3,4), t=1, a=b=2; decorrelated pen-and-paper + Codex, corank2-cert)
- peelCharge = 4, redChain = (1,3,4), minAdm(1,3,4)=3, minAdm(3,3,3,4)=7, ½minAdm = 7/2.
- Front-first majorant on the corank cell is ASYMMETRIC: g̃ ≍ max(s₂,s₃)^{−3}·min(s₂,s₃)^{−(2c'−6)} (s₂≥s₃ the two small singular values of the tail P=Ã₁·A₂).
- The tube is finite for c'<7/2 via the JOINT pushforward density μ{s₂≤t₂,s₃≤t₃} ≍ t₂³·t₃·log(e/t₂) (dμ ≍ s₂²·log ds₃ds₂). Using MARGINALS (min(t₂⁴,t₃)) only gives c'<... η<1/4, INSUFFICIENT. The joint two-scale estimate is REQUIRED.
- The SYMMETRIC ∧²-compound weight (s₂s₃)^{−b} FAILS: pointwise needs b≥c'−3/2>3/2, integrability needs b<1, no overlap.
- The coupled corner blow-up gives 7/2: on the resolved corner the two exceptional divisors are u₀ (the 2×2=4-dim corank-block radial, Jacobian |u₀|³) and u₁ (a 3-dim boundary-row radial, |u₁|²); the coupled blow-up u₁=u₀τ gives |u₀|^{3+2+1}=|u₀|⁶ (the +1 is du₁=u₀dτ), loss G=u₀²(U₀+τ²U₁) order 2, ∫|u₀|^{6−2c'}du₀<∞ ⟺ c'<7/2. Treating u₀,u₁ as INDEPENDENT divisors gives min(2,3/2)=3/2 — WRONG. The coupling (charges ADD onto one terminal divisor: 3+2+1=6, 6+1=7=minAdm) is load-bearing.

## The DESIGN under review (Route A — decorated (S,J) ledger, ONE peel of chain M at cut t)
STEP 1 (Γ-atom). Integrate Γ pointwise via the banked Γ-atom (good cells: c'>ab/2, rank Q_b=b, w>0) or the bounded branch (c'≤ab/2 or rank-deficient). This peels the front Γ-block (charge ab = peelCharge, threshold ab/2) and emits the residual R(A',x) = det(Q_bQ_bᵀ)^{−a/2}·(w + frobSq(C·Q̃ₚ(I−P_{Q_b})))^{−(c'−ab/2)}.
STEP 2 (finite chart cover). Cover the (A',x) box by the pivot-chart / rank flag of Q_b (rank r = 0..b). On rank r=b: Γ-atom applies. On r<b: integrate the ar active Γ-directions, keep the kernel in its bounded box, recurse the rank flag. (Cover-derisk: transition Jacobian = 1 on the flag seam; det-Gram weight handled by Cauchy–Binet as a TOOL.)
STEP 3 (JOINT corner resolution of {w=0}/rank-deficiency — the crux). The residual R couples the det-Gram weight det(Q_bQ_bᵀ)^{−a/2} and the shifted core, BOTH functions of the SHARED tail product (Q_b, Q̃ₚ share Z=A'₂···). Resolve them JOINTLY by the (S,J) corner blow-up (route S): the corank-block radial u₀ and the boundary-row radial u₁ coupled (u₁=u₀τ), NOT as independent divisors, NOT via a symmetric compound weight, NOT via marginals. The coupled corner carries the loss to the monomial form ∑ᵢ(∏|u_ℓ|^{e_iℓ})² (the ledger's SJSupport), landing on sjLoss_terminal. The accumulated Jacobian/divisor charges ADD to minAdm(M) (peelCharge from u₀'s block + the deeper contribution).
STEP 4 (bottom). The deeper product M₂···M_last is the reduced chain: closed by hIH(redChain t M) at threshold c'−½peelCharge < ½minAdm(redChain) [charge shift]. For the leaf (single tail matrix), sjLoss_terminal closes directly. Charges ADD: peelCharge + minAdm(redChain) = minAdm(M).

## What I need from you (adversarial, ranked)
</task>

<output_contract>
Answer these, each with a clear VERDICT (sound / incomplete / wrong) + the sharpest reason. Rank by how likely each is to sink the design. Be concrete; give the cheapest discriminating check for any doubt.

Q1 (charges-ADD, general widths). The anchor gives 3+2+1=6→7/2 for (3,3,3,4). Does the corner-blow-up Jacobian power equal exactly (peelCharge + minAdm(redChain) − 1) = minAdm(M)−1 for GENERAL (a,b,t) and general redChain, so the terminal ∫|u₀|^{(minAdm−1)−2c'}du₀ gives threshold ½minAdm? Or does the geometric corner charge only match the arithmetic minAdm recursion at special widths? Where could the geometric Jacobian count and the arithmetic peelCharge+minAdm(redChain) DIVERGE?

Q2 (the joint corner vs the recursion boundary). STEP 3 resolves the shared-tail coupling by a JOINT corner blow-up to sjLoss_terminal, but STEP 4 hands the deeper product to hIH(redChain) (a PLAIN, undecorated box integral). Is this consistent? Specifically: after the Γ-atom emits det(Q_bQ_bᵀ)^{−a/2}, can the deeper integral honestly be handed to the PLAIN hIH, or must the det-Gram weight be carried INTO the reduced chain (a decorated IH) — i.e. does the plain hIH(redChain) suffer the zero-slack Hölder failure that killed the naive route? Is the corner blow-up (STEP 3) supposed to FULLY discharge the det-Gram decoration BEFORE STEP 4, and is that actually possible in one peel?

Q3 (chart cover finiteness/completeness). Is the rank-flag / pivot-chart cover of the (A',x) box genuinely FINITE and COMPLETE (every point in some chart, seams null, transition Jacobian controlled)? Where could a chart be missing, or the cover be infinite, or a seam carry a divergence the design ignores? (The corank cells INCLUDE {det = 0}; a clean cast with Jacobian |det M|^{−k} is non-integrable there — is the design's rank-flag recursion the correct fix, or does it also secretly use a non-integrable cast?)

Q4 ({w=0} joint density faithfulness). The design claims the coupled corner (route S) captures the joint flag-tube μ≍t₂³t₃log and avoids the marginal undershoot. Is the corner-blow-up resolution PROVABLY equivalent to (or dominating) the joint-density estimate, or is there a regime where the corner coordinates miss a piece of the {w=0} neighbourhood that the joint density catches (or vice versa)? Is the "log" (tie multiplicity) harmless in the corner picture as claimed?

Q5 (the fatal hole, if any). What is the single most likely reason this ONE-peel design does NOT close I<∞ for all c'<½minAdm(M) at general widths? Name it and give the cheapest test.
</output_contract>

<grounding_rules>
Distinguish DERIVED (you computed it) from INFERRED (plausible but unchecked) explicitly on every claim. Do not invent Mathlib lemmas. If a step is sound, say so plainly; if you cannot determine soundness without a computation, say exactly which computation. The anchor numbers ((3,3,3,4): 7/2, joint density t₂³t₃log, corner 3+2+1=6) are decorrelated-verified — you may assume them; your job is the GENERALISATION and the one-peel architecture, not re-deriving the anchor.
</grounding_rules>
