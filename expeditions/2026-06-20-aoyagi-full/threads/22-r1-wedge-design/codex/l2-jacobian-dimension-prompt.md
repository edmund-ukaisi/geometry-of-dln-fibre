<task>
I am formalising (Lean) the L=2 (3,3,4) RLCT lower-bound box-divergence via a single weighted radial blow-up, and I have hit a DIMENSION/JACOBIAN tension that I need adjudicated. This is a MATH soundness question about the construction, not Lean syntax.

## Setup
- Flat space: Fin 21 → ℝ (21 = 3·3 + 3·4 entries of C1:3×3, C2:3×4).
- Loss F = ‖C1·C2‖²_F. minAdm = 8. Need: ∫_{box [-ε,ε]^21} |F|^{-c'} = ⊤ for c' ≥ 4.
- The proven leaf atom: a weighted-blow-up chart φ on Fin 21 with F∘φ = (monomial)·U, U two-sided-bounded (c₀ ≤ U ≤ C) on the chart box, and Jacobian |det Dφ| = u^{a}, reduces to ∫ u^{a - 2k c'} = ⊤ when a - 2k c' ≤ -1. With the binding axis (k=1) and a = minAdm-1 = 7, at c'=4: 7 - 8 = -1. ⊤. ✓
- pivotBlowupOn(active, p): pivot coord p ↦ x_p (=u), active coords j≠p ↦ x_p·x_j, ALL OTHER coords (spectators) ↦ x_j (FREE, unchanged). Jacobian = (x_p)^(|active|-1). Spectators are integrated freely over the box.

## The cert's EXACT construction (sympy-verified)
C1 = [[1,0,0],[0,u·g0,u·g1],[0,u·g2,u·g3]], C2=[[u·g4,u·g5,u·g6,u·g7],[g8..g11],[g12..g15]].
Then F = u²·U EXACTLY (pure degree-2 in u), U = Σ_j(g[4+j])² + ‖D̄·S‖² ≥ ¼ on a slice.
Here the 8 u-scaled entries = C1's bottom-right 2×2 (4) + C2's top row (4). minAdm=8, Jacobian u^7.
CRUCIALLY: C1's first row and first column are FIXED to (1,0,0) — i.e. 5 entries are CONSTANTS: C1(0,0)=1, C1(0,1)=C1(0,2)=C1(1,0)=C1(2,0)=0.

## THE TENSION
To get F = u²·U EXACTLY (every product entry O(u)), every term C1[i,k]·C2[k,j] must be O(u):
- C2[0,j] is u-scaled (top row active); C2[1,j],C2[2,j] are O(1) (bottom rows, free spectators).
- So for k=1,2: need C1[i,1],C1[i,2] = O(u) (active). For k=0: C2[0,j]=O(u), so C1[i,0] can be free.
- Row 0: P[0,j] = C1[0,0]·C2[0,j] + C1[0,1]·C2[1,j] + C1[0,2]·C2[2,j]. If C1(0,1),C1(0,2) are FREE spectators (not scaled, not zero), then C1[0,1]·C2[1,j] = free·free = O(1) — F gets an O(1) part, NOT u²·U.

So the EXACT factorization REQUIRES C1(0,1),C1(0,2) [and by symmetry C1(1,0),C1(2,0)] to be either u-SCALED (active) or ZERO.
- If I make C1 columns 1,2 fully active (6 entries) + C2 top row (4) = 10 active → Jacobian u^9 → exponent 9-8 = +1 > -1 → CONVERGES, no divergence.
- If I FIX C1(0,1),C1(0,2),C1(1,0),C1(2,0) to ZERO and C1(0,0) to 1: that fixes 5 of 21 coords to constants → the chart image is 16-dimensional (measure zero in 21-dim) → ∫ over it = 0, not ⊤.

The pivotBlowupOn spectators are FREE, so the 5 special C1 entries float over [-ε,ε], breaking the exact factorization. I cannot fix them (kills dimension) nor make them active (kills Jacobian).

## My questions
1. Is the construction actually SOUND as a 21-dim box divergence, or does the minAdm=8 Jacobian only arise on a lower-dim slice (making the 21-dim claim FALSE)? I.e. is ∫_{[-ε,ε]^21}|F|^{-c'} genuinely ⊤ at c'=4, or is that an over-claim and the true 21-dim RLCT exponent different?
2. If sound: what is the CORRECT chart on the full 21 dims? Specifically, how do the 5 "constrained" C1 entries get handled so that (a) F∘φ factors as monomial·(two-sided-bounded U), (b) the Jacobian is u^7 not u^9? Is the resolution that the C1 column-0 entries (1,0),(2,0) and C1(0,1),(0,2) should be a DIFFERENT kind of chart coordinate — e.g. the blow-up is NOT a single pivotBlowupOn but the radial coord u times a chart where these enter U, with a Jacobian contribution I'm miscounting?
3. Concretely: does the divergence integral genuinely live on all 21 dims with the 13 non-active coords as free spectators contributing a FINITE factor, while the 8 active (incl pivot) carry the u^7 Jacobian and the u²-loss — i.e. is F = u²·U with U two-sided-bounded achievable with the 5 special C1 coords FREE if I instead choose a smarter active set / pivot, OR by a change of the chart that absorbs them into U? Or must some of those 13 be fixed, reducing to a <21-dim integral (which then needs a Fubini argument that the remaining-coords integral is a positive finite constant, NOT that the whole thing is measure-zero)?
4. Decisive check: for the (2,2,2) analog (Fin 8, minAdm=3, the PROVEN phiUnit chart), how many coords are active vs spectator, and are ANY coords fixed to constants? If phiUnit has NO fixed coords and all 8 are either active or free-spectator-into-U, what is the structural difference from (3,3,4) that I'm missing — does (3,3,4) genuinely also have all-free-or-active with NO fixed coords?
</task>

<output_contract>
1. VERDICT: is ∫_{[-ε,ε]^21}|F|^{-c'}=⊤ at c'=4 TRUE (sound 21-dim claim) or is the minAdm=8 Jacobian a lower-dim artifact (over-claim)? One line + the decisive reason.
2. The CORRECT chart structure on 21 dims (active set, pivot, how the 5 special C1 coords are handled), or a clear statement that some coords must be fixed + how the resulting lower-dim integral still gives ⊤ (Fubini: remaining integral = positive finite const).
3. The resolution of the Jacobian count (why u^7 not u^9, exactly which 8 coords are active).
4. The (2,2,2) phiUnit structural answer to Q4 — does it fix coords, and the structural analogy/disanalogy to (3,3,4).
Under ~500 words. Flag inference vs certainty. If the 21-dim claim is an over-claim, SAY SO plainly — I must not formalise a false statement.
</output_contract>

<grounding_rules>
This is a pure math-soundness adjudication. Be rigorous about dimension counting and the Jacobian of a blow-up. The honest answer may be "the construction needs a Fubini split: fix/integrate the spectators, the active block carries the divergence." Do NOT rationalise a false 21-dim claim. If the divergence genuinely lives on a lower-dim slice, the correct Lean statement integrates over the FULL box but the divergence comes from a positive-measure TUBE around the achiever curve where U is two-sided bounded — clarify whether that tube is genuinely positive-measure in 21-dim or measure-zero.
</grounding_rules>
