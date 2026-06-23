<task>
I am a Lean formaliser in a DLN-RLCT formalisation project. I was assigned to build the "blow-up
coordinate bridge": prove that the deep-linear-network square-Frobenius loss `dlnLoss M 0`, composed
with a banked blow-up chart `pivotBlowupOn`, presents in a "Schur block form" so that a banked
SQUEEZE toolkit (`IsSchurStraightenSqueeze` / `schur_straighten_squeeze_exists`) can conclude a
per-node RLCT split `rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn(G²) 0`.

I believe the assignment rests on a FALSE PREMISE — that the banked blow-up atlas `pivotBlowupOn`
produces the additive Schur form the squeeze toolkit consumes. I want you to red-team that judgment.
Tell me if I am wrong.

THE TWO NORMAL FORMS (the crux):

(A) What the SQUEEZE toolkit's hypothesis `hnode` demands (the additive Schur form). It asks for a
    function `flatCore : (Fin nReg → ℝ) × Y → ℝ` and a neighbourhood of `(0,0)` on which:
        flatCore w = (∑_j (w.1 j)²) + (∑_{i,j} (bcol(w) i · w.1 j + SΓ(w) i j)²)
        G(w.2)² = ∑_{i,j} (SΓ(w) i j)²
        ∑_i (bcol(w) i)² ≤ T²
    i.e. flatCore = (regular squares ∑E²) + (Schur block ‖b·E + SΓ‖²), a SUM. The squeeze is then
        c₁·Φ ≤ flatCore ≤ c₂·Φ,  Φ = ∑E² + ‖SΓ‖²,
    with c₁,c₂ POSITIVE CONSTANTS (no Jacobian, no change of variables). This yields an ADDITIVE
    RLCT split nReg/2 + rlctAtOn(G²).

(B) What the BANKED blow-up chart actually produces for the 2-factor loss. The banked theorem
    `myF222_step1A` (for the (2,2,2) loss `myF222 = ‖A·B‖²`, A,B 2×2, flat coords x0..x7) is:
        myF222(step1A y) = y0² · ( (y4 + y1·y6)² + (y5 + y1·y7)² + (y2·y4+y3·y6)² + (y2·y5+y3·y7)² )
    where step1A is the a00-pivot blow-up (a00=y0, a01=y0·y1, a10=y0·y2, a11=y0·y3, B passes through).
    This is a PRODUCT: (pivot)² · (residual Q). It feeds the project's `monomialThreshold` cover lane
    (`g5_pivotNode`: ∫_U g = Σ_p ∫ |det φ'|·g∘φ, Jacobian weight |y0|³, RLCT = ⨅ monomialThreshold).
    The banked (2,2,2) RLCT result `rlctAtOn myF222 0 = ⨅ monomialThreshold(d)(k)(h) = 3/2` is computed
    ENTIRELY through this monomial/cover route, NOT through any additive squeeze.

MY CLAIM: form (B) `pivot² · residual` (a product, monomial Jacobian, ⨅-of-thresholds) and form (A)
`∑E² + ‖bE+SΓ‖²` (a sum, positive-constant squeeze, additive split) are DIFFERENT normal forms from
DIFFERENT resolution routes. The blow-up chart `pivotBlowupOn` realises (B). Nothing in the banked
atlas presents `dlnLoss M 0 ∘ pivotBlowupOn` in the additive form (A). Therefore I cannot discharge
the toolkit's `hnode` from the blow-up construction — the coordinate bridge as specified does not
compose. The squeeze toolkit is a DIFFERENT (parallel, not downstream) resolution strategy from the
blow-up atlas, and gluing them as "blow-up THEN squeeze" is not supported by what is banked.

POSSIBLE HOLES IN MY CLAIM (check each):
1. Could `pivot² · Q` be rewritten as an additive `∑E² + ‖bE+SΓ‖²` near 0 after some FURTHER step
   (e.g. a Schur/Lemma-2 regular change of variables) that I am missing, so that (B) feeds (A)?
2. Is the squeeze datum meant to apply to the RESIDUAL Q (post-blow-up, post-pivot-strip), not to
   `dlnLoss M 0` directly — i.e. is `flatCore` supposed to be Q, not the full loss? If so, does the
   `nReg` regular-square block ∑(w.1 j)² come from the blow-up pivot directions or from Q's own
   structure?
3. Is there a reading where the squeeze and the monomial route give the SAME per-node recursion and I
   am wrong that they diverge?

CONTEXT NUMBERS: the (2,2,2) verified RLCT is 3/2. A measure-preserving (det-1) recursion that
conserves dimension telescopes to ambient/2 = 4 ≠ 3/2 — the project explicitly notes the clean
det-1-chart route is FALSE for this reason, and the monomial blow-up is what supplies the gap. The
squeeze route claims to be NOT measure-preserving (positive constants, not a unit→1 chart), so it is
not obviously caught by that argument — but I want you to check whether the squeeze route, applied
node-by-node, actually reproduces 3/2 or whether it is itself unsound/mis-scoped.
</task>

<output_contract>
Answer in 4 short sections, terse:
1. VERDICT: Is my STOP judgment correct (the blow-up atlas does NOT determine the additive Schur
   form, so the coordinate bridge as specified does not compose)? YES / NO / PARTIAL.
2. THE HOLES: address holes 1, 2, 3 above — for each, is it a real escape route or not, and why.
3. IF I AM WRONG: the single concrete identity or construction I would need to find/prove to make
   (B) feed (A). Be specific (what equals what, near 0).
4. IF I AM RIGHT: what is the minimal honest thing to surface to the team-lead — is the squeeze
   toolkit salvageable as a parallel route, or is `hnode` simply not dischargeable from the atlas?
</output_contract>

<grounding_rules>
You do NOT have the repo. Reason from the two explicit normal forms (A) and (B) and the algebra given.
Flag clearly when you are INFERRING vs when the algebra forces a conclusion. Do not invent banked
lemmas. If you cannot decide a hole from the given algebra, say so and name the one fact that would
decide it.
</grounding_rules>
