<task>
Lean 4 / Mathlib formalisation scoping question for a research expedition (Aoyagi/DLN RLCT).
NEUTRAL truth-value question: is a specific step a one-tide composition of banked pieces, or a
multi-tide new measure-theory construction? My leaning is WITHHELD; give your independent read.

## The target
Prove, for every width vector `M : Fin (L+1) → ℕ`, the finiteness
`RouteMBoxThresholdFinite M`:
    ∀ c' : NNReal, (c':ℝ) < (minAdm M)/2  →  ∫⁻_{A ∈ box} frobSq(prod M A)^{−c'} < ⊤,
where `prod M A = A_0 · A_1 · … · A_{L-1}` is a product of layer matrices (A_s : M_s × M_{s+1}),
`box` = all entries in [−1,1], `frobSq` = squared Frobenius norm, and `minAdm M` is a combinatorial
codimension satisfying the layer-peel recursion
    minAdm M = min_{t ≤ min(M_0,M_1)} [ (M_0−t)(M_1−t) + minAdm(redChain t M) ],
`redChain t M = (t, M_2, …, M_L)` (one fewer layer).

## What is BANKED (all sorry-free, axiom-clean)
- `corankStep` : POINTWISE algebra. For a corank block Δ = fromBlocks A B C D (A invertible t×t) and
  any downstream Q: `frobSq((u•Δ)·Q) = u²·(frobSq(A·Q̃) + frobSq(C·Q̃ + Γ·Q_b))`, Q̃ = Q_p + A⁻¹B·Q_b,
  Γ = D − C A⁻¹ B (Schur complement, produced by UNIT det-1 elimination — no Gram determinant).
- Isotropic block peels (measure-theoretic): for a FREE block Δ entering via its OWN Frobenius energy,
  `∫_z ∫_{Δ∈box}(frobSq Δ + W z)^{−c'} dΔ dz < ⊤`  when c' < pq/2, μZ<∞, W≥0  (Morse terminal);
  and `∫_z ∫_{Δ∈box}(frobSq Δ + W z)^{−c'} ≤ Cresid·∫_z (W z)^{−(c'−pq/2)}` when c' > pq/2, W>0
  (the EXPONENT-SHIFT peel c' ↦ c' − ½pq). NOTE these are for `frobSq Δ` (isotropic), NOT `frobSq(Δ·Q_b)`.
- Terminal monomial finiteness: `∫_{[0,1]^d}(∏|u_ℓ|^{h_ℓ})(sjLoss e u)^{−c'} < ⊤` below the per-axis
  monomial threshold, where sjLoss = ∑(monomials in u)², with the shared-divisor `min_i` ledger.
- Peel-charge soundness (combinatorial): `minAdm M ≤ (M_0−t)(M_1−t) + minAdm(redChain t M)`, hence the
  ℝ shift `½minAdm M − ½(M_0−t)(M_1−t) ≤ ½minAdm(redChain t M)`.
- The box-peel cover: `∫_{box} frobSq(prod M A)^{−c'} ≤ ∑_{t,ρ,κ} ∫_{A'∈box(tail)} ∫_{A_0∈box∩pivotChart}
  frobSq(A_0·prod(tail)A')^{−c'}` (pure measure cover, closed).

## The STEP in question (call it "peelStep soundness")
Reduce each per-chart integral `∫_{A'} ∫_{A_0∈box∩pivotChart} frobSq(A_0·Q)^{−c'}` (Q = prod(tail)A',
A_0 has an invertible t×t pivot minor on the chart) to a STRICTLY-shorter chain integral times a finite
radial factor, PRODUCING the exponent shift c' ↦ c' − ½(M_0−t)(M_1−t), so the strong IH
(`RouteMBoxThresholdFinite` for the shorter chain redChain t M at the shifted exponent) closes it.

Two facts I have established about the routes:
(1) The Gram change-of-variables `Γ ↦ Γ·Q_b` (Jacobian det(Q_b Q_bᵀ)^{−p/2}) — the "atom route" — is
    a FALSE WALL: det(Q_b Q_bᵀ) is a genuinely non-coordinate (Plücker-minor) ideal (dense-torus
    rank-drop, exact Gröbner), which char-0 embedded resolution could handle but Mathlib lacks.
(2) The "pure route" (Aoyagi §blowup): keep Γ a chart coordinate, blow up the residual-block origin
    {Γ=0} (coordinate radial u, `Γ = u•Γ'`), det-1 unit Schur-clear, DESCEND on the tail. sympy-verified
    end-to-end on (3,3,3,4): reaches normal-crossing monomials with coordinate centers only, Gram-det
    never forms. The radial's Jacobian |u|^{charge−1} produces the exponent shift.
    BUT the pure route interleaves (a) resolving the pivot energy frobSq(A·Q̃) as a shorter-chain
    (top-t-rows) product AND (b) blowing up the corank block — Aoyagi's (S,J) double recursion.

## The precise question
Is "peelStep soundness" — the measure-theoretic reduction that maps the per-chart integral to a
strictly-shorter-chain integral at the shifted exponent — a ONE-TIDE composition of the banked pieces
above (pointwise `corankStep` + isotropic block peels + monomial terminal + charge soundness), or is it
a genuinely-NEW multi-tide measure-theory construction (a nonlinear blow-up change-of-variables with a
monomial Jacobian on ℝ^{pq}, plus the pivot/corank double recursion interleaving), NOT reducible to the
banked pieces?

Key sub-question: the banked isotropic peels handle `frobSq Δ` (Δ's OWN energy). The chart loss has the
corank block as `frobSq(C·Q̃ + Γ·Q_b)` — ANISOTROPIC (Γ coupled to Q_b) AND with an additive cross
term C·Q̃. Can the ANISOTROPY + the CROSS TERM be removed by a composition of the banked pieces (a
measure-preserving map + the pointwise corankStep), or does removing them require either the Gram CoV
(false wall) or a genuinely-new blow-up-Jacobian CoV that is NOT banked?
</task>

<output_contract>
1. VERDICT (one line): "one-tide composition" OR "multi-tide new construction".
2. The single load-bearing reason (≤4 sentences): name the exact measure-theoretic object that is or is
   not banked.
3. If "multi-tide new construction": name the ONE most-central unbanked sub-brick precisely (what
   measure-theory lemma / change-of-variables must be built), and estimate whether it is BOUNDED
   (coordinate centers, standard Mathlib CoV at scale) vs research-grade (needs a resolution theorem
   Mathlib lacks).
4. Sanity check my plan: build the pure-route recursion carrier (structure + data transform + base +
   skeleton, all sorry-free) with the peelStep soundness as a NAMED Prop-hypothesis contract (like the
   existing sorry-free wrapper `routeMBoxThresholdFinite_of_step` consuming `SJStepHyp`), NOT a bare
   sorry. Is this genuine bedrock progress, or is it "laundering" one named contract into another
   equivalent one? Answer in ≤3 sentences.
</output_contract>

<grounding_rules>
State plainly what is INFERENCE vs what you can derive. You do not have the Lean source; reason from the
mathematical structure I gave. If you cannot determine one-tide vs multi-tide from what I gave, say what
one additional fact would decide it.
</grounding_rules>
