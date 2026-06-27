<task>
You are an independent fidelity reviewer of a Lean 4 + Mathlib formalisation. I am NOT asking you to
write Lean. I am asking you to judge whether the Lean statements faithfully capture the informal claim,
and whether any definition secretly TRIVIALIZES (makes vacuous / tautological) the headline.

CONTEXT. Deep linear networks: a parameter tuple is a composable matrix chain `A^(0)·…·A^(L-1)`. The
square-Frobenius loss at the zero target is `dlnLoss M 0 A = ∑_ij (prod M A)_ij^2` (prod = the chain
product). `paramsEquivFlat M` is a measure-preserving equiv `Params M ≃ (Fin N → ℝ)` (N = total #params).
`routeMCore M x := dlnLoss M 0 ((paramsEquivFlat M).symm x)` — the loss in flat coordinates.

THE HEADLINE being formalised (an atom currently a `sorry` in general): for c' ≥ ½·minAdm(M) and every
ε>0, the box integral `∫⁻_{[-ε,ε]^N} |routeMCore M x|^{-c'} dx = ⊤` (diverges). minAdm(M) is the
achiever codimension. The deliverable discharges this for the CLEAN class (extra hypotheses).

THE MECHANISM. A single radial blow-up of the deepest layer:
  `cleanPhi u := pivotBlowupOn (deepestCoords M hL) (deepestPivot M hL hne) u`
where `pivotBlowupOn active p x i = (if i = p then x p else if i ∈ active then x p * x i else x i)`,
`deepestCoords M hL` = the flat coords whose FlatIdx layer is the deepest (L-1), `deepestPivot = hne.choose`
(a chosen element of deepestCoords, with `deepestPivot_mem : deepestPivot ∈ deepestCoords`).

KEY LEMMAS (all proven sorry-free; #print axioms = [propext, Classical.choice, Quot.sound] for the pieces,
+ monomial_rlct only on the headline):

(1) RATE: `routeMCore M (cleanPhi u) = (u p)^2 * dlnLoss M 0 (unblownParams u)` where
    `unblownParams u := (paramsEquivFlat M).symm (unblownFlat u)`,
    `unblownFlat u c := if c = p then 1 else u c` (pivot coord set to 1, rest of u kept).
    Proof chain: cleanParams = scaleLayer (u p) (deepLayer) unblownParams (deepest layer scaled by u_p,
    earlier layers untouched), then dlnLoss_homogeneous_layer: dlnLoss 0 (scaleLayer c s A) = c^2 · dlnLoss 0 A.

(2) DET: `|det (pivotBlowupOnDeriv active p u)| = |u p|^(active.card - 1)`, and
    `deepestCoords.card = minAdm M` (for clean M), so det = |u p|^(minAdm-1).

(3) UNIT NONVANISHING: U(u) := dlnLoss M 0 (unblownParams u) = eval u (UPolyClean), UPolyClean a real
    MvPolynomial, shown ≠ 0 by evaluating at the all-ones point u≡1: there unblownParams = allOnesParams
    (every matrix entry 1, INCLUDING the pivot slot since the if-branch gives 1), and the all-ones chain
    product has positive (0,0) entry = ∏(inner widths) > 0, so dlnLoss > 0. Then {U=0} is Lebesgue-null.

(4) The threshold: the binding pivot axis has (loss-base exponent k_p, jacobian exponent h_p) = (1, minAdm-1),
    giving axis ratio (h_p+1)/(2 k_p) = minAdm/2. Spectator axes have k=0 (ratio ⊤). monomial_rlct (the
    cited S2 axiom) says threshold = min_j (h_j+1)/(2 k_j) = minAdm/2.

CLEAN-CLASS HYPOTHESES carried by the headline: NoInteriorBothDrop M (a chain-native "no interior
boundary drops both row and column rank" condition); deepRank M = deepRows M (clean equality);
1 ≤ minAdm M; ∀ s, 0 < M s (all widths positive); (deepestCoords M hL).Nonempty (nonempty deepest block).
NoInteriorBothDrop + clean are used ONLY to prove minAdm = deepRows·M_L (the deepestCoords.card = minAdm step).
</task>

<output_contract>
Five short sections, each a yes/no verdict + one-sentence justification:
1. RATE genuineness: is `routeMCore (cleanPhi u) = (u p)^2 · dlnLoss M 0 (unblownParams u)` a genuine
   loss factorization, or could it be a tautology/vacuous (e.g. if unblownParams = the identity decode of u,
   or if dlnLoss M 0 collapses to something trivial)?
2. THRESHOLD soundness: does (k_p,h_p)=(1,minAdm-1) ⟹ axis ratio minAdm/2 correctly realize the claimed
   ½·minAdm divergence threshold, or is there an off-by-one (e.g. should the radial exponent be minAdm or
   minAdm-2)? State the arithmetic.
3. UNIT witness honesty: is "unblownParams(1) = allOnes, all-ones chain product (0,0) entry = ∏ widths > 0"
   a correct nonvanishing argument, or does setting the PIVOT slot to 1 (rather than its u-value) make the
   witness not actually a point of the chart family / break the U ≢ 0 claim?
4. HYPOTHESIS necessity: are NoInteriorBothDrop, clean equality, all-widths-positive, nonempty-deepest each
   load-bearing (could any be dropped, signalling an overclaim that they are "Assumed")? Flag any that look
   removable or, conversely, INSUFFICIENT (a hidden hypothesis silently needed).
5. SCOPE honesty: the deliverable claims to discharge the atom ONLY for the clean class, with the headline
   carrying these hypotheses (not the general atom). Is there any way the listed clean hypotheses are
   secretly always-true / vacuous, which would mean the "clean only" scoping is misleading?
</output_contract>

<grounding_rules>
Distinguish what you can VERIFY from the statements given vs what you must INFER. If a risk depends on
a definition I did not give you (e.g. exact deepestCoords filter, exact minAdm definition), say so and
state what you'd need to check. Do not invent Lean lemma names. Flag inference vs fact explicitly.
</grounding_rules>
