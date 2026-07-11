<task>
Adjudicate the ARCHITECTURE of the inductive step of a matrix-integral finiteness proof. Two candidate
routes; pick decisively and stress-test the winner. Exact reasoning; I withhold my lean.
</task>

<setup>
Goal: ∀ layer-chains M (length ≥2 nodes), the box integral I(M,c') = ∫_{param box} frobSq(prod M)^{-c'}
is < ∞ for c' < ½·minAdm(M). Proved by STRONG INDUCTION ON CHAIN LENGTH (redChain = one node shorter).

The inductive STEP peels the leading layer at the binding cut u★ (minAdm M = ab + minAdm(redChain u★ M),
a=M0−u★, b=M1−u★, both ≥1 so minAdm M > ab). One peel: pivot-chart + Schur-split + free the corank block
Γ (a×b), then integrate Γ. The banked corank atom gives (for c'>ab/2, Q_b=corank rows of the deep factor
of full row rank):
   ∫_Γ (freedSchurLoss)^{-c'} = det(Q_bQ_bᵀ)^{-a/2}·C·(reduced core H)^{-(c'−ab/2)},
landing on redChain at exponent c'−ab/2 < ½·minAdm(redChain) (strict). PROVEN LAST ROUND (decorrelated):
the persistent weight det(Q_bQ_bᵀ)^{-a/2} is NOT absorbed by the plain redChain box integrand (scaling
test Q_b=εR ⟹ det^{-a/2}=ε^{-ab}·(…)→∞ with H fixed), and it must not be scalar-split from H (they share
the deep rank-drop divisor; a scalar split takes the MIN of charges = RLCT-collapse, correct resolution
ADDS the charges to reach ½·minAdm). So the plain box IH is insufficient.

A carrier already exists (a "decoration"): a structure SJDecoration on M with a decorated integral
Dec(δ, c') and a predicate DecoratedBoxThresholdFinite(δ) := Dec(δ,c')<∞ for c'<½minAdm(M); the TRIVIAL
decoration equals the plain box (banked iff). A "radialAttach" op multiplies the decorated loss by u₀²
(raising the exceptional-coordinate count by 1) is banked, with its per-divisor Morse threshold. The
generic strong-induction-on-arity driver is banked for the PLAIN predicate.

Two candidate architectures:
(A) DECORATED double induction. Strengthen the step to: (∀ shorter M', ∀ decoration δ',
    DecoratedBoxThresholdFinite δ' M') ⟹ (∀ decoration δ, DecoratedBoxThresholdFinite δ M). The per-peel
    maps a decoration δ on M to a decoration δ_reduced on redChain (the carrier ABSORBS the det/shared-
    divisor weight), closed by the decorated IH at shorter arity.
(B) A STANDALONE joint anisotropic lemma: prove ∫ det(Q_bQ_bᵀ)^{-a/2}·H^{-(c'−ab/2)} < ∞ directly, as
    its own result, feeding the plain recursion.
</setup>

<questions>
Q1 (A vs B — decide). Is (B) genuinely standalone, or does the standalone joint-weighted lemma for
   redChain reduce to ANOTHER peel of redChain (the det weight = a corank coupling of a deeper layer),
   i.e. collapse into (A)? Decide which architecture is primitive. Reason about whether the det weight at
   level k is "the same kind of object" as the corank coupling produced at level k+1's peel.

Q2 (the ∀-decoration quantifier — is it too strong?). Route (A) quantifies "∀ decoration δ". Is EVERY
   decoration on the base (2-node free-matrix) chain finite below threshold, or only the decorations that
   the peel-recursion actually PRODUCES? If ∀δ is too strong (some pathological δ diverges), the predicate
   must be restricted to the reachable decoration class. Which is correct, and what pins the class (the
   accumulated Jacobian exponents jac and the shared-divisor carrier)?

Q3 (charges ADD across levels — verify the mechanism). The coupling→½minAdm is claimed to be realised by
   "one radialAttach (u₀²) per level + the per-level exponent shift c'↦c'−½·peelCharge", the Jacobian
   powers ADDING onto ONE shared terminal divisor while the loss stays order 2. Verify this reaches
   ½·minAdm and not the min-caricature: with peelCharges p_1,...,p_m along a root-to-leaf path summing to
   minAdm, and one u₀²-divisor per level, does the terminal monomial ∏|u_k|^{h_k}·(∏u_k²)^{-c'} have
   threshold min_k (h_k+1)/2 = ½minAdm (charges add), or does a shared divisor force a single
   (Σh_k+1)/2? Which, and does the A2-rank-drop (deep factor degenerates) need an EXPLICIT extra stratum
   (not an a.e.-drop) to keep the units bounded below?
</questions>

<output_contract>
For each Q1–Q3: direct answer + "FACT" vs "INFERENCE". End with a VERDICT: is architecture (A) the right
primitive, is the ∀-decoration predicate correct or must it be a reachable-class predicate, and is the
per-peel charge-addition mechanism sound to ½minAdm — or does a sub-piece remain a genuine obstruction
(isolate it precisely).
</output_contract>

<grounding_rules>
Exact algebra / induction-structure reasoning. Distinguish "the atom majorant" from "the true integral".
If (A) needs a restricted decoration class, say exactly what constrains it. If the charge-addition can
silently degrade to the min at the shared divisor, say where.
