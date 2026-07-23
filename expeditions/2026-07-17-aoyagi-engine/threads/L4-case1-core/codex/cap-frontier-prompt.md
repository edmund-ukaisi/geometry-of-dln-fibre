<task>
Red-team two reductions I made about a Lean formalisation lemma. Tell me whether each reduction is
CORRECT or has a flaw. Do NOT try to guess what I want to conclude — just check the logic + algebra.
</task>

<context>
We formalise a recursive resolution-of-singularities fold. Fixed definitions (verbatim shape):

- A flat coordinate `k` decodes to `(layer L, row, col)`; `row ∈ Fin d[L+1]`, `col ∈ Fin d[L]`.
- `layerCoords(ℓ)` = { coords with layer = ℓ } (the full matrix layer).
- `widthMinUpto(ℓ)` = min(d[0], …, d[ℓ]).
- `blockCoords(ℓ)` = { coords with layer = ℓ AND col < widthMinUpto(ℓ) }  (caps the col axis).
- `supportAt(S, J)` = if J = 0 then blockCoords(S) else if S+1 < N then layerCoords(S+1) else ∅.
- `foldResid` is a residual family carried down a tree path. One append edge maps
  child_resid(u) = parent_resid( Φ(u) ), where per δ = [parent.cleared = 0]:
    * δ=1: Φ(u)[k] = (1 if k = pivot else shear(u)[k])          -- "strict transform"
    * δ=0: Φ(u)[k] = blockBlowupMap(center, pivot, shear(u))[k]
      blockBlowupMap(S,p,w)[k] = (w[p] if k=p ; w[p]*w[k] if k∈S ; w[k] otherwise).
- State transitions: an append (case2/case12) sends (S,J) → (S,J+1); a "rollover" sends (S,J) → (S+1,0).
- For a rollover edge the construction pins center = ∅ and shear = identity.
- `Deg1SupportedSlot(resid, S_supp, ...)` requires: ∃ continuous coefficients c with
  resid(u) = Σ_{i ∈ S_supp} c_i(u) · u_i  (i.e. resid ∈ ⟨ coords in S_supp ⟩ as a continuous combination),
  plus a per-layer degree ≤ 1 condition.

The lemma under scrutiny (`realBranch_appendResidDescent`): from the PARENT hypothesis
"resid_parent is Deg1SupportedSlot on supportAt(parent)", conclude
"resid_child is a continuous combination Σ_{i ∈ supportAt(child)} c_i · u_i".
</context>

<claims_to_check>
CLAIM 1 (about a rollover edge). For a rollover, center = ∅ and shear = id, so
Φ(u)[k] = blockBlowupMap(∅, pivot, u)[k] = u[k] for every k (∅ has no non-pivot members and the pivot
maps to u[pivot]). Hence child_resid = parent_resid exactly (the rollover leaves the residual
unchanged). Therefore the child's required support supportAt(S+1, 0) = blockCoords(S+1) must be
satisfied by the SAME function that the parent carried on supportAt(S, J≥1) = layerCoords(S+1). Since
blockCoords(S+1) ⊆ layerCoords(S+1) and the inclusion is STRICT whenever widthMinUpto(S+1) < d[S+1],
the child conclusion is strictly stronger than the parent hypothesis on such a "wide" case.
Is CLAIM 1 (rollover ⇒ child_resid = parent_resid, and child-support strictly narrower) correct?

CLAIM 2 (about a δ=1 append edge). The pivot coordinate is a member of supportAt(parent) = blockCoords(S)
(pivot = diagonal corner (S,0,0), col 0 < widthMinUpto(S) since all d ≥ 1). Consider a parent residual
equal to the single coordinate function  resid_parent(w) = w[pivot].  This satisfies
Deg1SupportedSlot on blockCoords(S) (take c_pivot ≡ 1, others 0; per-layer degree 1). Its δ=1 child is
child_resid(u) = resid_parent(Φ(u)) = Φ(u)[pivot] = 1 (constant, since δ=1 maps pivot → 1). A constant 1
is NOT of the form Σ_{i ∈ supportAt(child)} c_i(u)·u_i (evaluate at u=0: LHS 1, RHS 0). Hence the parent
hypothesis Deg1SupportedSlot(supportAt parent) does NOT entail the child conclusion — i.e. the lemma
cannot be proved treating resid_parent as an arbitrary black box satisfying the hypothesis; a proof
must use more than the hypothesis (e.g. the concrete recursion).
Is CLAIM 2 (the black-box counterexample to "hypothesis ⇒ conclusion") correct?
</claims_to_check>

<output_contract>
For each claim: VALID / INVALID, with the specific algebraic step that is right or wrong. If a claim is
INVALID, give the precise flaw (a mis-stated definition, a missed case, a wrong evaluation). Then state,
independently, whether "supportAt(fresh rollover child) = blockCoords(S+1)" can hold for a residual that
genuinely reads an out-of-cap column of layer S+1 — a yes/no with reason. Do not speculate about intent.
</output_contract>

<grounding_rules>
Reason only from the definitions given. Treat blockBlowupMap, the δ-branches, and the state transitions
as exact. Continuous = the coefficients c_i may be any continuous functions (in particular the constant 1).
</grounding_rules>
