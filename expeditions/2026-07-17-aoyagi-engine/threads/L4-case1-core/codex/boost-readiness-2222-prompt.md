# Consult: verify case1(1)-δ=1 boost-readiness on d=(2,2,2,2), + the carried-vs-derived question

You have a read-only sandbox with sympy. BUILD and RUN an exact-algebra check, then answer the verdict. This gates a Lean formalisation's proof architecture — correctness matters more than speed.

## The object (match these fold semantics EXACTLY)

Aoyagi's resolution of `∏ C = C^(1)·C^(2)·…·C^(N)` (each `C^(k)` is `d_k × d_{k-1}`; here d=(2,2,2,2), N=3, all 2×2, entries fresh symbols). `coreGen` = the `d_N·d_0` entries of the product.

The resolution folds along a path of blow-ups. Two coordinate objects accumulate:
- `foldG` (the chart map) composes `stepMap = blockBlowupMap(center,pivot) ∘ edgeShear`, where `blockBlowupMap S p w j = (j=p ? w_p : j∈S ? w_p·w_j : w_j)`.
- `foldResid` (the residual family) = `coreGen` STRICT-TRANSFORMED: at each δ=1 edge it composes the QUOTIENT map `qm = blockBlowupCoordQuot(pivot) ∘ edgeShear`, where `blockBlowupCoordQuot p j w = (j=p ? 1 : w_j)` — i.e. the pivot coord is set to 1 (the u_pivot is divided out), other coords via the shear. So `foldResid p (u) = coreGen(qm_{e1}(…qm_{en}(u)))` along the path (NOT blockBlowupMap — the quotient removes the pivots).
- `foldB` (the dominant monomial) = `∏_edges (u_pivot)^δ ∘ pullbacks`, δ = [cleared=0].

Case-2 edge (δ=1): radial-in-pivot chart `C^(S)-block = u·C̄` with `C̄[0,0]=1`, then Q clears the pivot row (`Q=[[1,-β],[0,I]]`, β = C̄'s pivot-row tail), Schur `D' = δ_block − γβ`; the later matrix `C^(S+1)` recoordinatises by `Q^{-1}` (its pivot row only). Rollover = ledger relabel (shear=id, no blow-up).

## The (2,2,2,2) path to the target node p (I derived this; verify it)
- (S=1,J=0) case2 δ=1: clear pivot of C^(1) block → births divisor u₁₁; block 2×2.
- (S=1,J=1) case2 δ=1: clear the 1×1 Schur → births divisor u₁₂; T=(1,1).
- rollover S:1→2 (J resets to 0). b-chain now (u₁₁, u₁₁·u₁₂); layer-2 residual block = recoordinatised C^(2).
- **(S=2,J=0) case1(1) BOOST — THE TARGET EDGE.** Reuses divisor u₁₂ (born (1,1)); pivot = u₁₂'s IMMUTABLE birth corner (the layer-1 (1,1)-corner); boost center = {that pivot} ∪ {layer-2 partial block: col 0 only (runLen=1), all rows}. supportAt(parent) = the FULL layer-2 block (both cols).

The PARENT node p is the state (2,0) reached just before this boost. `foldResid p` = the residual after the two layer-1 δ=1 clears + rollover (u₁₁, u₁₂ divided out via the quotient maps).

## What to verify (exact, sympy)
Compute `foldResid p` (the residual entries as polynomials in the exceptional coords) at node p. Then, with center C = the case1(1) boost center {pivot} ∪ {layer-2 col-0 block}:
1. **A1:** each residual entry with ALL center vars set to 0 is identically 0 (no center-degree-0 part).
2. **A2:** each residual entry is jointly degree ≤ 1 in the center vars (no monomial with two center factors / a center var squared). A1+A2 ⟹ `Deg1SupportedOn C` (the boost-readiness claim).
3. **A3:** after the boost substitution `blockBlowupMap C pivot`, each residual entry is divisible by u_pivot as a polynomial (the ÷u_pivot is exact — the b-chain mechanism).

## THE HEADLINE QUESTION (this is why the check exists)
Codex earlier argued boost-readiness holds because the untouched (support∖center = layer-2 col-1) terms carry u_pivot in their non-dominant b-chain coefficient (b_i/b_1). The Lean proof will be a DERIVED induction off `IsRealBranch` (the b-chain is branch-determined), a sibling of the multiAffine stub — UNLESS the induction needs a carried strengthening. So:

> **Does boost-readiness (A1+A2) at node p FOLLOW from (a) the weaker "foldResid p is Deg1 on the FULL supportAt block" (which the invariant already carries) PLUS (b) the branch-determined b-chain structure (foldB p) — i.e. is it a self-contained real-branch consequence? Or does closing the inductive step (boost-readiness preserved at each edge type: case2 δ=1, rollover, case1(1)) genuinely require carrying boost-readiness as an extra invariant?**

Check the inductive step at each edge type on (2,2,2,2): given boost-readiness (or supportAt-Deg1) at the child, does it hold at the parent using only branch data? Report: self-contained (→ derived stub) or needs-carrying (→ forced carried conjunct), with the evidence.

## Deliverables
Return: (1) the verdict on A1/A2/A3 for (2,2,2,2) [TRUE/FALSE, with any counterexample]; (2) the headline self-contained-vs-needs-carrying answer with evidence; (3) a proposed one-line inductive statement for the derived stub; (4) the sympy script you ran (I will transcribe it into a durable battery). If the fold is ambiguous at some step, say which — do not guess.
