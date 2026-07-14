<task>
I am formalising (in Lean 4 / Mathlib) a per-shell finiteness bound in a deep-linear-network RLCT computation.
Red-team the SOUNDNESS of a reduction I plan to build. This is measure theory + matrix algebra; give exact judgement.

SETUP (all integrals are ∫⁻ over ℝ≥0∞, nonneg integrands, boxes = per-entry [-1,1]).

Chain widths: M : Fin (L+3) → ℕ, i.e. widths (M0, M1, M2, ..., M_last). "tailChain M" is the chain (M1,...,M_last).
"prod (tailChain M) A'" is the layer product of a tuple A' of matrices with widths (M1,...,M_last); it is an
M1 × M_last matrix. For L=0 the tail is a single M1×M2 matrix and prod = that matrix.

Cut u = t + j with 1 ≤ u ≤ min(M0,M1); a,b := M0-u, M1-u. κ : Fin u ↪ Fin M1 is an embedding; blockSplitEquiv κ
is the induced equiv (Fin u ⊕ Fin (M1-u)) ≃ Fin M1.

The object (shellSpineIntegrand), a DECORATED integral:

  I_shell(c') = ∫_{A' ∈ box, prod(tailChain M) A' ∈ singularShell_j}
                  ∫_{x ∈ outerDom u a b}  ∫_{Γ : Γ+schurShift x ∈ genBox}
                    ( freedSchurLoss x Γ  Q_sub )^(-c')

where Q_sub = (prod(tailChain M) A').submatrix (blockSplitEquiv κ) id  (an (Fin u ⊕ Fin b) × Fin M_last matrix),
x = (P, B12, C) is a block triple with P the u×u pivot, outerDom additionally requires IsUnit P (det P ≠ 0),
schurShift x = C·P⁻¹·B12, and (BANKED, proven) freedSchurLoss x Γ Q = frobSq(B'·Q) where
B' = [[P, B12],[C, Γ + C·P⁻¹·B12]] is the reconstructed full front (Fin u⊕Fin a)×(Fin u⊕Fin b) block.

BANKED EQUALITY (proven in repo): for any Q,
  ∫_{x∈outerDom} ∫_{Γ : Γ+schurShift x ∈ genBox} (freedSchurLoss x Γ Q)^(-c')
    = ∫_{B ∈ genBox(u⊕a, u⊕b) ∩ {IsUnit toBlocks11 B}} frobSq(of B · Q)^(-c').

BANKED (proven): prod M A = (A 0) · prod(tailChain M) (A∘succ)  [head-split, front layer A0 is M0×M1];
Params M ≃(measure-preserving) (M0×M1 front block) × Params(tailChain M), box↦box.

TARGET box: routeMLayerBoxIntegral M c' 1 = ∫_{A ∈ paramsBoxM M 1} frobSq(prod M A)^(-c'), the bare full-chain box.
BANKED: for L=0 (3 widths m,n,p), routeMBoxThresholdFinite_mnp: this box < ⊤ for c' < minAdm(m,n,p)/2.
For L≥1 the analogous box finiteness (RouteMBoxThresholdFinite M) is a NAMED, currently-unproved hypothesis
(it is the recursion's own top-level goal).

THE REDUCTION I claim (want to build sorry-free):
  I_shell(c')
   =[banked un-free EQ]  ∫_{A'∈box∩shell} ∫_{B ∈ genBox(u⊕a,u⊕b) ∩ IsUnit P} frobSq(of B · Q_sub)^(-c')
   ≤[drop IsUnit P]      ∫_{A'∈box∩shell} ∫_{B ∈ genBox(u⊕a,u⊕b)} frobSq(of B · Q_sub)^(-c')
   ≤[drop shell]         ∫_{A'∈box}       ∫_{B ∈ genBox(u⊕a,u⊕b)} frobSq(of B · Q_sub)^(-c')
   =[reindex cols of B by blockSplitEquiv κ (cancels Q_sub's row-submatrix), reindex rows of B by any
     Fin u⊕Fin a ≃ Fin M0 (u+a=M0), frobSq invariant under row/col permutation]
                          ∫_{A'∈box} ∫_{B'∈matBox M0 M1} frobSq(of B' · prod(tailChain M) A')^(-c')
   =[Fubini + head-split reassembly Params M ≃ front×tail, prod_headSplit]
                          routeMLayerBoxIntegral M c' 1.

Then: I_shell(c') ≤ routeMLayerBoxIntegral M c' 1, hence
  - L=0: I_shell(c') < ⊤ for c' < minAdm(M)/2  (via routeMBoxThresholdFinite_mnp), UNCONDITIONAL.
  - L≥1: I_shell(c') < ⊤ for c' < minAdm(M)/2  CONDITIONAL on RouteMBoxThresholdFinite M (named).

CONTEXT: a prior decorrelated hunt certified that the SAME object with IsUnit dropped, targeting a HIGHER
threshold T2=(minAdm(redChain u M)+ab)/2, DIVERGES for j>r/2 (the "false full-block wall"). My target is the
LOWER threshold T1 = minAdm(M)/2. The claim is that the full off-shell box (IsUnit dropped) has RLCT exactly
minAdm(M)/2 = T1, so dropping IsUnit is harmless when targeting T1 (not T2).
</task>

<output_contract>
1. VERDICT: is the inequality I_shell(c') ≤ routeMLayerBoxIntegral M c' 1 TRUE as an inequality of ℝ≥0∞
   (independent of any threshold)? YES/NO + the single most likely place it could be WRONG.
2. Is dropping IsUnit P sound HERE (targeting T1), given the prior hunt found dropping it unsound when
   targeting T2? Explain the distinction in one paragraph, or refute it.
3. The reindex step (cols by blockSplitEquiv κ, rows by an arbitrary equiv): any subtlety that could make
   frobSq(of B · Q_sub) ≠ frobSq(of B' · prod) after reindexing? Confirm frobSq is permutation-invariant
   and the column-cancel identity B·(P.submatrix e id) = (B.submatrix id e.symm)·P holds.
4. Is bounding I_shell (a peel-component of the chain-M box) BY the chain-M box routeMLayerBoxIntegral M
   circular for the induction? Is it still a legitimate STANDALONE theorem (given RouteMBoxThresholdFinite M
   as a hypothesis for L≥1)? One paragraph.
5. Any OTHER soundness hole, esp. around measurability/Tonelli (nonneg integrand) or the shell/box being
   the right domains.
Keep it under ~500 words. Flag inference vs certainty.
</output_contract>
