<task>
Honest Lean-effort read for ONE block-matrix identity in a Lean4/Mathlib formalisation. Is it a contained
build (1-2 tides) or a research-grade multi-tide grind? Concise (<450 words). Be honest — flag multi-tide
if it is.
</task>

<identity>
Verified TRUE (sympy, non-commutative 2x2-block faithful). For M×M blocks, A_s invertible:
  C_s = fromBlocks (A_s) (Y_s) (Z_s) (T_s),  s=0,1.   Product C0·C1 = fromBlocks P Q R S with
  P=A0A1+Y0Z1, Q=A0Y1+Y0T1, R=Z0A1+T0Z1, S=Z0Y1+T0T1.
  Per-layer Schur:  S_s = T_s − Z_s·A_s⁻¹·Y_s.   Global Schur:  Rcore = S − R·P⁻¹·Q.
  IDENTITY:  Rcore = S0·(1 − Z1·P⁻¹·Y0)·S1.
THREE inverses (A0⁻¹,A1⁻¹,P⁻¹). No single `ring` proof (non-commutative + inverses).
</identity>

<lean_context>
Mathlib `LinearAlgebra/Matrix/SchurComplement.lean` HAS:
- `fromBlocks_eq_of_invertible₁₁ A B C D [Invertible A] : fromBlocks A B C D = fromBlocks 1 0 (C⅟A) 1 *
   fromBlocks A 0 0 (D−C⅟A B) * fromBlocks 1 (⅟A B) 0 1`  (per-layer block-LU + Schur).
- `invOf_fromBlocks_zero₂₁_eq`/`_zero₁₂_eq` (triangular inverses), `Matrix.schur_complement_eq₂₂`.
- `fromBlocks_multiply`, `Matrix.mul_invOf_cancel_left`, `invOf_mul_self` (the inverse-cancel simp set).
The repo HAS `schur_P11_decomp` (its own block-Schur split) + the S5c atom that CONSUMES this identity
as a hypothesis `hR` (so this identity is the LAST unbuilt piece).

My proposed route: (1) per-layer LU via `fromBlocks_eq_of_invertible₁₁` ×2 ⇒ C_s=L_s D_s U_s; (2) the
unipotent-strip Schur-invariance `Schur(L0·M·U1)=Schur(M)` (L0 lower-, U1 upper-unipotent) — NOT a direct
Mathlib lemma, prove from fromBlocks_multiply + the (2,2)-Schur formula (~50-80 LoC); (3) the middle
D0·(U0 L1)·D1 = fromBlocks P (Y0 S1) (S0 Z1) (S0 S1) (block-mul + invOf-cancel, ~40-60 LoC); (4) its Schur
= S0(1−K)S1 (~30-40 LoC). Total ~150-250 LoC.
</lean_context>

<questions>
1. Is my ~150-250 LoC / 1-2 tide estimate REALISTIC, or am I under-estimating? The "no clean ring proof"
   + 3 inverses + non-commutative — does that push it to research-grade multi-tide, or is the directed
   block-LDU sequence genuinely contained given Mathlib's SchurComplement API?
2. The step-2 unipotent-strip Schur-invariance is my flagged watch-item (not a direct Mathlib lemma). Is
   it actually a clean ~50-80 LoC lemma (fromBlocks_multiply + the (2,2)-Schur absorbs the unipotent
   shifts), OR is it the kind of thing that balloons (the non-commutative inverse bookkeeping)? 
3. Is there a SIMPLER route I'm missing? E.g. a DIRECT proof of Rcore = S0(1−K)S1 by `fromBlocks`-free
   manipulation (treat it as an identity in the 8 block variables + the 3 inverses, prove by
   `mul`/`sub`/`invOf`-cancel rewrites guided by the verified sympy), bypassing the unipotent-strip
   abstraction? Would that be MORE or LESS Lean than the LDU route? 
4. NET honest read: contained (1-2 tides), moderate (2-3), or research-grade multi-tide? + the single
   biggest risk.
</questions>

<output_contract>
1. Q1 realistic? + corrected estimate if not. 2. Q2 step-2 clean or balloons. 3. Q3 simpler direct route?
4. NET: contained / moderate / multi-tide + the biggest risk. Be honest — if it's multi-tide, say so.
Mark exact vs inference. End: "Honest read: [CONTAINED 1-2 tides / MODERATE 2-3 / MULTI-TIDE research-grade]
because ___; biggest risk ___."
</output_contract>
