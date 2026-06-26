<task>
Decorrelated check of a matrix comparability in a Lean RLCT formalisation. Re-derive independently; tell
me the precise true statement + scope. Do NOT rubber-stamp.
</task>

<setting>
Block-2x2 matrices C_s = [[a_s, Y_s],[Z_s, T_s]], s=0,1, with a_s a 1x1 (scalar) invertible pivot,
T_s an M×M block (M≥2), Y_s 1×M, Z_s M×1. Near a "deepest point" all OFF-pivot data → 0 and a_s → 1,
T_s → (a fixed core); precisely Y_s,Z_s → 0, a_s → 1.

Two M×M core quantities:
- R = Schur complement of the PRODUCT P=C0·C1 wrt its (1,1) scalar pivot: R = P22 − P21·P11⁻¹·P12.
- ∏S = S0·S1, the product of per-layer Schur complements S_s = T_s − Z_s·a_s⁻¹·Y_s.

I derived (block-LDU): C_s = L_s·diag(a_s, S_s)·U_s, L_s=[[1,0],[Z_s/a_s, I]], U_s=[[1,Y_s/a_s],[0,I]]
unipotent. Schur is invariant under outer L0-left / U1-right unipotents, so
R = Schur(D0·M·D1), M = U0·L1 = [[A/(a0a1), Y0/a0],[Z1/a1, I_M]], A = a0a1 + Y0·Z1 (scalar),
D_s = diag(a_s, S_s). The (2,2) block of D0·M·D1 is S0·I_M·S1 = ∏S, and
R = ∏S − (S0·(Y0/a0))·(A/(a0a1))⁻¹·((Z1/a1)·S1)  [the Schur correction of D0 M D1].

The RLCT squeeze needs the Frobenius comparability ∑‖R‖² ≍ ∑‖∏S‖² on a neighborhood of the deepest point.
</setting>

<facts_established_by_me>
- r=1 (M=1, scalar) EXACT: R = u·∏S, u = (∏ a_s)/A → 1, a bounded unit. Standalone ∑R²≍∑(∏S)².
- M≥2: R = ∏S − S0·(Y0/a0)·(a0a1/A)·(Z1/a1)·S1 (the correction). The correction is O(Y0·Z1)·(S0..S1),
  i.e. carries TWO off-pivot factors (Y0 and Z1), so → 0 faster than ∏S near the deepest point.
- Numerics (M=2): ∑‖R‖²/∑‖∏S‖² → 1 as scale→0 ([0.995,1.003] at scale 1e-2, [1.0000,1.0001] at 1e-3).
  R·(∏S)⁻¹ → I.
</facts_established_by_me>

<questions>
1. Independently confirm R = ∏S − [correction], with the correction carrying two off-pivot factors
   (so O(‖off-pivot‖)·‖∏S‖). Is the correction a LEFT+RIGHT bounded-operator perturbation of ∏S, i.e.
   R = (I − Λ_L)·∏S·(I − Λ_R)-ish, or only an additive ∏S − G with G = small·(stuff)?
2. Does ∑‖R‖²_F ≍ ∑‖∏S‖²_F hold STANDALONE on a neighborhood (∃ m,M>0, m·∑‖∏S‖² ≤ ∑‖R‖² ≤ M·∑‖∏S‖²)?
   The danger for M≥2 vs M=1: the correction is ADDITIVE (R = ∏S − G), and additive perturbations can
   CANCEL (make ‖R‖ ≪ ‖∏S‖) even when G is "small" in operator norm IF G aligns with ∏S. Is there a path
   where ∏S ≠ 0 but R = 0 (exact cancellation), breaking the LOWER bound m·∑‖∏S‖² ≤ ∑‖R‖²?
   Hunt it: can S0·(Y0/a0)·(a0a1/A)·(Z1/a1)·S1 = ∏S = S0·S1 (i.e. the correction = the whole product)?
   That needs (Y0/a0)(a0a1/A)(Z1/a1) = I_M on the relevant subspace — but Y0 is 1×M, Z1 is M×1, so their
   product is RANK ≤ 1; can a rank-≤1 correction equal S0·S1 (generically rank M)? Reason about ranks.
3. If the standalone Frobenius comparability HOLDS, give the scope (which quantities bounded: a_s units,
   A unit, AND must ‖Y0‖,‖Z1‖ be small — i.e. is it a GERM at the deepest point, the correction being
   higher-order?). If it FAILS, give the precise weaker true statement.
4. The build-ready form: is the right statement "R = ∏S·(I + o(1)) so ∑‖R‖²≍∑‖∏S‖² on a germ" (a
   multiplicative/higher-order-additive comparability), or must it be charged into the ∑E²+‖·‖² sum
   (like the leak)? Note the correction carries Y0 AND Z1 which are ALSO in the regular energy ∑E².
</questions>

<output_contract>
Per question VERDICT + reasoning, exact-algebra vs inference marked. The decisive output: does the
matrix-core standalone Frobenius comparability ∑‖R‖²≍∑‖∏S‖² HOLD on a germ, and WHY the rank-≤1
correction can't cause lower-bound cancellation (or if it can, the counterexample). End with: "The
matrix-core S5c is [TRUE standalone germ / TRUE only in-sum / FALSE], because ___; build-ready statement ___."
</output_contract>

<grounding_rules>
Re-derive the block algebra. The rank of the correction (Y0 1×M, Z1 M×1 ⇒ rank ≤1) is likely the crux
of the lower bound. Distinguish a germ (higher-order) comparability from a uniform one.
</grounding_rules>
