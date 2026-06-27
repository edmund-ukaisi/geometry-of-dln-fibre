<task>
I am formalising a matrix-analysis lemma in Lean 4 + Mathlib (v4.29). The numerical truth is CONFIRMED
(ratio bounded in [0.245, 3.39] across r=2,3,4, all j, even at the det→0 edge). I need the cleanest
Lean PROOF ROUTE and a realistic SCOPE judgement, NOT the math (math is settled).

THE LEAN STATEMENT (`schur_minorPivot_split`, general r,j,p). frobSq M = ∑_i ∑_j (M i j)^2 (raw sum,
NOT Mathlib's Matrix.frobenius). rmatMul X Y i j = ∑_k X i k * Y k j (raw entry product). R : r×r,
S : r×p (as Fin r → Fin p → ℝ). M11 = top-left j×j block of R, M12/M21/M22 the other blocks.

  ∃ (c₀ c₁ : ℝ), 0 < c₀ ∧ 0 < c₁ ∧
    ∀ (R : Matrix (Fin r) (Fin r) ℝ) (S : Fin r → Fin p → ℝ),
      (∀ a b, |R a b| ≤ 1) →                                   -- hbd: bounded entries
      (∀ I J : Fin j → Fin r, |(R.submatrix I J).det| ≤ |M11.det|) →  -- hpivot: M11 is a MAX-modulus j-minor
      M11.det ≠ 0 →                                             -- hne
      ∃ Sc : Matrix (Fin (r-j)) (Fin (r-j)) ℝ,
        Sc = M22 − M21 * M11⁻¹ * M12 ∧                          -- Schur complement (structural pin)
        R.det = M11.det * Sc.det ∧                              -- Schur det identity
        c₀ * (frobSq (R·S)_top + frobSq (Sc · S_bot)) ≤ frobSq (R·S) ∧   -- (R·S)_top = top j rows of R·S
        frobSq (R·S) ≤ c₁ * (frobSq (R·S)_top + frobSq (Sc · S_bot))     -- S_bot = bottom r−j rows of RAW S

CRUCIAL: c₀,c₁ are quantified BEFORE ∀R,S (uniform). The cell hyps (hbd, hpivot, hne) are what MAKE
uniform constants exist (off-cell the ratio is unbounded). The Morse block uses (R·S)_top (the SHEARED
top block M11·S'_top), NOT raw S_top.

THE MATH (settled, from a pen-and-paper cert):
- block-Gauss det-1 normal form L·R·U = diag(M11, Sc), L=[[I,0],[−M21 M11⁻¹,I]], U=[[I,−M11⁻¹ M12],[0,I]].
- the Cramer minor-ratio shear bound: each entry of M21 M11⁻¹ AND M11⁻¹ M12 has |·| ≤ 1, BECAUSE M11 is
  the max-modulus j-minor (numerator is another j-minor of R, ≤ det M11 in modulus). This is what makes
  c₀,c₁ ABSOLUTE (depend only on r,j, not on the specific R).
- the comparison is two-sided: ‖R·S‖² ≍ ‖M11·P‖² + ‖Sc·Q‖² where P=S'_top, Q=S'_bot, S=U·(P;Q). The
  Lean form uses (R·S)_top = M11·P and RAW S_bot (not Q). Numerically the raw form still gives a uniform
  two-sided bound.

WHAT IS ALREADY PROVED in the file (axiom-clean):
- N1: frobSq((a•R)·S) = a²·frobSq(R·S)  (ring).
- N2a: the r=2 rank-1 outer-product split (ring-clean, the scalar-M11 special case).

<output_contract>
Answer in EXACTLY these sections, terse and concrete:

1. SCOPE VERDICT (one of): (a) full general-r proof is realistically reachable in one tide (~how many
   hundred LoC + which Mathlib pieces are the long pole); (b) only a RESTRICTED version is reachable now
   (say which — e.g. j=1 general r, or a fixed small r), with the general statement left as a documented
   skeleton; (c) the statement as written is the wrong Lean target — propose a better-factored equivalent
   that is provable AND still discharges what N4 needs (frobSq(R·S)^{−c'} threshold = the disjoint-sum
   threshold). Pick ONE and justify in 3-4 lines.

2. THE c₀/c₁ CONSTRUCTION. The single hardest sub-goal is producing the explicit uniform c₀,c₁ and the
   two-sided inequality. Give the cleanest Lean-tractable route. Specifically: is it better to (i) prove
   an OPERATOR-NORM comparison via L,U and Mathlib's `Matrix.frobenius_norm`/opNorm congruence lemmas, or
   (ii) stay entirely in the raw frobSq sum and bound via Cauchy-Schwarz + the ≤1 shear entrywise, never
   invoking opNorm? Rank (i) vs (ii) for v4.29 Lean tractability and name the load-bearing Mathlib lemmas
   for the winner.

3. THE SHEAR BOUND (the ≤1 Cramer ratio) in Lean. Which Mathlib lemma gives "entry of M21·M11⁻¹ = a
   j-minor-ratio"? Candidates I see: Matrix.inv_def (A⁻¹ = (det)⁻¹ • adjugate), Matrix.cramer_apply
   (cramer A b i = (A.updateCol i b).det), Matrix.mul_adjugate. Give the exact chain to
   |(M21·M11⁻¹) a b| ≤ 1 from hpivot, or flag if this is the real Lean long-pole and should be its own
   pre-staged lemma.

4. CHEAPEST FIRST MILESTONE. Given the build-order constraint (N4 depends on N2b), what is the smallest
   honest sub-lemma I should land FIRST that is real progress toward N2b and de-risks the rest? (e.g. the
   shear bound alone as a standalone lemma; or the j=1 case as a warm-up that subsumes N2a.)

5. TRAPS. Up to 4 specific Lean-v4.29 traps for THIS proof (Matrix.submatrix index bookkeeping, the
   Fin (r-j) offset omega proofs, Matrix vs raw-function frobSq mismatch, inv of non-square via block
   indexing, etc.). Flag inference vs fact (you do not have the Mathlib source in front of you — say when
   you are inferring a lemma name).
</output_contract>

<grounding_rules>
You do NOT have the Mathlib v4.29 source in front of you. When you name a Mathlib lemma, mark it
[INFER] if you are recalling the name from memory vs [LIKELY-EXISTS] if you are confident it is standard.
Do not invent lemma names with false confidence — if unsure a lemma exists, say "verify exists" and give
the search term. Distinguish "this is the math" (settled) from "this is my Lean-tractability inference".
</grounding_rules>
