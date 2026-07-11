<task>
Audit whether a Lean proof genuinely AVOIDS algebraic-geometry infrastructure (irreducible-component
decomposition, generic-rank-on-a-variety-component) — or whether it secretly re-imports it. Reason in exact
algebra. Self-contained.

THE THEOREM (Lean 4 / Mathlib):
  corank_survival_ae {b m D : ℕ} (Zdeep : Matrix (Fin m) (Fin D) ℝ) (hb : b ≤ Zdeep.rank) :
      ∀ᵐ A : Fin b → Fin m → ℝ, (Matrix.of A * Zdeep).rank = b
"For a FIXED Zdeep of rank ≥ b, almost-every free b×m block A has rank(A·Zdeep) = b."

THE PROOF (paraphrased):
1. rank(A·Zdeep) ≤ b always (b rows).
2. The deficient set {A | rank < b} ⊆ zero-set of ONE fixed b×b minor det((A·Zdeep).submatrix id ec), where
   ec is a fixed b-column selection. (Mathlib: rank ≤ r ⟹ all (r+1)-minors vanish.)
3. That minor = eval_A(P) for a fixed multivariate polynomial P in the entries of A (matrix product commutes
   with polynomial eval; RingHom.map_det).
4. P ≠ 0: the ONE-HOT ROW-SELECTION witness A₀ (indicator on the b independent rows `er` extracted from
   `b ≤ Zdeep.rank` via "rank ≥ b ⟹ ∃ nonzero b×b minor") gives A₀·Zdeep = Zdeep.submatrix er id, whose
   ec-minor = det(Zdeep.submatrix er ec) ≠ 0.
5. A nonzero polynomial's real zero-set is Lebesgue-null (banked); transport to the matrix box by a
   measure-preserving flatten. Hence a.e. the minor ≠ 0, so rank = b.

ASSESS (the AG-wall watch-point — this problem previously hit a Mathlib-frontier AG wall that this proof is
meant to route around):
 Q1. Is the genericity genuinely in the FREE integration variable A (an a.e./Lebesgue-null statement over a
     Euclidean matrix box), NOT "generic rank on an irreducible component of a variety"? Pin the difference.
 Q2. Does the hypothesis `b ≤ Zdeep.rank` or the witness extraction (`rank ≥ b ⟹ ∃ nonzero b×b minor`) secretly
     invoke irreducible components / generic-rank-on-a-component, or is it elementary linear algebra (a
     nonzero minor exists by the rank definition)?
 Q3. Is the deficient-set-⊆-one-minor-zero-set step sound and genuinely a SINGLE minor-cut null set (not a
     union needing component analysis)? Any gap (e.g. does {rank<b} need MORE than one minor to be captured)?
 Q4. Net: does the proof genuinely avoid the AG wall, and is the statement `∀ᵐ A, rank(A·Zdeep)=b` the correct
     "corank rows survive full-row-rank b" fact (given rank Zdeep ≥ b), or is there a subtle unsoundness /
     over/under-statement?
</task>

<output_contract>
Answer Q1-Q4. Each: verdict (AG-FREE / NEEDS-AG / GAP / UNSOUND) + reason. Mark [DERIVED]/[INFERRED]. End:
does the proof avoid the AG wall (YES/NO), and any residual concern.
</output_contract>

<grounding_rules>
Distinguish "a.e. over a free Euclidean variable" (elementary measure/analysis) from "generic rank on a
variety component" (AG). Try to find a hidden component argument. Do not paste code.
</grounding_rules>
