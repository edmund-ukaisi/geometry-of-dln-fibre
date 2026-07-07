<task>
I am formalising in Lean 4 (Mathlib) the finiteness of a "joint resolution" integral for the RLCT of
deep-linear-network square loss (Aoyagi's (S,J) blow-up resolution). I need you to nail the EXACT
pointwise matrix-algebra identity for one recursion step ("STEP-3, the Z-independent unit
block-elimination"), because the wrong statement wastes a build cycle. This is pure real matrix algebra
(Frobenius norms of matrix products) — NO measure theory in your answer.

## Notation
- `frobSq M := ∑_{i,j} M_{ij}²` (squared Frobenius norm).
- `fromBlocks A B C D` = the block matrix `[[A,B],[C,D]]`.
- For `Q : Matrix (t ⊕ b) n`, `Q_p := Q.submatrix Sum.inl id` (top t rows), `Q_b := Q.submatrix Sum.inr id`.
- `schurCompl A B C D := D − C·A⁻¹·B`.

## Banked EXACT identity (proved in Lean, "corankStep"), for `A` a `t×t` invertible pivot:
    frobSq ((u • fromBlocks A B C D) · Q)
      = u² · ( frobSq (A · Q̃_p) + frobSq (C · Q̃_p + Γ · Q_b) )
    where  Q̃_p := Q_p + A⁻¹·B·Q_b ,  Γ := schurCompl A B C D  (dim (M₀−t)×(M₁−t)).
So one radial `u` factors out; the residual splits into the pivot energy `frobSq(A·Q̃_p)` (t rows) and the
CROSS-COUPLED corank residual `frobSq(C·Q̃_p + Γ·Q_b)` ((M₀−t) rows), with Γ the corank block.

## The two "pure isotropic peels" I want to consume (proved in Lean), for a block Δ : Fin p → Fin q → ℝ:
(TERMINAL) `matBox_corank_dominates_absZ_lt_top`: if 0 ≤ c' < p·q/2, μ(Z)<∞, W:Ω→ℝ with W z ≥ 0, then
    ∫_{z∈Z} ∫_{Δ∈[−T,T]^{p×q}} (frobSq Δ + W z)^{−c'} dΔ dz  <  ∞ .
(INTERMEDIATE) `matBox_corank_residual_absZ_le`: if p·q/2 < c', W z > 0, then
    ∫_{z∈Z} ∫_{Δ∈box} (frobSq Δ + W z)^{−c'} dΔ dz  ≤  Cresid(pq,c') · ∫_{z∈Z} (W z)^{−(c'−pq/2)} dz .
BOTH require the block Δ to enter through its OWN Frobenius norm `frobSq Δ` (isotropically), added to a
NON-NEGATIVE additive core W z that depends only on the OUTER parameter z.

## The concrete (2,2,2) template that must generalise (proved in Lean):
`blockForm q v w G H := v² + w² + (q·v+G)² + (q·w+H)²`  [ = frobSq([[v,w],[q·v+G, q·w+H]]) = frobSq(L·N),
   L = [[1,0],[q,1]] unit-lower-triangular det 1, N = [[v,w],[G,H]] ].
`blockForm_step3`: blowing up N's radial (v=u, w=u·a1, G=u·a2, H=u·a3) gives
    blockForm q u (u·a1)(u·a2)(u·a3) = u² · ((q·a1+a3)² + (q+a2)² + a1² + 1),  and the bracket ≥ 1 (a UNIT).
Note the (2,2,2) TERMINAL step reaches `u² · (unit ≥ 1)` — monomial×unit — NOT the `frobSq Δ + W` shape.

## THE CORE TENSION I need you to resolve
The corankStep residual `frobSq(C·Q̃_p + Γ·Q_b)` is ANISOTROPIC: the corank block Γ enters as `Γ·Q_b`
(coupled to the downstream `Q_b`), NOT as `frobSq Γ`. A unit-triangular ROW transform L applied to make
Γ block-diagonal does NOT preserve the Frobenius norm of the product `(L·…)·Z` (L is not orthogonal). So
it is not obvious how a "Z-independent unit block-elimination" converts `frobSq(C·Q̃_p + Γ·Q_b)` into the
`frobSq Δ + W z` shape (isotropic block + nonneg outer core) that the two pure peels require.

## QUESTIONS (answer each, in order)
1. Is the `frobSq Δ + W z` peel shape actually reachable for the FIRST peel of `gammaPeelIntegral`
   (integrand `frobSq(A0 · Q)^{−c'}`, A0 the M₀×M₁ leading matrix over its box ∩ pivot-chart, Q = fixed
   downstream product)? If YES, give the EXACT pointwise identity (a Lean-provable `frobSq(...) = frobSq Δ
   + W` with Δ some block of A0 that enters isotropically and W depending only on the OUTER variables).
   If NO, say so plainly and identify which mechanism the pure route actually uses.
2. Reconcile: the (2,2,2) terminal is `monomial × (unit ≥ 1)` (integrableOn_monomial_mul_unit), whereas the
   two pure peels want `frobSq Δ + W`. Are these the SAME mechanism viewed two ways, or TWO different
   endpoints? Which one does the general-L degenerate-strata recursion actually terminate on?
3. Give the cleanest EXACT general-width pointwise identity for one STEP-3 (the "Z-independent unit
   block-elimination `D_J' → [[1,O],[O,D_{J+1}]]`"), stated as an equality of `frobSq` of matrix products,
   that (a) is provable by matrix algebra (mul_assoc, fromBlocks, Frobenius row-split, det-1 triangular
   factors) and (b) advances the recursion one corank step. Be explicit about what "absorbed into the
   adjacent downstream factor" means at the norm level (which factor, left/right, and why frobSq survives).
4. Realistic scope: is closing `sjJointResolution` (the full (S,J) carrier recursion over opaque widths)
   from these banked pieces a BOUNDED formalisation (state a rough lemma-count / structure), or is it a
   genuine multi-week "mountain" whose honest partial deliverable is just the STEP-3 pointwise identity +
   a single-layer instance? Flag inference vs. what you can derive.
</task>

<output_contract>
Four numbered sections (Q1–Q4), matching the questions. In Q1 and Q3, write the exact identity as a
displayed equation with every term defined. Prefer a chain of small exact matrix identities over one dense
claim. Be concrete about matrix dimensions. Keep prose minimal. If an identity is FALSE as I've sketched
it, say so and give the corrected form. End with a one-line VERDICT on whether the pure peels are the right
tool for the general degenerate recursion or whether the monomial×unit endpoint is.
</output_contract>

<grounding_rules>
Distinguish (i) exact algebraic identities you can verify by hand from (ii) structural/strategic inferences
about the formalisation. Mark each Q4 claim as inference. Do NOT assume any Lemma exists in Mathlib without
noting it as an assumption. The banked identities above are given as ground truth (proved).
</grounding_rules>
