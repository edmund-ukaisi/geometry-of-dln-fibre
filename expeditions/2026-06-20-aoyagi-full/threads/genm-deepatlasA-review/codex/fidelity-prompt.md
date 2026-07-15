<task>
You are an independent adversarial reviewer of a Lean 4 (Mathlib) formalisation. I give you (A) informal
DESIGN claims from a math-research design doc, and (B) the Lean theorem signatures that are supposed to
faithfully realise those claims. Your job: judge FIDELITY — does each Lean statement capture exactly the
informal claim, with NO overclaim, NO vacuity (trivially-true-as-stated), and NO hidden gap where a
hypothesis silently narrows the statement or does work that hides the real content? Argue whichever way the
evidence points; if you think the formalisation is faithful, say so; if you find a mismatch, name it exactly
(the specific matrix/rank/orientation/type discrepancy). I am WITHHOLDING my own conclusion deliberately.

Mathlib conventions you need:
- `Matrix.fromBlocks A B C D` = the block matrix [[A,B],[C,D]] (A top-left, B top-right, C bottom-left,
  D bottom-right), row type `m₁ ⊕ m₂`, col type `n₁ ⊕ n₂`.
- `Matrix.fromRows A B` stacks A over B vertically (same col type; row type `m₁ ⊕ m₂`).
- `Matrix.fromCols A B` places A left of B horizontally (same row type; col type `n₁ ⊕ n₂`).
- `Matrix.rank` is the (real) matrix rank. `IsUnit Δ.det` means Δ is invertible; `Δ⁻¹` is the nonsing inverse.
- `v ᵥ* M` is row-vector-times-matrix (vecMul); `(fun i => L i ᵥ* G)` equals the matrix product `L * G`.
- `∫⁻` is the Lebesgue (lower) integral over the raw pi type `Fin m → Fin n → ℝ` (product Lebesgue measure).

===== (A) DESIGN CLAIMS =====

Setting: an "effective last layer" matrix M ∈ ℝ^{n×d}, with a chosen invertible top-left r×r pivot Δ, so
M = [[Δ, U],[V, W]] (U is r×(d−r), V is (n−r)×r, W is (n−r)×(d−r)). Define the transverse Schur coordinate
E := W − V·Δ⁻¹·U ∈ ℝ^{(n−r)×(d−r)}.

DESIGN §2.1 (per-level block-Schur big-cell — reuse of a "chart 5" fact):
  (a) the map (Δ,U,V,E) ↦ [[Δ,U],[V, V·Δ⁻¹·U + E]] is a translation in the W-block, Jacobian ≡ 1, so the
      raw-pi Lebesgue integral is preserved under E ↦ E + (V·Δ⁻¹·U);
  (b) rank M = r + rank E (for Δ invertible);
  (c) {rank M ≤ r} = {E = 0} in the E-coordinates (for Δ invertible).

DESIGN §2.2 (product-layer reduction — the genuinely new piece):
  On the rank-drop stratum {E=0}, M = [[Δ,U],[V, V·Δ⁻¹·U]]. Skeleton (CUR) factorization:
      [[Δ,U],[V, V·Δ⁻¹·U]] = A · Δ⁻¹ · D,  where A = [[Δ],[V]] (pivot COLUMNS), D = [Δ | U] (pivot ROWS).
  The completion G₀ = [[I_r, 0],[V·Δ⁻¹, I_{n−r}]] is unitriangular, det G₀ = 1, so the reduction change of
  variables (right-multiply the free preceding layer L by G₀) has Jacobian 1 and preserves Lebesgue measure.
  Consequence: on {E=0}, for a preceding head B·L, rank(B·L·M) = rank(B·H) where H = L·A·Δ⁻¹ (the reduced
  free last layer); the pivot rows D = [Δ|U] (full row rank r) drop out.

Scope guard: this is a RANK/MEASURE atlas, independent of any loss. The composed-loss product seam "F·E"
(F := L·K a spectator) is explicitly OUT of scope (deferred). No loss / rlct claim should appear.

===== (B) LEAN SIGNATURES (the formalisation to audit) =====

variable {r s t : ℕ}   -- section vars for the three §2.1 re-exports

1. deepLevel_bigcell_cov
   (f : (Chart5FixedBlocks r s t) × (Fin s → Fin t → ℝ) → ℝ≥0∞) (hf : Measurable f) :
   ∫⁻ p : (Chart5FixedBlocks r s t) × (Fin s → Fin t → ℝ), f (p.1, p.2 + chart5Shift p.1) = ∫⁻ p, f p
   -- where chart5Shift (Δ,U,V) is DEFINED as V * Δ⁻¹ * U.

2. deepLevel_rank_eq
   (Δ : Matrix (Fin r) (Fin r) ℝ) (U : Matrix (Fin r) (Fin t) ℝ) (V : Matrix (Fin s) (Fin r) ℝ)
   (W : Matrix (Fin s) (Fin t) ℝ) (hΔ : IsUnit Δ.det) :
   (Matrix.fromBlocks Δ U V W).rank = r + (W - V * Δ⁻¹ * U).rank

3. deepLevel_rank_le_iff
   (Δ : Matrix (Fin r) (Fin r) ℝ) (U : Matrix (Fin r) (Fin t) ℝ) (V : Matrix (Fin s) (Fin r) ℝ)
   (E : Fin s → Fin t → ℝ) (hΔ : IsUnit Δ.det) :
   (Matrix.fromBlocks Δ U V (E + chart5Shift (Δ, U, V))).rank ≤ r ↔ E = 0

4. deepReduce_skeleton {r nr dc : ℕ}
   (Δ : Matrix (Fin r) (Fin r) ℝ) (U : Matrix (Fin r) (Fin dc) ℝ) (V : Matrix (Fin nr) (Fin r) ℝ)
   (hΔ : IsUnit Δ.det) :
   (Matrix.fromBlocks Δ U V (V * Δ⁻¹ * U) : Matrix (Fin r ⊕ Fin nr) (Fin r ⊕ Fin dc) ℝ)
     = Matrix.fromRows Δ V * Δ⁻¹ * Matrix.fromCols Δ U

5. deepReduce_G0_det_eq_one {r nr : ℕ} (S : Matrix (Fin nr) (Fin r) ℝ) :
   (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 S 1).det = 1

6. deepReduce_cov {m n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hG : |G.det| = 1)
   (g : (Fin m → Fin n → ℝ) → ℝ≥0∞) (hg : Measurable g) :
   ∫⁻ L : Fin m → Fin n → ℝ, g (fun i => L i ᵥ* G) = ∫⁻ L, g L
   -- G₀ from the design lives over the sum type Fin r ⊕ Fin(n−r); this is stated over Fin n for a general
   -- |det G|=1 matrix. The det-preserving reindex Fin n ≃ Fin r ⊕ Fin(n−r) is DEFERRED to a later tide.

7. rank_mul_eq_of_mul_eq_one {p q s : Type*} [Fintype q] [Fintype s] [DecidableEq q]
   (X : Matrix p q ℝ) (D : Matrix q s ℝ) (D' : Matrix s q ℝ) (h : D * D' = 1) :
   (X * D).rank = X.rank

8. deepReduce_rank {p r nr dc : ℕ}
   (X : Matrix (Fin p) (Fin r ⊕ Fin nr) ℝ)
   (Δ : Matrix (Fin r) (Fin r) ℝ) (U : Matrix (Fin r) (Fin dc) ℝ) (V : Matrix (Fin nr) (Fin r) ℝ)
   (hΔ : IsUnit Δ.det) :
   (X * Matrix.fromBlocks Δ U V (V * Δ⁻¹ * U)).rank = (X * Matrix.fromRows Δ V * Δ⁻¹).rank
   -- design's rank(B·L·M)=rank(B·H) is the instance X = B·L, H = L·A·Δ⁻¹, A = fromRows Δ V.
</task>

<output_contract>
For EACH of the 8 signatures, in order, one short verdict block:
  - FAITHFUL / OVERCLAIM / VACUOUS / GAP / MISMATCH  (pick the sharpest)
  - one or two sentences of exact justification (name the specific discrepancy if any: an orientation slip,
    a transpose, a wrong block, a hypothesis that trivialises or narrows, a rank claim that does not follow).
Specifically adjudicate these four points and state a yes/no with reasoning:
  (P1) Is deepReduce_skeleton the EXACT identity M-on-{E=0} = (pivot cols)·Δ⁻¹·(pivot rows)? Any transpose /
       fromRows-vs-fromCols orientation error?
  (P2) In deepReduce_rank, does rank(X·M) = rank(X·fromRows Δ V·Δ⁻¹) genuinely hold (D=[Δ|U] right-invertible
       via [[Δ⁻¹],[0]]), or is the rank preservation smuggled/assumed?
  (P3) Is the deepReduce_cov deferral (stating over Fin n for general |det G|=1, deferring the sum-type
       reindex of G₀) SOUND — is that reindex genuinely a det-1 coordinate permutation with no hidden step?
  (P4) Do any hypotheses (IsUnit Δ.det, |det G|=1) silently narrow a statement below what the design claims,
       or make any statement vacuous?
End with a single line: OVERALL: <FAITHFUL to design | list of the signatures with problems>.
</output_contract>

<grounding_rules>
- Distinguish what you can VERIFY by algebra (matrix identities, rank facts, determinant of block-triangular)
  from what you INFER about Lean elaboration you cannot see. Flag every inference explicitly as "inference".
- You do NOT have the proofs, only the signatures + the stated Mathlib lemma conventions. Judge the STATEMENTS.
  A statement can be faithful even if you cannot see its proof; a statement can be an overclaim regardless of
  proof. If a statement is only faithful UNDER an unstated assumption, say which.
- Do the block algebra concretely (e.g. A·Δ⁻¹·D expansion) before pronouncing on orientation.
</grounding_rules>
