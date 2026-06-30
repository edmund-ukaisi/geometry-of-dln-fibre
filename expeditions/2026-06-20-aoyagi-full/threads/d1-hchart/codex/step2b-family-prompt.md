<task>
Lean 4 + Mathlib v4.29. I need the CLEANEST FORMALIZABLE proof of one linear-algebra
inequality. Pure math/design question — prose + key identities, no Lean syntax needed.

## The statement (the `sorry` to fill)

`v⁰ : Mat(H0×H1) ℝ`, `v¹ : Mat(H1×H2) ℝ`, with `v⁰·v¹` of rank `r`.
Define the linear map
    Dg : Mat(H0×H1) × Mat(H1×H2) →ₗ[ℝ] Mat(H0×H2),   Dg(δ⁰,δ¹) = δ⁰·v¹ + v⁰·δ¹.
Prove:  nReg := r·(H0 + H2 − r)  ≤  finrank ℝ (range Dg).

(I will then feed `nReg ≤ Matrix.rank (Dg-matrix)` into a determinantal-minor extractor.)

## What I have / standard facts available

- `Submodule.finrank_mono` (S ≤ T ⟹ finrank S ≤ finrank T).
- `LinearIndependent.finrank_le`-style: an n-element linearly independent family in a submodule
  W gives n ≤ finrank W. Or: build an injective linear map ℝ^nReg →ₗ range Dg.
- `B := v⁰·v¹` has `rank B = r`. Over ℝ a rank-r matrix factors `B = U·W`, `U : H0×r` rank r,
  `W : r×H2` rank r (e.g. column space basis). Mathlib has `Matrix.rank`, `LinearMap.range`,
  column/row space tools, `Matrix.rank_eq_finrank_range_toLin'`-style.
- rowspace(B) ⊆ rowspace(v¹) and colspace(B) ⊆ colspace(v⁰) (since B = v⁰v¹). So:
  every row of W ∈ rowspace(v¹) ⟹ ∃ δ⁰ with δ⁰·v¹ = (that row placed in row i);
  every col of U ∈ colspace(v⁰) ⟹ ∃ δ¹ with v⁰·δ¹ = (that col placed in col j).

## My candidate family (numerically verified rank = nReg, including the slack case r<min(rk v⁰,rk v¹))

In range(Dg), take the union:
  (A) e_i ⊗ Wₚ      (i ∈ [H0], p ∈ [r])   — H0·r vectors, each = δ⁰·v¹ for some δ⁰
  (B) Uₚ ⊗ e_j      (p ∈ [r], j ∈ [H2])   — r·H2 vectors, each = v⁰·δ¹ for some δ¹
with the r×r overlap removed, giving H0·r + r·H2 − r² = nReg independent vectors.
The span of (A) = {matrices whose rows ∈ rowspace(W)=rowspace(B)} (dim H0·r);
the span of (B) = {matrices whose cols ∈ colspace(U)=colspace(B)} (dim r·H2);
their intersection = U·(r×r)·... = {M : rows∈rowsp(B) AND cols∈colsp(B)} ≅ Mat(r×r) (dim r²).

## Questions

Q1. Is there a SLICKER characterization avoiding explicit index-juggling of (A)∪(B)?
    Candidate: range(Dg) ⊇ S_row + S_col where
      S_row = {M : rowspace(M) ⊆ rowspace(v¹)} = range(· ↦ ·v¹) restricted? No—S_row = {δ⁰·v¹}
      S_col = {v⁰·δ¹}.
    finrank(S_row + S_col) = finrank S_row + finrank S_col − finrank(S_row ∩ S_col).
    finrank S_row = H0·rank(v¹), finrank S_col = rank(v⁰)·H2,
    finrank(S_row∩S_col) = rank(v⁰)·rank(v¹)?? (the tensor colsp(v⁰)⊗rowsp(v¹)).
    That gives the EXACT rank H0·b+a·H2−a·b, but the intersection-dim (=a·b) is the HARD fact
    (no Mathlib tensor/Hom intersection lemma). Is there a way to get just the LOWER BOUND nReg
    WITHOUT computing the intersection dim — e.g. by exhibiting an explicit injective
    ℝ^nReg →ₗ range(Dg) whose components are visibly independent, sidestepping the inclusion-
    exclusion entirely?

Q2. The cleanest Lean construction of the injective map ℝ^nReg →ₗ range(Dg): I'd index nReg by
    {(i,p): i∈H0,p∈[r]} ⊔ {(p,j): p∈[r],j∈[H2], excluding p<r×... } — the disjoint union is
    awkward. Is it cleaner to (a) build the family as the image of a fixed BASIS of
    Mat(H0×r) ⊕ Mat(r×H2) / (overlap) under a single linear map, or (b) prove
    nReg = finrank(Mat(H0×r)) + finrank(Mat(r×H2)) − finrank(Mat(r×r)) and use a
    finrank_sup-type identity on two concretely-described subspaces? Which fights Lean less?

Q3. The map δ⁰ ↦ δ⁰·v¹ has range S_row with finrank = H0·rank(v¹) (= H0·b, NOT H0·r). For the
    LOWER bound I only want the H0·r-dim subspace {rows ∈ rowspace(B)} ⊆ S_row. Cleanest way to
    get a rank-r "selector": post-compose with multiplication by a fixed r-column-selecting matrix?
    i.e. is the map  (X : Mat(H0×r)) ↦ X·W  (W : r×H2 the rank-r factor of B, rowspace(W)=rowsp(B))
    INJECTIVE (since W has rank r ⟹ X·W=0 ⟹ X=0)? That would make
      ι_A : Mat(H0×r) →ₗ range(Dg), X ↦ X·W   (need X·W ∈ range Dg: X·W = (X·?)·v¹? need W=?·v¹)
    Hmm — is W = (some δ⁰-shaped)·v¹? W's rows ∈ rowspace(v¹) so W = K·v¹ for some K:r×H1. Then
    X·W = X·K·v¹ = (X·K)·v¹ ∈ range(δ⁰↦δ⁰v¹). GOOD. Similarly U = v⁰·K' so Uₚ⊗... = v⁰·(K'·Y).
    So ι_A(X)=X·K·v¹, ι_B(Y)=v⁰·K'·Y, both in range(Dg). Confirm: is
      Mat(H0×r) ⊕ Mat(r×H2) → range(Dg), (X,Y) ↦ X·K·v¹ + v⁰·K'·Y
    of rank exactly nReg (kernel dim = r², the diagonal Mat(r×r) overlap)? And is THIS the cleanest
    nReg-lower-bound route (inj on a complement of the r²-overlap)?

Q4. RANK THE ROUTES by formalization cost in Mathlib v4.29 and name the single biggest trap /
    the 3-attempt-then-surface watch point. Routes: (i) explicit (A)∪(B) family + LinearIndependent;
    (ii) finrank_sup inclusion-exclusion on S_row,S_col (needs intersection dim — likely the trap);
    (iii) the ι_A⊕ι_B map (Q3) with kernel = r² diagonal; (iv) something better you see.
    I care about LOWER BOUND nReg only — I do NOT need the exact rank.
</task>

<output_contract>
Four sections Q1–Q4. For Q4 give an explicit ranking (cheapest first) + one named trap.
Be concrete and adversarial: if route (iii) hides a false/hard sub-step (e.g. computing the
kernel dim of the ι_A⊕ι_B map is itself the intersection-dim trap in disguise), SAY SO and give
the route that genuinely sidesteps the a·b intersection computation for a pure LOWER bound.
</output_contract>

<grounding_rules>
Flag any claim you are inferring vs. stating as standard Mathlib-available fact. If you assert a
specific Mathlib lemma name, mark it as "name may differ at v4.29 — verify".
</grounding_rules>
