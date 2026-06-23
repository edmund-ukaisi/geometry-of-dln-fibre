<task>
Lean 4 + Mathlib (v4.29). I need the cleanest proof route for a "scaling one factor of a matrix-chain
product scales the product linearly" lemma, to then conclude a squared-Frobenius loss is degree-2
homogeneous in one layer block.

The product is defined by a DEPENDENT recursion `prodAux` over Fin indices with cast juggling:

  def Params (H : Fin (L + 1) → ℕ) : Type := ∀ s : Fin L, Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ

  def prodAux (H : Fin (L + 1) → ℕ) (A : Params H) :
      (k : ℕ) → (hk : k < L + 1) → Matrix (Fin (H 0)) (Fin (H ⟨k, hk⟩)) ℝ
    | 0, _ => (1 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ)
    | k + 1, hk => by
        have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
        have hkL : k < L := Nat.lt_of_succ_lt_succ hk
        refine (prodAux H A k hk') * ?_
        have e1 : (⟨k, hk'⟩ : Fin (L+1)) = (⟨k, hkL⟩ : Fin L).castSucc := by apply Fin.ext; simp [Fin.castSucc]
        have e2 : (⟨k+1, hk⟩ : Fin (L+1)) = (⟨k, hkL⟩ : Fin L).succ := by apply Fin.ext; simp [Fin.succ]
        rw [e1, e2]; exact A ⟨k, hkL⟩

  def prod (H) (A : Params H) : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ := prodAux H A L (Nat.lt_succ_self L)
  def dlnLoss (H) (B) (A : Params H) : ℝ := ∑ i, ∑ j, ((prod H A - B) i j) ^ 2

GOAL: define `scaleLayer (c : ℝ) (s : Fin L) (A : Params H) : Params H` (= A but layer s multiplied by c),
and prove
  (1) prod H (scaleLayer c s A) = c • prod H A           [linearity in one factor]
  (2) dlnLoss H 0 (scaleLayer c s A) = c^2 * dlnLoss H 0 A   [degree-2 homogeneity at B=0]

The product is multilinear: scaling ANY one factor by c scales the whole product by c (Matrix.smul_mul /
Matrix.mul_smul move the scalar out). (2) then follows from (1): entries scale by c, squares by c², sum by c².

QUESTIONS:
1. For (1): is induction on the prodAux recursion the right approach, and what's the cleanest way to
   handle the scaled layer being at an ARBITRARY position s (not just the last)? Two sub-cases per
   recursion step (s = current layer k vs s < k)? Or is there a slicker formulation (e.g. prove a more
   general `prodAux (scaleLayer c s A) k = (if s < k then c else 1) • prodAux A k` style invariant)?
2. The cast juggling (e1/e2, Fin.castSucc/succ, the rw + cast in prodAux) is the friction point. Any
   idiom to avoid fighting the dependent casts — e.g. reformulating scaleLayer so it commutes with the
   prodAux cast rewrites definitionally?
3. Is there an EASIER target that still serves: instead of (1) for arbitrary s, just prove (2) directly
   by an entry-level induction, or is (1) genuinely needed?
4. Concrete Mathlib lemma names (v4.29) for the scalar-out-of-product steps and the sum-of-squares scaling.
</task>

<output_contract>
4 short sections answering 1-4. For each, the cleanest tactic-level route + the specific Mathlib lemma
names. Flag if (1)-for-arbitrary-s is a thrash trap and recommend the simplest sufficient target. Lean 4
Mathlib v4.29 idiom. Terse; this is a route-check, not a full proof.
</output_contract>

<grounding_rules>
You don't have the repo beyond what's quoted. Reason from the prodAux definition given. Flag any lemma
name you're unsure exists at v4.29 (I'll verify with scripts/lean-search). Don't invent Mathlib lemmas.
</grounding_rules>
