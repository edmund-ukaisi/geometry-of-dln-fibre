<task>
Lean 4 + Mathlib v4.29.0. I am proving `prodAux_front_peel` by induction on k. The BASE CASE is DONE.
I am stuck on TWO specific mechanical sub-steps in the INDUCTIVE STEP. I need the exact tactics.

## Context (all PROVEN / available)

```lean
-- left-associated dependent matrix product; prodAux_succ peels the LAST layer:
theorem prodAux_succ (H : Fin (L + 1) → ℕ) (A : Params H) (k : ℕ) (hk : k + 1 < L + 1)
    (e1 : H (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin (L+1)) = H ((⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).castSucc))
    (e2 : H (⟨k + 1, hk⟩ : Fin (L+1)) = H ((⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin L).succ)) :
    prodAux H A (k + 1) hk = prodAux H A k (Nat.lt_of_succ_lt hk) *
        (Matrix.reindex (finCongr e1.symm) (finCongr e2.symm) (A ⟨k, Nat.lt_of_succ_lt_succ hk⟩)) := by
  obtain rfl : e1 = rfl := Subsingleton.elim _ _; obtain rfl : e2 = rfl := Subsingleton.elim _ _; rfl

-- reindex distributes over a product:
theorem reindex_finCongr_mul {a b c a' b' c' : ℕ} (ha : a = a') (hb : b = b') (hc : c = c')
    (X : Matrix (Fin a) (Fin b) ℝ) (Y : Matrix (Fin b) (Fin c) ℝ) :
    Matrix.reindex (finCongr ha) (finCongr hc) (X * Y)
      = Matrix.reindex (finCongr ha) (finCongr hb) X * Matrix.reindex (finCongr hb) (finCongr hc) Y

-- the tail layers, as a Params (Mtail M):
def Mtail (M : Fin (L + 1 + 1) → ℕ) : Fin (L + 1) → ℕ := fun i => M i.succ
def Atail (M : Fin (L + 1 + 1) → ℕ) (A : Params M) : Params (Mtail M) := fun s =>
  (by
    have e1 : Mtail M s.castSucc = M s.succ.castSucc := by simp only [Mtail]; congr 1
    have e2 : Mtail M s.succ = M s.succ.succ := rfl
    rw [e1, e2]; exact A s.succ :
    Matrix (Fin (Mtail M s.castSucc)) (Fin (Mtail M s.succ)) ℝ)
```

## The inductive step, current state

After `rw [prodAux_succ M A (k+1) hk eP1 eP2]`, `rw [ih ...]`, `rw [prodAux_succ (Mtail M) (Atail M A) k ...]`,
`rw [reindex_finCongr_mul emid hb ecol ...]`, the GOAL is EXACTLY (copied from Lean, `⋯` = elided proofs):

```
A 0 * (reindex (finCongr emid) (finCongr ecolk)) (prodAux (Mtail M) (Atail M A) k ⋯) *
    (reindex (finCongr eP1.symm) (finCongr eP2.symm)) (A ⟨k + 1, ⋯⟩) =
  A 0 *
    ((reindex (finCongr emid) (finCongr hb)) (prodAux (Mtail M) (Atail M A) k ⋯) *
      (reindex (finCongr hb) (finCongr ecol)) ((reindex (finCongr eT1.symm) (finCongr eT2.symm)) (Atail M A ⟨k, ⋯⟩)))
```

where (ALL these width equalities are `rfl`-TRUE, just not syntactically rfl):
- `emid : Mtail M 0 = M (Fin.succ 0)`        [row of A0's right factor; fixed]
- `ecolk : Mtail M ⟨k,_⟩ = M ⟨k+1,_⟩`         [from IH]
- `hb : Mtail M ⟨k,_⟩ = M ⟨k+1,_⟩`            [middle interface; SAME TYPE as ecolk, rfl]
- `ecol : Mtail M ⟨k+1,_⟩ = M ⟨k+2,_⟩`        [outer column]
- `eP1 : M ⟨k+1,_⟩ = M (⟨k+1,_⟩.castSucc)`, `eP2 : M ⟨k+2,_⟩ = M (⟨k+1,_⟩.succ)`  [parent peel, rfl]
- `eT1 : Mtail M ⟨k,_⟩ = Mtail M (⟨k,_⟩.castSucc)`, `eT2 : Mtail M ⟨k+1,_⟩ = Mtail M (⟨k,_⟩.succ)` [tail peel, rfl]

The matrix types in the goal:
- `A 0 : Matrix (Fin (M 0)) (Fin (M (Fin.succ 0)))`  [= Fin (M 0) × Fin (M 1)]
- both `reindex ... (prodAux tail k)` factors : `Matrix (Fin (M 0)) (Fin (M ⟨k+1,_⟩))`
- `reindex (finCongr eP1.symm)(finCongr eP2.symm)(A ⟨k+1,_⟩)` : `Matrix (Fin (M ⟨k+1,_⟩)) (Fin (M ⟨k+2,_⟩))`
- the doubly-reindexed `Atail M A ⟨k,_⟩` factor : also `Matrix (Fin (M ⟨k+1,_⟩)) (Fin (M ⟨k+2,_⟩))`

## SUB-STEP 1 (reassociation): I cannot turn LHS `(A0 * X) * Y` into `A0 * (X * Y)`.
`rw [Matrix.mul_assoc]`, `rw [mul_three_reassoc]` (a Type*-generic `a*b*c = a*(b*c)`), and
`conv_lhs => rw [mul_three_reassoc]` ALL fail with "Did not find an occurrence of the pattern `?a * ?b * ?c`"
— the dependent-dimension HMul (`instHMulOfFintypeOfMulOfAddCommMonoid`) defeats higher-order `rw` matching.
The pattern Lean reports wanting: `@HMul.hMul (Matrix ?m ?m ℝ) (Matrix ?m ?m ℝ) (Matrix ?m ?m ℝ) inst (?a * ?b) ?c`.
`simp only [Matrix.mul_assoc]` reports "no progress".

## SUB-STEP 2 (layer identification): after I split with `congr 1`, the second goal is
```
(reindex (finCongr eP1.symm) (finCongr eP2.symm)) (A ⟨k+1,_⟩)
  = (reindex (finCongr hb) (finCongr ecol)) ((reindex (finCongr eT1.symm) (finCongr eT2.symm)) (Atail M A ⟨k,_⟩))
```
i.e. parent layer `A ⟨k+1,_⟩` reindexed = tail layer `(Atail M A) ⟨k,_⟩` doubly-reindexed. They live at the
SAME type `Matrix (Fin (M ⟨k+1,_⟩)) (Fin (M ⟨k+2,_⟩))`. The content: `(Atail M A) ⟨k,_⟩` is `A ⟨k,_⟩.succ = A ⟨k+1,_⟩`
modulo the `Atail` def's `Eq.mpr` cast, and all the finCongr are rfl-true so collapse to refl.
</task>

<output_contract>
Give me, CONCRETELY:

1. SUB-STEP 1: the exact tactic to reassociate `(A0 * X) * Y → A0 * (X * Y)` through a dependent-dimension
   HMul that defeats `rw`. Options to evaluate and pick the most robust: (i) `Matrix.mul_assoc` as a
   fully-applied TERM in a `calc`/`Eq.trans` (does `exact`'s defeq unification dodge the rw-matching?);
   (ii) restructure so I never reassociate — e.g. apply `prodAux_succ` to the WHOLE `prodAux M A (k+1+1)`
   and `ih` in a different order; (iii) `show` the LHS into the explicit dependent type then a term proof.
   If a fully-applied `Matrix.mul_assoc A0 X Y` term works via `exact` or `rw [Matrix.mul_assoc A0 X Y]`
   with X, Y given as the exact goal subterms, say so and give the precise syntax for extracting X, Y
   (e.g. via `set X := ... with hX`).

2. SUB-STEP 2: the exact tactic chain for the layer identification. I expect: collapse all `finCongr e =
   Equiv.refl _` via `finCongr_refl`, then `reindex_refl_refl` (via `erw`, since plain `rw`/`simp` won't
   match the dependent `Matrix.reindex`), reducing both sides to `A ⟨k+1,_⟩` vs `Atail M A ⟨k,_⟩`, then a
   defeq `rfl` or a `cases`-on-the-Atail-cast. Give the precise sequence. In particular: how do I prove
   `A ⟨k+1,_⟩ = (Atail M A) ⟨k,_⟩` when the two have defeq-but-not-syntactic-equal `Matrix` types and the
   `Atail` def hides an `Eq.mpr`? (e.g. is the right move to first prove a clean `Atail_apply` rewrite lemma
   `(Atail M A) ⟨k,h⟩ = reindex (finCongr _) (finCongr _) (A ⟨k+1,_⟩)` by the `prodAux_succ` Subsingleton.elim
   idiom, then everything is reindex algebra? give that lemma's statement + proof.)

Concrete Lean over prose. Mark any lemma you are unsure exists in v4.29 as VERIFY. <600 words.
</output_contract>

<grounding_rules>
Design advice; I run everything locally. Distinguish "this will work" from "shape is right, cast details
may need a tweak". The base case already worked with: `prodAux_succ` then four
`rw [show (finCongr e.symm) = Equiv.refl _ from finCongr_refl _]` then `erw [Matrix.reindex_refl_refl, ...]`
then `erw [Matrix.one_mul, Matrix.mul_one]; rfl`. So that idiom is CONFIRMED working in this exact setting.
</grounding_rules>
