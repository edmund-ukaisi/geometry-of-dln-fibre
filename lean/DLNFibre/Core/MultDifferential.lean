import DLNFibre.Core.MatrixKaehler
import DLNFibre.Core.MultComorphism
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# `DLNFibre.Core.MultDifferential` — the differential of `mult` (H2)

The second rung of the HEIGHT-DIRECT route. The Jacobian of the fibre generators (consumed by H3)
has columns indexed by the coordinate variables `X ⟨i, s, t⟩`; the column at `⟨i, s, t⟩` is the
partial derivative of the product entries `multPoly d r c` with respect to that variable. This
module computes that partial derivative in **closed form**.

The multiplication map `mult` is a degree-`N` ordered product `A_{N-1} ⋯ A₀`. Differentiating with
respect to the entries of the single factor `A_i` lands, by the product (Leibniz) rule, on that
factor alone. Splitting `mult = (suffix `A_{N-1} ⋯ A_i`) · (prefix `A_{i-1} ⋯ A₀`)` at `i` and
applying the entrywise matrix-product Leibniz (`Core.MatrixKaehler.derivMatrix_mul_apply`) twice
gives, for the partial derivative `pderiv ⟨i, s, t⟩` (a `Derivation`):

  `pderiv ⟨i,s,t⟩ (multPoly d r c) = (suffix `·s`-column entry) · (prefix `t·`-row entry)`,

a **rank-one** outer product `(suffix column s) ⊗ (prefix row t)` — the structure the
generic-Jacobian rank count (H3) reads off. Evaluated at a tuple `A`, the suffix/prefix become the
actual products `(A_{N-1} ⋯ A_{i+1})` and `(A_{i-1} ⋯ A₀)`.

Deliverables, for `d : Fin (N+1) → ℕ`:

* **`multSuffix`** — the suffix product `A_{N-1} ⋯ A_j : Matrix (Fin d_N) (Fin d_j) k`, the
  right-fold mirror of `Core.Setup.multPrefix`, with `rfl` step lemmas (`multSuffix_last`,
  `multSuffix_castSucc`).
* **`multSuffix_mul_multPrefix`** — the split `mult = multSuffix d A j · multPrefix d A j` at any
  `j`.
* **`pderiv_multPoly`** (H2 headline) — the closed-form partial derivative as the outer product.
* **`eval_pderiv_multPoly`** — the evaluated form: at `A`, the Jacobian entry is
  `(A_{N-1} ⋯ A_{i+1}) r s · (A_{i-1} ⋯ A₀) t c`.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

universe u

variable {k : Type u} [CommRing k] {N : ℕ}

/-! ## The suffix product `A_{N-1} ⋯ A_j` -/

/-- The suffix product `A_{N-1} ⋯ A_j : Matrix (Fin d_N) (Fin d_j) k` of the factors from index `j`
up. Right-fold mirror of `multPrefix`: `multSuffix (last N) = 1`, and the next factor joins on the
**right**, `multSuffix i.castSucc = multSuffix i.succ * A i`. -/
def multSuffix (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) :
    (j : Fin (N + 1)) → Matrix (Fin (d (Fin.last N))) (Fin (d j)) k :=
  Fin.reverseInduction (1 : Matrix (Fin (d (Fin.last N))) (Fin (d (Fin.last N))) k)
    (fun i prev ↦ prev * A i)

/-- The full suffix product is the identity. -/
@[simp] theorem multSuffix_last (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) :
    multSuffix d A (Fin.last N) = 1 :=
  Fin.reverseInduction_last

/-- The suffix product gains its next factor on the right:
`(suffix from i) = (suffix from i.succ) * Aᵢ`. -/
@[simp] theorem multSuffix_castSucc (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) (i : Fin N) :
    multSuffix d A i.castSucc = multSuffix d A i.succ * A i :=
  Fin.reverseInduction_castSucc i

/-- **The split.** `mult = (suffix from `j`) · (prefix to `j`)` at any `j`: the suffix product of
the top factors times the prefix product of the bottom factors is the whole ordered product.
Downward induction on `j` (`Fin.reverseInduction`): the `last N` case is `1 · mult = mult`; the step
splits one factor across the suffix/prefix boundary, `(S * A i) * P = S * (A i * P)`. -/
theorem multSuffix_mul_multPrefix (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) (j : Fin (N + 1)) :
    multSuffix d A j * multPrefix d A j = mult d A := by
  induction j using Fin.reverseInduction with
  | last => rw [multSuffix_last, Matrix.one_mul]; rfl
  | cast i ih =>
    rw [multSuffix_castSucc, Matrix.mul_assoc, ← multPrefix_succ]
    exact ih

/-! ## Support lemmas: the prefix/suffix products do not involve the boundary factor

The prefix `A_{j-1} ⋯ A₀` involves only the factors `A_{i'}` with `i'.castSucc < j`; the suffix
`A_{N-1} ⋯ A_j` involves only the factors with `j ≤ i'.castSucc`. So the partial derivative
`pderiv ⟨i, s, t⟩` of a prefix/suffix entry of the **generic tuple** vanishes whenever the factor
`i` falls outside the respective range. Both by `Fin.induction` on the boundary, using the entrywise
product Leibniz (`derivMatrix_mul_apply`) and `pderiv_X_of_ne` at the mismatched coordinate. -/

variable (d : Fin (N + 1) → ℕ)

/-- The generic prefix product to `j` does not involve the factor `A_i` when `j ≤ i.castSucc`:
`pderiv ⟨i, s, t⟩` of any of its entries vanishes. Induction on `j`. -/
theorem pderiv_multPrefix_genericTuple_eq_zero (i : Fin N)
    (s : Fin (d i.succ)) (t : Fin (d i.castSucc)) (j : Fin (N + 1))
    (hj : j ≤ i.castSucc) (r : Fin (d j)) (c : Fin (d 0)) :
    pderiv (⟨i, s, t⟩ : RepCoord d) ((multPrefix d (genericTuple (k := k) d) j) r c) = 0 := by
  induction j using Fin.induction with
  | zero =>
    rw [multPrefix_zero, Matrix.one_apply]
    split <;> simp
  | succ j' ih =>
    have hj'lt : j'.castSucc < i.castSucc := lt_of_lt_of_le (Fin.castSucc_lt_succ (i := j')) hj
    have hj'le : j'.castSucc ≤ i.castSucc := le_of_lt hj'lt
    rw [multPrefix_succ, derivMatrix_mul_apply]
    refine Finset.sum_eq_zero fun u _ ↦ ?_
    rw [ih hj'le u]
    -- the `genericTuple j'` factor: its entries are `X ⟨j', r, u⟩` with `j' ≠ i`, so pderiv = 0
    have hj'i : j' ≠ i := Fin.ne_of_lt (Fin.castSucc_lt_castSucc_iff.mp hj'lt)
    have hne : (⟨j', r, u⟩ : RepCoord d) ≠ ⟨i, s, t⟩ := fun h ↦ hj'i (congrArg Sigma.fst h)
    simp [genericTuple_apply, pderiv_X_of_ne hne]

/-- The generic suffix product from `j` does not involve the factor `A_i` when `i.succ ≤ j`:
`pderiv ⟨i, s, t⟩` of any of its entries vanishes. Downward induction on `j`
(`Fin.reverseInduction`). -/
theorem pderiv_multSuffix_genericTuple_eq_zero (i : Fin N)
    (s : Fin (d i.succ)) (t : Fin (d i.castSucc)) (j : Fin (N + 1))
    (hj : i.succ ≤ j) (r : Fin (d (Fin.last N))) (c : Fin (d j)) :
    pderiv (⟨i, s, t⟩ : RepCoord d) ((multSuffix d (genericTuple (k := k) d) j) r c) = 0 := by
  induction j using Fin.reverseInduction with
  | last =>
    rw [multSuffix_last, Matrix.one_apply]
    split <;> simp
  | cast j' ih =>
    -- here `hj : i.succ ≤ j'.castSucc`, so `i < j'`
    have hij' : i < j' := Fin.succ_le_castSucc_iff.mp hj
    have hj'le : i.succ ≤ j'.succ := le_trans hj (le_of_lt (Fin.castSucc_lt_succ (i := j')))
    rw [multSuffix_castSucc, derivMatrix_mul_apply]
    refine Finset.sum_eq_zero fun u _ ↦ ?_
    rw [ih hj'le u]
    -- the `genericTuple j'` factor: its entries are `X ⟨j', u, c⟩` with `j' ≠ i`, so pderiv = 0
    have hj'i : j' ≠ i := (Fin.ne_of_lt hij').symm
    have hne : (⟨j', u, c⟩ : RepCoord d) ≠ ⟨i, s, t⟩ := fun h ↦ hj'i (congrArg Sigma.fst h)
    simp [genericTuple_apply, pderiv_X_of_ne hne]

/-! ## The closed-form partial derivative (H2 headline) -/

/-- **H2 — the partial derivative of the product entry.** Differentiating the generic product entry
`multPoly d r c` with respect to the coordinate variable `X ⟨i, s, t⟩` (the `(s,t)` entry of the
`i`-th factor) gives the **rank-one** outer product: the `(r,s)` entry of the generic suffix product
`A_{N-1} ⋯ A_{i+1}` times the `(t,c)` entry of the generic prefix product `A_{i-1} ⋯ A₀`. -/
theorem pderiv_multPoly (i : Fin N)
    (s : Fin (d i.succ)) (t : Fin (d i.castSucc))
    (r : Fin (d (Fin.last N))) (c : Fin (d 0)) :
    pderiv (⟨i, s, t⟩ : RepCoord d) (multPoly (k := k) d r c)
      = multSuffix d (genericTuple d) i.succ r s
        * multPrefix d (genericTuple d) i.castSucc t c := by
  set G := genericTuple (k := k) d with hG
  -- `mult d G = (multSuffix i.succ * G i) * multPrefix i.castSucc`
  have hsplit : mult d G = multSuffix d G i.succ * G i * multPrefix d G i.castSucc := by
    rw [← multSuffix_mul_multPrefix d G i.castSucc, multSuffix_castSucc]
  -- apply Leibniz to the outer product `(multSuffix i.succ * G i) * multPrefix i.castSucc`
  rw [multPoly, hsplit, derivMatrix_mul_apply]
  -- the prefix factor `multPrefix i.castSucc` has zero derivative, so only the `pderiv (M r w)`
  -- term survives, where `M = multSuffix i.succ * G i`
  have hPzero : ∀ w, pderiv (⟨i, s, t⟩ : RepCoord d)
      ((multPrefix d G i.castSucc) w c) = 0 := fun w ↦
    pderiv_multPrefix_genericTuple_eq_zero d i s t i.castSucc le_rfl w c
  simp only [hPzero, smul_zero, zero_add]
  -- `pderiv (M r w) = Σ_v (multSuffix i.succ r v • pderiv (G i v w))`, the suffix term being zero
  have hM : ∀ w, pderiv (⟨i, s, t⟩ : RepCoord d) ((multSuffix d G i.succ * G i) r w)
      = ∑ v, multSuffix d G i.succ r v • pderiv (⟨i, s, t⟩ : RepCoord d) (G i v w) := fun w ↦ by
    rw [derivMatrix_mul_apply]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [pderiv_multSuffix_genericTuple_eq_zero d i s t i.succ le_rfl r v, smul_zero, add_zero]
  simp only [hM]
  -- `pderiv (G i v x) = [⟨i,(v,x)⟩ = ⟨i,(s,t)⟩]`; collapse the inner sum at `v = s`, then the outer
  -- sum at `x = t`.
  have hpd : ∀ (v : Fin (d i.succ)) (x : Fin (d i.castSucc)),
      pderiv (⟨i, s, t⟩ : RepCoord d) (G i v x)
        = if (⟨i, v, x⟩ : RepCoord d) = ⟨i, s, t⟩ then 1 else 0 := fun v x ↦ by
    rw [hG, genericTuple_apply, pderiv_X]
    simp [Pi.single_apply, eq_comm]
  -- inner sum collapses to `if x = t then multSuffix … r s else 0`
  have hinner : ∀ x : Fin (d i.castSucc),
      (∑ v, multSuffix d G i.succ r v • pderiv (⟨i, s, t⟩ : RepCoord d) (G i v x))
        = if x = t then multSuffix d G i.succ r s else 0 := fun x ↦ by
    rw [Finset.sum_eq_single s]
    · rw [hpd s x]
      by_cases hx : x = t
      · subst hx; simp
      · rw [if_neg (by simp [hx]), if_neg hx, smul_zero]
    · intro v _ hv
      rw [hpd v x, if_neg (by simp [hv]), smul_zero]
    · exact fun h ↦ absurd (Finset.mem_univ s) h
  simp only [hinner]
  rw [Finset.sum_eq_single t]
  · rw [if_pos rfl, smul_eq_mul, mul_comm]
  · intro x _ hx; rw [if_neg hx, smul_zero]
  · exact fun h ↦ absurd (Finset.mem_univ t) h

/-- The eval-bridge for the suffix product, companion of `Core.MultComorphism.map_eval_multPrefix`:
the ring hom `eval (canonicalCoord d A)` carries the generic suffix product to the actual suffix
product, entrywise. Downward induction on `j` (`Fin.reverseInduction`). -/
theorem map_eval_multSuffix (A : Tuple (k := k) d) (j : Fin (N + 1)) :
    (multSuffix d (genericTuple (k := k) d) j).map (eval (canonicalCoord d A))
      = multSuffix d A j := by
  induction j using Fin.reverseInduction with
  | last =>
    simp only [multSuffix_last]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  | cast i ih =>
    rw [multSuffix_castSucc, multSuffix_castSucc, Matrix.map_mul, ih, eval_genericTuple]

/-- **The evaluated Jacobian entry.** At a tuple `A`, the partial derivative of `multPoly d r c`
w.r.t. `X ⟨i, s, t⟩` evaluates to `(A_{N-1} ⋯ A_{i+1}) r s · (A_{i-1} ⋯ A₀) t c`. -/
theorem eval_pderiv_multPoly (A : Tuple (k := k) d) (i : Fin N)
    (s : Fin (d i.succ)) (t : Fin (d i.castSucc))
    (r : Fin (d (Fin.last N))) (c : Fin (d 0)) :
    eval (canonicalCoord d A) (pderiv (⟨i, s, t⟩ : RepCoord d) (multPoly (k := k) d r c))
      = multSuffix d A i.succ r s * multPrefix d A i.castSucc t c := by
  rw [pderiv_multPoly, map_mul,
    show eval (canonicalCoord d A) (multSuffix d (genericTuple (k := k) d) i.succ r s)
      = multSuffix d A i.succ r s from by
        have h := map_eval_multSuffix d A i.succ
        have := congrFun (congrFun h r) s
        rwa [Matrix.map_apply] at this,
    show eval (canonicalCoord d A) (multPrefix d (genericTuple (k := k) d) i.castSucc t c)
      = multPrefix d A i.castSucc t c from by
        have h := map_eval_multPrefix d A i.castSucc
        have := congrFun (congrFun h t) c
        rwa [Matrix.map_apply] at this]

/-! ## Non-vacuity witness -/

section Witness

/-- The split `mult = multSuffix · multPrefix` on the `(2,2,2)` witness, at the boundary `j = 1`:
`A₂ · A₁` reproduces the actual product `!![1,2;3,7]`. Shows `multSuffix` and the split compute
(non-vacuous). -/
example : multSuffix dWitness tupleWitness 1 * multPrefix dWitness tupleWitness 1
    = !![1, 2; 3, 7] := by
  rw [multSuffix_mul_multPrefix]
  unfold mult multPrefix tupleWitness dWitness
  decide

/-- The evaluated Jacobian column on the `(2,2,2)` witness at coordinate `⟨1, 0, 0⟩` (the `(0,0)`
entry of the second factor `A₂`), output entry `(0,0)`: the partial derivative of `multPoly 0 0`
evaluates to `(suffix from 2) 0 0 · (prefix to 1) 0 0 = 1 · (A₁) 0 0 = 1` — a genuine, nonzero
Jacobian entry, so the differential `pderiv_multPoly` is non-vacuous. -/
example :
    eval (canonicalCoord dWitness tupleWitness)
        (pderiv (⟨1, ⟨0, by decide⟩, ⟨0, by decide⟩⟩ : RepCoord dWitness)
          (multPoly dWitness ⟨0, by decide⟩ ⟨0, by decide⟩)) = 1 := by
  rw [eval_pderiv_multPoly dWitness tupleWitness 1 ⟨0, by decide⟩ ⟨0, by decide⟩
        ⟨0, by decide⟩ ⟨0, by decide⟩]
  unfold multSuffix multPrefix tupleWitness dWitness
  decide

end Witness

end DLNFibre.Core
