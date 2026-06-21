import DLNFibre.Core.OrbitVariety
import DLNFibre.Core.PolynomialCurveLimit

/-!
# `DLNFibre.Core.BoxMoveDegeneration` — the box-move degeneration (L6.1)

The per-move building block of the orbit-closure order (Abeasis–Del Fra, the "hard" direction of
Lehalleur–Rimányi 2024 Thm 3.8). For interval data with `a < c ≤ b+1 ≤ e`, the **downstairs** tuple
`M_{[a,b]} ⊕ M_{[c,e]} ⊕ rest` lies in the Zariski closure of the orbit of the **upstairs** tuple
`M_{[a,e]} ⊕ M_{[c,b]} ⊕ rest` (`M_{[c,b]} = 0` when `c = b+1`, the split case). The mechanism is
the one-parameter extension family

    0 → M_{[c,e]} → M_{[a,e]} ⊕ M_{[c,b]} → M_{[a,b]} → 0,   extension class t

`t ≠ 0` gives the upstairs middle term (an orbit point of `upstairs`); `t = 0` gives the split
downstairs sum. Concretely: a family `F : k → Tuple d`, entrywise polynomial in `t`, with
`F 0 = downstairs` and `F t ∈ orbit(upstairs)` for `t ≠ 0`.

**The engine** `mem_zeroLocus_vanishingIdeal_orbitSet_of_polynomialFamily` is the reusable,
network-free core (it consumes L6.0): from a polynomial-coefficient tuple `Fpoly` with
`Fpoly.eval 0 = D` and `Fpoly.eval t ∈ orbit(U)` for every `t ≠ 0`, it derives

    canonicalCoord d D ∈ zeroLocus (vanishingIdeal (orbitSet U))

i.e. `D` is in the Zariski closure of `orbit(U)` — the L6.0-consumption shape that feeds the
cover-classification chain L6.2. Any degeneration family (box move, split, …) plugs into it by
supplying its `Fpoly` and the two hypotheses; it is fully general in the dimension vector `d`.

**Witness.** The certified small instance `M_{[0,2]} ⊕ M_{[1,1]} ⇝ M_{[0,1]} ⊕ M_{[1,2]}` over
`d = (1,2,1)` supplies one such `Fpoly` explicitly (`boxMoveWitnessFamilyPoly`, cut arrow
`[X, C 1]`): its `t ≠ 0` orbit certificate is the explicit base change `P₁ = [[1,-t⁻¹],[0,1]]`,
`P₂ = [t]` (`boxMoveWitnessFamily_mem_orbit`), and the headline
`boxMoveWitness_downstairs_mem_closure` reads the engine's conclusion. **The general box-move
construction** (the family + base change for arbitrary `a < c ≤ b+1 ≤ e` and arbitrary `rest`) is
the remaining gap above the engine — see the thread report.

**Typeclass.** `[Field k]` (the `t⁻¹` orbit certificate); `[Infinite k]` for the limit lemma (an
algebraically closed field is automatically infinite). **Dependency rule:** `Core` only.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

universe u

variable {k : Type u} [Field k]

/-! ## The degeneration engine: a polynomial family lands the limit in the orbit closure

The reusable, network-free core of L6.1 (and of any one-parameter degeneration on `Tuple d`):
package a degeneration as a tuple `Fpoly` of *univariate polynomials* — `Fpoly i r c : k[X]` is the
`(r,c)` entry of edge `i`, polynomial in the parameter `t`. Its `eval`-at-`t` is a tuple
`Fpoly.eval t : Tuple d`. If the limit `Fpoly.eval 0` is the **downstairs** tuple `D`, and for every
`t ≠ 0` the point `Fpoly.eval t` lies in the orbit of the **upstairs** tuple `U`, then `D`'s
flattening lies in the Zariski closure of `orbitSet U`. This is exactly the L6.0-consumption shape;
the box-move construction below supplies one such `Fpoly`. -/

/-- The `eval`-at-`t` tuple of a polynomial tuple: edge `i` is `(Fpoly i).map (eval t)`. -/
noncomputable def tupleEval {d : Fin (N + 1) → ℕ} (Fpoly : Tuple (k := Polynomial k) d) (t : k) :
    Tuple (k := k) d :=
  fun i ↦ (Fpoly i).map (Polynomial.eval t)

/-- The flattening curve of a polynomial-coefficient tuple: coordinate `⟨i,r,c⟩` is the entry
polynomial `Fpoly i r c`. Its `curvePoint` at `t` is `canonicalCoord (Fpoly.eval t)`. -/
noncomputable def tupleCurve {d : Fin (N + 1) → ℕ} (Fpoly : Tuple (k := Polynomial k) d) :
    RepCoord d → Polynomial k :=
  fun x ↦ Fpoly x.1 x.2.1 x.2.2

/-- `curvePoint (tupleCurve Fpoly) t = canonicalCoord (tupleEval Fpoly t)`: the flattening curve
evaluated at `t` is the flattened `eval`-tuple (definitional through `Matrix.map_apply`). -/
theorem curvePoint_tupleCurve {d : Fin (N + 1) → ℕ} (Fpoly : Tuple (k := Polynomial k) d) (t : k) :
    curvePoint (tupleCurve Fpoly) t = canonicalCoord d (tupleEval Fpoly t) := by
  funext x
  rw [curvePoint_apply, canonicalCoord_apply, tupleCurve, tupleEval, Matrix.map_apply]

/-- **The degeneration engine (L6.1 core).** Over an infinite field, if a polynomial-coefficient
tuple `Fpoly` has limit `Fpoly.eval 0 = D` and every `t ≠ 0` point `Fpoly.eval t` lies in the orbit
of `U` (`∃ P, P • U = Fpoly.eval t`), then the flattening of `D` lies in the Zariski closure of the
orbit of `U`: `canonicalCoord D ∈ zeroLocus (vanishingIdeal (orbitSet U))`. The L6.0-consumption
shape, factored out of any specific degeneration family. -/
theorem mem_zeroLocus_vanishingIdeal_orbitSet_of_polynomialFamily [Infinite k]
    {d : Fin (N + 1) → ℕ} (U D : Tuple (k := k) d) (Fpoly : Tuple (k := Polynomial k) d)
    (h0 : tupleEval Fpoly 0 = D)
    (horb : ∀ t : k, t ≠ 0 → ∃ P : BaseChangeGroup (k := k) d, P • U = tupleEval Fpoly t) :
    canonicalCoord d D
      ∈ MvPolynomial.zeroLocus (σ := RepCoord d) (k := k) k
          (MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k (orbitSet U)) := by
  have hlim : curvePoint (tupleCurve Fpoly) 0 = canonicalCoord d D := by
    rw [curvePoint_tupleCurve, h0]
  rw [← hlim]
  refine curvePoint_zero_mem_zeroLocus_vanishingIdeal (tupleCurve Fpoly) (orbitSet U)
    (fun t ht ↦ ?_)
  rw [curvePoint_tupleCurve]
  obtain ⟨P, hP⟩ := horb t ht
  exact ⟨tupleEval Fpoly t, ⟨P, hP⟩, rfl⟩

/-! ## The certified `(1,2,1)` witness instance

`M_{[0,2]} ⊕ M_{[1,1]} ⇝ M_{[0,1]} ⊕ M_{[1,2]}` over `d = (1,2,1)` (`N = 2`, `Fin 3`). The three
tuples are written explicitly: edge `0 : Matrix (Fin 2) (Fin 1) k` and edge `1 : Matrix (Fin 1)
(Fin 2) k`. The recombination arrow is edge `1`; the family perturbs it by `[t, 1]`. -/

/-- The witness dimension vector `(1, 2, 1)`. -/
def boxDim : Fin 3 → ℕ := ![1, 2, 1]

/-- The **upstairs** tuple `M_{[0,2]} ⊕ M_{[1,1]}`: edge `0 = [[1],[0]]`, edge `1 = [[1,0]]`
(rank pattern `r_{01} = r_{12} = r_{02} = 1`). -/
def boxMoveWitnessUp : Tuple (k := k) boxDim := fun i ↦
  match i with
  | 0 => !![1; 0]
  | 1 => !![1, 0]

/-- The **downstairs** tuple `M_{[0,1]} ⊕ M_{[1,2]}`: edge `0 = [[1],[0]]`, edge `1 = [[0,1]]`
(rank pattern `r_{01} = r_{12} = 1`, `r_{02} = 0`). -/
def boxMoveWitnessDown : Tuple (k := k) boxDim := fun i ↦
  match i with
  | 0 => !![1; 0]
  | 1 => !![0, 1]

/-- The one-parameter family `F t : Tuple (1,2,1)`: edge `0 = [[1],[0]]` (unperturbed), cut arrow
edge `1 = [[t, 1]]`. `F 0 = downstairs`; for `t ≠ 0`, `F t` is in the orbit of `upstairs`. -/
def boxMoveWitnessFamily (t : k) : Tuple (k := k) boxDim := fun i ↦
  match i with
  | 0 => !![1; 0]
  | 1 => !![t, 1]

/-- `F 0 = downstairs`: at `t = 0` the cut arrow `[0, 1]` is the split sum's edge map. -/
theorem boxMoveWitnessFamily_zero :
    boxMoveWitnessFamily (0 : k) = boxMoveWitnessDown := by
  funext i
  fin_cases i <;> simp [boxMoveWitnessFamily, boxMoveWitnessDown]

/-! ## The `t ≠ 0` orbit certificate: an explicit base change `P • upstairs = F t`

For `t ≠ 0`, the base change `P₀ = 1`, `P₁ = [[1, -t⁻¹],[0,1]]`, `P₂ = [t]` carries `upstairs` to
`F t`: it fixes edge `0` (`P₁ · [[1],[0]] = [[1],[0]]`) and turns edge `1`'s `[[1,0]]` into the cut
arrow `[[t,1]]` (`[t] · [[1,0]] · P₁⁻¹ = [[t,1]]`). `P₁`/`P₂` are units (explicit inverses, needing
`t ≠ 0`). The recombination is genuinely at the overlap vertex `1` and the right-tail scalar `t`. -/

/-- The vertex-`1` base-change unit `[[1, -t⁻¹],[0,1]]`, with inverse `[[1, t⁻¹],[0,1]]` (the
inverse holds for every `t`: the off-diagonals cancel). -/
def boxMoveUnit₁ (t : k) : (Matrix (Fin 2) (Fin 2) k)ˣ where
  val := !![1, -t⁻¹; 0, 1]
  inv := !![1, t⁻¹; 0, 1]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The vertex-`2` base-change unit `[t]` (right-tail scalar), with inverse `[t⁻¹]` (`t ≠ 0`). -/
def boxMoveUnit₂ {t : k} (ht : t ≠ 0) : (Matrix (Fin 1) (Fin 1) k)ˣ where
  val := !![t]
  inv := !![t⁻¹]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, mul_inv_cancel₀ ht]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, inv_mul_cancel₀ ht]

/-- The matrix value of the inverse unit `(boxMoveUnit₁ t)⁻¹` (its `inv` field) is `[[1,t⁻¹],[0,1]]`
— the inverse the conjugation at the overlap vertex needs. -/
theorem boxMoveUnit₁_inv_val (t : k) :
    (Units.val (boxMoveUnit₁ t)⁻¹ : Matrix (Fin 2) (Fin 2) k) = !![1, t⁻¹; 0, 1] := by
  rw [← Units.inv_eq_val_inv]; rfl

/-- The base change carrying `upstairs` to `F t` (`t ≠ 0`): identity at vertex `0`, `boxMoveUnit₁`
at vertex `1`, `boxMoveUnit₂` at vertex `2`. -/
def boxMoveBaseChange {t : k} (ht : t ≠ 0) : BaseChangeGroup (k := k) boxDim :=
  fun v ↦ match v with
    | 0 => 1
    | 1 => boxMoveUnit₁ t
    | 2 => boxMoveUnit₂ ht

/-- **The `t ≠ 0` orbit certificate.** `boxMoveBaseChange ht • upstairs = F t`: the explicit base
change carries the upstairs interval sum to the perturbed family `F t`. -/
theorem boxMoveBaseChange_smul {t : k} (ht : t ≠ 0) :
    boxMoveBaseChange ht • boxMoveWitnessUp = boxMoveWitnessFamily t := by
  funext e
  rw [smul_eq_baseChange, baseChange_apply]
  fin_cases e
  · -- edge 0 : P₁ · [[1],[0]] · (P₀)⁻¹ = [[1],[0]] (vertex-0 unit is the identity)
    change Units.val (boxMoveUnit₁ t) * (!![1; 0] : Matrix (Fin 2) (Fin 1) k)
        * Units.val (1 : (Matrix (Fin 1) (Fin 1) k)ˣ)⁻¹ = !![1; 0]
    rw [show Units.val (1 : (Matrix (Fin 1) (Fin 1) k)ˣ)⁻¹ = 1 by simp, Matrix.mul_one]
    simp only [boxMoveUnit₁]
    ext r c; fin_cases r <;> fin_cases c <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · -- edge 1 : P₂ · [[1,0]] · (P₁)⁻¹ = [[t,1]]
    change Units.val (boxMoveUnit₂ ht) * (!![1, 0] : Matrix (Fin 1) (Fin 2) k)
        * Units.val (boxMoveUnit₁ t)⁻¹ = !![t, 1]
    rw [boxMoveUnit₁_inv_val t]
    simp only [boxMoveUnit₂]
    ext r c; fin_cases r <;> fin_cases c <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ ht]

/-- For `t ≠ 0`, `F t` lies in the orbit of `upstairs` (the `t ≠ 0` membership feeding L6.0). -/
theorem boxMoveWitnessFamily_mem_orbit {t : k} (ht : t ≠ 0) :
    ∃ P : BaseChangeGroup (k := k) boxDim, P • boxMoveWitnessUp = boxMoveWitnessFamily t :=
  ⟨boxMoveBaseChange ht, boxMoveBaseChange_smul ht⟩

/-! ## The witness polynomial family and the headline (L6.0 consumption)

The family `F t` is the `eval`-at-`t` of one polynomial tuple: the cut-arrow entry is `X`
(eval `t = t`), every other entry is a constant. The engine
`mem_zeroLocus_vanishingIdeal_orbitSet_of_polynomialFamily` then lands the headline from the limit
(`t = 0`, downstairs) and the `t ≠ 0` orbit membership. -/

/-- The polynomial-coefficient tuple: edge `0 = [[C 1],[C 0]]`, cut arrow edge `1 = [[X, C 1]]`. Its
entrywise `eval t` is the family `F t`. -/
noncomputable def boxMoveWitnessFamilyPoly : Tuple (k := Polynomial k) boxDim := fun i ↦
  match i with
  | 0 => !![Polynomial.C 1; Polynomial.C 0]
  | 1 => !![Polynomial.X, Polynomial.C 1]

/-- The `eval`-at-`t` of the polynomial tuple is the family `F t`: `tupleEval Fpoly t = F t`. -/
theorem tupleEval_boxMoveWitnessFamilyPoly (t : k) :
    tupleEval boxMoveWitnessFamilyPoly t = boxMoveWitnessFamily t := by
  funext i
  fin_cases i
  · change (!![Polynomial.C 1; Polynomial.C 0] : Matrix (Fin 2) (Fin 1) (Polynomial k)).map
        (Polynomial.eval t) = !![1; 0]
    ext r c; fin_cases r <;> fin_cases c <;> simp
  · change (!![Polynomial.X, Polynomial.C 1] : Matrix (Fin 1) (Fin 2) (Polynomial k)).map
        (Polynomial.eval t) = !![t, 1]
    ext r c; fin_cases r <;> fin_cases c <;> simp

/-- **The box-move degeneration (L6.1, witness).** Over an infinite field, the downstairs flattening
`canonicalCoord (M_{[0,1]} ⊕ M_{[1,2]})` lies in the Zariski closure of the orbit of the upstairs
`M_{[0,2]} ⊕ M_{[1,1]}`: it is in `zeroLocus (vanishingIdeal (orbitSet upstairs))`. An instance of
the degeneration engine `mem_zeroLocus_vanishingIdeal_orbitSet_of_polynomialFamily`: the polynomial
family `boxMoveWitnessFamilyPoly` has limit `F 0 = downstairs` and every `t ≠ 0` point in
`orbit(upstairs)` (`boxMoveWitnessFamily_mem_orbit`), so the `t = 0` limit lies in the closure. -/
theorem boxMoveWitness_downstairs_mem_closure [Infinite k] :
    canonicalCoord boxDim boxMoveWitnessDown
      ∈ MvPolynomial.zeroLocus (σ := RepCoord boxDim) (k := k) k
          (MvPolynomial.vanishingIdeal (σ := RepCoord boxDim) (K := k) k
            (orbitSet boxMoveWitnessUp)) := by
  refine mem_zeroLocus_vanishingIdeal_orbitSet_of_polynomialFamily boxMoveWitnessUp
    boxMoveWitnessDown boxMoveWitnessFamilyPoly ?_ (fun t ht ↦ ?_)
  · rw [tupleEval_boxMoveWitnessFamilyPoly, boxMoveWitnessFamily_zero]
  · rw [tupleEval_boxMoveWitnessFamilyPoly]
    exact boxMoveWitnessFamily_mem_orbit ht

end DLNFibre.Core
