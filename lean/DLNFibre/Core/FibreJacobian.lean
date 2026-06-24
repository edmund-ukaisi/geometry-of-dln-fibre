import DLNFibre.Core.MultDifferential
import DLNFibre.Core.CotangentJacobian

/-!
# `DLNFibre.Core.FibreJacobian` — the Jacobian of the fibre generators (H3a)

Rung **H3a** of the HEIGHT-DIRECT route: assemble the Jacobian of the fibre generators and establish
the tangent-space = `ker(Jacobian)` identity at a rational point of the fibre. This rung is the
*mechanical setup* — it does **not** compute the rank value (`C + δ`, the H3b pen-and-paper job) and
does **not** invoke genericity or smoothness (H3c). No result here claims `codim = C + δ`.

The fibre generators are `g_{(r,c)} = multPoly d r c − C (B r c)`
(`Core.MultComorphism.fibreGenSet`), one per output entry `(r, c) : Fin d_N × Fin d_0`. Presenting
them as the **product-indexed family** `fibreGen d B` (rather than the `Set.range` of
`fibreGenSet`) lets them plug into `Core.CotangentJacobian.jacobianMatrix`, whose row index is now
an arbitrary `Fintype` (generalised from `Fin m`): the rows of the fibre Jacobian *are* the output
entries `(r, c)`, its columns the coordinate variables `⟨i, s, t⟩ : RepCoord d`.

Deliverables, for `d : Fin (N+1) → ℕ` and a target `B`:

* **`fibreGen`** — the generator family; `span (range (fibreGen d B)) = fibreGenIdeal d B`.
* **`eval_fibreGen_eq_zero`** — at a tuple `A` in the fibre (`mult d A = B`), every generator
  vanishes at `canonicalCoord d A` — the rational-point hypothesis the cotangent headline consumes.
* **`fibreJacobianMatrix` / `fibreJacobian`** — the Jacobian matrix / linear map of the fibre
  generators at `A`, with **`fibreJacobianMatrix_apply`** giving the closed-form entry
  `(A_{N-1} ⋯ A_{i+1}) r s · (A_{i-1} ⋯ A₀) t c` (the constant `C (B r c)` is killed by `pderiv`, so
  the entry is exactly `Core.MultDifferential.eval_pderiv_multPoly`).
* **`finrank_cotangentSpace_fibre_eq_finrank_ker`** (the tangent = ker identity) — the local
  cotangent space of the fibre ring at `A` has `k`-dimension `= finrank (ker (fibreJacobian))`,
  unconditionally (no smoothness), reusing
  `Core.CotangentJacobian.finrank_cotangentSpace_eq_finrank_ker_jacobian`.
* **`finrank_ker_add_rank_fibreJacobianMatrix`** — the card-rank reading
  `finrank (ker) + rank(matrix) = card (RepCoord d)`, into which H3b plugs `rank = C + δ` to read
  `finrank (ker) = card − C − δ`.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial Module IsLocalRing

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## The fibre generators as a product-indexed family -/

/-- The fibre generators `g_{(r,c)} = multPoly d r c − C (B r c)`, indexed by the output entry
`(r, c) : Fin d_N × Fin d_0`. The product-indexed presentation of `fibreGenSet d B`, so it plugs
directly into `jacobianMatrix` (whose rows the entries become). -/
noncomputable def fibreGen (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) :
    Fin (d (Fin.last N)) × Fin (d 0) → MvPolynomial (RepCoord d) k :=
  fun rc ↦ multPoly d rc.1 rc.2 - C (B rc.1 rc.2)

/-- `range (fibreGen d B)` is the generating set `fibreGenSet d B`. -/
theorem range_fibreGen (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) :
    Set.range (fibreGen d B) = fibreGenSet d B := rfl

/-- The span of the fibre generators is the fibre generator ideal `fibreGenIdeal d B`. -/
theorem span_range_fibreGen (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) :
    Ideal.span (Set.range (fibreGen d B)) = fibreGenIdeal d B := rfl

/-- At a tuple `A` in the fibre (`mult d A = B`), every fibre generator vanishes at the rational
point `canonicalCoord d A`: `eval (canonicalCoord d A) (multPoly d r c − C (B r c)) = 0`. The
rational-point hypothesis the cotangent headline consumes. -/
theorem eval_fibreGen_eq_zero (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) (A : Tuple (k := k) d)
    (hA : mult d A = B) (rc : Fin (d (Fin.last N)) × Fin (d 0)) :
    eval (canonicalCoord d A) (fibreGen d B rc) = 0 := by
  rw [fibreGen, map_sub, eval_multPoly, eval_C, hA, sub_self]

/-! ## The fibre Jacobian -/

/-- **The fibre Jacobian matrix** at a tuple `A`: rows = output entries `(r, c)`, columns =
coordinate variables `⟨i, s, t⟩ : RepCoord d`. Entry `((r,c), ⟨i,s,t⟩)` is the partial derivative of
`multPoly d r c − C (B r c)` w.r.t. `X ⟨i,s,t⟩`, evaluated at `canonicalCoord d A`. -/
noncomputable def fibreJacobianMatrix (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) (A : Tuple (k := k) d) :
    Matrix (Fin (d (Fin.last N)) × Fin (d 0)) (RepCoord d) k :=
  jacobianMatrix (fibreGen d B) (canonicalCoord d A)

/-- **The fibre Jacobian** as a `k`-linear map `(RepCoord d → k) →ₗ[k] (Fin d_N × Fin d_0 → k)`
(multiplication by `fibreJacobianMatrix`). The tangent space to the fibre at `A` is its kernel. -/
noncomputable def fibreJacobian (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) (A : Tuple (k := k) d) :
    (RepCoord d → k) →ₗ[k] (Fin (d (Fin.last N)) × Fin (d 0) → k) :=
  jacobian (fibreGen d B) (canonicalCoord d A)

/-- **The fibre Jacobian entry in closed form.** The constant `C (B r c)` is killed by `pderiv`, so
the `((r,c), ⟨i,s,t⟩)` entry is exactly the evaluated differential of the product entry
(`Core.MultDifferential.eval_pderiv_multPoly`): the outer product
`(A_{N-1} ⋯ A_{i+1}) r s · (A_{i-1} ⋯ A₀) t c`. -/
theorem fibreJacobianMatrix_apply (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) (A : Tuple (k := k) d)
    (r : Fin (d (Fin.last N))) (c : Fin (d 0)) (i : Fin N)
    (s : Fin (d i.succ)) (t : Fin (d i.castSucc)) :
    fibreJacobianMatrix d B A (r, c) ⟨i, s, t⟩
      = multSuffix d A i.succ r s * multPrefix d A i.castSucc t c := by
  rw [fibreJacobianMatrix, jacobianMatrix, fibreGen, map_sub, pderiv_C, sub_zero,
    eval_pderiv_multPoly]

/-! ## The tangent = ker identity (unconditional) and the card-rank reading -/

/-- **Tangent = ker Jacobian.** For a tuple `A` in the fibre (`mult d A = B`), the local cotangent
space of the fibre coordinate ring at the rational point `canonicalCoord d A` has `k`-dimension
equal to `finrank (ker (fibreJacobian d B A))`. Unconditional (no smoothness, no genericity),
reusing `Core.CotangentJacobian.finrank_cotangentSpace_eq_finrank_ker_jacobian`. The localised
ideal is `maxIdealAt (fibreGen d B) (canonicalCoord d A) hg`, whose underlying ideal is the
localisation of `fibreGenIdeal d B` (`span (range (fibreGen d B)) = fibreGenIdeal d B`) at `A`. -/
theorem finrank_cotangentSpace_fibre_eq_finrank_ker (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) (A : Tuple (k := k) d)
    (hA : mult d A = B) :
    finrank k (CotangentSpace (Localization.AtPrime
        (maxIdealAt (fibreGen d B) (canonicalCoord d A) (eval_fibreGen_eq_zero d B A hA))))
      = finrank k (LinearMap.ker (fibreJacobian d B A)) :=
  finrank_cotangentSpace_eq_finrank_ker_jacobian (fibreGen d B) (canonicalCoord d A)
    (eval_fibreGen_eq_zero d B A hA)

/-- **The card-rank reading.** `finrank (ker (fibreJacobian)) + rank (fibreJacobianMatrix) =
card (RepCoord d)`. H3b supplies `rank (fibreJacobianMatrix) = C + δ` at a generic `A`, giving
`finrank (ker) = card − C − δ`; H3c supplies smoothness so this kernel dimension is the local
dimension of the fibre. The number of columns `card (RepCoord d)` is the total number of matrix
entries `∑ i, d_{i+1} · d_i`. -/
theorem finrank_ker_add_rank_fibreJacobianMatrix (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) (A : Tuple (k := k) d) :
    finrank k (LinearMap.ker (fibreJacobian d B A)) + (fibreJacobianMatrix d B A).rank
      = Fintype.card (RepCoord d) := by
  have h : finrank k (LinearMap.range (fibreJacobian d B A))
      + finrank k (LinearMap.ker (fibreJacobian d B A)) = Fintype.card (RepCoord d) := by
    rw [LinearMap.finrank_range_add_finrank_ker]; simp
  have hr : finrank k (LinearMap.range (fibreJacobian d B A)) = (fibreJacobianMatrix d B A).rank :=
    rfl
  omega

/-! ## Non-vacuity witness -/

section Witness

/-- The witness tuple `(A₁, A₂)` over `ℚ` (the `(2,2,2)` witness of `Core.Setup`, over a field so
the fibre Jacobian — gated by `[Field k]` for the cotangent identity — instantiates). -/
def tupleWitnessQ : Tuple (k := ℚ) dWitness := fun i ↦
  match i with
  | 0 => !![1, 2; 0, 1]
  | 1 => !![1, 0; 3, 1]

/-- The `(2,2,2)` fibre Jacobian at the witness tuple, entry `((0,0), ⟨0,0,0⟩)`: the partial of the
generator `multPoly 0 0 − C (B 0 0)` w.r.t. `X ⟨0,0,0⟩` (the `(0,0)` entry of the first factor `A₀`)
equals `(suffix from 1) 0 0 · (prefix to 0) 0 0 = (A₁) 0 0 · 1 = 1` — a genuine, nonzero
fibre-Jacobian entry, so the assembly is non-vacuous. -/
example :
    fibreJacobianMatrix dWitness (!![1, 2; 3, 7]) tupleWitnessQ
        (⟨0, by decide⟩, ⟨0, by decide⟩) ⟨0, ⟨0, by decide⟩, ⟨0, by decide⟩⟩ = 1 := by
  rw [fibreJacobianMatrix_apply]
  unfold multSuffix multPrefix tupleWitnessQ dWitness
  decide +kernel

end Witness

end DLNFibre.Core
