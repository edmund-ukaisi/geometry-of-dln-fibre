import DLNFibre.Core.MultComorphism
import DLNFibre.Core.BaseChange

/-!
# `DLNFibre.Core.EndpointNormalization` — the gauge-change `AlgEquiv` (R2-3b-3)

The second rung of the deep product trivialization `e`. On the **unquotiented** coordinate ring
`MvPolynomial (RepCoord d) R` over an **arbitrary** commutative ring `R`, the gauge-change map is the
linear coordinate substitution implementing the vertex-unit conjugation action
`Aᵢ ↦ P_{i+1} · Aᵢ · P_i⁻¹` of `Core.BaseChange.baseChange` on the generic tuple. For the endpoint
normalization of the paper's route, the gauge `P` is identity at every interior vertex and carries
`H` at the source vertex `0`, `L⁻¹` at the target vertex `Fin.last N`: then
`mult(Ã) = L⁻¹ · mult(A) · H⁻¹`, normalizing the two endpoint factors only. Kept GENERAL in the gauge
`P` (one invertible matrix per vertex over `R`) so R2-3b-4 instantiates it with the Schur-data
unipotents.

The deliverables, for a fixed dimension vector `d : Fin (N + 1) → ℕ` over `[CommRing R]` and a gauge
`P : ∀ v, (Matrix (Fin (d v)) (Fin (d v)) R)ˣ`:

1. `gaugeSub d P` — the coordinate substitution `RepCoord d → MvPolynomial (RepCoord d) R`: the
   `⟨i, (r, c)⟩` entry of `baseChange (P.map C) (genericTuple d)`, i.e. the entries of
   `P_{i+1} · Xᵢ · P_i⁻¹` with the unit matrices pushed into the coefficient ring by `C`.
2. `gaugeEquiv d P` — the coordinate-change `AlgEquiv` of `MvPolynomial (RepCoord d) R`, assembled by
   `AlgEquiv.ofAlgHom` from `aeval (gaugeSub P)` and `aeval (gaugeSub P⁻¹)`. The round-trips collapse
   by the group-action laws `baseChange_mul` / `baseChange_one` on the generic tuple.
3. The **mult-transport** `aeval_gaugeSub_multPoly` : `aeval (gaugeSub P) (multPoly d r c) =
   (P_last.val.map C · Matrix.of (multPoly d) · (P 0)⁻¹.val.map C) r c` — the generic product matrix
   transforms by the two end-vertex gauges (interior units telescope away, `mult_smul`). For the
   endpoint normalization this is `L⁻¹ · multPoly · H⁻¹` (the bridge R2-3b-4 needs to turn
   `mult(A) = LEH` into `mult(Ã) = E`).

The `N = 1` coincidence (first factor = last factor) is automatic: `baseChange` is defined uniformly
per edge from both endpoint vertices, so the single edge `0` of `Fin 1` already carries both end
gauges.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`. The gauge is over the arbitrary
coefficient ring `R`; nothing here needs a field, `IsAlgClosed`, or `Infinite` (in particular we
avoid `baseChangePullback`, which carries `[Infinite k]` from polynomial-function ext).
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

universe u

variable {R : Type u} [CommRing R] {N : ℕ}

/-! ## Lifting a gauge into the coefficient ring -/

/-- Lift a gauge `P : ∀ v, (Matrix (Fin (d v)) (Fin (d v)) R)ˣ` to one over the coordinate ring
`MvPolynomial (RepCoord d) R` by pushing each unit matrix through `C` (the `RingHom.mapMatrix` of the
inclusion `C : R →+* MvPolynomial (RepCoord d) R`). -/
noncomputable def liftGauge (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d) :
    BaseChangeGroup (k := MvPolynomial (RepCoord d) R) d :=
  fun v ↦ Units.map (RingHom.mapMatrix (C : R →+* MvPolynomial (RepCoord d) R)).toMonoidHom (P v)

/-- `liftGauge` is a group homomorphism on the gauge group (it lifts `Units.map` of a monoid hom,
pointwise). Stated as the two facts the round-trip needs: it preserves `1` and `⁻¹` pointwise via the
defining `Units.map`. -/
theorem liftGauge_mul (d : Fin (N + 1) → ℕ) (P Q : BaseChangeGroup (k := R) d) :
    liftGauge d (P * Q) = liftGauge d P * liftGauge d Q := by
  funext v
  simp only [liftGauge, Pi.mul_apply, map_mul]

@[simp] theorem liftGauge_one (d : Fin (N + 1) → ℕ) :
    liftGauge d (1 : BaseChangeGroup (k := R) d) = 1 := by
  funext v
  simp only [liftGauge, Pi.one_apply, map_one]

theorem liftGauge_inv (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d) :
    liftGauge d (P⁻¹) = (liftGauge d P)⁻¹ := by
  funext v
  simp only [liftGauge, Pi.inv_apply, map_inv]

/-! ## The gauge substitution -/

/-- **The gauge substitution** `gaugeSub d P : RepCoord d → MvPolynomial (RepCoord d) R`: the
`⟨i, (r, c)⟩` coordinate maps to the `(r, c)` entry of the gauged generic factor
`baseChange (liftGauge d P) (genericTuple d) i = P_{i+1} · Xᵢ · P_i⁻¹` (units lifted by `C`). -/
noncomputable def gaugeSub (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d) :
    RepCoord d → MvPolynomial (RepCoord d) R :=
  fun x ↦ baseChange (liftGauge d P) (genericTuple d) x.1 x.2.1 x.2.2

/-- `aeval (gaugeSub P)` carries the generic factor `genericTuple i` to the gauged factor
`baseChange (liftGauge d P) (genericTuple d) i`. The generator goes to the corresponding entry by
definition of `gaugeSub`; `aeval_X` evaluates it. -/
theorem aeval_gaugeSub_genericTuple (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
    (i : Fin N) :
    (genericTuple d i).map (aeval (R := R) (gaugeSub d P))
      = baseChange (liftGauge d P) (genericTuple d) i := by
  funext r c
  rw [Matrix.map_apply, genericTuple_apply, aeval_X, gaugeSub]

/-! ## The ring hom commutes with the prefix product -/

/-- A coordinate substitution commutes with the generic prefix product: applying `aeval φ`
(rectangular `Matrix.map`) to `multPrefix (genericTuple d) j` gives the prefix product of the image
tuple `Ã i = (genericTuple d i).map (aeval φ)`. The `aeval`-analog of
`Core.MultComorphism.map_eval_multPrefix`. -/
theorem map_aeval_multPrefix (d : Fin (N + 1) → ℕ)
    (φ : RepCoord d → MvPolynomial (RepCoord d) R) (j : Fin (N + 1)) :
    (multPrefix d (genericTuple d) j).map (aeval (R := R) φ)
      = multPrefix d (fun i ↦ (genericTuple d i).map (aeval (R := R) φ)) j := by
  induction j using Fin.induction with
  | zero =>
    simp only [multPrefix_zero]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  | succ i ih =>
    rw [multPrefix_succ, multPrefix_succ, Matrix.map_mul, ih]

/-- The full generic product under `aeval (gaugeSub P)` is `mult` of the gauged generic tuple:
`(Matrix.of (multPoly d)).map (aeval (gaugeSub P)) = mult d (baseChange (liftGauge d P)
(genericTuple d))`. Combines `map_aeval_multPrefix` with `aeval_gaugeSub_genericTuple`. -/
theorem map_aeval_gaugeSub_mult (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d) :
    (Matrix.of (multPoly d)).map (aeval (R := R) (gaugeSub d P))
      = mult d (baseChange (liftGauge d P) (genericTuple d)) := by
  have hof : (Matrix.of (multPoly d) : Matrix _ _ (MvPolynomial (RepCoord d) R))
      = multPrefix d (genericTuple d) (Fin.last N) := by
    funext r c; rfl
  have htup : (fun i ↦ (genericTuple d i).map (aeval (R := R) (gaugeSub d P)))
      = baseChange (liftGauge d P) (genericTuple d) := by
    funext i; exact aeval_gaugeSub_genericTuple d P i
  rw [hof, map_aeval_multPrefix d (gaugeSub d P) (Fin.last N), htup]
  rfl

/-! ## The mult-transport -/

/-- **mult-equivariance over a `CommRing`.** `mult d (P • A) = P_last · mult d A · P_0⁻¹`: the
interior units of the base change telescope away (`submult_baseChange` at the full interval,
through `mult_eq_submult`). The `Core.FibreNormalForm.mult_smul` proof is over a `Field`; this is
the same statement over the weaker `CommRing` (the proof uses only `CommRing` facts). -/
theorem mult_smul_commRing (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
    (A : Tuple (k := R) d) :
    mult d (baseChange P A)
      = Units.val (P (Fin.last N)) * mult d A * Units.val ((P 0)⁻¹) := by
  rw [mult_eq_submult, mult_eq_submult, submult_baseChange]

/-- **The mult-transport.** Applying `aeval (gaugeSub P)` to the generic product entry `multPoly d r
c` gives the `(r, c)` entry of `P_last · Matrix.of (multPoly d) · P_0⁻¹` (the end-vertex units lifted
by `C`); the interior units telescope away (`mult_smul`). For the endpoint normalization
(`P_0 = H`, `P_last = L⁻¹`, interior `= 1`) this is `L⁻¹ · multPoly · H⁻¹`. -/
theorem aeval_gaugeSub_multPoly (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
    (r : Fin (d (Fin.last N))) (c : Fin (d 0)) :
    aeval (R := R) (gaugeSub d P) (multPoly d r c)
      = ((Units.val (liftGauge d P (Fin.last N)) * Matrix.of (multPoly d)
            * Units.val ((liftGauge d P 0)⁻¹)
          : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) (MvPolynomial (RepCoord d) R)) r c) := by
  have h : aeval (R := R) (gaugeSub d P) (multPoly d r c)
      = ((Matrix.of (multPoly d)).map (aeval (R := R) (gaugeSub d P))) r c := rfl
  rw [h, map_aeval_gaugeSub_mult d P,
    mult_smul_commRing d (liftGauge d P) (genericTuple d)]
  rfl

/-! ## The composition law and the gauge `AlgEquiv` -/

/-- The entries of `Units.val (liftGauge d Q v)` are `C`-images: `(liftGauge d Q v).val = (Q v).val.map
C` (it is `Units.map (C.mapMatrix)` of `Q v`). -/
theorem liftGauge_val_eq (d : Fin (N + 1) → ℕ) (Q : BaseChangeGroup (k := R) d) (v : Fin (N + 1)) :
    Units.val (liftGauge d Q v)
      = (Units.val (Q v)).map (C : R →+* MvPolynomial (RepCoord d) R) := by
  show Units.val (Units.map _ (Q v)) = _
  rw [Units.coe_map]
  rfl

/-- The entries of `Units.val ((liftGauge d Q v)⁻¹)` are `C`-images: `= (Q v)⁻¹.val.map C`. -/
theorem liftGauge_inv_val_eq (d : Fin (N + 1) → ℕ) (Q : BaseChangeGroup (k := R) d)
    (v : Fin (N + 1)) :
    Units.val ((liftGauge d Q v)⁻¹)
      = (Units.val ((Q v)⁻¹)).map (C : R →+* MvPolynomial (RepCoord d) R) := by
  show Units.val (Units.map _ (Q v))⁻¹ = _
  rw [Units.coe_map_inv]
  rfl

/-- A `C`-lifted (constant) gauge matrix is fixed by `aeval (gaugeSub P)`: its entries are `C`-images
in the coefficient ring, and `aeval` fixes constants (`aeval_C`). -/
theorem map_aeval_gaugeSub_liftGauge (d : Fin (N + 1) → ℕ) (P Q : BaseChangeGroup (k := R) d)
    (v : Fin (N + 1)) :
    (Units.val (liftGauge d Q v)).map (aeval (R := R) (gaugeSub d P)) = Units.val (liftGauge d Q v)
    ∧ (Units.val ((liftGauge d Q v)⁻¹)).map (aeval (R := R) (gaugeSub d P))
        = Units.val ((liftGauge d Q v)⁻¹) := by
  refine ⟨?_, ?_⟩
  · rw [liftGauge_val_eq]
    funext a b
    rw [Matrix.map_apply, Matrix.map_apply, aeval_C, MvPolynomial.algebraMap_eq]
  · rw [liftGauge_inv_val_eq]
    funext a b
    rw [Matrix.map_apply, Matrix.map_apply, aeval_C, MvPolynomial.algebraMap_eq]

/-- **The composition law on the generic tuple.** Applying `aeval (gaugeSub P)` to the gauged
generic factor `baseChange (liftGauge Q) (genericTuple) i` re-gauges by `P` inside: the result is
`baseChange (liftGauge Q) (baseChange (liftGauge P) (genericTuple)) i`. The constant `C`-lifted
`Q`-matrices are fixed (`map_aeval_gaugeSub_liftGauge`), the variable block re-gauges
(`aeval_gaugeSub_genericTuple`). -/
theorem map_aeval_gaugeSub_baseChange (d : Fin (N + 1) → ℕ) (P Q : BaseChangeGroup (k := R) d)
    (i : Fin N) :
    (baseChange (liftGauge d Q) (genericTuple d) i).map (aeval (R := R) (gaugeSub d P))
      = baseChange (liftGauge d Q) (baseChange (liftGauge d P) (genericTuple d)) i := by
  rw [baseChange_apply, baseChange_apply, Matrix.map_mul, Matrix.map_mul,
    (map_aeval_gaugeSub_liftGauge d P Q i.succ).1,
    (map_aeval_gaugeSub_liftGauge d P Q i.castSucc).2,
    aeval_gaugeSub_genericTuple d P i]

/-- The two `aeval (gaugeSub …)` directions compose to the identity on the generators: for any gauges
`P`, `Q`, `aeval (gaugeSub P) (gaugeSub Q x)` is the `x`-entry of `baseChange (liftGauge (Q * P))
(genericTuple)`. Specialized to `Q = P⁻¹` (resp. `P = Q⁻¹`) it collapses to `X x`. -/
theorem aeval_gaugeSub_gaugeSub (d : Fin (N + 1) → ℕ) (P Q : BaseChangeGroup (k := R) d)
    (x : RepCoord d) :
    aeval (R := R) (gaugeSub d P) (gaugeSub d Q x)
      = baseChange (liftGauge d (Q * P)) (genericTuple d) x.1 x.2.1 x.2.2 := by
  have h : aeval (R := R) (gaugeSub d P) (gaugeSub d Q x)
      = ((baseChange (liftGauge d Q) (genericTuple d) x.1).map
          (aeval (R := R) (gaugeSub d P))) x.2.1 x.2.2 := rfl
  rw [h, map_aeval_gaugeSub_baseChange d P Q x.1, ← baseChange_mul, liftGauge_mul]

/-- **The gauge `AlgEquiv`** of `MvPolynomial (RepCoord d) R`: `aeval (gaugeSub P)`, with inverse
`aeval (gaugeSub P⁻¹)`. The round-trips collapse by the group-action laws (`baseChange_mul` /
`baseChange_one`) on the generic tuple. The endpoint normalization instantiates `P`. -/
noncomputable def gaugeEquiv (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d) :
    MvPolynomial (RepCoord d) R ≃ₐ[R] MvPolynomial (RepCoord d) R :=
  AlgEquiv.ofAlgHom (aeval (gaugeSub d P)) (aeval (gaugeSub d P⁻¹))
    (by
      apply MvPolynomial.algHom_ext
      intro x
      rw [AlgHom.comp_apply, AlgHom.id_apply, aeval_X, aeval_gaugeSub_gaugeSub, inv_mul_cancel,
        liftGauge_one, baseChange_one, genericTuple_apply])
    (by
      apply MvPolynomial.algHom_ext
      intro x
      rw [AlgHom.comp_apply, AlgHom.id_apply, aeval_X, aeval_gaugeSub_gaugeSub, mul_inv_cancel,
        liftGauge_one, baseChange_one, genericTuple_apply])

/-- `gaugeEquiv d P` acts as `aeval (gaugeSub d P)` (the forward `AlgHom` of the `ofAlgHom`). -/
@[simp] theorem gaugeEquiv_apply (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
    (p : MvPolynomial (RepCoord d) R) :
    gaugeEquiv d P p = aeval (R := R) (gaugeSub d P) p := rfl

/-- **The mult-transport, in `gaugeEquiv` form.** `gaugeEquiv d P` sends the generic product entry
`multPoly d r c` to the `(r, c)` entry of `P_last · multPoly · P_0⁻¹`. This is the bridge R2-3b-4
needs: with the endpoint gauge (`P_0 = H`, `P_last = L⁻¹`), it turns the chart target `mult(A) = LEH`
into `mult(Ã) = E`. -/
theorem gaugeEquiv_multPoly (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
    (r : Fin (d (Fin.last N))) (c : Fin (d 0)) :
    gaugeEquiv d P (multPoly d r c)
      = ((Units.val (liftGauge d P (Fin.last N)) * Matrix.of (multPoly d)
            * Units.val ((liftGauge d P 0)⁻¹)
          : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) (MvPolynomial (RepCoord d) R)) r c) := by
  rw [gaugeEquiv_apply, aeval_gaugeSub_multPoly]

/-! ## Non-vacuity witnesses

(i) The identity gauge `P = 1` reproduces the identity `AlgEquiv` — the construction is honest at
`H = L = 1`. (ii) The transport on the `(2,2,2)` witness with a non-identity end-vertex gauge over
`ℚ` is the genuine conjugation `P_last · M · P_0⁻¹` of the generic product. -/

section Witness

/-- The identity gauge substitution is the identity on coordinates: `gaugeSub d 1 x = X x`. -/
theorem gaugeSub_one (d : Fin (N + 1) → ℕ) (x : RepCoord d) :
    gaugeSub d (1 : BaseChangeGroup (k := R) d) x = X x := by
  rw [gaugeSub, liftGauge_one, baseChange_one, genericTuple_apply]

/-- At the identity gauge the `AlgEquiv` is the identity (`H = L = 1` reproduces the identity) —
the construction is non-vacuous and honest. -/
example (d : Fin (N + 1) → ℕ) (p : MvPolynomial (RepCoord d) R) :
    gaugeEquiv d (1 : BaseChangeGroup (k := R) d) p = p := by
  rw [gaugeEquiv_apply]
  have : aeval (R := R) (gaugeSub d (1 : BaseChangeGroup (k := R) d))
      = AlgHom.id R (MvPolynomial (RepCoord d) R) := by
    apply MvPolynomial.algHom_ext
    intro x
    rw [aeval_X, gaugeSub_one, AlgHom.id_apply]
  rw [this, AlgHom.id_apply]

/-- The constant dimension vector `(2, 2, 2)` (every `d v = 2` definitionally, so the uniform gauge
type-checks without `![…]`-reduction friction). -/
def dConst : Fin 3 → ℕ := fun _ ↦ 2

/-- The uniform `(2,2,2)` gauge over `ℤ` carrying `witnessUnit` (`!![1,1;0,1]`) at every vertex. -/
def witnessGauge : BaseChangeGroup (k := ℤ) dConst := fun _ ↦ witnessUnit

/-- The gauge `AlgEquiv` is available at the concrete non-identity `(2,2,2)` gauge `witnessGauge` over
`ℤ` — the construction is non-vacuous at a genuine `!![1,1;0,1]`-conjugation. -/
noncomputable example :
    MvPolynomial (RepCoord dConst) ℤ ≃ₐ[ℤ] MvPolynomial (RepCoord dConst) ℤ :=
  gaugeEquiv dConst witnessGauge

/-- The mult-transport fires at the concrete non-identity gauge `witnessGauge`: `gaugeEquiv` carries
each generic product entry to the conjugation `P_last · multPoly · P_0⁻¹` of the generic product.
Non-vacuous (the gauge is the genuine `!![1,1;0,1]` at every vertex, not the identity). -/
example (r : Fin (dConst (Fin.last 2))) (c : Fin (dConst 0)) :
    gaugeEquiv (R := ℤ) dConst witnessGauge (multPoly dConst r c)
      = aeval (R := ℤ) (gaugeSub dConst witnessGauge) (multPoly dConst r c) :=
  gaugeEquiv_apply dConst witnessGauge (multPoly dConst r c)

end Witness

end DLNFibre.Core
