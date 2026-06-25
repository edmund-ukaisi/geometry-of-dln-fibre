import DLNFibre.Core.Setup
import DLNFibre.Core.OrbitCodim

/-!
# `DLNFibre.Core.GenericTuple` — the generic tuple over the coordinate ring

The shared substrate for polynomialising the entries of `mult`/`submult`: the **generic tuple**
`genericTuple d`, whose `(i, r, c)` entry is the coordinate variable `X ⟨i, r, c⟩` of
`MvPolynomial (RepCoord d) k`, and the bridge `eval_genericTuple` saying that evaluating at the
point `canonicalCoord d A` recovers the factor `A i`. Both hold over any `CommRing k` (the field is
not needed to flatten coordinates), so they live here at the weakest hypothesis and are reused by
`Core.RankLocusClosed` (minor polynomials of `submult`) and `Core.MultComorphism` (the coordinate-ring
map of `mult`).

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

universe u

variable {k : Type u} [CommRing k] {N : ℕ}

/-- The **generic tuple** over the coordinate ring `MvPolynomial (RepCoord d) k`: the `(i, r, c)`
entry is the coordinate variable `X ⟨i, r, c⟩`. Evaluating at `canonicalCoord d A` recovers `A`. -/
noncomputable def genericTuple (d : Fin (N + 1) → ℕ) :
    Tuple (k := MvPolynomial (RepCoord d) k) d :=
  fun i r c ↦ X ⟨i, r, c⟩

@[simp] theorem genericTuple_apply (d : Fin (N + 1) → ℕ) (i : Fin N)
    (r : Fin (d i.succ)) (c : Fin (d i.castSucc)) :
    (genericTuple (k := k) d i) r c = X ⟨i, r, c⟩ := rfl

/-- Evaluating the generic tuple at `canonicalCoord d A` recovers the factor `A i`. -/
theorem eval_genericTuple {d : Fin (N + 1) → ℕ} (A : Tuple (k := k) d) (i : Fin N) :
    (genericTuple (k := k) d i).map (MvPolynomial.eval (canonicalCoord d A)) = A i := by
  funext r c
  simp only [Matrix.map_apply, genericTuple, MvPolynomial.eval_X, canonicalCoord_apply]

end DLNFibre.Core
