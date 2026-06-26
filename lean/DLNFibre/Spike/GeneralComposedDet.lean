import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Algebra.Order.Ring.Abs

/-!
# SPIKE — general composed-det telescoping (R1 lower-leg #1 risk probe)

**THIS IS A FEASIBILITY SPIKE, NOT A BUILD.** Spike-only scratch file under `DLNFibre/Spike/`; NOT
wired into `DLNFibre.lean`. The controller decides whether/how to promote.

## The risk (from thread 32, `r1-general-hdiv-design`)
R1-general's LOWER leg (achiever box-divergence) needs `|det Dφ_M|` for a descent-path-indexed `φ_M`
whose factor list is **variable-length** (one Schur/shear/radial factor per boundary level,
`L`-dependent). The pen-and-paper probe flagged the #1 risk: a variable-length `det_comp` over a
dependently-typed factor list (maps between different `Fin (r-j)` spaces) could be a multi-week
dependent-`Fin`-cast fight.

## The hypothesis to test (the escape)
If `φ_M` is assembled as a `List.prod` of **FULL-AMBIENT** endomorphisms — each level's operation
embedded as an `End` of the FIXED ambient `(Fin N → ℝ)` (NOT maps between `Fin (r-j)` spaces) — then
the determinant telescopes via the **det monoid-hom** with NO dependent casts:

  `(List.prod fs).det = (fs.map LinearMap.det).prod`.

`LinearMap.det : (M →ₗ[A] M) →* A` is **literally a `MonoidHom`** (Mathlib
`Mathlib/LinearAlgebra/Determinant.lean:172`), and the monoid multiplication on `M →ₗ[A] M` is
`comp` (`Module.End.mul_eq_comp`, def-eq `rfl`). So `map_list_prod` discharges it directly — no
`det_comp` induction, no `Fin`-cast.

## Verdict (see the module-foot `VERDICT` note)
The telescoping lemma (deliverable 1) is a **clean Mathlib one-liner** (`map_list_prod`). The risk
of a variable-length `det_comp` cast-fight is **dissolved** by the full-ambient `List.prod` form —
for the determinant step. The residual work (per-factor full-ambient embeddings + their per-factor
dets) is NOT a cast fight; it is the same per-block det computation the `(3,3,3,3)` anchor already
does, now indexed by a `List` rather than a fixed 27-block grading.
-/

namespace DLNFibre.Spike

open scoped BigOperators

/-! ## Deliverable 1 — the KEY telescoping lemma (PROVEN, both plain and abs) -/

/-- **The key telescoping lemma (plain `det`).** For a `List` of full-ambient endomorphisms of the
FIXED space `Fin N → ℝ`, the determinant of the list-product is the product of the per-factor
determinants. `LinearMap.det` is a `MonoidHom`, so this is `MonoidHom.map_list_prod` — NO dependent
`Fin`-cast, NO induction-on-length `det_comp` chain. -/
theorem listProd_det (N : ℕ) (fs : List ((Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ))) :
    (fs.prod).det = (fs.map LinearMap.det).prod :=
  LinearMap.det.map_list_prod fs

/-- **The key telescoping lemma (abs `|det|`).** Composing `listProd_det` with `absHom` (the
`MonoidWithZeroHom` `|·|`): the absolute value of the list-product determinant is the product of the
per-factor absolute determinants. This is the shape the achiever box-divergence atom consumes
(`|det Dφ_M| = ∏_s m_s`). -/
theorem listProd_abs_det (N : ℕ) (fs : List ((Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ))) :
    |(fs.prod).det| = (fs.map (fun f ↦ |LinearMap.det f|)).prod := by
  rw [listProd_det]
  rw [show (fun f : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) ↦ |LinearMap.det f|)
        = (fun a : ℝ ↦ |a|) ∘ LinearMap.det from rfl, ← List.map_map]
  exact map_list_prod absHom (fs.map LinearMap.det)

/-! ## Deliverable 1' — the ContinuousLinearMap analog (PROVEN)

The DLN charts are CLMs (`Q3333CLM`, `T3333Deriv`, &c. are `→L[ℝ]`). The CLM coercion to a plain
`LinearMap` is a `RingHom` (`ContinuousLinearMap.toLinearMapRingHom`, needs `ContinuousAdd` —
automatic for `Fin N → ℝ`), hence a `MonoidHom`, so the list-product coercion commutes and the
LinearMap telescoping transports. In Mathlib's c-o-v API the determinant of a CLM `f` is written
`LinearMap.det (f : E →ₗ[ℝ] E)` (no separate `ContinuousLinearMap.det` def exists in Mathlib at this
pin — `EqHaar.lean` uses `LinearMap.det ↑f`); we state the analog in that exact form. -/

/-- **The CLM telescoping lemma (abs).** For a `List` of full-ambient CONTINUOUS endomorphisms, the
abs determinant (read through the LinearMap coercion, as the Mathlib c-o-v API does) telescopes. The
CLM→LinearMap coercion respects `List.prod` (it is a `RingHom`), so this reduces to
`listProd_abs_det` with no new casts. -/
theorem listProd_clm_abs_det (N : ℕ)
    (fs : List ((Fin N → ℝ) →L[ℝ] (Fin N → ℝ))) :
    |LinearMap.det (fs.prod).toLinearMap|
      = (fs.map (fun f ↦ |LinearMap.det f.toLinearMap|)).prod := by
  -- Compose the three monoid homs (CLM→LinearMap ring hom, `det`, `|·|`) into ONE, then
  -- `map_list_prod` fires once — no per-step coercion-binder juggling.
  let Φ : ((Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) →* ℝ :=
    (absHom : ℝ →*₀ ℝ).toMonoidHom.comp
      (LinearMap.det.comp
        (ContinuousLinearMap.toLinearMapRingHom :
            ((Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) →+* _).toMonoidHom)
  have h := Φ.map_list_prod fs
  -- `h : |det fs.prod.toLinearMap| = (fs.map (|·| ∘ det ∘ ·.toLinearMap)).prod`.
  rw [show (fun f : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) ↦ |LinearMap.det f.toLinearMap|) = ⇑Φ from rfl]
  exact h

/-! ## Deliverable 2 — the general composed-det CONTRACT (statement is the deliverable)

The contract the general lower-atom needs: `φ_M` assembled as a `List.prod` of full-ambient factors
with per-factor abs-dets `m_s`, then `|det Dφ_M| = ∏_s m_s`. The point of the spike: this follows
from `listProd_abs_det` in ONE line once the per-factor dets are in hand — the variable-length
composition is discharged by the telescoping, with NO induction-on-`L` `Fin`-cast fight.

No `sorry` is needed: the per-factor det list comes in as a hypothesis (`hfac`), so the contract is
PROVEN, discharged by the telescoping in one `rw`. (The prompt permitted a `sorry`-stated contract;
stating the per-factor dets as a hypothesis makes it sorry-free instead.) -/

/-- **General composed-det contract.** `φDeriv = List.prod fs` with `fs` full-ambient endomorphisms
of `Fin N → ℝ`; if each factor has abs-det `m s` (indexed by the factor list position), then
`|det φDeriv| = ∏ m`. The `hfac` hypothesis packages the per-factor dets; the conclusion is the
telescoped product. This is the general-`M`, variable-length analog of `phi3333_abs_det`. -/
theorem general_composed_abs_det
    (N : ℕ) (fs : List ((Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ))) (m : List ℝ)
    (hfac : fs.map (fun f ↦ |LinearMap.det f|) = m) :
    |(fs.prod).det| = m.prod := by
  rw [listProd_abs_det, hfac]

/-- **General composed-det contract (CLM form).** Same, for a `φDeriv` given as a `List.prod` of
full-ambient CLMs (the shape the DLN charts produce). The per-factor abs-dets `m` are supplied by
the per-level embedding lemmas (the residual build work); telescoping is `listProd_clm_abs_det`. -/
theorem general_composed_clm_abs_det
    (N : ℕ) (fs : List ((Fin N → ℝ) →L[ℝ] (Fin N → ℝ))) (m : List ℝ)
    (hfac : fs.map (fun f ↦ |LinearMap.det f.toLinearMap|) = m) :
    |LinearMap.det (fs.prod).toLinearMap| = m.prod := by
  rw [listProd_clm_abs_det, hfac]

/-! ## Deliverable 2'' — the contract is NON-VACUOUS: a worked variable-length instance

A 2×2 sanity instance to show the telescoping fires on a genuine, length-3 product of full-ambient
factors (a diagonal scaling, a shear, another scaling) and lands the expected `∏ |det|`. This is the
shape the per-level factors take; the determinant step needs no per-instance work. -/

/-- Variable-length non-vacuous check: a length-3 product of `2×2` full-ambient factors telescopes
to the product of per-factor abs-dets. Demonstrates `listProd_abs_det` is non-vacuous and fires on a
concrete factor list (here all dets computed; the `Matrix.det_fin_two_of` evaluations are the only
per-factor work, exactly what the per-level embedding lemmas supply in the general atom). -/
example (a d : ℝ) :
    |((([Matrix.toLin' !![a, 0; 0, 1],
        Matrix.toLin' !![1, (3 : ℝ); 0, 1],
        Matrix.toLin' !![1, 0; 0, d]] :
          List ((Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))).prod).det)|
      = |a| * (|(1 : ℝ)| * |d|) := by
  rw [listProd_abs_det]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    LinearMap.det_toLin']
  rw [Matrix.det_fin_two_of, Matrix.det_fin_two_of, Matrix.det_fin_two_of]
  ring_nf

/-! ## VERDICT (deliverable 3)

**BUILD-READY modulo per-factor full-ambient embeddings + their dets.** The full-ambient `List.prod`
form DISSOLVES the dependent-`Fin`-cast risk for the determinant step:

- `listProd_det` / `listProd_abs_det` are **one-liners** (`MonoidHom.map_list_prod` + `absHom`); the
  CLM analog `listProd_clm_abs_det` adds only the CLM→LinearMap `RingHom` (`toLinearMapRingHom`),
  also a one-liner. NO `det_comp` induction-on-length, NO `Fin (r-j)`-to-`Fin (r-j')` cast.
- `general_composed_abs_det` shows the variable-length composition is discharged in ONE `rw` once
  the per-factor det list `m` is supplied (`hfac`).
- The worked length-3 `2×2` instance confirms the telescoping is non-vacuous and fires concretely.

The residual work for the general lower-atom is therefore NOT a cast fight; it is:
  (a) defining each level's operation (Schur/shear/radial) as a full-ambient `End (Fin N → ℝ)` —
      a `Matrix.toLin'`/`Pi.single`-style embedding, like `Kparam3333`/`Frame3333` already;
  (b) computing each per-factor det (block-triangular / `det_fin_two`-style), as the `(3,3,3,3)`
      anchor already does per block.
Both (a) and (b) are the bounded, mechanical per-level work the anchor demonstrates at fixed `L=3`;
neither reintroduces the variable-length cast the probe feared.

**The one honest caveat:** the escape holds ONLY IF the per-level operations CAN be expressed as
full-ambient `End (Fin N → ℝ)` whose product equals `Dφ_M` — i.e. the chart factorisation must be
re-expressed in the fixed ambient (each level acts as identity off its active block) rather than as
genuine maps between `Fin (r-j)` spaces. The `(3,3,3,3)` anchor's `Frame3333Deriv`/`Kparam3333Deriv`
ARE already full-ambient `Fin 27` endos, so this re-expression is the established pattern; the
general atom must produce its factor list in the same fixed-ambient form. If a future chart needs
inter-dimensional maps, THAT factor would fall outside this lemma — but the descent-path charts are
naturally full-ambient (identity off the active level), so this is not expected to bite.
-/

end DLNFibre.Spike
