import DLNFibre.Core.DeterminantalBasePresentation
import DLNFibre.Core.FibreReducedTrivialization

/-!
# `DLNFibre.Core.DeepChartRing` — the deep chart ring `Sred` + the localized base→total map
# (R2-3b-1+2)

The first rungs of the **deep** product trivialization `e` that R2-3a
(`Core.FibreReducedTrivialization`) carries as a hypothesis. The engine's localized determinantal
presentation (`Core.DeterminantalBasePresentation`) is `N = 1` only: `basePresentationEquiv` lives
over `dStratum q p = ![q, p]`, a single matrix. This module builds, for a **general** dimension
vector `d : Fin (N + 1) → ℕ`, the deep localized chart ring `Sred` of the rank-`≤ r` product locus
on the pivot chart, and the localized base→total `k`-algebra map that gives `Sred` its
`SchurLoc`-algebra structure (the `R = SchurLoc`-algebra structure that R2-3a's `e` needs).

The deliverables, with `q = d 0` (source dimension) and `p = d (Fin.last N)` (target dimension):

**R2-3b-1 — the deep chart ring (definitions + instances + bridges).**
1. `ΔPdeep d r hp hq` — the deep pivot minor: the determinant of the top-left `r×r` submatrix of the
   **deep** generic product `Matrix.of (multPoly d)` (the deep analog of `N = 1`'s `detPivotPoly`).
2. `IadDeep d r hp hq` — the localized base ideal `(sigmaIdeal d r).map (algebraMap …)` pushed into
   `Localization.Away (ΔPdeep …)` (the deep analog of `Iad`).
3. `Sred d r hp hq := Localization.Away (ΔPdeep …) ⧸ IadDeep …` — the deep chart quotient ring, with
   its `CommRing` / `Algebra k` instances inherited, and `isReduced_Sred` : `IsReduced (Sred …)`
   (over any field — `sigmaIdeal` is a vanishing ideal, radical by the field-general
   `vanishingIdeal_isRadical`, justifying the name — this is R2-3a's `hSred`, now discharged).
4. The **type bridge** `repStratumEquiv : RepCoord (dStratum q p) ≃ Fin p × Fin q` (the
   single-matrix stratum coords), via `Equiv.uniqueSigma` (the `Sigma` over the `Unique` base
   `Fin 1`), and the deep base comorphism `deepBaseComap d` carrying the `N = 1` base coordinate
   ring into the deep total coordinate ring (`multComap d` after the rename).

**R2-3b-2 — the localized base→total map + the `SchurLoc`-algebra structure.**
5. `deepBaseComap_detPivot` — the load-bearing transport: `deepBaseComap d` carries the `N = 1`
   pivot minor `detPivotPoly` to the deep `ΔPdeep` (det commutes with `aeval`, `AlgHom.map_det`),
   making the localized map well-typed.
6. `deepBaseComap_sigmaIdeal_le` — the (non-circular) ideal direction: `deepBaseComap d` maps the
   base `sigmaIdeal (dStratum q p) r` into the deep `sigmaIdeal d r`. Mechanism: a **deep** total
   point
   `A ∈ Σ̄^r_d` maps by `mult` to a single-matrix **base** point in `Σ̄^r_{(q,p)}` (chase via
   `aeval_deepBaseComap` + `singleTuple`). It does **not** assume the circular `sigmaIdeal ≤
   fibreGenIdeal`.
7. `baseLocMap` / `schurToSred` — the localized base map `Localization.Away detPivotPoly →ₐ[k]
   Localization.Away (ΔPdeep …)` (`IsLocalization.Away.mapₐ`), lifted to the quotients
   (`Ideal.quotientMapₐ`), then composed with `basePresentationEquiv.symm` to give a `k`-algebra map
   `SchurLoc q p r →ₐ[k] Sred d r hp hq`. The resulting `SchurLoc`-algebra structure on `Sred`
   (`RingHom.toAlgebra`) + the `IsScalarTower k (SchurLoc …) (Sred …)` instance.

**Scope (what is NOT here).** The full product iso `e : Sred ≃ₐ[k] SchurLoc ⊗_k FibreAlg`, the
endpoint-normalization `AlgEquiv`, and the descent of the iso to the reduced chart quotient are
**not built in this module** (they were the later R2-3b rungs of this route-(b) chain). No result
here claims `codim (fibre) = C + δ`. (R2-3a's *other* hypothesis, `IsReduced S`, **is** discharged
here: `isReduced_Sred`.) The endpoint-normalization `aeval`-substitution contract is pre-staged
below as an `example` block (an arbitrary coefficient ring `R`, via `AlgEquiv.ofAlgHom`, **not**
`baseChangeAlgEquiv` which carries `[Infinite k]`).

**Off the critical path (route-β superseded this).** The unconditional `codim (fibre d B) = C + δ`
(`Core.FibreCodimFinal`) was reached by **route-β**, whose localized chart `AlgEquiv` `e` is BUILT
in `Core.ChartLocalizedAlgEquiv` — not via the deep product iso this route-(b) chain was building.
So the rungs here are a self-contained component of that superseded route, no longer gating the
codimension result.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## R2-3b-1 — the type bridge and the deep base comorphism

For the single-arrow stratum `dStratum q p = ![q, p]`, the coordinate index
`RepCoord (dStratum q p)` is a `Sigma` over `Fin 1`; collapsing it gives `Fin p × Fin q` (the
single-matrix entry coords). The deep base comorphism is the `N = 1` base coordinate map
`multComap d` precomposed with this rename. -/

/-- **The single-matrix stratum-coordinate bridge** `RepCoord (dStratum q p) ≃ Fin p × Fin q`. The
coordinate index of `dStratum q p = ![q, p]` is `Σ i : Fin 1, Fin (dStratum q p i.succ) ×
Fin (dStratum q p i.castSucc)`; over the `Unique` base `Fin 1` this is the single fibre
`Fin p × Fin q` (`default = 0`, `dStratum q p (0).succ = p`, `dStratum q p (0).castSucc = q`). -/
def repStratumEquiv (q p : ℕ) : RepCoord (dStratum q p) ≃ Fin p × Fin q :=
  Equiv.uniqueSigma (fun i : Fin 1 ↦ Fin (dStratum q p i.succ) × Fin (dStratum q p i.castSucc))

@[simp] theorem repStratumEquiv_mk (q p : ℕ) (x : Fin p × Fin q) :
    repStratumEquiv q p ⟨0, x⟩ = x := rfl

/-- **The deep base comorphism** `MvPolynomial (RepCoord (dStratum q p)) k →ₐ[k]
MvPolynomial (RepCoord d) k` (`q = d 0`, `p = d (last N)`): the `mult` comorphism `multComap d`
precomposed with the single-matrix coordinate rename. Carries the `N = 1` base coordinate ring into
the deep total coordinate ring. -/
noncomputable def deepBaseComap (d : Fin (N + 1) → ℕ) :
    MvPolynomial (RepCoord (dStratum (d 0) (d (Fin.last N)))) k →ₐ[k]
      MvPolynomial (RepCoord d) k :=
  (multComap d).comp (renameEquiv k (repStratumEquiv (d 0) (d (Fin.last N)))).toAlgHom

/-- `deepBaseComap d` sends the single-matrix coordinate variable `X ⟨0, (a, b)⟩` to the deep
generic product entry `multPoly d a b`. -/
@[simp] theorem deepBaseComap_X (d : Fin (N + 1) → ℕ)
    (a : Fin (d (Fin.last N))) (b : Fin (d 0)) :
    deepBaseComap (k := k) d (X ⟨0, (a, b)⟩) = multPoly d a b := by
  rw [deepBaseComap]
  simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, renameEquiv_apply,
    rename_X, repStratumEquiv_mk, multComap_X]

/-! ## R2-3b-1 — the deep chart ring `Sred` -/

/-- **The deep pivot minor** `ΔPdeep d r`: the determinant of the top-left `r×r` submatrix of the
deep generic product `Matrix.of (multPoly d)`. The deep analog of `N = 1`'s `detPivotPoly`;
inverting it is the pivot chart. -/
noncomputable def ΔPdeep (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) : MvPolynomial (RepCoord d) k :=
  ((Matrix.of (multPoly d)).submatrix
    (fun i : Fin r ↦ (Fin.castLE hp i : Fin (d (Fin.last N))))
    (fun j : Fin r ↦ (Fin.castLE hq j : Fin (d 0)))).det

/-- **The deep localized base ideal** `IadDeep d r`: the determinantal base ideal `sigmaIdeal d r`
pushed into the localized total ring `Localization.Away (ΔPdeep …)`. The deep analog of `Iad`. -/
noncomputable def IadDeep (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    Ideal (Localization.Away (ΔPdeep (k := k) d r hp hq)) :=
  (sigmaIdeal d r).map (algebraMap (MvPolynomial (RepCoord d) k)
    (Localization.Away (ΔPdeep (k := k) d r hp hq)))

/-- **The deep chart ring** `Sred d r := Localization.Away (ΔPdeep …) ⧸ IadDeep …`: the localized
chart quotient of the rank-`≤ r` product locus for general `d`, on the pivot chart. The `CommRing` /
`Algebra k` instances are inherited from the localization-quotient. -/
noncomputable abbrev Sred (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) : Type u :=
  Localization.Away (ΔPdeep (k := k) d r hp hq) ⧸ IadDeep (k := k) d r hp hq

/-! ## R2-3b-1 — `Sred` is reduced (justifying the name; discharges R2-3a's `hSred`)

The name `Sred` asserts reducedness, and that reducedness is precisely R2-3a's second hypothesis
`hSred : IsReduced S` (`Core.FibreReducedTrivialization.fibreGenIdeal_isRadical_of_trivialization`).
It is **cheap** here: `IadDeep = (sigmaIdeal d r).map (algebraMap …)` is radical because
`sigmaIdeal` is radical (`vanishingIdeal_isRadical`, a field-general no-nilpotents fact — every
vanishing ideal is radical over any field, not the strong Nullstellensatz) and localization
carries radical
ideals to radical ideals (`IsLocalization.map_radical`); a quotient by a radical ideal is reduced
(`Ideal.isRadical_iff_quotient_reduced`). No quotient↔localization interchange iso is needed. -/

/-- **`IadDeep` is radical** (over any field — `vanishingIdeal_isRadical` is a field-general
no-nilpotents fact, not the strong Nullstellensatz, so no `[IsAlgClosed k]`): the localized image of
the radical determinantal base ideal `sigmaIdeal d r`. Via `IsLocalization.map_radical`
(`(I.map …).radical = I.radical.map …`) and `sigmaIdeal`'s radicality
(`vanishingIdeal_isRadical`). -/
theorem IadDeep_isRadical (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    (IadDeep (k := k) d r hp hq).IsRadical := by
  have hsig : (sigmaIdeal (k := k) d r).IsRadical := by
    rw [sigmaIdeal]; exact vanishingIdeal_isRadical _
  rw [← Ideal.radical_eq_iff, IadDeep,
    ← IsLocalization.map_radical (M := Submonoid.powers (ΔPdeep (k := k) d r hp hq)),
    hsig.radical]

/-- **`Sred` is reduced** (over any field — see `IadDeep_isRadical`), justifying the name.
`Sred = Localization.Away ΔPdeep ⧸ IadDeep` with `IadDeep` radical (`IadDeep_isRadical`); a quotient
by a radical ideal is reduced
(`Ideal.isRadical_iff_quotient_reduced`). This is exactly R2-3a's `hSred : IsReduced S` for
`S = Sred` — so R2-3b-4 needs to build only `e` itself, not also `IsReduced S`. -/
theorem isReduced_Sred (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    IsReduced (Sred (k := k) d r hp hq) :=
  (Ideal.isRadical_iff_quotient_reduced _).mp (IadDeep_isRadical d r hp hq)

/-! ## R2-3b-2 — the load-bearing transports

`deepBaseComap` carries the `N = 1` pivot minor `detPivotPoly` to the deep `ΔPdeep` (making the
localized map well-typed), and the base `sigmaIdeal` into the deep `sigmaIdeal` (making the quotient
lift well-typed). -/

/-- **The pivot-minor transport** (load-bearing): `deepBaseComap d` carries the `N = 1` pivot minor
`detPivotPoly (d 0) (d last) r` to the deep pivot minor `ΔPdeep d r`. The determinant commutes with
the algebra map (`AlgHom.map_det`); each pivot entry `X ⟨0, (castLE i, castLE j)⟩` goes to
`multPoly d (castLE i) (castLE j)` (`deepBaseComap_X`), the corresponding entry of `Matrix.of
(multPoly d)`. (Exact analog of the landed `renameEquiv_detPivot`.) -/
theorem deepBaseComap_detPivot (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    deepBaseComap (k := k) d
        (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq)
      = ΔPdeep (k := k) d r hp hq := by
  rw [detPivotPoly, ΔPdeep, AlgHom.map_det]
  congr 1
  funext i j
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply,
    show (Matrix.of (multPoly (k := k) (dStratum (d 0) (d (Fin.last N)))))
        (Fin.castLE hp i) (Fin.castLE hq j)
        = X ⟨0, (Fin.castLE hp i, Fin.castLE hq j)⟩ from multPoly_stratum_apply _ _ _ _,
    deepBaseComap_X]
  rfl

/-! ### The single-matrix tuple and the comorphism chase -/

/-- The **single-matrix tuple** over `dStratum q p` from a matrix `M : Mat (p × q)`: the `N = 1`
`Tuple` whose lone factor is `M`. -/
def singleTuple (k : Type u) [Field k] (q p : ℕ) (M : Matrix (Fin p) (Fin q) k) :
    Tuple (k := k) (dStratum q p) :=
  fun i ↦ match i with | 0 => M

/-- `mult` of the single-matrix tuple is its matrix (the `N = 1` product is the lone factor). -/
theorem mult_singleTuple (q p : ℕ) (M : Matrix (Fin p) (Fin q) k) :
    mult (dStratum q p) (singleTuple k q p M) = M := by
  rw [mult_stratum_eq q p (singleTuple k q p M)]; rfl

/-- **The comorphism chase.** Evaluating `deepBaseComap d f` at the coordinates of a deep tuple `A`
equals evaluating `f` at the coordinates of the single-matrix base tuple of `mult d A`. Both are
`k`-algebra maps in `f`; on the generator `X ⟨0, (a, b)⟩` both give `(mult d A) a b`
(`eval_multPoly`). -/
theorem aeval_deepBaseComap (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d)
    (f : MvPolynomial (RepCoord (dStratum (d 0) (d (Fin.last N)))) k) :
    aeval (canonicalCoord d A) (deepBaseComap d f)
      = aeval (R := k) (canonicalCoord (dStratum (d 0) (d (Fin.last N)))
          (singleTuple k (d 0) (d (Fin.last N)) (mult (k := k) d A))) f := by
  have hgen : (aeval (canonicalCoord d A)).comp (deepBaseComap d)
      = aeval (R := k) (canonicalCoord (dStratum (d 0) (d (Fin.last N)))
          (singleTuple k (d 0) (d (Fin.last N)) (mult (k := k) d A))) := by
    apply MvPolynomial.algHom_ext
    intro x
    obtain ⟨i, a, b⟩ := x
    obtain rfl : i = 0 := Subsingleton.elim i 0
    simp only [AlgHom.comp_apply, deepBaseComap_X]
    rw [show aeval (R := k) (canonicalCoord d A) (multPoly d a b)
          = eval (canonicalCoord d A) (multPoly d a b) from by rw [aeval_def, eval]; rfl,
      eval_multPoly, aeval_X, canonicalCoord_apply]
    rfl
  exact DFunLike.congr_fun hgen f

/-- **The base→deep `sigmaIdeal` direction** (non-circular): `deepBaseComap d` maps the base
`sigmaIdeal (dStratum q p) r` into the deep `sigmaIdeal d r`. Via `Ideal.map_le_iff_le_comap`: a
base generator `f` vanishing on `Σ̄^r_{(q,p)}` pulls back to a polynomial vanishing on `Σ̄^r_d`,
because a **deep** total point `A ∈ Σ̄^r_d` maps by `mult` to a single-matrix **base** point in
`Σ̄^r_{(q,p)}` (`mult_singleTuple`, `rank (mult d A) ≤ r`), where `f` vanishes
(`aeval_deepBaseComap`).
Does **not** assume the circular `sigmaIdeal ≤ fibreGenIdeal`. -/
theorem deepBaseComap_sigmaIdeal_le (d : Fin (N + 1) → ℕ) (r : ℕ) :
    (sigmaIdeal (k := k) (dStratum (d 0) (d (Fin.last N))) r).map
        (deepBaseComap (k := k) d).toRingHom
      ≤ sigmaIdeal (k := k) d r := by
  rw [Ideal.map_le_iff_le_comap]
  intro f hf
  rw [Ideal.mem_comap, sigmaIdeal, mem_vanishingIdeal_iff]
  intro x hx
  obtain ⟨A, hA, rfl⟩ := hx
  rw [mem_productRankLocusLE] at hA
  change aeval (R := k) (canonicalCoord d A) ((deepBaseComap d).toRingHom f) = 0
  rw [show (deepBaseComap d).toRingHom f = deepBaseComap d f from rfl, aeval_deepBaseComap]
  rw [sigmaIdeal, mem_vanishingIdeal_iff] at hf
  exact hf _ ⟨singleTuple k (d 0) (d (Fin.last N)) (mult d A), by
    rw [mem_productRankLocusLE, mult_singleTuple]; exact hA, rfl⟩

/-! ## R2-3b-2 — the localized base map and the `SchurLoc`-algebra structure on `Sred`

The localized base map `Localization.Away detPivotPoly →ₐ[k] Localization.Away (ΔPdeep …)`
(`IsLocalization.Away.mapₐ deepBaseComap detPivotPoly`, well-typed by the transport
`deepBaseComap_detPivot`), lifted to the quotients (`Ideal.quotientMapₐ`, the ideal hypothesis
discharged by `deepBaseComap_sigmaIdeal_le`), then composed with `basePresentationEquiv.symm`. -/

/-- **The localized base map** `Localization.Away (detPivotPoly …) →ₐ[k]
Localization.Away (ΔPdeep …)`, `IsLocalization.Away.mapₐ` of the deep base comorphism
`deepBaseComap d` at `detPivotPoly`. The
codomain localization instance at `deepBaseComap d (detPivotPoly …)` is `ΔPdeep`'s (the transport
`deepBaseComap_detPivot`). -/
noncomputable def baseLocMap (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    Localization.Away (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq) →ₐ[k]
      Localization.Away (ΔPdeep (k := k) d r hp hq) := by
  haveI : IsLocalization.Away
      (deepBaseComap (k := k) d (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq))
      (Localization.Away (ΔPdeep (k := k) d r hp hq)) := by
    rw [deepBaseComap_detPivot]; infer_instance
  exact IsLocalization.Away.mapₐ _ _ (deepBaseComap d)
    (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq)

/-- `baseLocMap` sends `algebraMap … x` to `algebraMap … (deepBaseComap d x)` — it intertwines the
two localization maps (`IsLocalization.Away.mapₐ` / `IsLocalization.map` on the base ring). -/
theorem baseLocMap_algebraMap (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0)
    (x : MvPolynomial (RepCoord (dStratum (d 0) (d (Fin.last N)))) k) :
    baseLocMap (k := k) d r hp hq
        (algebraMap (MvPolynomial (RepCoord (dStratum (d 0) (d (Fin.last N)))) k)
          (Localization.Away (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq)) x)
      = algebraMap (MvPolynomial (RepCoord d) k) (Localization.Away (ΔPdeep (k := k) d r hp hq))
          (deepBaseComap d x) := by
  haveI : IsLocalization.Away
      (deepBaseComap (k := k) d (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq))
      (Localization.Away (ΔPdeep (k := k) d r hp hq)) := by
    rw [deepBaseComap_detPivot]; infer_instance
  rw [baseLocMap, IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map,
    IsLocalization.map_eq]
  rfl

/-- The base ideal `Iad` is carried into `IadDeep` by `baseLocMap`
(`Iad ≤ IadDeep.comap baseLocMap`), the hypothesis the quotient lift needs. `Iad`/`IadDeep` are the
localized images of the base / deep
`sigmaIdeal`s; `baseLocMap` intertwines the localization maps (`baseLocMap_algebraMap`) and carries
the base `sigmaIdeal` into the deep one (`deepBaseComap_sigmaIdeal_le`). -/
theorem Iad_le_comap_IadDeep (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    Iad (k := k) (d 0) (d (Fin.last N)) r hp hq
      ≤ (IadDeep (k := k) d r hp hq).comap (baseLocMap (k := k) d r hp hq) := by
  rw [Iad, Ideal.map_le_iff_le_comap]
  intro g hg
  rw [Ideal.mem_comap, Ideal.mem_comap, baseLocMap_algebraMap, IadDeep]
  -- `deepBaseComap g ∈ sigmaIdeal d r` (the base → deep direction), then push into the localization
  have hmem : deepBaseComap (k := k) d g ∈ sigmaIdeal (k := k) d r :=
    deepBaseComap_sigmaIdeal_le d r (Ideal.mem_map_of_mem _ hg)
  exact Ideal.mem_map_of_mem _ hmem

/-- **The localized base→total map on the quotients** `(Localization.Away detPivotPoly ⧸ Iad) →ₐ[k]
Sred d r`: the quotient lift of `baseLocMap` (`Ideal.quotientMapₐ`, the ideal hypothesis from
`Iad_le_comap_IadDeep`). -/
noncomputable def baseQuotMap (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    (Localization.Away (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq)
        ⧸ Iad (k := k) (d 0) (d (Fin.last N)) r hp hq)
      →ₐ[k] Sred (k := k) d r hp hq :=
  Ideal.quotientMapₐ (IadDeep (k := k) d r hp hq) (baseLocMap (k := k) d r hp hq)
    (Iad_le_comap_IadDeep d r hp hq)

/-- **The base→total `k`-algebra map** `SchurLoc q p r →ₐ[k] Sred d r` (`q = d 0`, `p = d last`):
`baseQuotMap` precomposed with `basePresentationEquiv.symm`. This is the morphism whose induced
algebra structure makes `Sred` a `SchurLoc`-algebra (the `R = SchurLoc`-algebra structure that
R2-3a's product iso `e` needs). `[IsAlgClosed k] [CharZero k]` (for `basePresentationEquiv`). -/
noncomputable def schurToSred [IsAlgClosed k] [CharZero k] (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    SchurLoc (k := k) (d 0) (d (Fin.last N)) r →ₐ[k] Sred (k := k) d r hp hq :=
  (baseQuotMap (k := k) d r hp hq).comp
    (basePresentationEquiv (k := k) (d 0) (d (Fin.last N)) r hp hq).symm.toAlgHom

/-! ## R2-3b-2 — the `SchurLoc`-algebra structure on `Sred` and the scalar tower

The base→total map `schurToSred` induces (via `RingHom.toAlgebra`) the `SchurLoc q p r`-algebra
structure on `Sred`, with `k → SchurLoc → Sred` a scalar tower. These instances are the
`[Algebra R S]` slot that R2-3a's `e : S ≃ₐ[k] R ⊗_k FibreAlg` consumes (`R = SchurLoc q p r`). -/

/-- **The `SchurLoc`-algebra structure on `Sred`**, induced by the base→total map `schurToSred`
(`RingHom.toAlgebra`). The `R = SchurLoc q p r`-algebra structure R2-3a's product iso `e` needs. -/
@[reducible] noncomputable def sredSchurAlgebra [IsAlgClosed k] [CharZero k] (d : Fin (N + 1) → ℕ)
    (r : ℕ) (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    Algebra (SchurLoc (k := k) (d 0) (d (Fin.last N)) r) (Sred (k := k) d r hp hq) :=
  (schurToSred (k := k) d r hp hq).toRingHom.toAlgebra

/-- The induced `SchurLoc`-algebra structure on `Sred` makes `k → SchurLoc q p r → Sred` a scalar
tower: `algebraMap k Sred` factors through `algebraMap k (SchurLoc …)` (both `schurToSred` and the
localization-quotient maps are `k`-algebra maps). -/
theorem sredSchur_isScalarTower [IsAlgClosed k] [CharZero k] (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    @IsScalarTower k (SchurLoc (k := k) (d 0) (d (Fin.last N)) r) (Sred (k := k) d r hp hq)
      _ (sredSchurAlgebra (k := k) d r hp hq).toSMul _ := by
  letI := sredSchurAlgebra (k := k) d r hp hq
  refine IsScalarTower.of_algebraMap_eq (fun x ↦ ?_)
  -- `algebraMap (SchurLoc …) Sred = schurToSred.toRingHom` (by `toAlgebra`); `schurToSred` is a
  -- `k`-algebra map, so it commutes with `algebraMap k (SchurLoc …)` (`AlgHom.commutes`).
  change algebraMap k (Sred (k := k) d r hp hq) x
      = (schurToSred (k := k) d r hp hq).toRingHom (algebraMap k _ x)
  exact (AlgHom.commutes (schurToSred (k := k) d r hp hq) x).symm

/-! ## R2-3b-3 pre-stage (durable contract, NOT proved here)

The endpoint-normalization `AlgEquiv` for R2-3b-3 is an `aeval`-substitution on the **unquotiented**
`MvPolynomial (RepCoord d) R` over an **arbitrary** coefficient ring `R` (Codex: NOT
`baseChangeAlgEquiv`, which carries `[Infinite k]` from polynomial-function ext). The contract — two
`aeval` substitutions that round-trip on generators, assembled by `AlgEquiv.ofAlgHom` — is pinned
here so R2-3b-3 inherits the exact shape. (`example`: the contract, not the genuine
substitution.) -/

/-- **R2-3b-3 pre-stage contract.** Two coordinate substitutions `toSub`, `fromSub : RepCoord d →
MvPolynomial (RepCoord d) R` over an arbitrary commutative ring `R`, mutually inverse on the
generators, assemble to a coordinate-change `AlgEquiv` of `MvPolynomial (RepCoord d) R` via
`AlgEquiv.ofAlgHom` (each direction an `aeval`; the round-trips by `MvPolynomial.algHom_ext` +
`aeval_X`). The endpoint-normalization substitution of R2-3b-3 instantiates this. -/
noncomputable example {R : Type u} [CommRing R] (d : Fin (N + 1) → ℕ)
    (toSub fromSub : RepCoord d → MvPolynomial (RepCoord d) R)
    (h_to_from : ∀ x, aeval toSub (fromSub x) = (X x : MvPolynomial (RepCoord d) R))
    (h_from_to : ∀ x, aeval fromSub (toSub x) = (X x : MvPolynomial (RepCoord d) R)) :
    MvPolynomial (RepCoord d) R ≃ₐ[R] MvPolynomial (RepCoord d) R :=
  AlgEquiv.ofAlgHom (aeval toSub) (aeval fromSub)
    (by
      apply MvPolynomial.algHom_ext
      intro x
      change aeval toSub (aeval fromSub (X x)) = _
      rw [aeval_X]; exact h_to_from x)
    (by
      apply MvPolynomial.algHom_ext
      intro x
      change aeval fromSub (aeval toSub (X x)) = _
      rw [aeval_X]; exact h_from_to x)

/-! ## Non-vacuity witnesses

The deep constructions fire on the `N = 1` specialization `(d 0, d last) = (q, p)`, where they
reproduce the `N = 1` base data. We exhibit (i) the type bridge at `(2, 2)`, (ii) `deepBaseComap` /
`deepBaseComap_detPivot` at the `N = 1` stratum `dStratum 2 2`, `r = 1`, where the deep pivot minor
**is** the `N = 1` `detPivotPoly` (`deepBaseComap` is the identity-up-to-rename there), and (iii)
the localized base→total quotient map `baseQuotMap` available at that anchor over
`AlgebraicClosure ℚ`. -/

section Witness

/-- The type bridge `RepCoord (dStratum 2 2) ≃ Fin 2 × Fin 2` round-trips on a concrete coordinate
(the `(1, 0)` entry of the single matrix). -/
example : repStratumEquiv 2 2 ⟨0, (⟨1, by norm_num⟩, ⟨0, by norm_num⟩)⟩
    = (⟨1, by norm_num⟩, ⟨0, by norm_num⟩) := rfl

/-- `deepBaseComap` at the `N = 1` stratum `dStratum 2 2` sends `X ⟨0, (a, b)⟩` to the deep generic
product entry `multPoly (dStratum 2 2) a b` — non-vacuous (`N = 1` specialization). -/
example (a : Fin (dStratum 2 2 (Fin.last 1))) (b : Fin (dStratum 2 2 0)) :
    deepBaseComap (k := AlgebraicClosure ℚ) (dStratum 2 2) (X ⟨0, (a, b)⟩)
      = multPoly (dStratum 2 2) a b :=
  deepBaseComap_X _ a b

/-- The pivot-minor transport fires at the `N = 1` stratum `dStratum 2 2`, `r = 1`:
`deepBaseComap (detPivotPoly …) = ΔPdeep …`. -/
example (h : (1 : ℕ) ≤ 2) :
    deepBaseComap (k := AlgebraicClosure ℚ) (dStratum 2 2)
        (detPivotPoly (k := AlgebraicClosure ℚ) (dStratum 2 2 0) (dStratum 2 2 (Fin.last 1)) 1 h h)
      = ΔPdeep (k := AlgebraicClosure ℚ) (dStratum 2 2) 1 h h :=
  deepBaseComap_detPivot (dStratum 2 2) 1 h h

/-- The localized base→total quotient map `baseQuotMap` is available at the `N = 1` anchor
`dStratum 2 2`, `r = 1`, over `AlgebraicClosure ℚ` — non-vacuous. (It needs no `IsAlgClosed` /
`CharZero`; `schurToSred` composes this with `basePresentationEquiv.symm`.) -/
noncomputable example (h : (1 : ℕ) ≤ 2) :
    (Localization.Away
          (detPivotPoly (k := AlgebraicClosure ℚ)
            (dStratum 2 2 0) (dStratum 2 2 (Fin.last 1)) 1 h h)
        ⧸ Iad (k := AlgebraicClosure ℚ) (dStratum 2 2 0) (dStratum 2 2 (Fin.last 1)) 1 h h)
      →ₐ[AlgebraicClosure ℚ] Sred (k := AlgebraicClosure ℚ) (dStratum 2 2) 1 h h :=
  baseQuotMap (dStratum 2 2) 1 h h

/-- `Sred` is reduced at the `N = 1` anchor `dStratum 2 2`, `r = 1`, over `AlgebraicClosure ℚ` — the
name is honest there, and R2-3a's `hSred` is discharged. -/
example (h : (1 : ℕ) ≤ 2) :
    IsReduced (Sred (k := AlgebraicClosure ℚ) (dStratum 2 2) 1 h h) :=
  isReduced_Sred (dStratum 2 2) 1 h h

end Witness

end DLNFibre.Core
