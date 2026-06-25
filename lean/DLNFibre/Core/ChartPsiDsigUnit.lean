/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.ChartPsiDescent
import DLNFibre.Core.ChartGaugeNormalize

/-!
# `DLNFibre.Core.ChartPsiDsigUnit` — the deep pivot minor maps to a unit (seam C sorry-2)

The symbolic product-reconstruction completing seam C of the route-β Ψ descent (thread 31): the Ψ
comorphism carries the deep pivot minor `ΔPdeep` (the top-left `r×r` minor of the generic product)
to a **unit** of `Localization.Away gF`. This discharges `chartPsi_dsig_isUnit`, the last obligation
before `chartPsiLoc` is an honest localized algebra hom.

The value: `chartPsiAeval ΔPdeep = (image of detSchurS in Away gF)`, a unit (it is the inverted
element of the schur-side localization, pushed in by `schurToGfib`). Two ingredients:

1. `map_algebraMap_multPoly` — the generic product entry is natural in the coefficient ring:
   `map (algebraMap k S) (multPoly_k r c) = multPoly_S r c`. By `multPrefix` induction (the
   `X`-generators are fixed by `map (algebraMap)`).

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix

universe u

variable {k : Type u} [CommRing k] {N : ℕ}

/-- The generic prefix product is natural in the coefficient ring: `map (algebraMap k S)` carries
the `k`-prefix product to the `S`-prefix product (the `X`-generators are fixed). `multPrefix`
induction, mirroring `map_eval_multPrefix`. -/
theorem map_algebraMap_multPrefix (S : Type u) [CommRing S] [Algebra k S]
    (d : Fin (N + 1) → ℕ) (j : Fin (N + 1)) :
    (multPrefix d (genericTuple (k := k) d) j).map
        (MvPolynomial.map (algebraMap k S) : MvPolynomial (RepCoord d) k →+* _)
      = multPrefix d (genericTuple (k := S) d) j := by
  induction j using Fin.induction with
  | zero =>
    simp only [multPrefix_zero]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  | succ i ih =>
    rw [multPrefix_succ, multPrefix_succ, Matrix.map_mul, ih]
    congr 1
    funext rr cc
    rw [Matrix.map_apply, genericTuple_apply, genericTuple_apply, MvPolynomial.map_X]

/-- **The generic product entry is natural in the coefficient ring.**
`map (algebraMap k S) (multPoly_k r c) = multPoly_S r c`. The `map`-image of the deep generic
product over `k` is the deep generic product over `S` (the `X`-generators are fixed by `map`). -/
theorem map_algebraMap_multPoly (S : Type u) [CommRing S] [Algebra k S]
    (d : Fin (N + 1) → ℕ) (r : Fin (d (Fin.last N))) (c : Fin (d 0)) :
    MvPolynomial.map (algebraMap k S) (multPoly (k := k) d r c)
      = multPoly (k := S) d r c := by
  have h := map_algebraMap_multPrefix (k := k) S d (Fin.last N)
  have h2 := congrFun (congrFun h r) c
  rw [Matrix.map_apply] at h2
  simpa [multPoly, mult] using h2

section Field

variable {k : Type u} [Field k] {N : ℕ}

/-- **The Ψ comorphism factors through the gauge `AlgEquiv` (`k`-coefficient form).** For any
`k`-coefficient polynomial `p`, `chartPsiAeval p` is the `chartPsiTower`-image of the gauge
`AlgEquiv` (`gaugeEquiv (endpointGauge⁻¹)`) applied to the `SchurLoc`-lift `map (algebraMap k
SchurLoc) p`. Pure ring-hom bookkeeping (avoids `comp_aeval`, which needs `chartPsiTower` to be
`SchurLoc`-linear, but it is only `k`-linear): push `chartPsiTower` through the `aeval` by
`map_aeval` (its coefficient leg is `schurToGfib`, `aevalTower_comp_algebraMap`), and match
`chartPsiAeval = eval₂Hom (algebraMap k (Away gF)) chartPsiSub` via `eval₂Hom_map_hom` + the scalar
tower `schurToGfib ∘ algebraMap k SchurLoc = algebraMap k (Away gF)`. The seam-3b
`chartPsiTower_gaugeEquiv` bridge, at `k`-coeffs. -/
theorem chartPsiAeval_eq_tower_gaugeEquiv_map (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) (p : MvPolynomial (RepCoord d) k) :
    chartPsiAeval k d r hp hq p
      = chartPsiTower k d r hp hq
          (gaugeEquiv d (endpointGauge (k := k) d r hp hq)⁻¹
            (MvPolynomial.map
              (algebraMap k (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)) p)) := by
  -- RHS: push `chartPsiTower` through `aeval (gaugeSub …)` at the ring-hom level (`map_aeval`).
  rw [gaugeEquiv_apply,
    show chartPsiTower k d r hp hq
        (aeval (gaugeSub d (endpointGauge (k := k) d r hp hq)⁻¹)
          (MvPolynomial.map (algebraMap k (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)) p))
      = (chartPsiTower k d r hp hq).toRingHom
          (aeval (gaugeSub d (endpointGauge (k := k) d r hp hq)⁻¹)
            (MvPolynomial.map
              (algebraMap k (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)) p)) from rfl,
    MvPolynomial.map_aeval]
  -- the coefficient leg `chartPsiTower ∘ algebraMap SchurLoc = schurToGfib`.
  rw [show (chartPsiTower k d r hp hq).toRingHom.comp
        (algebraMap (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
          (MvPolynomial (RepCoord d) (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)))
      = (schurToGfib k d r hp hq).toRingHom from by
    rw [chartPsiTower]; exact MvPolynomial.aevalTower_comp_algebraMap _ _]
  -- RHS: `eval₂Hom schurToGfib chartPsiSub (map (algebraMap k SchurLoc) p)` collapses to
  -- `eval₂Hom (schurToGfib ∘ algebraMap k SchurLoc) chartPsiSub p` (`eval₂Hom_map_hom`).
  rw [MvPolynomial.eval₂Hom_map_hom]
  -- LHS: `chartPsiAeval = aeval chartPsiSub = eval₂Hom (algebraMap k (Away gF)) chartPsiSub`.
  rw [chartPsiAeval]
  change (MvPolynomial.aeval (chartPsiSub k d r hp hq)) p
    = MvPolynomial.eval₂Hom
        ((schurToGfib k d r hp hq).toRingHom.comp
          (algebraMap k (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)))
        (chartPsiSub k d r hp hq) p
  rw [MvPolynomial.aeval_def]
  -- both sides are `eval₂` with substitution `chartPsiSub`; match the coefficient ring homs.
  congr 1
  -- `schurToGfib ∘ algebraMap k SchurLoc = algebraMap k (Away gF)` (scalar tower, `k`-alg hom).
  ext a
  change algebraMap k (Localization.Away (chartGfib k d r hp hq)) a
    = (schurToGfib k d r hp hq).toRingHom
        (algebraMap k (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r) a)
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]

/-- **`chartPsiTower` on a `SchurLoc`-lifted `k`-polynomial reads the `O(F)`-class.**
`chartPsiTower (map (algebraMap k SchurLoc) p) = algebraMap O(F) (Away gF) (mk_F p)`: the
`k`-constant coefficients pass straight through (coeff leg `schurToGfib ∘ algebraMap k SchurLoc =
algebraMap k`), and the `RepCoord` generators evaluate via `fibCoordT` to the `O(F)`-classes, so the
whole polynomial reads its `O(F)`-class `mk_F p`. Proved by ring-hom extensionality
(`MvPolynomial.ringHom_ext` on the two composite homs, then applied to `p`). The bridge that turns
the `multPoly` block into its fibre value `normalForm`. -/
theorem chartPsiTower_map_algebraMap (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) (p : MvPolynomial (RepCoord d) k) :
    chartPsiTower k d r hp hq
        (MvPolynomial.map
          (algebraMap k (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)) p)
      = algebraMap (sweepFibreRing k d r hp hq) (Localization.Away (chartGfib k d r hp hq))
          (Ideal.Quotient.mk (vanishingIdeal k (sweepFibre k d r hp hq)) p) := by
  -- compare the two composite ring homs `MvPoly (RepCoord d) k →+* Away gF` (then apply to `p`).
  have hext : (chartPsiTower k d r hp hq).toRingHom.comp
        (MvPolynomial.map (algebraMap k (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)))
      = (algebraMap (sweepFibreRing k d r hp hq)
            (Localization.Away (chartGfib k d r hp hq))).comp
          (Ideal.Quotient.mk (vanishingIdeal k (sweepFibre k d r hp hq))) := by
    refine MvPolynomial.ringHom_ext ?_ ?_
    · intro a
      -- constants: both sides are `algebraMap k (Away gF) a`.
      rw [RingHom.comp_apply, MvPolynomial.map_C, RingHom.comp_apply]
      change chartPsiTower k d r hp hq
          (C (algebraMap k (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r) a)) = _
      rw [chartPsiTower, MvPolynomial.aevalTower_C, AlgHom.commutes,
        show Ideal.Quotient.mk (vanishingIdeal k (sweepFibre k d r hp hq)) (C a)
          = algebraMap k (sweepFibreRing k d r hp hq) a from rfl,
        ← IsScalarTower.algebraMap_apply]
    · intro x
      -- generators: `chartPsiTower (X x) = fibCoordT x = algebraMap O(F) (Away gF) (mk (X x))`.
      rw [RingHom.comp_apply, MvPolynomial.map_X, RingHom.comp_apply]
      change chartPsiTower k d r hp hq (X x) = _
      rw [chartPsiTower, MvPolynomial.aevalTower_X, fibCoordT]
  have := DFunLike.congr_fun hext p
  rw [RingHom.comp_apply, RingHom.comp_apply] at this
  exact this

/-- **The generic product reads its fibre value `normalForm` (modulo the fibre vanishing ideal).**
`multPoly d a b − C (normalForm a b)` vanishes on the fibre locus `sweepFibre`: a fibre point
`canonicalCoord B` has `mult B = normalForm`, so `eval (canonicalCoord B) (multPoly a b) =
(mult B) a b = normalForm a b`. The bridge that, under `chartPsiTower`, turns the `multPoly`
block into the rank-`r` normal form `diag(I_r, 0)`. -/
theorem multPoly_sub_normalForm_mem_vanishingIdeal (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (a : Fin (d (Fin.last (N + 1)))) (b : Fin (d 0)) :
    multPoly d a b - C (normalForm (d (Fin.last (N + 1))) (d 0) r hp hq a b)
      ∈ vanishingIdeal k (sweepFibre k d r hp hq) := by
  rw [mem_vanishingIdeal_iff]
  rintro y ⟨B, hB, rfl⟩
  rw [aeval_eq_eval, map_sub, eval_multPoly, MvPolynomial.eval_C]
  -- `mult B = normalForm` since `B ∈ fibre normalForm`, so the two values coincide.
  rw [(mem_fibre.mp hB)]
  exact sub_self _

/-- **The `SchurLoc`-lifted generic product entry reads the normal form under `chartPsiTower`.**
Combining brick 3 (`chartPsiTower_map_algebraMap`) with the fibre fact: the `chartPsiTower`-image of
the `SchurLoc`-lifted generic product entry is the `Away gF`-image of the constant `normalForm a b`.
The per-entry input to the matrix-product collapse. -/
theorem chartPsiTower_map_multPoly_eq_normalForm (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (a : Fin (d (Fin.last (N + 1)))) (b : Fin (d 0)) :
    chartPsiTower k d r hp hq
        (MvPolynomial.map (algebraMap k (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r))
          (multPoly d a b))
      = algebraMap k (Localization.Away (chartGfib k d r hp hq))
          (normalForm (d (Fin.last (N + 1))) (d 0) r hp hq a b) := by
  rw [chartPsiTower_map_algebraMap]
  -- `mk_F (multPoly a b) = mk_F (C (normalForm a b))` by the fibre fact, then `mk_F (C c) =
  -- algebraMap k O(F) c`, and the scalar tower `algebraMap O(F) ∘ algebraMap k = algebraMap k`.
  rw [show Ideal.Quotient.mk (vanishingIdeal k (sweepFibre k d r hp hq)) (multPoly d a b)
      = Ideal.Quotient.mk (vanishingIdeal k (sweepFibre k d r hp hq))
          (C (normalForm (d (Fin.last (N + 1))) (d 0) r hp hq a b)) from by
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact multPoly_sub_normalForm_mem_vanishingIdeal d r hp hq a b]
  rw [show Ideal.Quotient.mk (vanishingIdeal k (sweepFibre k d r hp hq))
        (C (normalForm (d (Fin.last (N + 1))) (d 0) r hp hq a b))
      = algebraMap k (sweepFibreRing k d r hp hq)
          (normalForm (d (Fin.last (N + 1))) (d 0) r hp hq a b) from rfl,
    ← IsScalarTower.algebraMap_apply]

/-- The target-vertex value of the **inverse** endpoint gauge is the `C`-image of `Lmat`. With
`P = endpointGauge⁻¹`, `liftGauge P last = (liftGauge endpointGauge last)⁻¹`, whose value is the
`C`-image of `(endpointGauge last)⁻¹ = Lmat` (`endpointGauge_last`: `endpointGauge last =
Lmat-unit⁻¹`, so its inverse is `Lmat`). -/
theorem liftGauge_endpointGauge_inv_last (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    Units.val (liftGauge d (endpointGauge (k := k) d r hp hq)⁻¹ (Fin.last (N + 1)))
      = (Lmat (k := k) (d 0) (d (Fin.last (N + 1))) r hp).map
          (C : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →+* _) := by
  rw [liftGauge_inv, Pi.inv_apply, liftGauge_inv_val_eq, endpointGauge_last, inv_inv]
  rfl

/-- The source-vertex value of the **inverse** of the inverse endpoint gauge is the `C`-image of
`Hmat`. With `P = endpointGauge⁻¹`, `(liftGauge P 0)⁻¹ = liftGauge endpointGauge 0` (double
inverse), whose value is the `C`-image of `endpointGauge 0 = Hmat` (`endpointGauge_zero`). -/
theorem liftGauge_endpointGauge_inv_zero_inv (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    Units.val ((liftGauge d (endpointGauge (k := k) d r hp hq)⁻¹ 0)⁻¹)
      = (Hmat (k := k) (d 0) (d (Fin.last (N + 1))) r hq).map
          (C : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →+* _) := by
  rw [liftGauge_inv, Pi.inv_apply, inv_inv, liftGauge_val_eq, endpointGauge_zero]
  rfl

/-- **The Ψ comorphism on a generic product entry is the conjugated entry under `chartPsiTower`.**
Combining brick 2 (`chartPsiAeval_eq_tower_gaugeEquiv_map`), brick 1 (`map_algebraMap_multPoly`),
`gaugeEquiv_multPoly` at `P = endpointGauge⁻¹`, and the two gauge-inverse value identities
(`(P⁻¹)_last = Lmat`, `((P⁻¹)_0)⁻¹ = Hmat`): `chartPsiAeval (multPoly rr cc) = chartPsiTower
((C Lmat · M_SL · C Hmat) rr cc)`, the `(rr, cc)` entry of the conjugated `SchurLoc`-product. -/
theorem chartPsiAeval_multPoly_eq_conj (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (rr : Fin (d (Fin.last (N + 1)))) (cc : Fin (d 0)) :
    chartPsiAeval k d r hp hq (multPoly d rr cc)
      = chartPsiTower k d r hp hq
          (((Lmat (k := k) (d 0) (d (Fin.last (N + 1))) r hp).map
                (C : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →+* _)
              * Matrix.of (multPoly d)
              * (Hmat (k := k) (d 0) (d (Fin.last (N + 1))) r hq).map
                (C : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →+* _) :
            Matrix (Fin (d (Fin.last (N + 1)))) (Fin (d 0))
              (MvPolynomial (RepCoord d) (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)))
            rr cc) := by
  rw [chartPsiAeval_eq_tower_gaugeEquiv_map, map_algebraMap_multPoly, gaugeEquiv_multPoly,
    liftGauge_endpointGauge_inv_last d r hp hq, liftGauge_endpointGauge_inv_zero_inv d r hp hq]

/-! ## Brick 4 — the determinant assembly (`chartPsiAeval ΔPdeep` is a unit) -/

/-- `chartPsiTower` reads a constant `C s` (`s : SchurLoc`) as `schurToGfib s` (the coefficient leg
of the `aevalTower`). -/
theorem chartPsiTower_C (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (s : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r) :
    chartPsiTower k d r hp hq (C s) = schurToGfib k d r hp hq s := by
  rw [chartPsiTower, MvPolynomial.aevalTower_C]

/-- **The Ψ-image of the generic product matrix factors as `L' · E · H'` over `Away gF`.** The full
`p×q` identity behind `chartPsiAeval ΔPdeep`: mapping the generic product `Matrix.of (multPoly d)`
entrywise by `chartPsiAeval` gives `(Lmat.map schurToGfib) · (normalForm.map (algebraMap k)) ·
(Hmat.map schurToGfib)`. Each entry is `chartPsiAeval_multPoly_eq_conj` (the conjugated entry under
`chartPsiTower`); pushing the ring hom `chartPsiTower` through the matrix product (`Matrix.map_mul`)
turns the `C`-lifted gauge blocks into their `schurToGfib`-images (`chartPsiTower_C`) and the
generic product into the normal form `E = diag(I_r, 0)`
(`chartPsiTower_map_multPoly_eq_normalForm`). -/
theorem map_chartPsiAeval_multPoly_eq (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    (Matrix.of (multPoly d)).map (chartPsiAeval k d r hp hq)
      = (Lmat (k := k) (d 0) (d (Fin.last (N + 1))) r hp).map (schurToGfib k d r hp hq)
          * (normalForm (d (Fin.last (N + 1))) (d 0) r hp hq).map
              (algebraMap k (Localization.Away (chartGfib k d r hp hq)))
          * (Hmat (k := k) (d 0) (d (Fin.last (N + 1))) r hq).map (schurToGfib k d r hp hq) := by
  -- Step 1: `Mpsi = (C Lmat · M_SL · C Hmat).map chartPsiTower` (per-entry brick 2/1 + gauge).
  -- abbreviate the `SchurLoc`-coefficient conjugated product.
  set conj : Matrix (Fin (d (Fin.last (N + 1)))) (Fin (d 0))
      (MvPolynomial (RepCoord d) (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)) :=
    (Lmat (k := k) (d 0) (d (Fin.last (N + 1))) r hp).map
        (C : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →+* _)
      * Matrix.of (multPoly d)
      * (Hmat (k := k) (d 0) (d (Fin.last (N + 1))) r hq).map
        (C : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →+* _) with hconj
  have hstep1 : (Matrix.of (multPoly d)).map (chartPsiAeval k d r hp hq)
      = conj.map (chartPsiTower k d r hp hq).toRingHom := by
    ext rr cc
    rw [Matrix.map_apply, Matrix.of_apply, chartPsiAeval_multPoly_eq_conj, Matrix.map_apply, hconj]
    rfl
  rw [hstep1, hconj, Matrix.map_mul, Matrix.map_mul]
  -- identify the three mapped factors with `L'`, `E`, `H'`.
  have hL : ((Lmat (k := k) (d 0) (d (Fin.last (N + 1))) r hp).map
        (C : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →+* _)).map
          (chartPsiTower k d r hp hq).toRingHom
      = (Lmat (k := k) (d 0) (d (Fin.last (N + 1))) r hp).map (schurToGfib k d r hp hq) := by
    ext a b
    rw [Matrix.map_apply, Matrix.map_apply, Matrix.map_apply]
    exact chartPsiTower_C d r hp hq _
  have hH : ((Hmat (k := k) (d 0) (d (Fin.last (N + 1))) r hq).map
        (C : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →+* _)).map
          (chartPsiTower k d r hp hq).toRingHom
      = (Hmat (k := k) (d 0) (d (Fin.last (N + 1))) r hq).map (schurToGfib k d r hp hq) := by
    ext a b
    rw [Matrix.map_apply, Matrix.map_apply, Matrix.map_apply]
    exact chartPsiTower_C d r hp hq _
  have hM : (Matrix.of (multPoly d) :
        Matrix (Fin (d (Fin.last (N + 1)))) (Fin (d 0))
          (MvPolynomial (RepCoord d) (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r))).map
          (chartPsiTower k d r hp hq).toRingHom
      = (normalForm (d (Fin.last (N + 1))) (d 0) r hp hq).map
          (algebraMap k (Localization.Away (chartGfib k d r hp hq))) := by
    ext a b
    rw [Matrix.map_apply, Matrix.map_apply, Matrix.of_apply]
    -- `multPoly_SL a b = map (algebraMap k SchurLoc) (multPoly_k a b)` (brick 1), then brick 3.
    rw [show (multPoly (k := SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r) d a b)
        = MvPolynomial.map (algebraMap k (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r))
            (multPoly d a b) from (map_algebraMap_multPoly _ d a b).symm]
    exact chartPsiTower_map_multPoly_eq_normalForm d r hp hq a b
  rw [hL, hM, hH]

set_option synthInstance.maxHeartbeats 400000 in
-- The deep `Localization.Away (chartGfib …)` coefficient type makes the matrix instance search
-- (`AddZeroClass`/`Mul` on `Matrix _ _ (Away gF)`) deep; the block-arithmetic `simp only` at the
-- end needs the raised `synthInstance` budget.
/-- **The top-left `r×r` block of the Ψ-image factorization is `schurΔLoc.map schurToGfib`.** The
deep pivot minor `ΔPdeep` is the determinant of the `castLE`-submatrix of `Matrix.of (multPoly d)`;
its `chartPsiAeval`-image is the determinant of the top-left block of `L' · E · H'`
(`map_chartPsiAeval_multPoly_eq`). With `L'` lower-unitriangular, `E = diag(I_r, 0)`, `H'` upper-
triangular with pivot block `Δ' = schurΔLoc.map schurToGfib`, that block computes (block-product
`[[1,0],[*,1]]·[[1,0],[0,0]]·[[Δ',Y],[0,1]]`) to `Δ'`. -/
theorem submatrix_map_chartPsiAeval_eq_schurΔ (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    (((Matrix.of (multPoly d)).map (chartPsiAeval k d r hp hq)).submatrix
        (fun i : Fin r ↦ (Fin.castLE hp i : Fin (d (Fin.last (N + 1)))))
        (fun j : Fin r ↦ (Fin.castLE hq j : Fin (d 0))))
      = (schurΔLoc (k := k) (d 0) (d (Fin.last (N + 1))) r).map (schurToGfib k d r hp hq) := by
  rw [map_chartPsiAeval_multPoly_eq]
  -- unfold the three mapped factors to block-submatrix form (`Lmat`/`normalForm`/`Hmat`).
  rw [show (Lmat (k := k) (d 0) (d (Fin.last (N + 1))) r hp).map (schurToGfib k d r hp hq)
      = ((LblockSum (d 0) (d (Fin.last (N + 1))) r).map (schurToGfib k d r hp hq)).submatrix
          (finSplit hp) (finSplit hp) from by
    rw [Lmat, reindexAlgEquiv_apply, reindex_apply, Equiv.symm_symm, ← Matrix.submatrix_map]]
  rw [show (Hmat (k := k) (d 0) (d (Fin.last (N + 1))) r hq).map (schurToGfib k d r hp hq)
      = ((HblockSum (d 0) (d (Fin.last (N + 1))) r).map (schurToGfib k d r hp hq)).submatrix
          (finSplit hq) (finSplit hq) from by
    rw [Hmat, reindexAlgEquiv_apply, reindex_apply, Equiv.symm_symm, ← Matrix.submatrix_map]]
  rw [show (normalForm (d (Fin.last (N + 1))) (d 0) r hp hq).map
        (algebraMap k (Localization.Away (chartGfib k d r hp hq)))
      = ((Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) _) 0 0 0).map
            (algebraMap k (Localization.Away (chartGfib k d r hp hq)))).submatrix
          (finSplit hp) (finSplit hq) from by
    rw [normalForm, ← Matrix.submatrix_map]]
  -- telescope the two products over the matching inner reindexings (`finSplit hp`, `finSplit hq`).
  rw [Matrix.submatrix_mul_equiv _ _ _ (finSplit hp) _,
    Matrix.submatrix_mul_equiv _ _ _ (finSplit hq) _]
  -- the outer `castLE`-submatrix picks the `Sum.inl` (= `toBlocks₁₁`) block.
  rw [Matrix.submatrix_submatrix]
  ext i j
  rw [Matrix.submatrix_apply, Function.comp_apply, Function.comp_apply,
    finSplit_castLE, finSplit_castLE]
  -- the block-(1,1) of the block product `[[1,0],[*,1]]·[[1,0],[0,0]]·[[Δ',Y],[0,1]]` is `Δ'`.
  rw [LblockSum, HblockSum, Matrix.fromBlocks_map, Matrix.fromBlocks_map, Matrix.fromBlocks_map,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _),
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _),
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_apply₁₁]
  -- block-(1,1): `(1·1+0·0)·Δ' + (1·0+0·0)·0 = Δ'`.
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, Matrix.mul_one, Matrix.one_mul]

/-- **The deep pivot minor maps to a unit (seam C sorry-2).** `chartPsiAeval ΔPdeep` is a unit of
`Localization.Away gF`. By `AlgHom.map_det` it is the determinant of the top-left `r×r` block of the
Ψ-image of the generic product, which is `schurΔLoc.map schurToGfib`
(`submatrix_map_chartPsiAeval_eq_schurΔ`); its determinant is `schurToGfib (det schurΔLoc) =
schurToGfib (detSchurS-image)`, the inverted element of `SchurLoc` carried to a unit by the
`k`-algebra hom `schurToGfib`. This discharges `chartPsi_dsig_isUnit`. -/
theorem chartPsiAeval_ΔPdeep_isUnit (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    IsUnit (chartPsiAeval k d r hp hq (ΔPdeep d r hp hq)) := by
  -- `chartPsiAeval ΔPdeep = det (submatrix (M.map chartPsiAeval) castLE castLE)`.
  rw [ΔPdeep, AlgHom.map_det, AlgHom.mapMatrix_apply, ← Matrix.submatrix_map,
    submatrix_map_chartPsiAeval_eq_schurΔ]
  -- `det (schurΔLoc.map schurToGfib) = schurToGfib (det schurΔLoc)`, a unit.
  rw [show (schurΔLoc (k := k) (d 0) (d (Fin.last (N + 1))) r).map (schurToGfib k d r hp hq)
      = (schurToGfib k d r hp hq).toRingHom.mapMatrix
          (schurΔLoc (k := k) (d 0) (d (Fin.last (N + 1))) r) from rfl,
    ← RingHom.map_det]
  exact (isUnit_det_schurΔLoc (k := k) (d 0) (d (Fin.last (N + 1))) r).map
    (schurToGfib k d r hp hq).toRingHom

/-! ## Seam C — closing `chartPsi_dsig_isUnit` and the localized comorphism `chartPsiLoc` -/

variable (k) in
/-- **The localizing element maps to a unit** (seam C sorry-2, discharged). `chartPsiQuot dsig` is a
unit of `Localization.Away gF`: `chartPsiQuot` commutes with `mk`, so the goal is `IsUnit
(chartPsiAeval ΔPdeep)`, which is `chartPsiAeval_ΔPdeep_isUnit` (the brick-4 determinant assembly:
the deep pivot minor reads the Schur determinant, a unit). -/
theorem chartPsi_dsig_isUnit [Infinite k] (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    IsUnit (chartPsiQuot k d r hp hq (chartDsig k d r hp hq)) := by
  rw [show chartPsiQuot k d r hp hq (chartDsig k d r hp hq)
      = chartPsiAeval k d r hp hq (ΔPdeep d r hp hq) from by
    rw [chartDsig, chartPsiQuot, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]; rfl]
  exact chartPsiAeval_ΔPdeep_isUnit d r hp hq

variable (k) in
/-- **The localized Ψ comorphism** `chartPsiLoc : Localization.Away dsig →ₐ[k] Away gF`: the
`IsLocalization.liftAlgHom` lift of `chartPsiQuot`, which inverts the localizing element `dsig`
because `chartPsi_dsig_isUnit` makes its image a unit (the powers of `dsig` are then all units). -/
noncomputable def chartPsiLoc [Infinite k] (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    Localization.Away (chartDsig k d r hp hq) →ₐ[k] Localization.Away (chartGfib k d r hp hq) :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (chartDsig k d r hp hq))
    (f := chartPsiQuot k d r hp hq)
    (by
      rintro ⟨y, n, rfl⟩
      rw [map_pow]
      exact (chartPsi_dsig_isUnit k d r hp hq).pow n)

end Field

end DLNFibre.Core
