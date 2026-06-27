import DLNFibre.DLN.RLCT.Validate.RouteMGenChartId
import DLNFibre.DLN.RLCT.Validate.RouteMGenLeafIntegrand

/-!
# `RouteMGenFlatChart` — Phase B1: the general flat-frame chart + the ∀M general C1 (rate transfer)

The general (∀M) flat chart `chartParamsFlat`, generalizing the `(3,3,3,3)` probe
(`RouteMFlatChartProbe3333`) over the opaque `Wext`/`Text` widths. The decoder `genBlkFlat` reads the
`GenBlk M t` block data from a flat coordinate vector `x : Fin (routeMAmbient M) → ℝ`, with the IDENTITY
boundary at `k = 0` (`Bmat 0 = reindexed 1`, `Rmat 0 = 0`, under the descent condition `t_0 = M_0` so
`Text 0 = Text 1 = M_0`). Then `chartParamsFlat := chartParamsGen ∘ genBlkFlat`, so:

* **The general C1 keystone is definitional** (`rfl`): `chartParamsFlat x = chartParamsGen (x p) M t
  (genBlkFlat x) hle` (`chartParamsFlat_eq_chartParamsGen`).
* **The rate transfers ∀M for FREE**: `routeMCore_chartParamsFlat : routeMCore M (paramsEquivFlat ∘
  chartParamsFlat) = (x p)²·V` from the BANKED `routeMCore_phiGen`, given the identity-boundary `hC0`
  (`C 0 · suffix = suffix`). `hC0` is dischargeable per-instance (the concrete-width `C 0 = 1`, as
  `RouteMFlatChartProbe3333.Bflat3333_C0_eq_one` does for `(3,3,3,3)`); over the OPAQUE `Wext`/`Text`
  widths it is a heterogeneous-width fact carried as a hypothesis here.

The binding pivot is `p = ⟨0,_⟩` (the radial). The SPECIFIC block coordinatization (a uniform modular
index) is not load-bearing for the rate; it is fixed here so the downstream det (B3) has explicit factors.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (pure matrix algebra; no S2).
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

open Matrix

variable {L : ℕ}

/-! ## `chainQ` at `c = 0` is the identity (the `c`-general HEq form) -/

/-- **`chainQ` at `c = 0` is the identity** (`c`-general HEq form): when `c = 0` (so `M' = t`),
`chainQ h N` is heterogeneously the identity `1 : Matrix (Fin t) (Fin t)`. The dependent-width companion
of `chainQ_cZero` for when the residual width `c` is provably (not definitionally) `0`. -/
theorem chainQ_cZero_heq {M' t c : ℕ} (h : t + c = M') (hc : c = 0)
    (N : Matrix (Fin t) (Fin c) ℝ) :
    HEq (chainQ h N) (1 : Matrix (Fin t) (Fin t) ℝ) := by
  subst hc
  have hMt : M' = t := by omega
  subst hMt
  rw [chainQ_cZero h N]

/-- Under the descent condition `t_0 = M_0`, the first compressed width equals the second:
`Text 0 = Text 1` (both `= M_0`). The square-ness making the identity boundary's `Bmat 0` an identity. -/
theorem Text0_eq_Text1 (M t : Fin (L + 1) → ℕ) (hL : 0 < L) (ht0 : t ⟨0, by omega⟩ = M 0) :
    Text M t 0 = Text M t 1 := by
  rw [Text_succ M t 0 (by omega), ht0]; rfl

/-! ## The general flat decoder `genBlkFlat` -/

/-- A clean modular flat index into `Fin (routeMAmbient M)`. -/
def flatIdxOf (M : Fin (L + 1) → ℕ) (hN : 0 < routeMAmbient M) (n : ℕ) : Fin (routeMAmbient M) :=
  ⟨n % routeMAmbient M, Nat.mod_lt _ hN⟩

/-- **The general flat decoder** `genBlkFlat M t hN hL ht0 x : GenBlk M t` — reads the block data from
the flat coordinates, with the IDENTITY boundary `k = 0` (`Bmat 0 = reindexed 1`, `Rmat 0 = 0`); the
`ht0 : t_0 = M_0` descent condition makes `Text 0 = Text 1` so the `Bmat 0` reindex is the genuine
identity. The other boundaries read distinct flat slots (uniform modular indexing). -/
noncomputable def genBlkFlat (M t : Fin (L + 1) → ℕ) (hN : 0 < routeMAmbient M) (hL : 0 < L)
    (ht0 : t ⟨0, by omega⟩ = M 0) (x : Fin (routeMAmbient M) → ℝ) : GenBlk M t where
  Bmat := fun k => match k with
    | 0 => Matrix.reindex (Equiv.refl _) (finCongr (Text0_eq_Text1 M t hL ht0))
        (1 : Matrix (Fin (Text M t 0)) (Fin (Text M t 0)) ℝ)
    | (k + 1) => Matrix.of (fun i j => x (flatIdxOf M hN (i.val * 31 + j.val * 7 + (k + 1) * 3)))
  Nblk := fun k => Matrix.of (fun i j => x (flatIdxOf M hN (i.val * 31 + j.val * 7 + k * 13 + 1)))
  Wblk := fun k => Matrix.of (fun i j => x (flatIdxOf M hN (i.val * 31 + j.val * 7 + k * 13 + 2)))
  Rmat := fun k => match k with
    | 0 => (0 : Matrix (Fin (Text M t 0)) (Fin (Wext M 0)) ℝ)
    | (k + 1) => Matrix.of (fun i j => x (flatIdxOf M hN (i.val * 31 + j.val * 7 + (k + 1) * 13 + 3)))
  Rfin := fun k => Matrix.of (fun i j => x (flatIdxOf M hN (i.val * 31 + j.val * 7 + k * 13 + 4)))

/-! ## The general flat chart + the general C1 keystone (definitional) + the rate transfer -/

/-- **The general flat chart** `chartParamsFlat := chartParamsGen ∘ genBlkFlat`. Binding pivot `⟨0,_⟩`. -/
noncomputable def chartParamsFlat (M t : Fin (L + 1) → ℕ) (hN : 0 < routeMAmbient M) (hL : 0 < L)
    (ht0 : t ⟨0, by omega⟩ = M 0) (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k)
    (x : Fin (routeMAmbient M) → ℝ) : Params M :=
  chartParamsGen (x ⟨0, hN⟩) M t (genBlkFlat M t hN hL ht0 x) hle

/-- **The general C1 keystone (definitional)**: `chartParamsFlat = chartParamsGen (x p) M t
(genBlkFlat x) hle`. The `rfl` route validated on `(3,3,3,3)` (`RouteMFlatChartProbe3333`), now ∀M. -/
theorem chartParamsFlat_eq_chartParamsGen (M t : Fin (L + 1) → ℕ) (hN : 0 < routeMAmbient M) (hL : 0 < L)
    (ht0 : t ⟨0, by omega⟩ = M 0) (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k)
    (x : Fin (routeMAmbient M) → ℝ) :
    chartParamsFlat M t hN hL ht0 hle x
      = chartParamsGen (x ⟨0, hN⟩) M t (genBlkFlat M t hN hL ht0 x) hle := rfl

/-- **The flat chart as a map** `phiFlat := paramsEquivFlat ∘ chartParamsFlat`. -/
noncomputable def phiFlat (M t : Fin (L + 1) → ℕ) (hN : 0 < routeMAmbient M) (hL : 0 < L)
    (ht0 : t ⟨0, by omega⟩ = M 0) (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k)
    (x : Fin (routeMAmbient M) → ℝ) : Fin (routeMAmbient M) → ℝ :=
  paramsEquivFlat M (chartParamsFlat M t hN hL ht0 hle x)

/-- **The rate transfers to the flat chart ∀M** (the general C1 payoff). Given the identity-boundary
`hC0` (`C 0 · suffix = suffix`; dischargeable per-instance, e.g. `Bflat3333_C0_eq_one`), the BANKED
`routeMCore_phiGen` gives `routeMCore M (phiFlat x) = (x p)²·V` — NO re-proof of the telescope/cast rate
work (the keystone being `rfl`). -/
theorem routeMCore_chartParamsFlat (M t : Fin (L + 1) → ℕ) (hN : 0 < routeMAmbient M) (hL : 0 < L)
    (ht0 : t ⟨0, by omega⟩ = M 0) (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k)
    (x : Fin (routeMAmbient M) → ℝ)
    (hC0 : (chainOfMt (x ⟨0, hN⟩) M t (genBlkFlat M t hN hL ht0 x) hle).toChain.C 0
        * (chainOfMt (x ⟨0, hN⟩) M t (genBlkFlat M t hN hL ht0 x) hle).toChain.suffix 0 (Nat.zero_le L)
      = (chainOfMt (x ⟨0, hN⟩) M t (genBlkFlat M t hN hL ht0 x) hle).toChain.suffix 0
          (Nat.zero_le L)) :
    routeMCore M (phiFlat M t hN hL ht0 hle x)
      = (x ⟨0, hN⟩) ^ 2 * VvalGen (x ⟨0, hN⟩) M t (genBlkFlat M t hN hL ht0 x) hle := by
  rw [phiFlat, chartParamsFlat]
  exact routeMCore_phiGen (x ⟨0, hN⟩) M t (genBlkFlat M t hN hL ht0 x) hle hC0

end DLNFibre.DLN.RLCT
