import DLNFibre.DLN.RLCT.Validate.RouteMGenChartId

/-!
# `RouteMGenChartId3333` — the ∀M chart identity SPECIALIZES to `(3,3,3,3)` (validation)

Confirms the general `routeMCore_phiGen` (`RouteMGenChartId`) fires on the decisive multi-pivot witness
`M = (3,3,3,3)`, descent `t = (3,2,1,0)` (`Text = (3,3,2,1)` = the `(3,3,3,3)` compressed widths, matching
`RouteM3333Chain`'s `T3333w`). With the identity-boundary block data (`Bmat 0 = 1`, `Rmat 0 = 0`, empty
residual `N_0` so `chainQ` at `c_0 = 0` is `I` — `chainQ_cZero`), the hypothesis `hC0` (`C 0 · suffix =
suffix`) is discharged, so `routeMCore M3 (φ u) = u²·V` holds for `(3,3,3,3)` THROUGH the general
construction — the structural lift reproduces the concrete instance.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (pure matrix algebra; no analysis).
-/

namespace DLNFibre.DLN.RLCT

open Matrix

/-- `M3 = (3,3,3,3)`. -/
abbrev M3spec : Fin 4 → ℕ := ![3, 3, 3, 3]

/-- The achiever descent `t = (3,2,1,0)` (`t_0 = M_0 = 3`, `t_3 = 0`, strictly decreasing). -/
abbrev t3spec : Fin 4 → ℕ := ![3, 2, 1, 0]

/-- The descent admissibility `Text (k+1) ≤ Wext k` for the `(3,3,3,3)` achiever path. -/
theorem hle3spec : ∀ k, k < 3 → Text M3spec t3spec (k + 1) ≤ Wext M3spec k := by
  intro k hk; interval_cases k <;> simp [Text, Wext]

/-- The identity-boundary block data: `Bmat 0 = 1`, `Rmat 0 = 0`, and the residual `N 0` is the empty
`Fin 3 → Fin 0` block (`c_0 = Wext 0 − Text 1 = 3 − 3 = 0`). The other boundaries carry arbitrary free
block matrices `B*`. -/
noncomputable def genBlk3spec
    (B1 : Matrix (Fin 3) (Fin 2) ℝ) (R1 : Matrix (Fin 3) (Fin 3) ℝ)
    (N1 : Matrix (Fin 2) (Fin (Wext M3spec 1 - Text M3spec t3spec 2)) ℝ)
    (W1 : Matrix (Fin (Wext M3spec 1 - Text M3spec t3spec 2)) (Fin 3) ℝ)
    (B2 : Matrix (Fin 2) (Fin 1) ℝ) (R2 : Matrix (Fin 2) (Fin 3) ℝ)
    (N2 : Matrix (Fin 1) (Fin (Wext M3spec 2 - Text M3spec t3spec 3)) ℝ)
    (W2 : Matrix (Fin (Wext M3spec 2 - Text M3spec t3spec 3)) (Fin 3) ℝ)
    (Rleaf : Matrix (Fin 1) (Fin 3) ℝ) : GenBlk M3spec t3spec where
  Bmat := fun k =>
    match k with
    | 0 => (1 : Matrix (Fin 3) (Fin 3) ℝ)
    | 1 => B1
    | 2 => B2
    | (_ + 3) => 0
  Nblk := fun k =>
    match k with
    | 0 => (0 : Matrix (Fin 3) (Fin 0) ℝ)
    | 1 => N1
    | 2 => N2
    | (_ + 3) => 0
  Wblk := fun k =>
    match k with
    | 0 => (0 : Matrix (Fin 0) (Fin 3) ℝ)
    | 1 => W1
    | 2 => W2
    | (_ + 3) => 0
  Rmat := fun k =>
    match k with
    | 0 => (0 : Matrix (Fin 3) (Fin 3) ℝ)
    | 1 => R1
    | 2 => R2
    | (_ + 3) => 0
  Rfin := fun k =>
    match k with
    | 3 => Rleaf
    | _ => 0

/-- **`hC0` for the `(3,3,3,3)` specialization.** `C 0 · suffix 0 = suffix 0`: `C 0 = Bmat 0 · chainQ(N_0)
+ u • Rmat 0 = 1 · I + u • 0 = 1` (the identity boundary, `chainQ_cZero` at `c_0 = 0`), so `C 0` is the
identity and `C 0 · suffix = suffix`. -/
theorem hC0_3spec (u : ℝ)
    (B1 : Matrix (Fin 3) (Fin 2) ℝ) (R1 : Matrix (Fin 3) (Fin 3) ℝ)
    (N1 : Matrix (Fin 2) (Fin (Wext M3spec 1 - Text M3spec t3spec 2)) ℝ)
    (W1 : Matrix (Fin (Wext M3spec 1 - Text M3spec t3spec 2)) (Fin 3) ℝ)
    (B2 : Matrix (Fin 2) (Fin 1) ℝ) (R2 : Matrix (Fin 2) (Fin 3) ℝ)
    (N2 : Matrix (Fin 1) (Fin (Wext M3spec 2 - Text M3spec t3spec 3)) ℝ)
    (W2 : Matrix (Fin (Wext M3spec 2 - Text M3spec t3spec 3)) (Fin 3) ℝ)
    (Rleaf : Matrix (Fin 1) (Fin 3) ℝ) :
    (chainOfMt u M3spec t3spec (genBlk3spec B1 R1 N1 W1 B2 R2 N2 W2 Rleaf) hle3spec).toChain.C 0
        * (chainOfMt u M3spec t3spec (genBlk3spec B1 R1 N1 W1 B2 R2 N2 W2 Rleaf) hle3spec).toChain.suffix
            0 (Nat.zero_le 3)
      = (chainOfMt u M3spec t3spec (genBlk3spec B1 R1 N1 W1 B2 R2 N2 W2 Rleaf) hle3spec).toChain.suffix
            0 (Nat.zero_le 3) := by
  have hC0eq : (chainOfMt u M3spec t3spec (genBlk3spec B1 R1 N1 W1 B2 R2 N2 W2 Rleaf) hle3spec).toChain.C 0
      = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    rw [chainOfMt_C_zero u M3spec t3spec _ hle3spec (by norm_num)]
    -- `chainQ(N_0) = I` (c_0 = 0, `chainQ_cZero`); `Bmat 0 = 1`, `Rmat 0 = 0` (identity-boundary data).
    have hQ : chainQ (genWidthEq M3spec t3spec hle3spec 0 (by norm_num))
          ((genBlk3spec B1 R1 N1 W1 B2 R2 N2 W2 Rleaf).Nblk 0) = (1 : Matrix (Fin 3) (Fin 3) ℝ) :=
      chainQ_cZero _ _
    rw [hQ]
    -- `Bmat 0 = 1`, `Rmat 0 = 0` are the `match` arms; force literal `Fin 3` types via `show`.
    show (1 : Matrix (Fin 3) (Fin 3) ℝ) * (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + u • (0 : Matrix (Fin 3) (Fin 3) ℝ) = (1 : Matrix (Fin 3) (Fin 3) ℝ)
    rw [Matrix.one_mul, smul_zero, add_zero]
  -- `C 0 · suffix = 1 · suffix = suffix` (`rw [hC0eq]` keeps the right dependent type; `one_mul`).
  rw [hC0eq]
  exact Matrix.one_mul _

/-- **The ∀M chart identity SPECIALIZES to `(3,3,3,3)`.** `routeMCore M3 (φ u) = u²·V` for `M = (3,3,3,3)`,
descent `t = (3,2,1,0)`, via the GENERAL `routeMCore_phiGen` — the structural lift fires on the decisive
multi-pivot witness. -/
theorem routeMCore_phiGen_3spec (u : ℝ)
    (B1 : Matrix (Fin 3) (Fin 2) ℝ) (R1 : Matrix (Fin 3) (Fin 3) ℝ)
    (N1 : Matrix (Fin 2) (Fin (Wext M3spec 1 - Text M3spec t3spec 2)) ℝ)
    (W1 : Matrix (Fin (Wext M3spec 1 - Text M3spec t3spec 2)) (Fin 3) ℝ)
    (B2 : Matrix (Fin 2) (Fin 1) ℝ) (R2 : Matrix (Fin 2) (Fin 3) ℝ)
    (N2 : Matrix (Fin 1) (Fin (Wext M3spec 2 - Text M3spec t3spec 3)) ℝ)
    (W2 : Matrix (Fin (Wext M3spec 2 - Text M3spec t3spec 3)) (Fin 3) ℝ)
    (Rleaf : Matrix (Fin 1) (Fin 3) ℝ) :
    routeMCore M3spec (phiGen u M3spec t3spec (genBlk3spec B1 R1 N1 W1 B2 R2 N2 W2 Rleaf) hle3spec)
      = u ^ 2 * VvalGen u M3spec t3spec (genBlk3spec B1 R1 N1 W1 B2 R2 N2 W2 Rleaf) hle3spec :=
  routeMCore_phiGen u M3spec t3spec (genBlk3spec B1 R1 N1 W1 B2 R2 N2 W2 Rleaf) hle3spec
    (hC0_3spec u B1 R1 N1 W1 B2 R2 N2 W2 Rleaf)

end DLNFibre.DLN.RLCT
