import DLNFibre.DLN.RLCT.Validate.DeepestNormalFormFrontPivot
import DLNFibre.DLN.RLCT.Validate.DeepestCoreNonvanishing

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestNormalFormFrontPivotL2` — taint-clean L=2 value lemma

The `#44`-at-`L=2` close (thread `genm-44l2`). It re-homes the front-pivot value chain
(`DeepestNormalFormFrontPivot`) onto the **L=2-clean** gauge construction
`deepest_gauge_construction_L2` (`DeepestL2Wiring`), so the chain no longer inherits the `sorryAx`
taint of the GENERAL `deepest_gauge_construction` (whose `L ≥ 3` branch carries the roadmapped
`#120` interior/grouped-diffeo `sorry`s — `#print axioms` does NOT prune the unexecuted branch, so
the general producer taints any consumer even at `L = 2`).

## Why a separate producer (`deepest_gauge_chart_construct_L2`)

`deepest_gauge_chart_construct` (`DeepestL2Wiring`) obtains its chart from the general
`deepest_gauge_construction`. The L=2-clean `deepest_gauge_construction_L2` produces the SAME
16-field `DeepestGaugeChart` bundle, but needs the extra `hLlt : L < 3` (the L-split dispatch tag).
We thread `hLlt` and call `_L2` directly — same destructure, no general producer in the closure.

## Status of the four inputs (the honest named-open hypotheses)

The value form `deepest_regular_core_normal_form_L2` is the `L = 2` instance of the Skeleton's
`deepest_regular_core_normal_form` (`#44`), CONDITIONAL on:

- **`hJfront`** — the deepest-point frame-pivot `.choose` is the front embedding `frontEmbed`.
  **OPEN** (GATE-0, genm-44l2): the `#100`/`#154` column/row WLOG
  (`headline_frontRowColPivot_exists`) is at the `⨅ optimalSet` level and gives front-COLUMN-rank +
  top-ROW-rank facts, but nothing bridges those to the abstract-`.choose`-`frontEmbed` identity at
  the single `deepestPoint`. This is the remaining obstacle to the UNCONDITIONAL L=2 value (it also
  gates the D1 ≥-leg's `hDeepest`).
- **`htop`** — `B`'s top `r` rows are full rank (the row-alignment, KC1). OPEN, the row-WLOG dual.
- **`hRValue`** — R1's resolution core-value `rlctAtOn (dlnLoss M 0) 0 = ofReal(lambdaCore M)`
  (R1's lane, in flight).
- **`hGne`** — the reduced-core germ-nonvanishing. **DISCHARGED here** from `hpos`
  (`dlnLoss_deepest_core_ae_ne_zero`, the `DeepestCoreNonvanishing` glue): `r < H s ⟹ 1 ≤ H s − r`.

So the value form below leaves only `hJfront`, `htop`, `hRValue` (+ the `L = 2` tags `hL2`/`hLlt`)
as named-open hypotheses — `hGne` is glued in.

`M = fun s => H s - r` throughout.
-/

open MeasureTheory
open scoped ENNReal Topology

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The L=2-clean gauge chart producer** (taint-kill). Same conclusion as
`deepest_gauge_chart_construct` (`DeepestL2Wiring`), but obtains the chart from the L=2-clean
`deepest_gauge_construction_L2` (threading `hLlt : L < 3`) rather than the general
`deepest_gauge_construction` — so the produced `DeepestGaugeChart` does NOT inherit the general
producer's `L ≥ 3` `sorry` branch. -/
theorem deepest_gauge_chart_construct_L2 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hpos : ∀ s : Fin (L + 1), r < H s)
    (hJfront : ((deepestPoint_frame_pivot_exists H r B hB hr hL hL2).choose).trans
        (finCongr (H_lastLayer_succ H hL)).toEmbedding = frontEmbed H r hr)
    (htop : (B.submatrix (Fin.castLE (hr 0) : Fin r → Fin (H 0))
        (id : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))).rank = r)
    (hLlt : L < 3) :
    Nonempty (DeepestGaugeChart H r B hB hr hL) := by
  obtain ⟨nGauge, split, coreAbsorb, regStraighten, hsplit_mp, hsplit_base, hca_base, hca_reg,
    hca_spec, hca_rlct, hra_cont, hra_base, hra_core, hra_spec, hra_rlct, hsq⟩ :=
    deepest_gauge_construction_L2 H r B hB hr hL hL2 hpos hJfront htop hLlt
  exact ⟨{
    nGauge := nGauge
    split := split
    split_mp := hsplit_mp
    split_basepoint := hsplit_base
    coreAbsorb := coreAbsorb
    coreAbsorb_basepoint := hca_base
    coreAbsorb_regular := hca_reg
    coreAbsorb_spectator := hca_spec
    coreAbsorb_rlct := hca_rlct
    regStraighten := regStraighten
    regStraighten_continuous := hra_cont
    regStraighten_basepoint := hra_base
    regStraighten_core := hra_core
    regStraighten_spectator := hra_spec
    regAbsorb_rlct := hra_rlct
    loss_squeeze := hsq }⟩

/-- **The VALUE-FREE L=2 reduction at front-pivot `B`, taint-clean.** Mirrors
`deepest_regular_core_reduces_frontPivot` (`DeepestNormalFormFrontPivot`) but obtains the chart from
the L=2-clean producer `deepest_gauge_chart_construct_L2`. The local RLCT of `dlnLoss H B` at the
deepest point splits as the regular gauge shift `nReg/2` plus the reduced singular core RLCT
`rlctAtOn (dlnLoss M 0) 0`. The `hGne` precondition is threaded (discharged in the value form). -/
theorem deepest_regular_core_reduces_frontPivot_L2 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hpos : ∀ s : Fin (L + 1), r < H s)
    (hJfront : ((deepestPoint_frame_pivot_exists H r B hB hr hL hL2).choose).trans
        (finCongr (H_lastLayer_succ H hL)).toEmbedding = frontEmbed H r hr)
    (htop : (B.submatrix (Fin.castLE (hr 0) : Fin r → Fin (H 0))
        (id : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))).rank = r)
    (hLlt : L < 3)
    (hGne : ∃ U ∈ 𝓝 (0 : Fin (flatDim (fun s => H s - r)) → ℝ),
      ∀ᵐ z ∂(volume.restrict U),
        dlnLoss (fun s => H s - r)
          (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ)
          ((paramsEquivFlat (fun s => H s - r)).symm z) ≠ 0) :
    rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL)
      = ((r * (H 0 + H (Fin.last L) - r) : ℕ) : ℝ≥0∞) / 2
        + rlctAtOn
            (fun A : Params (fun s => H s - r) =>
              dlnLoss (fun s => H s - r)
                (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ) A)
            (fun _ => 0 : Params (fun s => H s - r)) := by
  obtain ⟨Γ⟩ := deepest_gauge_chart_construct_L2 H r B hB hr hL hL2 hpos hJfront htop hLlt
  rw [deepest_squeeze_transport H r B hB hr hL Γ,
    deepest_regular_smooth_split H r B hB hr hL Γ hGne]

/-- **The L=2 normal form (the `#44`-at-L=2 standalone value lemma), taint-clean.** The `L = 2`
instance of the Skeleton's `deepest_regular_core_normal_form` (`#44`): the local RLCT of
`dlnLoss H B` at the deepest point equals the closed form `nReg/2 + ofReal(lambdaCore M)`, with
`nReg = r(H⁰+Hᴸ−r)` and `M = H − r`.

This is the EXACT `deepest_regular_core_normal_form` conclusion at `L = 2`, CONDITIONAL on the three
named-open hypotheses `hJfront` (the front-pivot frame alignment — OPEN, GATE-0), `htop` (the
row-alignment — OPEN), and `hRValue` (R1's core-value — in flight). `hGne` is DISCHARGED internally
from `hpos` via `dlnLoss_deepest_core_ae_ne_zero` (`r < H s ⟹ 1 ≤ H s − r`).

Proof: `deepest_regular_core_reduces_frontPivot_L2` (value-free, L=2-clean) `▸` `hRValue`. -/
theorem deepest_regular_core_normal_form_L2 (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hpos : ∀ s : Fin (L + 1), r < H s)
    (hJfront : ((deepestPoint_frame_pivot_exists H r B hB hr hL hL2).choose).trans
        (finCongr (H_lastLayer_succ H hL)).toEmbedding = frontEmbed H r hr)
    (htop : (B.submatrix (Fin.castLE (hr 0) : Fin r → Fin (H 0))
        (id : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))).rank = r)
    (hLlt : L < 3)
    (hRValue :
      rlctAtOn
          (fun A : Params (fun s => H s - r) =>
            dlnLoss (fun s => H s - r)
              (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ) A)
          (fun _ => 0 : Params (fun s => H s - r))
        = ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ)) :
    rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL)
      = ((r * (H 0 + H (Fin.last L) - r) : ℕ) : ℝ≥0∞) / 2
        + ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ) := by
  -- `hGne` from `hpos` (`r < H s ⟹ 1 ≤ M s = H s − r`), via the `DeepestCoreNonvanishing` glue.
  have hGne := dlnLoss_deepest_core_ae_ne_zero (fun s => H s - r)
    (fun s => Nat.sub_pos_of_lt (hpos s))
  rw [deepest_regular_core_reduces_frontPivot_L2 H r B hB hr hL hL2 hpos hJfront htop hLlt hGne,
    hRValue]

end DLNFibre.DLN.RLCT
