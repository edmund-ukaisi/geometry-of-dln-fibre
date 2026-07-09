import DLNFibre.DLN.RLCT.Validate.DeepestFrontGauge
import DLNFibre.DLN.RLCT.Validate.DeepestL2Wiring
import DLNFibre.DLN.RLCT.Validate.DeepestNormalFormFrontPivot

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestFrontGaugeGen` — general-`L` FRONT gauge chain (hJfront-free)

The general-`L` (`L ≥ 3` included) parallel of the L = 2 front chain (`DeepestFrontGauge`,
`DeepestNormalFormFrontPivot`). Everything here is conditional on the PROVABLE column-WLOG precursor
`hcolfront` (`B`'s front `r` columns full rank) + the row-WLOG `htop`, and NEVER on the unprovable
`.choose`-based `hJfront`.

The general gauge construction `deepest_gauge_construction_front` dispatches: `L < 3` → the hoisted
`deepest_gauge_construction_L2_front`; `L ≥ 3` → the FRONT block-triangular boundary-frame bundle
(`deepestPoint_frame_pivot_triangular_front_exists`, `J = frontEmbed` by construction from `hcolfront`,
now carrying `hInterior`) fed to the frame-generic `deepest_gauge_construction_ofBundle`. So the SAME
`_ofBundle` core serves both the arbitrary route (via `deepest_gauge_construction`, threading the
`.choose`-based `hJfront`) and this hJfront-free front route.

Downstream, mirroring `DeepestNormalFormFrontPivot` but hcolfront-based:

- `deepest_gauge_chart_construct_front` — the `DeepestGaugeChart` at a column-aligned `B`.
- `deepest_regular_core_reduces_frontPivot_front` — the VALUE-FREE reduction
  (`rlctAt(deepestPoint) = nReg/2 + rlctAtOn(dlnLoss M 0) 0`), the axiom-GATE lemma.
- `deepest_regular_core_normal_form_gen_front` — the #44 normal form (`hGne` discharged internally from
  `hpos`; consumes R1's `hRValue`), the headline value feeder.
- `aoyagi_learning_coefficient_frontPivot_front` — the headline at a front-pivot `B` (consumes the D1
  `≥`-leg `hD1`). The general-`B` headline follows by the ⨅-level column/row-perm WLOG (Step 3).
-/

open MeasureTheory
open scoped ENNReal Topology

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The general-`L` gauge construction at a column-aligned `B`** (front, hJfront-free). `L < 3`
dispatches to `deepest_gauge_construction_L2_front`; `L ≥ 3` obtains the FRONT block-triangular bundle
(`deepestPoint_frame_pivot_triangular_front_exists`, from `htop` + `hcolfront`, `J = frontEmbed` by
construction) and feeds the frame-generic `deepest_gauge_construction_ofBundle`. Same existential
conclusion as `deepest_gauge_construction`, but with `hJfront` REPLACED by the provable `hcolfront`. -/
theorem deepest_gauge_construction_front (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hpos : ∀ s : Fin (L + 1), r < H s)
    (htop : (B.submatrix (Fin.castLE (hr 0) : Fin r → Fin (H 0))
        (id : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))).rank = r)
    (hcolfront : (B.submatrix (id : Fin (H 0) → Fin (H 0))
        (Fin.castLE (hr (Fin.last L)) : Fin r → Fin (H (Fin.last L)))).rank = r) :
    ∃ (nGauge : ℕ) (split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r nGauge)
      (coreAbsorb : DeepestSplit H r nGauge ≃ₜ DeepestSplit H r nGauge)
      (regStraighten : DeepestSplit H r nGauge → DeepestSplit H r nGauge),
      MeasurePreserving split volume volume ∧
      split ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) = 0 ∧
      coreAbsorb 0 = 0 ∧
      (∀ q : DeepestSplit H r nGauge, (coreAbsorb q).1 = q.1) ∧
      (∀ q : DeepestSplit H r nGauge, (coreAbsorb q).2.2 = q.2.2) ∧
      rlctAtOn
          (fun q : DeepestSplit H r nGauge => (∑ i, q.1 i ^ 2) + deepestCoreF H r (coreAbsorb q).2.1)
          (0 : DeepestSplit H r nGauge)
        = rlctAtOn
            (fun q : DeepestSplit H r nGauge => (∑ i, q.1 i ^ 2) + deepestCoreF H r q.2.1)
            (0 : DeepestSplit H r nGauge) ∧
      Continuous regStraighten ∧
      regStraighten 0 = 0 ∧
      (∀ q : DeepestSplit H r nGauge, (regStraighten q).2.1 = q.2.1) ∧
      (∀ q : DeepestSplit H r nGauge, (regStraighten q).2.2 = q.2.2) ∧
      rlctAtOn
          (fun q : DeepestSplit H r nGauge =>
            (∑ i, (regStraighten q).1 i ^ 2) + deepestCoreF H r (coreAbsorb q).2.1)
          (0 : DeepestSplit H r nGauge)
        = rlctAtOn
            (fun q : DeepestSplit H r nGauge =>
              (∑ i, q.1 i ^ 2) + deepestCoreF H r (coreAbsorb q).2.1)
            (0 : DeepestSplit H r nGauge) ∧
      rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL)
        = rlctAtOn
            (fun x : Fin (flatDim H) → ℝ =>
              (∑ i, (regStraighten (split x)).1 i ^ 2)
                + deepestCoreF H r (coreAbsorb (split x)).2.1)
            ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) := by
  rcases Nat.lt_or_ge L 3 with hLlt | hL3
  · exact deepest_gauge_construction_L2_front H r B hB hr hL hL2 hpos htop hcolfront hLlt
  · obtain ⟨Jb, Pf, Qf, hJtri, hPunit, hQunit, hQf0, hPfL, hNF, hQf22b, hcorner, hPtri, hQtri,
        hP22one, hQ22one, hInterior⟩ :=
      deepestPoint_frame_pivot_triangular_front_exists H r B hB hr hL hL2 htop hcolfront
    exact deepest_gauge_construction_ofBundle H r B hB hr hL hL2 hpos htop
      Jb Pf Qf hJtri hPunit hQunit hQf0 hPfL hNF hQf22b hcorner hPtri hQtri hP22one hQ22one
      hInterior

/-- **The general-`L` gauge chart at a column-aligned `B`** (front, taint-clean). Destructures
`deepest_gauge_construction_front` into the `DeepestGaugeChart` structure — the general (`hLlt`-free)
`hcolfront`-conditional analog of `deepest_gauge_chart_construct_L2_front`. -/
theorem deepest_gauge_chart_construct_front (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hpos : ∀ s : Fin (L + 1), r < H s)
    (htop : (B.submatrix (Fin.castLE (hr 0) : Fin r → Fin (H 0))
        (id : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))).rank = r)
    (hcolfront : (B.submatrix (id : Fin (H 0) → Fin (H 0))
        (Fin.castLE (hr (Fin.last L)) : Fin r → Fin (H (Fin.last L)))).rank = r) :
    Nonempty (DeepestGaugeChart H r B hB hr hL) := by
  obtain ⟨nGauge, split, coreAbsorb, regStraighten, hsplit_mp, hsplit_base, hca_base, hca_reg,
    hca_spec, hca_rlct, hra_cont, hra_base, hra_core, hra_spec, hra_rlct, hsq⟩ :=
    deepest_gauge_construction_front H r B hB hr hL hL2 hpos htop hcolfront
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

/-- **The VALUE-FREE general-`L` reduction at front-pivot `B`** (hJfront-free, the axiom-GATE lemma).
Mirrors `deepest_regular_core_reduces_frontPivot` but obtains the chart from the general
`deepest_gauge_chart_construct_front` (`hcolfront`-based, no `hJfront`). The local RLCT of `dlnLoss H B`
at the deepest point splits as the regular gauge shift `nReg/2` plus the reduced singular core RLCT
`rlctAtOn (dlnLoss M 0) 0`, `M = H − r`. -/
theorem deepest_regular_core_reduces_frontPivot_front (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hpos : ∀ s : Fin (L + 1), r < H s)
    (htop : (B.submatrix (Fin.castLE (hr 0) : Fin r → Fin (H 0))
        (id : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))).rank = r)
    (hcolfront : (B.submatrix (id : Fin (H 0) → Fin (H 0))
        (Fin.castLE (hr (Fin.last L)) : Fin r → Fin (H (Fin.last L)))).rank = r)
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
  obtain ⟨Γ⟩ := deepest_gauge_chart_construct_front H r B hB hr hL hL2 hpos htop hcolfront
  rw [deepest_squeeze_transport H r B hB hr hL Γ,
    deepest_regular_smooth_split H r B hB hr hL Γ hGne]

/-- **The #44 normal form at front-pivot `B`, general `L`** (hJfront-free). Mirrors
`deepest_regular_core_normal_form_L2_front` at general `L`: discharges `hGne` internally from `hpos`
(via `dlnLoss_deepest_core_ae_ne_zero`), consumes R1's resolution value `hRValue`, and returns the
closed form `nReg/2 + ofReal(lambdaCore M)`. The headline value feeder. -/
theorem deepest_regular_core_normal_form_gen_front (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hpos : ∀ s : Fin (L + 1), r < H s)
    (htop : (B.submatrix (Fin.castLE (hr 0) : Fin r → Fin (H 0))
        (id : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))).rank = r)
    (hcolfront : (B.submatrix (id : Fin (H 0) → Fin (H 0))
        (Fin.castLE (hr (Fin.last L)) : Fin r → Fin (H (Fin.last L)))).rank = r)
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
  have hGne := dlnLoss_deepest_core_ae_ne_zero (fun s => H s - r)
    (fun s => Nat.sub_pos_of_lt (hpos s))
  rw [deepest_regular_core_reduces_frontPivot_front H r B hB hr hL hL2 hpos htop hcolfront hGne,
    hRValue]

/-- **The headline learning coefficient at a front-pivot `B`, general `L`** (hJfront-free). Consumes
the D1 `≥`-leg `hD1` (`⨅ = rlctAt deepestPoint`) + R1's `hRValue`; via the front normal form
(`deepest_regular_core_normal_form_gen_front`) ▸ the arithmetic recombination
(`reg_shift_add_core_eq_aoyagiLambda`), the ⨅ over the optimal set equals Aoyagi's closed form. The
general-`B` headline follows by the ⨅-level column/row-perm WLOG (Step 3, `HeadlineGenAssembly`). -/
theorem aoyagi_learning_coefficient_frontPivot_front (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L)
    (hpos : ∀ s : Fin (L + 1), r < H s)
    (htop : (B.submatrix (Fin.castLE (hr 0) : Fin r → Fin (H 0))
        (id : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))).rank = r)
    (hcolfront : (B.submatrix (id : Fin (H 0) → Fin (H 0))
        (Fin.castLE (hr (Fin.last L)) : Fin r → Fin (H (Fin.last L)))).rank = r)
    (hRValue :
      rlctAtOn
          (fun A : Params (fun s => H s - r) =>
            dlnLoss (fun s => H s - r)
              (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ) A)
          (fun _ => 0 : Params (fun s => H s - r))
        = ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ))
    (hD1 : (⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w)
        = rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL)) :
    (⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w) = ENNReal.ofReal (aoyagiLambda H r) := by
  rw [hD1,
    deepest_regular_core_normal_form_gen_front H r B hB hr hL hL2 hpos htop hcolfront hRValue,
    reg_shift_add_core_eq_aoyagiLambda H r hr hL]

end DLNFibre.DLN.RLCT
