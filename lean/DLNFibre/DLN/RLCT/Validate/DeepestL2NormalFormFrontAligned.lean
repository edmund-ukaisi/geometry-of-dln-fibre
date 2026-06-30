import DLNFibre.DLN.RLCT.Validate.DeepestL2Wiring
import DLNFibre.DLN.RLCT.Validate.DeepestCoreNonvanishing

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestL2NormalFormFrontAligned` — #44 at L=2 for FRONT-ALIGNED `B`

The L=2 deepest-point RLCT normal form (`deepest_regular_core_normal_form`, Skeleton #44) closed for
a **front-aligned** target `B` — one whose rank-`r` pivot columns are the first `r` (`hJfront`) and
whose top `r` rows have full rank (`htop`) — modulo the single R1 core-value hypothesis `hcore`.

**Why front-aligned, not arbitrary `B` (the verify-first gate firing, genm-p44wire).** The Skeleton
#44 statement is per-`B` POINTWISE at `deepestPoint H r B`, an arbitrary `Classical.choice`
deepest-layers witness. The banked gauge chart (`deepest_gauge_chart_construct`) PROVES the normal
form, but only when `B` is front-aligned. Transferring to an ARBITRARY `B` via the `B·Π`
permutation-WLOG (`τ` the induced param-space homeomorphism) gives
`rlctAt (dlnLoss Bpr) (τ (deepestPoint B)) = rlctAt (dlnLoss B) (deepestPoint B)` — but
`τ (deepestPoint B)` is NOT the arbitrary `deepestPoint Bpr` the chart computes at, so stitching the
two needs **local-RLCT constancy across the deepest gauge orbit** (a `GL` gauge-orbit invariance of
the LOCAL RLCT) — NEW MATH, not in the banked transfer machinery (decorrelated Codex adjudication,
`threads/44-p44wire/codex/p44-route-answer.md`, xhigh). So the honest wiring-bounded deliverable
keeps `B` front-aligned (hJfront/htop as HYPOTHESES); the permutation-WLOG is applied by the
DOWNSTREAM consumer at the infimum (`⨅ optimalSet`) level, where the `Set.BijOn.iInf_congr`
point-matching
(`rlct_infimum_{row,col}Perm_eq`) handles the gauge orbit globally — no single-point orbit
invariance needed.

**What this file delivers.** `deepest_regular_core_normal_form_frontAligned`: at `L = 2`, given the
front alignment (`hJfront`, `htop`), the strict reduced-width positivity (`hpos`), and the R1
core-value (`hcore`, an explicit hypothesis — R1's lane), `deepest_regular_core_normal_form`'s
conclusion holds. The germ-nonvanishing `hGne` is discharged INTERNALLY from
`dlnLoss_deepest_core_ae_ne_zero` (banked) via `hpos`. The proof obtains the gauge chart from the
L=2-specific `deepest_gauge_chart_construct_L2` (this file), which destructures the clean-three
`deepest_gauge_construction_L2` — NOT the general `deepest_gauge_chart_construct`, whose term
carries
the L≥3 `#120` interior/grouped-diffeo `sorry`s and so is NOT axiom-clean even at `L = 2` (a
verify-first finding, genm-p44wire: `#print axioms` exposed the persisted `sorryAx` the green build
masked). It then replicates the value-free reduction (`deepest_squeeze_transport` ▸
`deepest_regular_smooth_split`) ▸ `hcore`.

All three lemmas are axiom-clean `[propext, Classical.choice, Quot.sound]` (with `hcore` a
hypothesis). So the ONLY remaining gap is `hcore` (the R1 core-value).
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators Topology

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **hGne for the reduced widths from strict positivity.** When every `r < H s`, the reduced core
`dlnLoss (H−r) 0` is `≠ 0` a.e. near the flat origin (the germ-nonvanishing `hGne`). Banked
`dlnLoss_deepest_core_ae_ne_zero` at `M = fun s => H s - r`, whose `∀ s, 1 ≤ M s` precondition is
`r < H s ⟹ 1 ≤ H s - r`. -/
theorem deepest_reduced_core_ae_ne_zero_of_pos (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hpos : ∀ s : Fin (L + 1), r < H s) :
    ∃ U ∈ 𝓝 (0 : Fin (flatDim (fun s => H s - r)) → ℝ),
      ∀ᵐ z ∂(volume.restrict U),
        dlnLoss (fun s => H s - r)
          (0 : Matrix (Fin ((fun s => H s - r) 0)) (Fin ((fun s => H s - r) (Fin.last L))) ℝ)
          ((paramsEquivFlat (fun s => H s - r)).symm z) ≠ 0 :=
  dlnLoss_deepest_core_ae_ne_zero (fun s => H s - r) (fun s => Nat.sub_pos_of_lt (hpos s))

/-- **The `DeepestGaugeChart` instance at `L = 2`, clean-three.** Destructures the L=2 construction
`deepest_gauge_construction_L2` (clean `[propext, Classical.choice, Quot.sound]`) into the chart
structure. Differs from the general `deepest_gauge_chart_construct` (which routes through the
general `deepest_gauge_construction` and so carries the L≥3 `#120` interior/grouped-diffeo `sorry`s
in its term, NOT axiom-clean even at L=2) by taking `hLlt : L < 3` and consuming the hoisted clean
L=2 arm. -/
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

/-- **#44 at L=2 for a front-aligned `B`, modulo the R1 core-value `hcore`.** At `L = 2`, for a
rank-`r` target `B` whose pivot columns are at the front (`hJfront`) and whose top `r` rows are
full rank (`htop`), with strict reduced-width positivity (`hpos`), the local RLCT of `dlnLoss H B`
at the deepest point is the regular shift `nReg/2` plus the closed-form core `ofReal (lambdaCore M)`
— the exact `deepest_regular_core_normal_form` conclusion — GIVEN the R1 core-value `hcore`. The
germ-nonvanishing `hGne` is discharged from `hpos`; the gauge chart is built clean via the
L=2-specific `deepest_gauge_chart_construct_L2` (the clean-three L=2 arm — NOT the general
`deepest_gauge_chart_construct`, whose term carries the L≥3 `#120` `sorry`s), so the ONLY remaining
gap is `hcore` (R1's lane). Axiom-clean `[propext, Classical.choice, Quot.sound]` with `hcore` a
hyp. -/
theorem deepest_regular_core_normal_form_frontAligned (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L) (hLlt : L < 3)
    (hpos : ∀ s : Fin (L + 1), r < H s)
    (hJfront : ((deepestPoint_frame_pivot_exists H r B hB hr hL hL2).choose).trans
        (finCongr (H_lastLayer_succ H hL)).toEmbedding = frontEmbed H r hr)
    (htop : (B.submatrix (Fin.castLE (hr 0) : Fin r → Fin (H 0))
        (id : Fin (H (Fin.last L)) → Fin (H (Fin.last L)))).rank = r)
    (hcore : rlctAtOn
        (fun A : Params (fun s => H s - r) =>
          dlnLoss (fun s => H s - r)
            (0 : Matrix (Fin ((fun s => H s - r) 0))
              (Fin ((fun s => H s - r) (Fin.last L))) ℝ) A)
        (fun _ => 0 : Params (fun s => H s - r))
      = ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ)) :
    rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL)
      = ((r * (H 0 + H (Fin.last L) - r) : ℕ) : ℝ≥0∞) / 2
        + ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ) := by
  -- hGne from hpos (banked).
  have hGne := deepest_reduced_core_ae_ne_zero_of_pos H r hpos
  -- Build the gauge chart CLEAN at L=2 (the hoisted clean-three arm — NOT the general construct,
  -- whose term carries the L≥3 #120 sorries, nor the bare `deepest_gauge_squeeze_exists` stub).
  obtain ⟨Γ⟩ := deepest_gauge_chart_construct_L2 H r B hB hr hL hL2 hpos hJfront htop hLlt
  -- Replicate the value-free reduction (cf. `deepest_regular_core_reduces`), then `hcore`.
  rw [deepest_squeeze_transport H r B hB hr hL Γ,
    deepest_regular_smooth_split H r B hB hr hL Γ hGne, hcore]

end DLNFibre.DLN.RLCT
