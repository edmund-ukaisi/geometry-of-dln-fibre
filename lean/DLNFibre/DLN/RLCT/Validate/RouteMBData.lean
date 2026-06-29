import DLNFibre.DLN.RLCT.Validate.RouteMBInterface

/-!
# `RouteMBData` — the radial-scaling core of the B-interface map identity (the `hmap` algebra)

The genuinely-reachable, network-free core of `BData.hmap` (`phiFlatLiveR1 = B ∘ pivotBlowupOn`):
the radial scalar `u` of the achiever chart `phiGen u M t B hle` can be ABSORBED into the block
data, because `phiGen` reads `u` and `B` ONLY through `Cgen u M t B hle = Bmat·chainQ(N) + u•Rmat`
(interior) / `u•Rfin` (leaf) — the `u` multiplies ONLY the residual blocks `Rmat`/`Rfin`. So scaling
those two fields by `u` (keeping `Bmat`/`Nblk`/`Wblk`) and setting the radial to `1` reproduces the
SAME chart:

  `phiGen u M t B hle = phiGen 1 M t (smulRmatRfin u B) hle`.

This is the cast-LIGHT algebraic identity (pure `GenBlk`/`Cgen`/`Agen` matrix algebra, NO
`chartIdxEquiv` slot surgery). It is the lever Codex's gate verdict (`codex/bdata-gate-answer.md`,
V-CONSTRUCTIBLE-HARD) flagged: define the boundary factor with the radial set to `1` reading the
already-scaled residual coordinates; the radial degree comes entirely from `pivotBlowupOn`, not from
`B`.

It does NOT route through the Codex-REFUTED `composeFold fs = φ` disjoint-factor fold (genm-mapeq
@d7e75c8d): the radial is factored out as the genuine `pivotBlowupOn` map, and `B` here is the
radial-`1` chart itself — an arbitrary map, NOT a disjoint fold (so the chain-coupling unsoundness
that killed F1 does not apply; see `codex/bdata-gate-answer.md` Q2).

* `smulRmatRfin` — scale a `GenBlk`'s residual blocks `Rmat`/`Rfin` by a scalar (the
  radial-absorbing reblocking), keeping `Bmat`/`Nblk`/`Wblk`.
* `Cgen_smulRmatRfin` — `Cgen 1 (smulRmatRfin u B) = Cgen u B` (the per-boundary residual identity).
* `Agen_smulRmatRfin` / `chartParamsGen_smulRmatRfin` — the layer / chart-parameter consequences.
* `phiGen_smul_radial` — `phiGen u M t B hle = phiGen 1 M t (smulRmatRfin u B) hle` (chart id).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (pure matrix algebra; no analysis).
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped BigOperators

variable {L : ℕ}
variable {𝕜 : Type} [CommRing 𝕜]

/-- **The radial-absorbing reblocking.** Scale a `GenBlk`'s residual blocks `Rmat`/`Rfin` by `u`,
keeping the kept/residual/lift blocks `Bmat`/`Nblk`/`Wblk` unchanged. Then
`Cgen 1 (smulRmatRfin u B) = Cgen u B`: the radial `u` is absorbed into the residual coordinates. -/
noncomputable def smulRmatRfin (u : 𝕜) (M t : Fin (L + 1) → ℕ) (B : GenBlk M t 𝕜) :
    GenBlk M t 𝕜 where
  Bmat := B.Bmat
  Nblk := B.Nblk
  Wblk := B.Wblk
  Rmat := fun k => u • B.Rmat k
  Rfin := fun k => u • B.Rfin k

/-- **The per-boundary residual identity** `Cgen 1 (smulRmatRfin u B) = Cgen u B` (every `k`).
Interior: `Bmat·chainQ(N) + 1•(u•Rmat) = Bmat·chainQ(N) + u•Rmat`; leaf: `1•(u•Rfin) = u•Rfin`. The
`Bmat`/`Nblk` blocks are shared (`smulRmatRfin` keeps them), so the `chainQ` part is untouched. -/
theorem Cgen_smulRmatRfin (u : 𝕜) (M t : Fin (L + 1) → ℕ) (B : GenBlk M t 𝕜)
    (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k) (k : ℕ) :
    Cgen 1 M t (smulRmatRfin u M t B) hle k = Cgen u M t B hle k := by
  unfold Cgen smulRmatRfin
  by_cases hk : k < L
  · rw [dif_pos hk, dif_pos hk, one_smul]
  · rw [dif_neg hk, dif_neg hk, one_smul]

/-- **The per-layer identity** `Agen 1 (smulRmatRfin u B) = Agen u B` (every `k`). `Agen u B k =
chainA(N_k, W_k, Cgen u B (k+1))`; the `N_k`/`W_k` blocks are shared (`smulRmatRfin` keeps
`Nblk`/`Wblk`) and the accumulator `Cgen (k+1)` is matched by `Cgen_smulRmatRfin`. -/
theorem Agen_smulRmatRfin (u : 𝕜) (M t : Fin (L + 1) → ℕ) (B : GenBlk M t 𝕜)
    (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k) (k : ℕ) :
    Agen 1 M t (smulRmatRfin u M t B) hle k = Agen u M t B hle k := by
  unfold Agen
  by_cases hk : k < L
  · rw [dif_pos hk, dif_pos hk]
    show chainA _ ((smulRmatRfin u M t B).Nblk k) ((smulRmatRfin u M t B).Wblk k) _ = _
    rw [Cgen_smulRmatRfin u M t B hle (k + 1)]
    rfl
  · rw [dif_neg hk, dif_neg hk]

/-- **The chart-parameter identity** `chartParamsGen 1 (smulRmatRfin u B) = chartParamsGen u B`.
`chartParamsGen` is the width-reindex of the chain layer `chainOfMt.toChain.A = Agen`, matched
boundary-wise by `Agen_smulRmatRfin`. -/
theorem chartParamsGen_smulRmatRfin (u : ℝ) (M t : Fin (L + 1) → ℕ) (B : GenBlk M t)
    (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k) :
    chartParamsGen 1 M t (smulRmatRfin u M t B) hle = chartParamsGen u M t B hle := by
  funext s
  unfold chartParamsGen
  congr 1
  exact Agen_smulRmatRfin u M t B hle s.val

/-- **The radial-scaling chart identity** `phiGen u M t B hle = phiGen 1 M t (smulRmatRfin u B)`.
The radial scalar `u` of the achiever chart is absorbed into the residual blocks: `phiGen` reads `u`
only through `Cgen`, which `smulRmatRfin` reproduces at radial `1`. The load-bearing algebra of the
B-interface map identity (the radial degree then comes from `pivotBlowupOn`, not from `B`). -/
theorem phiGen_smul_radial (u : ℝ) (M t : Fin (L + 1) → ℕ) (B : GenBlk M t)
    (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k) :
    phiGen u M t B hle = phiGen 1 M t (smulRmatRfin u M t B) hle := by
  unfold phiGen
  rw [chartParamsGen_smulRmatRfin u M t B hle]

/-- **Non-vacuity**: at radial `u = 1` the reblocking is invisible (`smulRmatRfin 1 B` has the same
`Cgen` as `B`), so `phiGen 1 B = phiGen 1 (smulRmatRfin 1 B)` — the identity is consistent, and at a
genuine radial it relocates the scalar into the residual blocks. -/
example (M t : Fin (L + 1) → ℕ) (B : GenBlk M t)
    (hle : ∀ k, k < L → Text M t (k + 1) ≤ Wext M k) :
    phiGen 1 M t B hle = phiGen 1 M t (smulRmatRfin 1 M t B) hle :=
  phiGen_smul_radial 1 M t B hle

/-! ## The `φ = B ∘ pivotBlowupOn` reduction (the map-identity half, modulo the slot-identification)

⚠ **SUPERSEDED by `phiFlatLiveR1_eq_B_comp_pivotBlowupOn_chart` below (the Fix-B CHART contract).**
The `hslot` hypothesis below is FALSE for `genBlkFlatLiveR1` — REFUTED
sorry-free in `RouteMSlotId.not_hslot_genBlkFlatLiveR1` (triple-confirmed: hand + Codex + sympy
`route-i-l2/fixed_pivot_refutation.py`). `phiFlatLiveR1` uses the GAUGE-FIXED pivot decoder
`genBlkFlatLiveR1`: its pivot `Rmat p = rmatPad (pivotEIndicator p)` is the LITERAL `1` (not a free
`readE`). So `smulRmatRfin (x p₀)` scales it to entry `x p₀`, while the RHS keeps the SAME constant
`pivotEIndicator` (entry `1`) — `hslot` forces `x p₀ = 1`, false for general `x`.

DEEPER: `φ = B ∘ pivotBlowupOn` ITSELF fails for the fixed pivot — the pivot E-block carries the
ADDITIVE radial `u·1 = u`, which the MULTIPLICATIVE `pivotBlowupOn` (blowing up OTHER active coords)
cannot reproduce; `B` (radial-`1`) loses that `u`. The route-(i) decoder choice is UNSETTLED
(controller-level: the fixed pivot is the `minAdm−1` count gauge per the `RouteMFlatLive` header;
re-targeting at the live-pivot `phiFlatLive` reshapes the det/count). It stays a VALID CONDITIONAL
(the `phiGen_smul_radial` reduction is sound + reusable) but is OFF the build path until resettled.

The radial split `φ = B ∘ pivotBlowupOn active p₀`: `B` the radial-`1` boundary chart
`B y := phiGen 1 M t (genBlkFlatLiveR1 … (rfin y) y) hle`. Holds iff the `GenBlk`-level
SLOT-IDENTIFICATION `smulRmatRfin (x p₀) (B₀ x) = B₀ (pivotBlowupOn active p₀ x)` (`hslot`) — FALSE
(above). Via `phiGen_smul_radial` + `hslot`. -/
theorem phiFlatLiveR1_eq_B_comp_pivotBlowupOn (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (hN : 0 < routeMAmbient M) (p : ℕ)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (rfin : (Fin (routeMAmbient M) → ℝ) → Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (active : Finset (Fin (routeMAmbient M)))
    (hslot : ∀ x : Fin (routeMAmbient M) → ℝ,
      smulRmatRfin (x (structPivot M hN)) M t (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x)
        = genBlkFlatLiveR1 M t ha p hp1 hp2
            (rfin (pivotBlowupOn active (structPivot M hN) x))
            (pivotBlowupOn active (structPivot M hN) x)) :
    phiFlatLiveR1 M t ha hN p hp1 hp2 rfin
      = (fun y => phiGen 1 M t (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin y) y) (hleStruct M t ha))
        ∘ pivotBlowupOn active (structPivot M hN) := by
  funext x
  show phiGen (x (structPivot M hN)) M t (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x)
      (hleStruct M t ha) = _
  rw [phiGen_smul_radial (x (structPivot M hN)) M t
    (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x) (hleStruct M t ha), hslot x]
  rfl

/-! ## The Fix-B `φ = B ∘ pivotBlowupOn` reduction — CHART-level (not the false GenBlk `hslot`)

⚠ **`hchart` is UNDISCHARGEABLE for `B := phiGen 1 (genBlkFlatLiveR1 …)`** (verify-first, sympy
`route-i-l2/actual_B_check.py` + `agen_layer_check.py`): `genBlkFlatLiveR1`'s pivot `Rmat p` is the
FIXED `pivotEIndicator` — a CONSTANT (literal 1), x-free. So `phiGen 1 (genBlkFlatLiveR1 …(pbo x))`
reads `E(0,0)` as the constant `1`, NOT additively from the pivot coord — `φ = B ∘ pbo` FAILS at the
anchor (`φ_E00 = … + x_p` vs `B(pbo)_E00 = … + 1`). Equivalently the per-layer `chartParamsGen`
(`hcp` in `hchart_of_chartParamsGen`) is FALSE at the anchor (`x_p` vs `1`). The genm-detradj Fix-B
contract's `B` ("de-radialized chart reading `E(0,0)` ADDITIVELY from the pivot") is NOT
`phiGen 1 (genBlkFlatLiveR1 …)` — they DIFFER at the fixed pivot. My earlier
`fixb_corrected_contract_verify.py` used a HAND-MODELED additive-`B`, not the concrete decoder — a
conflation, caught before building the per-layer proof. Fix B as instantiated below (with `B` the
radial-1 `genBlkFlatLiveR1` chart) is OFF the build path; the contract needs a `B` whose pivot-E00
is an ADDITIVE pivot-coord read — genm-detradj's residual.

The reduction stays a VALID CONDITIONAL (on the CHART-level `hchart`); `phiGen_smul_radial` +
`hchart_of_chartParamsGen` are sound + reusable. But `hchart` for this `B` is the (false-here)
per-boundary additive/multiplicative `Agen`-split — the open piece, not dischargeable here. -/
theorem phiFlatLiveR1_eq_B_comp_pivotBlowupOn_chart (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (hN : 0 < routeMAmbient M) (p : ℕ)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (rfin : (Fin (routeMAmbient M) → ℝ) → Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (active : Finset (Fin (routeMAmbient M)))
    (hchart : ∀ x : Fin (routeMAmbient M) → ℝ,
      phiGen 1 M t (smulRmatRfin (x (structPivot M hN)) M t
          (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x)) (hleStruct M t ha)
        = phiGen 1 M t (genBlkFlatLiveR1 M t ha p hp1 hp2
            (rfin (pivotBlowupOn active (structPivot M hN) x))
            (pivotBlowupOn active (structPivot M hN) x)) (hleStruct M t ha)) :
    phiFlatLiveR1 M t ha hN p hp1 hp2 rfin
      = (fun y => phiGen 1 M t (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin y) y) (hleStruct M t ha))
        ∘ pivotBlowupOn active (structPivot M hN) := by
  funext x
  show phiGen (x (structPivot M hN)) M t (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x)
      (hleStruct M t ha) = _
  rw [phiGen_smul_radial (x (structPivot M hN)) M t
    (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x) (hleStruct M t ha), hchart x]
  rfl

/-! ## `hchart` from the per-layer `Agen` equality (the genuine map-identity content)

`hchart` (the CHART-level `phiGen 1 (smulRmatRfin (x_p) GBx) = phiGen 1 (GB(pbo x))`) reduces — via
`phiGen = paramsEquivFlat ∘ chartParamsGen` + the banked `chartParamsGen_smulRmatRfin`
(`chartParamsGen 1 (smulRmatRfin u B) = chartParamsGen u B`) — to the `chartParamsGen` equality
`chartParamsGen (x_p) GBx = chartParamsGen 1 (GB(pbo x))`, i.e. PER-LAYER (`reindex` injective)
`Agen (x_p) GBx s = Agen 1 (GB(pbo x)) s`. The per-layer split (K/X/N/W non-active ⟹ unchanged under
`pbo`; free E/leaf active ⟹ scaled by `x_p` (matches `Agen (x_p)`); fixed E00 the additive-anchor)
is the genuine content (genm-detradj's ∀M residual; exact at L=2 single bdy). This lemma BANKS the
clean structural reduction `hchart ⟸ the chartParamsGen equality`, isolating that content. -/
theorem hchart_of_chartParamsGen (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (hN : 0 < routeMAmbient M) (p : ℕ)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (rfin : (Fin (routeMAmbient M) → ℝ) → Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (active : Finset (Fin (routeMAmbient M))) (x : Fin (routeMAmbient M) → ℝ)
    (hcp : chartParamsGen (x (structPivot M hN)) M t
        (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x) (hleStruct M t ha)
      = chartParamsGen 1 M t
        (genBlkFlatLiveR1 M t ha p hp1 hp2
          (rfin (pivotBlowupOn active (structPivot M hN) x))
          (pivotBlowupOn active (structPivot M hN) x)) (hleStruct M t ha)) :
    phiGen 1 M t (smulRmatRfin (x (structPivot M hN)) M t
        (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x)) (hleStruct M t ha)
      = phiGen 1 M t (genBlkFlatLiveR1 M t ha p hp1 hp2
          (rfin (pivotBlowupOn active (structPivot M hN) x))
          (pivotBlowupOn active (structPivot M hN) x)) (hleStruct M t ha) := by
  unfold phiGen
  rw [chartParamsGen_smulRmatRfin (x (structPivot M hN)) M t
    (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x) (hleStruct M t ha), hcp]

end DLNFibre.DLN.RLCT
