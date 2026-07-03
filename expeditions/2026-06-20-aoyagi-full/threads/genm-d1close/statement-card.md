# genm-d1close — b2 (residual-rank identity) + the b1→b2 Jacobian-rank bridge LANDED

LEAF 2 (`HeadlineL2Assembly.lean:107`) is NOT closed and is left correctly-stated (untouched — verified
`git diff origin/genm-d1gates` empty on `HeadlineL2Assembly.lean` and `Skeleton.lean`). This hand banks
the two reachable, load-bearing bricks of the `hrank₂` runway and reports the precise remaining
obstruction. Nothing laundered; no `sorry`/`admit`/`native_decide`/new-axiom added.

## What LANDED (two clean bricks, both sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`)

### b2 — `DLNFibre.Core.residual_finrank_eq` (`lean/DLNFibre/Core/ResidualRank.lean`, network-free)
The abstract residual-rank identity underneath `hrank₂`, previously only numerically certified
(`hrank2_residual_rank_certificate.py`, 0/400 abstract), now PROVEN:

    finrank ℝ (range (zeroSel er ∘ T ∘ P.symm ∘ inj)) = finrank ℝ (range T) − k

for `T : (Fin N → ℝ) →ₗ (Fin m → ℝ)`, injective selectors `er : Fin k → Fin m`, `ec : Fin k → Fin N`,
an invertible `P : (Fin N → ℝ) ≃ₗ (Fin N → ℝ)` whose selected coords read the selected `T`-rows
(`hP : ∀ x j, P x (ec j) = T x (er j)`), a complement injection `inj` onto `W = {z : z (ec j) = 0}`
(`hinjW`), and the minor-driven surjectivity `hsurj : Surjective (selRowProj er ∘ T)`.

Supporting API (same file):
- `finrank_map_ker_comp` — the rank-nullity core: `finrank (map T (ker S)) = rank T − rank S` when
  `ker T ≤ ker S`. (Reusable, generic over any field + finite-dim domain.)
- `residual_range_eq` — `range (composite) = map T (ker (selRowProj er ∘ T))` (`P.symm` carries `W` to
  `ker(πR∘T)`; `zeroSel` is the identity on that kernel).
- `selRowProj` / `zeroSel` / `zeroSel_eq_self_of_sel_zero` / `map_eq_self_of_fixed` — the components.

The clean content (no `P⁻¹` matrix built): the ONLY property of `P` used is the selected-coordinate
relation `hP`. Under it, `P.symm(W) = ker(πR∘T)`; on that kernel the selected rows of `T·` vanish so
`zeroSel = id`; so `range L = T''(ker(πR∘T))` and rank-nullity twice gives `rank T − rank(πR∘T)`; the
minor makes `πR∘T` surjective (`rank = k`).

### b1→b2 bridge — `DLNFibre.DLN.RLCT.jacResid_rank_eq_of_hasFDerivAt`
(`lean/DLNFibre/DLN/RLCT/Validate/D1ResidualJacobianRank.lean`)
Connects a KNOWN residual derivative to the gate's matrix-rank form:

    HasFDerivAt h L t0  ⟹  (jacResid h t0).rank = finrank ℝ (range L).

Because `jacResid h t0 i c = fderiv (h · i) t0 (single c 1) = L (single c 1) i` (component derivative
`= proj i ∘ L`), so `jacResid h t0 = toMatrix' (euclidReadout L)` and its `Matrix.rank = finrank(range
L)` (via `rank_eq_finrank_range_toLin` + the Euclidean ≃ Pi iso preserving `finrank`). Supporting:
`hasFDerivAt_component_of_hasFDerivAt`, `jacResid_apply_of_hasFDerivAt`,
`jacResid_eq_toMatrix'_of_hasFDerivAt`, `euclidReadout` + `finrank_range_euclidReadout`.

## The precise REMAINING obstruction (the honest runway; consistent with genm-d1gates verdict B)

`hrank₂ : extraCountRect (H0−r)(H2−r) a b ≤ (jacResid (q(0,·)) t0).rank` now factors as:

    b1 (produce HasFDerivAt (q(0,·)) L t0, L the b2 composite)
      ▸ bridge (LANDED: (jacResid).rank = finrank(range L))
      ▸ b2 (LANDED: finrank(range L) = finrank(range T) − nReg)
      ▸ b3 (finrank(range T) − nReg = extraCountRect …, the middle-stratum count).

Still OPEN, each genuine new content, none reducible to a banked lemma:

1. **b1 — the derivative-exposing first-peel chart variant.** `dln_hchart_residual_c2` DISCARDS the
   derivative (outputs only the RLCT-transfer measure equation, from which the Jacobian cannot be
   recovered — Codex's load-bearing reason, re-confirmed by reading the module). A variant must:
   (a) re-expose `Ψsymm` + `HasFDerivAt Ψsymm f'.symm 0` (the internal `hsymm_hfderiv` in
   `exists_boundedUnit_chart_of_contDiffAt` at `S1IFTChart.lean:139`, discarded by the `_fix`
   corollary — the return type does not surface `DΨsymm 0 = f'.symm`, so a new producer variant is
   needed); (b) build `HasFDerivAt rawResidVec Tres 0` (the residual-vector differential = the flat
   Jacobian with `er`-rows zeroed; reachable via `hasStrictFDerivAt_lossEntry` +
   `hasFDerivAt_pi`-style assembly, cf. the banked `hasFDerivAt_abChartΦ` pattern in
   `D1SecondPeelChart.lean` — but a genuine ~150–250 LoC build); (c) chain-rule the composite
   `q(0,·) =ᶠ rawResidVec ∘ Ψsymm ∘ splitHomeo.symm ∘ (0,·)` (locality: `q =ᶠ g₁` near `w0`, so
   `fderiv (q(0,·)) t0 = fderiv (g₁(0,·)) t0`); (d) identify the composite's linear map with b2's
   `zeroSel ∘ T ∘ P.symm ∘ inj` where `P = chartFDerivEquiv` (`hP` from `dChartΦcoord_sel`,
   `D1HChartConstruction.lean:107`), `T = jacFlatL2`-as-linear-map, `inj` = the flat-complement
   injection (`splitHomeo.symm ∘ (0,·)`, range `= W`).
2. **b3 — the `(a,b)` extraction + DLN-Jacobian-excess count.** `finrank(range T) − nReg =
   extraCountRect (H0−r)(H2−r) a b`, i.e. `rank Dg(v) = (r+b)H0 + (r+a)H2 − (r+a)(r+b)` at a general
   middle-stratum optimal `v` with layer-rank rises `(a,b)`, plus extracting `(a,b)` under the
   honest-subtraction constraints. Certified numerically; not built.
3. **`hInterface`** (R1 degraded-core at `M' = MprimeRect (H−r) a b`, on the built second-peel residual)
   and **`hRne`** (slice non-vanishing) — each independently open; sequence on b1+b2+b3.

## Build status
`genm-d1close` @ `9ba81450` (pushed `origin/genm-d1close`). Both new modules green in the full
import-closure build (3009 jobs, exit 0); coexist cleanly (bridge imports `Core.ResidualRank`). No new
name clashes (both under fresh top-level names). LEAF-2 sorry footprint unchanged.

## Pointer for the next hand
The remaining CORE-geometry content of `hrank₂` is now b1 + b3; the bridge and b2 are DONE, so once b1
produces `HasFDerivAt (q(0,·)) L t0` with `L = zeroSel er ∘ (jacFlatL2-linmap) ∘ (chartFDerivEquiv).symm
∘ (flat-complement-inj)` and b3 gives the count, `hrank₂` closes by:
`(jacResid).rank =[bridge] finrank(range L) =[b2, hP+hsurj from the minor] finrank(range T) − nReg
=[b3] extraCountRect`. Then `hInterface` + `hRne` + the two-peel value close (`d1ge_L2_rect_two_peel`)
finish LEAF 2.
