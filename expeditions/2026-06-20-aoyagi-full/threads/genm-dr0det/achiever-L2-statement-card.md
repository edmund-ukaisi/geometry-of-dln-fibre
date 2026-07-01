# Statement card — the L=2 achiever box-divergence (`routeMCore_box_diverges_achiever_L2`)

> **Claim.** For every dimension vector `M : Fin 3 → ℕ` with `1 ≤ minAdm M`, and every `c'` at-or-above
> the achiever threshold `½·minAdm M`, the flat-coordinate box integral of the threshold density
> `|routeMCore M|^{−c'}` over the cube `[−ε,ε]^N` is `⊤`, for every `ε > 0`. This is the R1-LOWER value
> leg's headline at `L = 2` — the lower bound `rlctAtOn ≤ ½·minAdm M`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.routeMCore_box_diverges_achiever_L2`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDeepRank0Atom.lean`, module uncommitted to the
>   aggregator — controller to wire into `DLNFibre.lean` + `AxCheck`).
> - **Gloss.** `∫⁻ x in cubeBox (routeMAmbient M) ε, ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) = ⊤`.
>   Assembled by the `2 ≤ L` trichotomy (`achiever_trichotomy_total`) done DIRECTLY at `L = 2`:
>   INTERIOR / BOUNDARY-CLEAN / BOUNDARY-SMEARED.
> - **Proved.** Unconditionally (given `1 ≤ minAdm M`, `½·minAdm ≤ c'`, `0 < ε`):
>   - **INTERIOR** (`routeMCore_box_diverges_interior_L2`): cases on `deepRank M = Text M (tach M) 2`.
>     `0 < deepRank` → the banked LIVE-leaf∘kLDU atom `routeMCore_box_diverges_interiorLive`;
>     `deepRank = 0` → the NEW E-radial atom `routeMCore_box_diverges_eDeepRank0` (this thread, items
>     1-8). So `hInterior` holds on ALL `InteriorDrop M`.
>   - **BOUNDARY-CLEAN**: the banked `routeMCore_box_diverges_clean`, with `hNo : NoInteriorBothDrop M`
>     DERIVED in-branch from the clean equality `deepRank M = deepRows M` (`boundaryClean_noInteriorBothDrop_L2`,
>     #160), and the deepest-block nonemptiness `hne` from `deepestCoords_card = M1·M2 > 0` (widths
>     positive, `widths_pos_of_minAdm`).
>   - **BOUNDARY-SMEARED**: the banked `hSmeared_L2_apply` (the square-`P₁` stratum).
> - **Assumed.** `1 ≤ minAdm M` (non-degeneracy: the achiever center has positive codimension) — forces
>   all three widths positive (`widths_pos_of_minAdm`). No genericity/positivity beyond this.
> - **Cited.** `monomial_rlct` (S2) — inherited from the clean / interior monomial box-divergence atoms
>   (the bare-monomial `∫ |u_p|^{−…} = ⊤` at the achiever threshold). NO other analytic interface.
> - **Deferred.** The general-`L` `routeMCore_box_diverges_achiever` (`RouteMLayerCoverGE`) remains open
>   (its `sorry`, #120-gated) — this card is the `L = 2` specialization ONLY; it is NOT the general
>   headline, and does not close it.
>
> **Design note (why the direct trichotomy, not the spine).** The banked spine
> `routeMCore_box_diverges_achiever_spine` takes `hNo : NoInteriorBothDrop M` as a FLAT hypothesis, but
> `NoInteriorBothDrop M` is FALSE on the interior/smeared branches at `L = 2` (interior ⟺ `deepRank < M0 ∧
> deepRank < M1`, which is exactly an interior both-drop). So the spine cannot be fed a true `hNo` for a
> general `M`. The `L = 2` wire instead does the trichotomy directly and derives `hNo` in the clean branch
> from `hclean` — sound and sorry-free.

## The `deepRank = 0` box-divergence atom (`routeMCore_box_diverges_eDeepRank0`, item 8)

> **Claim.** For a `deepRank = 0` interior stratum at `L = 2` (`Text 2 = 0`, `0 < M0, M1, M2`), the
> achiever box integral diverges at `c' ≥ ½·minAdm M`, for every `ε > 0`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.routeMCore_box_diverges_eDeepRank0`
>   (`RouteMInteriorDeepRank0Atom.lean`).
> - **Proved.** Via the M-agnostic `routeMCore_box_diverges_of_nodeChart` fed the `eDeepRank0NodeChart`
>   bundle: chart `eDeepRank0Phi` (the E-fixed-pivot radial blow-up), binding pivot `eBlockPivot`, the
>   SINGLE-AXIS `eDeepRank0_leafH` (`minAdm−1` at the pivot, `0` else), the UNCONDITIONAL det
>   `eDeepRank0_abs_det = ∏_j |u_j|^{leafH j} = |u_p|^{minAdm−1}` (item 5: `radialComp_abs_det_at` +
>   `|det DB| = 1`, the latter via `BchartE = BchartLeaf` at `deepRank = 0` + the banked
>   `BchartLeaf_abs_det_free` + the empty-K det, since `readK ⟨0⟩` is `0×0`), the cov
>   (`ldu_cov_of_differentiable_injOn`, PURE monomial), the injOn `eDeepRank0_injOn` (unconditional
>   K-det=1 recovery), and the a.e.-positive unit `eDeepRank0Unit_ae_pos` (item 6, PROVED).
> - **Bedrock note (the double-count trap avoided).** The naïve `phiFlatLiveAt … eBlockPivot` chart
>   (direct `readE`) would read the pivot E-slot as a free residual AND scale it by the radial, giving
>   `(x_p)²` in the map and an EXTRA `|u_p|` in the det (for `M=(1,1,2)`: `2|u_p|`, not `|u_p|^0 = 1`) —
>   the Item-102 double-count. The fix (Codex xhigh + `RouteMBData222`-precedented): gauge-fix the pivot
>   E-slot to the literal `1` (the `EfixedReader`/`genBlkFlatEfp` decoder), keeping the OTHER E-slots
>   live. Then the det is EXACTLY the single-axis monomial (no K-product), and `½·minAdm = ½·M0·M1` is the
>   headline rate.
>
> **Axioms (force-recompiled `#print axioms`):**
> - `routeMCore_box_diverges_achiever_L2` = `[propext, Classical.choice, Quot.sound, monomial_rlct]`.
> - `routeMCore_box_diverges_eDeepRank0` = `[propext, Classical.choice, Quot.sound, monomial_rlct]`.
> - `routeMCore_box_diverges_interiorLive` (the pre-existing interior atom) UNCHANGED = same four.
> - `eDeepRank0Unit_ae_pos` = `[propext, Classical.choice, Quot.sound]` (no S2).
>
> No `sorryAx` / `native_decide` / custom axioms in the `deepRank = 0` chain.
