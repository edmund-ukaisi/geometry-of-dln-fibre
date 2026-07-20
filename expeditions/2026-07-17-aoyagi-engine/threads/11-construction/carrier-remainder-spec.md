# Carrier-REMAINDER spec — qNodeOf + u-coord + counts (t05's closer)

*architect-t05's last deliverable (hatch stands, tick-212). The arithmetic selector is MERGED
(`Engine/CenterIndices.lean`: `flatCoordOf` + `resBlockCenterIndices`, both injective, clean-three —
the load-bearing piece). This spec is the REMAINDER, for the seat that builds qNodeOf (t06 post-landing
if its budget reads honest, else t07). Supersedes `t07-carrier-spec.md` (this is the merged-selector
update with the qNodeOf traps named). Then t05 stands down.*

## Banked foundation (inherit, do not rebuild)

`Engine/CenterIndices.lean` (merged, clean-three):
- `flatCoordOf M s i j : Fin (flatDim M)` = `Fintype.equivFin (FlatIdx M) ⟨⟨s,i⟩,j⟩` — the `(i,j)`
  entry of the `s`-th weight matrix as a flat index (the reindex `paramsEquivFlat` uses). `+ _injective`.
- `resBlockCenterIndices M s J rows cols (hrow : J+rows ≤ M s.castSucc) (hcol : J+cols ≤ M s.succ) :
  Fin (rows*cols) → Fin (flatDim M)` — the residual sub-block, flattened, injective. Instantiate:
  case-2 `(resRows,resCols)`; case-1(2) `(runLen,resCols)`.

## 1. qNodeOf — the Homeomorph assembly (the intricate remainder) + THE TRAPS

`qNodeOf (node) : Params M ≃ₜ (Fin d_center → ℝ) × (Fin (flatDim M − d_center) → ℝ)`, node-DERIVED from
the selector (seam pin: node-indexed def, never existential). Three composed steps:
1. `paramsEquivFlat M` as a **Homeomorph** — use `paramsEquivFlatCLE M` (the continuous-linear-equiv,
   `ParamsFlat.lean`)`.toHomeomorph`; its continuity both ways is banked (`ParamsFlat.lean:104+`).
2. a permutation `σ : Fin (flatDim M) ≃ Fin d_center ⊕ Fin (flatDim M − d_center)` built FROM the
   injective `centerIndices` (the center coords = its `Fin d_center` image; the rest = the complement).
3. `arrowCongr` split: `(Fin (flatDim M) → ℝ) ≃ (Fin d_center ⊕ rest → ℝ) ≃ (Fin d_center → ℝ) ×
   (Fin rest → ℝ)` (`Equiv.arrowCongr σ (.refl ℝ)` then `Equiv.sumArrowEquivProdArrow`), each a
   Homeomorph (`Homeomorph.piCongrLeft` / `Homeomorph.sumArrowHomeomorphProdArrow` if present, else
   `Continuous` on both directions is routine on finite pi/products).

**TRAPS (foreseen — name them so t07 doesn't rediscover):**
- **A. Totality.** qNodeOf needs `d_center ≤ flatDim M` + injective `centerIndices` — hold on REACHABLE
  nodes only. Use a `dite`-fallback for junk states (like `leafOfState`), correctness on the cone
  (thread from the node's `OracleInv`/`StateInvariant`). Do NOT try to make it total-and-correct.
- **B. The permutation from the injective selector (§2 step).** Extending injective `centerIndices :
  Fin d_center ↪ Fin (flatDim M)` to `σ : Fin (flatDim M) ≃ Fin d_center ⊕ Fin (flatDim M − d_center)`:
  use the range + its complement (`Equiv.sumCompl`, `Function.Embedding.toEquivRange`, or
  `Equiv.Perm` from the embedding). The `rest` size is `flatDim M − d_center` — the `Fintype.card`
  bookkeeping (`card (range) = d_center` by injectivity; complement card = `flatDim − d_center`) is the
  fiddly step; `Fintype.card_compl_set` / `Finset.card_compl`. This is where the intricacy concentrates.
- **C. Homeomorph vs measure/instance diamond.** `paramsEquivFlatCLE` lives on the `Params M`
  NormedSpace instance; the `Matrix.module` vs `NormedSpace.toModule` diamond (lean/CLAUDE.md gotcha)
  can bite if you mix the CLE with a `Matrix.module`-built map. Stay on the CLE's instance; do the
  split on `Fin (flatDim M) → ℝ` (the flat side), never on `Params M` directly.
- **D. arrowCongr continuity.** The sum/product `arrowCongr` steps are continuous on FINITE index
  types; if a ready `Homeomorph` combinator is absent, `continuous_pi` + `continuous_apply` on each
  factor closes both directions — routine but verbose. Don't hand-roll the equiv; reuse `Equiv.*` +
  prove `Continuous` on the two maps.
- **E. Per-case dispatch.** case-1 emits TWO edges (partition): case-1(1) `d_center_edge = 1` (u-pivot,
  §2 below); case-1(2) `= runLen·resCols` (NOT resRows — the d-family). case-2 `= resRows·resCols`.
  rollover `= 0`. Node `d_center` = sum; never the node total on the case-1(2) edge (double-counts u).

## 2. The u-coord slot — one line, wired to pnp-slot's verdict

The case-1(1) center's `u`-pivot is an existing divisor `u_{s,k}` (ledger-tied). READ pnp-slot's
slot-stability cert:
- **IF slot-stable** (t05's + controller's hypothesis: substitution-in-place ⟹ a divisor keeps its
  BIRTH CORNER flat slot): the u-coord = `flatCoordOf M s ⟨J, _⟩ ⟨J, _⟩` (the corner `d_{J+1,J+1} =
  u_{S,J+1}`, `page-pin-centers.md`) — ONE line into the case-1(1) selector `Fin 1 → Fin (flatDim M)`.
  Needs a `divBirthCoord` birth-record field (set at case-1(2)/case-2 births, carried VERBATIM by every
  transition — congruence maintenance, cheap) IF the chosen divisor's `(s,J)` birth isn't recoverable
  from `divProfile`; the cert adjudicates recoverability.
- **IF NOT slot-stable:** the map is dynamic (bigger) — surface to the controller (budget).

## 3. Per-edge count helpers (trivial)

`dCenterOfEdge (node : StepData M) (e : Edge M) : ℕ` by case: `case11 => 1`; `case12 => e.subst.runLen
* node.resCols`; `case2 => node.resRows * node.resCols`; `rollover => 0`. (Coverage can also inline
these; a named helper is convenience.)

## 4. Per-case shapes + verification gate

- case-2: center = residual block; `centerIndices = resBlockCenterIndices M s J resRows resCols _ _`.
- case-1(1): `d_center_edge = 1`, the u-coord (§2).
- case-1(2): `centerIndices = resBlockCenterIndices M s J runLen resCols _ _`.
- rollover: 0 (chartless).
- **Gate:** full `lake build DLNFibre` + `#print axioms` all watched roots at expected footprints +
  (2,2,4) witness re-elaboration, one batch. Protected-set re-probe (`canonicalResolution224_arithmetic`,
  `region_glue_of_chartBridge`, `minAdm_le_terminalExponents`, `isFullMonomialization_buildTree_conRoot`
  — disjoint files, confirm undisturbed). qNodeOf node-indexed (seam pin), no existential.

## Pointers
Interface: `carrier-interface-proposal.md` (f0a8363fd) + `carrier-interface-review.md` (mine) +
elder-gate9 (journal tick 206). Geometry: `page-pin-centers.md`, `cert-psi-mix.md`. Reuse:
`banked-families.md` § CARRIER-ADJACENT REUSE INDEX. u-pivot: pnp-slot's cert (pending — read directly).
