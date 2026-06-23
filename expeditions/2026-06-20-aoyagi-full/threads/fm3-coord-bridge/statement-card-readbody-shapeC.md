# Statement card — #99 read body (Shape C): binding cell + complement cover

The general non-leaf `routeStep` read (#99), built green-with-named-gaps in `RouteMScaffold.lean`. The
binding (achiever) cell is constructed GREEN; the complement cover is the named gap (a structure the #99
grind produces). Decorrelated-Codex Shape C (`codex/readbody-skeleton-answer.md`).

**NOTE (controller ruling 2026-06-23, @`4f499ad`):** a CONCRETE achiever-only producer (`PUnit` binding
cell + empty complement) was built then REVERTED — it is degenerate-as-cover + redundant-as-value (the
achiever-binds-at-`minAdm` is already `routeM_value_eq`'s `i₀`/`hbind₀`), i.e. trap-(iii) in value-correct
disguise. The Shape-C structures below are the INTERFACE; the genuine multi-cell read is G-a-gated (#135).

> **Claim.** For a general non-leaf node (root `M₀`, current `M`), the rank-pattern read produces a
> `BranchData M₀ M` (the `RouteStep.branch` payload) whose binding cell carries the achiever's
> root-anchored `PivotWitness M₀ (minAdm M₀)` (so the value fold's `C=∃` leaf is present), assembled from
> a binding cell + a complement cover. The binding cell at the root is constructible; the complement cover
> is the genuine combinatorial decomposition (the named gap).

- **Lean:**
  - `DLNFibre.DLN.RLCT.R1BindingCell` / `R1ComplementData` (structures)
  - `DLNFibre.DLN.RLCT.branchDataOfReadParts` (the producer)
  - `DLNFibre.DLN.RLCT.r1BindingCellRoot` (the GREEN root binding cell)
  - `DLNFibre.DLN.RLCT.branchDataOfReadParts_binding_present` (non-vacuity guard)
  - (`lean/DLNFibre/DLN/RLCT/Validate/RouteMScaffold.lean` @ `43de87c`)
- **Gloss.**
  - `R1BindingCell M₀ M` = ⟨`split : ChainDimSplit M`, `codim : ℕ`, `witness : PivotWitness M₀ codim`,
    `hbind : codim = minAdm M₀`⟩ — the achiever cell's data, root-anchored at `M₀`.
  - `R1ComplementData M₀ M` = ⟨`cells`, `[Fintype]`, `split`, `codim`,
    `witness : (c) → PivotWitness M₀ (codim c)`⟩ — the remaining pivot cells (NO `Nonempty`: the
    complement can be empty; reviewer fix @`212ec6f`).
  - `branchDataOfReadParts b d : BranchData M₀ M` = the `PUnit ⊕ d.cells` assembly; the binding cell
    (`Sum.inl`) is always present, complement cells are `Sum.inr`.
  - `r1BindingCellRoot M₀ split : R1BindingCell M₀ M₀` — the witness is `achieverPivotWitness M₀` (the
    `inf'`-achiever `T*` from `Finset.exists_mem_eq_inf'`), `codim = minAdm M₀`, `hbind = rfl`.
  - `branchDataOfReadParts_binding_present` — the assembled `codim (Sum.inl _) = b.codim` (by `rfl`).
- **Proved (unconditional, GREEN, zero sorry).** The producer `branchDataOfReadParts` (assembles a valid
  `BranchData` from the two parts); the root binding cell `r1BindingCellRoot` (the achiever leaf is
  constructed, non-vacuously — `T*` exhibited via `exists_mem_eq_inf'`, `codim = minAdm M₀` definitionally);
  the non-vacuity guard (the binding cell's codim survives into the assembled `BranchData`).
- **Assumed (the named gap, as a structure INPUT, not a `sorry`).** `R1ComplementData M₀ M` for arbitrary
  non-leaf `M` — the genuine combinatorial rank-pattern read (which non-binding pivot cells exist + their
  per-cell admissible `T_c` codims). PLUS the binding cell's `T*`-profile `ChainDimSplit M` (the achiever's
  rank-drop split, NOT the front-collapsing uniform `schurState` — §4 cert §4; supplied as the `split`
  input to `r1BindingCellRoot`). These are the formaliser-weeks #99 content (#135).
- **Cited.** none (combinatorial; the `inf'`-achiever and `PivotWitness` machinery are all in-repo GREEN).
- **Deferred (NOT in this read — separate lanes).**
  - The per-cell ANALYTIC descent (`IsSchurStraightenSqueeze`/`hnode` Schur presentation tying each cell's
    pullback to `dlnLoss (split c).red 0`) — carried separately at the cover-lintegral level (#104,
    crux2's `redCore_eq`), NOT a field of the read (§4 feasibility cert §3). The read is COMBINATORIAL.
  - The geometric-codim identification (`codim = Mval M₀ T_c` IS the actual exceptional-divisor codim) —
    fm3's R1-result + the `hnode` gate (#133/#135), NOT this read (controller ruling 2026-06-23).
  - The achiever realizability tie (`rankFn (cascadeTuple M₀ T*) = achieverRankPattern M₀ T*`) — tie-fm's
    #121-(ii) (#128–#132). The read's `PivotWitness.hAdm` fences the cap-bug; realizability rides #121-(ii).
- **Status.** sorry-free (awaiting reviewer fidelity check).

## Fidelity points for the reviewer

1. Is `branchDataOfReadParts` a faithful `BranchData` assembly (no field fudged; `witness` correctly
   `Sum.elim`-ed with the binding witness on `Sum.inl`)?
2. Is the binding cell GENUINELY non-vacuous (the `C=∃` achiever leaf), or does `r1BindingCellRoot` smuggle
   the value? Check: `witness = achieverPivotWitness M₀` exhibits `T* ∈ Adm M₀` with `Mval M₀ T* = minAdm`
   (NOT `⟨_, rfl⟩`); `hbind = rfl` because `codim` is definitionally `minAdm M₀`.
3. Is the named gap (`R1ComplementData` + the `T*`-profile split) the RIGHT gap — the genuine
   combinatorial read — and is everything Deferred correctly OUTSIDE the read (analytic descent #104,
   geometric fidelity fm3-R1, realizability tie #121-(ii))?
4. Does the skeleton compose with `routeStepOf`/`routeAtlasOf`/`routeM_value_eq` (already GREEN)? The
   producer's output is exactly the `hbranch` input `routeStepOf` consumes.
