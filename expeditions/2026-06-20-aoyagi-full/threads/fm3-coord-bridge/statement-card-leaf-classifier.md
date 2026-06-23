# Statement card — the `routeStep` leaf classifier + the #108 leaf-fidelity gate

The terminal-node test for the general `routeStep` dispatcher (the recursion's BASE CASE) and its exact
geometric characterization. Reviewed (fidelity SURVIVED, a3a7737, decorrelated-Codex-concurred).

---

> **Claim (the leaf test).** A node `M` is a leaf iff its minimal admissible codim is `0`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.isLeafNode`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMClassify.lean` @ `1b0cf96`)
> - **Gloss.** `isLeafNode M := ((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat = 0` — the `inf` of the
>   Aoyagi candidate value `Mval` over the admissible cone `Adm M`, cast to `ℕ`, is `0`. Decidable.
> - **Proved.** The predicate + its `Decidable` instance.
> - **Assumed.** none.
> - **Cited.** none (`Adm`/`Mval` are concrete `Foundations/Lambda.lean` definitions).
> - **Deferred.** none.
> - **Status.** sorry-free + reviewed.

> **Claim (#108 GATE — the exact geometric characterization).** A node is a leaf iff some layer width
> has collapsed: `minAdm M = 0 ⟺ ∃ s, M_s = 0` (chains of length `≥ 2`).
>
> - **Lean:** `DLNFibre.DLN.RLCT.isLeafNode_iff_width_zero`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMClassify.lean` @ `1b0cf96`)
> - **Gloss.** `isLeafNode M ↔ ∃ s, M s = 0` for `M : Fin (L'+1+1) → ℕ`. The leaf test detects exactly the
>   DEGENERATE BOUNDARY (a width-0 layer bottlenecks the chain through rank 0). `⇒` =
>   `exists_width_zero_of_isLeafNode` (the no-false-leaf direction: all widths `≥ 1` ⟹ every admissible
>   `Mval ≥ 1`, via a downward `Fin.reverseInduction` forcing `T ≡ 0` then `Mval = M_0·M_1 ≥ 1`). `⇐` =
>   `exists_admissible_Mval_zero` (the prefix-min witness `witT M j = ⨅_{i≤j+1} M_i`: `Mval M witT = 0`
>   unconditionally by termwise telescoping `(a−min a b)(b−min a b)=0`, and admissible exactly when a width
>   collapses; handles INTERIOR `M_{≥2}=0`, not only `M_0/M_1`).
> - **Proved.** The full `iff`, both directions, sorry-free. Non-vacuity anchors: `not_isLeafNode_M222`
>   (`(2,2,2)` minAdm=3, a branch), `isLeafNode_collapsed` `(0,0,2)`, `isLeafNode_degenerate_tail` `(2,2,0)`
>   (leaf though `schurState` still applies), `isLeafNode_interior_zero` `(3,0,3)` (interior leg via `⇐`).
> - **Assumed.** chain length `≥ 2` (`Fin (L'+1+1)`) — necessary, since the sharp form indexes `M 1`
>   (`Mval_zeroT_eq = M_0·M_1`). The general `∃ T ∈ Adm, Mval=0` form (`isLeafNode_iff_exists_zero`) is at
>   full `Fin (L+1)`.
> - **Cited.** `Mval_nonneg_adm` (`ResolutionAtlas.lean`, `0 ≤ Mval` on `Adm` — imported, not reproved).
> - **Deferred.** none for the classifier. **The leaf VALUE is NOT this gate** — see the caveat.
> - **Status.** sorry-free + reviewed. Matches pp2 #109 cert (g232/g233, 1360 M, 0 mismatches).

**⊤-TRAP CAVEAT (fidelity-critical, pp2 g231; recorded in the iff docstring).** At a leaf node
`dlnLoss M 0 ≡ 0` (a width-0 layer makes the product vacuous), so its RLCT is `⊤`, **NOT** `½·minAdm = 0`.
The leaf VALUE must route through the **#70 degenerate-boundary Morse handler** (`rlctAt = nReg/2`), not the
additive `½·minAdm` fold. This is the leaf-arm value-wiring obligation for sub-3/sub-4 (open).

> **Claim (the branch constructor — sub-2a).** The generic `RouteStep.branch` assembly, consuming
> root-anchored witnesses.
>
> - **Lean:** `DLNFibre.DLN.RLCT.routeStepBranch` + `routeStepBranch_M222`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMBranch.lean` @ `1b0cf96`)
> - **Gloss.** `routeStepBranch M₀ M hlo cells codim witness : RouteStep M₀ M` = `.branch` with the uniform
>   `schurState M hlo` split. `routeStepBranch_M222 = case222_routeStep_branch` by `rfl` (reproduces the
>   worked (2,2,2) template).
> - **Proved.** The assembly + the (2,2,2) reproduction.
> - **Assumed.** the per-cell `PivotWitness M₀ (codim c)` is SUPPLIED by the caller.
> - **Cited.** none.
> - **Deferred.** the achiever-branch realizability (`T* ∈ RealizableRank M₀` via the diagonal cascade,
>   sub-2b) — the committed `PivotWitness` carries no realizability field, so the constructor cannot
>   manufacture it; this is the genuinely-new Core piece (`Matrix.rank` count-the-1s), NOT done here.
> - **Status.** sorry-free + reviewed (the honesty boundary is correctly drawn — consumes, not smuggles).
