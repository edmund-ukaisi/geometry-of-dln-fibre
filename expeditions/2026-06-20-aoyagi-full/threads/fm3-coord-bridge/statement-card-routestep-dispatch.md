# Statement card — `routeStep` leaf-first dispatch (#103, the assembly)

The general-M dispatcher's leaf-first classify (the recursion's per-node step), assembled on the settled
#108 base case. Leaf arm + dispatch CONCRETE; the general branch is the single fenced named gap (→ #104).

---

> **Claim (the dispatch).** `routeStep` classifies a node `(root M₀, current M)` leaf-first: a leaf at the
> degenerate boundary (`minAdm M = 0 ⟺ ∃ s, M_s = 0`) carrying the non-binding `leafMonoData 0` (⊤); else a
> branch.
>
> - **Lean:** `DLNFibre.DLN.RLCT.routeStep`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean` @ `f318d63`)
> - **Gloss.** `routeStep M₀ M := if (minAdm M).toNat = 0 then .leaf (leafMonoData 0) else <branch>`. The
>   leaf test is the geometric degenerate boundary (`isLeafNode`, `RouteMClassify.isLeafNode_iff_width_zero`).
>   Leaf-first (the test GATES the branch): a node with a collapsed width is a leaf even when `schurState`
>   technically applies (the `(2,2,0)` catch), so split-first would over-pivot.
> - **Proved.** The leaf arm + the leaf-first dispatch are concrete and build green. The leaf datum
>   `leafMonoData 0` (threshold `⊤`) is the **non-binding path-terminator** — settled #108(b)/g236 (pp2
>   @8eea89e, controller-pinned, the 3×-flip-flop resolved): the value `⨅` rides the codims ACCUMULATED along
>   the path (`appendDivisor` at branch nodes), not the terminal's own value; a `0`-binding leaf would force
>   `⨅ = 0` — the `⊤` AVOIDS that. `routeStep` computes the CORE (`½·minAdm = lambdaCore`); `nReg/2` is L2's
>   shift OUTSIDE; `#70` is the degenerate-**ROOT** whole-case ONLY (NOT a per-leaf handler — that would
>   double-count). [Decl-forced + decorrelated-Codex-confirmed, `codex/leaf-arm-answer.md`.]
> - **Assumed.** none for the dispatch/leaf arm.
> - **Cited.** `leafMonoData` / `Adm` / `Mval` (banked); `isLeafNode_iff_width_zero` (#108, reviewed).
> - **Deferred (the single named gap).** The GENERAL branch arm (`else` ↦ `sorry`): for a non-leaf `M`, emit
>   the cells + per-cell admissible-`Mval` codims + the achiever `T*` (the rank-pattern read). This is the
>   formaliser-weeks general dispatcher; realizability (chart path reaches the stratum) is NOT manufactured
>   here — it lives in the `IsRouteMCover` COVER (#104, the honesty-gate, controller's option-a ruling). The
>   achiever-leaf-existence rides the cascade realizability (`Core.CascadeRealizable.cascadeTuple_mem_realizableRank`,
>   #116) at #104.
> - **Status.** sorry-free except the single fenced branch `sorry` (the named gap). The dispatch + leaf arm
>   are the landed #103 increment; the value-fold over the actual `routeMIota` rides the general branch.

**Value-fold status (the #103 value target).** `⨅ over routeMIota M₀ of monomialThreshold(data i) =
½·minAdm(M₀)` for non-degenerate `M₀` is the headline the dispatch feeds. It is **branch-gated**: `routeAtlas`
(`WellFounded.fix` matching on `routeStep`) cannot unfold through the branch `sorry`, so `routeMIota M222`
does not compute, and the value-over-`routeMIota` rides the general branch. The ABSTRACT anchor value IS
banked: `Case222RouteStep.case222_routeStep_value = 3/2` (over `codimsOf222 = [4,3]`, via
`foldFamily_iInf_eq_half_minAdm`). The `(2,2,2)` recursion is TRACED (pp2 g237 @ee81ce8): node `(2,2,2)`
(BRANCH) appends `Mval((2,2,2),(0,0)) = 4` → `(1,1,2)` (BRANCH) appends `Mval((2,2,2),(1,0)) = 3 = minAdm`
→ `(0,0,2)` (TERMINAL, `⊤`, appends `[]`); `foldDivisors([4,3]) = min(2, 3/2) = 3/2`. So the per-node codim
is the ROOT-anchored `Mval M₀ T_node` (the `PivotWitness M₀` content), `T_node = (0,0)` then `(1,0)`.

**Two blockers to wiring the value-over-`routeMIota` (both flagged, neither faked):**
1. **Layout (a hard Lean cycle).** Making `routeStep`'s branch split concrete (`schurState M hlo`) needs
   `hlo`/`isLeafNode` in `routeStep`'s scope, but `isLeafNode` + `schurState_hlo_of_not_isLeafNode` live in
   `RouteMClassify` which IMPORTS `RouteMRecursion` (where `routeStep` is). Fix = move the leaf classifier
   UPSTREAM (a new `RouteMLeaf.lean` that `RouteMRecursion` imports). Awaiting the controller's layout call.
2. **The general branch = the rank-pattern read** (the cells/codim/witness for arbitrary non-leaf `M`: which
   root-anchored `T_node` per node). This is the formaliser-weeks general dispatcher, and its
   achiever-leaf-existence rides the orbit-side realizability tie (#96/#121, `Adm ↔ RealizableRank`) — the
   genuine gate. Sub-2b (`cascadeTuple_mem_realizableRank`, #116) is the `RealizableRank`-side witness source;
   #121 ties it to `Adm`/`Mval`. The general value-over-`routeMIota` closes once both land (#104-adjacent).
