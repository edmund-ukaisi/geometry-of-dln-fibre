# Statement card — `routeStep` leaf-first dispatch (#103, the assembly)

The general-M dispatcher's leaf-first classify (the recursion's per-node step), assembled on the settled
#108 base case. Leaf arm + dispatch CONCRETE; the general branch is the single fenced named gap (the general
dispatcher BODY → **#85**; the per-node descent-soundness is the SEPARATE #104, the geometric fidelity #135).

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
>   formaliser-weeks general dispatcher BODY (**#85**). The achiever-leaf-existence rides the GENUINE
>   orbit-side realizability tie **#121** = `rankFn_cascadeTuple_eq_achieverRankPattern` (PROVEN):
>   `rankFn (cascadeTuple M₀ T*) = achieverRankPattern M₀ T*`, where `achieverRankPattern` is the achiever's
>   prescribed pattern `r*` built from `(M₀, T*)`/`Adm` ALONE (the formalized #96 `Adm ↔ RealizableRank`
>   map) — NOT from the cascade. **Do NOT cite `cascadeTuple_rankFn_mem_range` as the realizability**: it is
>   the VACUOUS `∈`-range tautology (`rankFn (cascadeTuple) ∈ range rankFn := ⟨_, rfl⟩`, f(x)∈range(f)) — it
>   realizes the cascade's OWN pattern, says nothing about `r*`. #116 supplies the matrix substance
>   (`rankPattern_cascade_prefix`, the `(0,j)` row); #121 is the genuine `= r*` equality. The per-node
>   descent-SOUNDNESS (the `IsRouteMCover` cover-CoV) is the SEPARATE **#104**; the geometric-codim fidelity
>   is **#135**. (So: value-of-the-read rides #85 + the #121 tie; descent rides #104; geometry rides #135.)
> - **Status.** sorry-free except the single fenced branch `sorry` (the named gap, → #85). The dispatch +
>   leaf arm are the landed #103 increment; the value-fold over the actual `routeMIota` rides #85 (the general
>   dispatcher body) + the #121 achiever tie, NOT #104 (which is the separate descent-soundness).

**Value-fold status (the #103 value target) — the WIRING is BUILT (`routeM_value_eq`, `RouteMValue.lean`).**
`routeM_value_eq` proves `⨅ over routeMIota M of monomialThreshold(routeD/routeK/routeH i) = ½·minAdm(M)`
CONDITIONALLY on (a) the recursion-accumulation `hdata : (routeAtlas M M).data i = foldDivisors (codimsOf i)`
+ (b) the `foldFamily_iInf` data (per-codim root-anchored `PivotWitness M`, an achiever leaf `i₀` with
`minAdm ∈ codimsOf i₀`). It reduces to `foldFamily_iInf_eq_half_minAdm` — PivotWitness-ONLY, NO cascade. This
is the honest value-fold LOGIC: it does NOT unfold the branch `sorry` (the hypotheses `hdata`/`hwit`/`i₀` are
INPUTS the `routeStep` branch supplies — the named gap), and it smuggles nothing (no trap-iii Unit-cell, no
fabricated achiever). The branch construction (proving `hdata` + emitting the genuine codims/witnesses/achiever
for general `M`) is the named gap, riding the rank-pattern read / #121. The ABSTRACT anchor value IS banked:
`Case222RouteStep.case222_routeStep_value = 3/2` (over `codimsOf222 = [4,3]`, via `foldFamily_iInf`). The `(2,2,2)` recursion is TRACED (pp2 g237 @ee81ce8): node `(2,2,2)`
(BRANCH) appends `Mval((2,2,2),(0,0)) = 4` → `(1,1,2)` (BRANCH) appends `Mval((2,2,2),(1,0)) = 3 = minAdm`
→ `(0,0,2)` (TERMINAL, `⊤`, appends `[]`); `foldDivisors([4,3]) = min(2, 3/2) = 3/2`. So the per-node codim
is the ROOT-anchored `Mval M₀ T_node` (the `PivotWitness M₀` content), `T_node = (0,0)` then `(1,0)`.

**Two blockers to wiring the value-over-`routeMIota` (1 RESOLVED, 1 the named gap):**
1. **Layout — RESOLVED (A-refactor @`815cd89`).** The leaf classifier (`isLeafNode` +
   `schurState_hlo_of_not_isLeafNode`) was moved UPSTREAM into `RouteMLeaf.lean`, which `RouteMRecursion`
   (where `routeStep` lives) now IMPORTS — so `routeStep`'s leaf-first dispatch has `isLeafNode`/`hlo` in
   scope (`RouteMRecursion.lean:199`/`206`). The def-ordering cycle is gone; no `RouteStep`-type change was
   needed (the dispatch body constructs the existing `.branch` fields). NOT an open layout question.
2. **The general branch = the rank-pattern read** (the cells/codim/witness for arbitrary non-leaf `M`: which
   root-anchored `T_node` per node). This is the formaliser-weeks general dispatcher, and its
   achiever-leaf-existence rides the orbit-side realizability tie (#96/#121, `Adm ↔ RealizableRank`) — the
   genuine gate. Sub-2b (#116) supplies the (0,j)-row computation (rankPattern_cascade_prefix); the genuine
   realizability tie is **#121** (`rankFn_cascadeTuple_eq_achieverRankPattern`, PROVEN — `rankFn(cascadeTuple
   t*) = achieverRankPattern`, the INDEPENDENT `r*` built from `(M,T)` alone; NOT the renamed
   `cascadeTuple_rankFn_mem_range` ∈-range tautology). **Scope (controller ruling):** the value-over-
   `routeMIota` closes with the GENERAL dispatcher BODY (**#85**, the general `routeStep`); **#104** is the
   SEPARATE descent-soundness (cover-CoV), NOT the value-closure. So: value rides #85 (+ the #121 tie for the
   achiever leaf); #104 is the descent.
