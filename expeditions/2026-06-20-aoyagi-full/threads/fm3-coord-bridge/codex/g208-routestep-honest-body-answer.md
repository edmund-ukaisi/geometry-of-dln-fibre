   189	    exact Finset.mem_singleton.2 rfl
   190	  stratum_surjective := by
   191	    intro T hT
   192	    rw [show (Adm (![1, 1] : Fin 2 → ℕ)) = {(fun _ => 0)} from by decide,
   193	      Finset.mem_singleton] at hT
   194	    exact ⟨(), hT.symm⟩
   195	  mult_one := by intro _ j; fin_cases j; rfl
   196	  threshold_eq := by
   197	    intro _
   198	    rw [show Mval (![1, 1] : Fin 2 → ℕ) (fun _ => 0) = 1 from by decide]
   199	    -- monomialThreshold 1 ![1] ![0] = axisRatio 0 1 = 1/2 = ½·(1).toNat.

codex
Verdict: **blocked** for an honest general `routeStep`.

What is banked today is enough to define the recursion skeleton and value-side folds, but not enough to certify the dispatcher. The current `RouteStep.branch` only carries `split`, `codim`, and `PivotWitness M₀ codim`; `routeAtlas` then uses `split` and `codim`, while the geometric “this cell is genuinely reached” proof is not a field. See [RouteMRecursion.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fm3-routem/lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:151).

Two clarifications:

- A total green body is syntactically possible, including non-leaf fake bodies. For example, one could branch on availability of the `schurState` positivity hypothesis, use `Unit` cells, `split := schurState M hlo`, and choose a combinatorial `T` such as `0` or an `inf'` minimizer. `zero_mem_Adm` and concrete `Mval` mean some `PivotWitness` fields can be discharged without realizability. So the obstruction is not always Lean typing of `hAdm`/`hCodim`.
- But that body is not certified. `PivotWitness` only says `T ∈ Adm M` and `c = (Mval M T).toNat`; it does not say the rank stratum is reached by this chart path. See [RouteMState.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fm3-routem/lean/DLNFibre/DLN/RLCT/Validate/RouteMState.lean:287). Choosing `codim := minAdm` would force the abstract fold value, but it would be smuggling the missing coverage/reachability theorem into the dispatcher.

The value theorem explicitly needs exhaustiveness: `IsResolutionAtlas.stratum_surjective` is the field that every admissible stratum, in particular the minimizer, is reached. `resolution_value_of_atlas` uses that field in the `≤` direction. See [ResolutionAtlas.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fm3-routem/lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:97) and [ResolutionAtlas.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fm3-routem/lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:164).

Leaf-everywhere is also not an honest escape: `leafMonoData` has threshold `⊤`, so it cannot give `½·minAdm` in nondegenerate cases. See [RouteMState.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fm3-routem/lean/DLNFibre/DLN/RLCT/Validate/RouteMState.lean:60). Degenerate zero-width `M` is not a clean partial arm for the stated value either; R1 explicitly carves those out because the core degenerates while the combinatorial right side is finite. See [Skeleton.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fm3-routem/lean/DLNFibre/DLN/RLCT/Skeleton.lean:1018).

The only honest partial object I see is not a general `routeStep` body: the tiny `M = ![1,1]` `IsResolutionAtlas` example is constructed directly, and the `(1,1,1)` case is handled independently. See [ResolutionAtlas.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fm3-routem/lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:184).

So: keep the named `sorry`. Fence exactly these obligations: reached-cell/realizability coverage, geometric codim equals `Mval` for the reached stratum, and the residual-core leaf classifier (`IsUnit residualCore`, or the properly scoped smooth terminal case).
tokens used
259,407
Verdict: **blocked** for an honest general `routeStep`.

What is banked today is enough to define the recursion skeleton and value-side folds, but not enough to certify the dispatcher. The current `RouteStep.branch` only carries `split`, `codim`, and `PivotWitness M₀ codim`; `routeAtlas` then uses `split` and `codim`, while the geometric “this cell is genuinely reached” proof is not a field. See [RouteMRecursion.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fm3-routem/lean/DLNFibre/DLN/RLCT/Validate/RouteMRecursion.lean:151).

Two clarifications:

- A total green body is syntactically possible, including non-leaf fake bodies. For example, one could branch on availability of the `schurState` positivity hypothesis, use `Unit` cells, `split := schurState M hlo`, and choose a combinatorial `T` such as `0` or an `inf'` minimizer. `zero_mem_Adm` and concrete `Mval` mean some `PivotWitness` fields can be discharged without realizability. So the obstruction is not always Lean typing of `hAdm`/`hCodim`.
- But that body is not certified. `PivotWitness` only says `T ∈ Adm M` and `c = (Mval M T).toNat`; it does not say the rank stratum is reached by this chart path. See [RouteMState.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fm3-routem/lean/DLNFibre/DLN/RLCT/Validate/RouteMState.lean:287). Choosing `codim := minAdm` would force the abstract fold value, but it would be smuggling the missing coverage/reachability theorem into the dispatcher.

The value theorem explicitly needs exhaustiveness: `IsResolutionAtlas.stratum_surjective` is the field that every admissible stratum, in particular the minimizer, is reached. `resolution_value_of_atlas` uses that field in the `≤` direction. See [ResolutionAtlas.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fm3-routem/lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:97) and [ResolutionAtlas.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fm3-routem/lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:164).

Leaf-everywhere is also not an honest escape: `leafMonoData` has threshold `⊤`, so it cannot give `½·minAdm` in nondegenerate cases. See [RouteMState.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fm3-routem/lean/DLNFibre/DLN/RLCT/Validate/RouteMState.lean:60). Degenerate zero-width `M` is not a clean partial arm for the stated value either; R1 explicitly carves those out because the core degenerates while the combinatorial right side is finite. See [Skeleton.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fm3-routem/lean/DLNFibre/DLN/RLCT/Skeleton.lean:1018).

The only honest partial object I see is not a general `routeStep` body: the tiny `M = ![1,1]` `IsResolutionAtlas` example is constructed directly, and the `(1,1,1)` case is handled independently. See [ResolutionAtlas.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fm3-routem/lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean:184).

So: keep the named `sorry`. Fence exactly these obligations: reached-cell/realizability coverage, geometric codim equals `Mval` for the reached stratum, and the residual-core leaf classifier (`IsUnit residualCore`, or the properly scoped smooth terminal case).
