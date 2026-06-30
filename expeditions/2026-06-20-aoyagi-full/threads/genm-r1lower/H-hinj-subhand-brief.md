# Sub-hand brief #3 — `hinj`: ∀M-L2 InjOn of the LDU-lensed interior chart (the NAMED build-risk)

**Base:** branch off `origin/expedition/genm-r1lower` (current tip `481d8352` — has the merged H2a
`lduleafH` + H3 cov engine + my `BchartLDU` foundation). Build in an isolated worktree.

**MODULE BOUNDARY:** prove your result as a **named atom in your OWN new file** (suggested
`lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLDUInjOn.lean`), importing
`RouteMInteriorLDUContract` (for `interiorLDUphi`, `interiorLDU_leafH`, `structPivot`). Do NOT edit
`RouteMInteriorLDUContract.lean` / `RouteMInteriorLDULeafH.lean` / `RouteMInteriorLDUCov.lean` / my
`BchartLDU` defs. Hand genm-r1lower the named atom; I wire it into the contract's `hinj` slot at
assembly.

## Your atom (EXACT signature — H3's `interiorLDU_cov_of_facts` consumes this shape)
```
theorem interiorLDU_injOn (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (hN : 0 < routeMAmbient M) :
    Set.InjOn (interiorLDUphi M ha hN)
      {u : Fin (routeMAmbient M) → ℝ | u (structPivot M hN) ≠ 0
        ∧ ∀ j ∈ (Finset.univ.filter (fun a => 0 < interiorLDU_leafH M ha hN a)).erase (structPivot M hN),
            u j ≠ 0} := …
```
(The domain E = weighted axes EXCLUDING the pivot, `genm-h3`-confirmed. Confirm the exact `E`/set
shape H3's `interiorLDU_cov_of_facts` wants by reading `RouteMInteriorLDUCov.lean`'s `hinj` hypothesis
— match it verbatim so the wire is a one-liner. The pivot is handled by the separate `u_p ≠ 0`
conjunct.)

## The proof: the phi3333_injOn-style triangular recovery, generalized to opaque widths
`interiorLDUphi = phiFlatLDU M (tach M) ha hN (kLDU …) = phiGen (x_p) (genBlkFlatStruct (kLDU x))`.
Off the weighted planes, recover every coordinate of `x` from `interiorLDUphi x` (the chart output) by
the triangular structure — direct slot reads + divisions by the nonzero weighted pivots (the radial
`x_p`, the LDU diagonal pivots `q_{s,i}`). The TEMPLATE is `RouteM3333Atom.chartParams3333_injOn`
(`RouteM3333Atom.lean:534`, sorry-free): it recovers all 27 coords off `{u0,u1,u4,u9 ≠ 0}` via the
chartA/B/C matrix entries + the two `2×2` A-frame systems (det = `u1·u4 ≠ 0`). Generalize that
recovery to the opaque-width `chartParamsGen`/`Agen` slot structure + the kLDU-lensed K-cores.

## ⚠️ NAMED RISK — flag-if-walls (lead's instruction)
This is the genuine ∀M-injOn build-risk. If the triangular recovery does NOT generalize off the
(3,3,3,3) anchor to opaque widths — e.g. the coordinate-recovery order / the division-by-pivot
structure breaks for general layer widths — STOP and flag the PRECISE obstruction (the way `hJfront`
was flagged), do NOT fake the injOn or assert it. A wrong InjOn is unsound (H3's φ=u²/2 counterexample
shows a det value never certifies injectivity). Report the exact coordinate/step that won't recover.

## Discipline
Sorry-free, honest. Zero new axioms; `#print axioms interiorLDU_injOn` clean-three. Green-gate the
full `lake build DLNFibre` (name-clash guard on your new top-level names). Build from your WORKTREE
`lean/` via `scripts/lb` (or `lake env lean` on warm oleans if the semaphore contends — lead's note).
Hand genm-r1lower the named atom `interiorLDU_injOn`.
