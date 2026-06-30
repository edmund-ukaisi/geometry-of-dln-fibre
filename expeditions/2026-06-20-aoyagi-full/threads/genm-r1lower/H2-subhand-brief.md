# H2 sub-hand brief — multi-axis `leafH` + per-factor det bookkeeping (∀M-L2)

**Base:** branch off genm-r1lower's pushed tip (the controller will give the exact branch/ref). The
skeleton `lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLDUContract.lean` builds green with 9 stated
`sorry`s and FROZEN signatures.

**MODULE BOUNDARY (lead's collision-guard):** you do NOT edit `RouteMInteriorLDUContract.lean`. You
prove your results as **named atoms in your OWN new file** (suggested
`lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLDULeafH.lean`), importing the skeleton's defs.
genm-r1lower (H1) then imports your file and wires your atoms into its `sorry`s at assembly. Match the
EXACT shapes below so the wiring is a one-liner.

## Your atoms (define + prove in your file)

### (H2a) the multi-axis exponent vector + its pivot value — INDEPENDENT of `fs`, START NOW
Provide a def and a lemma the skeleton's `interiorLDU_leafH`/`interiorLDU_leafH_pivot` will be set to:
```
noncomputable def lduleafH (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (hN : 0 < routeMAmbient M) : Fin (routeMAmbient M) → ℕ := …
theorem lduleafH_pivot (M …) (ha …) (hN …) :
    lduleafH M ha hN (structPivot M hN) = minAdm M - 1 := …
```
The exponent vector: `radial(minAdm−1)` at the pivot `structPivot M hN`, `(r_s+c_s) + 2(t_s−1−i)` at the
lensed K-diagonal flat slot `(s, q_{s,i})`, `0` elsewhere. Widths: `r_s = Text M (tach M) s − Text M
(tach M) (s+1)`, `c_s = Wext M s − Text M (tach M) (s+1)`, `t_s = Text M (tach M) (s+1)`. K-diagonal
slots via `chartIdxEquiv` + the K-branch `frameSplitEquiv (Sum.inl(Sum.inl(Sum.inl …)))` at `(i,i)` —
cf. `kLDU`'s decode (`RouteMKLens.lean:67`). VALIDATED at (3,3,3,3): `|u0|⁵·|u1|⁴·|u4|²·|u9|³` (radial 5;
2×2-core boundary r+c=2→{4,2}; 1×1-core boundary r+c=3→{3}; numeric check in this thread's gate verdict).
Pivot lemma mirrors banked `leafH3333_pivot`/`RouteMBudget.leafH_pivot` (#165).

### (H2b) the per-factor det bookkeeping — WAITS on H1's `fs`
```
theorem ldu_det_bookkeeping (M …) (ha …) (hN …) (u : Fin (routeMAmbient M) → ℝ) :
    ((foldDerivList (interiorLDU_factors M ha hN) u).map
        (fun D ↦ |LinearMap.det D.toLinearMap|)).prod = ∏ j, |u j| ^ (lduleafH M ha hN j) := …
```
Consumes H1's `interiorLDU_factors` (the ordered factor list) — **do not start H2b until H1 publishes
`fs`** (genm-r1lower will ping). Then MECHANICAL: each factor's abs-det is a banked monomial — radial
`pivotBlowupOn_abs_det = |u_p|^{minAdm−1}`; Schur on the lensed K `schurFrame_abs_det = |det K|^{r+c}`
with `det K = ∏q_i` (`readK_kLDU_det`); LDU `lduCoreDeriv_det = ∏|q_i|^{2(t−1−i)}`; chain `= 1`. Multiply
(prefix-evaluated via `foldDerivList_cons`/`composeFold_abs_det`/`cleConjFactor_abs_det`), collect per-axis
exponents `(r+c)+2(t−1−i)` → `∏_j|u_j|^{lduleafH_j}`.

## Discipline
Sorry-free, honest. Zero new axioms. Green-gate the FULL `lake build DLNFibre` (name-clash guard — your
new file's top-level names must not clash). `#print axioms` on `ldu_det_bookkeeping` clean-three (no S2).
Build from the WORKTREE `lean/` via `scripts/lb`. The exponent arithmetic is load-bearing — derive
`(r+c)+2(t−1−i)` from the banked per-factor dets, don't assert it. Hand genm-r1lower the two named atoms
(`lduleafH`+`lduleafH_pivot`, `ldu_det_bookkeeping`); H1 wires them in (sets `interiorLDU_leafH :=
lduleafH`, etc.).
