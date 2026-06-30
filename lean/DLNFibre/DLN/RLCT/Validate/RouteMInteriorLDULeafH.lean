import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLDUContract

/-!
# `RouteMInteriorLDULeafH` — the multi-axis Jacobian exponent vector `lduleafH` (H2a, ∀M-L2)

The fs-INDEPENDENT sub-piece of the R1-LOWER LDU-lensed interior box-divergence: the multi-axis
Jacobian-exponent vector `lduleafH M ha hN : Fin (routeMAmbient M) → ℕ` of the LDU-lensed interior
achiever chart, plus its value at the binding pivot axis.

The exponent vector follows the per-factor determinant bookkeeping of the lensed chart
(`RouteMInteriorLDUContract` header):

* the **radial** blow-up `pivotBlowupOn` contributes `|u_p|^{minAdm−1}` at the pivot axis
  `p = structPivot M hN = ⟨0,_⟩`;
* per Schur boundary `s` (= `k+1`, `k : Fin L`), the lensed K-core diagonal pivot `q_{s,i}` carries
  the **Schur frame** exponent `r_s + c_s` (`schurFrameDeriv_det` gives `|det K|^{r+c}` and the LDU
  lens makes `det K = ∏_i q_i`, banked `kLens_det`) PLUS the **LDU core** exponent `2·(t_s − 1 − i)`
  (`lduCoreDeriv_det` gives `∏_i |q_i|^{2(t−1−i)}`), i.e. `(r_s + c_s) + 2·(t_s − 1 − i)` at the
  K-diagonal flat slot `(s, q_{s,i})`;
* every other (spectator) flat axis carries `0`.

Here the boundary-`s` widths (frame boundary `s = k+1`, `k : Fin L`) are
`t_s = Text M (tach M) (k+2)` (the K-core size),
`r_s = Text M (tach M) (k+1) − Text M (tach M) (k+2)` (the residual rows),
`c_s = Wext M (k+1) − Text M (tach M) (k+2)` (the residual columns) — exactly the `frameSplitEquiv`
role widths.

The construction mirrors the banked interior witness `wOnIdx`/`wInt`
(`RouteMAchieverWitnessInterior`): a `ChartIdx`-indexed placement `lduleafHOnIdx` (K-branch diagonal
entry → the exponent, else `0`) composed with the chart bijection `chartIdxEquiv`, with the pivot
axis OVERRIDDEN to the radial value `minAdm − 1`. The override-at-pivot keeps the radial bookkeeping
separate from the K bookkeeping (the radial axis is read directly as `x ⟨0⟩`, not through
`chartIdxEquiv`), and makes the pivot value `if_pos rfl`.

This file is fs-INDEPENDENT (it never touches the factor list `fs` / `interiorLDU_factors`): it
supplies the two named atoms `lduleafH` and `lduleafH_pivot` that `RouteMInteriorLDUContract`'s
`interiorLDU_leafH` / `interiorLDU_leafH_pivot` are wired to (one-liner
`interiorLDU_leafH := lduleafH`).

Axiom-clean `[propext, Classical.choice, Quot.sound]` target (finite equivalences + ℕ arithmetic; no
analysis). The exponent values are pinned to the per-factor dets by the SEPARATE det-bookkeeping
atom (`ldu_det_bookkeeping`, H2b — not in this file).
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators

variable {L : ℕ}

/-! ## The `ChartIdx`-indexed K-diagonal exponent placement -/

/-- **The `ChartIdx`-indexed exponent placement** for the LDU-lensed interior chart. At a frame slot
(`Sum.inl s`), boundary `k : Fin L`, the K-role branch (`Sum.inl (Sum.inl (Sum.inl qK))`) decodes
the matrix index `(i,j) = finProdFinEquiv.symm qK`; on the diagonal `i = j` it returns the per-pivot
exponent `(r_s + c_s) + 2·(t_s − 1 − i)` — the Schur frame `r_s+c_s` (`|det K|^{r+c}`) plus the LDU
core `2(t_s−1−i)` (`∏_i |q_i|^{2(t−1−i)}`) — at boundary `s = k+1` with widths
`t_s = Text M (tach M) (k+2)`, `r_s = Text M (tach M) (k+1) − Text M (tach M) (k+2)`,
`c_s = Wext M (k+1) − Text M (tach M) (k+2)`. Every off-diagonal K entry, the X/N/E roles, and the
lift slot carry `0`. (Mirrors the banked witness `wOnIdx`.) -/
noncomputable def lduleafHOnIdx (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) :
    ChartIdx M (tDesc M (tach M)) → ℕ := fun q =>
  match q with
  | ⟨k, Sum.inl s⟩ =>
    match frameSplitEquiv M (tach M) (k.val + 1) (ha.hdesc k.val k.isLt) (ha.hub k.val) s with
    | Sum.inl (Sum.inl (Sum.inl qK)) =>  -- K role
      let ij := finProdFinEquiv.symm qK
      if ij.1 = ij.2 then
        (Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2))   -- r_s
          + (Wext M (k.val + 1) - Text M (tach M) (k.val + 2))         -- c_s
          + 2 * (Text M (tach M) (k.val + 2) - 1 - ij.1.val)           -- 2·(t_s − 1 − i)
      else 0
    | _ => 0  -- X, N, E roles
  | ⟨_, Sum.inr _⟩ => 0  -- lift slot

/-! ## The flat-coordinate exponent vector `lduleafH` -/

/-- **H2a — the multi-axis Jacobian exponent vector** for the LDU-lensed interior chart:
`lduleafH = radial(minAdm−1) at the pivot ⊕ per-boundary[(r_s+c_s) + 2(t_s−1−i)]` on the lensed
K-diagonal flat slots, `0` on spectator axes. The pivot axis `p = structPivot M hN = ⟨0,_⟩` is
overridden to the radial blow-up exponent `minAdm M − 1` (the radial axis is read directly as
`x ⟨0⟩`, not through `chartIdxEquiv`); every non-pivot axis takes the `ChartIdx`-placed K-diagonal
exponent `lduleafHOnIdx`.

(Validated at `(3,3,3,3)`: `|u0|⁵·|u1|⁴·|u4|²·|u9|³` — radial `5 = minAdm−1` at axis `0`; the
`2×2`-core boundary `r+c = 2 → {4, 2}` at the two diagonal pivots; the `1×1`-core boundary
`r+c = 3 → {3}`.) -/
noncomputable def lduleafH (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (hN : 0 < routeMAmbient M) : Fin (routeMAmbient M) → ℕ := fun j =>
  if j = structPivot M hN then
    minAdm M - 1
  else
    lduleafHOnIdx M ha (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL j)

/-- **H2a — the binding axis carries `minAdm−1`** (the radial blow-up exponent at the pivot). The
pivot override is `if_pos rfl` — `lduleafH M ha hN (structPivot M hN) = minAdm M − 1`. -/
theorem lduleafH_pivot (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (hN : 0 < routeMAmbient M) :
    lduleafH M ha hN (structPivot M hN) = minAdm M - 1 := by
  rw [lduleafH, if_pos rfl]

end DLNFibre.DLN.RLCT
