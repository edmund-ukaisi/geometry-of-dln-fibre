# STEP-0 — pure R-BLOWUP peel reaches the monomial endpoint WITHOUT forming det(QbQbᵀ)

**Thread `genm-sjpure`** (branch off `expedition/aoyagi-full @4faa82fa`, isolated worktree).
Re-ran r1flip's exact-algebra probes (`flip2_coordinate_resolution.py`, `flip3_shared_radial_and_exponents.py`,
sympy 1.14) from the formaliser seat on the corank-2 product anchor `(3,3,3,4)`, binding branch `t=(1,0,0)`.

## VERDICT: PASS — the pure peel reaches normal-crossing with COORDINATE centers only, Gram-det never forms.

`flip2` (the front peel of the layer-1 corank block `Δ0` coupled to the product tail `Zb = W·C2·C3`):
- **(A) corankStep.** Blow up `{Δ0=0}` (a COORDINATE center): `‖(u1·Dp)·Q‖² = u1²·‖Dp·Q‖²` (radial factors
  cleanly, verified `= 0` symbolically, any opaque `Q`). The pivot Schur clear `L·Dp·R = diag(1, dd−ab)`
  with `det L = det R = 1` (UNIT transforms), producing the scalar corank `δ' = dd−ab` from `Dp`'s OWN
  entries. **`det(Q Qᵀ)` appears nowhere** — the Schur complement is unit elimination.  This IS the banked
  `RouteMSJCorankStep.corankStep` (`frobSq((u•fromBlocks A B C D)·Q) = u²·(frobSq(A·Q̃) + frobSq(C·Q̃ + Γ·Qb))`,
  `Γ = schurCompl`), re-confirmed at these widths.
- **(B) ideal split** `⟨[1 ⊕ δ']·Zrows⟩ = ⟨pivot row⟩ + δ'·⟨corank row⟩`, both a depth-2 product core sharing
  `C2·C3`. `δ'` a fresh chart coordinate. No Gram det.
- **(C) end-to-end.** A faithful depth-2 shared-product ideal `⟨B·C⟩` resolves to MONOMIAL generators
  `{ uB·c'_1a, uB·c'_1b, uB·δ_B·c'_2a, uB·δ_B·c'_2b }` in coordinate peels ({B=0}, then free-coord strata):
  NORMAL CROSSING, all centers coordinate, shared radial `uB` divides all four.
- **(D)** shared-`uB` terminal toric value `1.0` < fresh-per-block `2.0` — the shared exceptional divisor
  (Aoyagi's `diag(b)`) gives the correct LOWER value; fresh-per-block undercounts. (Absolute value is in the
  LP's `lct×2` normalisation; the relative `shared < fresh` is the load-bearing fact.)

`flip3`:
- **(1) shared radial, front-first.** Peeling `C2` (`center {C2=0}`) factors ONE radial `u2` from BOTH coupled
  terms `(W1)·C2·C3` and `(W2)·C2·C3` (verified: `u2` divides all entries of both). r1carrier's C10 used
  deepest-first (NOT Aoyagi's order); front-first shares the divisor.
- **(2)** after peeling `C2` the residual is depth-1 (`C3` free) → free-coordinate monomials; 2 coordinate peels.
- **(3) box cutoff (exact).** `(c0 + ‖Γ·Qb‖²)^{−c'} ≤ c0^{−c'}` for a positive core `c0>0`, so the corank
  box integral `≤ c0^{−c'}·(2R)^{pq} < ∞` for EVERY `Qb` (incl. the rank-1 dense-torus `Qb*`), with NO
  `det(Qb Qbᵀ)` factor. The atom divergence is manufactured by integrating `Γ` over full space with `c0`
  ABSENT.
- **(4)** branch exponents `(3,3,3,4) t=(1,0,0)`: charges `4 + 3 + 0 = 7 = minAdm(3,3,3,4)`, threshold `7/2`;
  `c' < 7/2 ⟹ c' < Mval/2` on every divisor ⟹ monomial endpoint converges.

## Consequence for the build

The pure peel does NOT secretly need the Gram det. The build proceeds (no re-opening the wall). The banked
`corankStep` IS the pointwise per-step identity confirmed here; the remaining Lean labour is the
measure-theoretic CARRIER ASSEMBLY (the blow-up chart cover + Jacobian + descent) — the "bookkeeping is the
proof" content, NOT a missing theorem.
