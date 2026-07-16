# genm-intcell — statement card

The interior `h_int` arm of the coupled b-split. This card covers the ONE genuinely-new
analytic atom landed by the tide (`radial_morse_critical_power_le`, couplerad §w3-boundary R3/R4).
The full arm (`GenericCellFinite` for interior cells) is a larger deep-structure build (the "mountain") —
scoped below; the atom is the leaf it consumes.

---

## Card 1 — the unified interior `+ub` residual-power atom (LANDED)

> **Claim.** For a Euclidean Morse block `P : Fin (m+1) → ℝ` over the box `[−T,T]^{m+1}`, a
> strictly-positive core `w > 0`, and ANY exponent `c'`, with a residual exponent `ε` satisfying
> `0 < ε ≤ c'` and `c' − ε < (m+1)/2`,
> `∫⁻_{[−T,T]^{m+1}} (∑ᵢ Pᵢ² + w)^{−c'} dP ≤ ofReal( w^{−ε} · C )`, where `C = ∫_{ball_R} ‖P‖^{−2(c'−ε)}`
> (`R = √((m+1)T²)+1`) is a finite, `w`-independent constant. This is the `2q ≤ ub` companion of the
> banked `radial_morse_residual_power_le` (`2q > ub`); the `ε`-parameter UNIFIES all three couplerad
> regimes ①②③ (including the boundary log `c' = (m+1)/2`, i.e. `2q = ub`), folding the log into `w^{−ε}`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.radial_morse_critical_power_le` (box form) and
>   `DLNFibre.DLN.RLCT.lintegral_ball_critical_le` (ball-form core)
>   (`lean/DLNFibre/DLN/RLCT/Validate/RadialCriticalPower.lean` @ `49019b5668d71f3c5f81b7fbd8398a74742544d1`)
> - **Gloss.** The critical/sub-critical box integral of `(∑Pᵢ²+w)^{−c'}` is dominated by a residual
>   power `w^{−ε}` of the core, times a `w`-independent ball constant. The residual exponent `ε` can be
>   taken as small as one likes (any `ε > 0` at the critical `c' = (m+1)/2`), which is what lets the deep
>   sub-chain threshold `½·minAdm(![u+a,u,d])` absorb it in the composition.
> - **Proved.** Both statements unconditionally (sorry-free, axiom footprint `[propext,
>   Classical.choice, Quot.sound]`). The pointwise a.e. bound `(‖P‖²+w)^{−c'} ≤ w^{−ε}·‖P‖^{−2(c'−ε)}`
>   (off the null point `P = 0`) via `Real.rpow_le_rpow_of_nonpos` twice; the constant finite via the
>   banked `euclidND_ball_integrable` (`c'−ε < (m+1)/2`); the box→ball transport verbatim from
>   `radial_morse_residual_power_le` (`PiLp.volume_preserving_toLp` + box ⊆ `ball 0 R`).
> - **Assumed.** `0 < ε ≤ c'`, `c' − ε < (m+1)/2`, `w > 0`, `T > 0`. (The ε-window is nonempty exactly
>   when `2c' < ub + minAdm(![u+a,u,d])` — corankrec's QIP `minAdm_le_inf_pivot_qip` certifies this at
>   every interior cell; that check lives in the composition, not this atom.)
> - **Cited.** none. S2-FREE: the only analytic input is `euclidND_ball_integrable` (⟵ `radial_ball_iff`
>   ⟵ Mathlib `integrable_fun_norm_addHaar`). NATIVE — no `cited_aoyagi_dln`.
> - **Deferred.** none, for the atom. (The atom is isotropic `∑Pᵢ²+w` and `Q_b`-agnostic by design; the
>   per-row-`(Q_bQ_bᵀ)^{1/2}` CoV that makes `‖B̃Q_b‖²` isotropic, and the Tonelli composition over
>   `(E,Y)`, live UPSTREAM — see Card 2.)
> - **Structure & ideas observed (couplerad §w3-boundary).** The load-bearing step is the exponent split
>   `−c' = −ε + (−(c'−ε))`: `(‖P‖²+w)^{−ε} ≤ w^{−ε}` (base `≥ w`) and `(‖P‖²+w)^{−(c'−ε)} ≤ ‖P‖^{−2(c'−ε)}`
>   (base `≥ ‖P‖²`, needs `ε ≤ c'`). corankrec's decorrelated verification: the atom SUBSUMES all three
>   regimes for `w > 0` (the regime split dissolves into the ε-parameter); `radial_morse_residual_power_le`
>   (③) becomes a cross-check, not a dependency. Numerically pre-verified (pointwise + integral, showing
>   the critical-log growth of `I(w)` dominated by `C_ε·w^{−ε}`).
> - **Route (coordinator).** Build the isotropic box atom first (green + clean-three), mirroring
>   `radial_morse_residual_power_le`; the CoV/Tonelli/RectSchurCore composition wires it afterward.
> - **Status.** sorry-free (awaiting fidelity review).

---

## Card 2 — the interior `h_int` arm / free-box (SCOPED, NOT yet landed)

> **Target.** `GenericCellFinite M (t+j) c'` on generic interior cells (`a+b ≤ deepTailMin M`,
> `a = M₀−(t+j)`, `b = M₁−(t+j)`), i.e. `∫_cell coupledBoxIntegrand M (t+j) c' < ⊤`. Both b-split arms
> (`h_int_b1`: `b = 1`; `h_int_b2`: `b ≥ 2`) of `routeMBoxThresholdFinite_of_coupled_bsplit`
> (`RouteMSJHcellNull.lean`).
>
> - **Reduction (banked pieces, on base @a070b639a).** `coupledBox_cell_lt_top_of_generic` (null cells
>   `∫=0`) + `coupledBox_le_frontCharge` (a.e., needs `hGae_cell_interior` + `hEtop` a.e.) +
>   `frontCharge_cell_lt_top_of_freebox` (cell ⟸ whole-box) reduce the arm to the **per-cell terminal
>   finiteness** `∫_cell frontChargeIntegrand M u c' < ⊤` for the generic (deepest, `k=ρ`) interior cell.
> - **The remaining content (the mountain).** `frontChargeIntegrand = ∫_x [det(Q_bQ_bᵀ)^{−a/2} ·
>   Cresid(ab)c' · (E_top+E_tr)^{−q}]`, `q = c'−ab/2`. couplerad §w3-boundary reduces it (R1 Frobenius-
>   orthogonal split → `E_top = frobSq(P·Y)+frobSq(B̃·Q_b)`, `E_tr = frobSq(C·Y)`, `Y = z0·Z_deepΠ`; R2
>   deep CoV `z0↦Y`; Φ-Fubini + box-sandwich; charge-through-recursion at `δ=0` via det-monotonicity on
>   the PSD Gram; the per-row-`(Q_bQ_bᵀ)^{1/2}` CoV `‖B̃Q_b‖²→‖w‖²` with Jac `det(Q_bQ_bᵀ)^{−u/2}`;
>   Tonelli over `(E,Y)`) to `Card 1` (the ε-atom) + `rectCore_schurGen_lt_top (u+a) u d ε` (banked) +
>   the QIP `minAdm_le_inf_pivot_qip` (banked, certifies the ε-window nonempty).
> - **Cited.** none intended (NATIVE — only the codim LOWER bound is used).
> - **Deferred (NOT done).** R1, R2, Φ-Fubini, the charge-through-recursion, the per-row G^{1/2} CoV,
>   and the Tonelli assembly. Entangled with `hsQ`/`deeperFlagZdeep`/`E_top`/`E_tr` and under active build
>   by several interior threads (intloss, intmtn, schurB, slabD). Ownership/next-boundary flagged to the
>   coordinator.
> - **Build notes for the mountain (couplerad, machine-ε verified — bank when building).**
>   - **Per-row CoV — do NOT use `Matrix.PosDef.sqrt`** (spectral → the `IsHermitian.eigenvalues` whnf /
>     D-C friction trap). Use the **LQ/Cholesky co-isometry factor** `L` of `Q_b`: `Q_b = L·Q̃`
>     (`L` = `b×b` factor, `LLᵀ = Q_bQ_bᵀ`; `Q̃ = L⁻¹Q_b` row-orthonormal, `Q̃Q̃ᵀ = I_b`). Then `w := B̃·L`
>     (`u×b`) gives `‖B̃·Q_b‖² = ‖B̃·L‖² = ‖w‖²` (co-isometry kills `Q̃`) and Jac `= det(L)^u`,
>     `det(L)² = det(Q_bQ_bᵀ)` ⟹ Jac `= det(Q_bQ_bᵀ)^{u/2}` — SAME constant as the spectral route, friction-free.
>     **Reuse slabD's LQ/co-isometry lemma** (genm-schurcore-D, `corankSlabD_charge_sint_le`; `Q_b = A_cor·Z_deep`
>     is the same `b×n` full-row-rank shape as slabD's `A = R·Q`). The factor CoV is on RAW-PI → `EuclideanSpace`
>     (Matrix.module diamond, per lean/CLAUDE.md), NOT `Matrix.module`.
>   - **The circumscribe** (ellipsoid `w`-image ⊆ `ball R₀`) is a one-liner: `lintegral_mono_set` on top of
>     `lintegral_ball_critical_le` (Card 1) — no new content.
>   - **R1 Frobenius split** (`E_top = frobSq(P·Y)+frobSq(B̃·Q_b)`, `E_tr = frobSq(C·Y)`; `B̃ = B₁₂+P·Ã_z`,
>     `Ã_z = Q_inl·Q_bᵀ(Q_bQ_bᵀ)⁻¹`, cross-term `0` via `Q_b·Π = 0`) — couplerad holds the machine-ε-verified
>     identity, to be pinned against corankrec's exact `hsQ`/`Q_inl`/`Q_b`/`Π` object names once the boundary is set.
> - **Status.** scoped; atom (Card 1) landed as the leaf.
