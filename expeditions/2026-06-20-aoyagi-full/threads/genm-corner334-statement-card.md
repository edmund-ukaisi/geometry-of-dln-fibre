# Statement card — `(3,3,3,4)` `t=1` decorated corner-slice (genm-corner334)

Module: `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJCorner334.lean` (~330 LoC).
Base commit `e67a2a42` (`expedition/aoyagi-full`); file delivered uncommitted for the controller to bank.
Axioms: clean three `[propext, Classical.choice, Quot.sound]` on every headline (forced `#print axioms`,
oleans deleted first — no stale mask). Zero `sorry`/`axiom`/`native_decide`. Builds in isolation and in
the full `DLNFibre` aggregator (no sibling name clash).

Revised after reviewer `corner334-review` (decorrelated) escalations: the earlier fixed-slice cover
`sjCorner334_fiber_lt_top_of_deeper` was DROPPED (false-premise — see below), the divergence direction was
ADDED (the sharp boundary), the "units ⇔ full rank" prose corrected to one-directional, and `_fiber`
renamed to `_slice`.

---

> **Claim.** The `(3,3,3,4)`, binding-cut `t=1`, decorated corner-slice fiber integral — the additive
> two-block corner loss `u₀²·U₀ + u₁²·U₁` with radial Jacobian `|u₀|³·|u₁|²` and deep-data units
> `U₀ = ‖w₁ᵥ*A₂‖² + δ²‖w₂ᵥ*A₂‖²`, `U₁ = a_piv²‖v̄ᵥ*A₂‖²` — is finite (`< ⊤`) for every
> `c' < 7/2 = ½·minAdm(3,3,3,4)` on the full-row-rank sector of `A₂`, and DIVERGES (`= ⊤`) when a unit
> vanishes and `c'` is at/above the corresponding boundary — so the units-positive hypothesis is sharp on
> the fixed slice; the `A₂`-rank-drop complement's finiteness is a joint (Tonelli) follow-on obligation.

- **Lean (headlines):**
  - `DLNFibre.DLN.RLCT.sjCorner334_sector_slice_lt_top` — the sector slice, UNCONDITIONAL at `7/2`.
  - `DLNFibre.DLN.RLCT.cornerSlice334_eq_top_of_unit1_zero` — divergence: `U₁=0<U₀`, `c'≥2` ⟹ `⊤`.
  - `DLNFibre.DLN.RLCT.cornerSlice334_eq_top_of_unit0_zero` — divergence: `U₀=0<U₁`, `c'≥3/2` ⟹ `⊤`.
  - `DLNFibre.DLN.RLCT.sjLoss_indicator_two_block` — the min→sum crux at the carrier level.
  - `DLNFibre.DLN.RLCT.cornerUnits_pos` — full row rank + nonzero test dirs ⟹ units `> 0` (one-directional).
  - (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJCorner334.lean` @ `e67a2a42`, file pending bank)

- **Gloss.**
  - `sjLoss_indicator_two_block`: recording the block-additive support with the **indicator** columns
    `![1,1,0]`, `![0,0,1]` (banked `prependColumn`) factors the terminal loss as the SUM
    `u₀²·(b₀²+b₁²) + u₁²·(b₂²)` — each block owns its own fresh divisor, the two NOT shared. (Contrast the
    banked `sjLoss_prependColumn_one` = `radialAttach` all-ones → MULTIPLICATIVE `u₀²·(reduced)` → `3/2`.)
  - `cornerUnits_pos`: with `A₂` full row rank (`Function.Injective A₂.vecMul` = rows independent) and the
    test directions `w₁, v̄` nonzero and `a_piv ≠ 0`, both `cornerUnit0` and `cornerUnit1` are `> 0`. This
    is a SUFFICIENT condition only — the converse fails (a rank-deficient `A₂` not annihilating the test
    vectors also gives positive units), so it is NOT an `iff`.
  - `sjCorner334_sector_slice_lt_top`: on the sector `{A₂ : full row rank}` (+ nonzero test dirs),
    `∫⁻_{u∈box} (u₀²U₀+u₁²U₁)^{−c'}·|u₀|³|u₁|² < ⊤` for `c' < 7/2`. Via `cornerUnits_pos` → the banked
    additive-corner endpoint `sjSlice334_corner_lintegral_lt_top` with constant lower bound `a = min(U₀,U₁)`.
  - `cornerSlice334_eq_top_of_unit1_zero` / `_unit0_zero`: if a unit vanishes (e.g. `A₂` rank-drop
    annihilating `v̄`, so `U₁=0`), the slice is `⊤` for `c'` at/above the boundary (`c'≥2` for `U₁=0`;
    `c'≥3/2` for `U₀=0`) — via the banked box divergence `monomialIntegrand_lintegral_box_eq_top_of_axis`
    (the loss collapses to a single-axis monomial whose marginal `∫₀¹ u^{h−2c'}` diverges).

- **Proved (unconditional).** (i) The min→sum carrier identity: indicator `prependColumn` → additive
  two-block loss. (ii) Full row rank + nonzero test dirs ⇒ deep units `> 0`. (iii) The SECTOR slice
  finiteness at `7/2 = ½·minAdm(3,3,3,4)` (banked charge `sjSlice334_minAdm_eq : minAdm ![3,3,3,4] = 7`),
  via the banked weighted-AM-GM additive-corner endpoint (codimensions ADD, `4+3 → 7`). (iv) The DIVERGENCE
  directions — a vanishing unit forces `⊤` below `7/2` — so the units-positive hypothesis is NECESSARY on
  the fixed slice, not just sufficient. Both non-vacuity witnesses in-file (sector: `A₂=1`; divergence:
  `A₂ = diagonal ![1,0]`, `U₁=0`, the reviewer's boundary witness).

- **Assumed (hypotheses the claim also needs).** Sector = `Function.Injective A₂.vecMul` (full row rank) +
  `w₁, v̄` nonzero + `a_piv ≠ 0`. Constant-in-radial units = the **fixed vertical slice** (angular/deep data
  fixed).

- **Cited.** none reproved here — S2-FREE (no `monomial_rlct`, no `cited_aoyagi_dln`). Box-finiteness at the
  branch threshold only; the `rlct = ½·codim` reading stays Cited.

- **Deferred (named, not omitted).** (1) The `A₂`-rank-drop complement is **not finite fixed-slice by
  fixed-slice** (the divergence lemmas show `⊤` for `c' ∈ [2,7/2)`); its finiteness is a JOINT obligation
  (integrated over the deep data `A₂`, Tonelli, at the deeper stratum's threshold), deferred to the
  general recursion — NOT a fixed-slice hypothesis, NOT an a.e.-drop. (2) The general `∀`-block indicator
  lemma + decorated arity driver over the admissible class. (3) The `m>2` blockwise-polar wrapper
  (`corner_block_cube_lintegral_lt_top`). (4) The Tonelli assembly over the deep data.

- **Precision note (no clean `iff`).** Finiteness is NOT `⟺ (U₀>0 ∧ U₁>0)` on the nose: the degenerate
  `U₀=U₁=0` case has loss ≡ 0, so the integrand is `0` and the slice integral is `0 < ⊤` (finite). The two
  directional lemmas (finite when both units `>0`; `⊤` when exactly one vanishes near the threshold) map the
  boundary honestly without forcing a false biconditional.

- **Soundness note (the RLCT-collapse trap avoided).** The additive-corner endpoint's proof is the weighted
  AM-GM where the two codimensions ADD (`→ 7/2`); an independent scalar split would take the MIN (`→ 3/2`,
  the `z²(x²+y²)` collapse). The units-positive hypothesis pins the coupled (additive) branch; where a unit
  vanishes the slice genuinely diverges (the divergence lemmas), so the complement is stratified off via the
  joint follow-on, never averaged in. An earlier fixed-slice "cover" hypothesis `hDeeper : ¬injective → (<⊤)`
  was DROPPED as false-premise: its conclusion is itself false for `c' ∈ [2,7/2)`.

- **Status.** sorry-free (reviewer re-check pending on the revision).
