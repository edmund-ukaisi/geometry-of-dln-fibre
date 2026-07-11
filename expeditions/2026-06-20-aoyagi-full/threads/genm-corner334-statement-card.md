# Statement card — `(3,3,3,4)` `t=1` decorated corner-slice (genm-corner334)

Module: `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJCorner334.lean` (221 LoC).
Base commit `e67a2a42` (`expedition/aoyagi-full`); file delivered uncommitted for the controller to bank.
Axioms: clean three `[propext, Classical.choice, Quot.sound]` on every headline (forced `#print axioms`,
oleans deleted first — no stale mask). Zero `sorry`/`axiom`/`native_decide`. Builds in isolation and in
the full `DLNFibre` aggregator (no sibling name clash).

---

> **Claim.** The `(3,3,3,4)`, binding-cut `t=1`, decorated corner-slice fiber integral — the additive
> two-block corner loss `u₀²·U₀ + u₁²·U₁` with the accumulated radial Jacobian `|u₀|³·|u₁|²` and the
> deep-data units `U₀ = ‖w₁ᵥ*A₂‖² + δ²‖w₂ᵥ*A₂‖²`, `U₁ = a_piv²‖v̄ᵥ*A₂‖²` — is finite (`< ⊤`) for every
> `c' < 7/2 = ½·minAdm(3,3,3,4)` on the full-row-rank sector of the deep data `A₂`, and the `A₂`-rank-drop
> complement routes to an explicit named deeper-stratum hypothesis.

- **Lean (headlines):**
  - `DLNFibre.DLN.RLCT.sjCorner334_sector_fiber_lt_top` — the sector fiber, UNCONDITIONAL at `7/2`.
  - `DLNFibre.DLN.RLCT.sjCorner334_fiber_lt_top_of_deeper` — the stratified cover (sector ⊔ rank-drop).
  - `DLNFibre.DLN.RLCT.sjLoss_indicator_two_block` — the min→sum crux at the carrier level.
  - `DLNFibre.DLN.RLCT.cornerUnits_pos` — units bounded below ⇔ full row rank.
  - (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJCorner334.lean` @ `e67a2a42`, file pending bank)

- **Gloss.**
  - `sjLoss_indicator_two_block`: recording the block-additive support with the **indicator** columns
    `![1,1,0]`, `![0,0,1]` (banked `prependColumn`) factors the terminal loss as the SUM
    `u₀²·(b₀²+b₁²) + u₁²·(b₂²)` — each block owns its own fresh divisor, the two NOT shared. (Contrast the
    banked `sjLoss_prependColumn_one` = the `radialAttach` all-ones column → the MULTIPLICATIVE
    `u₀²·(reduced)` → the `3/2` undershoot `sjSlice334_symmetric_undershoot`.)
  - `cornerUnits_pos`: with `A₂` full row rank (`Function.Injective A₂.vecMul` = rows independent) and
    the test directions `w₁, v̄` nonzero and `a_piv ≠ 0`, both `cornerUnit0` and `cornerUnit1` are `> 0`.
  - `sjCorner334_sector_fiber_lt_top`: on the sector `{A₂ : full row rank}`, `∫⁻_{u∈box}
    (u₀²U₀+u₁²U₁)^{−c'}·|u₀|³|u₁|² < ⊤` for `c' < 7/2`. Via `cornerUnits_pos` → the banked additive-corner
    endpoint `sjSlice334_corner_lintegral_lt_top` with the constant lower bound `a = min(U₀,U₁)`.
  - `sjCorner334_fiber_lt_top_of_deeper`: for EVERY `A₂`, the fiber is `< ⊤`, PROVIDED the rank-drop
    complement is routed. Proof exhibits the cover `{Injective A₂.vecMul} ⊔ {¬Injective}`: the sector
    branch is the previous theorem (unconditional); the complement branch (`¬Injective` = rank-drop) is
    the **named hypothesis `hDeeper`**.

- **Proved (unconditional).** (i) The min→sum carrier identity: indicator `prependColumn` → additive
  two-block loss. (ii) Full row rank ⇒ deep units strictly positive. (iii) The SECTOR fiber finiteness at
  the honest branch threshold `7/2 = ½·minAdm(3,3,3,4)` (banked charge `sjSlice334_minAdm_eq : minAdm
  ![3,3,3,4] = 7`), via the banked weighted-AM-GM additive-corner endpoint (the codimensions ADD:
  `4 + 3 → 7`, min-cut weights `(4/7,3/7)`). Non-vacuity witness in-file (`A₂ = 1`, `w₁=v̄=![1,1]`).

- **Assumed (hypotheses the claim also needs).** Full row rank on the sector (`Function.Injective
  A₂.vecMul`); nonzero test directions `w₁, v̄` and `a_piv ≠ 0` (else the units can vanish even at full
  rank). Constant-in-radial units — the **fixed vertical slice** (angular/deep data fixed); the general
  case integrates over that data (Tonelli), the follow-on.

- **Cited.** none reproved here — S2-FREE (no `monomial_rlct`, no `cited_aoyagi_dln`). This is
  box-finiteness at the branch threshold only; the `rlct = ½·codim` reading stays Cited.

- **Deferred (named, not omitted).** (1) The `A₂`-rank-drop complement `{¬ Injective A₂.vecMul}`, routed
  to the named hypothesis `hDeeper` — in the general recursion it is a strictly-deeper corank stratum
  (higher `Mval`, threshold `≥ ½·minAdm`), NOT an a.e.-drop (the weight is unbounded near it). (2) The
  general `∀`-block indicator lemma + the decorated arity driver over the admissible class. (3) The `m>2`
  blockwise-polar wrapper (`corner_block_cube_lintegral_lt_top`). (4) The Tonelli assembly integrating the
  fiber over the deep/angular data.

- **Soundness note (the RLCT-collapse trap avoided).** The additive-corner endpoint's proof is the
  weighted AM-GM where the two codimensions ADD (`→ 7/2`); an independent scalar split of the two divisors
  would take the MIN (`→ 3/2`, the `z²(x²+y²)` collapse). The units-bounded-below hypothesis pins the
  coupled (additive) branch; the `A₂`-rank-drop complement (where the units lose their lower bound) is
  stratified OFF via the explicit cover, never averaged in. The log-borderline `c' = ab/2 = 2` is strictly
  below `7/2`, so the strict `c' < 7/2` carries no borderline hole (the additive endpoint is uniformly
  valid, no regime switch at `ab/2`).

- **Status.** sorry-free (reviewer fidelity check pending).
