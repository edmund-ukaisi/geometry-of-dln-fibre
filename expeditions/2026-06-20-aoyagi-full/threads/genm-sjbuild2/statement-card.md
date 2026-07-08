# Statement card — R1-UPPER decorated predicate (pieces 1-4 + π=∅ recovery + radial sub-brick)

Thread `genm-sjbuild2`. Module `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJDecorated.lean` @
`7a8f4b45`. Isolated green build (`scripts/lb DLNFibre.DLN.RLCT.Validate.RouteMSJDecorated`,
force-recompiled "Built"); NOT yet wired into the `DLNFibre.lean` aggregator (controller wires).

> **Claim (π=∅ recovery).** The decorated finiteness predicate, at the trivial decoration (no
> exceptional coordinates, identity carrier at the full layer product), is EXACTLY the original
> box-finiteness `RouteMBoxThresholdFinite M`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.decoratedBoxThresholdFinite_trivial_iff`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJDecorated.lean` @ `7a8f4b45`)
> - **Gloss.** `DecoratedBoxThresholdFinite (SJDecoration.trivial M) ↔ RouteMBoxThresholdFinite M`:
>   the decorated integral of the trivial decoration equals `∫ frobSq(prod M A)^{−c'}` over the
>   parameter box (`trivial_integral_eq`), and the carrier threshold `carrierThreshold M = ½·minAdm M`
>   is the same threshold. So the decorated recursion, once it lands the trivial-decoration predicate,
>   delivers `RouteMBoxThresholdFinite M` with no residual gap.
> - **Proved.** The equivalence, unconditionally (all `M`). Plus: `carrierThreshold_shift` (piece 4,
>   the banked soundness cast `carrierThreshold M − ½·peelCharge M u ≤ carrierThreshold (redChain u M)`);
>   `trivial_integral_eq` (the trivial integral IS `routeMLayerBoxIntegral`, via the `unitBox 0` collapse
>   + `loss_ofMatrix`); `radialAttach_decLoss` (the Case-2 radial attach multiplies the decorated loss by
>   `u₀²`, via banked `loss_radialStep`); non-vacuity witness at `d = 1` on `(3,3,4)`.
> - **Assumed.** None (the predicate + recovery are unconditional definitions/equivalences).
> - **Cited.** None in this module (S2-FREE; no `monomial_rlct`, no `cited_aoyagi_dln`). Axiom-clean
>   clean-three `[propext, Classical.choice, Quot.sound]` on every result (forced `#print axioms`).
> - **Deferred (the mountain, pieces 5-6-7-full).** `decorated_peel_step` — the clear-first scalar Schur
>   elimination (`rowMix R` at constant support, carrying the chart's analytic Schur matrix `R`) → radial
>   attach (landed as `radialAttach`) → block split → regime A (`matBox_corank_residual_absZ_le`,
>   exponent shift `c'↦c'−pq/2`) / regime B (`matBox_corank_dominates_absZ_lt_top`, terminal Morse),
>   INCLUDING the `c'=pq/2` boundary ε-argument. And `decorated_base` (terminal dispatch) + the
>   well-founded recursion discharging `sjJointResolution`. This is the ~65-75% genuinely-new CoV
>   (chart change-of-variables); UNBANKED, multi-tide. `sjJointResolution` (`RouteMSJResolution`, still
>   the single named analytic sorry) is UNTOUCHED.
> - **Structure & ideas observed (STEP-0 gate, this thread).** The terminal count↔monomial bridge
>   `½·minAdm(remChain) ≤ monomialThreshold(sharedDivisorExp, jac)` is UNIFORM over all route terminals
>   (`step0-terminal-bridge.md`, exact + toric-LP, GATE PASS): the charge is carried ADDITIVELY by the
>   exponent-shift recursion (regime A) + free-matrix Morse terminal (regime B), and the diagonal
>   monomialThreshold `= ½·min(charges)` (which undercounts multi-peel) is NEVER the operative gate —
>   at free-matrix terminals regime B fires (exponent budget lands at `pq_T/2 = ½·minAdm(remChain term)`
>   via the soundness gate), at collapsed terminals `minAdm(remChain) = 0` makes the bridge trivial.
>   Hence **the carrier threshold depends only on `remChain`, not the decoration** — Codex's named
>   failure mode (decoration must enter the threshold) does NOT fire.
> - **Route.** The decorated recursion (design PINNED in `genm-r1predicate/cert.md`): well-founded on
>   remaining-chain arity, `decorated_peel_step` at internal nodes, `decorated_base` at leaves; π=∅
>   consumer via `decoratedBoxThresholdFinite_trivial_iff` (landed).
> - **Status.** sorry-free (this module); the deferred mountain is a separate multi-tide obligation.
