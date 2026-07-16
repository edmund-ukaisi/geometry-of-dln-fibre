# genm-corankrec — statement card: item-4 `hfin` (coupled per-cell finiteness)

Thread `genm-corankrec` (aoyagi-full Stage 2/3a). Formalises the item-4 interface — the coupled
per-deep-cell finiteness that is the SOLE hypothesis of G2 (`frontChargeBox_lt_top_of_hfin`), and the
LAST substantive analytic content of the arity≥4 `(□)` discharge. Route A (corank recursion), design
`genm-couplerad/couplerad-cert.md` §2/§4/§5/§8.

---

> **Claim (interface).** The coupled per-cell finiteness `hfin` that G2 consumes — at a binding-shell
> cut `u = t+j` (`1 ≤ j < r`, `r = min(M₀−t, M₁−t)`, rankgen `a+b ≤ ρ−1`), in the top-`c'` window
> `(M₀−u)(M₁−u)/2 < c' < ½·minAdm M` — is EXACTLY `frontChargeBox_lt_top_of_hfin`'s `hfin` slot.
>
> - **Lean:** `DLNFibre.DLN.RLCT.coupled_hfin`, `coupled_hfin_cell`, `BindingShell`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJCorankRec.lean` @ `84d335b2b`)
> - **Gloss.** For a chain `M : Fin (L+1+1+1) → ℕ`, a nondegenerate binding cut `t` (`hbind`,
>   `t+1 ≤ min(M₀,M₁)`), and an interior shell `1 ≤ j < r` with rankgen, at every deep-atlas cell
>   `i : CRIndex (dropHead (redChain (t+j) M))` the coupled front-charge box integral
>   `∫_{p ∈ box ∩ projDeep⁻¹'(deepCell i)} frontChargeIntegrand M (t+j) c' p` is finite, in the window
>   `(M₀−(t+j))(M₁−(t+j))/2 < c' < carrierThreshold M`.
> - **Proved.** The interface's TYPE-fidelity: an in-file `example` proves
>   `frontChargeBox_lt_top_of_hfin M (t+j) c' (coupled_hfin M t j c' hshell hc'lo hc'hi)` typechecks —
>   `coupled_hfin`'s output IS G2's `hfin` slot, so arch1build's assembly composes with no bridge.
>   `coupled_hfin = fun i => coupled_hfin_cell … i` (the `∀ i` form over the finite cell family).
>   Signature green-gated (`lean/scripts/lb`, exit 0), NATIVE (no `cited_aoyagi_dln`), no name clash.
> - **Assumed (carried as hypotheses, load-bearing).**
>   - `BindingShell M t j` = { `htb : t+1 ≤ min(M₀,M₁)`; `hbind : minAdm M = peelCharge M t + minAdm
>     (redChain t M)`; `hj1 : 1 ≤ j`; `hjr : j < min(M₀−t, M₁−t)`; `hrankgen : (M₀−(t+j)) +
>     (M₁−(t+j)) + 1 ≤ deepTailMin M` }. The binding-shell + rankgen scope is LOAD-BEARING (couplerad
>     §5, Codex-red-teamed): off it the charge lowers the codim below the floor (CE `(6,8,5,5) u=5`, a
>     non-binding cut). Boundary cuts `j=0`/`j=r` are OUTSIDE this scope — arch1build's separate `hbdryFin`.
>   - `hc'lo : (M₀−u)(M₁−u)/2 < c'` (the LINK's block-charge lower window) and
>     `hc'hi : c' < carrierThreshold M = ½·minAdm M` (the shell threshold upper window).
> - **Cited.** None. NATIVE — the per-cell RLCT-codim LOWER bound is elementary `∫ r^{c−1−2q} dr < ∞`
>   per chart; `cited_aoyagi_dln` (the `rlct = ½·codim` equality) is NOT used.
> - **Deferred (the mountain, ONE documented `sorry` at `RouteMSJCorankRec.lean:70`).**
>   `coupled_hfin_cell` — the per-cell coupled finiteness itself. This is couplerad ★5: the covering
>   monomial resolution reaching the floor `minAdm((u,)+deep) ≥ 2·T1q`. Decomposition (couplerad §2,
>   the roadmap; see `thread.md`): Stage A raw pivot/Schur split (NEW, raw-pi CoV — the `Matrix.module`
>   diamond) → Move 1 y-Morse peel (banked atom A `radial_morse_residual_power_le` / `core_T_peel_le`) →
>   Move 2 lost-block bilinear corank recursion — terminal UNIFIED (square + non-square) via schurrec's
>   `routeMBoxThresholdFinite_mnp u M₂ n_last`, but as a CHARGED variant: the charge
>   `det(Q_bQ_bᵀ)^{−a/2}` is threaded THROUGH the per-corank step (couplerad §w3 CORRECTION, 2026-07-16).
>   The earlier "fold the charge into the loss at a shifted exponent onto uncharged `mnp`" plan is
>   REFUTED — the fold under-proves on TIGHT shells (all 4 dispatch witnesses); the exact fact is
>   `δ = 0` (charged codim = uncharged codim = floor, via CODIM not a fold: `N_loss(e) − γ^hier(e) ≥
>   floor/2`), so the charge must live IN the corank recursion, absorbed at each rank-drop by the freed
>   measure/Jacobian (`γ^hier ≤ freed measure`), Cauchy-Binet-FREE via `Matrix.det_fromBlocks` (NOT
>   spectral det-monotonicity = option-2 compounding). The coupling (charge · loss through `Q_b`) is
>   ESSENTIAL — it does NOT factor into "charge finite × loss finite" (couplerad's whole point). Full
>   detail + the 4-piece wiring plan (w1–w4): `thread.md` §w3 CORRECTION.
> - **Structure & ideas observed.** couplerad's cert: Route A (corank recursion) over Route B
>   (chain-length IH, DEAD — charge compounds). SVD-free. Charge single-layer in `A_cor`. The
>   square-first-factor `(r,r,p)` `SchurCore` is banked; only the non-square per-corank step is new.
> - **Route.** couplerad §8 Route A + corrections: Cauchy-Binet out (v4.29); square not a freebie; and
>   couplerad §w3 (2026-07-16) — the charge is threaded THROUGH the corank recursion at δ=0 (charged
>   `RectSchurCore`), NOT folded onto the uncharged terminal (fold refuted on the tight dispatch shells).
> - **Status.** interface: green-gated + G2-type-witnessed + **REVIEWED (PASS, corankrec-rev)** on all
>   four items — fidelity (token-for-token G2 match at u=t+j), scope soundness (window = exactly
>   `0 < q < T1q`; `carrierThreshold` correctly the full-chain q-threshold), honest-sorry, and rankgen.
>   `#print axioms coupled_hfin` (force-elaborated, decorrelated from build exit) =
>   `[propext, sorryAx, Classical.choice, Quot.sound]` — exactly one `sorryAx` (the mountain), NO
>   `cited_aoyagi_dln` (NATIVE confirmed at the axiom level). NOT sorry-free (one documented mountain
>   sorry, `coupled_hfin_cell`). Rankgen RESOLVED: the strict `a+b+1≤ρ` is genuinely needed (Codex: charge
>   pole `~r^{−a}`, `a` load-bearing) and IS derivable at the binding cut (arch1build's `bindingShell_rankgen`
>   via BackPeel `ρ ≤ tailMin` + the cominimizer lower bound, arity≥4) — I carry it, arch1build fills it.
> - **Architecture update (2026-07-16, coordinator).** **Route B (coupledBox) is CANONICAL** (see
>   `thread.md` §★★ ARCHITECTURE SETTLED). The frontCharge/G2 route this card's `coupled_hfin_cell` states
>   is SUPERSEDED as the TOP-LEVEL route (it is TRUE + reviewed at interior cuts — `hrankgen` excludes the
>   divergent edge/deep-corank cuts — but frontCharge is `+∞` at edge cuts, so it can't be the whole route).
>   My LIVE contribution rescopes to the INTERIOR: `coupledCell_le_frontCell` → schurrec's interior
>   `ChargedRectSchurCore` (scoped `a+b≤ρ`, endpoint `RouteMSchurWishartWeight.lean` @847e71039). The
>   corankrec NULL insight (all non-generic cells null ⟹ `∫=0`, `deepFactor_rank_ge_deepTailMin_ae` +
>   `setLIntegral_measure_zero`) is adopted by dbuild for Route B's deficient-cell disposal. This card's
>   `coupled_hfin_cell` STATEMENT + review stand; the exact interior slot is pending arch1build's pin.

---

## Rankgen OPEN question (flagged to arch1build + couplerad)

`hrankgen` carries couplerad §6's STRICT form `a+b+1 ≤ ρ` (= `a+b ≤ ρ−1`, `ρ = deepTailMin M`), which is
what the charge-domination scan uses. arch1build's banked BackPeel derives `M₁−t ≤ ρ` (= `b★ ≤ ρ`); at a
cut `u=t+j`, `b = M₁−t−j ≤ M₁−t ≤ ρ`, but `a+b ≤ ρ−1` is STRONGER (`a` can be large). OPEN: does BackPeel
discharge `a+b+1 ≤ ρ` at the binding cut, or only `b ≤ ρ`? If only `b ≤ ρ`, either the charge-domination
proof needs only `b ≤ ρ` (couplerad to confirm the weakest sufficient rankgen) or the scope has a gap to
resolve. Carried as an explicit hypothesis pending resolution (bedrock: weakest hypotheses, named).
