# Statement card — the α-unlock: back-peel co-minimizing deeper rank `ρ ≥ b`

Piece #1 of the §5 decorated-descent discharge (thread `genm-sj5-desc2`,
`transversality-recursion.md §8`, the NATIVE route honoring #97).

> **Claim (cert §8).** At a nondegenerate binding cut `t` of a chain `M` (`a = M₀−t ≥ 1`,
> `b = M₁−t ≥ 1`; the cut binding), every front-peel co-minimizing deeper rank `ρ` of the reduced
> chain `redChain t M = (t, M₂,…,M_L)` satisfies `ρ ≥ a+b−1 ≥ b`. Equivalently: the cert's named
> `minAdm_eq_backPeel` (`minAdm(t,M₂,…,M_L) = min_ρ[cCodim(M₂,…,M_L;ρ) + t·ρ]`) IS the banked
> front-peel `minAdm_eq_frontPeel` applied to `redChain t M`; the `p=0`-transversality's "deeper
> generic rank `r_X ≥ b`" is the incidence+convexity combination on it.
>
> - **Lean:** `DLNFibre.DLN.RLCT.minAdm_backPeel_cominimizer_ge` (sharp `a+b−1`),
>   `minAdm_backPeel_cominimizer_ge_corankWidth` (the `b` corollary),
>   `exists_minAdm_backPeel_cominimizer_corankWidth` (achiever existence)
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJBackPeel.lean`, untracked @ `c5a2ea6a`;
>   SHA on controller integration).
> - **Gloss.** For a parent `M : Fin (K+1+1+1+1) → ℕ` (≥ 4 widths) and pivot `t` with
>   `t+1 ≤ min(M₀,M₁)` and `minAdm M = peelCharge M t + minAdm (redChain t M)`: for any `ρ` with
>   `ρ ≤ tailMin (redChain t M)` and `frontCharge (redChain t M) ρ = minAdm (redChain t M)` (i.e. `ρ`
>   a front-peel co-minimizer), we have `(M₀−t)+(M₁−t)−1 ≤ ρ`, hence `M₁−t ≤ ρ`. `frontCharge C ρ =
>   C₀·ρ + minAdm(tail(C)−ρ)`; on `C = redChain t M` the leading `C₀ = t`, so this is exactly the
>   cert's back-peel term `t·ρ + minAdm((M₂,…,M_L)−ρ)`.
> - **Proved.** The full statement, unconditionally, pure ℕ. Incidence
>   (`minAdm (redChain (t+1) M) ≤ minAdm (redChain t M) + ρ`, from `minAdm_eq_frontPeel` /
>   `frontCharge_ge_minAdm` + tail-invariance `tailMin_redChain_le_succ`, `frontCharge_redChain_succ`)
>   combined with banked convexity `minAdm_redChain_succ_ge`. Axiom-clean
>   `[propext, Classical.choice, Quot.sound]`.
> - **Assumed.** `t` binding + nondegenerate (`ht1`, `hbind`) — exactly the "decoration exists"
>   condition (cert §3); `ρ` a co-minimizer. `≥ 4`-width parent so `redChain t M` is a ≥ 3-width
>   chain (front-peel's domain); the ≤3-width leaf base is handled separately (`minAdm(t,M₂)=t·M₂`).
> - **Cited.** none. (The `cCodim` geometric gloss `minAdm(deeper−ρ) = codim{rank ≤ ρ}` is NOT used
>   — it is the interpretive bridge, off this arithmetic critical path, per `minadm-ccodim-cert §1`.)
> - **Deferred.** The geometric identification "co-minimizing rank `ρ` = generic rank of `Zdeep` on
>   the top-dim component" (turning this ℕ bound into `rank(Zdeep) ≥ b`) is **piece #2**'s job, plus
>   the free-matrix corank survival `rank(A_cor·Zdeep) = b` (D1-lane genericity). Not part of #1.
> - **Structure & ideas observed (p&p `transversality-recursion.md §8`).** The load-bearing invariant
>   is `minAdm`-convexity `C_{t+1}−C_t ≥ a+b−1` (banked) squeezed against the incidence
>   `C_{t+1}−C_t ≤ ρ` (front-peel). Both TIGHT at many anchors (`ρ = a+b−1`), so the naive "Zdeep
>   full rank" over-claims; the correct margin is `ρ ≥ b`. Decorrelated Codex refuted the literal
>   full-rank form (reduced `(2,2,2)` at rank `1<2`) and supplied this cleaner invariant.
> - **Route (controller synthesis + formaliser recalibration).** The cert scoped #1 as a "fresh
>   Core.CTheta/QIP subsystem consuming `cCodim_rankShift`". On building: the back-peel identity is
>   the already-banked `minAdm_eq_frontPeel` (#117) read on `redChain t M`, so no Core build was
>   needed. Delivered as a ~150-line ℕ module reusing the front-peel + the banked convexity.
> - **Status.** sorry-free (awaiting cover fidelity review).

## Regression anchor (in-file `example`, cert §6 test 1)

`(3,3,2,2)` at the nondegenerate binding cut `t = 2` reduces to `(2,2,2)`; the front-peel of
`(2,2,2)` achieves its min `= 3` at rank `ρ = 1`, with `b = M₁−t = 1`, so `ρ = b` (TIGHT — a genuine
rank-drop cut where the corank row survives, `p = 0`). Encoded as
`frontCharge (redChain 2 ![3,3,2,2]) 1 = minAdm ![2,2,2]` (`by decide`).

## Numerical de-risk

`/tmp/backpeel_check.py`: over all parents (4–5 widths, widths 1–6), at every nondegenerate binding
cut, every front-peel co-minimizer `ρ` of `redChain t M` satisfies `ρ ≥ M₁−t` — 3124 cases, 0 fails;
front-peel identity `minAdm = min_ρ frontCharge` holds (0 fails).
