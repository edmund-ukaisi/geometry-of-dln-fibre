# Statement cards — the two Core leaves (L1 + terminal_bezout)

> Landed by seat-core (549a1c01a, integrated at the expedition tip); reviewed by rev-core
> (fidelity / precision / non-vacuity / circularity / consumer-fit, decorrelated Codex xhigh —
> artifacts at `../40-rev-core/codex/`). Docstring precision fix (openness-example attribution)
> applied by the controller at review integration.

## Card A — `terminal_bezout`

> **Claim.** Bézout / principality is not preservable at interior states; it is BORN at the
> terminal node where the pivot is cleared (thread-34 certificate split, half (B);
> `worked.tex:659`).
>
> - **Lean:** `DLNFibre.Core.Aoyagi.terminal_bezout`
>   (`lean/DLNFibre/Core/Aoyagi/PrincipalInv.lean` @ `549a1c01a`)
> - **Gloss.** At a terminal `StepInv` (residual exhausted to the single `≡ 1` entry — encodes
>   `S = L`), on an open `V ∋ 0`, with a cleared pivot `(F i₀∘g) = b·unit`, `unit 0 ≠ 0`
>   (encodes `J ≥ 1`): there is an open `V' ∋ 0`, `V' ⊆ V`, on which `PrincipalInv` holds —
>   divisibility (quotients `q · 0`) AND the Bézout identity (witness `r = ` the inverted unit
>   at `i₀`).
> - **Proved.** The full statement, unconditionally. `#print axioms` =
>   `[propext, Classical.choice, Quot.sound]` (re-derived by controller AND reviewer,
>   force-elaborated).
> - **Assumed.** The hypotheses as stated: terminal StepInv; `IsOpen V ∧ 0 ∈ V` (both halves
>   load-bearing — counterexamples `V = {u | 0 < u 0}` for `0 ∈ V`, `V = {0}` for openness);
>   the cleared-pivot factorization with `ContinuousOn unit V`. The theorem does NOT assert a
>   pivot exists — supplying `i₀`/`unit` is the consumer's (L5's) "born terminally" obligation.
> - **Cited.** None.
> - **Deferred.** None (in this statement). The interior→terminal transport is a SEPARATE named
>   obligation (`terminal_edge_stepInv`, arch-C's canonCenter round) — this theorem consumes the
>   terminal state, it does not produce it.
> - **Structure & ideas observed** (thread-34 pnp): principality FALSE at all `S < L` and all
>   `J = 0` (deep-layer vanishing forces 0 = 1 by continuity); first TRUE terminally; the
>   Bézout row is the weighted-cofactor expansion `b_{k₀} = Σ (U⁻¹)_{1i}(V⁻¹)_{j1}·(∏C∘g)_ij`.
> - **Route.** V′-shrink `V ∩ {unit ≠ 0}` (`ContinuousOn.isOpen_inter_preimage` + `isOpen_ne`);
>   divisibility from the Fin-1 sum collapse; Bézout witness `r i = if i = i₀ then unit⁻¹ else 0`
>   with `ContinuousOn.inv₀`.
> - **Status.** sorry-free + reviewed (rev-core, 2026-07-21: SURVIVED — fidelity/precision/
>   non-vacuity/circularity PASS; kill-set `km_terminal_bezout` fires the real mechanism:
>   genuinely-vanishing `b = u₀`, proper shrink dropping `u₀ = −1`).

## Card B — `principalInv_regionRepresents` (L1)

> **Claim.** The terminal `PrincipalInv` delivers the two region-ideal inclusions the Object-B
> charts need: `⟨F∘g⟩ = ⟨b⟩` on the region (the `M' = 1` compression), both directions.
>
> - **Lean:** `DLNFibre.Core.Aoyagi.principalInv_regionRepresents`
>   (`lean/DLNFibre/Core/Aoyagi/PrincipalInv.lean` @ `549a1c01a`)
> - **Gloss.** `PrincipalInv F g b q r V` implies `RegionRepresents (F∘g) (b) V` (divisibility,
>   cofactor `q`) and `RegionRepresents (b) (F∘g) V` (Bézout, cofactor `r`), both
>   continuous-on-`V`; direction convention per `IdealInvariance.RegionRepresents`
>   (`⟨first⟩ ⊆ ⟨second⟩`).
> - **Proved.** Both directions, unconditionally; clean-three (controller + reviewer re-derived).
> - **Assumed.** `PrincipalInv` as hypothesis (produced terminally by Card A).
> - **Cited.** None. **Deferred.** None.
> - **Route.** Fin-1 repackaging; `q` witnesses forward, `r` backward.
> - **Status.** sorry-free + reviewed (rev-core: genuine interface conversion, NOT an rfl-alias —
>   propositionally equivalent over `Fin 1`, not definitionally; `PrincipalInv` not trivially
>   satisfiable, `r = 0` would force `b = 0`). Consumer wiring already elaborates at the driver
>   (`exists_atlasRealizesExponents` :809–813 feeds `leafPath_chartGeometry`'s hfwd/hbwd).

## Consumer obligations recorded at review (for L5's eventual body — NOT defects here)

1. The leaf residual must be LITERALLY typed `Fin 1` with value `≡ 1` — a fold-native residual
   type merely defeq-to-`Fin 1` blocks the wiring.
2. The cleared pivot must be a SINGLE generator `(F i₀∘g) = b·unit` with `unit 0 ≠ 0` — not a
   linear combination / germ. Supplying `i₀`/`unit` is L5's "born terminally" obligation
   (via `terminal_edge_stepInv` + the terminal chart data).

Coverage notes (reviewer, non-blocking): the km kill-set is `M = 1` (the `M ≥ 2`
`sum_eq_single` path unexercised); openness-necessity asserted in prose, not committed as an
in-file `example`.
