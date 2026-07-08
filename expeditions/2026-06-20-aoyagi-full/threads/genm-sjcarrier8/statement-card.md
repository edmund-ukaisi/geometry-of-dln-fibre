# Statement card — `genm-sjcarrier8` (R1-UPPER `(S,J)` peel: the peel on the freed Γ-integral)

Thread: `genm-sjcarrier8` (formalisation tide). Branch: pushed to `genm-sjcarrier8` (off
`expedition/aoyagi-full` @ `5f749d54`). Module:
`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJFreedPeel.lean` (138 LoC, new leaf; imports
`RouteMSJResolution`, `RouteMSJChartShear`, `RouteMSJCorankPeel`).

This tide lands **mission item 1 — the peel on the freed Γ-integral**. The banked chain (block-reindex
→ Schur weld → MP shear freeing Γ) had rewritten the RAW inner chart integral to the freed cross-coupled
Schur form as an EQUALITY *inside* the inner fibre. This module (a) composes that whole chain onto
`gammaPeelIntegral` itself — landing the freed-Γ triple integral as a sorry-free EQUALITY — and (b) welds
the banked corank atom (`corankBlock_morsePeel_lt_top`) onto the freed loss, banking the inner-Γ
finiteness as a CONDITIONAL that exposes the exact 3-hypothesis interface the outer descent must supply.
Mission items 2/3 (the `(S,J)` OUTER `A'`-descent supplying that interface as a measure statement, the
matrix-box→blow-up change of variables, and the redChain IH wiring) do NOT land — they are the genuine
unbuilt mountain (design cert `genm-sjjoint-design/cert.md`: the IH saturates at the binding cut).
`sjJointResolution` (`RouteMSJResolution.lean:797`) is **UNTOUCHED** (still the single named sorry).
Honest-partial multi-tide progress.

---

> **Claim 1 (the freed-Γ equality for `gammaPeelIntegral`).** For an arbitrary `(t, ρ, κ)` pivot cut,
> the per-chart peeled integral equals the freed-Γ triple integral (outer tail box `A'`, then the
> `(P,B₁₂,C)`-outer domain `x`, then the freed corank block `Γ` over the shear-image box), of the freed
> Schur loss:
>
>     gammaPeelIntegral M t ρ κ c'
>       = ∫_{A'∈paramsBoxM (tailChain M) 1} ∫_{x∈outerDom t (M₀−t) (M₁−t) 1}
>           ∫_{Γ | Γ + schurShift x ∈ genBox ...} ofReal( (freedSchurLoss x Γ Q̃)^{−c'} ),
>     Q̃ = (prod (tailChain M) A').submatrix (blockSplitEquiv κ) id.
>
> - **Lean:** `DLNFibre.DLN.RLCT.gammaPeelIntegral_schurShearFree_eq`.
> - **Gloss.** The RAW per-chart peel integrand is rewritten, measure-preservingly, into the freed
>   cross-coupled Schur form with the corank block `Γ` an INDEPENDENT integration variable — the exact
>   form the `(S,J)` outer descent operates on.
> - **Proved.** The EQUALITY, unconditionally. Route: `lintegral_congr` over the outer `A'`, then the
>   banked weld (`chartInner_schurWeld_eq_of_emb`, over the inner `A₀`-fibre) via `rw`, then the banked
>   shear (`chartInner_schurShearFree_eq`, per outer `x`) via `exact` (defeq unification — `rw` did not
>   fire syntactically because the shear's `a` implicit is a domain-only metavariable).
> - **Assumed / Cited / Deferred.** none (holds for all `c'`; no threshold, no positivity, no PosDef).
> - **Status.** sorry-free (clean-three `[propext, Classical.choice, Quot.sound]`, forced `#print
>   axioms`).

> **Claim 2 (the conditional inner-Γ finiteness — the corank peel on the freed loss).** For a fixed
> outer triple `x` and tail `Q`, over ANY domain `s`, the freed corank integral `∫_{Γ∈s}
> (freedSchurLoss x Γ Q)^{−c'}` is finite provided the three interface hypotheses: `c'` above the block
> Morse threshold `a·b/2`; the coupling `Q_b Q_bᵀ` positive definite; the pivot energy `frobSq (P·Q̃ₚ)`
> strictly positive (the held core `w`).
>
> - **Lean:** `DLNFibre.DLN.RLCT.freedSchurLoss_inner_peel_lt_top` (+ `frobSq_empty_rows`).
> - **Gloss.** The freed loss `frobSq (P·Q̃ₚ) + frobSq (C·Q̃ₚ + Γ·Q_b)` is welded onto the banked atom's
>   shape `w + frobSq Apiv + frobSq (Ccross + Γ·Qb)` at `w := frobSq (P·Q̃ₚ)`, `Apiv := 0`
>   (`frobSq 0 = 0`, so the pivot energy plays the strictly-positive core), `Ccross := C·Q̃ₚ`, `Qb :=
>   Q_b`; then `corankBlock_morsePeel_lt_top` fires.
> - **Proved.** The `< ⊤`, conditionally. Route: instantiate `corankBlock_morsePeel_lt_top` at the four
>   assignments above; rewrite the integrand from `freedSchurLoss` to the atom shape (`lintegral_congr`
>   + `frobSq_empty_rows` + `ring`); `exact`.
> - **Assumed (EXPOSED as the interface, NOT asserted to hold).** `hc' : (a·b)/2 < c'`;
>   `hG : (Q_b Q_bᵀ).PosDef`; `hpiv : 0 < frobSq (P·Q̃ₚ)`. These are exactly the gates the design cert
>   identified; they FAIL pointwise for a fixed `(A', x)` (the pivot energy vanishes on a divisor, `Q_b
>   Q_bᵀ` is rank-deficient on ≈750/5440 bottleneck charts, and `c' < ½·minAdm M` does not force `c' >
>   a·b/2` on ≈94/480 charts). Supplying them as a MEASURE statement is the deferred outer descent.
> - **Cited.** none.
> - **Status.** sorry-free (clean-three, forced `#print axioms`).

> **Deferred (named, NOT done — the standing mountain).** Items 2/3: the `(S,J)` OUTER `A'`-descent
> supplying the three interface hypotheses of Claim 2 as a measure statement, by integrating the outer
> tail parameters `A'` and descending through the `SJLinGenState` carrier (`gen_rowMix_const`
> block-elim + `loss_radialStep` radial) to the monomial terminal (`sjLoss_terminal_lintegral_lt_top`),
> wiring the reduced coupling to the strong IH (`redChain t M`). Per the design cert
> (`genm-sjjoint-design/cert.md`, 3 decorrelated lines + Codex xhigh): at the binding cut
> `minAdm M = a + minAdm (redChain t* M)` the residual exponent EXACTLY saturates the reduced-chain IH
> threshold (0/4000) — Hölder-infeasible — so the strong IH is insufficient as a black box, and the
> matrix-box→blow-up change of variables is ~65–75% genuinely-new resolution-of-singularities content
> (the `RouteMSJLinGen`/`RouteMSJLedger`/`RouteMSJTerminal` headers concur; the terminal header cites
> concrete `L ≥ 3` counterexamples showing a naive per-layer descent FAILS). This is NOT closable from
> the banked inventory by composition — STOP + report, do not launder.

---

## Review status

**Fidelity: pending reviewer.** Requested via `REQUEST_SPAWN` (leaf executor does not review own
fidelity).

## Fidelity notes (for the reviewer)

- Both claims are an EQUALITY (Claim 1) and a CONDITIONAL finiteness (Claim 2). Claim 1 carries NO
  analytic strength beyond the (banked) measure-preserving changes of variables; the `…_eq` name is
  honest. Claim 2's `…_lt_top` is finiteness, but CONDITIONAL on three explicit hypotheses — it does NOT
  assert them (they fail pointwise). The interface is exposed, not laundered.
- Cross-check the `outerDom`/`genBox`/`schurShift`/`freedSchurLoss`/`blockSplitEquiv` on Claim 1's RHS
  against the banked `chartInner_schurShearFree_eq` (`RouteMSJChartShear`) — Claim 1 is the composition
  of `chartInner_schurWeld_eq_of_emb` then `chartInner_schurShearFree_eq` under `lintegral_congr`, so its
  RHS is the shear lemma's RHS with `a = M₀−t`, `b = M₁−t`, `Q = (prod (tailChain M) A').submatrix
  (blockSplitEquiv κ) id`.
- Claim 2's atom instantiation: verify `w := frobSq (P·Q̃ₚ)` (`P = of x.1.1`), `Apiv := 0`,
  `Ccross := of x.2 * Q̃ₚ`, `Qb := Q.submatrix Sum.inr id`, and that
  `frobSq (P·Q̃ₚ) + frobSq 0 + frobSq (C·Q̃ₚ + Γ·Q_b) = freedSchurLoss x Γ Q` (the `ring` step, with
  `frobSq_empty_rows`). Threshold `hc' : (a·b)/2 < c'` matches the atom's `(p·q)/2 < c'` at atom-`p = a`,
  atom-`q = b`, so `a·b = (M₀−t)(M₁−t) = peelExp M t` — Aoyagi's per-boundary exponent.
- `sjJointResolution` (`RouteMSJResolution.lean:797`) UNTOUCHED — confirm no edit and it is still the
  single named sorry in that file.
