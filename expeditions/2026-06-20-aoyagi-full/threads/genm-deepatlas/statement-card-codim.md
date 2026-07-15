# Statement card — `genm-deepatlas` (α): geometric codim = composite-rank recursion (Finding B(2))

Module: `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJDeepCodim.lean`
Branch: `genm-deepatlas` (base `12a7ae38a`; SHA pinned at integration). Namespace
`DLNFibre.DLN.RLCT.DeepAtlas`. Standalone (NOT aggregator-wired — controller integrates).
Build: green via `scripts/lb` (3699 jobs). Force-fresh `#print axioms` = `[propext, Classical.choice,
Quot.sound]`. Zero sorry. Unique name (no sibling clash).

Purpose: the honest discharge of **crstrat Finding B(2)** — "CRrec = geometric κ_k". Team-lead steer
(2026-07-15): land this codim equality [branch α]; the chart-atlas [β] is HELD on the native-vs-cited
fork. The "charts-exhaust {rank ≤ s}" set-coverage framing is VACUOUS (the size-0 empty-minor pivot
chart is the whole space); the genuine content is this codimension equality.

---

> **Claim.** The geometric codimension of the closed product rank-`≤ r` locus `Σ̄^r` equals the
> composite-rank (CR) recursion value `κ = minAdmRec (d − r)`. Hypotheses: `1 ≤ N` (a genuine chain),
> `∀ i, r ≤ d i` (rank in range), over an algebraically closed field of characteristic 0.
>
> - **Lean:** `DeepAtlas.codimRepCanonical_productRankLocusLE_eq_minAdmRec`
>   `{N : ℕ} {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] (d : Fin (N+1) → ℕ) (r : ℕ)`
>   `(hN : 1 ≤ N) (hr : ∀ i, r ≤ d i) :`
>   `codimRepCanonical (productRankLocusLE (k := k) d r) = (minAdmRec (dminus d r) : ℕ∞)`.
> - **Gloss.** `codimRepCanonical (…)` is the (canonical-representative) codimension of the algebraic
>   locus `{ M : Tuple d | (mult M).rank ≤ r }` in the tuple parameter space; `minAdmRec (dminus d r)`
>   is the layer-peeling composite-rank recursion `κ` evaluated at the shifted widths `d − r`. The
>   theorem: geometric codim = `κ`.
> - **Proved.** The equality, unconditionally, under the stated hypotheses, over `[IsAlgClosed][CharZero]`.
>   Assembly of four banked lemmas: `codimRepCanonical_productRankLocusLE_eq_cCodim_enat` (geometric
>   side, `Core.SigmaCodim`, quiver/orbit-closure) → `cCodim_rankShift` (`Core.CTheta`, LR Lemma 4.5) →
>   `minAdm_eq_cCodim` (`MinAdmCCodim`, QIP↔Ext) → `minAdmRec_eq_minAdm` (`RouteMLayerSplit`, layer-peel).
> - **Assumed.** `1 ≤ N`, `∀ i, r ≤ d i` (both needed by the banked lemmas — Kostant-nonemptiness and the
>   rank-shift), and `[IsAlgClosed k] [CharZero k]` (the geometric-codim machinery's Voigt-discharge scope).
> - **Cited.** The geometric codimension side is the paper's quiver/orbit-closure computation (banked,
>   sorry-free, over the algebraic setting). No RLCT / `rlct = ½·codim` content here — this is **pure
>   codimension**, not an rlct claim.
> - **RESIDUAL (named, NOT faked — a separate lane).** This equality lives over `Core.Tuple` and an
>   **algebraically closed char-0 field** (ℂ). The analytic RLCT capstone works over the **real**
>   parameter space `Params H`. "Real codim of the real product rank locus = `minAdmRec (d − r)`" needs
>   an **ℝ/ℂ codimension bridge for this locus, which is NOT banked** — deliberately not discharged here.
>   The transpose map fixes the `prod`↔`mult` orientation but does not supply the real↔complex bridge.
> - **Deferred (β, held).** The chart-atlas coverage + gluing (design §3.1/§3.2/§3.3) for the RLCT
>   integral — held on the native-vs-cited fork (seamrlct); not needed to discharge Finding B(2).
> - **Structure & ideas observed.** Decorrelated Codex (xhigh) caught that the "charts-exhaust"
>   coverage framing was vacuous and that Finding B(2) is fundamentally the codim equality, with the
>   geometric side already banked — reducing a ~1500-3000 LoC chart-atlas build to a ~1-lemma assembly.
> - **Status.** sorry-free, clean-three; fidelity review pending (controller-spawned).

## Companion (Tide B base brick, reusable)

> **`DeepAtlas.rankEqLocus_eq_iUnion_pivot_inter`** (`RouteMSJDeepCover.lean`) —
> `{M | M.rank = r} = ⋃ ρ κ, (pivotChart ρ κ ∩ {M | M.rank ≤ r})`: the non-vacuous exact-rank pivot
> coverage (CR-tree leaf), pure reuse of banked `pivotLocus_eq_iUnion`. Green, clean-three, sorry-free.
> Non-vacuous at `r = 0` (cell = `{M = 0}`). Bank as a clean companion to `pivotLocus_eq_iUnion`;
> feeds branch β if it is later un-held.
