# Statement cards — thread 31 (monument construction), formaliser tide

Commit SHA: **pending controller integration** (worktree branch `worktree-agent-a8b189ffcfdbcd4cb`,
based on `a7db69705`). Bump the SHA at integration.

---

## Card 1 — the salvage adapter (combinatorial half of `exists_coreResolution`, DISCHARGED)

> **Claim.** For a genuine deep network (`0 < N`, positive monotone widths `d`, `qipFeasible`
> nonempty), IF a geometric resolution atlas `res` of `∑(coreGen d e)ᵢ²` at `0` *realizes* the
> built Aoyagi resolution tree (`AtlasRealizesExponents d res` — every chart binding-axis exponent `jac a + 1`
> is a terminal exponent of the tree, and every leaf terminal divisor exponent is realized by some
> chart binding axis), THEN the two combinatorial conjuncts of `exists_coreResolution` hold:
> `hlb` (`qipMin d ≤ jac a + 1` on every binding axis) and `hattain` (some binding axis attains
> `qipMin d`).
>
> - **Lean:** `DLNFibre.DLN.Aoyagi.hlb_hattain_of_atlasRealizesExponents` and its `∃`-wrapped
>   leaf-shaped form `DLNFibre.DLN.Aoyagi.exists_hlb_hattain_of_exists_atlasRealizesExponents`
>   (`lean/DLNFibre/DLN/Aoyagi/RecursionAdapter.lean` @ `<sha>`); the seam is the predicate
>   `AtlasRealizesExponents` (an ℕ-exponent value-support match, NOT a structural chart↔leaf map;
>   clause (ii) conditioned on `= minAdm d`, the weakest form yielding `hattain`).
> - **Gloss.** The adapter reads the ALREADY-PROVED, axiom-clean Engine combinatorics — every terminal
>   exponent is `≥ minAdm d` (`Engine.minAdm_le_terminalExponents`) and some leaf divisor attains
>   `minAdm d` (`Engine.o5_core_realized`) — and transports them across the realization seam to the
>   `Chart`/`Resolution` vocabulary, using the bridge `qipMin d = minAdm d`
>   (`minAdm_eq_cCodim` ∘ `cCodim_eq_qipMin`).
> - **Proved.** `AtlasRealizesExponents d res → hlb ∧ hattain`, sorry-free, axiom cone
>   `[propext, Classical.choice, Quot.sound]`. The bridge `qipMin_eq_minAdm` (`qipMin d = minAdm d`
>   as `ℤ`, monotone `d`) is proved here too. Kill-set anchors reconciled with the decorrelated
>   `g-monument-mval-instances.py` battery: `minAdm ![2,2,3,2] = 3` (running-min, NOT raw `6`),
>   `minAdm ![2,2,1,1] = 1`, `minAdm ![3,3,4] = 8`, `minAdm ![4,4,4] = 12` (all `by decide`).
> - **Assumed.** `AtlasRealizesExponents d res` — the realization seam (the GEOMETRIC obligation). This is a
>   hypothesis of the adapter, NOT proved here.
> - **Cited.** none (the Engine combinatorics + `MinAdmCCodim` bridge are PROVED in-repo, axiom-clean;
>   re-audited by `#print axioms`).
> - **Deferred.** the geometric monument — constructing a `res : Resolution (coreGen d e) 0` (analytic
>   charts, two-sided ideal identity, Jacobian, cover) AND proving it realizes the tree
>   (`AtlasRealizesExponents d res`). This is the coupled corank-≥2 ideal-route build (charter §1.B); `hcover`
>   remains a build-vs-cite call.
> - **Structure & ideas observed.** The combinatorial half of Aoyagi's Cases-1&2 recursion is already
>   built + kernel-clean in the retired-but-salvageable Engine (`buildTree`/`minAdm_le_terminalExponents`
>   /`o5_core_realized`), so the certificate's Stage-1 "build the recursion as defs" is superseded by
>   REUSE. The seam `AtlasRealizes` cleanly separates the discharged combinatorial obligation from the
>   remaining geometric one; labels never cross the seam (only `divExp`/`divProfile` map), consistent
>   with the Case-2-CLOSED ledger.
> - **Route.** Codex-decorrelated (xhigh) scoping + charter §3 / RETIRED.md salvage blessing + elder
>   ratification: reuse the audited-green Engine closure (never a `Geo*`/`ChartBridge*` module), wire
>   via the `AtlasRealizes` seam. Import boundary C1 verified (O5Realization closure builds 0
>   `Geo*`/`Canonical*` modules).
> - **Status.** REVIEWED (rev-monument-adapter SURVIVED, 2026-07-21; two escalations applied: only-the-minimizer weakening + the AtlasRealizesExponents rename; integrated).

---

## Card 2 — the `Chart`/`Resolution` record inhabitation (de-risk)

> **Claim.** The `Chart`/`Resolution` record (Object B's certified atlas) is INHABITABLE and
> non-vacuous: the identity chart `g = id` inhabits every `Chart` field for any normal-crossing
> monomial family `∑ bₖ²` (a divisibility chain, squarefree-on-binders dominant generator), and a
> single-chart atlas over the unit box inhabits `Resolution`; its `divisorMin = 1`.
>
> - **Lean:** `DLNFibre.Core.Aoyagi.idChart` / `idResolution` / `idResolution_divisorMin`, with the
>   concrete non-vacuous witness `allOnesResolution` / `allOnesResolution_divisorMin`
>   (`lean/DLNFibre/Core/Aoyagi/ResolutionInhabited.lean` @ `<sha>`)
> - **Gloss.** For the single monomial `∏_d u_d` over `Fin (D+1)` (all binding axes, exponent 1),
>   `allOnesResolution D : Resolution (monomialFam ∏u_d) 0` is a real term and
>   `allOnesResolution_divisorMin : divisorMin = 1` shows Object B's per-chart value machinery
>   (`Chart.chartMin`, `Resolution.divisorMin`) composes on it — the RLCT of `(∏u_d)²` is `½`.
> - **Proved.** the full record is inhabitable, no over-constraint; sorry-free, axiom cone
>   `[propext, Classical.choice, Quot.sound]`.
> - **Assumed.** the family is a divisibility chain with a binding axis (the normal-crossing / clean
>   regime — the record's own hypotheses).
> - **Cited.** none.
> - **Deferred.** the coupled corank-≥2 inhabitation (`g` a genuine blow-up, not `id`) — the monument;
>   this card is the CLEAN end (positive inhabitation test), NOT that.
> - **Status.** REVIEWED (covered by the adapter review + rev-cov-fidelity's inhabitation audit, 2026-07-21; integrated).
