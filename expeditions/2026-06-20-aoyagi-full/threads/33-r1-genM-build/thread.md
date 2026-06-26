# Thread 33 — R1 general-M achiever atom: engine-banking pass + the design fork

**Seat:** formaliser (tide). **Date:** 2026-06-26. **Branch:** `worktree-agent-a4e6a2dedec612386`
(off `expedition/aoyagi-full`).
**Gate:** the lone general-`M` `sorry` `routeMCore_box_diverges_achiever`
(`RouteMLayerCoverGE.lean:120`) — the R1 LOWER leg, reduced M-agnostically to "construct
`NodeAchieverChart M`" (`routeMCore_box_diverges_of_nodeChart`, proven ∀M).

## What this pass banked (sorry-free, committed)

Two reusable, de-risked **engines** for the general construction — the pieces both the thread-32
pen-and-paper read and a decorrelated Codex read (this thread) named as the highest-value increments:

1. **`RouteMAchieverGeneralDet.lean`** — the composed-determinant telescoping (promoted from the
   banked `Spike/GeneralComposedDet`): `listProd_clm_abs_det` / `general_composed_clm_abs_det`. The
   general `φ_M` det (variable-length factor list) telescopes via the det monoid-hom
   (`MonoidHom.map_list_prod`) with NO dependent-`Fin` cast. Axiom-clean
   `[propext, Classical.choice, Quot.sound]`.
2. **`RouteMAchieverTelescope.lean`** — the abstract chained-product telescope. `structure Chain`
   bundles the per-level LOCAL identities `C_s · A_s = B_s · C_{s+1} + u • E_s` (+ terminal
   `C_n = u • R`); the keystone `Chain.chain_telescope` proves `C_s · suffix_s = u • Hmat_s` by
   downward induction, so `chain_telescope_zero` reads `prod = u • Hmat` at `s = 0`. The reusable
   algebraic heart of `prod M (φ_M u) = u·H`, decoupled from the block construction. Non-vacuity
   witness (length-1 RRR shape) included. Axiom-clean `[propext, Classical.choice, Quot.sound]`.

These convert the global telescope (the part most at risk of a multi-week dependent-cast fight) into
a *per-layer local identity* the block construction supplies one boundary at a time. The det step is
already a single `rw` once the per-factor dets are in hand.

## The decorrelated-Codex design read (gpt-5.x, xhigh; `codex/encoding-{prompt,answer}.md`)

Independently returned **ROADMAP** (matching thread-32). Conclusion withheld in the prompt; no rubber
stamp. Key outputs:
- Ranked the three encodings: **(A) dependent layer spaces + abstract telescope cheapest**, then (C)
  layer-peeling recursion, then (B) pad-to-ambient (avoid — proves the wrong product first).
- Named the single highest-value bankable increment: **the abstract telescope + one bridge lemma from
  `suffix` to `prod M A`** — exactly engine 2 above (the bridge is the remaining sub-piece, see below).
- Cost verdict: NOT a bounded `<1500`-line push; the chart map, arbitrary block construction,
  split-coordinate reindexing, and the `prod M A` bridge are the multi-pass part. Most-likely-wrong
  ROADMAP assumption: that the three fixed instances aren't already factoring through reusable
  `fromBlocks`/split APIs. Most-likely-wrong BUILD-NOW assumption: that `simp` will normalise the
  `Fin` transports `t_s + (M_s − t_s) = M_s` and `Fin.succ` tail products without named equivalences.

## The remaining roadmap (the design fork the controller gates)

The general `nodeChartGeneral M : NodeAchieverChart M` needs, beyond the two banked engines:

1. **The bridge `suffix 0 = prod M A`** (bounded, reusable; Codex's named sub-piece). Friction: the
   `Chain` widths are `ℕ → ℕ` while `M : Fin (L+1) → ℕ` (needs `Wwid k = M ⟨k, _⟩` extension), and
   `prodAux` peels PREFIX-first (`prod = (…(A₀·A₁)…)·A_{L−1}`) while `suffix` peels SUFFIX-first
   (`A₀·(A₁·(…))`) — equal by associativity but distinct induction structures + per-layer
   `Fin (M k)` vs `Fin (M k.castSucc)` casts. Not banked this pass (one bounded sub-build).
2. **The genuine layer matrices** (the `Chain.A`/`C`/`B`/`E`/`R` instance for arbitrary `M`): the
   thread-26 closed form — per-boundary LDU core `K_s` + unit-triangular chaining `G_s` + radial
   blow-up — defined over the dependent `Params M` block sizes (`t_s`, `c_s`, `r_s`, all M-dependent).
   This is the crux multi-pass piece (arbitrary-block `fromBlocks`/`reindex`/split construction +
   proving each LOCAL identity `C_s · A_s = B_s · C_{s+1} + u • E_s`).
3. **The per-factor full-ambient dets** (feeding engine 1's `hfac`): each level's `K_s`/`G_s`/radial
   factor as a full-ambient `End (Fin N → ℝ)` with its block-triangular det — the `(3,3,3,3)` anchor's
   `Frame3333Deriv_det`/`Kparam3333Deriv_det` pattern, now `List`-indexed. Define general `leafH`;
   prove `leafH p = minAdm M − 1`.
4. **The unit `V`** bounded + a.e.-positive (the MvPolynomial null-zero-set route, already general-N
   in spirit — `Vval3333_ae_pos`/`VPoly3333_ne_zero` generalise).
5. **The cov** — finite-family null-slice c-o-v over the general weighted-axis set
   (`measure_biUnion_null_iff` + `coordZero_null` + the general triangular `phi_M_injOn`).
6. **Assembly** `nodeChartGeneral M` + discharge `routeMCore_box_diverges_achiever` ∀M (one line,
   mirroring `routeMCore_box_diverges_achiever_3333`).

**Honest cost read:** pieces 2 + 5 are the multi-pass part (arbitrary dependent-block matrix
construction + injOn/cov over a growing weighted-axis set). Pieces 1, 3, 4, 6 are bounded given the
two banked engines + the three fixed-`L` anchors as templates. The three concrete instances
((4,4,2,2), (3,3,4), (3,3,3,3)) remain the right current banking of the headline's de-risking; the
general atom is reachable but is a controller-gated design pass, not a single tide.
