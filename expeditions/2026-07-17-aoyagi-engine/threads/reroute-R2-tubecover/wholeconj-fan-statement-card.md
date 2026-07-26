# Statement card — WHOLE-CONJUGATE born-native (3,3,4) fan + `hcover` + (C) `ek₀`/`hjac`/`divisorMin`

Reworks the value-BROKEN §2-shear-only fan (prior `native-fan-statement-card.md`, whose survivor
landed on an A1-spectator) to the value-correct WHOLE loss-symmetry conjugate `g_c = σ⁻¹∘gWrap∘σ`
(pnp double-certified `rlct ≥ 4` / `divisorMin ≥ 8` on all 288 — `whole_conjugate_all288.out`).

---

> **Claim (fan def, value-correct).** The whole-conjugate born-native (3,3,4) fan is a 3-node tree:
> node 1 applies, per dominant `p1 ∈ {0,…,7,20}`, `nativeChart1 p1 = nativeSel p1 ∘ nativePerm p1`
> (native §2 shear AFTER the native permutation); nodes 2, 3 are block blow-ups at the PERMUTED native
> centres `σ(C1)` / `σ(C2)` (`sigmaC1Fs`/`sigmaC2Fs`, p1-dependent) — NOT the fixed `C1`/`C2`. The
> leaf index is the DEPENDENT `Σ p1, σC1(p1) × σC2(p1) = 288` (the ACTUAL whole-conjugate leaves).
>
> - **Lean (perm atom):** `DLNFibre.DLN.Aoyagi.NativePerm334.nativePerm` / `nativeChart1` +
>   `permCoord_covers` / `nativePerm_covers` / `nativePerm_jacDet` / `nativeChart1_covers`
>   (`lean/DLNFibre/DLN/Aoyagi/Corank2NativePerm334.lean` @ `a50122055`)
> - **Lean (fan + family):** `DLNFibre.DLN.Aoyagi.NativeFan334.nativeFan` / `gFlat` / `gFin` /
>   `blockBlowupMap_conj` / `sigmaC1Fs` / `sigmaC2Fs`
>   (`lean/DLNFibre/DLN/Aoyagi/Corank2NativeFan334.lean` @ `a50122055`)
> - **Gloss.** `nativePerm p1` is the DIRECT coordinate permutation `w ↦ w ∘ cperm_p1` (the emitted
>   conj-permP index map, a genuine `Fin 21` bijection). `gFin c` for leaf `c = (p1,p2,p3)` is
>   `(blockBlowupMap {0..7,20} p1 ∘ nativeChart1 p1) ∘ blockBlowupMap (σC1 p1) p2 ∘
>   blockBlowupMap (σC2 p1) p3` — the value-correct whole-conjugate chart.
> - **Proved.** `nativeChart1 p1` box-contains (`C = 2`, `nativeChart1_covers`) and is differentiable;
>   `nativePerm p1` is a sup-norm isometry (`nativePerm_covers`, any radius) with `|jacDet| = 1`;
>   `blockBlowupMap_conj` — the elder-named characterization `σ⁻¹∘bb(C,p)∘σ = bb(σ C, σ p)` (the
>   σ-conjugate description of the direct native-centre atoms). Direct-atom composite `== whole_conj`
>   verified 288/288 (sympy).
> - **Assumed.** none.  **Cited.** none.
> - **Deferred.** the entry-equality `hentry` (the (B) seat, clean-144); the over-vanishing-144
>   regular-sequence + native CoV Ψ feeder (the (ii) seat, elder-confirmed mechanism).
> - **Structure & ideas observed.** `σ(C0) = C0` (the loss symmetry fixes the 9 A0 slots), so node-1
>   centre stays `S1` with pivot `σ(20) = p1`; only nodes 2/3 get σ-permuted centres. The node-2/node-3
>   `Covers` clauses are CENTER-BLIND (id shears), so the cover transfers verbatim from the shear-only
>   fan; only the node-1 clause changes (composite shear = shear ∘ perm-isometry).
> - **Route.** direct native-centre `blockBlowupMap` atoms (grep-clean of chart-level conjugation) +
>   `blockBlowupMap_conj` as the σ-description; `nativePerm` through `Equiv.ofBijective` (perms by
>   `decide`); the `FanTree` with p1-dependent child centres; flatten via `Sigma`-index chase.
> - **Status.** sorry-free  ·  axiom footprint `[propext, Classical.choice, Quot.sound]`.

> **Claim (`hcover`).** `volume (ball 0 1 \ ⋃ c, gFin c '' domFin c) = 0` — the whole-conjugate leaf
> family covers a neighbourhood of `0` (a FULL cover, a fortiori null).
>
> - **Lean:** `DLNFibre.DLN.Aoyagi.NativeFan334.native_hcover` (`…/Corank2NativeFan334.lean` @ `a50122055`)
> - **Proved.** `ball 0 1 ⊆ closedBall 0 1 ⊆ nativeFan.leafImages = ⋃ c, gFin c '' domFin c` via
>   `nativeFan_covers` (`Covers (r↦r+2r²) · 1`) + `leafImages_subset_flat` + the `Fin`-reindex.
> - **Assumed / Cited / Deferred.** none.  **Status.** sorry-free.

> **Claim ((C) survivor `ek₀` + binding contract).** Per leaf, `ek₀ c = 1@p1 + 1@p2` (the pivot-cross,
> the CLEAN-144 survivor monomial `u_{p1}·u_{p2}`, squarefree); `bindingAxes (ek₀ c) = {p1, p2}`,
> nonempty, mult-1.
>
> - **Lean:** `DLNFibre.DLN.Aoyagi.NativeValue334.ek₀` / `pivot1` / `pivot2` / `pivots_distinct` /
>   `hbind` / `hunit_mult` / `bindingAxes_ek₀` (`…/Corank2NativeValue334.lean` @ `a50122055`)
> - **Proved.** the reduction's `hbind` + `hunit_mult` fields; `p1 ≠ p2` (`p1 = σ(20) ∉ σ(C1) ∋ p2`).
> - **Deferred.** `k0` (the survivor `coreGen` entry index) + the exact `hentry` — the (B) seat, which
>   builds `hentry` against this `ek₀`. Over-vanishing-144 use a DIFFERENT (higher) `ek₀` via the (ii)
>   feeder (their pivot-cross `hentry` FAILS — 0 clean survivors).  **Status.** sorry-free.

> **Claim ((C) composite Jacobian + `hjac` + `divisorMin ≥ 8`).** `|jacDet (gFlat idx) u| =
> |u p1|^8 · |(bb σC2 p3 u) p2|^7 · |u p3|^3` (a single monomial); hence `|jacDet (gFin c) u| =
> jacWeight (jacFin c) u · |unitFin c u|` with `unit ≡ 1`; and every binding axis has Jacobian
> exponent `≥ 7`, so `8 ≤ inf'_c inf'_{d ∈ bindingAxes} (jacFin c d + 1)`.
>
> - **Lean:** `DLNFibre.DLN.Aoyagi.NativeJac334.abs_jacDet_gFlat` / `jacExp` / `hjac_gFlat` /
>   `hjac_gFin` / `jacFin` / `unitFin` / `divisorMin_ge_eight`
>   (`…/Corank2NativeJac334.lean` @ `a50122055`)
> - **Proved.** the composite Jacobian via the `jacDet_comp` telescope over the five atoms (two shears
>   `|jacDet|=1`, three blow-ups `|·_pivot|^(card−1)` = `8,7,3`; `p1` fixed through the inner atoms).
>   `jacExp_pivot1 = 8`, `jacExp_pivot2_ge ≥ 7`; the reduction's `hdivisorMin` (weakened `= 8 → 8 ≤`,
>   see below) at `8 ≤`. The pnp certifies the exact per-leaf `divisorMin ∈ {8, 9}` (min `8`).
> - **Assumed / Cited / Deferred.** none.  **Status.** sorry-free.

> **Claim (reduction weakening).** The (3,3,4) V-lower reduction chain accepts `divisorMin ≥ 8` (a
> lower bound), not equality — required because the born-native per-leaf `divisorMin ∈ {8,9}`.
>
> - **Lean:** `Core.Aoyagi.rlctAt_ge_four_of_half_divisorMin` (`8 ≤ v`),
>   `DLN.Aoyagi.rlctAt_coreGen334_ge_four_of_family` + `…_of_survivor_entries` (`hdivisorMin : 8 ≤ …`)
>   (`SandwichCoverValue.lean` / `Corank2Headline334.lean` / `Corank2HeadlineValue334.lean` @ `a50122055`)
> - **Proved.** `4 = 8/2 ≤ v/2 ≤ rlctAt`. No external consumers; the chain is otherwise unchanged.
> - **Status.** sorry-free.

---

**Fidelity note (reviewer target).** The load-bearing fidelity check: `gFin` (the value chart) equals
the σ-conjugate `whole_conj` that the pnp certified `rlct ≥ 4` — established Lean-side by
`blockBlowupMap_conj` (blow-up atoms) + `nativeSel = conj(shearH, σ)` (verified) + `nativePerm =
conj(permP, σ)` (emitted), and cross-checked numerically 288/288. The W3 grep-gate (no chart-level
conjugation / no `Transport334`/`conjResolution` imports in any value-chart DEF) is clean.
