# Statement card — Brick D piece (ii): chart (5) determinantal big-cell CoV

Thread `genm-sj5-chart5` (off `origin/genm-sj5-brickdcont` @ `c5954d6cc`). Module
`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJIncidenceChart5BigCell.lean`. Build green via
`scripts/lb DLNFibre.DLN.RLCT.Validate.RouteMSJIncidenceChart5BigCell`; all results axiom-clean
`[propext, Classical.choice, Quot.sound]` (forced recompile). Source: `incidence-cert.md` §3b(5), §3b(b);
spec `chart45-spec.md` §"Chart (5)".

---

> **Claim (CoV, Jacobian ≡ 1).** The chart-(5) big-cell change of variables — the `W₂₂ ↦ E`
> translation of the last block by the Schur shift `C·A⁻¹·B` — preserves the Lebesgue lintegral over
> the block product, for any measurable `ℝ≥0∞`-integrand `f`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.chart5_bigcell_cov`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJIncidenceChart5BigCell.lean` @ `192a27c27`)
> - **Gloss.** For blocks `(abc, D)` in `Chart5FixedBlocks r s t × (Fin s → Fin t → ℝ)` (pivot `A : r×r`,
>   `B : r×t`, `C : s×r`, last block `D : s×t`, all over the raw pi type) and measurable
>   `f : (Chart5FixedBlocks r s t) × (Fin s → Fin t → ℝ) → ℝ≥0∞`:
>   `∫⁻ p, f (p.1, p.2 + chart5Shift p.1) = ∫⁻ p, f p`, where `chart5Shift (A,B,C) = C · A⁻¹ · B`.
> - **Proved.** The equality holds **unconditionally** (no `det A ≠ 0` needed): the shear
>   `(abc, E) ↦ (abc, E + C·A⁻¹·B)` is measure-preserving on all of block space. Proof = Fubini
>   (`lintegral_prod`, over `volume = volume.prod volume`) isolating the last block, then Haar
>   translation-invariance (`lintegral_add_right_eq_self`) fibrewise. It is an **∫-level identity**,
>   never a pointwise `≤` (bltj guard 1). The Jacobian is genuinely `≡ 1` (pure `W₂₂`-translation);
>   no `|det D|` power is dropped (bltj guard 2 — those powers live in the linear `Qb`-minor chart (1)
>   + the `B`-shear chart (3), composed at the assembly, not here).
> - **Assumed.** `Measurable f` only.
> - **Cited.** none (Mathlib measure theory: `lintegral_prod`, `lintegral_add_right_eq_self`,
>   `volume_eq_prod`).
> - **Deferred.** the finite-minor **atlas** (arbitrary `(I,J)` minor → top-left via a perm CoV, G2)
>   and the **gluing/union coverage** (G3, piece (v)) — the assembly's concern, parked on `genm-bltj`.
>   The radial-finiteness `∫₀^δ r^{C_{ℓ,s}−1−2q} dr` (banked `RouteMSJRadialPolar` + the piece-(iv)
>   exponent gate) is the assembly step downstream of this CoV.
> - **Status.** sorry-free

> **Claim (rank geometry).** On the chart `det W₁₁ ≠ 0`, `rank W = r + rank E` and `{rank W ≤ r} = {E = 0}`
> where `E = W₂₂ − W₂₁ W₁₁⁻¹ W₁₂`; in the CoV `E`-coordinates the rank-drop locus is the slice `{E = 0}`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.chart5_rank_eq`, `chart5_rank_le_iff_schur`,
>   `chart5_rank_le_iff_reassembled` (same file @ `192a27c27`).
> - **Gloss.** With `A : r×r` invertible (`IsUnit A.det`): `(fromBlocks A B C D).rank = r + (D − C·A⁻¹·B).rank`;
>   `(fromBlocks A B C D).rank ≤ r ↔ D = C·A⁻¹·B`; and `(fromBlocks A B C (E + chart5Shift (A,B,C))).rank ≤ r ↔ E = 0`.
> - **Proved.** All three, for the top-left pivot block.
> - **Assumed.** `IsUnit A.det` (the chart condition).
> - **Cited.** the block-LU / Schur rank core `Core.SchurChartIff.rank_fromBlocks_invertible₁₁` /
>   `rank_le_iff_schur_eq` (banked, sorry-free; itself resting on the Core rank-normal-form primitives).
>   `chart5_rank_eq` / `chart5_rank_le_iff_schur` are chart-5-shape re-exports; `chart5_rank_le_iff_reassembled`
>   is the fresh bridge.
> - **Deferred.** general `(I,J)`-minor pivot (needs the perm reindex, G2 — atlas, deferred).
> - **Status.** sorry-free

---

**Non-vacuity.** In-file `example`: the `(2,2,1)`-minor cell `W = [[1,0],[0,0]]` has `rank ≤ 1` with `E = 0`.

**Which GAPs closed.** G1 (the translation-in-`W₂₂` CoV, `|det|≡1`) — CLOSED. G2 (per-minor perm CoV) and
G3 (finite-minor atlas gluing / union coverage) — deferred to the assembly per the "do NOT build the
union/coverage" guard (G3 is the coverage; G2 is per-minor reindex toward it).
