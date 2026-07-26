# Statement cards — the σ_p1 loss-symmetry TRANSPORT (16 canonical → ∀-144 over-vanishing)

Seat: the σ_p1-transport assembly (steps 1–6). Module:
`lean/DLNFibre/DLN/Aoyagi/Corank2OverVanishTransport334.lean` (branch
`expedition/aoyagi-r2ov-sigma-transport`, off `a6c287f94`). All results sorry-free and axiom-clean
`[propext, Classical.choice, Quot.sound]` — machine-verified by the in-file
`#assert_banked_clean_batch` (no `sorryAx`, no cite). The pre-existing crux `sumSq_coreGen_symm`
(a3f030 @ `a6c287f94`) is the one substantive lemma; this seat is the assembly around it.

## The picture

The whole-conjugate born-native fan (`Corank2NativeFan334`) has one leaf composite `gFlat idx` per
pivot-path `idx = (p1, p2, p3)` with `p1 ∈ S1` (the 9 A0-dominant slots). For each dominant pivot
`p1 = A0[i,j]`, the coordinate permutation `σ_p1 = colswap(j) ∘ rowswap(i)` (acting on `Fin 21`: it
row/col-swaps the A0 grid and col-swaps the A1 grid) is a genuine **loss-symmetry** of the `(3,3,4)`
network, and the born-native chart at `p1` IS the `σ_p1`-conjugate of the canonical `p1 = 20` chart.
So the over-vanishing product-germ domination transports from the 16 canonical `p1 = 20` leaves
(`(p2,p3) ∈ {1,5,6,7}²`, the pattern-A/B seats) to all `9 × 16 = 144` over-vanishing leaves.

## Setup / conventions

- **`σ_p1`** (`sigP0..sigP7`, `sigP20 = id` implicit) — the 9 loss-symmetry permutations, each an
  `Equiv.Perm (Fin 21)` built via `Function.Involutive.toPerm` from an explicit involution index map
  `sigC0..sigC7` (so `⇑σ = σ.symm = sigC`, both kernel-computable — the key to the `decide`-discharged
  conjugation identities). Derived from the crux's `hA0`/`hA1` spec; cross-validated against the
  emitted `cperm` data (`conj(cperm20, σ_p1) = cperm_p1`) and the fan's `sigmaC1Fs`/`sigmaC2Fs` centre
  data (all by `decide`).
- **`conjChart σ F := fun w t ↦ F (w∘σ) (σ⁻¹ t)`** — the coordinate-permutation conjugate of a chart
  (matches `blockBlowupMap_conj`'s LHS). Functorial (`conjChart_comp`), fixes `id`.
- **`gComposite p1 p2 p3`** — `gFlat idx` with the `Idx` projections spelled out
  (`gFlat_eq_gComposite : rfl`).

---

> **Claim (step 2) — the loss symmetry at each dominant pivot.** For each `p1 ∈ {0,…,7}`, the
> `coreGen` loss is invariant under `σ_p1`: `∑ₖ coreGen(w∘σ_p1)ₖ² = ∑ₖ coreGen(w)ₖ²`.
>
> - **Lean:** `DLNFibre.DLN.Aoyagi.OverVanishTransport334.loss_symm_P0 … loss_symm_P7`
>   (`lean/DLNFibre/DLN/Aoyagi/Corank2OverVanishTransport334.lean`, branch
>   `expedition/aoyagi-r2ov-sigma-transport`)
> - **Gloss.** `σ_p1` permutes the 21 weight coordinates as a row/col symmetry of `A0` (rows `0↔i`,
>   cols `0↔j`) plus the matching A1 column swap (`0↔i`); the crux `sumSq_coreGen_symm` (fed the
>   decidable `hA0_Pn`/`hA1_Pn`) then gives Frobenius-norm invariance of `A1·A0`.
> - **Proved.** All 8 pivots, unconditionally.
> - **Assumed / Cited / Deferred.** none.

> **Claim (steps 3–4) — the born-native chart transports.** `nativeChart1 p1 = conjChart σ_p1
> (nativeChart1 20)` and `gComposite p1 (σ_p1 p2) (σ_p1 p3) = conjChart σ_p1 (gComposite 20 p2 p3)`.
>
> - **Lean:** `nativeChart1_conj_P0 … _P7`, `gComposite_conj_P0 … _P7` (same module). Engine:
>   `conjChart_comp`, `conjChart_id`, `conjChart_blockBlowupMap`, `conjChart_permCoord`,
>   `conjChart_blockShear_qdisp` (with `conjTermData` / `sterm_conjTermData`).
> - **Gloss.** `nativeChart1 = nativeSel ∘ nativePerm`; the permutation atom conjugates to the
>   conjugate permutation (the `cperm` data-match by `decide`), and the `qdisp` block-shear atom
>   conjugates to the σ-conjugated-term-data shear. NOTE the shear conjugation MIXES the two signed-
>   term families (a term slides between the `t1`/`t2` slots), so only the `qdisp` SUM matches the
>   emitted `t1P`/`t2P` (verified per coordinate). The block blow-ups conjugate to their permuted-
>   centre siblings (`blockBlowupMap_conj`), with `σ_p1 S1 = S1`, `σ_p1 20 = p1`,
>   `σ_p1 (sigmaC1Fs 20) = sigmaC1Fs p1`, `σ_p1 (sigmaC2Fs 20) = sigmaC2Fs p1` (all `decide`).
> - **Proved.** All 8 pivots, unconditionally. The centre-image `decide`s cross-validate the σ
>   derivation against the independently machine-generated fan data.
> - **Assumed / Cited / Deferred.** none.

> **Claim (step 5) — the product germ reindexes.** `monoSumSqGerm a Z (w∘σ) = monoSumSqGerm (a∘σ⁻¹)
> (σ Z) w` for any coordinate permutation `σ`.
>
> - **Lean:** `monoSumSqGerm_conj` (same module).
> - **Gloss.** The monomial exponent reindexes by `σ⁻¹`, the sum-of-squares block by `σ`
>   (`Equiv.prod_comp` + `Finset.sum_image`).
> - **Proved / Assumed / Cited / Deferred.** Proved unconditionally; nothing assumed/cited/deferred.

> **Claim (step 6) — the domination transport.** Generic: from a base product-germ domination for a
> chart `H20` at `(a, Z)`, plus `σ`'s loss symmetry and `σ⁻¹ = σ`, the σ-conjugate chart
> `conjChart σ H20` dominates the transported germ `monoSumSqGerm (a∘σ⁻¹) (σ Z)`. Per-pivot
> (`leaf_domination_Pn`): the over-vanishing domination at leaf `(p1, σ_p1 p2, σ_p1 p3)` follows from
> the canonical `(20, p2, p3)` domination.
>
> - **Lean:** `domination_transport`; `leaf_domination_P0 … _P7`; helper `sumSqFam_coreGen_conj`.
> - **Gloss.** `leaf_domination_Pn` takes the canonical leaf's product-germ domination (chart
>   `gComposite 20 p2 p3 ∘ Ψ_20`, data `(a, Z)`) as `hbase` and produces the domination for the
>   `p1`-leaf's native chart `gComposite p1 (σ_p1 p2)(σ_p1 p3) ∘ (σ_p1-conjugate of Ψ_20)` at the
>   `σ_p1`-transported data `(a∘σ_p1, σ_p1 Z)`. Combining the loss symmetry, the chart conjugation,
>   and the germ reindex.
> - **Proved.** The full transport LOGIC, sorry-free, for all 8 non-canonical dominant pivots (the
>   16 `p1 = 20` leaves are the base). `hbase` is a hypothesis — one supplies each of the 16
>   canonical `canon_domination` facts (`OverVanishCanon334` / `OverVanishA_20_*` / `OverVanishB_20_*`)
>   via `gFlat_eq_gComposite`, yielding all `8 × 16 = 144` transported leaves.
> - **Assumed.** `hbase` (the per-`(p2,p3)` canonical domination) — supplied at wiring.
> - **Cited.** none.
> - **Deferred.** the concrete `∀`-over-`Idx` assembly module that imports the 16 canonical leaf
>   modules and applies `leaf_domination_Pn` over the 144 over-vanishing pivot-paths — MECHANICAL
>   wiring, gated only on the 16 canonical modules being co-present in one import graph (cross-branch
>   integration, controller). No new mathematics.
> - **Status.** sorry-free.
