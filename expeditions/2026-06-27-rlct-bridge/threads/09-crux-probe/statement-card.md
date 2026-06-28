# Statement card — Phase-2 crux: orbit-dim squeeze over a perfect field / over ℝ

> **Claim (crux, A6.1 reverse).** For a finite-type orbit closure over a **perfect, infinite** field `k`
> (no algebraic closedness), the orbit tangent image rank bounds the variety dimension:
> `finrank_k (range δ⁰_M) ≤ varietyDim (canonicalCoord '' orbitRankLocus M)`.
>
> - **Lean:** `DLNFibre.Core.finrank_range_deformationδ_le_varietyDim`
>   (`lean/DLNFibre/Core/OrbitTangentCotangent.lean` @ `0084b645`)
> - **Gloss.** With `[Field k] [PerfectField k] [Infinite k]`, for a tuple `M`, the `k`-dimension of
>   `range (deformationδ M M)` (the orbit tangent image δ⁰) is `≤` the variety dimension of the orbit
>   rank locus. Previously stated `[IsAlgClosed k]`; algebraic closedness was vestigial.
> - **Proved.** The inequality over `[PerfectField k] [Infinite k]`, axiom-clean
>   `[propext, Classical.choice, Quot.sound]`.
> - **Assumed.** `[PerfectField k]` (residue-field formal smoothness, smooth-point regularity) +
>   `[Infinite k]` (orbit primeness / domain / dense orbit points). Both supplied by `[CharZero k]`
>   as Mathlib instances; ℝ qualifies.
> - **Cited.** none (`FormallySmooth.of_perfectField`, `dense_smoothLocus_of_perfectField` are Mathlib
>   theorems, not citations; the M2 dim bridge is in-engine).
> - **Deferred.** none for this inequality.
> - **Status.** sorry-free.

> **Claim (squeeze over ℝ — the crux demonstration).** Over any characteristic-zero field (ℝ included),
> the orbit-closure variety dimension EQUALS the orbit tangent rank:
> `varietyDim (canonicalCoord '' orbitRankLocus M) = finrank_k (range δ⁰_M)`.
>
> - **Lean:** `DLNFibre.Core.varietyDim_orbitRankLocus_eq_finrank_range_deformationδ`
>   (`lean/DLNFibre/Core/VoigtDischarge.lean` @ `0084b645`); witnessed at `k = ℝ` by the in-file
>   `example`s (squeeze + Voigt's lemma on the `(2,2,2)` `(1,1)`-orbit).
> - **Gloss.** With `[CharZero k]`, `le_antisymm` of the unconditional submersion bound (`≤`,
>   `[CharZero][Infinite]`) and the relaxed reverse inequality (`≥`, `[PerfectField]`). Both supplied
>   by `[CharZero k]`.
> - **Proved.** The equality over `[CharZero k]`, and (downstream) Voigt's lemma
>   `codimRep (canonicalCoord) (orbitRankLocus M) = orbitLinearCodim M` over `[CharZero k]` — i.e. the
>   real codimension formula `codim_ℝ = orbitLinearCodim` over ℝ. Axiom-clean.
> - **Assumed.** `[CharZero k]` (⟹ `[PerfectField]` + `[Infinite]`).
> - **Cited.** none.
> - **Deferred.** The fibre-level transfer `T′` (`varietyDim_ℝ(fibre) = varietyDim_K(fibre)`) is NOT
>   here — it needs L7 (orbit-rank base-change invariance, route pinned, packaging) + L8 (the chart
>   δ-shift over ℝ, next wave). This card is the ORBIT-level squeeze, the crux input to `T′`.
> - **Status.** sorry-free.

> **L7 (pinned, not yet proved).** `finrank_K (range (deformationδ (M.map ι) (M.map ι))) =
> finrank_k (range (deformationδ M M))` for `ι : k →+* K` a field extension.
> - **Route.** R2 via the banked `DLNFibre.Core.finrank_range_baseChange` (specialized brick at
>   `deformationδ` is provable sorry-free; one tensor-conjugacy identity remains —
>   `deformationδ_K (M.map ι) ≅ (deformationδ_k M).baseChange K`). Packaging, not new math.
> - **Status.** statement pinned; not formalised (the conjugacy step is a future-wave packaging tide).
