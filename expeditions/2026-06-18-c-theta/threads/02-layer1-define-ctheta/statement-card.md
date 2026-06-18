# Statement card — Layer 1: define `C` and `θ` (combinatorial)

Module `lean/DLNFibre/Core/CTheta.lean`. Built on the committed Cor 3.5 quadratic form
(`Core.OrbitLinearCodim.orbitLinearCodim_eq_multSum`). Base commit `07216ed` (work uncommitted in the
`c-theta` worktree at audit time; controller bumps the SHA on integration).

---

> **Claim (the form).** `codimForm N m` is the Cor 3.5 quadratic form
> `∑_{1≤i≤u≤j≤v≤N} m_{i-1,j-1} · m_{uv}` as a functional of a ℤ-array `m`, and it is *literally* the
> right-hand side of the committed headline.
>
> - **Lean:** `DLNFibre.Core.codimForm`, `DLNFibre.Core.codimForm_multiplicityArray`
>   (`lean/DLNFibre/Core/CTheta.lean`)
> - **Gloss.** `codimForm N m` is the four nested `Finset.Icc` sums `∑ i∈[1,N] ∑ u∈[i,N] ∑ j∈[u,N]
>   ∑ v∈[j,N], m (i-1) (j-1) * m u v`. `codimForm_multiplicityArray` proves, by `rfl`, that on the
>   multiplicity array of any list `L` it equals the RHS of `orbitLinearCodim_eq_multSum`.
> - **Proved.** The `rfl` identity: `codimForm` is the committed headline form with the array abstracted.
> - **Assumed / Cited / Deferred.** none.
> - **Status.** sorry-free.

> **Claim (Kostant partitions).** The Kostant partitions of `d : Fin (N+1) → ℕ` with corner `m_{0N}=r`
> form a finite set: ℕ-arrays `m_{ij}` (`i,j : Fin (N+1)`) vanishing off `i ≤ j`, with
> `d_k = ∑_{i ≤ k ≤ j} m_{ij}` at every vertex `k` and `m_{0,last}=r`.
>
> - **Lean:** `DLNFibre.Core.kostantPartitions`, `DLNFibre.Core.mem_kostantPartitions`
>   (`lean/DLNFibre/Core/CTheta.lean`)
> - **Gloss.** `kostantPartitions d r : Finset (Fin(N+1)×Fin(N+1) → ℕ)` is the bounded product
>   `∏_p range(d p.1 + 1)` filtered by: `m p = 0` when `¬ p.1 ≤ p.2`; `kostantAt d m k` (i.e.
>   `d k = ∑_{p.1 ≤ k ≤ p.2} m p`) for all `k`; and `m (0, last N) = r`. `mem_kostantPartitions`
>   characterises membership as `(∀ p, m p ≤ d p.1) ∧ (support) ∧ (∀ k, kostant) ∧ (corner = r)`.
> - **Proved.** Finiteness (it is a `Finset`); the membership iff; the bound `m p ≤ d p.1` is sound
>   (each `m_{ij}` contributes to `d_i`).
> - **Assumed / Cited / Deferred.** none. (The Kostant constraint matches the engine convention
>   `d_k = ∑_{i ≤ k ≤ j} m_{ij}`, i.e. `rankPattern` diagonal = `cumul` of `multiplicityArray`.)
> - **Status.** sorry-free.

> **Claim (`C`, `θ`).** `C = min` of `codimForm` over the Kostant partitions; `θ = #{minimisers}`.
>
> - **Lean:** `DLNFibre.Core.cCodim`, `DLNFibre.Core.numTop` (`lean/DLNFibre/Core/CTheta.lean`)
> - **Gloss.** `cCodim d r h := (kostantPartitions d r).inf' h (fun m ↦ codimForm N (extendℤ m))`
>   (needs nonemptiness `h`); `numTop d r h := card of the minimisers` (those `m` with
>   `codimForm = cCodim`). `extendℤ` is the `0`-off-box ℤ-extension of the `Fin`-indexed `m`.
> - **Proved.** `cCodim`/`numTop` are well-defined (min / minimiser-count over a finite nonempty set).
> - **Assumed.** `cCodim` carries the nonemptiness hypothesis `h : (kostantPartitions d r).Nonempty`.
> - **Cited.** none.
> - **Deferred (the geometric reading).** `cCodim`/`numTop` are the **combinatorial** `C`/`θ` — min /
>   minimiser-count of a ℤ-quadratic form. Their equality with the **geometric** codimension /
>   component-count of the rank-`r` locus `Σ^r` rides on the deferred Voigt hypothesis `hVoigt`
>   (`Core.OrbitCodim`, geometric codim = expected codim `orbitLinearCodim`). NOT asserted here.
> - **Status.** sorry-free.

> **Claim (witness, Ex 4.3).** For `d = (2,2,2)`, `r = 0`: `C = 3` and `θ = 1`.
>
> - **Lean:** `DLNFibre.Core.cCodim_d222_zero`, `DLNFibre.Core.numTop_d222_zero`,
>   `DLNFibre.Core.kostantPartitions_d222_nonempty`, `DLNFibre.Core.mMin_mem`
>   (`lean/DLNFibre/Core/CTheta.lean`)
> - **Gloss.** `cCodim ![2,2,2] 0 _ = 3` and `numTop ![2,2,2] 0 _ = 1`. The six Kostant partitions of
>   `(2,2,2)` with `r=0` have `codimForm` values `{4,3,5,4,5,8}`; the minimum `3` is attained only at
>   the `(1,1)`-orbit `m₀₀=m₀₁=m₁₂=m₂₂=1` (`mMin`).
> - **Proved.** Both equalities, by axiom-clean kernel `decide +kernel` (no `native_decide`).
>   `#print axioms` = `{propext, Classical.choice, Quot.sound}`.
> - **Assumed / Cited / Deferred.** none (numerically cross-checked in Python; matches the existing
>   `(2,2,2)` `(1,1)`-orbit codim-3 witness in `DeformationExt`/`OrbitLinearCodim`).
> - **Status.** sorry-free.

---

## Audit

- `python3 scripts/sorries` → `0 sorry, 0 #exit, 0 native_decide, 0 axiom` (whole library).
- `lake build DLNFibre.Core.CTheta` green (≈10 s; the two witness `decide +kernel` enumerate the
  `3^6 = 729` upper-triangular candidates after the off-triangle carrier clamp, ~2.8 GB peak RSS).
- `#print axioms` on all four headline groups: only `propext`, `Classical.choice`, `Quot.sound`.
- Fidelity review (Lean statement ↔ informal claim): **PASS** (reviewer, 2026-06-18). One minor
  docstring overclaim flagged on `numTop_d222_zero` (a geometric "one top-dimensional component"
  reading) and fixed by hedging it to the deferred `hVoigt`. No signature-level mismatch or overclaim;
  witness independently re-derived (6 partitions, form values `{3,4,4,5,5,8}`, min 3 unique).
- **Status: sorry-free + reviewed.**

## Encoding choices that needed judgement

- **Partition as `Fin(N+1)×Fin(N+1) → ℕ`, extended to `ℤ → ℤ → ℤ` by `extendℤ`.** The committed form
  is ℤ-indexed (`multiplicityArray L : ℤ → ℤ → ℤ`); `codimForm` is kept ℤ-indexed so it is *literally*
  the headline form (`codimForm_multiplicityArray` is `rfl`), and the finite partitions are mapped in
  via `extendℤ` (`0` off the `Fin` box). The alternative — a separate `Fin`-indexed form — would have
  forced re-deriving the index machinery and broken the `rfl` cross-check.
- **Finiteness via `Fintype.piFinset` with an off-triangle clamp.** The `p`-carrier is
  `range (d p.1 + 1)` on the triangle `p.1 ≤ p.2` (so `m_{ij} ≤ d_i`, since vertex `i ∈ [i,j]`) and
  `range 1 = {0}` off it (forcing `m_{ij} = 0` for `i > j`). The clamp keeps only the `~6`
  upper-triangular entries varying — `3^6 = 729` candidates at `(2,2,2)` rather than `3^9` for a
  uniform bound, cutting the witness `decide +kernel` from ~130 s / 6 GB to ~10 s / 2.8 GB. The
  support `m_{ij} = 0` (`i > j`) is then free from carrier membership, so the `filter` carries only
  the Kostant constraint + corner. `mem_kostantPartitions` still exposes the same four-clause iff
  (bound, support, Kostant, corner) — the downstream contract is unchanged.
