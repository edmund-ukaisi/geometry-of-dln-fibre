# Statement card — S2c: closing the top-component residual of the smooth block

> **Claim.** The smooth-block certificate's remaining hypothesis — a top-dimensional component
> `I ∈ TopDimMinPrimes (sweepFibreRing …)` — is DISCHARGED under the kostant gate: such a component
> EXISTS. So the smooth-block certificate holds with NO `I, hI` input.
>
> - **Lean (THE deliverable):** `DLNFibre.Core.exists_topComponent_smoothBlock_certificate`
>   (`lean/DLNFibre/Core/FibreSmoothBlockExists.lean`)
>   - signature: `[IsAlgClosed k] [CharZero k] (d : Fin (N+2) → ℕ) (r : ℕ)`
>     `(hp : r ≤ d (Fin.last (N+1))) (hq : r ≤ d 0) (h : (kostantPartitions d r).Nonempty)`
>     `(B : Matrix (Fin (d (Fin.last (N+1)))) (Fin (d 0)) k) (hB : B.rank = r) :`
>     `∃ (I : Ideal (sweepFibreRing k d r hp hq))`
>     `  (_ : I ∈ TopDimMinPrimes (sweepFibreRing k d r hp hq))`
>     `  (m : Ideal (sweepFibreRing k d r hp hq ⧸ I)) (_ : m.IsMaximal),`
>     `  Algebra.IsSmoothAt k m ∧`
>     `  Module.Free (Localization.AtPrime m) (Ω[Localization.AtPrime m⁄k]) ∧`
>     `  ∃ n : ℕ, Module.finrank (Localization.AtPrime m) (Ω[Localization.AtPrime m⁄k]) = n ∧`
>     `    (n : ℕ∞) + codimRepCanonical (fibre d B) = (Nat.card (RepCoord d) : ℕ∞)`
> - **Gloss.** Under the kostant gate (NO `I, hI` hypothesis), there EXIST a top-dimensional
>   irreducible component `I` of the reduced fibre ring `sweepFibreRing` (`TopDimMinPrimes` = minimal
>   primes whose quotient realises the full Krull dimension), a maximal ideal `m` of the component
>   ring `A := sweepFibreRing ⧸ I` at which `A` is smooth (a smooth closed point), such that the
>   localized Kähler module `Ω[A_m⁄k]` is free of `A_m`-finrank `n` with `n + codim = ambient`, where
>   `codim = codimRepCanonical (fibre d B)` and `ambient = Nat.card (RepCoord d)`.
> - **Proved.** Composition of two new facts with the banked per-component certificate:
>   (1) `topDimMinPrimes_nonempty` — for a nontrivial Noetherian ring `A`, `TopDimMinPrimes A` is
>   nonempty: `minimalPrimes A` is finite (`minimalPrimes.finite_of_isNoetherianRing`) and nonempty
>   (`Ideal.nonempty_minimalPrimes` for `⊥ ≠ ⊤`); `q ↦ ringKrullDim (A ⧸ q)` attains a max at some
>   minimal `p` (`Set.exists_max_image`); that max IS `ringKrullDim A` because every prime `x`
>   dominates a minimal `q ≤ x` with `coheight x ≤ coheight q = ringKrullDim (A ⧸ q)` (banked
>   `ringKrullDim_quotient_eq_coheight` + `Order.coheight_anti`), and `ringKrullDim A = ⨆ coheight`
>   (`Order.krullDim_eq_iSup_coheight`); the reverse `ringKrullDim (A ⧸ p) ≤ ringKrullDim A` is
>   `ringKrullDim_quotient_le`. (2) `topDimMinPrimes_sweepFibreRing_nonempty` — specialises (1) to the
>   fibre ring, whose `Nontrivial` instance comes from the banked `vanishingIdeal_sweepFibre_ne_top`
>   (model fibre nonempty ⟹ proper vanishing ideal); `IsNoetherianRing` is auto-inferred (MvPolynomial
>   over a field with finitely many vars, quotiented). (3) the banked
>   `exists_smoothBlock_certificate` (the per-component free-rank certificate).
> - **Assumed (the gate, NO `I, hI`).** `[IsAlgClosed k]` (⟹ perfect + `Infinite k`), `[CharZero k]`
>   (codim closed form), `hp/hq` (rank bounds), `h : (kostantPartitions d r).Nonempty`,
>   `hB : B.rank = r`. `hN : (0 : Fin (N+2)) ≠ Fin.last (N+1)` (i.e. `N ≥ 1`) is DERIVED in-proof, not
>   assumed (it is structurally true for `Fin (N+2)`). The `[Algebra.IsSmoothAt k m]` per-point input
>   of the per-component certificate is discharged by `exists_isSmoothAt_isMaximal_component` (banked,
>   inside `exists_smoothBlock_certificate`).
> - **Cited.** None new. All upstream lemmas are PROVED Mathlib or PROVED `Core` engine, sorry-free.
> - **Deferred (unchanged from S2).** (a) Full component INCIDENCE: the produced `m` is *some* closed
>   point of the dense smooth open of *some* top component, not a prescribed θ-generic geometric point.
>   (b) The conormal/Jacobian module free of rank `= codim` is a DIFFERENT statement (not the Kähler
>   module proved here). NOTE: S2 Deferred (c) — "non-emptiness of `TopDimMinPrimes (sweepFibreRing)`"
>   — is exactly what THIS card resolves; it is no longer deferred.
> - **Status.** sorry-free; axiom-clean.

## Companion results (same module)

- `DLNFibre.Core.topDimMinPrimes_nonempty` — **generic engine** (pure commutative algebra,
  network-free, reusable): for ANY nontrivial Noetherian ring `A` (no finite-dimensionality
  hypothesis), `(TopDimMinPrimes A).Nonempty`. Axiom-clean.
- `DLNFibre.Core.topDimMinPrimes_sweepFibreRing_nonempty` — the gate-specialised nonemptiness for the
  fibre coordinate ring. Axiom-clean.

## Axiom check (`#print axioms`)

`topDimMinPrimes_nonempty`, `topDimMinPrimes_sweepFibreRing_nonempty`,
`exists_topComponent_smoothBlock_certificate`
→ `[propext, Classical.choice, Quot.sound]` (axiom-clean; no `sorryAx`, no extra axioms).

## Build / gate

- `scripts/lb DLNFibre.Core.FibreSmoothBlockExists` → green (3089 jobs), zero warnings in-module.
- `scripts/sorries` → `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
- `Core`-only: imports `DLNFibre.Core.FibreSmoothBlock` only. Does NOT import `DLNFibre.DLN`.

## Controller wiring note

`lean/DLNFibre.lean` (single-writer aggregator) must add `import DLNFibre.Core.FibreSmoothBlockExists`
at the end (after the existing `import DLNFibre.Core.FibreSmoothBlock`). I did NOT edit the aggregator.
