# Statement card — S2 smooth-block certificate (standard-smooth local model)

> **Claim.** At a smooth closed point of a top-dimensional component of the fibre, the
> standard-smooth local model holds: the local Kähler/cotangent module `Ω` is FREE, and its rank is
> the relative dimension `= ambient − codim`, with `codim` the PROVED closed-form fibre codimension
> `C + δ` (`C = cCodim d r`, `δ = r·(d_N + d_0 − r)`). Equivalently: `rank(Ω) + codim = ambient`.
>
> ⚠ **Fidelity note (Codex-vetted).** The brief's loose phrasing "Ω free of rank = codim" CONFLATES
> two complementary modules. For a smooth `X ⊆ 𝔸^ambient`, the **Kähler** module `Ω[O_X⁄k]` is free
> of rank `= dim X = ambient − codim` (relative dimension); the module free of rank `= codim` is the
> **conormal** `I/I²` (Jacobian ker/coker). This card reports the Kähler module and pins its rank as
> the complement of codim. It does NOT claim the conormal statement.
>
> - **Lean (THE deliverable):** `DLNFibre.Core.fibre_smoothBlock_certificate`
>   (`lean/DLNFibre/Core/FibreSmoothBlock.lean` @ `bf7fae1f`)
>   - signature: `[IsAlgClosed k] [CharZero k] (d : Fin (N+2) → ℕ) (r : ℕ)`
>     `(hp : r ≤ d (Fin.last (N+1))) (hq : r ≤ d 0) (h : (kostantPartitions d r).Nonempty)`
>     `(B : Matrix (Fin (d (Fin.last (N+1)))) (Fin (d 0)) k) (hB : B.rank = r)`
>     `(I : Ideal (sweepFibreRing k d r hp hq)) (hI : I ∈ TopDimMinPrimes (sweepFibreRing k d r hp hq))`
>     `(m : Ideal (sweepFibreRing k d r hp hq ⧸ I)) [m.IsMaximal] [Algebra.IsSmoothAt k m] :`
>     `Module.Free (Localization.AtPrime m) (Ω[Localization.AtPrime m⁄k]) ∧`
>     `∃ n : ℕ, Module.finrank (Localization.AtPrime m) (Ω[Localization.AtPrime m⁄k]) = n ∧`
>     `(n : ℕ∞) + codimRepCanonical (fibre d B) = (Nat.card (RepCoord d) : ℕ∞)`
> - **Gloss.** Fix a rank-`r` target `B`, a top-dimensional irreducible component `I` of the reduced
>   fibre ring `sweepFibreRing` (`TopDimMinPrimes` = minimal primes whose quotient realises the full
>   Krull dimension), and a maximal ideal `m` of the component ring `A := sweepFibreRing ⧸ I` at which
>   `A` is smooth (`Algebra.IsSmoothAt k m`). Then the localized Kähler module `Ω[A_m⁄k]` is a free
>   `A_m`-module, and its `A_m`-finrank `n` satisfies `n + codim = ambient`, where
>   `codim = codimRepCanonical (fibre d B)` is the geometric fibre codimension and
>   `ambient = Nat.card (RepCoord d)` is the number of coordinate variables (matrix entries). So
>   `n = ambient − codim` is the relative/component dimension.
> - **Proved.** (1) `Ω[A_m⁄k]` free (`free_kaehler_localizationAtPrime_of_isSmoothAt`: smooth ⟹
>   formally smooth ⟹ `Ω` projective ⟹ free over the local ring); (2) `finrank Ω = n` and
>   `ringKrullDim (A_m) = n` (the generic engine + banked `finrank_kaehler_localizationAtPrime_eq` /
>   `ringKrullDim_localizationAtPrime_eq_of_isSmoothAt`); (3) `ringKrullDim (A_m) = ringKrullDim A`
>   (local↔global at a closed point of a fin-type domain, via the third-iso double-quotient flatten +
>   the banked `height_eq_ringKrullDim_of_isMaximal_fintype`); (4) `codim + ringKrullDim A = ambient`
>   (`I` top-dimensional ⟹ `dim A = dim (sweepFibreRing) = varietyDim (sweepFibre)`, + the
>   reducible-locus catenary `codimRepCanonical_add_varietyDim_eq_card_of_nonempty`). The codim is
>   pinned to the closed form `C + δ` by `FibreCodimFinal.codimRepCanonical_fibre_eq_cCodim_add_shift`
>   (consumed via same-rank invariance `codimRepCanonical_fibre_eq_of_rank_eq`).
> - **Assumed.** `[IsAlgClosed k]` (⟹ perfect, so the residue/Kähler smoothness machinery fires; also
>   ⟹ `Infinite k`), `[CharZero k]` (inherited from the proved codim closed form), `hB : B.rank = r`,
>   `h : (kostantPartitions d r).Nonempty` (carried by `cCodim`), and the **per-point hypothesis**
>   `[m.IsMaximal] [Algebra.IsSmoothAt k m]` — that `m` is a smooth closed point. The last is the
>   honest "smooth closed point" localisation of "generic point"; its satisfiability is discharged
>   separately (see Proved companion `exists_isSmoothAt_isMaximal_component`).
> - **Cited.** None new. All upstream lemmas (generic smoothness, the codim closed form, the catenary)
>   are PROVED in the `Core` engine, sorry-free; this module reuses them. No external/cited analytic
>   interface (no `rlct`-style assumption) — this is the geometric upper-bound model only.
> - **Deferred.** (a) The full **component incidence**: the smooth closed point `m` produced by
>   `exists_isSmoothAt_isMaximal_component` is *some* closed point of the component (its smooth locus is
>   dense), not certified to be a prescribed/θ-generic geometric point — same residual honestly flagged
>   in `FibreComponentOrbitTransport.exists_isSmoothAt_chartDsig_unconditional`. (b) The **conormal /
>   Jacobian** module free of rank `= codim` is a DIFFERENT statement, not proved here (and not the
>   Kähler module). (c) Non-emptiness of `TopDimMinPrimes (sweepFibreRing)` for a concrete `d` is not
>   witnessed in-file (the certificate is stated for any given top component `I`).
> - **Status.** sorry-free; axiom-clean.

## Companion results (same module, same SHA)

- `DLNFibre.Core.kaehler_free_and_finrank_add_dim_of_isSmoothAt` — **the generic engine** (network-free):
  for any finite-type `k`-algebra `A` (field `k`) and smooth maximal `m`, `Ω[A_m⁄k]` is free of
  finrank `n` with `ringKrullDim (A_m) = n`. Axiom-clean.
- `DLNFibre.Core.free_kaehler_localizationAtPrime_of_isSmoothAt` — the standalone freeness instance.
- `DLNFibre.Core.exists_isSmoothAt_isMaximal_component` — **non-vacuity**: a smooth closed point of the
  top component EXISTS (fp domain over alg-closed `k` ⟹ dense, open smooth locus; Jacobson ⟹ contains a
  closed point). Axiom-clean.
- `DLNFibre.Core.exists_smoothBlock_certificate` — **fully closed over the smooth-point hypothesis**
  (existence ∘ per-point): given a top component `I`, there EXISTS a smooth closed point `m` with
  `Ω[A_m⁄k]` free of finrank `n`, `n + codim = ambient`. (Still takes `I ∈ TopDimMinPrimes` as a
  hypothesis — "fully closed" means it discharges the `[Algebra.IsSmoothAt k m]` input, NOT that it
  witnesses a top component exists; the latter is Deferred (c).) Axiom-clean.
- `DLNFibre.Core.codim_add_ringKrullDim_component_eq_card` — the bridge `codim + dim(component) =
  ambient` for a top component.
- `DLNFibre.Core.ringKrullDim_localizationAtPrime_component_eq` /
  `DLNFibre.Core.ringKrullDim_doubleQuot_mvPoly_eq` — the double-quotient local↔global dimension glue.

## Axiom check (`#print axioms`)

All four headlines:
`fibre_smoothBlock_certificate`, `kaehler_free_and_finrank_add_dim_of_isSmoothAt`,
`exists_smoothBlock_certificate`, `exists_isSmoothAt_isMaximal_component`
→ `[propext, Classical.choice, Quot.sound]` (axiom-clean; no `sorryAx`, no extra axioms).

## Build / gate

- `scripts/lb DLNFibre.Core.FibreSmoothBlock` → green (3088 jobs), zero warnings in-module.
- `scripts/sorries` → `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
- `Core`-only: imports `SmoothPointRegular`, `FibreCodimFinal`, `FibreComponentOrbitTransport`,
  `RadicalCatenary`, `OrbitTangentCotangent`, `Mathlib.RingTheory.Spectrum.Prime.Jacobson`. Does NOT
  import `DLNFibre.DLN`.

## Controller wiring note

`lean/DLNFibre.lean` (single-writer aggregator) must add `import DLNFibre.Core.FibreSmoothBlock` at the
end. I did not edit the aggregator.
