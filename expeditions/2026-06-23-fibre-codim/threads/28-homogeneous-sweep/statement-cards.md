# Statement cards — thread 28 (route c: the equivariant homogeneous sweep)

Two deliverables, both sorry-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`),
whole-library green. SHAs to be pinned by the controller at integration.

---

## Card 1 — the route-c arithmetic assembly `codim(fibre d B) = C + δ` (conditional bank)

> **Claim.** For a rank-`r` target `B` (`N ≥ 1`, alg-closed char 0), the geometric codimension of the
> multiplication-map fibre is the combinatorial codimension `C = cCodim d r` plus the matrix-stratum
> shift `δ = r·(d_N + d_0 − r)` — **given** the homogeneous-sweep dimension identity and the
> closure/density bridge.

- **Lean:** `DLNFibre.Core.codimRepCanonical_fibre_eq_cCodim_add_shift_of_sweep`
  (`lean/DLNFibre/Core/RouteCAssembly.lean`)
  and the primed variant `…_of_sweep'` (catenary hypotheses discharged).
- **Gloss.** `codimRepCanonical (fibre d B) = (cCodim d r h).toNat + r*(d_N + d_0 − r)`. The base
  theorem carries four named hypotheses: `hSweep` (`varietyDim Σ^r = δ + varietyDim F`), `hClosure`
  (`varietyDim Σ^r = varietyDim Σ̄^r`), and the two reducible-locus catenary relations `hCatFibre`,
  `hCatSigma` (`codim Z + varietyDim Z = card`). The proof is the purely-additive chain
  `C + δ + dim F = C + dim Σ̄^r = card = codim F + dim F`, left-cancelling the finite `dim F`. The
  primed variant takes the nonemptiness of `F` and `Σ̄^r` instead of `hCatFibre`/`hCatSigma`,
  discharging the latter via Card 2's corollary — leaving ONLY `hSweep` + `hClosure`.
- **Proved.** The arithmetic chaining + the `dim Σ̄^r = C` plug (LANDED `SigmaCodim`) + the finite
  cancellation. The primed variant additionally discharges the two catenary hypotheses.
- **Assumed (named hypotheses).** `hSweep` — the homogeneous-sweep dimension identity (the one
  genuinely-hard rung; orbit/associated-bundle dimension, Mathlib-absent — handed to thread 29);
  `hClosure` — the closure/density `dim Σ^r = dim Σ̄^r`.
- **Cited.** `hClosure` is Lehalleur–Rimányi 4.4/4.5 (the exact-rank locus is dense in `Σ̄^r`); it is
  NOT proved in the engine and is the single Cited bridge. The honest headline is therefore
  `codim F = C + δ` **modulo the named density `dim Σ^r = dim Σ̄^r`**.
- **Deferred.** `hSweep` (the bundle-shift dimension identity) — out of this thread's scope; the
  separate flatness/orbit-dimension route (thread 29) discharges it. No claim here that `hSweep` holds.
- **Status.** sorry-free.

---

## Card 2 — the reducible-locus (radical) catenary `codim Z + dim Z = card`

> **Claim.** For a polynomial ring over a field and a proper ideal `I ≠ ⊤` (no radicality needed),
> `height I + ringKrullDim (R ⧸ I) = Nat.card σ`; geometrically, for any **nonempty** Zariski-closed
> `Z ⊆ Rep_d`, `codimRepCanonical Z + varietyDim Z = card`. The dual of the per-prime catenary across
> the (possibly several, possibly different-dimension) irreducible components.

- **Lean:** `DLNFibre.Core.height_add_ringKrullDim_quotient_eq_card_of_ne_top` (ideal form) and
  `DLNFibre.Core.codimRepCanonical_add_varietyDim_eq_card_of_nonempty` (geometry form)
  (`lean/DLNFibre/Core/RadicalCatenary.lean`). Helpers: `exists_minimalPrime_height_eq_height`,
  `exists_minimalPrime_ringKrullDim_quotient_ge`, `vanishingIdeal_ne_top_of_nonempty`.
- **Gloss.** Ideal form: `(I.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial σ k ⧸ I) = Nat.card σ`
  for `I ≠ ⊤`. Two inequalities squeezed by `le_antisymm`: upper bound — a longest prime chain of
  `R ⧸ I` maps (strictly-monotone quotient `comap`) into `Spec R`, its head contains a minimal prime
  `p`, so `dim(R⧸I) ≤ coheight p = dim(R⧸p)` while `height I ≤ height p`, closed by the per-prime
  catenary; lower bound — a minimal prime `p₀` realises `height I`, the surjection `R⧸I ↠ R⧸p₀` gives
  `dim(R⧸p₀) ≤ dim(R⧸I)`, and the per-prime catenary for `p₀` reads `card = height I + dim(R⧸p₀) ≤
  height I + dim(R⧸I)`. Geometry form: convert to `ℕ∞` at the vanishing ideal of `canonicalCoord '' Z`
  (proper since `Z` nonempty; quotient nontrivial so `ringKrullDim ≠ ⊥`).
- **Proved.** Unconditionally, no radicality, no irreducibility — `[Finite σ] [Field k]` only (the
  geometry form adds nothing). Discharges the `hCatFibre`/`hCatSigma` hypotheses of Card 1.
- **Assumed.** `I ≠ ⊤` (ideal form) / `Z` nonempty (geometry form) — genuinely needed (an empty locus
  has no catenary). For `MvPolynomial σ k`: the per-prime catenary `height_add_ringKrullDim_quotient_
  eq_card` (LANDED `NullstellensatzCodim`) + `FiniteRingKrullDim`/`IsNoetherian` (from finite `σ`).
- **Cited.** None.
- **Deferred.** None.
- **Status.** sorry-free. Non-vacuity: `codim univ + dim univ = card` on `(2,2,2)/AlgebraicClosure ℚ`
  (in-file `example`).
