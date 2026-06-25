# Seam-D / seam-E architecture review (Lean 4 + Mathlib v4.29, DLNFibre)

You are reviewing a Lean formalisation design. Context: we are building a localized chart
`AlgEquiv` `e : Localization.Away dsig ≃ₐ[k] Localization.Away gF` between two coordinate-ring
localizations, by `AlgEquiv.ofAlgHom chartPsiLoc chartPhiLoc _ _`. The Ψ direction `chartPsiLoc`
is DONE (sorry-free). We need the Φ direction `chartPhiLoc` (seam D) and the two round-trips
(seam E). Question: what is the CLEANEST construction of `chartPhiLoc` that makes the seam-E
round-trips tractable?

## The setup (all LANDED, sorry-free)

`k` is an alg-closed char-0 field; `d : Fin (N+2) → ℕ`; `r ≤ d 0 =: q`, `r ≤ d (last) =: p`;
`δ = r(p+q−r)`. Let:
- `O(Σ) = MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Σ^r` (Σ^r = rank-exactly-r product locus).
- `O(F) = MvPolynomial (RepCoord d) k ⧸ vanishingIdeal F`, F = fibre over normalForm = diag(I_r,0).
- `dsig = mk(vanishingIdeal Σ^r) ΔPdeep ∈ O(Σ)`, ΔPdeep = top-left r×r minor (det) of the generic
  product `M = Matrix.of (multPoly d)`.
- `gF = map (algebraMap k O(F)) detSchurS ∈ MvPolynomial (SchurVar) O(F)`, detSchurS = det of the
  generic Schur Δ-block. `P := MvPolynomial (SchurVar) O(F)`.
- `SchurVar = (Fin r × Fin r) ⊕ ((Fin r × Fin(q−r)) ⊕ (Fin(p−r) × Fin r))` (Δ ⊕ B12 ⊕ B21 blocks).
- `SchurLoc = Localization.Away detSchurS` (over `MvPolynomial SchurVar k`).
- `schurToGfib : SchurLoc →ₐ[k] Away gF` (the coefficient base-change, LANDED).

The Ψ comorphism (DONE): `chartPsiAeval : MvPolynomial (RepCoord d) k →ₐ[k] Away gF`,
= `aeval chartPsiSub`, `chartPsiSub x = chartPsiTower (gaugeSub d endpointGauge⁻¹ x)`,
`chartPsiTower = aevalTower schurToGfib fibCoordT`, `fibCoordT x = algebraMap O(F) (Away gF) (mk_F (X x))`.
It descends through `vanishingIdeal Σ^r` to `chartPsiQuot : O(Σ) →ₐ[k] Away gF`, then lifts
(`ΔPdeep ↦ unit`) to `chartPsiLoc : Away dsig →ₐ[k] Away gF`.

The geometry: Ψ is the comorphism of `Ψ(M,B) = chartGauge(M)⁻¹ • B` (reconstruct a tuple from base
matrix M and fibre point B); Φ is the comorphism of `Φ(A) = (mult A, chartGauge(mult A) • A)`.
`endpointGauge` is the SchurLoc-valued gauge: H at vertex 0, L⁻¹ at the last vertex, where
L = [[I,0],[B21 Δ⁻¹,I]], H = [[Δ,B12],[0,I]] are the Schur unitriangular blocks; it satisfies
`gaugeEquiv endpointGauge (multPoly r c) = (L⁻¹ · M · H⁻¹) r c` over SchurLoc (LANDED).

## The brief's proposed seam-D shape

`chartPhiAeval : P = MvPolynomial SchurVar O(F) →ₐ[k] Away dsig`, an `aevalTower φc φv`:
- coeff leg `φc : O(F) → Away dsig`: a fibre coord `X x` (mod vanishingIdeal F) ↦ the FORWARD-gauge
  coordinate `gaugeSub d endpointGauge x` (over SchurLoc... but the target is Away dsig) pushed into
  Away dsig. [This is the part I am unsure about — see questions.]
- var leg `φv : SchurVar → Away dsig`: each Schur generator ↦ the corresponding Schur block entry of
  `M = Matrix.of (multPoly d)`, as a RepCoord-poly pushed (via mk(vanishingIdeal Σ^r) then algebraMap)
  into Away dsig.
Then descend `vanishingIdeal F ≤ ker chartPhiAeval` (target Away dsig localizes O(Σ), a
vanishingIdeal-quotient, so the Σ-side zero-test `away_eq_zero_iff_exists_pow_mul_mem` applies
directly — easier than Ψ), and lift (`gF ↦ unit`).

## My concern / the questions

1. **Coeff-leg coherence.** `chartPhiLoc ∘ chartPsiLoc = id` on `Away dsig` reduces (by
   `Localization.algHom_ext` + `Quotient` + `MvPolynomial.algHom_ext`) to checking on each `RepCoord`
   generator `X x`: `chartPhiLoc (chartPsiAeval (X x)) =? mk(vanishingIdeal Σ^r)(X x)` in Away dsig.
   But `chartPsiAeval (X x) = chartPsiSub x ∈ Away gF` is a fraction over P, not a polynomial. To apply
   `chartPhiLoc` to it I must push chartPhiLoc through the Away-localization of P. Is the cleanest route:
   (a) prove the round-trip at the UN-localized / UN-descended level first — i.e. find a single
   ring/alg-hom identity `chartPhiAeval ∘ (the P-level Ψ pieces) = ...` that telescopes via the gauge
   group law `aeval_gaugeSub_gaugeSub` (which collapses `P · P⁻¹ = 1` to `X x`)? Or (b) work directly
   with `Localization.algHom_ext` / `IsLocalization.lift` uniqueness on the localized homs?

2. **Is the aevalTower-into-Away-dsig coeff leg even the right object?** The Ψ side put the gauge on the
   RepCoord variables (`gaugeSub`) and the SchurLoc coefficients via `schurToGfib`. For Φ to be a clean
   inverse, would it be cleaner to make `chartPhiAeval` ALSO factor through a `gaugeSub`/`gaugeEquiv` of
   the SAME shape (so the two `aeval (gaugeSub P)` / `aeval (gaugeSub P⁻¹)` compose by the LANDED
   `gaugeEquiv` round-trip, which is already proven to be an `AlgEquiv`)? Concretely: is there a way to
   realize BOTH chartPsiLoc and chartPhiLoc as localizations of the SINGLE LANDED gauge `AlgEquiv`
   `gaugeEquiv d endpointGauge : MvPolynomial (RepCoord d) SchurLoc ≃ₐ MvPolynomial (RepCoord d) SchurLoc`
   transported to the two quotient-localizations — so that `e` is essentially that gauge `AlgEquiv`
   descended, and the round-trips come FOR FREE from `gaugeEquiv`'s `AlgEquiv` round-trips, rather than
   re-proving them on generators?

3. **Universe / scalar-tower traps.** Any foreseeable trap in the `aevalTower` coeff-leg landing in
   `Away dsig` (O(Σ) is a `Type u` quotient; Away dsig is its localization)? The Ψ side needed
   `[Infinite k]` for the descent (MvPolynomial.funext). Does the Φ descent (Σ-side zero-test) avoid it?

4. **Round-trip on which generators, exactly.** Spell out the MINIMAL set of generator identities
   needed for `AlgEquiv.ofAlgHom chartPsiLoc chartPhiLoc h1 h2`: h1 (`chartPsiLoc ∘ chartPhiLoc = id` on
   Away gF) reduces to P-generators (SchurVar generators + O(F) coeffs); h2 reduces to RepCoord
   generators. Which of these is the genuinely hard one, and what is the cleanest lemma to discharge it?

Please give: (A) your recommended construction of `chartPhiAeval`/`chartPhiLoc` (the substitution legs,
explicitly); (B) the round-trip strategy (the single load-bearing identity); (C) whether route-2
("descend the single LANDED gaugeEquiv AlgEquiv, get round-trips for free") is viable and preferable to
building Φ as an independent aevalTower; (D) the one most-likely-to-break step. Verify any Mathlib API
you cite is plausibly at v4.29. Be concrete and Lean-shaped.
