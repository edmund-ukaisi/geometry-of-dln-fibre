# Statement card — L1: the orbit `O_M` is an irreducible affine variety

- **Status:** reviewed (FAITHFUL-WITH-NOTES, 2026-06-19) — the headline/proof faithfully match the
  claim, axioms clean, non-vacuous, both directions honest. The one note (prose-only): "affine
  variety" connotes Zariski-*closed*, whereas the orbit is only locally closed and a prime vanishing
  ideal certifies its *closure* is the irreducible variety — the theorems already say "prime" /
  "Zariski-irreducible" (true of the orbit set itself, no closedness claimed). Header prose tightened
  accordingly (no signature change).
- **Module:** `lean/DLNFibre/Core/OrbitVariety.lean` (402 LoC)
- **Branch:** `expedition/voigt-discharge`
- **Axioms (headline):** `[propext, Classical.choice, Quot.sound]`

## Claim (informal)

The `G_d`-orbit `O_M = G_d · M` of a composable matrix tuple `M`, viewed as a point set in the
coordinate space `RepCoord d → k` of `Rep_d` via the canonical entry-flattening, is a **Zariski-
irreducible** affine variety: its vanishing ideal is prime. (Le Halleur–Rimányi 2024, §3 — the orbit
is the image of the irreducible group `G_d = ∏_v GL_{d_v}` under the polynomial orbit map, hence
irreducible. The orbit *closure* is the rank locus `orbitRankLocus`; that closure-equality is the
separate L6 box-move sub-ladder. This card is the orbit itself.)

## Lean headline

```lean
theorem isPrime_vanishingIdeal_orbitSet [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
    (M : Tuple (k := k) d) :
    (MvPolynomial.vanishingIdeal k (orbitSet M) :
      Ideal (MvPolynomial (RepCoord d) k)).IsPrime
```

with the point-space corollary `isZariskiIrreducible_orbitSet : IsZariskiIrreducible (orbitSet M)`
(the L0-dictionary form, the direct consumer of the L0 codimension bridge).

## Objects (exact)

- `orbitSet M := canonicalCoord d '' { A | ∃ P : BaseChangeGroup d, P • M = A }` — the orbit of `M`
  under the `G_d`-action `(P • A)_i = P_{i.succ} A_i P_{i.castSucc}⁻¹`, flattened to `RepCoord d → k`
  (one coordinate per matrix entry).
- `orbitMap M : BaseChangeGroup d → (RepCoord d → k)`, `P ↦ canonicalCoord d (P • M)`. Key:
  `range_orbitMap : Set.range (orbitMap M) = orbitSet M`.
- `groupRing d := Localization.Away (groupDenom d)` where `groupDenom d = ∏_v det (genericMat d v)`
  and `genericMat d v` is the generic matrix `X⟨v,i,j⟩` over `MvPolynomial (GroupCoord d) k`. This is
  `𝒪(G_d)`. `groupRing_isDomain : IsDomain (groupRing d)` (localization of a polynomial domain at the
  nonzero `Δ`).
- `orbitPullback M : MvPolynomial (RepCoord d) k →ₐ[k] groupRing d`, `μ_M^*`, the `aeval` sending the
  coordinate variable `X⟨i,r,c⟩` to the `(r,c)` entry of `Pgen_{i.succ} · M_i · Pgen_{i.castSucc}⁻¹`
  (the generic group element times the constant `M_i` times the generic inverse, the inverse built
  from `adjugate` and `IsLocalization.Away.invSelf Δ`).

## Load-bearing lemma

```lean
theorem vanishingIdeal_range_orbitMap_eq_ker [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
    (M : Tuple (k := k) d) :
    MvPolynomial.vanishingIdeal k (Set.range (orbitMap M))
      = RingHom.ker (orbitPullback M).toRingHom
```

- `⊇`: point-evaluation — `evalGroupRing P (μ_M^* g) = g (μ_M P)` (the bridge
  `evalGroupRing_orbitPullback`, proved by pushing the point-evaluation ring hom through the matrix
  product `Pgen · M · Pgen⁻¹` and recognising the unit inverse via `coe_units_inv`, `inv_def`,
  `RingHom.map_adjugate`).
- `⊆`: localization-vanishing-on-the-dense-open — `Away.surj` writes `μ_M^* g = mk'(h, Δ^n)`; `h·Δ`
  vanishes at every point of `GroupCoord d → k` (group points by `exists_baseChange_of_eval_ne_zero`,
  the rest by `Δ = 0`), so `MvPolynomial.funext` gives `h·Δ = 0`, domain gives `h = 0`, and `Δ` a unit
  in the localization gives `μ_M^* g = 0`. `[IsAlgClosed k]` enters only through `Infinite k`
  (needed by `funext`).

## Hypotheses

- `[Field k] [IsAlgClosed k]` (headline). `IsAlgClosed` is used solely via `Infinite k` for the
  point-faithfulness `MvPolynomial.funext`; it is a hypothesis, not a citation.
- The orbit/pullback objects (`orbitSet`, `orbitMap`, `groupRing`, `orbitPullback`,
  `vanishingIdeal_range_orbitMap_eq_ker`'s machinery) build over `[Field k]`; only the two final
  irreducibility theorems carry `[IsAlgClosed k]`.

## Non-vacuity

`orbitSet`/`orbitMap` exercised on the concrete `(2,2,2)/ℚ` full-rank witness `tupleWitnessQ`
(`canonicalCoord tupleWitnessQ ∈ orbitSet tupleWitnessQ` via `P = 1`).

## Provenance

- Sized then built (recon thread 14 judged "one module, bricks present"; Codex decorrelated xhigh
  consult `codex/l1-size-{prompt,answer}.md` confirmed route + flagged 600+ LoC budget and the global-
  denominator `invSelf` trick, adopted). Came in **bounded** (no absent sub-library) at 402 LoC — under
  the 600+ budget because the bridge collapsed cleanly via `MvPolynomial.ringHom_ext`.
- No new cited interfaces; full bedrock (zero sorry/axiom/native_decide; whole library green).
