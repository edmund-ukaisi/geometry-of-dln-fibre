# Thread 05 — Phase θ-count (`θ = numTop = #top-dimensional components`) — statement card

Module: `lean/DLNFibre/Core/ThetaComponentCount.lean` (439 LoC, sorry-free, axiom-clean).
Build: whole `DLNFibre` library green (3015 jobs); `scripts/sorries` = 0.
Axioms (`#print axioms` on all headlines): `[propext, Classical.choice, Quot.sound]`.

**Status.** The count-bijection's **structure** (realizer-over-`d` infrastructure + the **unconditional
injectivity** + the `MapsTo`/`SurjOn` bookkeeping) is **landed**. The count **headline**
`numTop d r = #top-dimensional components` is **gated** on two precisely-named, pen-and-paper-certified
corner-selection facts (`hLowerBound`, `hRecover`) that reduce to two unbuilt `Core` lemmas
(corner-monotonicity of `cCodim` + the Gabriel-normal-form recovery). The gap is honestly named, NOT
sorry-patched. The `(2,2,2)`, `r=0` machinery fires (witnesses in-file).

---

## Headline — the θ-count bijection (gated)

> **Claim.** `θ = numTop d r = #{top-dimensional irreducible components of Σ̄^r}`: the combinatorial
> minimiser-count `θ` (the number of Kostant partitions of `d` with corner `r` attaining the minimal
> `codimForm = cCodim`) equals the number of irreducible components of `Σ̄^r` of **minimal**
> codimension (the top-dimensional ones).

- **Lean (count headline, gated):** `DLNFibre.Core.numTop_eq_ncard_topComponents_of`
  (`[IsAlgClosed k] [CharZero k]`): under `hLowerBound` + `hRecover`,
  `numTop d r h = (topComponents d r h).ncard`, where
  `topComponents d r h := {p | p ∈ (sigmaIdeal d r).minimalPrimes ∧ p.height = (cCodim d r h).toNat}`.
- **Lean (the bijection, gated):** `DLNFibre.Core.bijOn_partitionIdeal_topComponents_of`:
  `Set.BijOn (partitionIdeal d r) ↑(minimisingPartitions d r h) (topComponents d r h)`, where
  `partitionIdeal d r m = vanishingIdeal (Ō_{realizerD m})` (the orbit ideal of the realizer over `d`).
- **`topComponents` fidelity.** `(sigmaIdeal d r).minimalPrimes` are the irreducible components of
  `Σ̄^r` (LANDED G3 `minimalPrimes_sigmaIdeal_eq` = the maximal `Ō_M`); `p.height = (cCodim d r h).toNat`
  selects the **minimal-codimension** ones (`codimRepCanonical (Ō_M) = (vanishingIdeal Ō_M).height`,
  the LANDED `rfl` bridge). So `topComponents` = the top-dimensional components.
- **The subtlety (thread 04).** A minimal-PRIME `Ō_M` (a component) need not have minimal CODIM;
  components are the maximal orbit closures. The TOP-DIMENSIONAL ones are the min-codim among them. The
  count is `numTop ↔ {min-codim components}`, NOT ↔ all components. `numTop` counts the **minimisers**
  of `codimForm` (one for `(2,2,2)`, `r=0`), not the maximal partitions (three).

---

## Proved unconditionally (the bedrock under the headline)

- **Injectivity (the load-bearing unconditional content).** `partition_eq_of_rankPattern_realizerD_eq`:
  if two minimising Kostant partitions' realizers have the same rank pattern on the triangle, the
  partitions are equal. Chain: `partitionIdeal m₁ = partitionIdeal m₂` → (vanishingIdeal antisymmetry,
  `vanishingIdeal_orbitRankLocus_le_iff`) equal flattened orbit closures → equal `orbitRankLocus` →
  equal realizer rank patterns → (the `diff/cumul` inversion `diff_cumul`, the four `diff` reference
  points all on the triangle) equal `extendℤ` → (`extendℤ_injOn_kostant`) `m₁ = m₂`. The `InjOn` half
  of the `BijOn` is this, unconditional.
- **Realizer over `d`.** `realizerD hm` (the interval direct sum `⊕_{(a,b)} M_{ab}^{m_{ab}}` over
  `listOfPartition m`, transported onto `d`). Supporting: `foldDim_listOfPartition_eq` (Kostant ⟹
  `foldDim = d`, via the dimension equation + `cumul_extendℤ_diag`), `rankPattern_realizerD`
  (`= cumul (extendℤ m)`), `rank_mult_realizerD` (corner `= r`), `codimRepCanonical_orbitRankLocus_realizerD`
  (`codim.toNat = codimForm (extendℤ m)`, consuming the LANDED `Core.CThetaGeometric`).
- **`MapsTo` / `SurjOn` bookkeeping.** Fully proved modulo `hLowerBound`/`hRecover`: the minimiser's
  realizer is a minimal prime (LANDED `orbitRankLocus_minCodim_mem_minimalPrimes`, fed `hLowerBound`)
  of height `cCodim.toNat` (top-dimensional); `SurjOn` consumes `hRecover` (a corner-`r` partition
  with `partitionIdeal = p`) and **derives** the minimising property from the top-dim height +
  `cCodim ≥ 0` (so `hRecover` is the recovery brick, not `SurjOn` restated).

## Gated on (the precise gap — NOT sorry-patched)

Two named hypotheses of `numTop_eq_ncard_topComponents_of` / `bijOn_partitionIdeal_topComponents_of`:

1. **`hLowerBound`** — the realizer of a minimising corner-`r` partition is **globally** min-codim over
   the whole corner-`≤ r` family: `∀ M' corner ≤ r, (cCodim d r h).toNat ≤ codimRepCanonical (Ō_{M'})`.
   Content: the **strict corner-monotonicity** `cCodim d r < cCodim d s` for `s < r` (a corner-`s`
   orbit, `s < r`, has strictly larger codim — pen-and-paper (★), via the interval-merge that raises
   the corner while strictly dropping `codimForm`) + the Gabriel reading
   `codimRep(Ō_{M'}) = codimForm`. Feeds the `∀ corner-≤r M'` quantifier of
   `orbitRankLocus_minCodim_mem_minimalPrimes`.
2. **`hRecover`** — every top-dimensional component is the orbit ideal of *some* corner-`r`
   Kostant-partition realizer (`∃ m ∈ kostantPartitions d r, partitionIdeal m = p` — membership in the
   FULL `kostantPartitions d r`, NOT pre-assumed minimising; the minimising property is **derived** in
   `SurjOn` from the top-dimensional height + `cCodim ≥ 0`). Content: the Gabriel normal form
   (`exists_orbitRankLocus_mem_rankPattern_eq` / `baseChange_normalForm`) recast as a corner-`r`
   Kostant partition (the `kostantArrayOfRank`/`CMPlus` recovery of `Core.OrbitKostant`, bridged to
   the `extendℤ` encoding), + corner-monotonicity forcing corner = `r` on a top-dim component. Phrased
   this way (not `∈ minimisingPartitions`) it is the genuine recovery brick, not `SurjOn` restated.

**(★) certificate.** Pen-and-paper (expedition thread 05, this thread): (★) "every top-dimensional
component has corner exactly `r`" is TRUE (strict corner-monotonicity; corner-`<r` orbits are absorbed /
have strictly larger codim). Verified by exact enumeration on thousands of `(d, r)` cases (zero
failures) and exact match to the landed `(2,2,2)`: `r=0` → `cCodim=3, numTop=1`; `r=1` → `cCodim=1,
numTop=2`. So `numTop` (corner-`r` minimisers) is the correct, faithful count (no under/over-count).

**Single missing lemma (the honest roadmap).** A corner-monotonicity lemma
`cCodim d r < cCodim d s` (`s < r`) — the constructive interval-merge (termination measure
`∑_b (N−b)·m_{0b}`) — plus the `Tuple → kostantPartitions d ((mult).rank)` Gabriel bridge in the
`extendℤ` encoding. Together these discharge `hLowerBound`/`hRecover` (vacuously for the
corner-monotonicity half when `r = 0`; the Gabriel bridge is still needed at `r = 0`). Estimate:
~120–180 LoC (the Gabriel bridge + the interval-merge induction). NOT attempted here (budget + thrash
risk; the brief's "land the reachable direction + report the precise gap" discipline).

---

## Supporting bricks (same module)

- `cumul_extendℤ_diag` — `cumul (extendℤ m) k k = ∑_{p.1≤k≤p.2} m p` (the diagonal cumul = Kostant
  filtered sum; the bridge for `foldDim = d`).
- `extendℤ_supported` / `extendℤ_apply_fin` / `extendℤ_injOn_kostant` — the `extendℤ` array facts
  feeding injectivity.
- `codimRepCanonical_orbitRankLocus_transport` — codim is transport-invariant along `foldDim = d`
  (`subst`).
- `partitionIdeal` / `partitionIdeal_of_mem` — the (total, `dite`-guarded) bijection map.
- `minimisingPartitions` / `numTop_eq_card_minimising` — `numTop` as the minimiser-set card.

## Non-vacuity witness in-file — `(2,2,2)`, `r = 0`, over `AlgebraicClosure ℚ`

- `mMin_mem_minimisingPartitions`: the minimiser `mMin` (`Core.CTheta`, codimForm = cCodim = 3) is in
  `minimisingPartitions d222 0` — the bijection's domain is nonempty on `(2,2,2)`.
- `partitionIdeal_mMin_mem_orbitIdeals`: its `partitionIdeal` is the realizer's orbit ideal, a member
  of the corner-`0` family — the map fires. Geometric side of the LANDED `numTop_d222_zero = 1`.

## Status

sorry-free + axiom-clean; whole library green. **Reviewer fidelity AUDIT: PASS-with-notes**
(reviewer 2026-06-21; Codex non-functional env-wide, reviewer was the decorrelation, independent
adversarial pass). Verdict: no soundness break; injectivity + realizer infrastructure are
unconditional axiom-clean bedrock; the gated headline is an honest deliverable (built skeleton +
load-bearing injectivity; the open content named in two hypotheses). Notes **applied**:
- (N2) `hRecover` was `SurjOn` restated verbatim → **reformulated** to `∈ kostantPartitions d r` (the
  genuine Gabriel-recovery brick), with the minimising property now **derived** in `SurjOn` from the
  top-dim height + `cCodim ≥ 0` — `hRecover` is no longer a restatement of the conclusion.
- (N1b) `topComponents` docstring "(the minimal codimension)" gloss → **tightened** to state that
  `cCodim` IS the min codim is delivered by the gating hypotheses, not asserted (with the
  non-circularity argument: `cCodim` is a fixed combinatorial integer, so `topComponents` is a genuine
  Spec-side subset, not the bijection's image).
- (N8) headline/module-header "bijection's structure proved unconditionally" overclaim → **corrected**
  to "realizer infrastructure + injectivity unconditional; MapsTo/SurjOn gated".

Gap honestly named (gated headline + the two corner-selection hypotheses), NOT sorry-patched. The
(★) "thousands of cases" enumeration is pen-and-paper evidence (not machine-checked here) — the
corner-monotonicity lemma is the roadmap'd item that would make it machine-checked.
