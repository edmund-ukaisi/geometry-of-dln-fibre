# Thread 14 — Orbit-geometry sizing recon (pen-and-paper, 2026-06-19)

## Engine facts (verified)
- `orbitRankLocus M = {A | ∀ i≤j, rankPattern d A i j ≤ rankPattern d M i j}`, `rankPattern = (submult).rank`,
  `submult d A i j = A_{j-1}···A_i` (`Matrix.rank` of interval sub-products). Literally the rank-≤ locus.
- `G_d = BaseChangeGroup`, action `(P•A)_i = P_{i.succ} A_i P_{i.castSucc}⁻¹`. `rankPattern_eq_iff_orbit`,
  `baseChange_normalForm` (`P•A = ⊕ M_{ab}`, Gabriel normal form) PROVED.
- L0 `height_vanishingIdeal_add_varietyDim_eq_card` consumes `(vanishingIdeal Z).IsPrime`; `varietyDim Z :=
  ringKrullDim(MvPolynomial σ k ⧸ vanishingIdeal Z)` — depends on `Z` only through `vanishingIdeal Z`
  (intrinsically the *closure* dimension). **⟹ L6 can be stated at the IDEAL level**, dodging point-space topology.
- L4★ interface: the whole AG bridge is keyed on producing **one instance `IsSmoothAt k m_M`** (+ `κ(m_M)=k`,
  `varietyDim(Z_M)=r`). `smooth_point_isRegularLocalRing`, `finrank_cotangentSpace_eq_of_isSmoothAt`, M2, L4d all landed.
- **Paper status (verified, source lines 707–725):** "Thm 3.8" = **Abeasis–Del Fra** `O_s ⊆ Ō_r ⟺ s ≤ r`; the
  paper proves neither direction (easy = rank lower-semicontinuity; hard converse = "lace-diagram combinatorics",
  CITED). So L6 is genuine new content, not transcription.

## Per-piece size
| Piece | Verdict | Binding cost |
|---|---|---|
| **L6** `vanishingIdeal Z_M = vanishingIdeal O_M` | **sub-library (3–4 modules)** | box-move generation (L6.1+L6.2) |
| **L1** primeness | one module (given L6.4) | orbit ideal = ker(μ_M^*) into a domain |
| **L3** `IsSmoothAt k m_M` | module + 1 sub-library piece (chart L3.0) | the normal-form pivot chart |
| **L2** cotangent = range δ⁰ | module IF chart exists; else sub-library (minor-Jacobian) | `m_M/m_M²` ≅ range δ⁰ |

## Sub-ladders
**L6 (ideal level):** L6.0 one-param limit lemma (`F:k→Rep`, `F t∈O_M` for `t≠0` ⟹ `g∈vanishingIdeal(O_M)`
vanishes at `F 0`; via `t↦g(F t)` univariate zero on infinite `k∖{0}`, `Polynomial.eq_zero_of_infinite_isRoot`,
`IsAlgClosed⟹Infinite`) — **bricks verified, free, independent**. L6.1 box move `M[a,d]⊕M[c,b] ⇝ M[a,b]⊕M[c,d]`
via explicit polynomial 1-param family through L6.0 (sub-library). L6.2 rank-order ⟹ finite move-chain (lace
combinatorics — **the hard part**). L6.3 easy direction (lower-semicontinuity). L6.4 assemble ideal equality.
**L1:** L1.0 `𝒪(G_d)=Localization.Away(∏det)` domain; L1.1 `vanishingIdeal(O_M)=ker μ_M^*` prime; L1.2 transfer to Z_M via L6.4.
**L3 (chart route):** L3.0 pivot chart — principal-open nbhd of `M` in `O_M` ≅ `Localization.Away f (k[Fin r])`,
`r=finrank(range δ⁰)`, from `baseChange_normalForm` (pivot-minor denominators + range/ker δ⁰ split) [sizeable];
L3.1 `Away f (k[Fin r])` `FormallySmooth k` (bricks verified) ⟹ `IsSmoothAt k m_M`.
**L2 (chart route):** L2.0 `κ(m_M)=k` (`m_M=ker eval_M`); L2.1 `ringKrullDim(AtPrime m_M)=r` from chart; L2.2
combine M3 + L2.0 + L2.1. (Heavy fallback if no chart: `m_M/m_M²=ker(pderiv-Jacobian of minors)=range δ⁰` — AVOID.)

## Hardest + kill-conditions
1. **L6.1+L6.2 box-move degeneration** — the irreducible combinatorial sub-library (paper only cites it).
   KILL: if "every `s≤r` reached by a finite box-move chain" doesn't reduce to a clean `diff`-induction, L6 inflates.
   De-risk: one move's explicit family + L6.0 on `(2,2,2)`, then state+test the generation induction.
2. **L3.0 pivot chart** — packages L2+L3, bypasses homogeneity (Spec detour) + minor-Jacobian. KILL: if the
   explicit chart doesn't close as an `AlgEquiv`, L2+L3 fall back to heavier routes. De-risk: chart for `(2,2,2)` first.

## Build order
1. **L6.0** (limit lemma, free, independent) — bank. 2. **L3.0 chart on (2,2,2)** (high-leverage gamble; collapses
L2+L3). 3. L3.1 + L2.* (chart payoff). 4. L6.1+L6.2 (box-move generation, heavy; parallel). 5. L6.3+L6.4+L1
(ideal equality + primeness). 6. L4-assembly + L7.
**Critical-path:** the chart computes `dim O_M` at `M`, but `varietyDim(Z_M)` needs L6.4's ideal equality — so L6
stays on the critical path for the dimension; the chart only removes the homogeneity + minor-Jacobian sub-libraries.

Codex (decorrelated, xhigh): convergent on all; its load-bearing contribution = the pivot chart (adopted as primary
L2/L3). Artefacts: `threads/14-geometry-recon/codex/orbit-geometry-{prompt,answer}.md`.
