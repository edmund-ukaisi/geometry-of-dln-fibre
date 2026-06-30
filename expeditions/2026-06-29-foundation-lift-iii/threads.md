# Threads — `foundation-lift-iii`

Per-rung formaliser/reviewer threads (the ladder is in [`priorities.md`](priorities.md)). One **builder/committer**
per shared worktree at a time; read-only auditors run concurrently. Controller integrates + re-gates per
[`loop-prompt.md`](loop-prompt.md).

## Phase 1 — differential-algebra interface (`fl3-p1`)

| rung | seat | teammate | status | notes |
|------|------|----------|--------|-------|
| P1.1 | formaliser | aa0363b6 | ✅ DONE `333a038b` | two-file split → `Core/RingTheory/Kaehler/GenericRank.lean` + `Core/Dimension/Trdeg.lean`; green 3822, axiom-clean. Wrapper char-FREE; `[CharZero]` quarantined to `diffIndepCriterion_proof` |
| P1.2 | reviewer | a445e1fc | ✅ REVIEWED | crux verdict: **leave `[CharZero]`** — `[PerfectField]` swap is FALSE (`𝔽_p[T]`, `x=T^p`: `D(T^p)=0`; perfect-field falls on `Pf=k(X)`, perfect iff char 0). Codex-concurred. Fidelity PASS (145 lines byte-identical). Action: drop unused `[Fintype ι]` in `D_adjoin_mem_span`. Char-`p` criterion → roadmap |
| P1.3 | controller | — | ✅ VERIFIED (no edit) | `CotangentJacobian.lean` — orientation discipline exemplary; namespace+path mirror Mathlib |
| P1.4 | controller | — | ✅ VERIFIED (no edit) | `CotangentLocalization.lean` — name=content, minimal hyps (`[Field k]` not needed) |
| P1.5 + P1.6-V2 | formaliser | a41d8e0e | ✅ DONE `1dc6c698` | `MatrixKaehler.lean` split → `Core/RingTheory/Derivation/Matrix.lean` + `Core/LinearAlgebra/BaseChange.lean` (V2 + 3-way distinctness docstring); green 3823, axiom-clean. Caught + honestly fixed a severed transitive instance import (→ L6) |
| **P1-final** (P1.7 + P1.2-finish + P1.6-V1) | formaliser | a30d5c63 | ✅ DONE `3419daa3`+`e51a9d35` | P1.7 layering inversion broken (`trdeg_eq_of_integral_injective`→`Dimension/Integral`, quotient lemma re-derived from general form, `AffineNoetherRank` thinned to 1 orbit lemma); `[Fintype ι]` dropped; V1 distinctness docstring. L6 hit+fixed again |
| P1.6-V3 | controller | — | ✅ RESOLVED (no extraction) | V3 = Mathlib's `Module.Flat.linearIndependent_one_tmul`, already named+documented in `GenericRank`. Wrapping it would be an anti-Mathlib re-export. BaseChange.lean V3 docstring aligned (controller) |

## Phase 1 — re-gate (controller, phase boundary) ✅ PASSED
Full build green (3823 jobs); sorries 0; axioms `[propext, Classical.choice, Quot.sound]` on all Phase-1
headlines + **both DLN payoffs** (`rlct_lossDLN_eq_half_cCodim_add_shift_via_aoyagi`,
`rlct_lossDLN_d222_one_eq_two_via_aoyagi`) — payoff footprint unchanged. longLine warnings all pre-FL-III
(out of scope). **Phase 1 complete → PR opened for async review; proceeding to Phase 2.**

## Phase 2 — orbit-dimension squeeze (`fl3-p2`)

| rung | seat | teammate | status | notes |
|------|------|----------|--------|-------|
| P2.0 | scout | abf59d3e | ✅ PROCEED `1e099b56` | de-`Tuple` probe → small hypothesis-carrying 4-brick engine; H1/H2 named hyps; keystone restates clean. Codex-concurred. Report = authoritative Phase-2 design |
| P2.2 | formaliser | aa04914a | ✅ DONE `64d75981` | keystone: **layered** `AffineGVariety` carrier `(ρ, R: k-domain, fρ)` (deformation deferred to extension) + `isPrime_ker_pullback` irreducibility + DLN `dlnOrbit` instance (DLN lemma re-derived). bare-Mathlib-mirror ns (→ L7 shadowing fix). green 3824 |
| P2.3 | formaliser | ad3cc933 | ✅ DONE `303db988` | A4.1 anchor `varietyDim 𝒪 = trdeg` in `Orbit/Dimension.lean`; `[Finite ρ]` minimal-hyp; DLN lemma re-derived to 3 lines (collapsed). green 3825, fidelity PASS + Codex. card `reviewed` |
| P2.1 | — | — | ⏳ folded → P2.4 | trace self-duality `traceEquiv` reusable, but abstract B1 likely uses Mathlib `finrank_range_dualMap_eq_finrank_range` (dropping `deltaT`); decide at P2.4 to avoid double-touching `OrbitDifferentialRank` |
| P2.4 | formaliser | a8e13a62 | ✅ DONE `0b580992` | B1 `GenericRankBound` (A4.3). **Guard caught it:** forward H1 undischargeable (`range(L∘δ.bc)=L(range δ)⊊`); pivoted to **transpose** H1 (`δAdj:C1→C0` + rank-tie, probe §1(iii)-blessed). B1 clean (V2, no `deltaT`); keystone re-derived sig-unchanged. green 3826, axioms clean. → L8 |
| P2.4-review | reviewer | a31f1da4 | ✅ SURVIVED | transpose-H1 honest (non-circular, **non-vacuity witness built** ℚ[X]/`id`), forward-fails diagnosis confirmed, discharge fidelity PASS (rank-tie *proved* via `finrank_range_deltaT`, `deltaT` confined to DLN file), keystone byte-identical, re-gate green 3826 + axioms clean, Codex concurred. Minor docstring flag judged non-blocking |
| P2.5a | formaliser | a7ccc4f1 | ✅ DONE `21908723` (+review `ccdd82ea`) | B3 `CotangentInjection`. **Forward H2 PINS** (no pivot — `InfinitesimalAction` carries `dirDeriv`/`c1coord`, coordinate test recovers δφ; no adjoint/rank-tie). Clean rank-nullity proof; R5 re-derived sig-unchanged, dead chain collapsed. green 3826. Formaliser self-spawned decorrelated review SURVIVED + Codex; **controller code-inspection confirms** honesty + non-vacuity (DLN instance built + trivial witness) → accepted, no 2nd review |
| P2.5b | formaliser | a0864888 | ✅ DONE `45049b6f` | B4 `SmoothCotangentDim` — `(finrank k m.Cotangent : ℕ∞) = varietyDim Z`. Hyps are honest INPUTS (`[IsSmoothAt k m]` + `hrat : ResidueField m ≃ₐ[k] k`, "is smooth + `k`-rational", not "exists"); R6 chain abstracted (M3/L2a/GAP2/GAP3), GAP2/3 re-homed to `Dimension/AffineDomain`. DLN discharges `k`-rationality via M3 density (smooth pt is an orbit pt). R6 re-derived sig-unchanged. green 3826, axioms clean |
| P2.5b-review | reviewer | a5bb3c7d | ✅ SURVIVED | `k`-rationality SOUND (smooth pt taken from dense `k`-rational `orbitSpecSet` ∩ smooth locus; `dense_smoothLocus_of_perfectField` no alg-closedness; `hrat` load-bearing for `[κ:k]=1`). Codex-concurred. GAP re-home PASS, R6/A6.1 byte-identical, re-gate green 3826. 2 cosmetic non-blockers (no in-file B4 witness; stale docstring `FibreDimFibration:82`) |
| **P2.6** | formaliser | dispatching | 🔄 | squeeze headline `varietyDim Z = finrank(range δ)` (abstract: B1 `≤` via A4.1+Phase-1 trdeg; B3∘B4 `≥`; `le_antisymm`) + re-derive DLN `VoigtDischarge` from it. **Folds the 2 cosmetic fixes** (in-file B4 `example` witness; `FibreDimFibration:82` docstring). Phase-2 boundary re-gate after |

## Concurrency rule (this expedition)
At most **one builder/committer** in `.claude/worktrees/fl3` at a time (a second `lake build` corrupts `.lake`;
two `git commit`s race the index). Read-only auditors (no build, no commit) may run alongside one builder.
Rungs touching the same file are serialized.

_Updated each tick._
