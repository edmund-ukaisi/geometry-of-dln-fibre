# Thread 09 — Phase 2 crux probe: relax `[IsAlgClosed]→[PerfectField]`, pin L7

**Type:** formalisation (tide). De-risk the Phase-2 build before committing to the full L1–L10 ladder.
Settle the CRUX (relax the vestigial typeclass on the orbit-dimension squeeze, green-build over ℝ) and
pin L7 (the `deformationδ` base-change rank-invariance lemma shape + route).

**Base:** `expedition/rlct-bridge-crux-probe` from `origin/expedition/rlct-bridge` (`110c2bc2`).
Recon read: `threads/08-realag-route-recon/thread.md` (the L1–L10 ladder; the squeeze route).

---

## VERDICT

**(a) CRUX settled — YES.** The `[IsAlgClosed k] → [PerfectField k] [Infinite k]` relaxation green-builds
over ℝ. The full `DLNFibre` library compiles (3817 jobs, 0 errors) with the relaxed chain, and the squeeze
`varietyDim_ℝ(orbit) = finrank_ℝ(range deformationδ)` is now a NAMED theorem over `k = ℝ`, axiom-clean
`[propext, Classical.choice, Quot.sound]` (verified by `#print axioms` on a forced recompile). Algebraic
closedness was genuinely vestigial — consumed at exactly two entry points, both relaxable to a perfect
base field (no kill-condition fired: no closed-pt=k-pt, no strong-Nullstellensatz, no residue=k-at-a-
non-rational-point use on the squeeze path).

**(b) L7 — packaging exercise, not a real gap.** The route is the banked brick
`DLNFibre.Core.MatrixKaehler.finrank_range_baseChange` (R2, the linear-map base-change route). Exact
statement pinned below; the specialized brick at `deformationδ` is fully provable now (probed, sorry-free);
the one remaining step is a tensor-conjugacy identity (`deformationδ_K (M.map ι) ≅ (deformationδ_k M).baseChange K`).
**Route R2 (linear-map base change), NOT R1 (Matrix.rank over ℤ).** No `Matrix.rank_map` lemma exists at v4.29;
the linear-map brick already exists and is cleaner.

**(c) GO for the full G2 build.** No new hard math. One reshaping vs the recon (below).

---

## (a) The relaxation — what was done

The CRUX lemma `finrank_range_deformationδ_le_varietyDim` (`OrbitTangentCotangent.lean:641`) and its
transitive `[IsAlgClosed]`-declared dependencies were relaxed. Bottom-up, each green-built then the FULL
aggregator green-gated (the single-module build masks stale-olean failures + name clashes — and DID here:
two `[IsAlgClosed]` lemmas not in the recon's chain only surfaced on the fresh full rebuild).

| lemma | file | was | now | why it relaxes |
|---|---|---|---|---|
| `isPrime_vanishingIdeal_orbitSet` | OrbitVariety | `[IsAlgClosed]` | `[Infinite]` | proof = `RingHom.ker_isPrime` ∘ `vanishingIdeal_range_orbitMap_eq_ker` (`[Infinite]`) |
| `isZariskiIrreducible_orbitSet` | OrbitVariety | `[IsAlgClosed]` | `[Infinite]` | via the above |
| `orbitRing_isDomain` (inst) | OrbitSmooth | `[IsAlgClosed]` | `[Infinite]` | quotient by the now-`[Infinite]` prime |
| `dense_orbitSpecSet` | OrbitSmooth | `[IsAlgClosed]` | `[Infinite]` | reduced (from domain) + generic zeroLocus/closure |
| SpecModel `variable` block (`exists_orbitPointIdeal_isSmoothAt`, `isSmoothAt_normalFormIdeal`, `residueFieldNormalFormEquiv`, +3 `omit` lemmas) | OrbitSmooth | `[IsAlgClosed]` | `[PerfectField][Infinite]` | `dense_smoothLocus_of_perfectField` ([PerfectField]); `IsReduced(orbitScheme)` from domain ([Infinite]) |
| `smooth_point_isRegularLocalRing`, `finrank_cotangentSpace_{le,eq}_of_isSmoothAt` | SmoothPointRegular | `[IsAlgClosed]` | `[PerfectField]` | only consumer is `FormallySmooth.of_perfectField`; M2 dim bridge is `[Field]`-only |
| `residueFieldAtPrimeNormalFormEquiv`, `finiteDimensional_cotangent_normalFormIdeal`, `finrank_range_deformationδ_le_{finrank_cotangent,varietyDim}`, `exists_ringKrullDim_orbitRing_eq`, `finrank_cotangent_eq_varietyDim` | OrbitTangentCotangent | `[IsAlgClosed]` | `[PerfectField]` (+`[Infinite]` for the pre-`variable` def) | inherit from above |
| `isPrime_vanishingIdeal_orbitRankLocus` | OrbitClosure | `[IsAlgClosed]` | `[Infinite]` | = `vanishingIdeal_orbitRankLocus_eq_orbitSet` + primeness (both `[Infinite]`) — **not in recon's chain; surfaced on full rebuild** |
| `codimRep_add_varietyDim_eq_card`, `codimRep_eq_card_sub_varietyDim`, `codimRepCanonical_eq_card_sub_varietyDim` | NullstellensatzCodim | `[IsAlgClosed]` | none (`[Field]`) | proof = `height_vanishingIdeal_*` (`[Finite σ]`-only) — **vestigial; surfaced on full rebuild** |
| squeeze `varietyDim_orbitRankLocus_eq_finrank_range_deformationδ` + Voigt's lemma `codimRep_orbitRankLocus_eq_orbitLinearCodim` + 2 `_unconditional` headlines | VoigtDischarge | `[IsAlgClosed][CharZero]` | `[CharZero]` | `CharZero ⟹ PerfectField` (instance, in closure) + `CharZero ⟹ Infinite` (instance, **needed `import Mathlib.Algebra.CharZero.Infinite`** — not in the base closure) |

**The two genuine alg-closed entry points** (decorrelated Codex xhigh agreed, independently):
1. `Algebra.FormallySmooth.of_perfectField [PerfectField K][EssFiniteType K L]` — residue-field formal
   smoothness (`SmoothPointRegular`).
2. `Scheme.Hom.dense_smoothLocus_of_perfectField [PerfectField K][IsReduced X]` — generic smoothness
   (`OrbitSmooth`).
Both `[PerfectField]`. Everything else is `[Infinite]` (orbit primeness) or `[Field]` (catenary).

**Two snags found on the full rebuild (the reason single-module builds are insufficient):**
- `isPrime_vanishingIdeal_orbitRankLocus` (OrbitClosure) and the 3 `codimRep_*` bridges (NullstellensatzCodim)
  were `[IsAlgClosed]` but off the recon's traced chain — caught only by the full aggregator build.
- `CharZero k ⟹ Infinite k` is an instance but `Mathlib.Algebra.CharZero.Infinite` is NOT in the base
  import closure of the orbit chain (verified: `inferInstance` for `Infinite k` from `[CharZero k]` failed
  against `OrbitDifferentialRank`). Fixed by importing it in `VoigtDischarge`. (`CharZero ⟹ PerfectField`
  via `PerfectField.ofCharZero` IS in closure.)

**Bedrock wins banked (witnesses shown in-file):**
- `OrbitVariety`: primeness now fires at ℚ (added `example`).
- `OrbitSmooth`: the **smoothness headline now fires at ℚ** — `Algebra.IsSmoothAt ℚ (normalFormIdeal tupleWitnessQ)`
  (added `example`) — non-vacuous off the algebraically-closed locus.
- `VoigtDischarge`: the squeeze AND Voigt's lemma fire over **ℝ** on the genuine `(2,2,2)` `(1,1)`-orbit
  (added two `example`s) — the crux relaxation made real.

Relaxed lemmas verified axiom-clean `[propext, Classical.choice, Quot.sound]`:
`finrank_range_deformationδ_le_varietyDim`, `varietyDim_orbitRankLocus_eq_finrank_range_deformationδ`,
`codimRep_orbitRankLocus_eq_orbitLinearCodim`, `isPrime_vanishingIdeal_orbitSet`, `isSmoothAt_normalFormIdeal`.

---

## (b) L7 — the exact statement + route

**Statement (pinned).** For a field extension `K/k` (i.e. `ι : k →+* K` a field hom ⟹ `[Algebra k K]`)
and a tuple `M` over `k`, with `M.mapRingHom ι := fun i ↦ (M i).map ι` the entrywise base change:

    finrank K (range (deformationδ (M.mapRingHom ι) (M.mapRingHom ι)))
      = finrank k (range (deformationδ M M))

(downstream, instantiated at `M = realizerD` over ℚ→ℝ and ℚ→K; entries are 0/1 integers, but the entries
are NOT needed for the route — see below.)

**Route R2 (decided).** Via the banked brick `MatrixKaehler.finrank_range_baseChange`:

    finrank_range_baseChange (K) (f) :
      finrank K (range (f.baseChange K)) = finrank k (range f)   -- [Module.Finite k (range f)] auto

Specialized to `deformationδ` it is FULLY PROVABLE NOW (probed sorry-free):

    finrank K (range ((deformationδ M Nt).baseChange K)) = finrank k (range (deformationδ M Nt))
      := finrank_range_baseChange K (deformationδ M Nt)

The remaining step (the ONLY gap): identify `deformationδ_K (M.mapRingHom ι)` with `(deformationδ_k M).baseChange K`
up to the canonical `cochain*_K ≅ K ⊗_k cochain*_k` isos (a `LinearEquiv.finrank_range`-preserving conjugacy;
the `Matrix.map ι`-vs-`K ⊗` compatibility on each Pi component). This is **packaging, not new math** — a
commuting-square check, estimated ~1 tide (it is the seam where the real↔complex transfer lives, genuinely
net-new: no banked `fibre K (B.map ι)` ↔ tuple-base-change connection exists).

**Why NOT R1** (Matrix.rank over ℤ): no `Matrix.rank_map` / rank-invariance-under-injective-ring-hom lemma
exists at Mathlib v4.29 (checked `LinearAlgebra/Matrix/Rank.lean`); R1 would require building it. R2's brick
already exists and avoids the entries entirely (works for any tuple, not just the 0/1 realizer).

---

## (c) GO / NO-GO + reshaping for the full G2 build

**GO.** No new hard math; every remaining rung is (a) a vestigial-typeclass relax on a proved lemma, (b) a
banked-piece assembly (`le_antisymm`, the catenary), or (c) the L7 packaging (one tensor-conjugacy identity).

**Reshaping vs the recon's L1–L10:**
1. **L6 (orbit-dim equality) is ALREADY LANDED over ℝ** — it is `VoigtDischarge.varietyDim_orbitRankLocus_eq_finrank_range_deformationδ`,
   now `[CharZero]`. The recon listed L6 as a new lemma to assemble; it is the relaxed existing squeeze. The
   full Voigt chain (Granularity 1) also relaxed for free: `codimRep_orbitRankLocus_eq_orbitLinearCodim` and
   both `_unconditional` headlines are now `[CharZero]` — i.e. the **real codim formula `codim_ℝ = orbitLinearCodim`
   holds over ℝ as a theorem**, not just the bare squeeze. (Granularity 1's "earned extension" partially banked.)
2. **The chain has more `[IsAlgClosed]` rungs than the recon traced** — `isPrime_vanishingIdeal_orbitRankLocus`
   + the 3 NullstellensatzCodim bridges. The full G2 build MUST green-gate the full aggregator each wave (not
   per-module) to catch these. The remaining `[IsAlgClosed]` consumers (the θ-count geometric headlines in
   `CTheta*`, `ClosureBridge`, the chart layer `SourceNoDrop`/`SchurSideNoDrop`/`RouteCAssembly`,
   `FibreCodimFinal`) were NOT relaxed this tide — they are L8's chart-sweep δ-shift territory + the
   geometric component count, the next wave.
3. **L7 next-action:** start with the tensor-conjugacy identity (the one gap); the rank brick is banked.
4. **L8 (chart δ-shift over ℝ) is the remaining unknown** — relax `SourceNoDrop` (1 alg-closed use) +
   `ClosureBridge` (4, tracing to the orbit-codim=C piece, now relaxed via L6). Probe whether the chart layer
   or the sigma-side alternative is lighter, as the recon flagged.

---

## Files touched (all green, sorry-free, `scripts/sorries` = 0)

- `lean/DLNFibre/Core/OrbitVariety.lean` — primeness/irreducibility `[IsAlgClosed]→[Infinite]` + ℚ witness.
- `lean/DLNFibre/Core/OrbitSmooth.lean` — domain/dense/SpecModel `→[PerfectField][Infinite]` + ℚ smoothness witness.
- `lean/DLNFibre/Core/SmoothPointRegular.lean` — M3 cotangent trio `→[PerfectField]`.
- `lean/DLNFibre/Core/OrbitTangentCotangent.lean` — the crux + R5/R6 chain `→[PerfectField]`.
- `lean/DLNFibre/Core/OrbitClosure.lean` — `isPrime_vanishingIdeal_orbitRankLocus` `→[Infinite]`.
- `lean/DLNFibre/Core/NullstellensatzCodim.lean` — 3 `codimRep_*` bridges `→[Field]` (vestigial).
- `lean/DLNFibre/Core/VoigtDischarge.lean` — squeeze + Voigt + 2 headlines `→[CharZero]`; import `CharZero.Infinite`;
  ℝ squeeze + ℝ Voigt witnesses.

## Codex

`codex/relaxation-plan-{prompt,answer}.md` (xhigh, decorrelated). Q1–Q3: relaxation mechanical, no instance-
resolution risk, bottom-up; `IsReduced(Spec)` from `IsDomain` auto. Q4: route R2, `finrank_range_baseChange`
exists in-repo (confirmed), L7 is packaging. GO. Full convergence with the independent read.

## Reflection

The relaxation was mechanical as predicted, but the recon's chain was INCOMPLETE (3 extra rungs +
the `CharZero⟹Infinite` import). The lesson: full-aggregator green-gating per wave is mandatory (the
`lean/CLAUDE.md` note about single-module builds masking failures fired exactly here — Step 5 passed on
a stale olean while the full build exposed `isPrime_vanishingIdeal_orbitRankLocus`). Next clarifying step
for the full build: the L7 tensor-conjugacy identity (the rank half is banked) and the L8 chart-vs-sigma
probe.
