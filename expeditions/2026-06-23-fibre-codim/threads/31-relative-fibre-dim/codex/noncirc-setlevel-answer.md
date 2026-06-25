   Updating ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (HEAD)
    Updated ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (fa7351f6ef4773f536ee4975c3251325eb9c44df)
Reading prompt from stdin...
OpenAI Codex v0.142.0
--------
workdir: /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
model: gpt-5.5
provider: openai-aisi
approval: untrusted
sandbox: read-only
reasoning effort: high
reasoning summaries: none
session id: 019efaba-6d04-7331-bc41-0b1525b303af
--------
user
# Codex consult — does the SET-LEVEL chart trivialization dodge the R2-3b-4 reducedness circularity?

Lean 4 + Mathlib v4.29. I am building route (c) for the relative-fibre-dimension identity
`hSweep : varietyDim Σ^r = δ + varietyDim F`. Rung 1 = a single-chart trivialization. The DECISIVE
de-risk: is the SET-LEVEL / `varietyDim` version non-circular, given a PRIOR attempt (R2-3b-4) at a
SCHEME-level iso was circular?

## The prior circularity (R2-3b-4), precisely

Earlier the team tried to prove the fibre `F_E` is REDUCED by building a *scheme/ring* product iso
`e : S ≃ₐ[k] R ⊗_k F_E` (S = O(Σ̄^r ∩ pivot chart), R = O(base chart)), then descending reducedness
`S reduced ⟹ R⊗F_E reduced ⟹ F_E reduced`. This was CIRCULAR for reducedness: the forward map of `e`
needs the ideal inclusion `sigmaIdeal ≤ ker(comorphism)`, but only `sigmaIdeal ≤ radical(ker)` is
available — establishing the strict inclusion (= reducedness of the cut) is what `e` was meant to
prove. So `e` as a *ring iso proving reducedness* re-enters its own hypothesis.

Independently known (NOT circular): `deepBaseComap_sigmaIdeal_le` — the base `sigmaIdeal` maps INTO
the deep `sigmaIdeal` (a containment, proved by a point-chase `mult`-image argument), does NOT assume
the circular inclusion.

## My claim: the dimension version dodges it (need you to confirm or break)

For `hSweep` I do NOT need reducedness. `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`
and `vanishingIdeal Z` is ALREADY radical (it's a vanishing ideal). Krull dim is RADICAL-INSENSITIVE:
`ringKrullDim (R⧸I) = ringKrullDim (R⧸√I)`. So `varietyDim` reads only the REDUCED/variety structure;
I never need to know whether the *generator* ideal `fibreGenIdeal` equals its radical. The chart
trivialization I need is a **variety-level (set-level, reduced) isomorphism** `mult⁻¹(U) ∩ Σ^r ≅ U × F`,
not a scheme iso of (possibly non-reduced) coordinate rings.

The set-level pieces LANDED: the sweep `Σ^r = ⋃_P (P•·)''F` (`H = GL×GL` acts, `mult` equivariant,
all rank-r matrices `H`-equivalent); the gauge coordinate-change `AlgEquiv` `nEquiv d P` on the
polynomial ring (transports `multPoly`); the comorphism `multComap`.

## Questions (be adversarial — this is make-or-break)

1. **Is `varietyDim` genuinely radical-insensitive in Mathlib v4.29** — i.e. is `ringKrullDim (R⧸I) =
   ringKrullDim (R⧸ I.radical)` available (or `ringKrullDim` factors through `√`)? Name the lemma if
   so. This is the linchpin: if true, the dimension route NEVER touches the reducedness question.

2. **Does constructing the SET-LEVEL chart bijection `mult⁻¹(U) ∩ Σ^r ≅ U × F` re-enter the
   circularity?** The map is: on the pivot chart `U`, gauge-normalize the target to `E` (algebraic
   row/col ops, the `H`-action), giving `A ∈ mult⁻¹(B) ↦ (B, P_B • A) ∈ U × F` where `P_B` is the
   chart's normalizing gauge. This is a bijection of SETS / a `varietyDim`-preserving map. Does
   proving it require the radical inclusion (`sigmaIdeal ≤ ker`), or only: (i) the sweep set-identity
   (LANDED, non-circular), (ii) the gauge being an algebraic iso on the chart open (LANDED `nEquiv`),
   (iii) `mult ∘ gauge = const E` on the fibre (LANDED `nSub_mult`)? My read: it needs only set-level
   + gauge-algebraic facts, all radical-insensitive — but tell me if the dimension-additivity
   `varietyDim(U×F) = varietyDim U + varietyDim F` secretly needs flatness/reducedness.

3. **The product-dimension step `varietyDim(U × F) = varietyDim U + varietyDim F`.** For a product of
   affine varieties over an alg-closed field, `dim(X × Y) = dim X + dim Y`. Is this in Mathlib v4.29
   (as `ringKrullDim (A ⊗_k B) = ringKrullDim A + ringKrullDim B`, or a variety-dimension product)?
   If absent, is it provable WITHOUT the relative-Noether/`proof_wanted` machinery — e.g. via `trdeg`
   of the tensor product (trdeg IS additive for the tensor of two domains over a field) PLUS the
   reducible-case max-over-components bookkeeping? Note `F` is REDUCIBLE (comps 10,9,9 on (3,3,3)r1) —
   does the product-dim survive reducibility radical-insensitively (take max component on each side)?

4. **The glue over the finite pivot cover.** `varietyDim(⋃_i Z_i) = max_i varietyDim(Z_i)` for a
   finite cover — is that radical-insensitive and in Mathlib (or trivial from `ringKrullDim` of a
   product/finite-union of irreducibles)?

5. **Net verdict:** does the SET-LEVEL/`varietyDim` route (c) dodge the R2-3b-4 circularity? If YES,
   give the rung decomposition (single-chart triv → per-chart dim-additivity → glue) and which steps
   are Mathlib-present vs new. If NO (the set-level chart iso ALSO needs the radical inclusion or some
   reducedness), say so plainly — that triggers a fallback to citing `hSweep`.

The key thing I need from you: a clean YES/NO on whether radical-insensitivity of `varietyDim` lets
the chart trivialization avoid the `sigmaIdeal ≤ ker` inclusion that made the scheme iso circular.

codex
I’ll check the local workspace first, especially the pinned Mathlib sources and existing definitions, because the exact lemma names and available dimension API matter here.
exec
/bin/bash -lc "pwd && rg --files -g 'lake-manifest.json' -g 'lakefile.*' -g 'lean-toolchain' -g 'CLAUDE.md' -g 'README.md' -g '*.lean' | head -200" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex

exec
/bin/bash -lc "rg -n \"varietyDim|ringKrullDim|radical|IsJacobson|KrullDim|tensor|TensorProduct\" . -g '*.lean' -g '*.md' | head -300" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
./route-choice-prompt.md:10:varietyDim (Σ^r)  =  δ  +  varietyDim F
./route-choice-prompt.md:13:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./route-choice-prompt.md:18:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./route-choice-prompt.md:28:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./route-choice-prompt.md:29:   ringKrullDim (R ⧸ ker(pullback)) = ringKrullDim((pullback).range) = trdeg_k(range)` for a
./route-choice-prompt.md:31:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./route-choice-prompt.md:52:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./route-choice-prompt.md:60:max component, i.e. `ringKrullDim`)? Is `ringKrullDim`-additivity over a sweep even true without
./route-choice-prompt.md:73:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./route-choice-prompt.md:75:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./noncirc-setlevel-prompt.md:4:`hSweep : varietyDim Σ^r = δ + varietyDim F`. Rung 1 = a single-chart trivialization. The DECISIVE
./noncirc-setlevel-prompt.md:5:de-risk: is the SET-LEVEL / `varietyDim` version non-circular, given a PRIOR attempt (R2-3b-4) at a
./noncirc-setlevel-prompt.md:13:needs the ideal inclusion `sigmaIdeal ≤ ker(comorphism)`, but only `sigmaIdeal ≤ radical(ker)` is
./noncirc-setlevel-prompt.md:23:For `hSweep` I do NOT need reducedness. `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`
./noncirc-setlevel-prompt.md:24:and `vanishingIdeal Z` is ALREADY radical (it's a vanishing ideal). Krull dim is RADICAL-INSENSITIVE:
./noncirc-setlevel-prompt.md:25:`ringKrullDim (R⧸I) = ringKrullDim (R⧸√I)`. So `varietyDim` reads only the REDUCED/variety structure;
./noncirc-setlevel-prompt.md:26:I never need to know whether the *generator* ideal `fibreGenIdeal` equals its radical. The chart
./noncirc-setlevel-prompt.md:36:1. **Is `varietyDim` genuinely radical-insensitive in Mathlib v4.29** — i.e. is `ringKrullDim (R⧸I) =
./noncirc-setlevel-prompt.md:37:   ringKrullDim (R⧸ I.radical)` available (or `ringKrullDim` factors through `√`)? Name the lemma if
./noncirc-setlevel-prompt.md:43:   chart's normalizing gauge. This is a bijection of SETS / a `varietyDim`-preserving map. Does
./noncirc-setlevel-prompt.md:44:   proving it require the radical inclusion (`sigmaIdeal ≤ ker`), or only: (i) the sweep set-identity
./noncirc-setlevel-prompt.md:47:   + gauge-algebraic facts, all radical-insensitive — but tell me if the dimension-additivity
./noncirc-setlevel-prompt.md:48:   `varietyDim(U×F) = varietyDim U + varietyDim F` secretly needs flatness/reducedness.
./noncirc-setlevel-prompt.md:50:3. **The product-dimension step `varietyDim(U × F) = varietyDim U + varietyDim F`.** For a product of
./noncirc-setlevel-prompt.md:52:   (as `ringKrullDim (A ⊗_k B) = ringKrullDim A + ringKrullDim B`, or a variety-dimension product)?
./noncirc-setlevel-prompt.md:54:   of the tensor product (trdeg IS additive for the tensor of two domains over a field) PLUS the
./noncirc-setlevel-prompt.md:56:   does the product-dim survive reducibility radical-insensitively (take max component on each side)?
./noncirc-setlevel-prompt.md:58:4. **The glue over the finite pivot cover.** `varietyDim(⋃_i Z_i) = max_i varietyDim(Z_i)` for a
./noncirc-setlevel-prompt.md:59:   finite cover — is that radical-insensitive and in Mathlib (or trivial from `ringKrullDim` of a
./noncirc-setlevel-prompt.md:62:5. **Net verdict:** does the SET-LEVEL/`varietyDim` route (c) dodge the R2-3b-4 circularity? If YES,
./noncirc-setlevel-prompt.md:64:   are Mathlib-present vs new. If NO (the set-level chart iso ALSO needs the radical inclusion or some
./noncirc-setlevel-prompt.md:67:The key thing I need from you: a clean YES/NO on whether radical-insensitivity of `varietyDim` lets
./noncirc-setlevel-answer.md:19:`hSweep : varietyDim Σ^r = δ + varietyDim F`. Rung 1 = a single-chart trivialization. The DECISIVE
./noncirc-setlevel-answer.md:20:de-risk: is the SET-LEVEL / `varietyDim` version non-circular, given a PRIOR attempt (R2-3b-4) at a
./noncirc-setlevel-answer.md:28:needs the ideal inclusion `sigmaIdeal ≤ ker(comorphism)`, but only `sigmaIdeal ≤ radical(ker)` is
./noncirc-setlevel-answer.md:38:For `hSweep` I do NOT need reducedness. `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`
./noncirc-setlevel-answer.md:39:and `vanishingIdeal Z` is ALREADY radical (it's a vanishing ideal). Krull dim is RADICAL-INSENSITIVE:
./noncirc-setlevel-answer.md:40:`ringKrullDim (R⧸I) = ringKrullDim (R⧸√I)`. So `varietyDim` reads only the REDUCED/variety structure;
./noncirc-setlevel-answer.md:41:I never need to know whether the *generator* ideal `fibreGenIdeal` equals its radical. The chart
./noncirc-setlevel-answer.md:51:1. **Is `varietyDim` genuinely radical-insensitive in Mathlib v4.29** — i.e. is `ringKrullDim (R⧸I) =
./noncirc-setlevel-answer.md:52:   ringKrullDim (R⧸ I.radical)` available (or `ringKrullDim` factors through `√`)? Name the lemma if
./noncirc-setlevel-answer.md:58:   chart's normalizing gauge. This is a bijection of SETS / a `varietyDim`-preserving map. Does
./noncirc-setlevel-answer.md:59:   proving it require the radical inclusion (`sigmaIdeal ≤ ker`), or only: (i) the sweep set-identity
./noncirc-setlevel-answer.md:62:   + gauge-algebraic facts, all radical-insensitive — but tell me if the dimension-additivity
./noncirc-setlevel-answer.md:63:   `varietyDim(U×F) = varietyDim U + varietyDim F` secretly needs flatness/reducedness.
./noncirc-setlevel-answer.md:65:3. **The product-dimension step `varietyDim(U × F) = varietyDim U + varietyDim F`.** For a product of
./noncirc-setlevel-answer.md:67:   (as `ringKrullDim (A ⊗_k B) = ringKrullDim A + ringKrullDim B`, or a variety-dimension product)?
./noncirc-setlevel-answer.md:69:   of the tensor product (trdeg IS additive for the tensor of two domains over a field) PLUS the
./noncirc-setlevel-answer.md:71:   does the product-dim survive reducibility radical-insensitively (take max component on each side)?
./noncirc-setlevel-answer.md:73:4. **The glue over the finite pivot cover.** `varietyDim(⋃_i Z_i) = max_i varietyDim(Z_i)` for a
./noncirc-setlevel-answer.md:74:   finite cover — is that radical-insensitive and in Mathlib (or trivial from `ringKrullDim` of a
./noncirc-setlevel-answer.md:77:5. **Net verdict:** does the SET-LEVEL/`varietyDim` route (c) dodge the R2-3b-4 circularity? If YES,
./noncirc-setlevel-answer.md:79:   are Mathlib-present vs new. If NO (the set-level chart iso ALSO needs the radical inclusion or some
./noncirc-setlevel-answer.md:82:The key thing I need from you: a clean YES/NO on whether radical-insensitivity of `varietyDim` lets
./route-choice-answer.md:25:varietyDim (Σ^r)  =  δ  +  varietyDim F
./route-choice-answer.md:28:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./route-choice-answer.md:33:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./route-choice-answer.md:43:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./route-choice-answer.md:44:   ringKrullDim (R ⧸ ker(pullback)) = ringKrullDim((pullback).range) = trdeg_k(range)` for a
./route-choice-answer.md:46:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./route-choice-answer.md:67:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./route-choice-answer.md:75:max component, i.e. `ringKrullDim`)? Is `ringKrullDim`-additivity over a sweep even true without
./route-choice-answer.md:88:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./route-choice-answer.md:90:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./route-choice-answer.md:114:./route-choice-prompt.md:31:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./route-choice-answer.md:129:./route-choice-answer.md:46:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./route-choice-answer.md:188:varietyDim (Σ^r)  =  δ  +  varietyDim F
./route-choice-answer.md:191:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./route-choice-answer.md:196:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./route-choice-answer.md:206:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./route-choice-answer.md:207:   ringKrullDim (R ⧸ ker(pullback)) = ringKrullDim((pullback).range) = trdeg_k(range)` for a
./route-choice-answer.md:209:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./route-choice-answer.md:230:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./route-choice-answer.md:238:max component, i.e. `ringKrullDim`)? Is `ringKrullDim`-additivity over a sweep even true without
./route-choice-answer.md:251:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./route-choice-answer.md:253:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./route-choice-answer.md:277:./route-choice-prompt.md:31:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./route-choice-answer.md:292:./route-choice-answer.md:46:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./route-choice-answer.md:325:/bin/bash -lc 'rg -n "Noether.*Norm|Noetherian.*Norm|normalization|GenericFreeness|generic freeness|height_eq_under|FlatQuasiFinite|HasGoingDown|trdeg_add_eq|rankLocus|productRankLocus|varietyDim|vanishingIdeal" -S .' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean
./route-choice-answer.md:450:./DLNFibre.lean:160:-- `codimRepCanonical Z + varietyDim Z = card` for nonempty Z. Discharges the catenary hyps of RouteCAssembly.
./route-choice-answer.md:466:./DLNFibre/Core/OrbitPullbackDim.lean:6:# `DLNFibre.Core.OrbitPullbackDim` — route-c setup: `varietyDim(Z_M) = ringKrullDim((μ_M^*).range)`
./route-choice-answer.md:467:./DLNFibre/Core/OrbitPullbackDim.lean:16:1. **Ideal identification.** `varietyDim Z_M = ringKrullDim (MvPolynomial (RepCoord d) k ⧸
./route-choice-answer.md:468:./DLNFibre/Core/OrbitPullbackDim.lean:17:   ker μ_M^*)`, immediate from the `varietyDim` definition, the Abeasis–Del Fra ideal equality L6.4
./route-choice-answer.md:471:./DLNFibre/Core/OrbitPullbackDim.lean:25:The headline `varietyDim_eq_ringKrullDim_range_orbitPullback` hands A4 a finitely-generated domain
./route-choice-answer.md:472:./DLNFibre/Core/OrbitPullbackDim.lean:48:`MvPolynomial (RepCoord d) k ⧸ ker μ_M^*`. `varietyDim` definition, then L6.4
./route-choice-answer.md:475:./DLNFibre/Core/OrbitPullbackDim.lean:52:theorem varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker [Infinite k]
./route-choice-answer.md:476:./DLNFibre/Core/OrbitPullbackDim.lean:54:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./route-choice-answer.md:477:./DLNFibre/Core/OrbitPullbackDim.lean:57:  rw [varietyDim, vanishingIdeal_orbitRankLocus_eq_orbitSet M, ← range_orbitMap,
./route-choice-answer.md:479:./DLNFibre/Core/OrbitPullbackDim.lean:70:transcendence degree. Combines `varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker` with the
./route-choice-answer.md:480:./DLNFibre/Core/OrbitPullbackDim.lean:74:theorem varietyDim_eq_ringKrullDim_range_orbitPullback [Infinite k] {d : Fin (N + 1) → ℕ}
./route-choice-answer.md:481:./DLNFibre/Core/OrbitPullbackDim.lean:76:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./route-choice-answer.md:482:./DLNFibre/Core/OrbitPullbackDim.lean:78:  rw [varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker M,
./route-choice-answer.md:483:./DLNFibre/Core/OrbitPullbackDim.lean:89:/-- The headline at the concrete `(2,2,2)/ℚ` tuple: `varietyDim (canonicalCoord '' orbitRankLocus
./route-choice-answer.md:484:./DLNFibre/Core/OrbitPullbackDim.lean:93:    varietyDim (canonicalCoord dWitness '' orbitRankLocus tupleWitnessQ)
./route-choice-answer.md:485:./DLNFibre/Core/OrbitPullbackDim.lean:95:  varietyDim_eq_ringKrullDim_range_orbitPullback tupleWitnessQ
./route-choice-answer.md:506:./DLNFibre/Core/DeterminantalStratumDim.lean:29:4. **The catenary bridge** (LANDED `codimRep_add_varietyDim_eq_card`): `codim + dim = card = m·n`,
./route-choice-answer.md:520:./DLNFibre/Core/DeterminantalStratumDim.lean:224:> `varietyDim (Mat^{rk ≤ r}_{m × n}) = r · (n + m − r)`.
./route-choice-answer.md:521:./DLNFibre/Core/DeterminantalStratumDim.lean:229:theorem varietyDim_productRankLocusLE_stratum [IsAlgClosed k] [CharZero k] (n m r : ℕ)
./route-choice-answer.md:522:./DLNFibre/Core/DeterminantalStratumDim.lean:231:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./route-choice-answer.md:524:./DLNFibre/Core/DeterminantalStratumDim.lean:237:  have hbridge := codimRep_add_varietyDim_eq_card (canonicalCoord (dStratum n m)) Z
./route-choice-answer.md:527:./DLNFibre/Core/DeterminantalStratumDim.lean:249:  -- `hbridge : (n−r)(m−r) + varietyDim Z = m·n`
./route-choice-answer.md:528:./DLNFibre/Core/DeterminantalStratumDim.lean:258:  have heq : (((n - r) * (m - r) : ℕ) : ℕ∞) + varietyDim (canonicalCoord (dStratum n m) '' Z)
./route-choice-answer.md:529:./DLNFibre/Core/DeterminantalStratumDim.lean:268:    varietyDim (canonicalCoord (dStratum 2 2) '' productRankLocusLE (k := k) (dStratum 2 2) 1)
./route-choice-answer.md:530:./DLNFibre/Core/DeterminantalStratumDim.lean:270:  have h := varietyDim_productRankLocusLE_stratum (k := k) 2 2 1 (by norm_num) (by norm_num)
./route-choice-answer.md:546:./DLNFibre/Core/DeepChartRing.lean:133:`sigmaIdeal` is radical (`vanishingIdeal_isRadical`, over `[IsAlgClosed k]`) and localization
./route-choice-answer.md:577:./DLNFibre/Core/FibreDimFibration.lean:45:`varietyDim = δ`, lifting the `unbotD 0` to the genuine `WithBot ℕ∞` value (the quotient is
./route-choice-answer.md:578:./DLNFibre/Core/FibreDimFibration.lean:51:The thermometer `varietyDim_productRankLocusLE_stratum` gives the `ℕ∞`-via-`unbotD` value; this lifts
./route-choice-answer.md:579:./DLNFibre/Core/FibreDimFibration.lean:54:theorem ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta [IsAlgClosed k] [CharZero k]
./route-choice-answer.md:585:./DLNFibre/Core/FibreDimFibration.lean:64:  -- the thermometer: `varietyDim = δ`, i.e. `(ringKrullDim (R ⧸ I)).unbotD 0 = δ`.
./route-choice-answer.md:586:./DLNFibre/Core/FibreDimFibration.lean:65:  have hvd : varietyDim (canonicalCoord (dStratum n m) ''
./route-choice-answer.md:588:./DLNFibre/Core/FibreDimFibration.lean:67:    varietyDim_productRankLocusLE_stratum n m r hn hm
./route-choice-answer.md:589:./DLNFibre/Core/FibreDimFibration.lean:68:  rw [varietyDim, ← hI] at hvd
./route-choice-answer.md:597:./DLNFibre/Core/FibreDimFibration.lean:102:    ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta n m r hn hm]
./route-choice-answer.md:605:./DLNFibre/Core/EndBaseChangeSweep.lean:16:consequence** `varietyDim (productRankLocus d r) = δ + varietyDim (fibre d E)` is the *one genuinely
./route-choice-answer.md:637:./DLNFibre/Core/FibreHeightDirect.lean:11:`fibreGenIdeal d B` (`Core.MultComorphism.vanishingIdeal_image_fibre_eq_radical`). The point of this
./route-choice-answer.md:639:./DLNFibre/Core/FibreHeightDirect.lean:47:(definition of `codimRepCanonical`/`codimRep`); `vanishingIdeal (…) = (fibreGenIdeal d B).radical`
./route-choice-answer.md:640:./DLNFibre/Core/FibreHeightDirect.lean:48:(`vanishingIdeal_image_fibre_eq_radical`, the Nullstellensatz); `(radical I).height = I.height`
./route-choice-answer.md:641:./DLNFibre/Core/FibreHeightDirect.lean:54:  rw [codimRepCanonical, codimRep, vanishingIdeal_image_fibre_eq_radical, Ideal.height_radical]
./route-choice-answer.md:643:./DLNFibre/Core/NullstellensatzCodim.lean:20:   Nullstellensatz over `[IsAlgClosed k]`): `vanishingIdeal Z` is always **radical**
./route-choice-answer.md:649:./DLNFibre/Core/NullstellensatzCodim.lean:31:   irreducible"), `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ` (`ℕ∞`, additive — `ℕ∞`
./route-choice-answer.md:650:./DLNFibre/Core/NullstellensatzCodim.lean:37:`axiom`. `varietyDim Z = ringKrullDim (R ⧸ vanishingIdeal Z)` is the Krull dimension of the
./route-choice-answer.md:652:./DLNFibre/Core/NullstellensatzCodim.lean:67:strong Nullstellensatz it equals its own radical, via `vanishingIdeal Z = vanishingIdeal (zeroLocus
./route-choice-answer.md:653:./DLNFibre/Core/NullstellensatzCodim.lean:68:(vanishingIdeal Z))` `= (vanishingIdeal Z).radical`. -/
./route-choice-answer.md:656:./DLNFibre/Core/NullstellensatzCodim.lean:71:  have h : vanishingIdeal k Z = (vanishingIdeal k Z).radical := by
./route-choice-answer.md:658:./DLNFibre/Core/NullstellensatzCodim.lean:74:        vanishingIdeal_zeroLocus_eq_radical (K := k)]
./route-choice-answer.md:664:./DLNFibre/Core/NullstellensatzCodim.lean:87:Nullstellensatz forces `vanishingIdeal (zeroLocus (vanishingIdeal Z)) = (vanishingIdeal Z).radical`,
./route-choice-answer.md:669:./DLNFibre/Core/NullstellensatzCodim.lean:97:    have h3 : vanishingIdeal k (zeroLocus k (vanishingIdeal k Z)) = (vanishingIdeal k Z).radical :=
./route-choice-answer.md:670:./DLNFibre/Core/NullstellensatzCodim.lean:98:      vanishingIdeal_zeroLocus_eq_radical (K := k) _
./route-choice-answer.md:674:./DLNFibre/Core/NullstellensatzCodim.lean:139:noncomputable def varietyDim (Z : Set (σ → k)) : ℕ∞ :=
./route-choice-answer.md:675:./DLNFibre/Core/NullstellensatzCodim.lean:140:  (ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal k Z)).unbotD 0
./route-choice-answer.md:677:./DLNFibre/Core/NullstellensatzCodim.lean:144:the ambient dimension `Nat.card σ`: `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ`. The
./route-choice-answer.md:679:./DLNFibre/Core/NullstellensatzCodim.lean:147:theorem height_vanishingIdeal_add_varietyDim_eq_card [Finite σ] {Z : Set (σ → k)}
./route-choice-answer.md:681:./DLNFibre/Core/NullstellensatzCodim.lean:149:    (vanishingIdeal k Z).height + varietyDim Z = (Nat.card σ : ℕ∞) := by
./route-choice-answer.md:682:./DLNFibre/Core/NullstellensatzCodim.lean:150:  have key := height_add_ringKrullDim_quotient_eq_card (vanishingIdeal k Z)
./route-choice-answer.md:684:./DLNFibre/Core/NullstellensatzCodim.lean:153:  have hne : ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal k Z) ≠ ⊥ :=
./route-choice-answer.md:685:./DLNFibre/Core/NullstellensatzCodim.lean:155:      ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial σ k ⧸ vanishingIdeal k Z)
./route-choice-answer.md:686:./DLNFibre/Core/NullstellensatzCodim.lean:157:  rw [varietyDim, ← hm, WithBot.unbotD_coe]
./route-choice-answer.md:687:./DLNFibre/Core/NullstellensatzCodim.lean:162:`height (vanishingIdeal Z) = Nat.card σ − varietyDim Z` for an irreducible variety `Z` (`ℕ∞`
./route-choice-answer.md:688:./DLNFibre/Core/NullstellensatzCodim.lean:163:subtraction; lossless here since `varietyDim Z ≤ Nat.card σ`). The geometric codimension is the
./route-choice-answer.md:689:./DLNFibre/Core/NullstellensatzCodim.lean:165:theorem height_vanishingIdeal_eq_card_sub_varietyDim [Finite σ] {Z : Set (σ → k)}
./route-choice-answer.md:691:./DLNFibre/Core/NullstellensatzCodim.lean:167:    (vanishingIdeal k Z).height = (Nat.card σ : ℕ∞) - varietyDim Z := by
./route-choice-answer.md:692:./DLNFibre/Core/NullstellensatzCodim.lean:168:  have hadd := height_vanishingIdeal_add_varietyDim_eq_card hp
./route-choice-answer.md:693:./DLNFibre/Core/NullstellensatzCodim.lean:169:  have hne : varietyDim Z ≠ ⊤ := by
./route-choice-answer.md:694:./DLNFibre/Core/NullstellensatzCodim.lean:182:`height_vanishingIdeal_add_varietyDim_eq_card` at `σ := RepCoord d`, `Z := coord '' Z`. -/
./route-choice-answer.md:695:./DLNFibre/Core/NullstellensatzCodim.lean:183:theorem codimRep_add_varietyDim_eq_card [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./route-choice-answer.md:697:./DLNFibre/Core/NullstellensatzCodim.lean:186:    codimRep coord Z + varietyDim (coord '' Z) = (Nat.card (RepCoord d) : ℕ∞) :=
./route-choice-answer.md:698:./DLNFibre/Core/NullstellensatzCodim.lean:187:  height_vanishingIdeal_add_varietyDim_eq_card hp
./route-choice-answer.md:699:./DLNFibre/Core/NullstellensatzCodim.lean:190:varietyDim (coord '' Z)` for an irreducible variety `coord '' Z`: geometric codimension `=` ambient
./route-choice-answer.md:700:./DLNFibre/Core/NullstellensatzCodim.lean:192:theorem codimRep_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./route-choice-answer.md:702:./DLNFibre/Core/NullstellensatzCodim.lean:195:    codimRep coord Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (coord '' Z) :=
./route-choice-answer.md:703:./DLNFibre/Core/NullstellensatzCodim.lean:196:  height_vanishingIdeal_eq_card_sub_varietyDim hp
./route-choice-answer.md:704:./DLNFibre/Core/NullstellensatzCodim.lean:199:`canonicalCoord d`, `codimRepCanonical Z = Nat.card (RepCoord d) − varietyDim (canonicalCoord d ''
./route-choice-answer.md:705:./DLNFibre/Core/NullstellensatzCodim.lean:201:theorem codimRepCanonical_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./route-choice-answer.md:707:./DLNFibre/Core/NullstellensatzCodim.lean:205:    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
./route-choice-answer.md:708:./DLNFibre/Core/NullstellensatzCodim.lean:206:  codimRep_eq_card_sub_varietyDim (canonicalCoord d) Z hp
./route-choice-answer.md:712:./DLNFibre/Core/NullstellensatzCodim.lean:225:alg-closed, `σ` finite), the vanishing ideal is `⊥` (prime), `varietyDim = Nat.card σ`, the bridge
./route-choice-answer.md:714:./DLNFibre/Core/NullstellensatzCodim.lean:230:      + varietyDim (Set.univ : Set (σ → k)) = (Nat.card σ : ℕ∞) := by
./route-choice-answer.md:717:./DLNFibre/Core/NullstellensatzCodim.lean:233:  exact height_vanishingIdeal_add_varietyDim_eq_card this
./route-choice-answer.md:740:./DLNFibre/Core/FibreReducedTrivialization.lean:33:3. **`vanishingIdeal_fibre_eq_fibreGenIdeal_of_trivialization`** — the **radical-collapse** of
./route-choice-answer.md:741:./DLNFibre/Core/FibreReducedTrivialization.lean:34:   `MultComorphism` point 4: with the cut ideal radical, `vanishingIdeal (fibre d B) =
./route-choice-answer.md:744:./DLNFibre/Core/FibreReducedTrivialization.lean:104:a `vanishingIdeal`), the fibre ideal `fibreGenIdeal d B` is **radical**. The certified mechanism:
./route-choice-answer.md:745:./DLNFibre/Core/FibreReducedTrivialization.lean:122:`vanishingIdeal (fibre d B) = radical (fibreGenIdeal d B)` collapses to
./route-choice-answer.md:746:./DLNFibre/Core/FibreReducedTrivialization.lean:123:`vanishingIdeal (fibre d B) = fibreGenIdeal d B`: the `radical (·)` wrapper drops. The clean
./route-choice-answer.md:749:./DLNFibre/Core/FibreReducedTrivialization.lean:132:  rw [vanishingIdeal_image_fibre_eq_radical,
./route-choice-answer.md:813:./DLNFibre/Core/PolynomialDimension.lean:18:* **L5.5** `ringKrullDim_quotient_eq_noetherRank` — `dim (R ⧸ p)` equals the Noether-normalization
./route-choice-answer.md:820:./DLNFibre/Core/OrbitDifferentialRank.lean:35:Krull-dimension bound) and `varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional`
./route-choice-answer.md:821:./DLNFibre/Core/OrbitDifferentialRank.lean:659:/-- **The AG-half submersion bound `varietyDim Z_M ≤ finrank (range δ⁰)`, UNCONDITIONAL (char 0).**
./route-choice-answer.md:822:./DLNFibre/Core/OrbitDifferentialRank.lean:660:Chaining the unconditional A4.4 with the landed A0 link `varietyDim_eq_ringKrullDim_range_orbitPullback`
./route-choice-answer.md:823:./DLNFibre/Core/OrbitDifferentialRank.lean:664:theorem varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional
./route-choice-answer.md:824:./DLNFibre/Core/OrbitDifferentialRank.lean:666:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./route-choice-answer.md:825:./DLNFibre/Core/OrbitDifferentialRank.lean:668:  varietyDim_orbitRankLocus_le_finrank_range_deformationδ M
./route-choice-answer.md:846:./DLNFibre/Core/RadicalCatenary.lean:27:The headline specialises to `codimRepCanonical Z + varietyDim Z = card` for any **nonempty**
./route-choice-answer.md:847:./DLNFibre/Core/RadicalCatenary.lean:157:/-! ## Specialisation to the geometry layer (`codimRepCanonical Z + varietyDim Z = card`) -/
./route-choice-answer.md:852:./DLNFibre/Core/RadicalCatenary.lean:173:/-- **The reducible-locus catenary at `codimRepCanonical`/`varietyDim` (additive, `ℕ∞`).** For a
./route-choice-answer.md:853:./DLNFibre/Core/RadicalCatenary.lean:176:equal the ambient dimension: `codimRepCanonical Z + varietyDim (canonicalCoord d '' Z) = card`. No
./route-choice-answer.md:854:./DLNFibre/Core/RadicalCatenary.lean:179:theorem codimRepCanonical_add_varietyDim_eq_card_of_nonempty {d : Fin (N + 1) → ℕ}
./route-choice-answer.md:855:./DLNFibre/Core/RadicalCatenary.lean:181:    codimRepCanonical Z + varietyDim (canonicalCoord d '' Z)
./route-choice-answer.md:862:./DLNFibre/Core/RadicalCatenary.lean:197:  rw [codimRepCanonical, codimRep, varietyDim, ← hm, WithBot.unbotD_coe]
./route-choice-answer.md:863:./DLNFibre/Core/RadicalCatenary.lean:203:The reducible-locus catenary at `codimRepCanonical`/`varietyDim` fires on the whole space `univ`
./route-choice-answer.md:864:./DLNFibre/Core/RadicalCatenary.lean:208:      + varietyDim (canonicalCoord dWitness ''
./route-choice-answer.md:865:./DLNFibre/Core/RadicalCatenary.lean:211:  codimRepCanonical_add_varietyDim_eq_card_of_nonempty
./route-choice-answer.md:884:./DLNFibre/Core/OrbitImageDim.lean:10:(`varietyDim_eq_ringKrullDim_range_orbitPullback`), discharges the AG-half of `hVoigt`:
./route-choice-answer.md:885:./DLNFibre/Core/OrbitImageDim.lean:15:- **A0** (landed): `varietyDim Z_M = (ringKrullDim (orbitPullback M).range).unbotD 0`.
./route-choice-answer.md:886:./DLNFibre/Core/OrbitImageDim.lean:77:the A4.3 identity is needed (the chain is `varietyDim = trdeg ≤ genericDifferentialRank ≤ finrank δ⁰`);
./route-choice-answer.md:887:./DLNFibre/Core/OrbitImageDim.lean:90:/-- **A4.4 chained with A0: `varietyDim Z_M ≤ finrank (range δ⁰)`.** Combining the landed A0 link
./route-choice-answer.md:888:./DLNFibre/Core/OrbitImageDim.lean:91:(`varietyDim_eq_ringKrullDim_range_orbitPullback`, needs `[Infinite k]`) with the submersion bound,
./route-choice-answer.md:889:./DLNFibre/Core/OrbitImageDim.lean:95:theorem varietyDim_orbitRankLocus_le_finrank_range_deformationδ
./route-choice-answer.md:890:./DLNFibre/Core/OrbitImageDim.lean:101:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./route-choice-answer.md:891:./DLNFibre/Core/OrbitImageDim.lean:103:  rw [varietyDim_eq_ringKrullDim_range_orbitPullback M]
./route-choice-answer.md:903:./DLNFibre/Core/MultComorphism.lean:27:4. **`vanishingIdeal(fibre) = radical(fibreGenIdeal)`** — over `[IsAlgClosed k]`, the engine's
./route-choice-answer.md:904:./DLNFibre/Core/MultComorphism.lean:28:   Nullstellensatz (`vanishingIdeal_zeroLocus_eq_radical`) reads the fibre's vanishing ideal as the
./route-choice-answer.md:905:./DLNFibre/Core/MultComorphism.lean:158:closed field, the engine's strong Nullstellensatz (`vanishingIdeal_zeroLocus_eq_radical`) reads the
./route-choice-answer.md:906:./DLNFibre/Core/MultComorphism.lean:160:theorem vanishingIdeal_image_fibre_eq_radical [IsAlgClosed k] (d : Fin (N + 1) → ℕ)
./route-choice-answer.md:907:./DLNFibre/Core/MultComorphism.lean:162:    vanishingIdeal k (canonicalCoord d '' (fibre d B)) = (fibreGenIdeal d B).radical := by
./route-choice-answer.md:908:./DLNFibre/Core/MultComorphism.lean:164:    vanishingIdeal_zeroLocus_eq_radical (K := k)]
./route-choice-answer.md:934:./DLNFibre/Core/AffineNoetherRank.lean:59:Noether-normalization rank `s`, hence agree: `(ringKrullDim (R ⧸ p)).unbotD 0 = (trdeg k (R ⧸ p)).toNat`.
./route-choice-answer.md:939:./DLNFibre/Core/FibreDimFibrationProbe.lean:37:/-- LANDED: the determinantal-stratum dimension `varietyDim (Mat^{≤r}) = r(n+m−r) = δ`. -/
./route-choice-answer.md:940:./DLNFibre/Core/FibreDimFibrationProbe.lean:39:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./route-choice-answer.md:941:./DLNFibre/Core/FibreDimFibrationProbe.lean:41:  varietyDim_productRankLocusLE_stratum n m r hn hm
./route-choice-answer.md:944:./DLNFibre/Core/FibreDimFibrationProbe.lean:55:/-- LANDED: the catenary closer (PRIMALITY-gated) — `codim Z = card − varietyDim Z`. -/
./route-choice-answer.md:946:./DLNFibre/Core/FibreDimFibrationProbe.lean:59:    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
./route-choice-answer.md:947:./DLNFibre/Core/FibreDimFibrationProbe.lean:60:  codimRepCanonical_eq_card_sub_varietyDim Z hp
./route-choice-answer.md:952:./DLNFibre/Core/FibreDimFibrationProbe.lean:96:MvPolynomial (RepCoord stratum) k ⧸ vanishingIdeal(…)`. From the thermometer (varietyDim = δ) which
./route-choice-answer.md:953:./DLNFibre/Core/FibreDimFibrationProbe.lean:97:unfolds to exactly `(ringKrullDim (… ⧸ vanishingIdeal …)).unbotD 0`, plus the quotient is nontrivial
./route-choice-answer.md:954:./DLNFibre/Core/FibreDimFibrationProbe.lean:100:/-- `varietyDim` unfolds to the `unbotD 0` of the quotient `ringKrullDim`. -/
./route-choice-answer.md:955:./DLNFibre/Core/FibreDimFibrationProbe.lean:102:    varietyDim Z = (ringKrullDim (MvPolynomial (RepCoord (dStratum 2 2)) k ⧸
./route-choice-answer.md:1050:./DLNFibre/Core/VoigtDischarge.lean:8:The capstone of the AG half. The A4 submersion bound `varietyDim Z_M ≤ finrank (range δ⁰)`
./route-choice-answer.md:1051:./DLNFibre/Core/VoigtDischarge.lean:9:(`varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional`, char 0) and the A6.1 reverse
./route-choice-answer.md:1052:./DLNFibre/Core/VoigtDischarge.lean:10:inequality `finrank (range δ⁰) ≤ varietyDim Z_M` (`finrank_range_deformationδ_le_varietyDim`) squeeze
./route-choice-answer.md:1053:./DLNFibre/Core/VoigtDischarge.lean:11:to **equality** `varietyDim Z_M = finrank (range δ⁰)` (the orbit closure is smooth of the expected
./route-choice-answer.md:1054:./DLNFibre/Core/VoigtDischarge.lean:33:/-! ## The squeeze — `varietyDim Z_M = finrank (range δ⁰)` -/
./route-choice-answer.md:1055:./DLNFibre/Core/VoigtDischarge.lean:38:theorem varietyDim_orbitRankLocus_eq_finrank_range_deformationδ
./route-choice-answer.md:1056:./DLNFibre/Core/VoigtDischarge.lean:40:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./route-choice-answer.md:1057:./DLNFibre/Core/VoigtDischarge.lean:43:  refine le_antisymm ?_ (finrank_range_deformationδ_le_varietyDim M)
./route-choice-answer.md:1058:./DLNFibre/Core/VoigtDischarge.lean:44:  exact varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional M
./route-choice-answer.md:1059:./DLNFibre/Core/VoigtDischarge.lean:64:    have hadd := codimRep_add_varietyDim_eq_card (canonicalCoord d) (orbitRankLocus M)
./route-choice-answer.md:1061:./DLNFibre/Core/VoigtDischarge.lean:66:    rwa [varietyDim_orbitRankLocus_eq_finrank_range_deformationδ M, ← hr] at hadd
./route-choice-answer.md:1063:./DLNFibre/Core/OrbitTangentCotangent.lean:14:# `DLNFibre.Core.OrbitTangentCotangent` — A6.1: the reverse inequality `finrank(range δ⁰) ≤ varietyDim Z_M`
./route-choice-answer.md:1064:./DLNFibre/Core/OrbitTangentCotangent.lean:19:`varietyDim Z_M = finrank (range δ⁰)`, the geometric heart of Voigt's lemma.
./route-choice-answer.md:1065:./DLNFibre/Core/OrbitTangentCotangent.lean:22:`I = orbitIdeal M = vanishingIdeal(orbitSet M)` directly — no determinantal minors, no radical. The
./route-choice-answer.md:1067:./DLNFibre/Core/OrbitTangentCotangent.lean:564:/-! ## R6 — chain `finrank (m_M.Cotangent)` to `varietyDim Z_M` -/
./route-choice-answer.md:1068:./DLNFibre/Core/OrbitTangentCotangent.lean:566:/-- `ringKrullDim (orbitRing M)` is a finite natural number `n`, equal to `varietyDim Z_M`:
./route-choice-answer.md:1069:./DLNFibre/Core/OrbitTangentCotangent.lean:571:      ∧ varietyDim (canonicalCoord d '' orbitRankLocus M) = (n : ℕ∞) := by
./route-choice-answer.md:1070:./DLNFibre/Core/OrbitTangentCotangent.lean:579:  -- `varietyDim Z_M = (ringKrullDim (orbitRing M)).unbotD 0` (L6.4 + `varietyDim` def)
./route-choice-answer.md:1071:./DLNFibre/Core/OrbitTangentCotangent.lean:580:  have hvar : varietyDim (canonicalCoord d '' orbitRankLocus M)
./route-choice-answer.md:1072:./DLNFibre/Core/OrbitTangentCotangent.lean:582:    rw [varietyDim, vanishingIdeal_orbitRankLocus_eq_orbitSet M]; rfl
./route-choice-answer.md:1073:./DLNFibre/Core/OrbitTangentCotangent.lean:598:/-- **R6 — `finrank k (m_M.Cotangent) = varietyDim Z_M`.** The cotangent finrank equals the variety
./route-choice-answer.md:1074:./DLNFibre/Core/OrbitTangentCotangent.lean:601:GAP3 (`ringKrullDim (AtPrime m_M) = ringKrullDim (orbitRing M)`), and `varietyDim Z_M =
./route-choice-answer.md:1075:./DLNFibre/Core/OrbitTangentCotangent.lean:603:theorem finrank_cotangent_eq_varietyDim [IsAlgClosed k] (M : Tuple (k := k) d) :
./route-choice-answer.md:1076:./DLNFibre/Core/OrbitTangentCotangent.lean:605:      = varietyDim (canonicalCoord d '' orbitRankLocus M) := by
./route-choice-answer.md:1078:./DLNFibre/Core/OrbitTangentCotangent.lean:635:/-! ## The A6.1 headline — `finrank (range δ⁰) ≤ varietyDim Z_M` -/
./route-choice-answer.md:1079:./DLNFibre/Core/OrbitTangentCotangent.lean:637:/-- **A6.1 (the reverse inequality).** `finrank k (range δ⁰) ≤ varietyDim Z_M`: the orbit tangent
./route-choice-answer.md:1080:./DLNFibre/Core/OrbitTangentCotangent.lean:641:theorem finrank_range_deformationδ_le_varietyDim [IsAlgClosed k] (M : Tuple (k := k) d) :
./route-choice-answer.md:1081:./DLNFibre/Core/OrbitTangentCotangent.lean:643:      ≤ varietyDim (canonicalCoord d '' orbitRankLocus M) := by
./route-choice-answer.md:1082:./DLNFibre/Core/OrbitTangentCotangent.lean:644:  rw [← finrank_cotangent_eq_varietyDim M]
./route-choice-answer.md:1083:./DLNFibre/Core/RouteCAssembly.lean:17:identity `varietyDim Σ^r = δ + varietyDim F` (`hSweep`) — and the Cited closure/density bridge
./route-choice-answer.md:1084:./DLNFibre/Core/RouteCAssembly.lean:18:`varietyDim Σ^r = varietyDim Σ̄^r` (`hClosure`, Lehalleur–Rimányi 4.4/4.5) are carried as **explicit
./route-choice-answer.md:1085:./DLNFibre/Core/RouteCAssembly.lean:20:relations `codimRepCanonical Z + varietyDim Z = card` are carried as named hypotheses
./route-choice-answer.md:1086:./DLNFibre/Core/RouteCAssembly.lean:50:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./route-choice-answer.md:1087:./DLNFibre/Core/RouteCAssembly.lean:52:          + varietyDim (canonicalCoord d '' fibre d B))
./route-choice-answer.md:1088:./DLNFibre/Core/RouteCAssembly.lean:53:    (hClosure : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./route-choice-answer.md:1089:./DLNFibre/Core/RouteCAssembly.lean:54:        = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r))
./route-choice-answer.md:1090:./DLNFibre/Core/RouteCAssembly.lean:56:        + varietyDim (canonicalCoord d '' fibre d B) = (Nat.card (RepCoord d) : ℕ∞))
./route-choice-answer.md:1092:./DLNFibre/Core/RouteCAssembly.lean:58:        + varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
./route-choice-answer.md:1095:./DLNFibre/Core/RouteCAssembly.lean:67:  have hdimSigma : varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
./route-choice-answer.md:1096:./DLNFibre/Core/RouteCAssembly.lean:69:        + varietyDim (canonicalCoord d '' fibre d B) := by
./route-choice-answer.md:1097:./DLNFibre/Core/RouteCAssembly.lean:72:  have hdimF_ne : varietyDim (canonicalCoord d '' fibre d B) ≠ ⊤ := by
./route-choice-answer.md:1098:./DLNFibre/Core/RouteCAssembly.lean:79:  have key : varietyDim (canonicalCoord d '' fibre d B) + codimRepCanonical (fibre d B)
./route-choice-answer.md:1099:./DLNFibre/Core/RouteCAssembly.lean:80:      = varietyDim (canonicalCoord d '' fibre d B)
./route-choice-answer.md:1100:./DLNFibre/Core/RouteCAssembly.lean:82:    calc varietyDim (canonicalCoord d '' fibre d B) + codimRepCanonical (fibre d B)
./route-choice-answer.md:1101:./DLNFibre/Core/RouteCAssembly.lean:83:        = codimRepCanonical (fibre d B) + varietyDim (canonicalCoord d '' fibre d B) := by
./route-choice-answer.md:1102:./DLNFibre/Core/RouteCAssembly.lean:88:              + varietyDim (canonicalCoord d '' fibre d B)) := hCatSigma.symm
./route-choice-answer.md:1103:./DLNFibre/Core/RouteCAssembly.lean:89:      _ = varietyDim (canonicalCoord d '' fibre d B)
./route-choice-answer.md:1104:./DLNFibre/Core/RouteCAssembly.lean:100:`codimRepCanonical_add_varietyDim_eq_card_of_nonempty` (`Core.RadicalCatenary`), given that the
./route-choice-answer.md:1106:./DLNFibre/Core/RouteCAssembly.lean:107:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./route-choice-answer.md:1107:./DLNFibre/Core/RouteCAssembly.lean:109:          + varietyDim (canonicalCoord d '' fibre d B))
./route-choice-answer.md:1108:./DLNFibre/Core/RouteCAssembly.lean:110:    (hClosure : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./route-choice-answer.md:1109:./DLNFibre/Core/RouteCAssembly.lean:111:        = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)) :
./route-choice-answer.md:1110:./DLNFibre/Core/RouteCAssembly.lean:115:    (codimRepCanonical_add_varietyDim_eq_card_of_nonempty hFne)
./route-choice-answer.md:1111:./DLNFibre/Core/RouteCAssembly.lean:116:    (codimRepCanonical_add_varietyDim_eq_card_of_nonempty hSigmaNe)
./route-choice-answer.md:1165:/-! ## The base-stratum Krull dimension brick: `ringKrullDim O(Mat^{≤r}) = δ`
./route-choice-answer.md:1172:`varietyDim = δ`, lifting the `unbotD 0` to the genuine `WithBot ℕ∞` value (the quotient is
./route-choice-answer.md:1173:nontrivial, so `ringKrullDim ≠ ⊥`). -/
./route-choice-answer.md:1175:/-- **The base-stratum Krull dimension** `ringKrullDim O(Mat^{≤r}) = δ`. For `r ≤ n`, `r ≤ m`, over an
./route-choice-answer.md:1178:The thermometer `varietyDim_productRankLocusLE_stratum` gives the `ℕ∞`-via-`unbotD` value; this lifts
./route-choice-answer.md:1180:is a nontrivial domain, so `ringKrullDim ≠ ⊥`). -/
./route-choice-answer.md:1181:theorem ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta [IsAlgClosed k] [CharZero k]
./route-choice-answer.md:1183:    ringKrullDim (MvPolynomial (RepCoord (dStratum n m)) k ⧸
./route-choice-answer.md:1191:  -- the thermometer: `varietyDim = δ`, i.e. `(ringKrullDim (R ⧸ I)).unbotD 0 = δ`.
./route-choice-answer.md:1192:  have hvd : varietyDim (canonicalCoord (dStratum n m) ''
./route-choice-answer.md:1194:    varietyDim_productRankLocusLE_stratum n m r hn hm
./route-choice-answer.md:1195:  rw [varietyDim, ← hI] at hvd
./route-choice-answer.md:1196:  -- the quotient is a nontrivial domain, so `ringKrullDim ≠ ⊥`.
./route-choice-answer.md:1199:  have hne : ringKrullDim (MvPolynomial (RepCoord (dStratum n m)) k ⧸ I) ≠ ⊥ :=
./route-choice-answer.md:1201:      ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (RepCoord (dStratum n m)) k ⧸ I)
./route-choice-answer.md:1209:By equidimensionality at a closed point (`OrbitTangentCotangent.height_eq_ringKrullDim_of_isMaximal_fintype`,
./route-choice-answer.md:1217:irreducible determinantal base, with `ringKrullDim O(Mat^{≤r}) = δ`. -/
./route-choice-answer.md:1228:  rw [height_eq_ringKrullDim_of_isMaximal_fintype,
./route-choice-answer.md:1229:    ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta n m r hn hm]
./route-choice-answer.md:1233:`affine_domain_height_add_ringKrullDim_quotient_eq` is over `MvPolynomial (Fin n) k`. Transport it to
./route-choice-answer.md:1235:`height_eq_ringKrullDim_of_isMaximal_fintype` does for the maximal corollary. This is the engine the
./route-choice-answer.md:1241:`height p + ringKrullDim (A ⧸ p) = ringKrullDim A`. Transports
./route-choice-answer.md:1242:`affine_domain_height_add_ringKrullDim_quotient_eq` through `renameEquiv` and the induced quotient
./route-choice-answer.md:1244:theorem affine_domain_height_add_ringKrullDim_quotient_eq_fintype {σ : Type*} [Finite σ]
./route-choice-answer.md:1246:    (p.height : WithBot ℕ∞) + ringKrullDim ((MvPolynomial σ k ⧸ I) ⧸ p)
./route-choice-answer.md:1247:      = ringKrullDim (MvPolynomial σ k ⧸ I) := by
./route-choice-answer.md:1260:  have hL := affine_domain_height_add_ringKrullDim_quotient_eq k (Fintype.card σ) J p'
./route-choice-answer.md:1263:    ringKrullDim_quotient_map_algEquiv Φ p, hJ, ringKrullDim_quotient_map_algEquiv e I] at hL
./route-choice-answer.md:1303:/-- LANDED: the determinantal-stratum dimension `varietyDim (Mat^{≤r}) = r(n+m−r) = δ`. -/
./route-choice-answer.md:1305:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./route-choice-answer.md:1307:  varietyDim_productRankLocusLE_stratum n m r hn hm
./route-choice-answer.md:1321:/-- LANDED: the catenary closer (PRIMALITY-gated) — `codim Z = card − varietyDim Z`. -/
./route-choice-answer.md:1325:    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
./route-choice-answer.md:1326:  codimRepCanonical_eq_card_sub_varietyDim Z hp
./route-choice-answer.md:1331:    (p.height : WithBot ℕ∞) + ringKrullDim (((MvPolynomial (Fin n) k) ⧸ I) ⧸ p)
./route-choice-answer.md:1332:      = ringKrullDim ((MvPolynomial (Fin n) k) ⧸ I) :=
./route-choice-answer.md:1333:  affine_domain_height_add_ringKrullDim_quotient_eq k n I p
./route-choice-answer.md:1338:    (m.height : WithBot ℕ∞) = ringKrullDim ((MvPolynomial (Fin n) k) ⧸ I) :=
./route-choice-answer.md:1339:  height_eq_ringKrullDim_of_isMaximal k n I m
./route-choice-answer.md:1359:/-! ## Candidate: the base ringKrullDim = δ (the brick the going-down/00OM route consumes)

codex
The workspace already has prior prompt/answer notes, but I’m not going to trust those as authoritative. I’m now checking the actual Lean sources and the vendored/pinned Mathlib API for the dimension and radical lemmas.
exec
/bin/bash -lc 'ls -la' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
total 1120
drwxrwxr-x 2 ubuntu ubuntu    4096 Jun 24 17:42 .
drwxrwxr-x 3 ubuntu ubuntu    4096 Jun 24 17:37 ..
-rw-rw-r-- 1 ubuntu ubuntu   49640 Jun 24 17:43 noncirc-setlevel-answer.md
-rw-rw-r-- 1 ubuntu ubuntu    5060 Jun 24 17:42 noncirc-setlevel-prompt.md
-rw-rw-r-- 1 ubuntu ubuntu 1066445 Jun 24 17:35 route-choice-answer.md
-rw-rw-r-- 1 ubuntu ubuntu    6557 Jun 24 17:32 route-choice-prompt.md

exec
/bin/bash -lc 'find .. -maxdepth 5 -name lake-manifest.json -o -name lakefile.lean -o -name lean-toolchain -o -name Mathlib | head -100' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
exec
/bin/bash -lc "sed -n '1,240p' DLNFibre/Core/NullstellensatzCodim.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 exited 2 in 0ms:
sed: can't read DLNFibre/Core/NullstellensatzCodim.lean: No such file or directory

exec
/bin/bash -lc "sed -n '1,220p' CLAUDE.md" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 exited 2 in 0ms:
sed: can't read CLAUDE.md: No such file or directory

codex
This thread directory only contains the consult notes, not the Lean project checkout. I’ll use the existing notes as context, but for lemma names I need to verify against Mathlib source rather than infer from memory.
exec
/bin/bash -lc "sed -n '1,220p' noncirc-setlevel-answer.md" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
   Updating ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (HEAD)
    Updated ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (fa7351f6ef4773f536ee4975c3251325eb9c44df)
Reading prompt from stdin...
OpenAI Codex v0.142.0
--------
workdir: /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
model: gpt-5.5
provider: openai-aisi
approval: untrusted
sandbox: read-only
reasoning effort: high
reasoning summaries: none
session id: 019efaba-6d04-7331-bc41-0b1525b303af
--------
user
# Codex consult — does the SET-LEVEL chart trivialization dodge the R2-3b-4 reducedness circularity?

Lean 4 + Mathlib v4.29. I am building route (c) for the relative-fibre-dimension identity
`hSweep : varietyDim Σ^r = δ + varietyDim F`. Rung 1 = a single-chart trivialization. The DECISIVE
de-risk: is the SET-LEVEL / `varietyDim` version non-circular, given a PRIOR attempt (R2-3b-4) at a
SCHEME-level iso was circular?

## The prior circularity (R2-3b-4), precisely

Earlier the team tried to prove the fibre `F_E` is REDUCED by building a *scheme/ring* product iso
`e : S ≃ₐ[k] R ⊗_k F_E` (S = O(Σ̄^r ∩ pivot chart), R = O(base chart)), then descending reducedness
`S reduced ⟹ R⊗F_E reduced ⟹ F_E reduced`. This was CIRCULAR for reducedness: the forward map of `e`
needs the ideal inclusion `sigmaIdeal ≤ ker(comorphism)`, but only `sigmaIdeal ≤ radical(ker)` is
available — establishing the strict inclusion (= reducedness of the cut) is what `e` was meant to
prove. So `e` as a *ring iso proving reducedness* re-enters its own hypothesis.

Independently known (NOT circular): `deepBaseComap_sigmaIdeal_le` — the base `sigmaIdeal` maps INTO
the deep `sigmaIdeal` (a containment, proved by a point-chase `mult`-image argument), does NOT assume
the circular inclusion.

## My claim: the dimension version dodges it (need you to confirm or break)

For `hSweep` I do NOT need reducedness. `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`
and `vanishingIdeal Z` is ALREADY radical (it's a vanishing ideal). Krull dim is RADICAL-INSENSITIVE:
`ringKrullDim (R⧸I) = ringKrullDim (R⧸√I)`. So `varietyDim` reads only the REDUCED/variety structure;
I never need to know whether the *generator* ideal `fibreGenIdeal` equals its radical. The chart
trivialization I need is a **variety-level (set-level, reduced) isomorphism** `mult⁻¹(U) ∩ Σ^r ≅ U × F`,
not a scheme iso of (possibly non-reduced) coordinate rings.

The set-level pieces LANDED: the sweep `Σ^r = ⋃_P (P•·)''F` (`H = GL×GL` acts, `mult` equivariant,
all rank-r matrices `H`-equivalent); the gauge coordinate-change `AlgEquiv` `nEquiv d P` on the
polynomial ring (transports `multPoly`); the comorphism `multComap`.

## Questions (be adversarial — this is make-or-break)

1. **Is `varietyDim` genuinely radical-insensitive in Mathlib v4.29** — i.e. is `ringKrullDim (R⧸I) =
   ringKrullDim (R⧸ I.radical)` available (or `ringKrullDim` factors through `√`)? Name the lemma if
   so. This is the linchpin: if true, the dimension route NEVER touches the reducedness question.

2. **Does constructing the SET-LEVEL chart bijection `mult⁻¹(U) ∩ Σ^r ≅ U × F` re-enter the
   circularity?** The map is: on the pivot chart `U`, gauge-normalize the target to `E` (algebraic
   row/col ops, the `H`-action), giving `A ∈ mult⁻¹(B) ↦ (B, P_B • A) ∈ U × F` where `P_B` is the
   chart's normalizing gauge. This is a bijection of SETS / a `varietyDim`-preserving map. Does
   proving it require the radical inclusion (`sigmaIdeal ≤ ker`), or only: (i) the sweep set-identity
   (LANDED, non-circular), (ii) the gauge being an algebraic iso on the chart open (LANDED `nEquiv`),
   (iii) `mult ∘ gauge = const E` on the fibre (LANDED `nSub_mult`)? My read: it needs only set-level
   + gauge-algebraic facts, all radical-insensitive — but tell me if the dimension-additivity
   `varietyDim(U×F) = varietyDim U + varietyDim F` secretly needs flatness/reducedness.

3. **The product-dimension step `varietyDim(U × F) = varietyDim U + varietyDim F`.** For a product of
   affine varieties over an alg-closed field, `dim(X × Y) = dim X + dim Y`. Is this in Mathlib v4.29
   (as `ringKrullDim (A ⊗_k B) = ringKrullDim A + ringKrullDim B`, or a variety-dimension product)?
   If absent, is it provable WITHOUT the relative-Noether/`proof_wanted` machinery — e.g. via `trdeg`
   of the tensor product (trdeg IS additive for the tensor of two domains over a field) PLUS the
   reducible-case max-over-components bookkeeping? Note `F` is REDUCIBLE (comps 10,9,9 on (3,3,3)r1) —
   does the product-dim survive reducibility radical-insensitively (take max component on each side)?

4. **The glue over the finite pivot cover.** `varietyDim(⋃_i Z_i) = max_i varietyDim(Z_i)` for a
   finite cover — is that radical-insensitive and in Mathlib (or trivial from `ringKrullDim` of a
   product/finite-union of irreducibles)?

5. **Net verdict:** does the SET-LEVEL/`varietyDim` route (c) dodge the R2-3b-4 circularity? If YES,
   give the rung decomposition (single-chart triv → per-chart dim-additivity → glue) and which steps
   are Mathlib-present vs new. If NO (the set-level chart iso ALSO needs the radical inclusion or some
   reducedness), say so plainly — that triggers a fallback to citing `hSweep`.

The key thing I need from you: a clean YES/NO on whether radical-insensitivity of `varietyDim` lets
the chart trivialization avoid the `sigmaIdeal ≤ ker` inclusion that made the scheme iso circular.

codex
I’ll check the local workspace first, especially the pinned Mathlib sources and existing definitions, because the exact lemma names and available dimension API matter here.
exec
/bin/bash -lc "pwd && rg --files -g 'lake-manifest.json' -g 'lakefile.*' -g 'lean-toolchain' -g 'CLAUDE.md' -g 'README.md' -g '*.lean' | head -200" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex

exec
/bin/bash -lc "rg -n \"varietyDim|ringKrullDim|radical|IsJacobson|KrullDim|tensor|TensorProduct\" . -g '*.lean' -g '*.md' | head -300" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
./route-choice-prompt.md:10:varietyDim (Σ^r)  =  δ  +  varietyDim F
./route-choice-prompt.md:13:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./route-choice-prompt.md:18:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./route-choice-prompt.md:28:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./route-choice-prompt.md:29:   ringKrullDim (R ⧸ ker(pullback)) = ringKrullDim((pullback).range) = trdeg_k(range)` for a
./route-choice-prompt.md:31:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./route-choice-prompt.md:52:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./route-choice-prompt.md:60:max component, i.e. `ringKrullDim`)? Is `ringKrullDim`-additivity over a sweep even true without
./route-choice-prompt.md:73:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./route-choice-prompt.md:75:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./noncirc-setlevel-prompt.md:4:`hSweep : varietyDim Σ^r = δ + varietyDim F`. Rung 1 = a single-chart trivialization. The DECISIVE
./noncirc-setlevel-prompt.md:5:de-risk: is the SET-LEVEL / `varietyDim` version non-circular, given a PRIOR attempt (R2-3b-4) at a
./noncirc-setlevel-prompt.md:13:needs the ideal inclusion `sigmaIdeal ≤ ker(comorphism)`, but only `sigmaIdeal ≤ radical(ker)` is
./noncirc-setlevel-prompt.md:23:For `hSweep` I do NOT need reducedness. `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`
./noncirc-setlevel-prompt.md:24:and `vanishingIdeal Z` is ALREADY radical (it's a vanishing ideal). Krull dim is RADICAL-INSENSITIVE:
./noncirc-setlevel-prompt.md:25:`ringKrullDim (R⧸I) = ringKrullDim (R⧸√I)`. So `varietyDim` reads only the REDUCED/variety structure;
./noncirc-setlevel-prompt.md:26:I never need to know whether the *generator* ideal `fibreGenIdeal` equals its radical. The chart
./noncirc-setlevel-prompt.md:36:1. **Is `varietyDim` genuinely radical-insensitive in Mathlib v4.29** — i.e. is `ringKrullDim (R⧸I) =
./noncirc-setlevel-prompt.md:37:   ringKrullDim (R⧸ I.radical)` available (or `ringKrullDim` factors through `√`)? Name the lemma if
./noncirc-setlevel-prompt.md:43:   chart's normalizing gauge. This is a bijection of SETS / a `varietyDim`-preserving map. Does
./noncirc-setlevel-prompt.md:44:   proving it require the radical inclusion (`sigmaIdeal ≤ ker`), or only: (i) the sweep set-identity
./noncirc-setlevel-prompt.md:47:   + gauge-algebraic facts, all radical-insensitive — but tell me if the dimension-additivity
./noncirc-setlevel-prompt.md:48:   `varietyDim(U×F) = varietyDim U + varietyDim F` secretly needs flatness/reducedness.
./noncirc-setlevel-prompt.md:50:3. **The product-dimension step `varietyDim(U × F) = varietyDim U + varietyDim F`.** For a product of
./noncirc-setlevel-prompt.md:52:   (as `ringKrullDim (A ⊗_k B) = ringKrullDim A + ringKrullDim B`, or a variety-dimension product)?
./noncirc-setlevel-prompt.md:54:   of the tensor product (trdeg IS additive for the tensor of two domains over a field) PLUS the
./noncirc-setlevel-prompt.md:56:   does the product-dim survive reducibility radical-insensitively (take max component on each side)?
./noncirc-setlevel-prompt.md:58:4. **The glue over the finite pivot cover.** `varietyDim(⋃_i Z_i) = max_i varietyDim(Z_i)` for a
./noncirc-setlevel-prompt.md:59:   finite cover — is that radical-insensitive and in Mathlib (or trivial from `ringKrullDim` of a
./noncirc-setlevel-prompt.md:62:5. **Net verdict:** does the SET-LEVEL/`varietyDim` route (c) dodge the R2-3b-4 circularity? If YES,
./noncirc-setlevel-prompt.md:64:   are Mathlib-present vs new. If NO (the set-level chart iso ALSO needs the radical inclusion or some
./noncirc-setlevel-prompt.md:67:The key thing I need from you: a clean YES/NO on whether radical-insensitivity of `varietyDim` lets
./noncirc-setlevel-answer.md:19:`hSweep : varietyDim Σ^r = δ + varietyDim F`. Rung 1 = a single-chart trivialization. The DECISIVE
./noncirc-setlevel-answer.md:20:de-risk: is the SET-LEVEL / `varietyDim` version non-circular, given a PRIOR attempt (R2-3b-4) at a
./noncirc-setlevel-answer.md:28:needs the ideal inclusion `sigmaIdeal ≤ ker(comorphism)`, but only `sigmaIdeal ≤ radical(ker)` is
./noncirc-setlevel-answer.md:38:For `hSweep` I do NOT need reducedness. `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`
./noncirc-setlevel-answer.md:39:and `vanishingIdeal Z` is ALREADY radical (it's a vanishing ideal). Krull dim is RADICAL-INSENSITIVE:
./noncirc-setlevel-answer.md:40:`ringKrullDim (R⧸I) = ringKrullDim (R⧸√I)`. So `varietyDim` reads only the REDUCED/variety structure;
./noncirc-setlevel-answer.md:41:I never need to know whether the *generator* ideal `fibreGenIdeal` equals its radical. The chart
./noncirc-setlevel-answer.md:51:1. **Is `varietyDim` genuinely radical-insensitive in Mathlib v4.29** — i.e. is `ringKrullDim (R⧸I) =
./noncirc-setlevel-answer.md:52:   ringKrullDim (R⧸ I.radical)` available (or `ringKrullDim` factors through `√`)? Name the lemma if
./noncirc-setlevel-answer.md:58:   chart's normalizing gauge. This is a bijection of SETS / a `varietyDim`-preserving map. Does
./noncirc-setlevel-answer.md:59:   proving it require the radical inclusion (`sigmaIdeal ≤ ker`), or only: (i) the sweep set-identity
./noncirc-setlevel-answer.md:62:   + gauge-algebraic facts, all radical-insensitive — but tell me if the dimension-additivity
./noncirc-setlevel-answer.md:63:   `varietyDim(U×F) = varietyDim U + varietyDim F` secretly needs flatness/reducedness.
./noncirc-setlevel-answer.md:65:3. **The product-dimension step `varietyDim(U × F) = varietyDim U + varietyDim F`.** For a product of
./noncirc-setlevel-answer.md:67:   (as `ringKrullDim (A ⊗_k B) = ringKrullDim A + ringKrullDim B`, or a variety-dimension product)?
./noncirc-setlevel-answer.md:69:   of the tensor product (trdeg IS additive for the tensor of two domains over a field) PLUS the
./noncirc-setlevel-answer.md:71:   does the product-dim survive reducibility radical-insensitively (take max component on each side)?
./noncirc-setlevel-answer.md:73:4. **The glue over the finite pivot cover.** `varietyDim(⋃_i Z_i) = max_i varietyDim(Z_i)` for a
./noncirc-setlevel-answer.md:74:   finite cover — is that radical-insensitive and in Mathlib (or trivial from `ringKrullDim` of a
./noncirc-setlevel-answer.md:77:5. **Net verdict:** does the SET-LEVEL/`varietyDim` route (c) dodge the R2-3b-4 circularity? If YES,
./noncirc-setlevel-answer.md:79:   are Mathlib-present vs new. If NO (the set-level chart iso ALSO needs the radical inclusion or some
./noncirc-setlevel-answer.md:82:The key thing I need from you: a clean YES/NO on whether radical-insensitivity of `varietyDim` lets
./route-choice-answer.md:25:varietyDim (Σ^r)  =  δ  +  varietyDim F
./route-choice-answer.md:28:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./route-choice-answer.md:33:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./route-choice-answer.md:43:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./route-choice-answer.md:44:   ringKrullDim (R ⧸ ker(pullback)) = ringKrullDim((pullback).range) = trdeg_k(range)` for a
./route-choice-answer.md:46:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./route-choice-answer.md:67:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./route-choice-answer.md:75:max component, i.e. `ringKrullDim`)? Is `ringKrullDim`-additivity over a sweep even true without
./route-choice-answer.md:88:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./route-choice-answer.md:90:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./route-choice-answer.md:114:./route-choice-prompt.md:31:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./route-choice-answer.md:129:./route-choice-answer.md:46:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./route-choice-answer.md:188:varietyDim (Σ^r)  =  δ  +  varietyDim F
./route-choice-answer.md:191:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./route-choice-answer.md:196:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./route-choice-answer.md:206:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./route-choice-answer.md:207:   ringKrullDim (R ⧸ ker(pullback)) = ringKrullDim((pullback).range) = trdeg_k(range)` for a
./route-choice-answer.md:209:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./route-choice-answer.md:230:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./route-choice-answer.md:238:max component, i.e. `ringKrullDim`)? Is `ringKrullDim`-additivity over a sweep even true without
./route-choice-answer.md:251:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./route-choice-answer.md:253:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./route-choice-answer.md:277:./route-choice-prompt.md:31:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./route-choice-answer.md:292:./route-choice-answer.md:46:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./route-choice-answer.md:325:/bin/bash -lc 'rg -n "Noether.*Norm|Noetherian.*Norm|normalization|GenericFreeness|generic freeness|height_eq_under|FlatQuasiFinite|HasGoingDown|trdeg_add_eq|rankLocus|productRankLocus|varietyDim|vanishingIdeal" -S .' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean
./route-choice-answer.md:450:./DLNFibre.lean:160:-- `codimRepCanonical Z + varietyDim Z = card` for nonempty Z. Discharges the catenary hyps of RouteCAssembly.
./route-choice-answer.md:466:./DLNFibre/Core/OrbitPullbackDim.lean:6:# `DLNFibre.Core.OrbitPullbackDim` — route-c setup: `varietyDim(Z_M) = ringKrullDim((μ_M^*).range)`
./route-choice-answer.md:467:./DLNFibre/Core/OrbitPullbackDim.lean:16:1. **Ideal identification.** `varietyDim Z_M = ringKrullDim (MvPolynomial (RepCoord d) k ⧸
./route-choice-answer.md:468:./DLNFibre/Core/OrbitPullbackDim.lean:17:   ker μ_M^*)`, immediate from the `varietyDim` definition, the Abeasis–Del Fra ideal equality L6.4
./route-choice-answer.md:471:./DLNFibre/Core/OrbitPullbackDim.lean:25:The headline `varietyDim_eq_ringKrullDim_range_orbitPullback` hands A4 a finitely-generated domain
./route-choice-answer.md:472:./DLNFibre/Core/OrbitPullbackDim.lean:48:`MvPolynomial (RepCoord d) k ⧸ ker μ_M^*`. `varietyDim` definition, then L6.4
./route-choice-answer.md:475:./DLNFibre/Core/OrbitPullbackDim.lean:52:theorem varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker [Infinite k]
./route-choice-answer.md:476:./DLNFibre/Core/OrbitPullbackDim.lean:54:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./route-choice-answer.md:477:./DLNFibre/Core/OrbitPullbackDim.lean:57:  rw [varietyDim, vanishingIdeal_orbitRankLocus_eq_orbitSet M, ← range_orbitMap,
./route-choice-answer.md:479:./DLNFibre/Core/OrbitPullbackDim.lean:70:transcendence degree. Combines `varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker` with the
./route-choice-answer.md:480:./DLNFibre/Core/OrbitPullbackDim.lean:74:theorem varietyDim_eq_ringKrullDim_range_orbitPullback [Infinite k] {d : Fin (N + 1) → ℕ}
./route-choice-answer.md:481:./DLNFibre/Core/OrbitPullbackDim.lean:76:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./route-choice-answer.md:482:./DLNFibre/Core/OrbitPullbackDim.lean:78:  rw [varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker M,
./route-choice-answer.md:483:./DLNFibre/Core/OrbitPullbackDim.lean:89:/-- The headline at the concrete `(2,2,2)/ℚ` tuple: `varietyDim (canonicalCoord '' orbitRankLocus
./route-choice-answer.md:484:./DLNFibre/Core/OrbitPullbackDim.lean:93:    varietyDim (canonicalCoord dWitness '' orbitRankLocus tupleWitnessQ)
./route-choice-answer.md:485:./DLNFibre/Core/OrbitPullbackDim.lean:95:  varietyDim_eq_ringKrullDim_range_orbitPullback tupleWitnessQ
./route-choice-answer.md:506:./DLNFibre/Core/DeterminantalStratumDim.lean:29:4. **The catenary bridge** (LANDED `codimRep_add_varietyDim_eq_card`): `codim + dim = card = m·n`,
./route-choice-answer.md:520:./DLNFibre/Core/DeterminantalStratumDim.lean:224:> `varietyDim (Mat^{rk ≤ r}_{m × n}) = r · (n + m − r)`.
./route-choice-answer.md:521:./DLNFibre/Core/DeterminantalStratumDim.lean:229:theorem varietyDim_productRankLocusLE_stratum [IsAlgClosed k] [CharZero k] (n m r : ℕ)
./route-choice-answer.md:522:./DLNFibre/Core/DeterminantalStratumDim.lean:231:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./route-choice-answer.md:524:./DLNFibre/Core/DeterminantalStratumDim.lean:237:  have hbridge := codimRep_add_varietyDim_eq_card (canonicalCoord (dStratum n m)) Z
./route-choice-answer.md:527:./DLNFibre/Core/DeterminantalStratumDim.lean:249:  -- `hbridge : (n−r)(m−r) + varietyDim Z = m·n`
./route-choice-answer.md:528:./DLNFibre/Core/DeterminantalStratumDim.lean:258:  have heq : (((n - r) * (m - r) : ℕ) : ℕ∞) + varietyDim (canonicalCoord (dStratum n m) '' Z)
./route-choice-answer.md:529:./DLNFibre/Core/DeterminantalStratumDim.lean:268:    varietyDim (canonicalCoord (dStratum 2 2) '' productRankLocusLE (k := k) (dStratum 2 2) 1)
./route-choice-answer.md:530:./DLNFibre/Core/DeterminantalStratumDim.lean:270:  have h := varietyDim_productRankLocusLE_stratum (k := k) 2 2 1 (by norm_num) (by norm_num)
./route-choice-answer.md:546:./DLNFibre/Core/DeepChartRing.lean:133:`sigmaIdeal` is radical (`vanishingIdeal_isRadical`, over `[IsAlgClosed k]`) and localization
./route-choice-answer.md:577:./DLNFibre/Core/FibreDimFibration.lean:45:`varietyDim = δ`, lifting the `unbotD 0` to the genuine `WithBot ℕ∞` value (the quotient is
./route-choice-answer.md:578:./DLNFibre/Core/FibreDimFibration.lean:51:The thermometer `varietyDim_productRankLocusLE_stratum` gives the `ℕ∞`-via-`unbotD` value; this lifts
./route-choice-answer.md:579:./DLNFibre/Core/FibreDimFibration.lean:54:theorem ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta [IsAlgClosed k] [CharZero k]
./route-choice-answer.md:585:./DLNFibre/Core/FibreDimFibration.lean:64:  -- the thermometer: `varietyDim = δ`, i.e. `(ringKrullDim (R ⧸ I)).unbotD 0 = δ`.
./route-choice-answer.md:586:./DLNFibre/Core/FibreDimFibration.lean:65:  have hvd : varietyDim (canonicalCoord (dStratum n m) ''
./route-choice-answer.md:588:./DLNFibre/Core/FibreDimFibration.lean:67:    varietyDim_productRankLocusLE_stratum n m r hn hm
./route-choice-answer.md:589:./DLNFibre/Core/FibreDimFibration.lean:68:  rw [varietyDim, ← hI] at hvd
./route-choice-answer.md:597:./DLNFibre/Core/FibreDimFibration.lean:102:    ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta n m r hn hm]
./route-choice-answer.md:605:./DLNFibre/Core/EndBaseChangeSweep.lean:16:consequence** `varietyDim (productRankLocus d r) = δ + varietyDim (fibre d E)` is the *one genuinely
./route-choice-answer.md:637:./DLNFibre/Core/FibreHeightDirect.lean:11:`fibreGenIdeal d B` (`Core.MultComorphism.vanishingIdeal_image_fibre_eq_radical`). The point of this
./route-choice-answer.md:639:./DLNFibre/Core/FibreHeightDirect.lean:47:(definition of `codimRepCanonical`/`codimRep`); `vanishingIdeal (…) = (fibreGenIdeal d B).radical`
./route-choice-answer.md:640:./DLNFibre/Core/FibreHeightDirect.lean:48:(`vanishingIdeal_image_fibre_eq_radical`, the Nullstellensatz); `(radical I).height = I.height`
./route-choice-answer.md:641:./DLNFibre/Core/FibreHeightDirect.lean:54:  rw [codimRepCanonical, codimRep, vanishingIdeal_image_fibre_eq_radical, Ideal.height_radical]
./route-choice-answer.md:643:./DLNFibre/Core/NullstellensatzCodim.lean:20:   Nullstellensatz over `[IsAlgClosed k]`): `vanishingIdeal Z` is always **radical**
./route-choice-answer.md:649:./DLNFibre/Core/NullstellensatzCodim.lean:31:   irreducible"), `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ` (`ℕ∞`, additive — `ℕ∞`
./route-choice-answer.md:650:./DLNFibre/Core/NullstellensatzCodim.lean:37:`axiom`. `varietyDim Z = ringKrullDim (R ⧸ vanishingIdeal Z)` is the Krull dimension of the
./route-choice-answer.md:652:./DLNFibre/Core/NullstellensatzCodim.lean:67:strong Nullstellensatz it equals its own radical, via `vanishingIdeal Z = vanishingIdeal (zeroLocus
./route-choice-answer.md:653:./DLNFibre/Core/NullstellensatzCodim.lean:68:(vanishingIdeal Z))` `= (vanishingIdeal Z).radical`. -/
./route-choice-answer.md:656:./DLNFibre/Core/NullstellensatzCodim.lean:71:  have h : vanishingIdeal k Z = (vanishingIdeal k Z).radical := by
./route-choice-answer.md:658:./DLNFibre/Core/NullstellensatzCodim.lean:74:        vanishingIdeal_zeroLocus_eq_radical (K := k)]
./route-choice-answer.md:664:./DLNFibre/Core/NullstellensatzCodim.lean:87:Nullstellensatz forces `vanishingIdeal (zeroLocus (vanishingIdeal Z)) = (vanishingIdeal Z).radical`,

exec
/bin/bash -lc 'rg -n "ringKrullDim_quotient|quotient.*radical|radical.*quotient|height_radical|prod|union|TensorProduct|trdeg_add|dimension" noncirc-setlevel-answer.md route-choice-answer.md | head -300' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
route-choice-answer.md:16:# Codex consult — route choice for the relative-fibre-dimension rung (Lean 4 / Mathlib v4.29)
route-choice-answer.md:18:I am formalising one dimension identity in Lean 4 + Mathlib v4.29 (a research engine for the geometry
route-choice-answer.md:30:- `Σ^r = productRankLocus d r = {A : rank(mult A) = r}` — the EXACT-rank locus (tuples of composable
route-choice-answer.md:31:  matrices whose product has rank exactly `r`).
route-choice-answer.md:39:   fibre). PROVED: `productRankLocus_eq_iUnion_smul_fibre`.
route-choice-answer.md:46:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
route-choice-answer.md:60:The chart map `R = O(Mat^{=r}) → S = O(Σ^r)` has POSITIVE relative dimension (`dim F = card−C−δ >
route-choice-answer.md:69:trdeg_{Frac O(Mat^{=r})} Frac O(Σ^r)` (tower additivity `trdeg_add_eq`), and the relative trdeg
route-choice-answer.md:91:2. Route (a): is "`dim(H·F) = dim(H·E) + dim F`" (sweep/orbit-dimension additivity) provable from
route-choice-answer.md:99:   `dim Σ^r = dim Mat^{=r} + dim F` is the bundle dimension formula — no generic flatness needed,
route-choice-answer.md:101:   Mathlib have homogeneous-space / principal-bundle dimension)? This feels like the real structure.
route-choice-answer.md:109:I’ll inspect the local Lean dependency surface first, especially whether Mathlib already has relative Noether normalization, generic flatness beyond finite modules, and the dimension/going-down bridge you mentioned. After that I’ll rank the routes against what is actually available in this worktree.
route-choice-answer.md:111:/bin/bash -lc 'rg -n "Noether( |ian)?[Nn]ormal|normalization|GenericFreeness|generic freeness|FlatQuasiFinite|height_eq_under|trdeg_add_eq|HasGoingDown|relative" -S .' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
route-choice-answer.md:113:./route-choice-prompt.md:1:# Codex consult — route choice for the relative-fibre-dimension rung (Lean 4 / Mathlib v4.29)
route-choice-answer.md:114:./route-choice-prompt.md:31:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
route-choice-answer.md:118:./route-choice-prompt.md:45:The chart map `R = O(Mat^{=r}) → S = O(Σ^r)` has POSITIVE relative dimension (`dim F = card−C−δ >
route-choice-answer.md:120:./route-choice-prompt.md:54:trdeg_{Frac O(Mat^{=r})} Frac O(Σ^r)` (tower additivity `trdeg_add_eq`), and the relative trdeg
route-choice-answer.md:128:./route-choice-answer.md:16:# Codex consult — route choice for the relative-fibre-dimension rung (Lean 4 / Mathlib v4.29)
route-choice-answer.md:129:./route-choice-answer.md:46:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
route-choice-answer.md:133:./route-choice-answer.md:60:The chart map `R = O(Mat^{=r}) → S = O(Σ^r)` has POSITIVE relative dimension (`dim F = card−C−δ >
route-choice-answer.md:135:./route-choice-answer.md:69:trdeg_{Frac O(Mat^{=r})} Frac O(Σ^r)` (tower additivity `trdeg_add_eq`), and the relative trdeg
route-choice-answer.md:142:./route-choice-answer.md:109:I’ll inspect the local Lean dependency surface first, especially whether Mathlib already has relative Noether normalization, generic flatness beyond finite modules, and the dimension/going-down bridge you mentioned. After that I’ll rank the routes against what is actually available in this worktree.
route-choice-answer.md:179:# Codex consult — route choice for the relative-fibre-dimension rung (Lean 4 / Mathlib v4.29)
route-choice-answer.md:181:I am formalising one dimension identity in Lean 4 + Mathlib v4.29 (a research engine for the geometry
route-choice-answer.md:193:- `Σ^r = productRankLocus d r = {A : rank(mult A) = r}` — the EXACT-rank locus (tuples of composable
route-choice-answer.md:194:  matrices whose product has rank exactly `r`).
route-choice-answer.md:202:   fibre). PROVED: `productRankLocus_eq_iUnion_smul_fibre`.
route-choice-answer.md:209:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
route-choice-answer.md:223:The chart map `R = O(Mat^{=r}) → S = O(Σ^r)` has POSITIVE relative dimension (`dim F = card−C−δ >
route-choice-answer.md:232:trdeg_{Frac O(Mat^{=r})} Frac O(Σ^r)` (tower additivity `trdeg_add_eq`), and the relative trdeg
route-choice-answer.md:254:2. Route (a): is "`dim(H·F) = dim(H·E) + dim F`" (sweep/orbit-dimension additivity) provable from
route-choice-answer.md:262:   `dim Σ^r = dim Mat^{=r} + dim F` is the bundle dimension formula — no generic flatness needed,
route-choice-answer.md:264:   Mathlib have homogeneous-space / principal-bundle dimension)? This feels like the real structure.
route-choice-answer.md:272:I’ll inspect the local Lean dependency surface first, especially whether Mathlib already has relative Noether normalization, generic flatness beyond finite modules, and the dimension/going-down bridge you mentioned. After that I’ll rank the routes against what is actually available in this worktree.
route-choice-answer.md:274:/bin/bash -lc 'rg -n "Noether( |ian)?[Nn]ormal|normalization|GenericFreeness|generic freeness|FlatQuasiFinite|height_eq_under|trdeg_add_eq|HasGoingDown|relative" -S .' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
route-choice-answer.md:276:./route-choice-prompt.md:1:# Codex consult — route choice for the relative-fibre-dimension rung (Lean 4 / Mathlib v4.29)
route-choice-answer.md:277:./route-choice-prompt.md:31:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
route-choice-answer.md:281:./route-choice-prompt.md:45:The chart map `R = O(Mat^{=r}) → S = O(Σ^r)` has POSITIVE relative dimension (`dim F = card−C−δ >
route-choice-answer.md:283:./route-choice-prompt.md:54:trdeg_{Frac O(Mat^{=r})} Frac O(Σ^r)` (tower additivity `trdeg_add_eq`), and the relative trdeg
route-choice-answer.md:291:./route-choice-answer.md:16:# Codex consult — route choice for the relative-fibre-dimension rung (Lean 4 / Mathlib v4.29)
route-choice-answer.md:292:./route-choice-answer.md:46:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
route-choice-answer.md:296:./route-choice-answer.md:60:The chart map `R = O(Mat^{=r}) → S = O(Σ^r)` has POSITIVE relative dimension (`dim F = card−C−δ >
route-choice-answer.md:298:./route-choice-answer.md:69:trdeg_{Frac O(Mat^{=r})} Frac O(Σ^r)` (tower additivity `trdeg_add_eq`), and the relative trdeg
route-choice-answer.md:305:./route-choice-answer.md:109:I’ll inspect the local Lean dependency surface first, especially whether Mathlib already has relative Noether normalization, generic flatness beyond finite modules, and the dimension/going-down bridge you mentioned. After that I’ll rank the routes against what is actually available in this worktree.
route-choice-answer.md:325:/bin/bash -lc 'rg -n "Noether.*Norm|Noetherian.*Norm|normalization|GenericFreeness|generic freeness|height_eq_under|FlatQuasiFinite|HasGoingDown|trdeg_add_eq|rankLocus|productRankLocus|varietyDim|vanishingIdeal" -S .' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean
route-choice-answer.md:447:./DLNFibre.lean:84:-- via the N=1 specialisation of the quiver engine (productRankLocusLE ![n,m] r = the determinantal variety).
route-choice-answer.md:449:./DLNFibre.lean:154:-- Route-c sweep structure (homogeneous sweep): `Σ^r = H·F` (`productRankLocus_eq_iUnion_smul_fibre`)
route-choice-answer.md:454:./DLNFibre/DLN/RlctPayoffGeneral.lean:15:  (`Core.SigmaCodim.codimRepCanonical_productRankLocusLE_eq_cCodim`): the geometric codimension of the
route-choice-answer.md:455:./DLNFibre/DLN/RlctPayoffGeneral.lean:16:  *closed rank-`≤ r` product locus* `Σ̄^r = productRankLocusLE d r` equals the combinatorial `C`. This
route-choice-answer.md:456:./DLNFibre/DLN/RlctPayoffGeneral.lean:71:`Σ̄^r = productRankLocusLE d r`, folding in `codim Σ̄^r = codim Σ^r` (Cor. 4.4 + Lemma 4.5,
route-choice-answer.md:457:./DLNFibre/DLN/RlctPayoffGeneral.lean:90:      = codimRepCanonical (productRankLocusLE (k := K) d r)
route-choice-answer.md:458:./DLNFibre/DLN/RlctPayoffGeneral.lean:110:(`Core.codimRepCanonical_productRankLocusLE_eq_cCodim`) rewrites `codim Σ̄^r = cCodim d r`. Both
route-choice-answer.md:459:./DLNFibre/DLN/RlctPayoffGeneral.lean:126:  have hAfin : codimRepCanonical (productRankLocusLE (k := K) d r) ≠ ⊤ := by
route-choice-answer.md:460:./DLNFibre/DLN/RlctPayoffGeneral.lean:127:    rw [codimRepCanonical_productRankLocusLE_eq_cCodim_enat d r h]; exact ENat.coe_ne_top _
route-choice-answer.md:461:./DLNFibre/DLN/RlctPayoffGeneral.lean:128:  have hAval : (codimRepCanonical (productRankLocusLE (k := K) d r)).toNat = (cCodim d r h).toNat := by
route-choice-answer.md:462:./DLNFibre/DLN/RlctPayoffGeneral.lean:129:    rw [codimRepCanonical_productRankLocusLE_eq_cCodim_enat d r h, ENat.toNat_coe]
route-choice-answer.md:463:./DLNFibre/DLN/RlctPayoffGeneral.lean:149:theorem codimRepCanonical_productRankLocusLE_d222_one :
route-choice-answer.md:464:./DLNFibre/DLN/RlctPayoffGeneral.lean:150:    (codimRepCanonical (productRankLocusLE (k := AlgebraicClosure ℚ) Core.d222 1)).toNat = 1 := by
route-choice-answer.md:465:./DLNFibre/DLN/RlctPayoffGeneral.lean:151:  have h := codimRepCanonical_productRankLocusLE_eq_cCodim (k := AlgebraicClosure ℚ) Core.d222 1
route-choice-answer.md:475:./DLNFibre/Core/OrbitPullbackDim.lean:52:theorem varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker [Infinite k]
route-choice-answer.md:479:./DLNFibre/Core/OrbitPullbackDim.lean:70:transcendence degree. Combines `varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker` with the
route-choice-answer.md:482:./DLNFibre/Core/OrbitPullbackDim.lean:78:  rw [varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker M,
route-choice-answer.md:486:./DLNFibre/DLN/RlctPayoff.lean:101:theorem fibre_zero_eq_productRankLocusLE_zero (d : Fin (N + 1) → ℕ) :
route-choice-answer.md:487:./DLNFibre/DLN/RlctPayoff.lean:102:    fibre (k := k) d 0 = productRankLocusLE (k := k) d 0 := by
route-choice-answer.md:488:./DLNFibre/DLN/RlctPayoff.lean:104:  rw [mem_fibre, mem_productRankLocusLE, Nat.le_zero]
route-choice-answer.md:489:./DLNFibre/DLN/RlctPayoff.lean:110:(definitional, via `fibre_zero_eq_productRankLocusLE_zero`). -/
route-choice-answer.md:490:./DLNFibre/DLN/RlctPayoff.lean:114:  rw [fibre_zero_eq_productRankLocusLE_zero]
route-choice-answer.md:501:./DLNFibre/Core/DeterminantalStratumDim.lean:16:`productRankLocusLE ![n,m] r = {M | M.rank ≤ r}` **is** the classical rank-`≤ r` determinantal
route-choice-answer.md:502:./DLNFibre/Core/DeterminantalStratumDim.lean:21:1. **Primality** (irreducible): for `N = 1`, `productRankLocusLE ![n,m] r = orbitRankLocus M₀` for a
route-choice-answer.md:504:./DLNFibre/Core/DeterminantalStratumDim.lean:25:2. **The codim value** (LANDED `codimRepCanonical_productRankLocusLE_eq_cCodim_enat`, unconditional
route-choice-answer.md:505:./DLNFibre/Core/DeterminantalStratumDim.lean:26:   in char 0 + alg-closed): `codimRepCanonical (productRankLocusLE ![n,m] r) = cCodim ![n,m] r`.
route-choice-answer.md:507:./DLNFibre/Core/DeterminantalStratumDim.lean:161:`productRankLocusLE ![n,m] r` — the only binding rank constraint at `N = 1` is the corner. Carries
route-choice-answer.md:508:./DLNFibre/Core/DeterminantalStratumDim.lean:163:theorem exists_orbitRankLocus_eq_productRankLocusLE_stratum (n m r : ℕ) (hn : r ≤ n) (hm : r ≤ m) :
route-choice-answer.md:509:./DLNFibre/Core/DeterminantalStratumDim.lean:165:      orbitRankLocus M₀ = productRankLocusLE (k := k) (dStratum n m) r := by
route-choice-answer.md:510:./DLNFibre/Core/DeterminantalStratumDim.lean:175:  · exact orbitRankLocus_subset_productRankLocusLE (dStratum n m) (hcorner.le)
route-choice-answer.md:511:./DLNFibre/Core/DeterminantalStratumDim.lean:177:    rw [mem_productRankLocusLE] at hA
route-choice-answer.md:512:./DLNFibre/Core/DeterminantalStratumDim.lean:196:flattening of) `productRankLocusLE ![n,m] r` is prime — it is `vanishingIdeal (Ō_{M₀})` of a single
route-choice-answer.md:514:./DLNFibre/Core/DeterminantalStratumDim.lean:198:theorem isPrime_vanishingIdeal_productRankLocusLE_stratum [IsAlgClosed k] (n m r : ℕ)
route-choice-answer.md:516:./DLNFibre/Core/DeterminantalStratumDim.lean:201:        (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r) :
route-choice-answer.md:517:./DLNFibre/Core/DeterminantalStratumDim.lean:203:  obtain ⟨M₀, hM₀⟩ := exists_orbitRankLocus_eq_productRankLocusLE_stratum (k := k) n m r hn hm
route-choice-answer.md:519:./DLNFibre/Core/DeterminantalStratumDim.lean:222:`productRankLocusLE ![n,m] r`) is
route-choice-answer.md:521:./DLNFibre/Core/DeterminantalStratumDim.lean:229:theorem varietyDim_productRankLocusLE_stratum [IsAlgClosed k] [CharZero k] (n m r : ℕ)
route-choice-answer.md:522:./DLNFibre/Core/DeterminantalStratumDim.lean:231:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
route-choice-answer.md:523:./DLNFibre/Core/DeterminantalStratumDim.lean:233:  set Z := productRankLocusLE (k := k) (dStratum n m) r with hZ
route-choice-answer.md:525:./DLNFibre/Core/DeterminantalStratumDim.lean:238:    (isPrime_vanishingIdeal_productRankLocusLE_stratum (k := k) n m r hn hm)
route-choice-answer.md:526:./DLNFibre/Core/DeterminantalStratumDim.lean:242:      codimRepCanonical_productRankLocusLE_eq_cCodim_enat (dStratum n m) r hne
route-choice-answer.md:529:./DLNFibre/Core/DeterminantalStratumDim.lean:268:    varietyDim (canonicalCoord (dStratum 2 2) '' productRankLocusLE (k := k) (dStratum 2 2) 1)
route-choice-answer.md:530:./DLNFibre/Core/DeterminantalStratumDim.lean:270:  have h := varietyDim_productRankLocusLE_stratum (k := k) 2 2 1 (by norm_num) (by norm_num)
route-choice-answer.md:550:./DLNFibre/Core/DeepChartRing.lean:239:  rw [mem_productRankLocusLE] at hA
route-choice-answer.md:552:./DLNFibre/Core/DeepChartRing.lean:244:    rw [mem_productRankLocusLE, mult_singleTuple]; exact hA, rfl⟩
route-choice-answer.md:555:./DLNFibre/Core/CTheta.lean:32:top-component count of the whole *closed* rank-`≤ r` locus `Σ̄^r = productRankLocusLE d r` (the
route-choice-answer.md:556:./DLNFibre/Core/CTheta.lean:36:`codim Σ̄^r = cCodim d r` (`Core.SigmaCodim.codimRepCanonical_productRankLocusLE_eq_cCodim`), and
route-choice-answer.md:557:./DLNFibre/Core/CTheta.lean:157:`Σ̄^r = productRankLocusLE d r` (`Core.SigmaCodim.codimRepCanonical_productRankLocusLE_eq_cCodim`,
route-choice-answer.md:561:./DLNFibre/Core/FibreCodim.lean:61:`(mult A).rank = r ≤ r`, so `A ∈ productRankLocusLE d r`: `mult⁻¹(B) ⊆ Σ̄^r`. -/
route-choice-answer.md:562:./DLNFibre/Core/FibreCodim.lean:62:theorem fibre_subset_productRankLocusLE {d : Fin (N + 1) → ℕ}
route-choice-answer.md:563:./DLNFibre/Core/FibreCodim.lean:64:    fibre d B ⊆ productRankLocusLE d r := by
route-choice-answer.md:564:./DLNFibre/Core/FibreCodim.lean:66:  rw [mem_productRankLocusLE]
route-choice-answer.md:565:./DLNFibre/Core/FibreCodim.lean:82:theorem codimRepCanonical_productRankLocusLE_le_codimRepCanonical_fibre {d : Fin (N + 1) → ℕ}
route-choice-answer.md:566:./DLNFibre/Core/FibreCodim.lean:84:    codimRepCanonical (productRankLocusLE (k := k) d r) ≤ codimRepCanonical (fibre d B) :=
route-choice-answer.md:567:./DLNFibre/Core/FibreCodim.lean:85:  codimRepCanonical_mono (fibre_subset_productRankLocusLE hB)
route-choice-answer.md:568:./DLNFibre/Core/FibreCodim.lean:99:    codimRepCanonical (productRankLocusLE (k := AlgebraicClosure ℚ) dWitness 0)
route-choice-answer.md:569:./DLNFibre/Core/FibreCodim.lean:102:  codimRepCanonical_productRankLocusLE_le_codimRepCanonical_fibre _ Matrix.rank_zero
route-choice-answer.md:574:./DLNFibre/Core/FibreDimFibration.lean:23:requiring `Algebra.HasGoingDown ⟸` flatness, which `mult` lacks globally since the fibre dimension
route-choice-answer.md:575:./DLNFibre/Core/FibreDimFibration.lean:42:`productRankLocusLE (dStratum n m) r`. Its coordinate ring `O(Mat^{≤r}) = MvPolynomial (RepCoord
route-choice-answer.md:578:./DLNFibre/Core/FibreDimFibration.lean:51:The thermometer `varietyDim_productRankLocusLE_stratum` gives the `ℕ∞`-via-`unbotD` value; this lifts
route-choice-answer.md:579:./DLNFibre/Core/FibreDimFibration.lean:54:theorem ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta [IsAlgClosed k] [CharZero k]
route-choice-answer.md:581:./DLNFibre/Core/FibreDimFibration.lean:58:          (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r))
route-choice-answer.md:583:./DLNFibre/Core/FibreDimFibration.lean:61:    (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r) with hI
route-choice-answer.md:584:./DLNFibre/Core/FibreDimFibration.lean:63:    isPrime_vanishingIdeal_productRankLocusLE_stratum (k := k) n m r hn hm
route-choice-answer.md:587:./DLNFibre/Core/FibreDimFibration.lean:66:      productRankLocusLE (k := k) (dStratum n m) r) = (r * (n + m - r) : ℕ) :=
route-choice-answer.md:588:./DLNFibre/Core/FibreDimFibration.lean:67:    varietyDim_productRankLocusLE_stratum n m r hn hm
route-choice-answer.md:590:./DLNFibre/Core/FibreDimFibration.lean:89:vanishingIdeal(…)` has height `δ = r(n + m − r)` — equidimensionality at a closed point of the
route-choice-answer.md:593:./DLNFibre/Core/FibreDimFibration.lean:95:          (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)))
route-choice-answer.md:595:./DLNFibre/Core/FibreDimFibration.lean:99:      (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)).IsPrime :=
route-choice-answer.md:596:./DLNFibre/Core/FibreDimFibration.lean:100:    isPrime_vanishingIdeal_productRankLocusLE_stratum (k := k) n m r hn hm
route-choice-answer.md:597:./DLNFibre/Core/FibreDimFibration.lean:102:    ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta n m r hn hm]
route-choice-answer.md:604:./DLNFibre/Core/EndBaseChangeSweep.lean:13:> `productRankLocus d r = ⋃_{P} (P • ·) '' (fibre d E)`   for any fixed rank-`r` target `E` (`N ≥ 1`).
route-choice-answer.md:605:./DLNFibre/Core/EndBaseChangeSweep.lean:16:consequence** `varietyDim (productRankLocus d r) = δ + varietyDim (fibre d E)` is the *one genuinely
route-choice-answer.md:606:./DLNFibre/Core/EndBaseChangeSweep.lean:56:`N ≥ 1`, the exact-rank locus `productRankLocus d r = {A : rank(mult A) = r}` is exactly the union,
route-choice-answer.md:607:./DLNFibre/Core/EndBaseChangeSweep.lean:59:> `A ∈ productRankLocus d r ↔ ∃ P, A ∈ (P • ·) '' (fibre d E)`.
route-choice-answer.md:608:./DLNFibre/Core/EndBaseChangeSweep.lean:64:theorem mem_productRankLocus_iff_mem_sweep (d : Fin (N + 1) → ℕ)
route-choice-answer.md:609:./DLNFibre/Core/EndBaseChangeSweep.lean:68:    A ∈ productRankLocus d r ↔
route-choice-answer.md:610:./DLNFibre/Core/EndBaseChangeSweep.lean:72:    rw [mem_productRankLocus] at hA
route-choice-answer.md:611:./DLNFibre/Core/EndBaseChangeSweep.lean:77:    rw [mem_productRankLocus, hPA, rank_endpoint_conj, hE]
route-choice-answer.md:612:./DLNFibre/Core/EndBaseChangeSweep.lean:79:/-- **The sweep identity (set form).** `productRankLocus d r = ⋃_P (P • ·) '' (fibre d E)` for a fixed
route-choice-answer.md:613:./DLNFibre/Core/EndBaseChangeSweep.lean:80:rank-`r` target `E`. The set-level statement of `mem_productRankLocus_iff_mem_sweep`. -/
route-choice-answer.md:614:./DLNFibre/Core/EndBaseChangeSweep.lean:81:theorem productRankLocus_eq_iUnion_smul_fibre (d : Fin (N + 1) → ℕ)
route-choice-answer.md:615:./DLNFibre/Core/EndBaseChangeSweep.lean:84:    productRankLocus d r
route-choice-answer.md:616:./DLNFibre/Core/EndBaseChangeSweep.lean:87:  rw [Set.mem_iUnion, mem_productRankLocus_iff_mem_sweep d hN E hE]
route-choice-answer.md:631:./DLNFibre/Core/DeterminantalBasePresentation.lean:341:    rw [sigmaIdeal]; exact isPrime_vanishingIdeal_productRankLocusLE_stratum q p r hq hp
route-choice-answer.md:641:./DLNFibre/Core/FibreHeightDirect.lean:54:  rw [codimRepCanonical, codimRep, vanishingIdeal_image_fibre_eq_radical, Ideal.height_radical]
route-choice-answer.md:650:./DLNFibre/Core/NullstellensatzCodim.lean:37:`axiom`. `varietyDim Z = ringKrullDim (R ⧸ vanishingIdeal Z)` is the Krull dimension of the
route-choice-answer.md:676:./DLNFibre/Core/NullstellensatzCodim.lean:143:`(vanishingIdeal Z).IsPrime` — the height of its vanishing ideal plus its variety dimension equals
route-choice-answer.md:677:./DLNFibre/Core/NullstellensatzCodim.lean:144:the ambient dimension `Nat.card σ`: `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ`. The
route-choice-answer.md:678:./DLNFibre/Core/NullstellensatzCodim.lean:145:catenary identity over `σ`, read at the prime `vanishingIdeal Z`. Geometric codimension `=` ambient
route-choice-answer.md:682:./DLNFibre/Core/NullstellensatzCodim.lean:150:  have key := height_add_ringKrullDim_quotient_eq_card (vanishingIdeal k Z)
route-choice-answer.md:688:./DLNFibre/Core/NullstellensatzCodim.lean:163:subtraction; lossless here since `varietyDim Z ≤ Nat.card σ`). The geometric codimension is the
route-choice-answer.md:699:./DLNFibre/Core/NullstellensatzCodim.lean:190:varietyDim (coord '' Z)` for an irreducible variety `coord '' Z`: geometric codimension `=` ambient
route-choice-answer.md:742:./DLNFibre/Core/FibreReducedTrivialization.lean:40:`sorry` or a global axiom. The deep trivialization `e` itself (the endpoint-normalization product
route-choice-answer.md:743:./DLNFibre/Core/FibreReducedTrivialization.lean:102:trivialization `e : S ≃ₐ[k] R ⊗_k F_B` (the endpoint-normalization product iso) and that the chart
route-choice-answer.md:750:./DLNFibre/Core/CThetaGeometricPerm.lean:12:* `codimRepCanonical_productRankLocusLE_eq_cCodim_enat` (`SigmaCodim`) — `codim Σ̄^r = (cCodim d r).toNat`.
route-choice-answer.md:751:./DLNFibre/Core/CThetaGeometricPerm.lean:31:`codimRepCanonical_productRankLocusLE_eq_cCodim` (`codim Σ̄^r = cCodim`) on both sides + the
route-choice-answer.md:752:./DLNFibre/Core/CThetaGeometricPerm.lean:33:theorem codim_productRankLocusLE_toNat_comp_perm [IsAlgClosed k] [CharZero k]
route-choice-answer.md:753:./DLNFibre/Core/CThetaGeometricPerm.lean:36:    (codimRepCanonical (productRankLocusLE (k := k) (d ∘ σ) r)).toNat
route-choice-answer.md:754:./DLNFibre/Core/CThetaGeometricPerm.lean:37:      = (codimRepCanonical (productRankLocusLE (k := k) d r)).toNat := by
route-choice-answer.md:755:./DLNFibre/Core/CThetaGeometricPerm.lean:38:  have e1 : ((codimRepCanonical (productRankLocusLE (k := k) (d ∘ σ) r)).toNat : ℤ)
route-choice-answer.md:756:./DLNFibre/Core/CThetaGeometricPerm.lean:39:      = cCodim (d ∘ σ) r h := codimRepCanonical_productRankLocusLE_eq_cCodim (d ∘ σ) r h
route-choice-answer.md:757:./DLNFibre/Core/CThetaGeometricPerm.lean:40:  have e2 : ((codimRepCanonical (productRankLocusLE (k := k) d r)).toNat : ℤ)
route-choice-answer.md:758:./DLNFibre/Core/CThetaGeometricPerm.lean:41:      = cCodim d r h' := codimRepCanonical_productRankLocusLE_eq_cCodim d r h'
route-choice-answer.md:759:./DLNFibre/Core/CThetaGeometricPerm.lean:42:  have hz : ((codimRepCanonical (productRankLocusLE (k := k) (d ∘ σ) r)).toNat : ℤ)
route-choice-answer.md:760:./DLNFibre/Core/CThetaGeometricPerm.lean:43:      = ((codimRepCanonical (productRankLocusLE (k := k) d r)).toNat : ℤ) := by
route-choice-answer.md:761:./DLNFibre/Core/CThetaGeometricPerm.lean:49:theorem codim_productRankLocusLE_toNat_comp_sort [IsAlgClosed k] [CharZero k]
route-choice-answer.md:762:./DLNFibre/Core/CThetaGeometricPerm.lean:53:    (codimRepCanonical (productRankLocusLE (k := k) (d ∘ _root_.Tuple.sort d) r)).toNat
route-choice-answer.md:763:./DLNFibre/Core/CThetaGeometricPerm.lean:54:      = (codimRepCanonical (productRankLocusLE (k := k) d r)).toNat :=
route-choice-answer.md:764:./DLNFibre/Core/CThetaGeometricPerm.lean:55:  codim_productRankLocusLE_toNat_comp_perm (_root_.Tuple.sort d) d r hr h h'
route-choice-answer.md:765:./DLNFibre/Core/CThetaGeometricPerm.lean:60:theorem codimRepCanonical_productRankLocusLE_comp_perm [IsAlgClosed k] [CharZero k]
route-choice-answer.md:766:./DLNFibre/Core/CThetaGeometricPerm.lean:63:    codimRepCanonical (productRankLocusLE (k := k) (d ∘ σ) r)
route-choice-answer.md:767:./DLNFibre/Core/CThetaGeometricPerm.lean:64:      = codimRepCanonical (productRankLocusLE (k := k) d r) := by
route-choice-answer.md:768:./DLNFibre/Core/CThetaGeometricPerm.lean:65:  rw [codimRepCanonical_productRankLocusLE_eq_cCodim_enat (d ∘ σ) r h,
route-choice-answer.md:769:./DLNFibre/Core/CThetaGeometricPerm.lean:66:      codimRepCanonical_productRankLocusLE_eq_cCodim_enat d r h',
route-choice-answer.md:770:./DLNFibre/Core/CThetaGeometricPerm.lean:96:theorem codimRepCanonical_productRankLocusLE_comp_perm_of_le [IsAlgClosed k] [CharZero k]
route-choice-answer.md:771:./DLNFibre/Core/CThetaGeometricPerm.lean:99:    codimRepCanonical (productRankLocusLE (k := k) (d ∘ σ) r)
route-choice-answer.md:772:./DLNFibre/Core/CThetaGeometricPerm.lean:100:      = codimRepCanonical (productRankLocusLE (k := k) d r) :=
route-choice-answer.md:773:./DLNFibre/Core/CThetaGeometricPerm.lean:101:  codimRepCanonical_productRankLocusLE_comp_perm σ d r hr
route-choice-answer.md:774:./DLNFibre/Core/SigmaCodim.lean:7:product locus* `Σ̄^r = productRankLocusLE d r` equals the combinatorial codimension `C = cCodim d r`:
route-choice-answer.md:775:./DLNFibre/Core/SigmaCodim.lean:9:* `codimRepCanonical_productRankLocusLE_eq_cCodim` (the `ℤ` form `(codim Σ̄^r).toNat = C`),
route-choice-answer.md:776:./DLNFibre/Core/SigmaCodim.lean:10:* `codimRepCanonical_productRankLocusLE_eq_cCodim_enat` (the `ℕ∞` form `codim Σ̄^r = (C.toNat : ℕ∞)`).
route-choice-answer.md:777:./DLNFibre/Core/SigmaCodim.lean:40:`Σ̄^r` itself* (`productRankLocusLE d r`), not the fibre — the fibre needs the Cited bundle shift.
route-choice-answer.md:778:./DLNFibre/Core/SigmaCodim.lean:48:theorem codimRepCanonical_productRankLocusLE_eq_height_sigmaIdeal (d : Fin (N + 1) → ℕ) (r : ℕ) :
route-choice-answer.md:779:./DLNFibre/Core/SigmaCodim.lean:49:    codimRepCanonical (productRankLocusLE (k := k) d r) = (sigmaIdeal (k := k) d r).height :=
route-choice-answer.md:780:./DLNFibre/Core/SigmaCodim.lean:53:codimension of `Σ̄^r = productRankLocusLE d r` equals the infimum, over the corner-`≤ r` orbit
route-choice-answer.md:781:./DLNFibre/Core/SigmaCodim.lean:58:theorem codimRepCanonical_productRankLocusLE_eq_iInf_orbitCodim
route-choice-answer.md:782:./DLNFibre/Core/SigmaCodim.lean:60:    codimRepCanonical (productRankLocusLE (k := k) d r)
route-choice-answer.md:783:./DLNFibre/Core/SigmaCodim.lean:63:  rw [codimRepCanonical_productRankLocusLE_eq_height_sigmaIdeal, Ideal.height]
route-choice-answer.md:788:./DLNFibre/Core/SigmaCodim.lean:101:theorem codimRepCanonical_productRankLocusLE_eq_cCodim_enat [IsAlgClosed k] [CharZero k]
route-choice-answer.md:789:./DLNFibre/Core/SigmaCodim.lean:103:    codimRepCanonical (productRankLocusLE (k := k) d r) = ((cCodim d r h).toNat : ℕ∞) := by
route-choice-answer.md:790:./DLNFibre/Core/SigmaCodim.lean:104:  rw [codimRepCanonical_productRankLocusLE_eq_iInf_orbitCodim]
route-choice-answer.md:792:./DLNFibre/Core/SigmaCodim.lean:132:`Σ̄^r = productRankLocusLE d r` equals the combinatorial codimension `cCodim d r = C`
route-choice-answer.md:793:./DLNFibre/Core/SigmaCodim.lean:136:theorem codimRepCanonical_productRankLocusLE_eq_cCodim [IsAlgClosed k] [CharZero k]
route-choice-answer.md:794:./DLNFibre/Core/SigmaCodim.lean:138:    ((codimRepCanonical (productRankLocusLE (k := k) d r)).toNat : ℤ) = cCodim d r h := by
route-choice-answer.md:795:./DLNFibre/Core/SigmaCodim.lean:139:  rw [codimRepCanonical_productRankLocusLE_eq_cCodim_enat d r h, ENat.toNat_coe]
route-choice-answer.md:813:./DLNFibre/Core/PolynomialDimension.lean:18:* **L5.5** `ringKrullDim_quotient_eq_noetherRank` — `dim (R ⧸ p)` equals the Noether-normalization
route-choice-answer.md:815:./DLNFibre/Core/PolynomialDimension.lean:40:the quotient dimension is preserved. That positioning is Mathlib's Noether-normalization `T`
route-choice-answer.md:820:./DLNFibre/Core/OrbitDifferentialRank.lean:35:Krull-dimension bound) and `varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional`
route-choice-answer.md:826:./DLNFibre/Core/DeterminantalChartRing.lean:227:`mult d A`, which vanishes on `Σ̄^r = productRankLocusLE d r` (rank `≤ r`). General in `N`. This is
route-choice-answer.md:827:./DLNFibre/Core/DeterminantalChartRing.lean:247:`Σ̄^r = productRankLocusLE d r`): it evaluates on every `A ∈ Σ̄^r` to an `(r+1)`-minor of the
route-choice-answer.md:829:./DLNFibre/Core/DeterminantalChartRing.lean:255:  rw [mem_productRankLocusLE] at hA
route-choice-answer.md:830:./DLNFibre/Core/DeterminantalChartRing.lean:315:/-- The witness lies in the determinantal base `Σ̄^r = productRankLocusLE ![q,p] r`. -/
route-choice-answer.md:831:./DLNFibre/Core/DeterminantalChartRing.lean:317:    chartWitness (k := k) q p r ∈ productRankLocusLE (k := k) (dStratum q p) r := by
route-choice-answer.md:832:./DLNFibre/Core/DeterminantalChartRing.lean:318:  rw [mem_productRankLocusLE, mult_chartWitness]; exact rank_chartWitness_le q p r
route-choice-answer.md:834:./DLNFibre/Core/DeterminantalChartRing.lean:367:    rw [sigmaIdeal]; exact isPrime_vanishingIdeal_productRankLocusLE_stratum q p r hq hp
route-choice-answer.md:835:./DLNFibre/Core/DeterminantalChartRing.lean:386:    ← codimRepCanonical_productRankLocusLE_eq_height_sigmaIdeal,
route-choice-answer.md:836:./DLNFibre/Core/DeterminantalChartRing.lean:387:    codimRepCanonical_productRankLocusLE_eq_cCodim_enat (dStratum q p) r hne]
route-choice-answer.md:841:./DLNFibre/Core/CThetaGeometric.lean:32:locus `Σ̄^r = productRankLocusLE d r = {A | rank (mult A) ≤ r}` — the genuine Zariski closure of the
route-choice-answer.md:842:./DLNFibre/Core/CThetaGeometric.lean:38:(`Core.SigmaCodim.codimRepCanonical_productRankLocusLE_eq_cCodim`) and the top-component count
route-choice-answer.md:853:./DLNFibre/Core/RadicalCatenary.lean:176:equal the ambient dimension: `codimRepCanonical Z + varietyDim (canonicalCoord d '' Z) = card`. No
route-choice-answer.md:866:./DLNFibre/Core/SigmaStratification.lean:8:`Σ̄^r = productRankLocusLE d r = {A | rank (mult A) ≤ r}` is the union of the orbit closures
route-choice-answer.md:867:./DLNFibre/Core/SigmaStratification.lean:13:  `productRankLocusLE d r = ⋃ (M) (_ : (mult d M).rank ≤ r), orbitRankLocus M`,
route-choice-answer.md:868:./DLNFibre/Core/SigmaStratification.lean:18:* `⊇` is per-orbit (`orbitRankLocus_subset_productRankLocusLE`): if `A ∈ Ō_M` then
route-choice-answer.md:869:./DLNFibre/Core/SigmaStratification.lean:68:/-- The orbit closure `Ō_M = orbitRankLocus M` is contained in `Σ̄^r = productRankLocusLE d r` as
route-choice-answer.md:870:./DLNFibre/Core/SigmaStratification.lean:71:theorem orbitRankLocus_subset_productRankLocusLE (d : Fin (N + 1) → ℕ) {r : ℕ}
route-choice-answer.md:871:./DLNFibre/Core/SigmaStratification.lean:73:    orbitRankLocus M ⊆ productRankLocusLE d r := by
route-choice-answer.md:872:./DLNFibre/Core/SigmaStratification.lean:75:  rw [mem_productRankLocusLE, ← corner_rankPattern_eq_rank d A]
route-choice-answer.md:873:./DLNFibre/Core/SigmaStratification.lean:117:`orbitRankLocus_subset_productRankLocusLE`; the `→` takes `M := A` (`self_mem_orbitRankLocus`,
route-choice-answer.md:874:./DLNFibre/Core/SigmaStratification.lean:119:theorem mem_productRankLocusLE_iff_exists_mem_orbitRankLocus (d : Fin (N + 1) → ℕ) (r : ℕ)
route-choice-answer.md:875:./DLNFibre/Core/SigmaStratification.lean:121:    A ∈ productRankLocusLE d r
route-choice-answer.md:876:./DLNFibre/Core/SigmaStratification.lean:125:    exact ⟨A, mem_productRankLocusLE.mp hA, self_mem_orbitRankLocus A⟩
route-choice-answer.md:877:./DLNFibre/Core/SigmaStratification.lean:127:    exact orbitRankLocus_subset_productRankLocusLE d hM hAM
route-choice-answer.md:878:./DLNFibre/Core/SigmaStratification.lean:131:(Le Halleur–Rimányi 2024, Cor 4.4). `⊇` is `orbitRankLocus_subset_productRankLocusLE`; `⊆` places
route-choice-answer.md:879:./DLNFibre/Core/SigmaStratification.lean:135:theorem productRankLocusLE_eq_iUnion_orbitRankLocus (d : Fin (N + 1) → ℕ) (r : ℕ) :
route-choice-answer.md:880:./DLNFibre/Core/SigmaStratification.lean:136:    productRankLocusLE d r
route-choice-answer.md:881:./DLNFibre/Core/SigmaStratification.lean:139:  rw [Set.mem_iUnion₂, mem_productRankLocusLE_iff_exists_mem_orbitRankLocus]
route-choice-answer.md:882:./DLNFibre/Core/SigmaStratification.lean:163:example : tupleWitnessStratQ ∈ productRankLocusLE dWitness 2 := by
route-choice-answer.md:883:./DLNFibre/Core/SigmaStratification.lean:164:  rw [productRankLocusLE_eq_iUnion_orbitRankLocus, Set.mem_iUnion₂]
route-choice-answer.md:931:./DLNFibre/Core/AffineNoetherRank.lean:17:algebraic over the polynomial subring, so `trdeg_add_eq` + `MvPolynomial.trdeg_of_isDomain` +
route-choice-answer.md:932:./DLNFibre/Core/AffineNoetherRank.lean:39:`trdeg_add_eq` the degree splits as `trdeg_k k[Fin s] + trdeg_{k[Fin s]} B = s + 0`. -/
route-choice-answer.md:933:./DLNFibre/Core/AffineNoetherRank.lean:52:      = Algebra.trdeg k B := trdeg_add_eq k (MvPolynomial (Fin s) k)
route-choice-answer.md:937:./DLNFibre/Core/FibreDimFibrationProbe.lean:34:    codimRepCanonical (productRankLocusLE (k := k) d r) = ((cCodim d r h).toNat : ℕ∞) :=
route-choice-answer.md:938:./DLNFibre/Core/FibreDimFibrationProbe.lean:35:  codimRepCanonical_productRankLocusLE_eq_cCodim_enat d r h
route-choice-answer.md:939:./DLNFibre/Core/FibreDimFibrationProbe.lean:37:/-- LANDED: the determinantal-stratum dimension `varietyDim (Mat^{≤r}) = r(n+m−r) = δ`. -/
route-choice-answer.md:940:./DLNFibre/Core/FibreDimFibrationProbe.lean:39:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
route-choice-answer.md:941:./DLNFibre/Core/FibreDimFibrationProbe.lean:41:  varietyDim_productRankLocusLE_stratum n m r hn hm
route-choice-answer.md:942:./DLNFibre/Core/FibreDimFibrationProbe.lean:52:    codimRepCanonical (productRankLocusLE (k := k) d r) ≤ codimRepCanonical (fibre d B) :=
route-choice-answer.md:943:./DLNFibre/Core/FibreDimFibrationProbe.lean:53:  codimRepCanonical_productRankLocusLE_le_codimRepCanonical_fibre B hB
route-choice-answer.md:948:./DLNFibre/Core/FibreDimFibrationProbe.lean:83:/-- The base `Mat^{≤r}` over the target `Mat_{d_N × d_0}` is `productRankLocusLE (dStratum (d 0)
route-choice-answer.md:950:./DLNFibre/Core/FibreDimFibrationProbe.lean:89:        productRankLocusLE (k := k) (dStratum (d 0) (d (Fin.last N))) r) :
route-choice-answer.md:951:./DLNFibre/Core/FibreDimFibrationProbe.lean:91:  isPrime_vanishingIdeal_productRankLocusLE_stratum (d 0) (d (Fin.last N)) r hq hp
route-choice-answer.md:957:./DLNFibre/Core/SigmaComponents.lean:9:The topology of the closed rank-`≤ r` product locus `Σ̄^r = productRankLocusLE d r`, building on the
route-choice-answer.md:960:./DLNFibre/Core/SigmaComponents.lean:20:  the finite family of prime orbit ideals (G2 + `vanishingIdeal` turns unions into infs), so its
route-choice-answer.md:966:./DLNFibre/Core/SigmaComponents.lean:129:vanishing ideal of the flattened `Σ̄^r = canonicalCoord d '' productRankLocusLE d r`. -/
route-choice-answer.md:968:./DLNFibre/Core/SigmaComponents.lean:133:    (canonicalCoord d '' productRankLocusLE d r)
route-choice-answer.md:969:./DLNFibre/Core/SigmaComponents.lean:136:orbit-ideal family: `vanishingIdeal` turns the G2 union `Σ̄^r = ⋃_M Ō_M` into an intersection. -/
route-choice-answer.md:971:./DLNFibre/Core/SigmaComponents.lean:149:    exact hp _ ⟨A, orbitRankLocus_subset_productRankLocusLE d hM hA, rfl⟩
route-choice-answer.md:973:./DLNFibre/Core/SigmaComponents.lean:155:    rw [mem_productRankLocusLE] at hA
route-choice-answer.md:996:./DLNFibre/Core/SigmaComponents.lean:298:theorem zero_mem_productRankLocusLE_d222 :
route-choice-answer.md:997:./DLNFibre/Core/SigmaComponents.lean:299:    (0 : Tuple (k := AlgebraicClosure ℚ) dWitness) ∈ productRankLocusLE dWitness 0 := by
route-choice-answer.md:998:./DLNFibre/Core/SigmaComponents.lean:300:  rw [mem_productRankLocusLE]
route-choice-answer.md:999:./DLNFibre/Core/SigmaComponents.lean:312:  ⟨_, ⟨0, zero_mem_productRankLocusLE_d222, rfl⟩⟩
route-choice-answer.md:1044:./DLNFibre/Core/Setup.lean:56:def productRankLocus (d : Fin (N + 1) → ℕ) (r : ℕ) : Set (Tuple (k := k) d) :=
route-choice-answer.md:1045:./DLNFibre/Core/Setup.lean:60:def productRankLocusLE (d : Fin (N + 1) → ℕ) (r : ℕ) : Set (Tuple (k := k) d) :=
route-choice-answer.md:1046:./DLNFibre/Core/Setup.lean:69:theorem mem_productRankLocus {d : Fin (N + 1) → ℕ} {r : ℕ} {A : Tuple (k := k) d} :
route-choice-answer.md:1047:./DLNFibre/Core/Setup.lean:70:    A ∈ productRankLocus d r ↔ (mult d A).rank = r := Iff.rfl
route-choice-answer.md:1048:./DLNFibre/Core/Setup.lean:73:theorem mem_productRankLocusLE {d : Fin (N + 1) → ℕ} {r : ℕ} {A : Tuple (k := k) d} :
route-choice-answer.md:1049:./DLNFibre/Core/Setup.lean:74:    A ∈ productRankLocusLE d r ↔ (mult d A).rank ≤ r := Iff.rfl
route-choice-answer.md:1086:./DLNFibre/Core/RouteCAssembly.lean:50:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
route-choice-answer.md:1088:./DLNFibre/Core/RouteCAssembly.lean:53:    (hClosure : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
route-choice-answer.md:1089:./DLNFibre/Core/RouteCAssembly.lean:54:        = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r))
route-choice-answer.md:1091:./DLNFibre/Core/RouteCAssembly.lean:57:    (hCatSigma : codimRepCanonical (productRankLocusLE (k := k) d r)
route-choice-answer.md:1092:./DLNFibre/Core/RouteCAssembly.lean:58:        + varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
route-choice-answer.md:1093:./DLNFibre/Core/RouteCAssembly.lean:63:  have hCsigma : codimRepCanonical (productRankLocusLE (k := k) d r)
route-choice-answer.md:1094:./DLNFibre/Core/RouteCAssembly.lean:65:    codimRepCanonical_productRankLocusLE_eq_cCodim_enat d r h
route-choice-answer.md:1095:./DLNFibre/Core/RouteCAssembly.lean:67:  have hdimSigma : varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
route-choice-answer.md:1105:./DLNFibre/Core/RouteCAssembly.lean:106:    (hSigmaNe : (canonicalCoord d '' productRankLocusLE (k := k) d r).Nonempty)
route-choice-answer.md:1106:./DLNFibre/Core/RouteCAssembly.lean:107:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
route-choice-answer.md:1108:./DLNFibre/Core/RouteCAssembly.lean:110:    (hClosure : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
route-choice-answer.md:1109:./DLNFibre/Core/RouteCAssembly.lean:111:        = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)) :
route-choice-answer.md:1120:The project is pinned to `leanprover-community/mathlib4` `v4.29.0` (`8a178386...`). The repo itself already has several probes around this rung, so I’ll read the relevant local files plus Mathlib’s normalization/dimension files to separate “already staged” from “absent upstream.”
route-choice-answer.md:1124:/bin/bash -lc 'rg -n "theorem .*Noether|def .*Noether|class .*Noether|finiteType|FiniteType|IsIntegral|NoetherNormalization|Noetherian|trdeg_add_eq|Transcendence|IsAlgebraic|FractionRing|GoingDown|HasGoingDown|flat|Flat" .lake/packages/mathlib/Mathlib/RingTheory .lake/packages/mathlib/Mathlib/FieldTheory .lake/packages/mathlib/Mathlib/AlgebraicGeometry -S' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean
route-choice-answer.md:1136:# `DLNFibre.Core.FibreDimFibration` — the fibre-dimension count toward Lemma 4.6 (H4)
route-choice-answer.md:1138:Rung **H4** of the HEIGHT-DIRECT route to Lehalleur–Rimányi Lemma 4.6's geometry: the dimension of
route-choice-answer.md:1140:`mult|_{Σ̄^r} : Σ̄^r ↠ Mat^{≤r}` (dominant) and the generic-fibre-dimension count
route-choice-answer.md:1144:This module banks the **base-stratum dimension brick** the count consumes, and the **easy
route-choice-answer.md:1148:exact-rank good locus where the fibre dimension does not jump — generic flatness / generic
route-choice-answer.md:1150:requiring `Algebra.HasGoingDown ⟸` flatness, which `mult` lacks globally since the fibre dimension
route-choice-answer.md:1165:/-! ## The base-stratum Krull dimension brick: `ringKrullDim O(Mat^{≤r}) = δ`
route-choice-answer.md:1168:`Mat_{m × n}` (`n = d_0`, `m = d_N`), encoded as the `N = 1` product-rank locus
route-choice-answer.md:1169:`productRankLocusLE (dStratum n m) r`. Its coordinate ring `O(Mat^{≤r}) = MvPolynomial (RepCoord
route-choice-answer.md:1171:irreducible determinantal variety) of Krull dimension `δ = r(n + m − r)`. From the LANDED thermometer
route-choice-answer.md:1175:/-- **The base-stratum Krull dimension** `ringKrullDim O(Mat^{≤r}) = δ`. For `r ≤ n`, `r ≤ m`, over an
route-choice-answer.md:1177:variety `Mat^{≤r}_{m × n}` (the `N = 1` product-rank locus) has Krull dimension `r(n + m − r) = δ`.
route-choice-answer.md:1178:The thermometer `varietyDim_productRankLocusLE_stratum` gives the `ℕ∞`-via-`unbotD` value; this lifts
route-choice-answer.md:1179:it to the genuine `WithBot ℕ∞` Krull dimension, using that the vanishing ideal is prime (the quotient
route-choice-answer.md:1181:theorem ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta [IsAlgClosed k] [CharZero k]
route-choice-answer.md:1185:          (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r))
route-choice-answer.md:1188:    (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r) with hI
route-choice-answer.md:1190:    isPrime_vanishingIdeal_productRankLocusLE_stratum (k := k) n m r hn hm
route-choice-answer.md:1193:      productRankLocusLE (k := k) (dStratum n m) r) = (r * (n + m - r) : ℕ) :=
route-choice-answer.md:1194:    varietyDim_productRankLocusLE_stratum n m r hn hm
route-choice-answer.md:1209:By equidimensionality at a closed point (`OrbitTangentCotangent.height_eq_ringKrullDim_of_isMaximal_fintype`,
route-choice-answer.md:1210:`Fintype`-indexed) and the base Krull dimension `= δ` just established: every maximal ideal of the
route-choice-answer.md:1216:vanishingIdeal(…)` has height `δ = r(n + m − r)` — equidimensionality at a closed point of the
route-choice-answer.md:1222:          (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)))
route-choice-answer.md:1226:      (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)).IsPrime :=
route-choice-answer.md:1227:    isPrime_vanishingIdeal_productRankLocusLE_stratum (k := k) n m r hn hm
route-choice-answer.md:1229:    ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta n m r hn hm]
route-choice-answer.md:1231:/-! ## Affine-domain equidimensionality over a `Fintype` coordinate index
route-choice-answer.md:1233:`affine_domain_height_add_ringKrullDim_quotient_eq` is over `MvPolynomial (Fin n) k`. Transport it to
route-choice-answer.md:1239:/-- **Affine-domain equidimensionality, finite index.** For `σ` finite, `I` a prime of
route-choice-answer.md:1242:`affine_domain_height_add_ringKrullDim_quotient_eq` through `renameEquiv` and the induced quotient
route-choice-answer.md:1244:theorem affine_domain_height_add_ringKrullDim_quotient_eq_fintype {σ : Type*} [Finite σ]
route-choice-answer.md:1260:  have hL := affine_domain_height_add_ringKrullDim_quotient_eq k (Fintype.card σ) J p'
route-choice-answer.md:1263:    ringKrullDim_quotient_map_algEquiv Φ p, hJ, ringKrullDim_quotient_map_algEquiv e I] at hL
route-choice-answer.md:1279:Un-aggregated probe pinning the exact engine signatures the H4 fibre-dimension count consumes, plus
route-choice-answer.md:1300:    codimRepCanonical (productRankLocusLE (k := k) d r) = ((cCodim d r h).toNat : ℕ∞) :=
route-choice-answer.md:1301:  codimRepCanonical_productRankLocusLE_eq_cCodim_enat d r h
route-choice-answer.md:1303:/-- LANDED: the determinantal-stratum dimension `varietyDim (Mat^{≤r}) = r(n+m−r) = δ`. -/
route-choice-answer.md:1305:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
route-choice-answer.md:1307:  varietyDim_productRankLocusLE_stratum n m r hn hm
route-choice-answer.md:1318:    codimRepCanonical (productRankLocusLE (k := k) d r) ≤ codimRepCanonical (fibre d B) :=
route-choice-answer.md:1319:  codimRepCanonical_productRankLocusLE_le_codimRepCanonical_fibre B hB

codex
I found that this directory captured a previous Codex run, but it mostly records repository facts rather than proving the new claim. I’m checking upstream Mathlib now for `ringKrullDim`, quotient, and tensor/product APIs.
web search: 
web search: site:github.com/leanprover-community/mathlib4 ringKrullDim quotient radical mathlib4
web search: 
web search: Mathlib RingTheory KrullDimension ringKrullDim radical
web search: 
web search: https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.29.0/Mathlib/RingTheory/KrullDimension/Basic.lean
web search: 
web search: https://github.com/leanprover-community/mathlib4/blob/v4.29.0/Mathlib/RingTheory/KrullDimension/Basic.lean
codex
The browser isn’t reliably fetching raw GitHub. Since the previous run points at a sibling `lean` checkout, I’m going to try read-only inspection there; if the sandbox blocks it, I’ll keep the answer at the level I can verify.
exec
/bin/bash -lc 'ls -la /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean | head -50' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
total 60
drwxrwxr-x 5 ubuntu ubuntu  4096 Jun 24 17:28 .
drwxrwxr-x 9 ubuntu ubuntu  4096 Jun 24 12:33 ..
drwxrwxr-x 3 ubuntu ubuntu  4096 Jun 23 17:37 .lake
-rw-rw-r-- 1 ubuntu ubuntu 13887 Jun 23 22:26 CLAUDE.md
drwxrwxr-x 4 ubuntu ubuntu  4096 Jun 24 14:13 DLNFibre
-rw-rw-r-- 1 ubuntu ubuntu 11441 Jun 24 17:27 DLNFibre.lean
-rw-rw-r-- 1 ubuntu ubuntu  3119 Jun 23 17:24 lake-manifest.json
-rw-rw-r-- 1 ubuntu ubuntu   353 Jun 23 17:24 lakefile.toml
-rw-rw-r-- 1 ubuntu ubuntu    25 Jun 23 17:24 lean-toolchain
drwxrwxr-x 2 ubuntu ubuntu  4096 Jun 23 17:24 scripts

exec
/bin/bash -lc 'rg -n "theorem .*radical|ringKrullDim.*radical|radical.*ringKrullDim|height_radical|quotient.*radical|PrimeSpectrum.*quotient|OrderIso.*prime|comap.*radical" /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory -S | head -300' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Radical.lean:26:theorem degree_radical_le {a : k[X]} (h : a ≠ 0) : (radical a).degree ≤ a.degree :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Radical.lean:29:theorem natDegree_radical_le {a : k[X]} :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/QuasiFinite/Basic.lean:135:    rw [Ideal.map_le_iff_le_comap, ← Ring.KrullDimLE.nilradical_eq_maximalIdeal]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/IrreducibleRing.lean:39:theorem Polynomial.Monic.irreducible_of_irreducible_map_of_isPrime_nilradical
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/ContentIdeal.lean:171:theorem mul_contentIdeal_le_radical_contentIdeal_mul :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Artinian/Ring.lean:63:theorem isNilpotent_nilradical : IsNilpotent (nilradical R) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Artinian/Module.lean:628:/-- The quotient of a commutative Artinian ring by its nilradical is isomorphic to
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Noetherian/Nilpotent.lean:25:theorem IsNoetherianRing.isNilpotent_nilradical (R : Type*) [CommSemiring R] [IsNoetherianRing R] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:150:theorem isClosed_iff_zeroLocus_radical_ideal (Z : Set (PrimeSpectrum R)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:229:theorem isIrreducible_zeroLocus_iff_of_radical (I : Ideal R) (hI : I.IsRadical) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:308:theorem discreteTopology_iff_finite_isMaximal_and_sInf_le_nilradical :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:437:lemma comap_quotientMk_bijective_of_le_nilradical {I : Ideal R} (hle : I ≤ nilradical R) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:858:    vanishingIdeal (Set.range (comap f)) = (RingHom.ker f).radical := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:860:  rw [RingHom.ker_eq_comap_bot, ← Ideal.comap_radical, Ideal.radical_eq_sInf]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:867:  rw [← zeroLocus_vanishingIdeal_eq_closure, vanishingIdeal_range_comap, zeroLocus_radical]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:870:    DenseRange (comap f) ↔ RingHom.ker f ≤ nilradical R := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Homeomorph.lean:53:    ⟨h1, (comap_quotientMk_bijective_of_le_nilradical hker).2.comp <|
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Radical/Basic.lean:145:@[simp] theorem radical_zero : radical (0 : M) = 1 := by simp [radical]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Radical/Basic.lean:146:@[simp] theorem radical_one : radical (1 : M) = 1 := by simp [radical]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Radical/Basic.lean:147:theorem radical_eq_of_associated (h : Associated a b) : radical a = radical b := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Radical/Basic.lean:159:theorem radical_of_isUnit (h : IsUnit a) : radical a = 1 :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Radical/Basic.lean:162:theorem radical_mul_of_isUnit_left (h : IsUnit u) : radical (u * a) = radical a :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Radical/Basic.lean:165:theorem radical_mul_of_isUnit_right (h : IsUnit u) : radical (a * u) = radical a :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Radical/Basic.lean:168:theorem radical_pow (a : M) {n : ℕ} (hn : n ≠ 0) : radical (a ^ n) = radical a := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Radical/Basic.lean:171:theorem radical_pow_dvd {n : ℕ} : radical (a ^ n) ∣ radical a := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Radical/Basic.lean:176:theorem radical_dvd_self : radical a ∣ a := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Radical/Basic.lean:186:theorem radical_of_prime (ha : Prime a) : radical a = normalize a := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Radical/Basic.lean:191:theorem radical_pow_of_prime (ha : Prime a) {n : ℕ} (hn : n ≠ 0) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Radical/Basic.lean:196:@[simp] theorem radical_ne_zero [Nontrivial M] : radical a ≠ 0 := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Radical/Basic.lean:253:theorem radical_eq_one_iff : radical a = 1 ↔ a = 0 ∨ IsUnit a := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Radical/Basic.lean:299:theorem radical_dvd_iff_primeFactors_subset (hb : b ≠ 0) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Radical/Basic.lean:305:theorem radical_mul (hc : IsRelPrime a b) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Radical/Basic.lean:310:theorem radical_prod {ι : Type*} {f : ι → M} (s : Finset ι)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Radical/Basic.lean:322:theorem radical_mul_dvd : radical (a * b) ∣ radical a * radical b := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Radical/Basic.lean:332:theorem radical_prod_dvd {ι : Type*} {s : Finset ι} {f : ι → M} :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Radical/Basic.lean:351:theorem radical_neg : radical (-a) = radical a :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Radical/Basic.lean:354:theorem radical_neg_one : radical (-1 : R) = 1 := by simp
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Radical/Basic.lean:367:theorem radical_mul_divRadical : radical a * divRadical a = a := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Radical/Basic.lean:371:theorem divRadical_mul_radical : divRadical a * radical a = a := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Radical/Basic.lean:382:theorem eq_divRadical (h : radical a * x = a) : x = divRadical a := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Basic.lean:210:theorem vanishingIdeal_zeroLocus_eq_radical (I : Ideal R) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Basic.lean:216:theorem nilradical_eq_iInf : nilradical R = iInf asIdeal := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Basic.lean:219:@[simp] theorem vanishingIdeal_univ : vanishingIdeal Set.univ = nilradical R := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Basic.lean:223:theorem zeroLocus_radical (I : Ideal R) : zeroLocus (I.radical : Set R) = zeroLocus I :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/ZariskisMainTheorem.lean:524:        (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/IsPrimary.lean:92:theorem IsPrimary.isPrime_radical_colon (hI : S.IsPrimary) : (S.colon .univ).radical.IsPrime := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/IsPrimary.lean:99:theorem IsPrimary.radical_colon_singleton_of_notMem (hI : S.IsPrimary) {m : M} (hm : m ∉ S) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/IsPrimary.lean:105:theorem IsPrimary.radical_colon_singleton_eq_ite (hS : S.IsPrimary) (m : M) [Decidable (m ∈ S)] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Zero.lean:129:theorem Ring.KrullDimLE.nilradical_eq_maximalIdeal [IsLocalRing R] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Zero.lean:135:theorem IsLocalRing.of_isMaximal_nilradical [(nilradical R).IsMaximal] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Zero.lean:141:theorem Ring.KrullDimLE.of_isMaximal_nilradical [(nilradical R).IsMaximal] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Jacobson/Ring.lean:95:theorem Ideal.radical_eq_jacobson [H : IsJacobsonRing R] (I : Ideal R) : I.radical = I.jacobson :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Basic.lean:133:theorem nilradical_le_jacobson (R) [CommRing R] : nilradical R ≤ Ring.jacobson R :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Basic.lean:136:theorem Ring.jacobson_eq_nilradical_of_krullDimLE_zero (R) [CommRing R] [KrullDimLE 0 R] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Jacobson/Ideal.lean:273:theorem radical_le_jacobson : radical I ≤ jacobson I :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Jacobson/Ideal.lean:315:theorem radical_eq_jacobson_iff_radical_quotient_eq_jacobson_bot :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Jacobson/Ideal.lean:326:    rw [comap_radical, comap_jacobson_of_surjective hf,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Jacobson/Ideal.lean:330:theorem jacobson_radical_eq_jacobson : I.radical.jacobson = I.jacobson :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Jacobson/Ideal.lean:352:theorem isLocal_of_isMaximal_radical {I : Ideal R} (hi : IsMaximal (radical I)) : IsLocal I :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/LocalRing/ResidueField/Fiber.lean:104:/-- The `OrderIso` between the fiber of `PrimeSpectrum S → PrimeSpectrum R` at a prime
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/LocalRing/ResidueField/Fiber.lean:127:/-- The `OrderIso` between the set of primes lying over a prime ideal `p : Ideal R`,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:15:The main statement of the theorem is `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:113:theorem radical_le_vanishingIdeal_zeroLocus (I : Ideal (MvPolynomial σ k)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:171:theorem vanishingIdeal_zeroLocus_eq_radical (I : Ideal (MvPolynomial σ k)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Finiteness/Ideal.lean:50:theorem exists_radical_pow_le_of_fg {R : Type*} [CommSemiring R] (I : Ideal R) (h : I.radical.FG) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Finiteness/Ideal.lean:68:theorem exists_pow_le_of_le_radical_of_fg_radical {R : Type*} [CommSemiring R] {I J : Ideal R}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/MinimalPrime/Basic.lean:86:theorem Ideal.radical_minimalPrimes : I.radical.minimalPrimes = I.minimalPrimes := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/MinimalPrime/Basic.lean:98:theorem Ideal.sInf_minimalPrimes : sInf I.minimalPrimes = I.radical := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/MinimalPrime/Basic.lean:116:theorem Ideal.minimalPrimes_eq_subsingleton (hI : I.IsPrimary) : I.minimalPrimes = {I.radical} := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nilpotent/Lemmas.lean:51:theorem mem_nilradical : x ∈ nilradical R ↔ IsNilpotent x :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nilpotent/Lemmas.lean:54:theorem nilradical_eq_sInf (R : Type*) [CommSemiring R] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nilpotent/Lemmas.lean:62:theorem nilradical_le_prime (J : Ideal R) [H : J.IsPrime] : nilradical R ≤ J :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nilpotent/Lemmas.lean:66:theorem nilradical_eq_zero (R : Type*) [CommSemiring R] [IsReduced R] : nilradical R = 0 :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nilpotent/Lemmas.lean:69:theorem nilradical_eq_bot_iff {R : Type*} [CommSemiring R] : nilradical R = ⊥ ↔ IsReduced R := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/IsPrimary.lean:48:theorem isPrime_radical {I : Ideal R} (hi : I.IsPrimary) : IsPrime (radical I) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/IsPrimary.lean:51:theorem isPrimary_of_isMaximal_radical {I : Ideal R} (hi : IsMaximal (radical I)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/IsPrimary.lean:82:  simp only [mem_comap, map_mul, ← comap_radical]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:159:    refine ⟨this, hsp.trans ((hr.comap f).isRadical.radical_le_iff.mpr ?_)⟩
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/AssociatedPrime/Basic.lean:268:theorem IsAssociatedPrime.eq_radical (hI : I.IsPrimary) (h : IsAssociatedPrime J (R ⧸ I)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Operations.lean:807:theorem mem_radical_iff {r : R} : r ∈ I.radical ↔ ∃ n : ℕ, r ^ n ∈ I := Iff.rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Operations.lean:813:theorem le_radical : I ≤ radical I := fun r hri => ⟨1, (pow_one r).symm ▸ hri⟩
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Operations.lean:816:theorem radical_eq_iff : I.radical = I ↔ I.IsRadical := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Operations.lean:826:theorem radical_top : (radical ⊤ : Ideal R) = ⊤ :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Operations.lean:829:theorem radical_mono (H : I ≤ J) : radical I ≤ radical J := fun _ ⟨n, hrni⟩ => ⟨n, H hrni⟩
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Operations.lean:833:theorem radical_isRadical : (radical I).IsRadical := fun r ⟨n, k, hrnki⟩ =>
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Operations.lean:837:theorem radical_idem : radical (radical I) = radical I :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Operations.lean:842:theorem IsRadical.radical_le_iff (hJ : J.IsRadical) : I.radical ≤ J ↔ I ≤ J :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Operations.lean:845:theorem radical_le_radical_iff : radical I ≤ radical J ↔ I ≤ radical J :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Operations.lean:849:theorem radical_eq_top : radical I = ⊤ ↔ I = ⊤ :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Operations.lean:859:theorem IsPrime.radical (H : IsPrime I) : radical I = I :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Operations.lean:862:theorem mem_radical_of_pow_mem {I : Ideal R} {x : R} {m : ℕ} (hx : x ^ m ∈ radical I) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Operations.lean:875:theorem radical_sup : radical (I ⊔ J) = radical (radical I ⊔ radical J) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Operations.lean:879:theorem radical_inf : radical (I ⊓ J) = radical I ⊓ radical J :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Operations.lean:913:theorem radical_iInf_le {ι} (I : ι → Ideal R) : radical (⨅ i, I i) ≤ ⨅ i, radical (I i) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Operations.lean:919:theorem radical_mul : radical (I * J) = radical I ⊓ radical J := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Operations.lean:928:theorem IsPrime.radical_le_iff (hJ : IsPrime J) : I.radical ≤ J ↔ I ≤ J :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Operations.lean:931:theorem radical_eq_sInf (I : Ideal R) : radical I = sInf { J : Ideal R | I ≤ J ∧ IsPrime J } :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Operations.lean:971:theorem radical_bot_of_noZeroDivisors {R : Type u} [CommSemiring R] [NoZeroDivisors R] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/MinimalPrime/Localization.lean:204:theorem IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Maps.lean:645:theorem comap_radical : comap f (radical K) = radical (comap f K) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Maps.lean:652:  rw [← hK.radical, comap_radical]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Maps.lean:657:theorem map_radical_le : map f (radical I) ≤ radical (map f I) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Maps.lean:1104:theorem map_radical_of_surjective {f : R →+* S} (hf : Function.Surjective f) {I : Ideal R}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/GradedAlgebra/Radical.lean:154:theorem Ideal.IsHomogeneous.radical_eq {I : Ideal A} (hI : I.IsHomogeneous 𝒜) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/GradedAlgebra/Radical.lean:165:theorem Ideal.IsHomogeneous.radical {I : Ideal A} (h : I.IsHomogeneous 𝒜) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/GradedAlgebra/Radical.lean:175:theorem HomogeneousIdeal.coe_radical (I : HomogeneousIdeal 𝒜) :

exec
/bin/bash -lc 'rg -n "ringKrullDim.*TensorProduct|TensorProduct.*ringKrullDim|varietyDim.*prod|zeroLocus.*prod|vanishingIdeal.*union|iSup|iInf|sup.*vanishing|trdeg.*TensorProduct|TensorProduct.*trdeg" /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib -S | head -300' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/TestFunction.lean:295:  exact le_trans (le_iSup₂_of_le K K_sub_Ω le_rfl) originalTop_le
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/TestFunction.lean:332:  simp_rw [topologicalSpace_le_iff, originalTop, iSup₂_le_iff, ← continuous_iff_le_induced,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/Basic.lean:257:  have H (v : AbsoluteValue K ℝ) : ⨆ i, v (x (e i)) = ⨆ i, v (x i) := e.iSup_congr (congrFun rfl)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/Basic.lean:306:private lemma max_eq_iSup {α : Type*} [ConditionallyCompleteLattice α] (a b : α) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/Basic.lean:307:    max a b = iSup ![a, b] :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/Basic.lean:308:  eq_of_forall_ge_iff <| by simp [ciSup_le_iff, Fin.forall_fin_two]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/Basic.lean:313:private lemma hasFiniteMulSupport_iSup_nonarchAbsVal {x : ι → K} (hx : x ≠ 0) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/Basic.lean:320:    refine le_antisymm (ciSup_le fun j ↦ ?_) (ciSup_le fun ⟨j, hj⟩ ↦ Finite.le_ciSup_of_le j le_rfl)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/Basic.lean:323:      exact Real.iSup_nonneg' ⟨⟨i, hi⟩, v.val.nonneg ..⟩
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/Basic.lean:324:    · exact Finite.le_ciSup_of_le ⟨j, h⟩ le_rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/Basic.lean:342:    ← mul_iSup_of_nonneg <| AbsoluteValue.nonneg .., Multiset.prod_map_mul]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/Basic.lean:353:  · refine Finite.le_ciSup_of_le i <| le_of_eq ?_
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/Basic.lean:355:  · refine one_le_finprod fun v ↦ Finite.le_ciSup_of_le i ?_
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/Basic.lean:377:    ciSup_le fun i ↦ Finite.le_ciSup_of_le (f i) le_rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/Basic.lean:379:  · exact finprod_nonneg fun v ↦ Real.iSup_nonneg_of_nonnegHomClass v.val _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/Basic.lean:380:  · exact Multiset.prod_map_nonneg fun v _ ↦ Real.iSup_nonneg_of_nonnegHomClass v _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/Basic.lean:381:  · exact Multiset.prod_map_le_prod_map₀ _ _ (fun v _ ↦ Real.iSup_nonneg_of_nonnegHomClass v _)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/Basic.lean:383:  · exact finprod_le_finprod (hasFiniteMulSupport_iSup_nonarchAbsVal h₀)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/Basic.lean:384:      (fun v ↦ Real.iSup_nonneg_of_nonnegHomClass v.val _)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/Basic.lean:385:      (hasFiniteMulSupport_iSup_nonarchAbsVal hx) fun v ↦ H v.val
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/Basic.lean:402:    refine le_antisymm ?_ <| ciSup_le fun i ↦ Finite.le_ciSup_of_le (.inl i) le_rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/Basic.lean:403:    refine ciSup_le fun j ↦ ?_
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/Basic.lean:405:    | inl i => exact Finite.le_ciSup_of_le i le_rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/Basic.lean:406:    | inr _ => simpa using Real.iSup_nonneg_of_nonnegHomClass v _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/Basic.lean:555:    simpa [this] using max_eq_iSup (v x) 1
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/Basic.lean:590:    exact (pow_left_mono n).map_ciSup_of_continuousAt (continuous_pow n).continuousAt
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/Basic.lean:594:    finprod_pow <| hasFiniteMulSupport_iSup_nonarchAbsVal hx, ← Multiset.prod_map_pow]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/Basic.lean:676:  simp_rw [map_prod, Real.iSup_prod_eq_prod_iSup_of_nonnegHomClass]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/Basic.lean:678:    finprod_prod_comm _ _ fun b _ ↦ hasFiniteMulSupport_iSup_nonarchAbsVal (hx b),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/Basic.lean:714:        (hasFiniteMulSupport_iSup_nonarchAbsVal hx) (hasFiniteMulSupport_iSup_nonarchAbsVal hy)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/Basic.lean:716:  · exact Real.iSup_fun_mul_eq_iSup_mul_iSup_of_nonneg v x y
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/Basic.lean:717:  · exact Real.iSup_fun_mul_eq_iSup_mul_iSup_of_nonneg v.val x y
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:517:  toTopologicalSpace_iInf.symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:519:protected theorem uniformSpace_eq_iInf : (uniformSpace : UniformSpace 𝓓^{n}_{K}(E, F)) =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:521:  UniformSpace.replaceTopology_eq _ toTopologicalSpace_iInf.symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:524:  topologicalAddGroup_iInf fun _ ↦ topologicalAddGroup_induced _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:527:  rw [ContDiffMapSupportedIn.uniformSpace_eq_iInf]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:528:  exact isUniformAddGroup_iInf fun _ ↦ IsUniformAddGroup.comap _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:531:  continuousSMul_iInf fun i ↦ continuousSMul_induced (structureMapLM 𝕜 n i)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:534:  LocallyConvexSpace.iInf fun _ ↦ LocallyConvexSpace.induced _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:545:  cont := continuous_iInf_dom continuous_induced_dom
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:574:    simp_rw [isUniformInducing_iff_uniformSpace, ContDiffMapSupportedIn.uniformSpace_eq_iInf,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:575:      Pi.uniformSpace_eq, comap_iInf, ← comap_comap]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:588:  simp [continuous_iInf_rng, continuous_induced_rng, structureMapCLM]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:642:    withSeminorms_iInf fun i ↦ LinearMap.withSeminorms_induced (norm_withSeminorms _ _) _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:700:  simp [BoundedContinuousFunction.norm_eq_iSup_norm,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:774:  simp [BoundedContinuousFunction.norm_eq_iSup_norm, ContDiffMapSupportedIn.seminorm_apply,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:823:  simp [ContDiffMapSupportedIn.seminorm_apply, BoundedContinuousFunction.norm_eq_iSup_norm,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:29:private lemma Height.iSup_fun_eq_max (f : Fin 2 → ℝ) : iSup f = max (f 0) (f 1) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:31:  exact (max_eq_iSup ..).symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:39:--       for emtpy iSups), which are not known there.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:51:    · exact Finite.le_ciSup_of_le ⟨_, s.mem_insert_self a⟩ le_rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:53:      · simpa using Real.iSup_nonneg_of_nonnegHomClass v _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:54:      exact ciSup_le fun i ↦ Finite.le_ciSup_of_le (⟨i.val, Finset.mem_insert_of_mem i.prop⟩) le_rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:67:lemma AbsoluteValue.iSup_abv_linearMap_apply_le (v : AbsoluteValue K ℝ) (A : ι' × ι → K)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:72:  refine ciSup_le fun j ↦ ?_
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:79:    · exact Real.iSup_nonneg_of_nonnegHomClass v _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:80:    · exact Finite.le_ciSup_of_le (j, i) le_rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:81:    · exact Finite.le_ciSup_of_le i le_rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:85:lemma IsNonarchimedean.iSup_abv_linearMap_apply_le {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:92:  refine ciSup_le fun j ↦ ?_
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:96:    Function.Surjective.iSup_comp (fun i ↦ ⟨⟨i, Finset.mem_univ i⟩, rfl⟩) f
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:98:  refine ciSup_le fun i ↦ ?_
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:100:  · exact Real.iSup_nonneg_of_nonnegHomClass v _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:101:  · exact Finite.le_ciSup_of_le (j, i) le_rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:102:  · exact Finite.le_ciSup_of_le i le_rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:136:  · exact finprod_nonneg fun v ↦ Real.iSup_nonneg_of_nonnegHomClass v.val _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:138:      exact prod_map_nonneg fun v _ ↦ Real.iSup_nonneg_of_nonnegHomClass v _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:141:    refine prod_map_le_prod_map₀ _ _ (fun v _ ↦ Real.iSup_nonneg_of_nonnegHomClass v _) fun v _ ↦ ?_
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:142:    rw [mul_comm (iSup _), ← mul_assoc]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:143:    exact v.iSup_abv_linearMap_apply_le A x
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:148:      (fun v ↦ Real.iSup_nonneg_of_nonnegHomClass v.val _) ?_ fun v ↦ ?_
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:150:    · exact (isNonarchimedean _ v.prop).iSup_abv_linearMap_apply_le A x
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:196:  exact Finite.le_ciSup (fun j ↦ v (x j)) i
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:211:  · exact Real.iSup_nonneg_of_nonnegHomClass v _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:212:  · exact Finite.le_ciSup_of_le (⟨s, hs₁⟩ : p.support) le_rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:215:    exact Finite.le_ciSup (fun j ↦ v (x j)) i
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:241:    Real.iSup_of_isEmpty, zero_le_one, sup_of_le_right]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:244:  simp only [Real.iSup_const_zero, Multiset.map_const', Multiset.prod_replicate, zero_pow_eq]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:256:private lemma hasFiniteMulSupport_iSup_max_iSup_one (h : Nonempty ι') (p : ι' → MvPolynomial ι K) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:259:  refine HasFiniteMulSupport.iSup fun j ↦ ?_
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:271:  · exact finprod_nonneg fun v ↦ Real.iSup_nonneg_of_nonnegHomClass ..
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:272:  · exact prod_map_nonneg fun v _ ↦ iSup_nonneg fun _ ↦ sum_nonneg fun _ _ ↦ by positivity
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:275:    exact prod_map_le_prod_map₀ _ _ (fun v _ ↦ Real.iSup_nonneg_of_nonnegHomClass ..)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:276:      fun v _ ↦ Finite.ciSup_mono (H v)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:279:      (fun v ↦ Real.iSup_nonneg_of_nonnegHomClass ..) (by fun_prop) ?_
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:280:    refine fun v ↦ Finite.ciSup_mono fun j ↦ ?_
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:284:    · exact le_sup_of_le_left <| Finite.le_ciSup_of_le ⟨0, by simp [h₀]⟩ le_rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:306:    iSup_nonneg (fun j ↦ sum_nonneg' <| fun s ↦ by positivity)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:311:    prod_map_nonneg fun _ _ ↦ Real.iSup_nonneg_of_nonnegHomClass ..
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:313:    finprod_nonneg fun _ ↦ Real.iSup_nonneg_of_nonnegHomClass ..
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:315:    finprod_nonneg fun _ ↦ Real.iSup_nonneg_of_nonnegHomClass ..
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:318:    pow_nonneg (Real.iSup_nonneg_of_nonnegHomClass v _) N
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:319:  have HH₂ (f : ι' → ℝ) (j : ι') : f j ≤ ⨆ j, f j := Finite.le_ciSup ..
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:326:    refine prod_map_le_prod_map₀ _ _ (fun _ _ ↦ Real.iSup_nonneg_of_nonnegHomClass ..)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:327:      fun v _ ↦ Real.iSup_le (fun j ↦ ?_) <| mul_nonneg (H₀ v) (HH₁ v)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:334:    have F := hasFiniteMulSupport_iSup_nonarchAbsVal hx
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:337:      (fun _ ↦ Real.iSup_nonneg_of_nonnegHomClass ..) (by fun_prop) fun v ↦ Real.iSup_le
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:342:      · grw [le_max_left (iSup ..) 1]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Height/MvPolynomial.lean:344:    · exact mul_nonneg (iSup_nonneg fun _ ↦ by positivity) <| by simp only [HH₁]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:518:  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf] at A ⊢
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Fourier/AddCircle.lean:182:  rw [ContinuousMap.norm_eq_iSup_norm]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Fourier/AddCircle.lean:185:  exact ciSup_const
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Fourier/PoissonSummation.lean:61:    simp_rw [norm_eq_iSup_norm, restrict_apply, mul_apply, norm_mul, this, one_mul]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/CategoryTheory/MorphismProperty/Limits.lean:655:  le_iSup (f := fun (J : Type w) ↦ W.colimitsOfShape (Discrete J)) J
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/CategoryTheory/MorphismProperty/Limits.lean:659:  simp only [coproducts, iSup_iff]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/CategoryTheory/MorphismProperty/Basic.lean:76:  dsimp [sSup, iSup]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/CategoryTheory/MorphismProperty/Basic.lean:84:lemma iSup_iff {ι : Sort*} (W : ι → MorphismProperty C) {X Y : C} (f : X ⟶ Y) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/CategoryTheory/MorphismProperty/Basic.lean:85:    iSup W f ↔ ∃ i, W i f := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/CategoryTheory/MorphismProperty/Basic.lean:163:lemma toSet_iSup {ι : Type*} (W : ι → MorphismProperty C) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:441:            ciInf_eq_of_forall_ge_of_forall_gt_exists_lt
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:444:        simp_rw [Real.mul_iInf_of_nonneg (norm_nonneg a), mul_add, ← map_smul_eq_mul p, ←
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:447:          Function.Surjective.iInf_congr ((a⁻¹ • ·) : E → E)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:459:      ciInf_le_of_le bddBelow_range_add x <| by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:462:      ciInf_le_of_le bddBelow_range_add 0 <| by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:465:      le_ciInf fun _ => (le_map_add_map_sub a _ _).trans <| add_le_add (hab _) (hac _) }
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:471:    smul_eq_mul, Real.mul_iInf_of_nonneg (NNReal.coe_nonneg _), mul_add]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:497:          rw [iSup_apply, ← @Real.iSup_const_zero s]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:504:          · simp [Real.iSup_of_isEmpty]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:506:          simp only [iSup_apply]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:507:          refine ciSup_le fun i =>
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:511:              (le_ciSup (f := fun i => (Subtype.val i : Seminorm 𝕜 E).toFun x) ⟨q x, ?_⟩ i)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:512:              (le_ciSup (f := fun i => (Subtype.val i : Seminorm 𝕜 E).toFun y) ⟨q y, ?_⟩ i)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:516:          simp only [iSup_apply]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:521:          simp only [iSup_apply]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:523:            Real.smul_iSup_of_nonneg (norm_nonneg a) fun i : s => (i : Seminorm 𝕜 E) x]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:538:      rw [Seminorm.coe_sSup_eq' H, iSup_apply]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:541:        le_ciSup ⟨q x, forall_mem_range.mpr fun i : s => hq (mem_image_of_mem _ i.2) x⟩ ⟨p, hp⟩⟩⟩
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:551:protected theorem coe_iSup_eq {ι : Sort*} {p : ι → Seminorm 𝕜 E} (hp : BddAbove (range p)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:554:  exact iSup_range' (fun p : Seminorm 𝕜 E => (p : E → ℝ)) p
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:558:  rw [Seminorm.coe_sSup_eq hp, iSup_apply]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:560:protected theorem iSup_apply {ι : Sort*} {p : ι → Seminorm 𝕜 E}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:562:  rw [Seminorm.coe_iSup_eq hp, iSup_apply]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:566:  rw [Seminorm.sSup_apply bddAbove_empty, Real.iSup_of_isEmpty]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:573:    dsimp <;> rw [Seminorm.coe_sSup_eq hs₁, iSup_apply]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:575:    exact le_ciSup ⟨q x, forall_mem_range.mpr fun i : s => hq i.2 x⟩ ⟨p, hp⟩
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:576:  · exact ciSup_le fun q => hp q.2 x
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:825:  rw [Finset.inf_eq_iInf]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:830:  rw [Finset.inf_eq_iInf]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:902:theorem closedBall_iSup {ι : Sort*} {p : ι → Seminorm 𝕜 E} (hp : BddAbove (range p)) (e : E)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:905:  · rw [iSup_of_empty', iInter_of_empty, Seminorm.sSup_empty]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:909:    simp only [mem_closedBall, mem_iInter, Seminorm.iSup_apply hp, ciSup_le_iff this]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/CategoryTheory/MorphismProperty/TransfiniteComposition.lean:349:  simp only [transfiniteCompositions, iSup_iff]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/CategoryTheory/MorphismProperty/HasCardinalLT.lean:44:lemma HasCardinalLT.iSup
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/CategoryTheory/MorphismProperty/HasCardinalLT.lean:49:  rw [toSet_iSup]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/ODE/PicardLindelof.lean:420:  have : Nonempty (Icc tmin tmax) := ⟨t₀⟩ -- needed for `ciSup_const`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/ODE/PicardLindelof.lean:422:    |>.dist_eq, dist_eq_norm, ContinuousMap.norm_eq_iSup_norm]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/OpenImmersion.lean:155:lemma image_iSup {ι : Sort*} (s : ι → X.Opens) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/OpenImmersion.lean:160:lemma image_iSup₂ {ι : Sort*} {κ : ι → Sort*} (s : (i : ι) → κ i → X.Opens) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/CategoryTheory/Presentable/Type.lean:71:      le_iSup (fun i ↦ (A i).1)⟩)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Restrict.lean:192:    rw [Opens.mem_iSup] at hx
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Restrict.lean:319:def Scheme.Opens.iSupOpenCover {J : Type*} {X : Scheme} (U : J → X.Opens) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Restrict.lean:323:  f j := X.homOfLE (le_iSup _ _)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Restrict.lean:327:    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp x.2
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/CategoryTheory/Presentable/Directed.lean:236:def Diagram.iSup {ι : Type*} (D : ι → Diagram J κ) (hι : HasCardinalLT ι κ) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/CategoryTheory/Presentable/Directed.lean:241:    simp only [MorphismProperty.iSup_iff, iSup_apply, iSup_Prop_eq] at hf ⊢
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/CategoryTheory/Presentable/Directed.lean:245:    simp only [MorphismProperty.iSup_iff, iSup_apply, iSup_Prop_eq] at hf ⊢
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/CategoryTheory/Presentable/Directed.lean:248:  hW := .iSup (fun i ↦ (D i).hW) hι
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/CategoryTheory/Presentable/Directed.lean:249:  hP := .iSup (fun i ↦ (D i).hP) hι
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/CategoryTheory/Presentable/Directed.lean:326:  (Diagram.iSup (fun i ↦ (D i).toDiagram) hι).sup (.single m)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/CategoryTheory/Presentable/Directed.lean:337:    · simp only [MorphismProperty.iSup_iff] at hf
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/CategoryTheory/Presentable/Directed.lean:345:    · simp only [MorphismProperty.iSup_iff] at hf
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/CategoryTheory/Presentable/Directed.lean:359:  · simp only [MorphismProperty.iSup_iff] at hf
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/CategoryTheory/Presentable/Directed.lean:384:        · simp only [MorphismProperty.iSup_iff] at hf
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/CategoryTheory/Presentable/Directed.lean:403:        · simp only [Diagram.iSup_W, MorphismProperty.iSup_iff] at hf
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/CategoryTheory/Presentable/Directed.lean:421:    · exact le_trans (le_trans (le_trans (by rfl) (le_iSup _ i)) le_sup_left) le_sup_left
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/CategoryTheory/Presentable/Directed.lean:422:    · exact le_trans (le_trans (by rfl) (le_iSup _ i)) le_sup_left)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Functorial.lean:170:  · rw [map, ← le_support_iff_le_vanishingIdeal, TopologicalSpace.Closeds.closure_le]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Functorial.lean:173:      range_subschemeι, coe_support_vanishingIdeal]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Functorial.lean:174:  · simp [le_map_iff_comap_le, ← le_support_iff_le_vanishingIdeal, ← Set.image_subset_iff,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Spectrum.lean:263:    exact iSup_le_iSup_of_subset (AlgHom.spectrum_apply_subset ψ s)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:32:  `support` and `vanishingIdeal` forms a Galois connection.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:100:      simp only [this, iSup_apply, Ideal.map_iSup, map_ideal_basicOpen, implies_true] }
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:188:lemma ideal_iSup {ι : Type*} {I : ι → IdealSheafData X} : (iSup I).ideal = ⨆ i, (I i).ideal := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:195:lemma ideal_biInf {ι : Type*} (I : ι → IdealSheafData X) {s : Set ι} (hs : s.Finite) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:198:  simp only [iInf_insert, e, ideal_inf]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:201:lemma ideal_iInf {ι : Type*} (I : ι → IdealSheafData X) [Finite ι] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:203:  simpa using ideal_biInf I Set.finite_univ
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:241:lemma le_of_iSup_eq_top {I J : X.IdealSheafData} {ι : Type*}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:248:    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hU.ge (Set.mem_univ x))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:252:    rw [← V.2.self_le_iSup_basicOpen_iff]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:253:    exact fun x hxV ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨_, _, rfl⟩, hxr ⟨x, hxV⟩⟩
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:268:lemma ext_of_iSup_eq_top {I J : X.IdealSheafData} {ι : Type*}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:271:  (le_of_iSup_eq_top U hU (by aesop)).antisymm (le_of_iSup_eq_top U hU (by aesop))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:319:  rw [TopologicalSpace.IsOpenCover.isClosed_iff_coe_preimage (iSup_affineOpens_eq_top X)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:612:lemma le_support_iff_le_vanishingIdeal {I : X.IdealSheafData} {Z : Closeds X} :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:613:    Z ≤ I.support ↔ I ≤ vanishingIdeal Z := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:625:/-- `support` and `vanishingIdeal` forms a Galois connection.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:627:lemma gc : @GaloisConnection X.IdealSheafData (Closeds X)ᵒᵈ _ _ (support ·) (vanishingIdeal ·) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:628:  fun _ _ ↦ le_support_iff_le_vanishingIdeal
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:648:  rw [← support_bot, vanishingIdeal_support, nilradical]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:650:@[simp] lemma vanishingIdeal_iSup {ι : Sort*} (Z : ι → Closeds X) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:651:    vanishingIdeal (iSup Z) = ⨅ i, vanishingIdeal (Z i) := gc.u_iInf
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:662:@[simp] lemma support_iSup {ι : Sort*} (I : ι → X.IdealSheafData) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:663:    (iSup I).support = ⨅ i, (I i).support := gc.l_iSup
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:680:  rw [← top_le_iff, le_support_iff_le_vanishingIdeal,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:774:lemma Hom.iInf_ker_openCover_map_comp_apply
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:777:  refine le_antisymm ?_ (le_iInf fun i ↦ (𝒰.f i).le_ker_comp f U)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:791:  simpa [Scheme.Hom.appLE] using ideal_ker_le _ _ (Ideal.mem_iInf.mp hs i)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:793:lemma Hom.iInf_ker_openCover_map_comp (f : X ⟶ Y) [QuasiCompact f] (𝒰 : X.OpenCover) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:795:  refine le_antisymm ?_ (le_iInf fun i ↦ (𝒰.f i).le_ker_comp f)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:796:  refine iInf_le_iff.mpr fun I hI U ↦ ?_
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:797:  rw [← f.iInf_ker_openCover_map_comp_apply 𝒰, le_iInf_iff]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:813:  simp only [Set.iUnion_inter, coe_support_inter, ← f.iInf_ker_openCover_map_comp_apply 𝒰,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:814:    Scheme.zeroLocus_iInf_of_nonempty]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Subscheme.lean:431:  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsPreimmersion)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Subscheme.lean:432:    _ (iSup_affineOpens_eq_top X)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Subscheme.lean:511:  idx x := (X.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top X)).idx x.1
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Subscheme.lean:513:    let U := (X.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top X)).idx x.1
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Subscheme.lean:515:      (X.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top X)).covers x.1
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Subscheme.lean:684:  Cover.glueMorphisms ((Y.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top Y)).pullback₁ f)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Subscheme.lean:696:  apply Cover.hom_ext ((Y.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top Y)).pullback₁ f)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/NumberTheory/Harmonic/EulerMascheroni.lean:132:  have := tendsto_atTop_ciSup strictMono_eulerMascheroniSeq.monotone ?_
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Limits.lean:322:  obtain ⟨i, y, rfl⟩ := by simpa only [Opens.iSup_mk, Opens.mem_mk, Set.mem_iUnion] using this
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Limits.lean:429:  · simpa [← WalkingPair.equivBool.symm.iSup_comp, iSup_bool_eq, ← codisjoint_iff] using hf.2
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Limits.lean:660:/-- A version with more restrictive universes. See `IsAffineOpen.iSup_of_disjoint`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Limits.lean:661:private lemma IsAffineOpen.iSup_of_disjoint_aux [Finite ι] {U : ι → X.Opens}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Limits.lean:663:    IsAffineOpen (iSup U) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Limits.lean:674:lemma IsAffineOpen.iSup_of_disjoint [Finite σ] {U : σ → X.Opens}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Limits.lean:676:    IsAffineOpen (iSup U) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Limits.lean:679:  rw [← e.symm.iSup_congr fun _ ↦ rfl]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Limits.lean:680:  exact .iSup_of_disjoint_aux (by simp [*]) fun i j h ↦ hU' (e.symm.injective.ne h)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Limits.lean:684:lemma IsAffineOpen.biSup_of_disjoint {s : Set σ} (hs : s.Finite)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Limits.lean:687:  rw [← iSup_subtype'']
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Limits.lean:689:  exact .iSup_of_disjoint (by simpa) fun i j e ↦ hU' i.2 j.2 (by aesop)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Limits.lean:695:  convert iSup_of_disjoint (U := fun i : Unit ⊕ Unit ↦ i.elim (fun _ ↦ U) (fun _ ↦ V)) (by simp_all)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Limits.lean:702:    .iSup_of_disjoint (fun i ↦ .of_subsingleton Set.subsingleton_singleton)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Continuity.lean:331:  simp only [nhdsSet_iUnion, mem_iSup] at hs'
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Continuity.lean:500:  simp only [nhdsSet_iUnion, mem_iSup] at hs'
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Continuity.lean:840:  simp only [nhdsSet_iUnion, mem_iSup] at hs'
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Continuity.lean:1023:  simp only [nhdsSet_iUnion, mem_iSup] at hs'
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:114:theorem coe_iSup_of_directed [Nonempty ι] (dir : Directed (· ≤ ·) t) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:115:    ↑(iSup t) = ⋃ i, (t i : Set L) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:117:    { __ := Subalgebra.copy _ _ (Subalgebra.coe_iSup_of_directed dir).symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:120:  have : iSup t = M := le_antisymm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:121:    (iSup_le fun i ↦ le_iSup (fun i ↦ (t i : Set L)) i) (Set.iUnion_subset fun _ ↦ le_iSup t _)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:124:theorem toSubalgebra_iSup_of_directed (dir : Directed (· ≤ ·) t) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:125:    (iSup t).toSubalgebra = ⨆ i, (t i).toSubalgebra := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:127:  · simp_rw [iSup_of_empty, bot_toSubalgebra]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:128:  · exact SetLike.ext' ((coe_iSup_of_directed dir).trans (Subalgebra.coe_iSup_of_directed dir).symm)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:130:instance finiteDimensional_iSup_of_finite [h : Finite ι] [∀ i, FiniteDimensional K (t i)] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:132:  rw [← iSup_univ]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:135:    rw [iSup_emptyset]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:138:    rw [iSup_insert]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:141:/-- See `finiteDimensional_iSup_of_finset'` for a stronger version,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:143:instance finiteDimensional_iSup_of_finset
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:146:  iSup_subtype'' s t ▸ IntermediateField.finiteDimensional_iSup_of_finite
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:148:theorem finiteDimensional_iSup_of_finset'
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:152:  iSup_subtype'' s t ▸ IntermediateField.finiteDimensional_iSup_of_finite
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:155:theorem isSplittingField_iSup {p : ι → K[X]}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:159:  have hF : ∀ i ∈ s, t i ≤ F := fun i hi ↦ le_iSup_of_le i (le_iSup (fun _ ↦ t i) hi)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:163:  simp only [rootSet_prod p s h0, ← Set.iSup_eq_iUnion, (@gc K _ L _ _).l_iSup₂]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:164:  exact iSup_congr fun i ↦ iSup_congr fun hi ↦ (h i hi).2
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:202:    adjoin_simple_le_iff, sSup_eq_iSup', ← exists_prop]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:205:  rwa [← SetLike.mem_coe, coe_iSup_of_directed hs.directed_val, mem_iUnion, Subtype.exists] at hx
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:210:  rw [← biSup_adjoin_simple]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:211:  simp_rw [Finset.mem_coe, ← Finset.sup_eq_iSup]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:223:        sSup_image.trans <| (biSup_adjoin_simple _).trans <|
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:226:theorem exists_finset_of_mem_iSup {ι : Type*} {f : ι → IntermediateField F E} {x : E}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:228:  have := (adjoin_simple_isCompactElement x).exists_finset_of_le_iSup (IntermediateField F E) f
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:234:  refine exists_finset_of_mem_iSup (SetLike.le_def.mp (iSup_le fun i x h ↦ ?_) hx)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:235:  exact SetLike.le_def.mp (le_iSup_of_le ⟨i, x, h⟩ (by simp)) (mem_adjoin_simple_self F x)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:240:  refine exists_finset_of_mem_iSup (SetLike.le_def.mp (iSup_le (fun i x1 hx1 => ?_)) hx)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:241:  refine SetLike.le_def.mp (le_iSup_of_le ⟨i, x1, hx1⟩ ?_)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:249:  simp_rw [← biSup_adjoin_simple S, ← iSup_subtype''] at hx
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:250:  obtain ⟨s, hx'⟩ := exists_finset_of_mem_iSup hx
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:253:  simp_rw [Finset.coe_image, iSup_le_iff, adjoin_le_iff]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:567:theorem isAlgebraic_iSup {ι : Type*} {t : ι → IntermediateField K L}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:580:  rw [← biSup_adjoin_simple, ← iSup_subtype'']
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:581:  exact isAlgebraic_iSup fun x ↦ isAlgebraic_adjoin_simple (hS x x.2)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:585:A direct corollary of `finiteDimensional_iSup_of_finite`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:588:  rw [← biSup_adjoin_simple, ← iSup_subtype'']
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:590:  exact finiteDimensional_iSup_of_finite
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:186:theorem coe_iInf {ι : Sort*} (S : ι → IntermediateField F E) : (↑(iInf S) : Set E) = ⋂ i, S i := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:187:  simp [iInf]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:190:theorem iInf_toSubalgebra {ι : Sort*} (S : ι → IntermediateField F E) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:191:    (iInf S).toSubalgebra = ⨅ i, (S i).toSubalgebra :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:192:  SetLike.coe_injective <| by simp [iInf]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:195:theorem iInf_toSubfield {ι : Sort*} (S : ι → IntermediateField F E) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:196:    (iInf S).toSubfield = ⨅ i, (S i).toSubfield :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:197:  SetLike.coe_injective <| by simp [iInf]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:200:theorem iSup_toSubfield {ι : Sort*} [Nonempty ι] (S : ι → IntermediateField F E) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:201:    (iSup S).toSubfield = ⨆ i, (S i).toSubfield := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:202:  simp only [iSup, Set.range_nonempty, sSup_toSubfield, ← Set.range_comp, Function.comp_def]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:282:theorem map_iSup {ι : Sort*} (f : E →ₐ[F] K) (s : ι → IntermediateField F E) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:283:    (iSup s).map f = ⨆ i, (s i).map f :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:284:  (gc_map_comap f).l_iSup
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:289:theorem map_iInf {ι : Sort*} [Nonempty ι] (f : E →ₐ[F] K) (s : ι → IntermediateField F E) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:290:    (iInf s).map f = ⨅ i, (s i).map f := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:457:  gc.l_iSup
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:459:theorem iSup_eq_adjoin {ι} (f : ι → IntermediateField F E) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:585:theorem biSup_adjoin_simple : ⨆ x ∈ S, F⟮x⟯ = adjoin F S := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:586:  rw [← iSup_subtype'', ← gc.l_iSup, iSup_subtype'']; congr; exact S.biUnion_of_singleton
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:670:theorem fg_iSup {ι : Sort*} [Finite ι] {S : ι → IntermediateField F E} (h : ∀ i, (S i).FG) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/PrimitiveElement.lean:284:  have hfin := finiteDimensional_iSup_of_finite (t := fun K : IF ↦ K.1)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/PrimitiveElement.lean:286:    le_iSup (fun K : IF ↦ K.1) ⟨F⟮x⟯, x, rfl⟩ <| mem_adjoin_simple_self F x
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/CardinalEmb.lean:164:theorem iSup_adjoin_eq_top : ⨆ i : ι, E⟮<i⟯ = ⊤ := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/CardinalEmb.lean:167:  refine le_iSup (α := IntermediateField F E) _ (i⁺) (subset_adjoin _ _ ⟨i, ?_, rfl⟩)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/CardinalEmb.lean:266:theorem iSup_filtration : ⨆ j : Iio i, filtration j = filtration i := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory/CardinalEmb.lean:268:  · rw [← range_coe, iSup_range']; exact iSup_adjoin_eq_top

codex
Read-only access to the sibling Lean checkout works. I’ve confirmed it is the pinned Mathlib install, so I’ll base the verdict on those sources.
exec
/bin/bash -lc "sed -n '1,260p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Basic.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li, Jujian Zhang
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic  -- shake: keep (used in `proof_wanted` only)
public import Mathlib.Order.KrullDimension
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Jacobson.Radical
public import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Krull dimensions of (commutative) rings

Given a commutative ring, its ring-theoretic Krull dimension is the order-theoretic Krull dimension
of its prime spectrum. Unfolding this definition, it is the length of the longest sequence(s) of
prime ideals ordered by strict inclusion.
-/

@[expose] public section

open Order

/--
The ring-theoretic Krull dimension is the Krull dimension of its spectrum ordered by inclusion.
-/
noncomputable def ringKrullDim (R : Type*) [CommSemiring R] : WithBot ℕ∞ :=
  krullDim (PrimeSpectrum R)

/-- Type class for rings with krull dimension at most `n`. -/
abbrev Ring.KrullDimLE (n : ℕ) (R : Type*) [CommSemiring R] : Prop :=
  Order.KrullDimLE n (PrimeSpectrum R)

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

lemma Ring.krullDimLE_iff {n : ℕ} :
    KrullDimLE n R ↔ ringKrullDim R ≤ n := Order.krullDimLE_iff n (PrimeSpectrum R)

@[nontriviality]
lemma ringKrullDim_eq_bot_of_subsingleton [Subsingleton R] :
    ringKrullDim R = ⊥ :=
  krullDim_eq_bot

lemma ringKrullDim_nonneg_of_nontrivial [Nontrivial R] :
    0 ≤ ringKrullDim R :=
  krullDim_nonneg

/-- If `f : R →+* S` is surjective, then `ringKrullDim S ≤ ringKrullDim R`. -/
theorem ringKrullDim_le_of_surjective (f : R →+* S) (hf : Function.Surjective f) :
    ringKrullDim S ≤ ringKrullDim R :=
  krullDim_le_of_strictMono (fun I ↦ ⟨Ideal.comap f I.asIdeal, inferInstance⟩)
    (Monotone.strictMono_of_injective (fun _ _ hab ↦ Ideal.comap_mono hab)
      (fun _ _ h => PrimeSpectrum.ext_iff.mpr <| Ideal.comap_injective_of_surjective f hf <| by
        simpa using h))

/-- If `I` is an ideal of `R`, then `ringKrullDim (R ⧸ I) ≤ ringKrullDim R`. -/
theorem ringKrullDim_quotient_le {R : Type*} [CommRing R] (I : Ideal R) :
    ringKrullDim (R ⧸ I) ≤ ringKrullDim R :=
  ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective

/-- If `R` and `S` are isomorphic, then `ringKrullDim R = ringKrullDim S`. -/
theorem ringKrullDim_eq_of_ringEquiv (e : R ≃+* S) :
    ringKrullDim R = ringKrullDim S :=
  le_antisymm (ringKrullDim_le_of_surjective e.symm e.symm.surjective)
    (ringKrullDim_le_of_surjective e e.surjective)

alias RingEquiv.ringKrullDim := ringKrullDim_eq_of_ringEquiv

/-- A ring has finite Krull dimension if its `PrimeSpectrum` is
finite-dimensional (and non-empty). -/
abbrev FiniteRingKrullDim (R : Type*) [CommSemiring R] :=
  FiniteDimensionalOrder (PrimeSpectrum R)

lemma ringKrullDim_ne_top [FiniteRingKrullDim R] :
    ringKrullDim R ≠ ⊤ := krullDim_ne_top_of_finiteDimensionalOrder

lemma ringKrullDim_lt_top [FiniteRingKrullDim R] :
    ringKrullDim R < ⊤ := ringKrullDim_ne_top.lt_top

lemma ringKrullDim_ne_bot [FiniteRingKrullDim R] :
    ringKrullDim R ≠ ⊥ := krullDim_ne_bot_of_finiteDimensionalOrder

lemma finiteRingKrullDim_iff_ne_bot_and_top :
    FiniteRingKrullDim R ↔ (ringKrullDim R ≠ ⊥ ∧ ringKrullDim R ≠ ⊤) :=
  (Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top (α := PrimeSpectrum R))

lemma Nontrivial.of_finiteRingKrullDim [FiniteRingKrullDim R] : Nontrivial R := by
  rw [← PrimeSpectrum.nonempty_iff_nontrivial]
  exact LTSeries.nonempty_of_finiteDimensionalOrder _

proof_wanted MvPolynomial.fin_ringKrullDim_eq_add_of_isNoetherianRing
    [IsNoetherianRing R] (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) R) = ringKrullDim R + n

section Zero

-- See `Mathlib/RingTheory/KrullDimension/Zero.lean` for further results.

lemma Ring.krullDimLE_zero_iff : Ring.KrullDimLE 0 R ↔ ∀ I : Ideal R, I.IsPrime → I.IsMaximal := by
  simp_rw [Ring.KrullDimLE, Order.krullDimLE_iff, Nat.cast_zero,
    Order.krullDim_nonpos_iff_forall_isMax,
    (PrimeSpectrum.equivSubtype R).forall_congr_left, Subtype.forall, PrimeSpectrum.isMax_iff]
  rfl

lemma Ring.KrullDimLE.mk₀ (H : ∀ I : Ideal R, I.IsPrime → I.IsMaximal) : Ring.KrullDimLE 0 R := by
  rwa [Ring.krullDimLE_zero_iff]

lemma Ideal.isMaximal_of_isPrime [Ring.KrullDimLE 0 R] (I : Ideal R) [I.IsPrime] : I.IsMaximal :=
  Ring.krullDimLE_zero_iff.mp ‹_› I ‹_›

/-- Also see `Ideal.IsPrime.isMaximal` for the analogous statement for Dedekind domains. -/
lemma Ideal.IsPrime.isMaximal' [Ring.KrullDimLE 0 R] {I : Ideal R} (hI : I.IsPrime) : I.IsMaximal :=
  I.isMaximal_of_isPrime

instance (priority := 100) (I : Ideal R) [I.IsPrime] [Ring.KrullDimLE 0 R] : I.IsMaximal :=
  I.isMaximal_of_isPrime

lemma Ideal.isMaximal_iff_isPrime [Ring.KrullDimLE 0 R] {I : Ideal R} : I.IsMaximal ↔ I.IsPrime :=
  ⟨IsMaximal.isPrime, fun _ ↦ inferInstance⟩

lemma Ideal.mem_minimalPrimes_of_krullDimLE_zero [Ring.KrullDimLE 0 R]
    (I : Ideal R) [I.IsPrime] : I ∈ minimalPrimes R :=
  minimalPrimes_eq_minimals (R := R) ▸
    ⟨‹_›, fun J hJ hJI ↦ (IsMaximal.eq_of_le inferInstance IsPrime.ne_top' hJI).ge⟩

lemma Ideal.mem_minimalPrimes_iff_isPrime [Ring.KrullDimLE 0 R] {I : Ideal R} :
    I ∈ minimalPrimes R ↔ I.IsPrime :=
  ⟨(·.1.1), fun _ ↦ I.mem_minimalPrimes_of_krullDimLE_zero⟩

theorem nilradical_le_jacobson (R) [CommRing R] : nilradical R ≤ Ring.jacobson R :=
  nilradical_eq_sInf R ▸ le_sInf fun _I hI ↦ sInf_le (Ideal.IsMaximal.isPrime ⟨hI⟩)

theorem Ring.jacobson_eq_nilradical_of_krullDimLE_zero (R) [CommRing R] [KrullDimLE 0 R] :
    jacobson R = nilradical R :=
  (nilradical_le_jacobson R).antisymm' <| nilradical_eq_sInf R ▸ le_sInf fun I (_ : I.IsPrime) ↦
    sInf_le Ideal.IsMaximal.out

end Zero

section One

instance [Ring.KrullDimLE 0 R] : Ring.KrullDimLE 1 R := .mono zero_le_one _

lemma Ring.krullDimLE_one_iff : Ring.KrullDimLE 1 R ↔
    ∀ I : Ideal R, I.IsPrime → I ∈ minimalPrimes R ∨ I.IsMaximal := by
  simp_rw [Ring.KrullDimLE, Order.krullDimLE_iff, Nat.cast_one,
    Order.krullDim_le_one_iff, (PrimeSpectrum.equivSubtype R).forall_congr_left,
    Subtype.forall, PrimeSpectrum.isMax_iff, PrimeSpectrum.isMin_iff]
  rfl

lemma Ring.KrullDimLE.mk₁ (H : ∀ I : Ideal R, I.IsPrime → I ∈ minimalPrimes R ∨ I.IsMaximal) :
    Ring.KrullDimLE 1 R := by
  rwa [Ring.krullDimLE_one_iff]

lemma Ring.krullDimLE_one_iff_of_isPrime_bot [(⊥ : Ideal R).IsPrime] :
    Ring.KrullDimLE 1 R ↔ ∀ I : Ideal R, I ≠ ⊥ → I.IsPrime → I.IsMaximal := by
  letI : OrderBot (PrimeSpectrum R) := { bot := ⟨⊥, ‹_›⟩, bot_le I := bot_le (a := I.1) }
  simp_rw [Ring.KrullDimLE, Order.krullDimLE_iff, Nat.cast_one,
    Order.krullDim_le_one_iff_forall_isMax, (PrimeSpectrum.equivSubtype R).forall_congr_left,
    Subtype.forall, PrimeSpectrum.isMax_iff, forall_comm (α := _ ≠ ⊥),
    ne_eq, PrimeSpectrum.ext_iff]
  rfl

lemma Ring.krullDimLE_one_iff_of_noZeroDivisors [NoZeroDivisors R] :
    Ring.KrullDimLE 1 R ↔ ∀ I : Ideal R, I ≠ ⊥ → I.IsPrime → I.IsMaximal := by
  cases subsingleton_or_nontrivial R
  · exact iff_of_true inferInstance fun I h ↦ (h <| Subsingleton.elim ..).elim
  exact Ring.krullDimLE_one_iff_of_isPrime_bot

/-- Alternative constructor for `Ring.KrullDimLE 1`, convenient for domains. -/
lemma Ring.KrullDimLE.mk₁' (H : ∀ I : Ideal R, I ≠ ⊥ → I.IsPrime → I.IsMaximal) :
    Ring.KrullDimLE 1 R := by
  by_cases hR : (⊥ : Ideal R).IsPrime
  · rwa [Ring.krullDimLE_one_iff_of_isPrime_bot]
  suffices Ring.KrullDimLE 0 R from inferInstance
  exact .mk₀ fun I hI ↦ H I (fun e ↦ hR (e ▸ hI)) hI

end One

exec
/bin/bash -lc 'rg -n "def ringKrullDim|theorem ringKrullDim|lemma ringKrullDim|ringKrullDim_quotient|orderIso|PrimeSpectrum.*quotient|quotient.*PrimeSpectrum|comap.*quotient" /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Algebra/Order -S | head -500' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Algebra/Order/Hom/Monoid.lean:522:theorem coe_orderIso (f : α ≃*o β) : ((f : α →o β) : α → β) = f :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Algebra/Order/Hom/Monoid.lean:569:theorem coe_trans_orderIso (f : α ≃*o β) (g : β ≃*o γ) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Algebra/Order/Hom/Ring.lean:369:theorem coe_orderIso_refl : (OrderRingIso.refl α : α ≃o α) = OrderIso.refl α :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Length.lean:113:  rw [Order.height_eq_krullDim_Iic, coe_length, Order.krullDim_eq_of_orderIso (Submodule.mapIic _)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Length.lean:119:    Order.krullDim_eq_of_orderIso (Submodule.comapMkQRelIso N)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Length.lean:125:    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap e)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Length.lean:133:    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f Function.bijective_id)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/SimpleModule/Isotypic.lean:120:  rw [Subtype.forall', ← (Submodule.MapSubtype.orderIso N).forall_congr_right]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/SimpleModule/Isotypic.lean:122:  simp_rw [Submodule.MapSubtype.orderIso, Equiv.coe_fn_mk, ← (e _).isSimpleModule_iff]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/SimpleModule/Isotypic.lean:127:  rw [Subtype.forall', ← (Submodule.MapSubtype.orderIso N).forall_congr_right]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/SimpleModule/Isotypic.lean:129:  simp_rw [Submodule.MapSubtype.orderIso, Equiv.coe_fn_mk, ← (e _).isSimpleModule_iff,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/SimpleModule/Basic.lean:82:    (Submodule.orderIsoMapComap e.toSemilinearEquiv).complementedLattice
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/SimpleModule/Basic.lean:99:  simp_rw [isSimpleModule_iff, (Submodule.orderIsoMapComapOfBijective l hl).isSimpleOrder_iff]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/SimpleModule/Basic.lean:104:  __ := (Submodule.orderIsoMapComap e).isSimpleOrder
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/SimpleModule/Basic.lean:296:  __ := (Submodule.orderIsoMapComap e.symm).complementedLattice
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/SimpleModule/Basic.lean:327:    (Submodule.orderIsoMapComapOfBijective l hl).complementedLattice_iff]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Algebra/Order/Module/HahnEmbedding.lean:159:  apply (iSupIndep_map_orderIso_iff (Submodule.mapIic u.baseDomain)).mp
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/ChainOfDivisors.lean:25:- `multiplicity_prime_eq_multiplicity_image_by_factor_orderIso` : if there is a
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/ChainOfDivisors.lean:219:theorem factor_orderIso_map_one_eq_bot [IsCancelMulZero N] {m : Associates M} {n : Associates N}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/ChainOfDivisors.lean:229:theorem coe_factor_orderIso_map_eq_one_iff [IsCancelMulZero N]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/ChainOfDivisors.lean:235:    conv_rhs => rw [← factor_orderIso_map_one_eq_bot d.symm]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/ChainOfDivisors.lean:238:    conv_rhs => rw [← factor_orderIso_map_one_eq_bot d]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/ChainOfDivisors.lean:247:theorem pow_image_of_prime_by_factor_orderIso_dvd
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/ChainOfDivisors.lean:279:theorem map_prime_of_factor_orderIso {m p : Associates M} {n : Associates N} (hn : n ≠ 0)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/ChainOfDivisors.lean:286:      coe_factor_orderIso_map_eq_one_iff _ d]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/ChainOfDivisors.lean:306:theorem mem_normalizedFactors_factor_orderIso_of_mem_normalizedFactors {m p : Associates M}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/ChainOfDivisors.lean:310:    exists_mem_normalizedFactors_of_dvd hn (map_prime_of_factor_orderIso hn hp d).irreducible
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/ChainOfDivisors.lean:315:theorem emultiplicity_prime_le_emultiplicity_image_by_factor_orderIso {m p : Associates M}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/ChainOfDivisors.lean:324:  apply pow_image_of_prime_by_factor_orderIso_dvd hn hp d (pow_multiplicity_dvd ..)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/ChainOfDivisors.lean:326:theorem emultiplicity_prime_eq_emultiplicity_image_by_factor_orderIso {m p : Associates M}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/ChainOfDivisors.lean:329:  refine le_antisymm (emultiplicity_prime_le_emultiplicity_image_by_factor_orderIso hp d) ?_
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/ChainOfDivisors.lean:336:    emultiplicity_prime_le_emultiplicity_image_by_factor_orderIso
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/ChainOfDivisors.lean:337:      (mem_normalizedFactors_factor_orderIso_of_mem_normalizedFactors hn hp d) d.symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/ChainOfDivisors.lean:404:  refine map_prime_of_factor_orderIso (mk_ne_zero.mpr hn) ?_ _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/ChainOfDivisors.lean:430:    emultiplicity_prime_eq_emultiplicity_image_by_factor_orderIso (mk_ne_zero.mpr hn) ?_
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/TwoSidedIdeal/Operations.lean:372:def orderIsoIdeal : TwoSidedIdeal R ≃o Ideal R where
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/TwoSidedIdeal/Operations.lean:416:@[simps] def TwoSidedIdeal.orderIsoIsTwoSided {R : Type*} [Ring R] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/TwoSidedIdeal/Basic.lean:98:def orderIsoRingCon : TwoSidedIdeal R ≃o RingCon R where
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/TwoSidedIdeal/Basic.lean:108:  orderIsoRingCon.map_rel_iff.symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Valuation/DiscreteValuativeRel.lean:30:lemma nonempty_orderIso_withZeroMul_int_iff :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Valuation/DiscreteValuativeRel.lean:67:      rw [nonempty_orderIso_withZeroMul_int_iff] at H
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:617:    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:659:/-- If we take `J = I.comap f` then `quotientMap` is injective automatically. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:784:lemma comap_map_quotientMk (I J : Ideal R) [I.IsTwoSided] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:787:  simp only [mem_comap, mem_quotient_iff_mem_sup, sup_comm]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Artinian/Module.lean:87:  let e := Submodule.orderIsoMapComapOfBijective l hl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:437:lemma comap_quotientMk_bijective_of_le_nilradical {I : Ideal R} (hle : I ≤ nilradical R) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:660:lemma range_comap_algebraMap_localization_compl_eq_range_comap_quotientMk
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:1167:    (TopologicalSpace.IrreducibleCloseds.orderIsoSubtype' (zeroLocus (I : Set R))).dual))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:1181:    (TopologicalSpace.IrreducibleCloseds.orderIsoSubtype' (PrimeSpectrum R)).dual))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:1288:  Order.krullDim_orderDual.symm.trans <| Order.krullDim_eq_of_orderIso
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Congruence/Hom.lean:351:  (RingCon.congr (hcd.trans comap_eq)).trans <| quotientKerEquivRangeS <| c.mk'.comp f
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Congruence/Hom.lean:566:  (RingCon.congrₐ R (h.trans comap_eq)).trans <| quotientKerEquivRangeₐ ((c.mkₐ _).comp f)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Homeomorph.lean:53:    ⟨h1, (comap_quotientMk_bijective_of_le_nilradical hker).2.comp <|
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/ChevalleyComplexity.lean:354:            ← range_comap_algebraMap_localization_compl_eq_range_comap_quotientMk,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:343:lemma height_le_ringKrullDim_quotient_add_spanFinrank {p I : Ideal R} [p.IsPrime] (h : I ≤ p) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:352:lemma ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank (I : Ideal R)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:358:  exact height_le_ringKrullDim_quotient_add_spanFinrank <|
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:370:lemma Ideal.height_le_ringKrullDim_quotient_add_encard {p : Ideal R} [p.IsPrime]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:372:  refine le_trans (height_le_ringKrullDim_quotient_add_spanFinrank (I := .span s) ?_) ?_
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:381:lemma Ideal.height_le_ringKrullDim_quotient_add_one {r : R} {p : Ideal R} [p.IsPrime]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:383:  convert Ideal.height_le_ringKrullDim_quotient_add_encard {r} (by simpa)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:386:lemma ringKrullDim_le_ringKrullDim_quotient_add_encard (s : Set R) (hs : s ⊆ Ring.jacobson R) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:388:  refine le_trans (ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank (Ideal.span s) ?_) ?_
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:392:lemma ringKrullDim_le_ringKrullDim_quotient_add_card (s : Finset R)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:395:  convert ringKrullDim_le_ringKrullDim_quotient_add_encard s hs
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:474:lemma ringKrullDim_le_spanFinrank_maximalIdeal [IsLocalRing R] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Over.lean:52:theorem comap_eq_of_scalar_tower_quotient [Algebra R S] [Algebra (R ⧸ p) (S ⧸ P)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Noetherian/Basic.lean:248:  let e := Submodule.orderIsoMapComapOfBijective l hl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/MinimalPrime/Basic.lean:170:    simpa [comap_map_quotientMk, hq.1, sup_le_iff] using comap_mono (f := Ideal.Quotient.mk I) h2
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/MinimalPrime/Localization.lean:51:      obtain ⟨h₁, h₂⟩ := ((IsLocalization.AtPrime.orderIsoOfPrime _ p) ⟨q, hq⟩).2
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/SimpleRing/Matrix.lean:22:  simple := letI := Classical.decEq ι; TwoSidedIdeal.orderIsoMatrix |>.symm.isSimpleOrder
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Jacobson/Ring.lean:139:    (comap_bot_le_of_injective _ algebraMap_quotient_injective)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Jacobson/Ring.lean:199:def IsLocalization.orderIsoOfMaximal [IsJacobsonRing R] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Jacobson/Ring.lean:357:    ((eq_bot_iff.2 (comap_bot_le_of_injective f quotientMap_injective)).symm ▸ this)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Jacobson/Ring.lean:362:          (by rwa [comap_comap, hcomm, ← bot_quotient_isMaximal_iff]))).trans _ _ (hφ'.quotient _))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Jacobson/Ring.lean:527:    (T := (R ⧸ comap C P)[X] ⧸ _) _ _ (injective_quotient_le_comap_map P) ?_
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Localization/AtPrime/Basic.lean:144:def orderIsoOfPrime : { p : Ideal S // p.IsPrime } ≃o { p : Ideal R // p.IsPrime ∧ p ≤ I } :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Localization/AtPrime/Basic.lean:145:  (IsLocalization.orderIsoOfPrime I.primeCompl S).trans <| .setCongr _ _ <| show setOf _ = setOf _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Localization/AtPrime/Basic.lean:151:  (PrimeSpectrum.equivSubtype S).trans <| (orderIsoOfPrime S I).trans
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Height.lean:272:    ← Order.height_orderIso (PrimeSpectrum.comapEquiv e.symm) ⟨p, ‹_›⟩]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Height.lean:294:lemma ringKrullDim_le_iff_height_le {R : Type*} [CommRing R] (n : WithBot ℕ∞) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Height.lean:304:lemma ringKrullDim_le_iff_isMaximal_height_le {R : Type*} [CommRing R] (n : WithBot ℕ∞) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Height.lean:318:  let e := IsLocalization.orderIsoOfPrime S A
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Height.lean:321:  exact Order.krullDim_eq_of_orderIso
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/NatInt.lean:95:theorem ringKrullDim_nat : ringKrullDim ℕ = 2 := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/SimpleRing/Principal.lean:23:instance : IsSimpleOrder (Ideal R) := TwoSidedIdeal.orderIsoIdeal.symm.isSimpleOrder
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Zero.lean:53:lemma ringKrullDimZero_iff_ringKrullDim_eq_zero [Nontrivial R] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/SimpleRing/Congr.lean:37:  let e := orderIsoIsTwoSided (R := R)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/SimpleRing/Congr.lean:38:  simp_rw [isSimpleRing_iff, isSimpleOrder_iff, orderIsoRingCon.toEquiv.nontrivial_congr,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/GoingDown.lean:146:    · exact (IsLocalization.AtPrime.orderIsoOfPrime _ Q ⟨Pl, inferInstance⟩).2.2
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/LocalRing.lean:20:lemma ringKrullDim_eq_one_iff_of_isLocalRing_isDomain {R : Type*}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/GoingUp.lean:139:    (p.map (Ideal.Quotient.mk (I.comap f))).eval₂ (Quotient.lift (I.comap f) _ quotient_f)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/OrderOfVanishing.lean:167:  exact (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hx).trans (Order.KrullDimLE.krullDim_le)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Localization/Ideal.lean:232:@[simps] def orderIsoOfPrime :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Localization/Ideal.lean:249:  (PrimeSpectrum.equivSubtype S).trans <| (orderIsoOfPrime M S).trans
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Localization/Ideal.lean:339:  convert (orderIsoOfPrime M S).lt_iff_lt.mpr (show (⟨⊥, Ideal.isPrime_bot⟩ :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:20:- `ringKrullDim_quotient_succ_le_of_nonZeroDivisor`: If `r` is not a zero divisor, then
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:32:lemma ringKrullDim_quotient (I : Ideal R) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:34:  rw [ringKrullDim, Order.krullDim_eq_of_orderIso I.primeSpectrumQuotientOrderIsoZeroLocus]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:36:lemma ringKrullDim_quotient_succ_le_of_nonZeroDivisor
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:47:  rw [ringKrullDim_quotient, Order.krullDim_eq_iSup_length, ringKrullDim,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:60:lemma ringKrullDim_succ_le_of_surjective (f : R →+* S) (hf : Function.Surjective f)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:62:  refine le_trans ?_ (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:68:lemma ringKrullDim_succ_le_ringKrullDim_polynomial :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:75:lemma ringKrullDim_mvPolynomial_of_isEmpty (σ : Type*) [IsEmpty σ] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:80:lemma ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial (σ : Type*) [Finite σ] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:96:lemma ringKrullDim_add_enatCard_le_ringKrullDim_mvPolynomial (σ : Type*) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:120:lemma ringKrullDim_succ_le_ringKrullDim_powerseries :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Field.lean:21:theorem ringKrullDim_eq_zero_of_field (F : Type*) [Field F] : ringKrullDim F = 0 :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Field.lean:24:theorem ringKrullDim_eq_zero_of_isField {F : Type*} [CommRing F] (hF : IsField F) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:120:lemma _root_.ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_jacobson {x : R}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:129:lemma ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors {r : R} (hr : r ∈ nonZeroDivisors R)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:132:  refine le_antisymm (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr) (h ▸ ?_)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:133:  exact Ideal.height_le_ringKrullDim_quotient_add_one hp
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:149:@[deprecated ringKrullDim_le_ringKrullDim_quotient_add_card (since := "2026-01-12")]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:153:  apply ringKrullDim_le_ringKrullDim_quotient_add_card
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:156:@[deprecated ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank (since := "2026-01-12")]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:159:  apply ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:179:lemma _root_.ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim {x : R}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:182:  ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_jacobson reg <| by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:187:lemma _root_.ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:190:  ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Module.lean:49:lemma supportDim_eq_ringKrullDim_quotient_annihilator [Module.Finite R M] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Module.lean:52:  rw [support_eq_zeroLocus, ringKrullDim_quotient]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Module.lean:57:  rw [supportDim_eq_ringKrullDim_quotient_annihilator, this]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Module.lean:67:  rw [supportDim_eq_ringKrullDim_quotient_annihilator, Ideal.annihilator_quotient]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Basic.lean:30:noncomputable def ringKrullDim (R : Type*) [CommSemiring R] : WithBot ℕ∞ :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Basic.lean:43:lemma ringKrullDim_eq_bot_of_subsingleton [Subsingleton R] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Basic.lean:47:lemma ringKrullDim_nonneg_of_nontrivial [Nontrivial R] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Basic.lean:52:theorem ringKrullDim_le_of_surjective (f : R →+* S) (hf : Function.Surjective f) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Basic.lean:60:theorem ringKrullDim_quotient_le {R : Type*} [CommRing R] (I : Ideal R) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Basic.lean:65:theorem ringKrullDim_eq_of_ringEquiv (e : R ≃+* S) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Basic.lean:77:lemma ringKrullDim_ne_top [FiniteRingKrullDim R] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Basic.lean:80:lemma ringKrullDim_lt_top [FiniteRingKrullDim R] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Basic.lean:83:lemma ringKrullDim_ne_bot [FiniteRingKrullDim R] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/DedekindDomain/Dvr.lean:74:  rw [← (IsLocalization.orderIsoOfPrime M Rₘ).lt_iff_lt] at hpP'
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/DedekindDomain/Dvr.lean:76:    ((IsLocalization.orderIsoOfPrime M Rₘ) ⟨p, hpp⟩).2.1
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/DedekindDomain/Dvr.lean:78:    ((IsLocalization.orderIsoOfPrime M Rₘ) ⟨P, hPm.isPrime⟩).2.1
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/DedekindDomain/Dvr.lean:155:    let f := (IsLocalization.orderIsoOfPrime q.primeCompl (Localization.AtPrime q)).symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Polynomial.lean:36:  · rw [show C = (algebraMap R (Polynomial R)) from rfl, Order.krullDim_eq_of_orderIso
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Polynomial.lean:106:lemma ringKrullDim_of_isNoetherianRing : ringKrullDim R[X] = ringKrullDim R + 1 := by

exec
/bin/bash -lc 'rg -n "trdeg_add_eq|trdeg.*TensorProduct|TensorProduct.*trdeg|trdeg_of|Algebra.trdeg" /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/FieldTheory /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory -S | head -500' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/AlgebraicIndependent/Basic.lean:45:@[stacks 030G] def Algebra.trdeg : Cardinal.{v} :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/AlgebraicIndependent/TranscendenceBasis.lean:446:theorem MvPolynomial.trdeg_of_isDomain [IsDomain S] : trdeg S (MvPolynomial ι S) = lift.{v} #ι := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/AlgebraicIndependent/TranscendenceBasis.lean:452:theorem Polynomial.trdeg_of_isDomain [IsDomain R] : trdeg R (Polynomial R) = 1 := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/AlgebraicIndependent/TranscendenceBasis.lean:481:theorem isTranscendenceBasis_of_lift_le_trdeg_of_finite
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/AlgebraicIndependent/TranscendenceBasis.lean:491:theorem isTranscendenceBasis_of_le_trdeg_of_finite {ι : Type w} [Finite ι] (x : ι → A)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/AlgebraicIndependent/TranscendenceBasis.lean:494:  isTranscendenceBasis_of_lift_le_trdeg_of_finite R x (by rwa [lift_id, lift_id])
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/AlgebraicIndependent/TranscendenceBasis.lean:500:  isTranscendenceBasis_of_lift_le_trdeg_of_finite R x le
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/AlgebraicIndependent/TranscendenceBasis.lean:539:@[stacks 030H] theorem lift_trdeg_add_eq [Nontrivial R] [NoZeroDivisors A] [FaithfulSMul R S]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/AlgebraicIndependent/TranscendenceBasis.lean:548:@[stacks 030H] theorem trdeg_add_eq [Nontrivial R] {A : Type v} [CommRing A] [NoZeroDivisors A]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/AlgebraicIndependent/TranscendenceBasis.lean:552:  exact lift_trdeg_add_eq R S A

codex
The key upstream fact is present, but under a slightly different route: `ringKrullDim_quotient` identifies the quotient dimension with the Krull dimension of the corresponding zero-locus in `Spec`, and `zeroLocus_radical` then gives radical-insensitivity. I’m checking whether there is a one-line wrapper already named for radicals.
exec
/bin/bash -lc "sed -n '1,130p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.Algebra.MvPolynomial.CommRing

/-!

# Krull dimension and non-zero-divisors

## Main results
- `ringKrullDim_quotient_succ_le_of_nonZeroDivisor`: If `r` is not a zero divisor, then
  `dim R/r + 1 ≤ dim R`.
- `ringKrullDim_succ_le_ringKrullDim_polynomial`: `dim R + 1 ≤ dim R[X]`.
- `ringKrullDim_add_enatCard_le_ringKrullDim_mvPolynomial`: `dim R + #σ ≤ dim R[σ]`.
-/

public section

open scoped nonZeroDivisors

variable {R S : Type*} [CommRing R] [CommRing S]

lemma ringKrullDim_quotient (I : Ideal R) :
    ringKrullDim (R ⧸ I) = Order.krullDim (PrimeSpectrum.zeroLocus (R := R) I) := by
  rw [ringKrullDim, Order.krullDim_eq_of_orderIso I.primeSpectrumQuotientOrderIsoZeroLocus]

lemma ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    {r : R} (hr : r ∈ R⁰) :
    ringKrullDim (R ⧸ Ideal.span {r}) + 1 ≤ ringKrullDim R := by
  by_cases hr' : Ideal.span {r} = ⊤
  · rw [hr', ringKrullDim_eq_bot_of_subsingleton]
    simp
  have : Nonempty (PrimeSpectrum.zeroLocus (R := R) (Ideal.span {r})) := by
    rwa [Set.nonempty_coe_sort, Set.nonempty_iff_ne_empty, ne_eq,
      PrimeSpectrum.zeroLocus_empty_iff_eq_top]
  have := Ideal.Quotient.nontrivial_iff.mpr hr'
  have := (Ideal.Quotient.mk (Ideal.span {r})).domain_nontrivial
  rw [ringKrullDim_quotient, Order.krullDim_eq_iSup_length, ringKrullDim,
    Order.krullDim_eq_iSup_length, ← WithBot.coe_one, ← WithBot.coe_add,
    ENat.iSup_add, WithBot.coe_le_coe, iSup_le_iff]
  intro l
  obtain ⟨p, hp, hp'⟩ := Ideal.exists_minimalPrimes_le (J := l.head.1.asIdeal) bot_le
  let p' : PrimeSpectrum R := ⟨p, hp.1.1⟩
  have hp' : p' < l.head := lt_of_le_of_ne hp' fun h ↦ Set.disjoint_iff.mp
    (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hp)
    ⟨show r ∈ p by simpa [← h] using l.head.2, hr⟩
  refine le_trans ?_ (le_iSup _ ((l.map Subtype.val (fun _ _ ↦ id)).cons p' hp'))
  simp

/-- If `R →+* S` is surjective whose kernel contains a nonzero divisor, then `dim S + 1 ≤ dim R`. -/
lemma ringKrullDim_succ_le_of_surjective (f : R →+* S) (hf : Function.Surjective f)
    {r : R} (hr : r ∈ R⁰) (hr' : f r = 0) : ringKrullDim S + 1 ≤ ringKrullDim R := by
  refine le_trans ?_ (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr)
  gcongr
  exact ringKrullDim_le_of_surjective (Ideal.Quotient.lift _ f (RingHom.ker f
    |>.span_singleton_le_iff_mem.mpr hr')) (Ideal.Quotient.lift_surjective_of_surjective _ _ hf)

open Polynomial in
lemma ringKrullDim_succ_le_ringKrullDim_polynomial :
    ringKrullDim R + 1 ≤ ringKrullDim R[X] :=
  ringKrullDim_succ_le_of_surjective constantCoeff (⟨C ·, coeff_C_zero⟩)
    X_mem_nonzeroDivisors coeff_X_zero

open MvPolynomial in
@[simp]
lemma ringKrullDim_mvPolynomial_of_isEmpty (σ : Type*) [IsEmpty σ] :
    ringKrullDim (MvPolynomial σ R) = ringKrullDim R :=
  ringKrullDim_eq_of_ringEquiv (isEmptyRingEquiv _ _)

open MvPolynomial in
lemma ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial (σ : Type*) [Finite σ] :
    ringKrullDim R + Nat.card σ ≤ ringKrullDim (MvPolynomial σ R) := by
  induction σ using Finite.induction_empty_option with
  | of_equiv e H =>
    convert ← H using 1
    · rw [Nat.card_congr e]
    · exact ringKrullDim_eq_of_ringEquiv (renameEquiv _ e).toRingEquiv
  | h_empty => simp
  | h_option IH =>
    simp only [Nat.card_eq_fintype_card, Fintype.card_option, Nat.cast_add, Nat.cast_one,
      ← add_assoc] at IH ⊢
    grw [IH, ringKrullDim_succ_le_ringKrullDim_polynomial]
    exact (ringKrullDim_eq_of_ringEquiv (MvPolynomial.optionEquivLeft _ _).toRingEquiv).ge

set_option backward.isDefEq.respectTransparency false in
open MvPolynomial in
lemma ringKrullDim_add_enatCard_le_ringKrullDim_mvPolynomial (σ : Type*) :
    ringKrullDim R + ENat.card σ ≤ ringKrullDim (MvPolynomial σ R) := by
  nontriviality R
  cases finite_or_infinite σ
  · rw [ENat.card_eq_coe_natCard]
    push_cast
    exact ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial _
  · simp only [ENat.card_eq_top_of_infinite, WithBot.coe_top]
    suffices ringKrullDim (MvPolynomial σ R) = ⊤ by simp_all
    rw [WithBot.eq_top_iff_forall_ge]
    intro n
    let ι := Infinite.natEmbedding σ ∘ Fin.val (n := n + 1)
    have := Function.invFun_surjective (f := ι) ((Infinite.natEmbedding σ).2.comp Fin.val_injective)
    refine le_trans ?_ (ringKrullDim_le_of_surjective
      (rename (R := R) _).toRingHom (rename_surjective _ this))
    refine le_trans ?_ (ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial _)
    simp only [ENat.some_eq_coe, Nat.card_eq_fintype_card, Fintype.card_fin, Nat.cast_add,
      Nat.cast_one]
    trans n + 1
    · norm_cast
      simp
    · exact WithBot.le_add_self Order.bot_lt_krullDim.ne' _

open PowerSeries in
lemma ringKrullDim_succ_le_ringKrullDim_powerseries :
    ringKrullDim R + 1 ≤ ringKrullDim (PowerSeries R) :=
  ringKrullDim_succ_le_of_surjective constantCoeff (⟨C ·, rfl⟩)
    MvPowerSeries.X_mem_nonzeroDivisors constantCoeff_X

exec
/bin/bash -lc "sed -n '180,235p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Basic.lean && sed -n '420,455p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
section Gc

variable (R)

/-- `zeroLocus` and `vanishingIdeal` form a Galois connection. -/
theorem gc :
    @GaloisConnection (Ideal R) (Set (PrimeSpectrum R))ᵒᵈ _ _ (fun I => zeroLocus I) fun t =>
      vanishingIdeal t :=
  fun I t => subset_zeroLocus_iff_le_vanishingIdeal t I

/-- `zeroLocus` and `vanishingIdeal` form a Galois connection. -/
theorem gc_set :
    @GaloisConnection (Set R) (Set (PrimeSpectrum R))ᵒᵈ _ _ (fun s => zeroLocus s) fun t =>
      vanishingIdeal t := by
  have ideal_gc : GaloisConnection Ideal.span _ := (Submodule.gi R R).gc
  simpa [zeroLocus_span, Function.comp_def] using ideal_gc.compose (gc R)

theorem subset_zeroLocus_iff_subset_vanishingIdeal (t : Set (PrimeSpectrum R)) (s : Set R) :
    t ⊆ zeroLocus s ↔ s ⊆ vanishingIdeal t :=
  (gc_set R) s t

end Gc

theorem subset_vanishingIdeal_zeroLocus (s : Set R) : s ⊆ vanishingIdeal (zeroLocus s) :=
  (gc_set R).le_u_l s

theorem le_vanishingIdeal_zeroLocus (I : Ideal R) : I ≤ vanishingIdeal (zeroLocus I) :=
  (gc R).le_u_l I

@[simp]
theorem vanishingIdeal_zeroLocus_eq_radical (I : Ideal R) :
    vanishingIdeal (zeroLocus (I : Set R)) = I.radical :=
  Ideal.ext fun f => by
    rw [mem_vanishingIdeal, Ideal.radical_eq_sInf, Submodule.mem_sInf]
    exact ⟨fun h x hx => h ⟨x, hx.2⟩ hx.1, fun h x hx => h x.1 ⟨hx, x.2⟩⟩

theorem nilradical_eq_iInf : nilradical R = iInf asIdeal := by
  apply range_asIdeal R ▸ nilradical_eq_sInf R

@[simp] theorem vanishingIdeal_univ : vanishingIdeal Set.univ = nilradical R := by
  rw [vanishingIdeal, iInf_univ, nilradical_eq_iInf]

@[simp]
theorem zeroLocus_radical (I : Ideal R) : zeroLocus (I.radical : Set R) = zeroLocus I :=
  vanishingIdeal_zeroLocus_eq_radical I ▸ (gc R).l_u_l_eq_l I

theorem subset_zeroLocus_vanishingIdeal (t : Set (PrimeSpectrum R)) :
    t ⊆ zeroLocus (vanishingIdeal t) :=
  (gc R).l_u_le t

theorem zeroLocus_anti_mono {s t : Set R} (h : s ⊆ t) : zeroLocus t ⊆ zeroLocus s :=
  (gc_set R).monotone_l h

theorem zeroLocus_anti_mono_ideal {s t : Ideal R} (h : s ≤ t) :
    zeroLocus (t : Set R) ⊆ zeroLocus (s : Set R) :=
  (gc R).monotone_l h
section SpecOfSurjective

/-! The comap of a surjective ring homomorphism is a closed embedding between the prime spectra. -/


open Function RingHom

variable [CommRing R] [CommRing S]
variable (f : R →+* S)
variable {R}

theorem comap_singleton_isClosed_of_surjective (f : R →+* S) (hf : Function.Surjective f)
    (x : PrimeSpectrum S) (hx : IsClosed ({x} : Set (PrimeSpectrum S))) :
    IsClosed ({comap f x} : Set (PrimeSpectrum R)) :=
  haveI : x.asIdeal.IsMaximal := (isClosed_singleton_iff_isMaximal x).1 hx
  (isClosed_singleton_iff_isMaximal _).2 (Ideal.comap_isMaximal_of_surjective f hf)

lemma comap_quotientMk_bijective_of_le_nilradical {I : Ideal R} (hle : I ≤ nilradical R) :
    Function.Bijective (comap <| Ideal.Quotient.mk I) := by
  refine ⟨comap_injective_of_surjective _ Ideal.Quotient.mk_surjective, ?_⟩
  simpa [← Set.range_eq_univ, range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    zeroLocus_eq_univ_iff]

theorem isClosed_range_comap_of_surjective (hf : Surjective f) :
    IsClosed (Set.range (comap f)) := by
  rw [range_comap_of_surjective _ f hf]
  exact isClosed_zeroLocus _

lemma isClosedEmbedding_comap_of_surjective (hf : Surjective f) : IsClosedEmbedding (comap f) where
  toIsInducing := comap_isInducing_of_surjective S f hf
  injective := comap_injective_of_surjective f hf
  isClosed_range := isClosed_range_comap_of_surjective S f hf

end SpecOfSurjective

section SpecProd

exec
/bin/bash -lc "sed -n '532,558p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/AlgebraicIndependent/TranscendenceBasis.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
    (hx : AlgebraicIndependent R x) (le : trdeg R A ≤ #ι) : IsTranscendenceBasis R x :=
  isTranscendenceBasis_of_lift_trdeg_le_of_finite hx (by rwa [lift_id, lift_id])

end AlgebraicIndependent

variable (R S A)

@[stacks 030H] theorem lift_trdeg_add_eq [Nontrivial R] [NoZeroDivisors A] [FaithfulSMul R S]
    [FaithfulSMul S A] : lift.{w} (trdeg R S) + lift.{v} (trdeg S A) = lift.{v} (trdeg R A) := by
  have ⟨s, hs⟩ := exists_isTranscendenceBasis R S
  have ⟨t, ht⟩ := exists_isTranscendenceBasis S A
  have := (FaithfulSMul.algebraMap_injective S A).noZeroDivisors _ (map_zero _) (map_mul _)
  have := (FaithfulSMul.algebraMap_injective R S).nontrivial
  rw [← hs.cardinalMk_eq_trdeg, ← ht.cardinalMk_eq_trdeg, ← lift_umax.{w}, add_comm,
    ← (hs.sumElim_comp ht).lift_cardinalMk_eq_trdeg, mk_sum, lift_add, lift_lift, lift_lift]

@[stacks 030H] theorem trdeg_add_eq [Nontrivial R] {A : Type v} [CommRing A] [NoZeroDivisors A]
    [Algebra R A] [Algebra S A] [FaithfulSMul R S] [FaithfulSMul S A] [IsScalarTower R S A] :
    trdeg R S + trdeg S A = trdeg R A := by
  rw [← (trdeg R S).lift_id, ← (trdeg S A).lift_id, ← (trdeg R A).lift_id]
  exact lift_trdeg_add_eq R S A

namespace IsTranscendenceBasis

variable {R S} [FaithfulSMul R S] [NoZeroDivisors S] (s : Set ι) (i j : ι) (v : ι → S)

/-- If `s` is a transcendence basis and `j` is algebraic over `s ∪ {i} \ {j}`,

exec
/bin/bash -lc 'rg -n "radical.*ringKrullDim|ringKrullDim.*radical|quotient_radical|radical_quotient|ringKrullDim_quotient.*radical|zeroLocus_radical" /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory -S' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Jacobson/Ideal.lean:315:theorem radical_eq_jacobson_iff_radical_quotient_eq_jacobson_bot :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:88:* `PrimeSpectrum.isClosed_iff_zeroLocus_radical_ideal`, `PrimeSpectrum.isRadical_vanishingIdeal`,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:150:theorem isClosed_iff_zeroLocus_radical_ideal (Z : Set (PrimeSpectrum R)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:153:    ⟨fun ⟨I, hI⟩ => ⟨_, I.radical_isRadical, (zeroLocus_radical I).substr hI⟩, fun ⟨I, _, hI⟩ =>
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:193:  · intro h; rw [← zeroLocus_radical, h, zeroLocus_radical]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:255:  zeroLocus_radical I ▸ isIrreducible_zeroLocus_iff_of_radical _ I.radical_isRadical
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:867:  rw [← zeroLocus_vanishingIdeal_eq_closure, vanishingIdeal_range_comap, zeroLocus_radical]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Basic.lean:223:theorem zeroLocus_radical (I : Ideal R) : zeroLocus (I.radical : Set R) = zeroLocus I :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Basic.lean:255:  rw [nilradical, zeroLocus_radical, Ideal.zero_eq_bot, zeroLocus_bot]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Basic.lean:355:  zeroLocus_radical (I ^ n) ▸ (I.radical_pow hn).symm ▸ zeroLocus_radical I

codex
So for question 1, the answer is yes mathematically and easy in Lean, but there is no obvious prepackaged lemma named exactly `ringKrullDim_quotient_radical` in v4.29. It is a two-rewrite lemma from `ringKrullDim_quotient` and `PrimeSpectrum.zeroLocus_radical`.
exec
/bin/bash -lc "sed -n '455,540p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
section SpecProd

variable {R S} [CommSemiring R] [CommSemiring S]

lemma primeSpectrumProd_symm_inl (x) :
    (primeSpectrumProd R S).symm (.inl x) = comap (RingHom.fst R S) x := by
  ext; simp [Ideal.prod]

lemma primeSpectrumProd_symm_inr (x) :
    (primeSpectrumProd R S).symm (.inr x) = comap (RingHom.snd R S) x := by
  ext; simp [Ideal.prod]

lemma range_comap_fst :
    Set.range (comap (RingHom.fst R S)) = zeroLocus (RingHom.ker (RingHom.fst R S)) := by
  refine Set.ext fun p ↦ ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨I, hI, rfl⟩; exact Ideal.comap_mono bot_le
  obtain ⟨p, hp, eq⟩ | ⟨p, hp, eq⟩ := p.1.ideal_prod_prime.mp p.2
  · exact ⟨⟨p, hp⟩, PrimeSpectrum.ext <| by simpa [Ideal.prod] using eq.symm⟩
  · refine (hp.ne_top <| (Ideal.eq_top_iff_one _).mpr ?_).elim
    simpa [eq] using h (show (0, 1) ∈ RingHom.ker (RingHom.fst R S) by simp)

lemma range_comap_snd :
    Set.range (comap (RingHom.snd R S)) = zeroLocus (RingHom.ker (RingHom.snd R S)) := by
  refine Set.ext fun p ↦ ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨I, hI, rfl⟩; exact Ideal.comap_mono bot_le
  obtain ⟨p, hp, eq⟩ | ⟨p, hp, eq⟩ := p.1.ideal_prod_prime.mp p.2
  · refine (hp.ne_top <| (Ideal.eq_top_iff_one _).mpr ?_).elim
    simpa [eq] using h (show (1, 0) ∈ RingHom.ker (RingHom.snd R S) by simp)
  · exact ⟨⟨p, hp⟩, PrimeSpectrum.ext <| by simpa [Ideal.prod] using eq.symm⟩

lemma isClosedEmbedding_comap_fst : IsClosedEmbedding (comap (RingHom.fst R S)) :=
  (isClosedEmbedding_iff _).mpr ⟨isEmbedding_comap_of_surjective _ _ Prod.fst_surjective, by
    simp_rw [range_comap_fst, isClosed_zeroLocus]⟩

lemma isClosedEmbedding_comap_snd : IsClosedEmbedding (comap (RingHom.snd R S)) :=
  (isClosedEmbedding_iff _).mpr ⟨isEmbedding_comap_of_surjective _ _ Prod.snd_surjective, by
    simp_rw [range_comap_snd, isClosed_zeroLocus]⟩

/-- The prime spectrum of `R × S` is homeomorphic
to the disjoint union of `PrimeSpectrum R` and `PrimeSpectrum S`. -/
noncomputable
def primeSpectrumProdHomeo :
    PrimeSpectrum (R × S) ≃ₜ PrimeSpectrum R ⊕ PrimeSpectrum S := by
  refine ((primeSpectrumProd R S).symm.toHomeomorphOfIsInducing ?_).symm
  refine (IsClosedEmbedding.of_continuous_injective_isClosedMap ?_
    (Equiv.injective _) ?_).isInducing
  · rw [continuous_sum_dom]
    simp only [Function.comp_def, primeSpectrumProd_symm_inl, primeSpectrumProd_symm_inr]
    exact ⟨continuous_comap _, continuous_comap _⟩
  · simp_rw [isClosedMap_sum, primeSpectrumProd_symm_inl, primeSpectrumProd_symm_inr]
    exact ⟨isClosedEmbedding_comap_fst.isClosedMap, isClosedEmbedding_comap_snd.isClosedMap⟩

end SpecProd

section CommSemiring

variable [CommSemiring R] [CommSemiring S]
variable {R S}

section BasicOpen

/-- `basicOpen r` is the open subset containing all prime ideals not containing `r`. -/
def basicOpen (r : R) : TopologicalSpace.Opens (PrimeSpectrum R) where
  carrier := { x | r ∉ x.asIdeal }
  is_open' := ⟨{r}, Set.ext fun _ => Set.singleton_subset_iff.trans <| Classical.not_not.symm⟩

@[simp]
theorem mem_basicOpen (f : R) (x : PrimeSpectrum R) : x ∈ basicOpen f ↔ f ∉ x.asIdeal :=
  Iff.rfl

theorem isOpen_basicOpen {a : R} : IsOpen (basicOpen a : Set (PrimeSpectrum R)) :=
  (basicOpen a).isOpen

@[simp]
theorem basicOpen_eq_zeroLocus_compl (r : R) :
    (basicOpen r : Set (PrimeSpectrum R)) = (zeroLocus {r})ᶜ :=
  Set.ext fun x => by simp only [SetLike.mem_coe, mem_basicOpen, Set.mem_compl_iff, mem_zeroLocus,
    Set.singleton_subset_iff]

@[simp]
theorem basicOpen_one : basicOpen (1 : R) = ⊤ :=
  TopologicalSpace.Opens.ext <| by simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem basicOpen_zero : basicOpen (0 : R) = ⊥ :=

exec
/bin/bash -lc 'rg -n "TensorProduct.*ringKrullDim|ringKrullDim.*TensorProduct|KrullDim.*Tensor|tensor.*Krull|prod.*Krull|Krull.*prod|Affine.*product|SpecProd|specProd|primeSpectrum.*Prod|primeSpectrum.*Tensor" /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry -S | head -500' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
exec
/bin/bash -lc 'rg -n "vanishingIdeal.*(union|iUnion|Union|sUnion)|zeroLocus.*(union|iUnion)|union.*vanishingIdeal|iUnion.*vanishingIdeal|vanishingIdeal.*sup|vanishingIdeal.*inf|Ideal.*inf.*vanishing|Set.*prod|prod.*vanishingIdeal" /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre -S | head -500' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Limits.lean:525:    coprodSpec R S (coprodMk _ _ x) = (PrimeSpectrum.primeSpectrumProd R S).symm x := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Limits.lean:536:    coprodSpec R S x = (PrimeSpectrum.primeSpectrumProd R S).symm ((coprodMk _ _).symm x) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Limits.lean:564:    PrimeSpectrum.primeSpectrumProdHomeo.trans (coprodMk (Spec <| .of R) (Spec <| .of S))).inv
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:71:* `PrimeSpectrum.primeSpectrumProdHomeo`: the prime spectrum of a product semiring is homeomorphic
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:455:section SpecProd
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:459:lemma primeSpectrumProd_symm_inl (x) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:460:    (primeSpectrumProd R S).symm (.inl x) = comap (RingHom.fst R S) x := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:463:lemma primeSpectrumProd_symm_inr (x) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:464:    (primeSpectrumProd R S).symm (.inr x) = comap (RingHom.snd R S) x := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:496:def primeSpectrumProdHomeo :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:498:  refine ((primeSpectrumProd R S).symm.toHomeomorphOfIsInducing ?_).symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:502:    simp only [Function.comp_def, primeSpectrumProd_symm_inl, primeSpectrumProd_symm_inr]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:504:  · simp_rw [isClosedMap_sum, primeSpectrumProd_symm_inl, primeSpectrumProd_symm_inr]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:507:end SpecProd
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Basic.lean:93:def primeSpectrumProdOfSum : PrimeSpectrum R ⊕ PrimeSpectrum S → PrimeSpectrum (R × S)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Basic.lean:99:noncomputable def primeSpectrumProd :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Basic.lean:102:    Equiv.ofBijective (primeSpectrumProdOfSum R S) (by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Basic.lean:105:          simp only [mk.injEq, Ideal.prod_inj, primeSpectrumProdOfSum] at h
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Basic.lean:118:theorem primeSpectrumProd_symm_inl_asIdeal (x : PrimeSpectrum R) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Basic.lean:119:    ((primeSpectrumProd R S).symm <| Sum.inl x).asIdeal = Ideal.prod x.asIdeal ⊤ := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Basic.lean:124:theorem primeSpectrumProd_symm_inr_asIdeal (x : PrimeSpectrum S) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Basic.lean:125:    ((primeSpectrumProd R S).symm <| Sum.inr x).asIdeal = Ideal.prod ⊤ x.asIdeal := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Polynomial.lean:38:      ← ringKrullDim_eq_of_ringEquiv (polyEquivTensor R (p.asIdeal.ResidueField)).toRingEquiv,

exec
/bin/bash -lc 'rg -n "quotient.*inf|inf.*quotient|quotient.*sup|Ideal.Quotient.*prod|Pi.*quotient|Product|Chinese|comaximal|ker.*prod|quotientInf|quotient.*Equiv" /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension -S | head -500' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Pure.lean:8:public import Mathlib.LinearAlgebra.TensorProduct.Quotient
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Pure.lean:36:open TensorProduct PrimeSpectrum
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Pure.lean:43:lemma injective_lTensor_quotient_iff_inf_eq_mul (I J : Ideal R) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Pure.lean:49:      (TensorProduct.rid R (R ⧸ I)).symm ∘ₗ f ∘ₗ TensorProduct.quotTensorEquivQuotSMul J I := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Pure.lean:51:    simp [f, ← Ideal.Quotient.algebraMap_eq, Algebra.TensorProduct.tmul_one_eq_one_tmul]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Pure.lean:62:  rw [← injective_lTensor_quotient_iff_inf_eq_mul]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Pure.lean:87:  rw [injective_lTensor_quotient_iff_inf_eq_mul]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/CotangentBaseChange.lean:8:public import Mathlib.LinearAlgebra.TensorProduct.Quotient
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/CotangentBaseChange.lean:11:public import Mathlib.RingTheory.TensorProduct.Quotient
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/CotangentBaseChange.lean:30:open TensorProduct
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/CotangentBaseChange.lean:38:attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/CotangentBaseChange.lean:45:      (I.map <| (Algebra.TensorProduct.includeRight.toRingHom : S →+* T ⊗[R] S)).Cotangent :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/CotangentBaseChange.lean:60:      t • (I.map Algebra.TensorProduct.includeRight.toRingHom).toCotangent
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/CotangentBaseChange.lean:66:  let a : S →+* T ⊗[R] S := Algebra.TensorProduct.includeRight.toRingHom
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/CotangentBaseChange.lean:86:  let a : S →+* T ⊗[R] S := Algebra.TensorProduct.includeRight.toRingHom
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/CotangentBaseChange.lean:93:    (Algebra.TensorProduct.tensorQuotientEquiv _ _ _ _).trans
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/CotangentBaseChange.lean:94:      (Ideal.quotientEquivAlgOfEq T (Ideal.map_pow _ _ _))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/CotangentBaseChange.lean:111:      (I.map (Algebra.TensorProduct.includeRight.toRingHom : _ →+* T ⊗[R] S)).Cotangent :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/CotangentBaseChange.lean:118:      t • (I.map Algebra.TensorProduct.includeRight.toRingHom).toCotangent
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/ChineseRemainder.lean:8:public import Mathlib.LinearAlgebra.TensorProduct.Pi
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/ChineseRemainder.lean:9:public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/ChineseRemainder.lean:12:/-! # Module version of Chinese remainder theorem
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/ChineseRemainder.lean:25:open TensorProduct LinearMap
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/ChineseRemainder.lean:29:      .pi (fun i ↦ TensorProduct.mk R (R ⧸ I i) M 1) ∘ₗ TensorProduct.lid R M := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/ChineseRemainder.lean:37:/-- A form of Chinese remainder theorem for modules, part I: if ideals `Iᵢ` of `R` are pairwise
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/ChineseRemainder.lean:39:theorem pi_tensorProductMk_quotient_surjective :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/ChineseRemainder.lean:40:    Surjective (LinearMap.pi fun i ↦ TensorProduct.mk R (R ⧸ I i) M 1) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/ChineseRemainder.lean:45:/-- A form of Chinese remainder theorem for modules, part II: if ideals `Iᵢ` of `R` are pairwise
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/ChineseRemainder.lean:48:theorem ker_tensorProductMk_quotient :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/ChineseRemainder.lean:49:    ker (LinearMap.pi fun i ↦ TensorProduct.mk R (R ⧸ I i) M 1) =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/ChineseRemainder.lean:52:  rw [← (TensorProduct.lid R M).conj_exact_iff_exact, exact_iff] at this
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Norm/AbsNorm.lean:22:the quotient `R ⧸ I` (setting it to 0 if the cardinality is infinite).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Norm/AbsNorm.lean:90:This is essentially just a repackaging of the Chinese Remainder Theorem.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Norm/AbsNorm.lean:95:    Nat.card_congr (Ideal.quotientMulEquivQuotientProd I J coprime).toEquiv,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/PowTransition.lean:38:established the first isomorphism theorem and Chinese remainder theorem, we put these pure technical
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Int.lean:43:    (Int.quotientSpanNatEquivZMod p).toMulEquiv.isField (Field.toIsField _)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Defs.lean:207:See also `Submodule.quotEquivOfEq` and `Ideal.quotientEquivAlgOfEq`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:116:  rw [← supportDim_quotient_eq_ringKrullDim, ← supportDim_self_eq_ringKrullDim]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:124:  rw [ringKrullDim_eq_of_ringEquiv (quotientEquivAlgOfEq R h).toRingEquiv,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:211:  rw [ringKrullDim_eq_of_ringEquiv (quotientEquivAlgOfEq R eq).toRingEquiv,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:212:    ← supportDim_quotient_eq_ringKrullDim, ← supportDim_self_eq_ringKrullDim]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/MinimalPrime/Basic.lean:170:    simpa [comap_map_quotientMk, hq.1, sup_le_iff] using comap_mono (f := Ideal.Quotient.mk I) h2
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Over.lean:293:  __ := quotientEquiv P Q σ h
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Index.lean:12:public import Mathlib.LinearAlgebra.TensorProduct.Quotient
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Index.lean:13:public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Index.lean:16:public import Mathlib.RingTheory.TensorProduct.Finite
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Index.lean:36:open TensorProduct in
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Index.lean:61:open TensorProduct in
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:18:- `RingHom.quotientKerEquivRange` : the **first isomorphism theorem** for commutative rings.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:19:- `RingHom.quotientKerEquivRangeS` : the **first isomorphism theorem**
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:21:- `AlgHom.quotientKerEquivRange` : the **first isomorphism theorem**
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:23:- `Ideal.quotientInfRingEquivPiQuotient`: the **Chinese Remainder Theorem**, version for coprime
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:38:This is an isomorphism if `f` has a right inverse (`quotientKerEquivOfRightInverse`) /
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:39:is surjective (`quotientKerEquivOfSurjective`).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:66:def quotientKerEquivOfRightInverse {g : S → R} (hf : Function.RightInverse g f) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:79:theorem quotientKerEquivOfRightInverse.apply {g : S → R} (hf : Function.RightInverse g f)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:80:    (x : R ⧸ ker f) : quotientKerEquivOfRightInverse hf x = kerLift f x :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:84:theorem quotientKerEquivOfRightInverse.Symm.apply {g : S → R} (hf : Function.RightInverse g f)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:85:    (x : S) : (quotientKerEquivOfRightInverse hf).symm x = Ideal.Quotient.mk (ker f) (g x) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:89:noncomputable def quotientKerEquivOfSurjective (hf : Function.Surjective f) : R ⧸ (ker f) ≃+* S :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:90:  quotientKerEquivOfRightInverse (Classical.choose_spec hf.hasRightInverse)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:93:lemma quotientKerEquivOfSurjective_apply_mk {f : R →+* S} (hf : Function.Surjective f) (x : R) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:94:    f.quotientKerEquivOfSurjective hf (Ideal.Quotient.mk _ x) = f x :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:98:lemma quotientKerEquivOfSurjective_symm_apply {f : R →+* S} (hf : Function.Surjective f) (x : R) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:99:    (RingHom.quotientKerEquivOfSurjective hf).symm (f x) = Ideal.Quotient.mk _ x := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:100:  apply (RingHom.quotientKerEquivOfSurjective hf).injective
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:103:lemma quotientKerEquivOfSurjective_symm_comp {f : R →+* S} (hf : Function.Surjective f) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:104:    (RingHom.quotientKerEquivOfSurjective hf).symm.toRingHom.comp f = Ideal.Quotient.mk _ := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:108:noncomputable def quotientKerEquivRangeS (f : R →+* S) : R ⧸ ker f ≃+* f.rangeS :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:110:  quotientKerEquivOfSurjective f.rangeSRestrict_surjective
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:115:noncomputable def quotientKerEquivRange (f : R →+* S) : R ⧸ ker f ≃+* f.range :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:117:    quotientKerEquivOfSurjective f.rangeRestrict_surjective
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:183:theorem mem_quotient_iff_mem_sup {I J : Ideal R} [I.IsTwoSided] {x : R} :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:188:/-- See also `Ideal.mem_quotient_iff_mem_sup` if the assumption `I ≤ J` is not available. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:191:  rw [mem_quotient_iff_mem_sup, sup_eq_left.mpr hIJ]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:193:section ChineseRemainder
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:198:/-- The homomorphism from `R/(⋂ i, f i)` to `∏ i, (R / f i)` featured in the Chinese
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:200:def quotientInfToPiQuotient (I : ι → Ideal R) [∀ i, (I i).IsTwoSided] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:205:lemma quotientInfToPiQuotient_mk (I : ι → Ideal R) [∀ i, (I i).IsTwoSided] (x : R) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:206:    quotientInfToPiQuotient I (Quotient.mk _ x) = fun i : ι ↦ Quotient.mk (I i) x :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:209:lemma quotientInfToPiQuotient_mk' (I : ι → Ideal R) [∀ i, (I i).IsTwoSided] (x : R) (i : ι) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:210:    quotientInfToPiQuotient I (Quotient.mk _ x) i = Quotient.mk (I i) x :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:213:lemma quotientInfToPiQuotient_inj (I : ι → Ideal R) [∀ i, (I i).IsTwoSided] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:214:    Injective (quotientInfToPiQuotient I) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:215:  rw [quotientInfToPiQuotient, injective_lift_iff, ker_Pi_Quotient_mk]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:219:lemma quotientInfToPiQuotient_surj {I : ι → Ideal R}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:220:    (hI : Pairwise (IsCoprime on I)) : Surjective (quotientInfToPiQuotient I) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:238:  rw [quotientInfToPiQuotient_mk', map_sum, Fintype.sum_eq_single i]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:243:/-- **Chinese Remainder Theorem**. Eisenbud Ex.2.6.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:245:noncomputable def quotientInfRingEquivPiQuotient (f : ι → Ideal R)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:247:  { Equiv.ofBijective _ ⟨quotientInfToPiQuotient_inj f, quotientInfToPiQuotient_surj hf⟩,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:248:    quotientInfToPiQuotient f with }
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:250:/-- Corollary of Chinese Remainder Theorem: if `Iᵢ` are pairwise coprime ideals in a
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:255:  obtain ⟨y, rfl⟩ := Ideal.quotientInfToPiQuotient_surj hf x
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:264:/-- Corollary of Chinese Remainder Theorem: if `Iᵢ` are pairwise coprime ideals in a
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:272:/-- **Chinese remainder theorem**, specialized to two ideals. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:273:noncomputable def quotientInfEquivQuotientProd (I J : Ideal R) (coprime : IsCoprime I J) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:282:            (Ideal.quotientInfRingEquivPiQuotient f hf).trans <| RingEquiv.piFinTwo fun i => R ⧸ f i
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:285:theorem quotientInfEquivQuotientProd_fst (I J : Ideal R) (coprime : IsCoprime I J) (x : R ⧸ I ⊓ J) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:286:    (quotientInfEquivQuotientProd I J coprime x).fst =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:291:theorem quotientInfEquivQuotientProd_snd (I J : Ideal R) (coprime : IsCoprime I J) (x : R ⧸ I ⊓ J) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:292:    (quotientInfEquivQuotientProd I J coprime x).snd =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:297:theorem fst_comp_quotientInfEquivQuotientProd (I J : Ideal R) (coprime : IsCoprime I J) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:299:        (quotientInfEquivQuotientProd I J coprime : R ⧸ I ⊓ J →+* (R ⧸ I) × R ⧸ J) =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:304:theorem snd_comp_quotientInfEquivQuotientProd (I J : Ideal R) (coprime : IsCoprime I J) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:306:        (quotientInfEquivQuotientProd I J coprime : R ⧸ I ⊓ J →+* (R ⧸ I) × R ⧸ J) =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:310:/-- **Chinese remainder theorem**, specialized to two ideals. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:311:noncomputable def quotientMulEquivQuotientProd (I J : Ideal R) (coprime : IsCoprime I J) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:314:    Ideal.quotientInfEquivQuotientProd I J coprime
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:317:theorem quotientMulEquivQuotientProd_fst (I J : Ideal R) (coprime : IsCoprime I J) (x : R ⧸ I * J) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:318:    (quotientMulEquivQuotientProd I J coprime x).fst =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:323:theorem quotientMulEquivQuotientProd_snd (I J : Ideal R) (coprime : IsCoprime I J) (x : R ⧸ I * J) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:324:    (quotientMulEquivQuotientProd I J coprime x).snd =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:329:theorem fst_comp_quotientMulEquivQuotientProd (I J : Ideal R) (coprime : IsCoprime I J) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:331:        (quotientMulEquivQuotientProd I J coprime : R ⧸ I * J →+* (R ⧸ I) × R ⧸ J) =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:336:theorem snd_comp_quotientMulEquivQuotientProd (I J : Ideal R) (coprime : IsCoprime I J) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:338:        (quotientMulEquivQuotientProd I J coprime : R ⧸ I * J →+* (R ⧸ I) × R ⧸ J) =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:342:end ChineseRemainder
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:507:This is an isomorphism if `f` has a right inverse (`quotientKerAlgEquivOfRightInverse`) /
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:508:is surjective (`quotientKerAlgEquivOfSurjective`).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:529:def quotientKerAlgEquivOfRightInverse {f : A →ₐ[R₁] B} {g : B → A}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:531:  { RingHom.quotientKerEquivOfRightInverse hf,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:536:noncomputable def quotientKerAlgEquivOfSurjective {f : A →ₐ[R₁] B} (hf : Function.Surjective f) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:538:  quotientKerAlgEquivOfRightInverse (Classical.choose_spec hf.hasRightInverse)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:541:lemma quotientKerAlgEquivOfSurjective_mk {f : A →ₐ[R₁] B} (hf : Function.Surjective f)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:542:    (a : A) : Ideal.quotientKerAlgEquivOfSurjective hf (Ideal.Quotient.mk _ a) = f a :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:546:lemma quotientKerAlgEquivOfSurjective_symm_apply {f : A →ₐ[R₁] B} (hf : Function.Surjective f)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:547:    (a : A) : (Ideal.quotientKerAlgEquivOfSurjective hf).symm (f a) = a := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:548:  apply (Ideal.quotientKerAlgEquivOfSurjective hf).injective
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:561:  .comp (Ideal.Quotient.liftₐ _ g H) (Ideal.quotientKerAlgEquivOfSurjective hf).symm.toAlgHom
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:569:  rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:617:    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:619:section quotientEquiv
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:626:def quotientEquiv : R ⧸ I ≃+* S ⧸ J where
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:632:      quotientMap_mk, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:636:      quotientMap_mk, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:639:theorem quotientEquiv_mk (x : R) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:640:    quotientEquiv I J f hIJ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J (f x) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:644:theorem quotientEquiv_symm_mk (x : S) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:645:    (quotientEquiv I J f hIJ).symm (Ideal.Quotient.mk J x) = Ideal.Quotient.mk I (f.symm x) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:648:end quotientEquiv
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:709:def quotientEquivAlg (f : A ≃ₐ[R₁] B) (hIJ : J = I.map (f : A →+* B)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:711:  { quotientEquiv I J (f : A ≃+* B) hIJ with
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:715:lemma quotientEquivAlg_symm (f : A ≃ₐ[R₁] B) (hIJ : J = I.map (f : A →+* B)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:716:    (quotientEquivAlg I J f hIJ).symm = quotientEquivAlg J I f.symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:722:lemma quotientEquivAlg_mk (f : A ≃ₐ[R₁] B) (hIJ : J = I.map (f : A →+* B)) (x : A) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:723:    Ideal.quotientEquivAlg I J f hIJ x = f x :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:758:def quotientEquivAlgOfEq {I J : Ideal A} [I.IsTwoSided] [J.IsTwoSided] (h : I = J) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:760:  quotientEquivAlg I J AlgEquiv.refl <| h ▸ (map_id I).symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:763:theorem quotientEquivAlgOfEq_mk {I J : Ideal A} [I.IsTwoSided] [J.IsTwoSided] (h : I = J) (x : A) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:764:    quotientEquivAlgOfEq R₁ h (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J x :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:768:theorem quotientEquivAlgOfEq_coe_eq_factorₐ
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:770:    (quotientEquivAlgOfEq R₁ h : A ⧸ I →ₐ[R₁] A ⧸ J) = Quotient.factorₐ R₁ (le_of_eq h) := rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:773:theorem quotientEquivAlgOfEq_coe_eq_factor
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:775:    (quotientEquivAlgOfEq R₁ h : A ⧸ I →+* A ⧸ J) = Quotient.factor (le_of_eq h) := rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:778:theorem quotientEquivAlgOfEq_symm {I J : Ideal A} [I.IsTwoSided] [J.IsTwoSided] (h : I = J) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:779:    (quotientEquivAlgOfEq R₁ h).symm = quotientEquivAlgOfEq R₁ h.symm := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:787:  simp only [mem_comap, mem_quotient_iff_mem_sup, sup_comm]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:800:noncomputable def quotientKerEquivRange
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:804:  (Ideal.quotientEquivAlgOfEq R (AlgHom.ker_rangeRestrict f).symm).trans <|
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:805:    Ideal.quotientKerAlgEquivOfSurjective f.rangeRestrict_surjective
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:819:    RingHom.quotientKerEquivOfRightInverse (f := .id R) (g := _root_.id) fun _ ↦ rfl

 succeeded in 123ms:
b/Mathlib/RingTheory/Ideal/Prod.lean:128:      simp [Set.snd_image_prod hs]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Prod.lean:208:      ← Ideal.span_prod (iff_of_true (by simp) (by simp)), Set.singleton_prod_singleton]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaStratification.lean:139:  rw [Set.mem_iUnion₂, mem_productRankLocusLE_iff_exists_mem_orbitRankLocus]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:20:  the finite family of prime orbit ideals (G2 + `vanishingIdeal` turns unions into infs), so its
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:136:orbit-ideal family: `vanishingIdeal` turns the G2 union `Σ̄^r = ⋃_M Ō_M` into an intersection. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalStratumDim.lean:196:flattening of) `productRankLocusLE ![n,m] r` is prime — it is `vanishingIdeal (Ō_{M₀})` of a single
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/ChevalleyComplexity.lean:406:          rw [← Set.union_singleton, zeroLocus_union,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/ChevalleyComplexity.lean:448:            ← Set.compl_eq_univ_diff, eq_compl_comm (y := zeroLocus _), ← zeroLocus_iUnion₂, this]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/ChevalleyComplexity.lean:465:        rw [Set.range_eq_iUnion, zeroLocus_iUnion]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/ChevalleyComplexity.lean:875:      Set.image_diff (hf := comap_injective_of_surjective g hg'), zeroLocus_union]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/NonUnitalSubsemiring/Basic.lean:575:  Set.prod_mono hs ht
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/NonUnitalSubsemiring/Basic.lean:598:  { Equiv.Set.prod (s : Set R) (t : Set S) with
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:232:      Ideal (MvPolynomial σ k)).IsPrime := by rw [vanishingIdeal_univ_eq_bot]; infer_instance
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/ConstructibleSet.lean:129:        compl_sdiff_compl, ← zeroLocus_iUnion₂, Set.biUnion_of_singleton]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:126:  ⟨(vanishingIdeal k {x} : Ideal (MvPolynomial σ k)), by infer_instance⟩
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:133:      (((PrimeSpectrum.mem_vanishingIdeal _ _).1 hp) ⟨vanishingIdeal k {x}, by infer_instance⟩
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Conductor.lean:137:      obtain ⟨a, ha⟩ := (Set.mem_image _ _ _).mp (prod_mem_ideal_map_of_mem_conductor hp
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/DividedPowerAlgebra/Init.lean:243:    span R (Set.range fun (n : ι →₀ ℕ) ↦ n.prod fun i k ↦ dp R k (v i)) = ⊤ := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/UniqueFactorizationDomain/FactorSet.lean:60:/-- Evaluates the product of a `FactorSet` to be the product of the corresponding multiset,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/UniqueFactorizationDomain/FactorSet.lean:62:def FactorSet.prod : FactorSet α → Associates α
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/UniqueFactorizationDomain/FactorSet.lean:67:theorem prod_top : (⊤ : FactorSet α).prod = 0 :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/UniqueFactorizationDomain/FactorSet.lean:72:    FactorSet.prod (s : FactorSet α) = (s.map (↑)).prod :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/UniqueFactorizationDomain/FactorSet.lean:76:theorem prod_add : ∀ a b : FactorSet α, (a + b).prod = a.prod * b.prod
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/UniqueFactorizationDomain/FactorSet.lean:77:  | ⊤, b => show (⊤ + b).prod = (⊤ : FactorSet α).prod * b.prod by simp
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/UniqueFactorizationDomain/FactorSet.lean:78:  | a, ⊤ => show (a + ⊤).prod = a.prod * (⊤ : FactorSet α).prod by simp
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/UniqueFactorizationDomain/FactorSet.lean:80:    rw [← FactorSet.coe_add, prod_coe, prod_coe, prod_coe, Multiset.map_add, Multiset.prod_add]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/UniqueFactorizationDomain/FactorSet.lean:83:theorem prod_mono : ∀ {a b : FactorSet α}, a ≤ b → a.prod ≤ b.prod
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/UniqueFactorizationDomain/FactorSet.lean:87:  | a, ⊤, _ => show a.prod ≤ (⊤ : FactorSet α).prod by simp
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/UniqueFactorizationDomain/FactorSet.lean:91:theorem FactorSet.prod_eq_zero_iff [IsCancelMulZero α] [Nontrivial α] (p : FactorSet α) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/UniqueFactorizationDomain/FactorSet.lean:173:theorem FactorSet.unique [Nontrivial α] {p q : FactorSet α} (h : p.prod = q.prod) : p = q := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/UniqueFactorizationDomain/FactorSet.lean:178:  · rw [eq_comm, ← FactorSet.prod_eq_zero_iff, ← h, Associates.prod_top]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/UniqueFactorizationDomain/FactorSet.lean:179:  · rw [← FactorSet.prod_eq_zero_iff, h, Associates.prod_top]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/UniqueFactorizationDomain/FactorSet.lean:241:theorem prod_factors [Nontrivial α] (s : FactorSet α) : s.prod.factors = s :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/UniqueFactorizationDomain/FactorSet.lean:242:  FactorSet.unique <| factors_prod _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/UniqueFactorizationDomain/FactorSet.lean:251:  exact ⟨fun h ↦ by rwa [← factors_prod a, FactorSet.prod_eq_zero_iff], fun h ↦ h ▸ factors_zero⟩
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/UniqueFactorizationDomain/FactorSet.lean:313:theorem prod_le [Nontrivial α] {a b : FactorSet α} : a.prod ≤ b.prod ↔ a ≤ b := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/UniqueFactorizationDomain/FactorSet.lean:429:    (by rw [factors_prod, FactorSet.prod.eq_def]; dsimp; rw [prod_singleton])
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/UniqueFactorizationDomain/FactorSet.lean:435:      rw [Associates.factors_prod, FactorSet.prod.eq_def]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/UniqueFactorizationDomain/FactorSet.lean:571:  use FactorSet.prod (u : FactorSet α)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/GradedAlgebra/HomogeneousLocalization.lean:947:      (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ ↦ hxd i) : Away 𝒜 f) |
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/GradedAlgebra/HomogeneousLocalization.lean:975:        exact H ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ ↦ hxd i
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/GradedAlgebra/HomogeneousLocalization.lean:980:        exact SetLike.prod_pow_mem_graded _ _ _ _ fun i _ ↦ hxd i
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/GradedAlgebra/HomogeneousLocalization.lean:1002:      (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ ↦ hxd i) |
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/GradedAlgebra/HomogeneousLocalization.lean:1015:      (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ ↦ hxd i) =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/GradedAlgebra/HomogeneousLocalization.lean:1017:      (H₀ ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ ↦ hxd i) *
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/GradedAlgebra/HomogeneousLocalization.lean:1068:      (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ ↦ hxd i) |
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/GradedAlgebra/HomogeneousLocalization.lean:1112:    (by convert SetLike.prod_pow_mem_graded _ _ _ _ fun i _ ↦ hxd i; exact ai.2.symm)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/MvPowerSeries/Rename.lean:87:  apply Set.Finite.subset (s := ↑((Finset.antidiagonal x).sup (fun q ↦ Finset.product {q}

exec
/bin/bash -lc 'cat /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/lake-manifest.json | head -80' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
{"version": "1.1.0",
 "packagesDir": ".lake/packages",
 "packages":
 [{"url": "https://github.com/leanprover-community/mathlib4",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "8a178386ffc0f5fef0b77738bb5449d50efeea95",
   "name": "mathlib",
   "manifestFile": "lake-manifest.json",
   "inputRev": "v4.29.0",
   "inherited": false,
   "configFile": "lakefile.lean"},
  {"url": "https://github.com/leanprover-community/plausible",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "83e90935a17ca19ebe4b7893c7f7066e266f50d3",
   "name": "plausible",
   "manifestFile": "lake-manifest.json",
   "inputRev": "main",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/LeanSearchClient",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "c5d5b8fe6e5158def25cd28eb94e4141ad97c843",
   "name": "LeanSearchClient",
   "manifestFile": "lake-manifest.json",
   "inputRev": "main",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/import-graph",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "48d5698bc464786347c1b0d859b18f938420f060",
   "name": "importGraph",
   "manifestFile": "lake-manifest.json",
   "inputRev": "main",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/ProofWidgets4",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "3c52dee17f0cd89c1ec14de78920d1bdaa3d26b3",
   "name": "proofwidgets",
   "manifestFile": "lake-manifest.json",
   "inputRev": "v0.0.95",
   "inherited": true,
   "configFile": "lakefile.lean"},
  {"url": "https://github.com/leanprover-community/aesop",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "7152850e7b216a0d409701617721b6e469d34bf6",
   "name": "aesop",
   "manifestFile": "lake-manifest.json",
   "inputRev": "master",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/quote4",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "707efb56d0696634e9e965523a1bbe9ac6ce141d",
   "name": "Qq",
   "manifestFile": "lake-manifest.json",
   "inputRev": "master",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/batteries",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "756e3321fd3b02a85ffda19fef789916223e578c",
   "name": "batteries",
   "manifestFile": "lake-manifest.json",

exec
/bin/bash -lc 'rg -n "mathlib" /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/lake-manifest.json /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/lean-toolchain' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/lake-manifest.json:4: [{"url": "https://github.com/leanprover-community/mathlib4",
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/lake-manifest.json:9:   "name": "mathlib",

exec
/bin/bash -lc 'rg -n "productRankLocus_eq_iUnion_smul_fibre|deepBaseComap_sigmaIdeal_le|nEquiv|nSub_mult|sigmaIdeal ≤|radical|FibreReduced|vanishingIdeal_image_fibre_eq_radical" /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre -S | head -300' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:23:(`orbitKostantPartitionEquiv`, `orbitCMPlusEquiv`): the complete invariant above +
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:2:import DLNFibre.Core.FibreReducedTrivialization
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:9:(`Core.FibreReducedTrivialization`) carries as a hypothesis. The engine's localized determinantal
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:10:presentation (`Core.DeterminantalBasePresentation`) is `N = 1` only: `basePresentationEquiv` lives
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:35:6. `deepBaseComap_sigmaIdeal_le` — the (non-circular) ideal direction: `deepBaseComap d` maps the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:39:   `aeval_deepBaseComap` + `singleTuple`). It does **not** assume the circular `sigmaIdeal ≤
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:43:   (`Ideal.quotientMapₐ`), then composed with `basePresentationEquiv.symm` to give a `k`-algebra map
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:131:`hSred : IsReduced S` (`Core.FibreReducedTrivialization.fibreGenIdeal_isRadical_of_trivialization`).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:132:It is **cheap** here: `IadDeep = (sigmaIdeal d r).map (algebraMap …)` is radical because
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:133:`sigmaIdeal` is radical (`vanishingIdeal_isRadical`, over `[IsAlgClosed k]`) and localization
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:134:carries radical
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:135:ideals to radical ideals (`IsLocalization.map_radical`); a quotient by a radical ideal is reduced
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:138:/-- **`IadDeep` is radical** (`[IsAlgClosed k]`): the localized image of the radical determinantal
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:139:base ideal `sigmaIdeal d r`. Via `IsLocalization.map_radical`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:140:(`(I.map …).radical = I.radical.map …`) and `sigmaIdeal`'s radicality
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:147:  rw [← Ideal.radical_eq_iff, IadDeep,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:148:    ← IsLocalization.map_radical (M := Submonoid.powers (ΔPdeep (k := k) d r hp hq)),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:149:    hsig.radical]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:152:`Sred = Localization.Away ΔPdeep ⧸ IadDeep` with `IadDeep` radical (`IadDeep_isRadical`); a quotient
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:153:by a radical ideal is reduced
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:229:Does **not** assume the circular `sigmaIdeal ≤ fibreGenIdeal`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:230:theorem deepBaseComap_sigmaIdeal_le (d : Fin (N + 1) → ℕ) (r : ℕ) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:251:discharged by `deepBaseComap_sigmaIdeal_le`), then composed with `basePresentationEquiv.symm`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:291:the base `sigmaIdeal` into the deep one (`deepBaseComap_sigmaIdeal_le`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:301:    deepBaseComap_sigmaIdeal_le d r (Ideal.mem_map_of_mem _ hg)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:316:`baseQuotMap` precomposed with `basePresentationEquiv.symm`. This is the morphism whose induced
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:318:R2-3a's product iso `e` needs). `[IsAlgClosed k] [CharZero k]` (for `basePresentationEquiv`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:323:    (basePresentationEquiv (k := k) (d 0) (d (Fin.last N)) r hp hq).symm.toAlgHom
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:417:`CharZero`; `schurToSred` composes this with `basePresentationEquiv.symm`.) -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitCodim.lean:58:dimension theorems (catenary `dim R/I = n − ht I`, determinantal height, Nullstellensatz radical
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:22:`I = orbitIdeal M = vanishingIdeal(orbitSet M)` directly — no determinantal minors, no radical. The
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:7:# `DLNFibre.Core.FibreReducedTrivialization` — route-(b) reducedness via the trivialization
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:11:ideal `I_E = (mult(Ã) − E)` is **radical** (`F_E = k[Ã]/I_E` **reduced**), for every `N ≥ 1`, every
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:31:   `fibreGenIdeal d B` is **radical** (`Ideal.isRadical_iff_quotient_reduced`).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:33:3. **`vanishingIdeal_fibre_eq_fibreGenIdeal_of_trivialization`** — the **radical-collapse** of
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:34:   `MultComorphism` point 4: with the cut ideal radical, `vanishingIdeal (fibre d B) =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:35:   radical (fibreGenIdeal d B) = fibreGenIdeal d B` — the `radical (·)` wrapper drops. This is the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:72:/-- `fibreGenIdeal d B` is radical **iff** `F_B` is reduced — the engine restatement of
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:74:geometric reducedness of `F_B` is exactly the radical-collapse the height-squeeze wants). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:101:/-- **Route (b): `fibreGenIdeal` radical, through the trivialization.** Given the chart
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:104:a `vanishingIdeal`), the fibre ideal `fibreGenIdeal d B` is **radical**. The certified mechanism:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:106:⟹ `fibreGenIdeal d B` radical. `[Nontrivial R]` (`R = SchurLoc` is a domain). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:117:  -- ⟹ `F_B` reduced (tensor-with-a-field descent) ⟹ `fibreGenIdeal` radical
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:120:/-- **The radical-collapse of `MultComorphism` point 4** (through the trivialization). With the cut
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:121:ideal radical (`fibreGenIdeal_isRadical_of_trivialization`), the engine's
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:122:`vanishingIdeal (fibre d B) = radical (fibreGenIdeal d B)` collapses to
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:123:`vanishingIdeal (fibre d B) = fibreGenIdeal d B`: the `radical (·)` wrapper drops. The clean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:132:  rw [vanishingIdeal_image_fibre_eq_radical,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:133:    (fibreGenIdeal_isRadical_of_trivialization d B R S e hSred).radical]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankPattern.lean:251:(`orbitKostantPartitionEquiv`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:81:theorem productRankLocus_eq_iUnion_smul_fibre (d : Fin (N + 1) → ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:5:# `DLNFibre.Core.FibreHeightDirect` — the radical-insensitive retarget of the fibre codimension (H1)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:10:Nullstellensatz identifies that vanishing ideal with the **radical** of the explicit generator ideal
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:11:`fibreGenIdeal d B` (`Core.MultComorphism.vanishingIdeal_image_fibre_eq_radical`). The point of this
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:12:rung is that **the height does not see the radical**: `(radical I).height = I.height`, because an
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:13:ideal and its radical have the same minimal primes (`Ideal.radical_minimalPrimes`), and
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:16:So `codimRepCanonical (fibre d B) = (fibreGenIdeal d B).height` — **unconditionally** (no radicality
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:18:radicality question (the thread-20 wall): the codimension, hence the RLCT payoff that consumes it,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:19:never depends on whether `fibreGenIdeal` is its own radical.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:32:/-- **The height of an ideal is the height of its radical.** An ideal `I` and `I.radical` have the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:33:same minimal primes (`Ideal.radical_minimalPrimes`), and `Ideal.height` is the infimum of the prime
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:35:theorem Ideal.height_radical {R : Type*} [CommRing R] (I : Ideal R) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:36:    I.radical.height = I.height := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:37:  simp only [Ideal.height, Ideal.radical_minimalPrimes]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:43:/-- **H1 — the radical-insensitive retarget.** Over an algebraically closed field, the canonical
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:47:(definition of `codimRepCanonical`/`codimRep`); `vanishingIdeal (…) = (fibreGenIdeal d B).radical`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:48:(`vanishingIdeal_image_fibre_eq_radical`, the Nullstellensatz); `(radical I).height = I.height`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:49:(`Ideal.height_radical`). The codimension does **not** depend on whether `fibreGenIdeal` is
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:50:radical. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:54:  rw [codimRepCanonical, codimRep, vanishingIdeal_image_fibre_eq_radical, Ideal.height_radical]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:20:   Nullstellensatz over `[IsAlgClosed k]`): `vanishingIdeal Z` is always **radical**
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:66:/-- The vanishing ideal of any subset of `σ → k` is **radical** (over `[IsAlgClosed k]`): by the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:67:strong Nullstellensatz it equals its own radical, via `vanishingIdeal Z = vanishingIdeal (zeroLocus
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:68:(vanishingIdeal Z))` `= (vanishingIdeal Z).radical`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:71:  have h : vanishingIdeal k Z = (vanishingIdeal k Z).radical := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:74:        vanishingIdeal_zeroLocus_eq_radical (K := k)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:75:  rw [h]; exact radical_isRadical _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:87:Nullstellensatz forces `vanishingIdeal (zeroLocus (vanishingIdeal Z)) = (vanishingIdeal Z).radical`,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:97:    have h3 : vanishingIdeal k (zeroLocus k (vanishingIdeal k Z)) = (vanishingIdeal k Z).radical :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:98:      vanishingIdeal_zeroLocus_eq_radical (K := k) _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:100:    exact Ideal.radical_eq_top.mp h3.symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitKostant.lean:35:* `orbitKostantPartitionEquiv d : Quotient (orbitSetoid d) ≃ KostantPartition d` — orbits ↔ the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitKostant.lean:128:`orbitKostantPartitionEquiv` below (carrier `kostantArrayOfRank`, the `diff`-array truncated to `0`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitKostant.lean:217:`orbitKostantPartitionEquiv` below. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitKostant.lean:373:noncomputable def rankKostantPartitionEquiv (d : Fin (N + 1) → ℕ) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitKostant.lean:388:`rankKostantPartitionEquiv`. The
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitKostant.lean:391:noncomputable def orbitKostantPartitionEquiv (d : Fin (N + 1) → ℕ) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitKostant.lean:393:  (orbitKostantEquiv d).trans (rankKostantPartitionEquiv d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitKostant.lean:397:@[simp] theorem orbitKostantPartitionEquiv_mk {d : Fin (N + 1) → ℕ} (A : Tuple (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitKostant.lean:398:    (orbitKostantPartitionEquiv d (Quotient.mk _ A) : KostantPartition (k := k) d).1
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitKostant.lean:631:`i ≤ j`-supported. The literal-codomain form of `orbitKostantPartitionEquiv`, retargeted onto the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitKostant.lean:635:  (orbitKostantPartitionEquiv d).trans (kostantPartitionCMPlusEquiv d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitKostant.lean:666:    (orbitKostantPartitionEquiv dWitness (Quotient.mk (orbitSetoid dWitness) tupleWitnessQ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitKostant.lean:714:so the `-3` artifact is gone. The literal bijection `orbitKostantPartitionEquiv` fires here. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:10:`codimRepCanonical (fibre d B) = Ideal.height (fibreGenIdeal d B)` (H1, radical-insensitive), and
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:16:`FibreReducedTrivialization` did for its `e`):
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntervalModule.lean:320:  fun t ↦ Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks (A t) 0 0 (B t))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntervalModule.lean:327:    Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks P 0 0 Q)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntervalModule.lean:328:        * Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks R 0 0 S)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntervalModule.lean:329:      = Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks (P * R) 0 0 (Q * S)) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntervalModule.lean:331:    Matrix.submatrix_mul_equiv _ _ _ finSumFinEquiv.symm _, fromBlocks_multiply]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntervalModule.lean:337:      = Matrix.reindex finSumFinEquiv finSumFinEquiv
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntervalModule.lean:347:      = Matrix.reindex finSumFinEquiv finSumFinEquiv
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:167:    (Equiv.sumCongr (Equiv.refl (Fin r)) finOneEquiv.symm).trans finSumFinEquiv with he
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:378:noncomputable def basePresentationEquiv [IsAlgClosed k] [CharZero k] (q p r : ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:414:  basePresentationEquiv 2 2 1 h h
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:27:4. **`vanishingIdeal(fibre) = radical(fibreGenIdeal)`** — over `[IsAlgClosed k]`, the engine's
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:28:   Nullstellensatz (`vanishingIdeal_zeroLocus_eq_radical`) reads the fibre's vanishing ideal as the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:29:   radical of `fibreGenIdeal d B = span {multPoly d r c − C (B r c)}`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:157:/-- **The fibre's vanishing ideal is the radical of the generator ideal.** Over an algebraically
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:158:closed field, the engine's strong Nullstellensatz (`vanishingIdeal_zeroLocus_eq_radical`) reads the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:159:vanishing ideal of the fibre's image as the radical of `fibreGenIdeal d B`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:160:theorem vanishingIdeal_image_fibre_eq_radical [IsAlgClosed k] (d : Fin (N + 1) → ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:162:    vanishingIdeal k (canonicalCoord d '' (fibre d B)) = (fibreGenIdeal d B).radical := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:164:    vanishingIdeal_zeroLocus_eq_radical (K := k)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:75:  (finCongr (show n = r + (n - r) by omega)).trans finSumFinEquiv.symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:83:    finSumFinEquiv_symm_apply_castAdd]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:103:    finSumFinEquiv_symm_apply_natAdd]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:90:  rcases finSumFinEquiv.symm r with r' | r' <;> rcases finSumFinEquiv.symm c with c' | c' <;>
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:101:  { val := Matrix.reindex finSumFinEquiv finSumFinEquiv
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:103:    inv := Matrix.reindex finSumFinEquiv finSumFinEquiv
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:117:      = Matrix.reindex finSumFinEquiv finSumFinEquiv
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:121:      = Matrix.reindex finSumFinEquiv finSumFinEquiv
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:603:coordinates (`finSumFinEquiv` reads the strand). At `λ = 0` the row is `[0, 1]` — the downstairs
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:628:long strand (`finSumFinEquiv inl`) carries `λ`, the short strand (`inr`) carries `1`. Defined entrywise
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:633:    then (match finSumFinEquiv.symm s with | Sum.inl _ => lam | Sum.inr _ => 1)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:731:    (Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks A 0 0 B))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:732:      (finSumFinEquiv (Sum.inl r)) (finSumFinEquiv (Sum.inl s)) = A r s := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:739:    (Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks A 0 0 B))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:740:      (finSumFinEquiv (Sum.inr r)) (finSumFinEquiv (Sum.inr s)) = B r s := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:747:    (Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks A 0 0 B))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:748:      (finSumFinEquiv (Sum.inl r)) (finSumFinEquiv (Sum.inr s)) = 0 := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:755:    (Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks A 0 0 B))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:756:      (finSumFinEquiv (Sum.inr r)) (finSumFinEquiv (Sum.inl s)) = 0 := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:764:    splice (k := k) a c e b lam b r (finSumFinEquiv (Sum.inl s)) = lam := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:771:    splice (k := k) a c e b lam b r (finSumFinEquiv (Sum.inr s)) = 1 := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:800:    finSumFinEquiv (Sum.inl (Fin.cast hdimj.symm 0)) with hr₀
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:802:    finSumFinEquiv (Sum.inr (Fin.cast hdimi_short.symm 0)) with hs₀
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:808:  rw [Matrix.mul_apply, ← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type] at hentry
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:809:  simp only [hr₀, hs₀, Matrix.mul_apply, ← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:835:    finSumFinEquiv (Sum.inl (Fin.cast hdimj.symm 0)) with hr₀
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:837:    finSumFinEquiv (Sum.inl (Fin.cast hdimi_long.symm 0)) with hs₀
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:843:  rw [Matrix.mul_apply, ← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type] at hentry
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:844:  simp only [hr₀, hs₀, Matrix.mul_apply, ← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:863:  rw [Matrix.zero_apply, Matrix.mul_apply, ← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:869:  obtain ⟨s', rfl⟩ := finSumFinEquiv.surjective s
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:1071:    then (match finSumFinEquiv.symm s with | Sum.inl _ => Polynomial.X | Sum.inr _ => 1)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:1083:    rcases finSumFinEquiv.symm s with sl | sr
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:1245:    splice (k := ℚ) 0 1 2 1 lam 1 r (finSumFinEquiv (Sum.inl s')) = lam := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:217:      (Equiv.sumCongr (Equiv.refl (Fin r)) finOneEquiv.symm).trans finSumFinEquiv
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:550:  toFun M := (Matrix.of (fun i j => M (finSumFinEquiv (Sum.inl i)) j),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:551:              Matrix.of (fun i j => M (finSumFinEquiv (Sum.inr i)) j))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:553:    Sum.elim (fun a => P.1 a j) (fun b => P.2 b j) (finSumFinEquiv.symm i)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:558:    change Sum.elim (fun a => M (finSumFinEquiv (Sum.inl a)) j)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:559:        (fun b => M (finSumFinEquiv (Sum.inr b)) j) (finSumFinEquiv.symm i) = M i j
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:560:    conv_rhs => rw [← Equiv.apply_symm_apply finSumFinEquiv i]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:561:    rcases finSumFinEquiv.symm i with c | d <;> simp only [Sum.elim_inl, Sum.elim_inr]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:567:    (matrixRowSplit a b γ M).1 i j = M (finSumFinEquiv (Sum.inl i)) j := rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:570:    (matrixRowSplit a b γ M).2 i j = M (finSumFinEquiv (Sum.inr i)) j := rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:575:        (Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks P 0 0 Q) * φ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:580:    rw [← finSumFinEquiv.sum_comp (fun x =>
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:581:      Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks P 0 0 Q)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:582:        (finSumFinEquiv (Sum.inl i)) x * φ x j)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:589:    rw [← finSumFinEquiv.sum_comp (fun x =>
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:590:      Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks P 0 0 Q)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:591:        (finSumFinEquiv (Sum.inr i)) x * φ x j)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:696:  toFun M := (Matrix.of (fun i j => M i (finSumFinEquiv (Sum.inl j))),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:697:              Matrix.of (fun i j => M i (finSumFinEquiv (Sum.inr j))))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:699:    Sum.elim (fun a => P.1 i a) (fun b => P.2 i b) (finSumFinEquiv.symm j)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:704:    change Sum.elim (fun a => M i (finSumFinEquiv (Sum.inl a)))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:705:        (fun b => M i (finSumFinEquiv (Sum.inr b))) (finSumFinEquiv.symm j) = M i j
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:706:    conv_rhs => rw [← Equiv.apply_symm_apply finSumFinEquiv j]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:707:    rcases finSumFinEquiv.symm j with c | d <;> simp only [Sum.elim_inl, Sum.elim_inr]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:713:    (matrixColSplit γ a b M).1 i j = M i (finSumFinEquiv (Sum.inl j)) := rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:716:    (matrixColSplit γ a b M).2 i j = M i (finSumFinEquiv (Sum.inr j)) := rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:722:        (X * Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks A 0 0 B))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:727:    rw [← finSumFinEquiv.sum_comp (fun x =>
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:728:      X i x * Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks A 0 0 B) x
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:729:        (finSumFinEquiv (Sum.inl j)))]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:736:    rw [← finSumFinEquiv.sum_comp (fun x =>
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:737:      X i x * Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks A 0 0 B) x
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:738:        (finSumFinEquiv (Sum.inr j)))]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:7:# `DLNFibre.Core.RadicalCatenary` — the catenary identity for a reducible (radical) locus
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:18:`le_antisymm` (no component-decomposition lemma, no radicality needed):
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:28:Zariski-closed `Z` (over an algebraically closed field its vanishing ideal is radical and proper),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:112:/-! ## The radical-locus catenary -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:117:Direct chain/coheight squeeze; no radicality needed. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:175:(its vanishing ideal is radical and proper), the geometric codimension plus the variety dimension

codex
I’m going to typecheck a tiny wrapper lemma in the pinned Lean checkout. That will catch namespace/import details for the radical-insensitivity statement before I give you a definitive answer.
exec
/bin/bash -lc "lake env lean --stdin <<'EOF'
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

open PrimeSpectrum

variable {R : Type*} [CommRing R]

lemma test_ringKrullDim_quotient_radical (I : Ideal R) :
    ringKrullDim (R ⧸ I.radical) = ringKrullDim (R ⧸ I) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient, zeroLocus_radical]

lemma test_ringKrullDim_quotient_radical' (I : Ideal R) :
    ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ I.radical) := by
  rw [test_ringKrullDim_quotient_radical]
EOF" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean
2026-06-24T17:44:23.605544Z ERROR codex_app_server::bespoke_event_handling: request failed with client error: JSONRPCErrorError { code: -32000, data: None, message: "command execution approval is not supported in exec mode for thread `019efaba-6d04-7331-bc41-0b1525b303af`" }
 exited 1:
2026-06-24T17:44:23.605803Z ERROR codex_core::tools::router: error=exec_command failed for `/bin/bash -lc "lake env lean --stdin <<'EOF'
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

open PrimeSpectrum

variable {R : Type*} [CommRing R]

lemma test_ringKrullDim_quotient_radical (I : Ideal R) :
    ringKrullDim (R ⧸ I.radical) = ringKrullDim (R ⧸ I) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient, zeroLocus_radical]

lemma test_ringKrullDim_quotient_radical' (I : Ideal R) :
    ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ I.radical) := by
  rw [test_ringKrullDim_quotient_radical]
EOF"`: CreateProcess { message: "Rejected(\"rejected by user\")" }
codex
The remaining gap is not reducedness; it is library coverage. Mathlib has basic Spec/zero-locus union lemmas, but I do not see an upstream affine-variety product-dimension or finite-union-dimension theorem that would make rungs 2 and 3 one-liners.
exec
/bin/bash -lc "sed -n '300,340p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Basic.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:

theorem zeroLocus_eq_univ_iff (s : Set R) :
    zeroLocus s = Set.univ ↔ s ⊆ nilradical R := by
  rw [← Set.univ_subset_iff, subset_zeroLocus_iff_subset_vanishingIdeal, vanishingIdeal_univ]

theorem zeroLocus_sup (I J : Ideal R) :
    zeroLocus ((I ⊔ J : Ideal R) : Set R) = zeroLocus I ∩ zeroLocus J :=
  (gc R).l_sup

theorem zeroLocus_union (s s' : Set R) : zeroLocus (s ∪ s') = zeroLocus s ∩ zeroLocus s' :=
  (gc_set R).l_sup

theorem vanishingIdeal_union (t t' : Set (PrimeSpectrum R)) :
    vanishingIdeal (t ∪ t') = vanishingIdeal t ⊓ vanishingIdeal t' :=
  (gc R).u_inf

theorem zeroLocus_iSup {ι : Sort*} (I : ι → Ideal R) :
    zeroLocus ((⨆ i, I i : Ideal R) : Set R) = ⋂ i, zeroLocus (I i) :=
  (gc R).l_iSup

theorem zeroLocus_iUnion {ι : Sort*} (s : ι → Set R) :
    zeroLocus (⋃ i, s i) = ⋂ i, zeroLocus (s i) :=
  (gc_set R).l_iSup

theorem zeroLocus_iUnion₂ {ι : Sort*} {κ : (i : ι) → Sort*} (s : ∀ i, κ i → Set R) :
    zeroLocus (⋃ (i) (j), s i j) = ⋂ (i) (j), zeroLocus (s i j) :=
  (gc_set R).l_iSup₂

theorem zeroLocus_bUnion (s : Set (Set R)) :
    zeroLocus (⋃ s' ∈ s, s' : Set R) = ⋂ s' ∈ s, zeroLocus s' := by simp only [zeroLocus_iUnion]

theorem vanishingIdeal_iUnion {ι : Sort*} (t : ι → Set (PrimeSpectrum R)) :
    vanishingIdeal (⋃ i, t i) = ⨅ i, vanishingIdeal (t i) :=
  (gc R).u_iInf

theorem zeroLocus_inf (I J : Ideal R) :
    zeroLocus ((I ⊓ J : Ideal R) : Set R) = zeroLocus I ∪ zeroLocus J :=
  Set.ext fun x => x.2.inf_le

theorem union_zeroLocus (s s' : Set R) :
    zeroLocus s ∪ zeroLocus s' = zeroLocus (Ideal.span s ⊓ Ideal.span s' : Ideal R) := by

exec
/bin/bash -lc 'rg -n "def vanishingIdeal|theorem vanishingIdeal|lemma vanishingIdeal|zeroLocus_eq|vanishingIdeal.*iUnion|vanishingIdeal.*union|radical|varietyDim" /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean -S | head -300' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:15:The main statement of the theorem is `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:61:def vanishingIdeal (V : Set (σ → K)) : Ideal (MvPolynomial σ k) where
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:73:theorem vanishingIdeal_anti_mono {A B : Set (σ → K)} (h : A ≤ B) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:76:theorem vanishingIdeal_empty : vanishingIdeal k (∅ : Set (σ → K)) = ⊤ :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:113:theorem radical_le_vanishingIdeal_zeroLocus (I : Ideal (MvPolynomial σ k)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:114:    I.radical ≤ vanishingIdeal k (zeroLocus K I) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:117:  rw [radical_eq_sInf] at hp
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:129:theorem vanishingIdeal_pointToPoint (V : Set (σ → K)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:171:theorem vanishingIdeal_zeroLocus_eq_radical (I : Ideal (MvPolynomial σ k)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:172:    vanishingIdeal k (zeroLocus K I) = I.radical := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:173:  refine le_antisymm ?_ (radical_le_vanishingIdeal_zeroLocus _)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:174:  rw [I.radical_eq_jacobson]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:182:@[simp high] -- This needs to fire before `vanishingIdeal_zeroLocus_eq_radical`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:185:  Trans.trans (vanishingIdeal_zeroLocus_eq_radical P) h.radical
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:20:   Nullstellensatz over `[IsAlgClosed k]`): `vanishingIdeal Z` is always **radical**
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:31:   irreducible"), `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ` (`ℕ∞`, additive — `ℕ∞`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:37:`axiom`. `varietyDim Z = ringKrullDim (R ⧸ vanishingIdeal Z)` is the Krull dimension of the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:66:/-- The vanishing ideal of any subset of `σ → k` is **radical** (over `[IsAlgClosed k]`): by the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:67:strong Nullstellensatz it equals its own radical, via `vanishingIdeal Z = vanishingIdeal (zeroLocus
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:68:(vanishingIdeal Z))` `= (vanishingIdeal Z).radical`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:69:theorem vanishingIdeal_isRadical [IsAlgClosed k] [Finite σ] (Z : Set (σ → k)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:71:  have h : vanishingIdeal k Z = (vanishingIdeal k Z).radical := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:74:        vanishingIdeal_zeroLocus_eq_radical (K := k)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:75:  rw [h]; exact radical_isRadical _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:87:Nullstellensatz forces `vanishingIdeal (zeroLocus (vanishingIdeal Z)) = (vanishingIdeal Z).radical`,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:97:    have h3 : vanishingIdeal k (zeroLocus k (vanishingIdeal k Z)) = (vanishingIdeal k Z).radical :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:98:      vanishingIdeal_zeroLocus_eq_radical (K := k) _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:100:    exact Ideal.radical_eq_top.mp h3.symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:139:noncomputable def varietyDim (Z : Set (σ → k)) : ℕ∞ :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:144:the ambient dimension `Nat.card σ`: `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ`. The
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:147:theorem height_vanishingIdeal_add_varietyDim_eq_card [Finite σ] {Z : Set (σ → k)}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:149:    (vanishingIdeal k Z).height + varietyDim Z = (Nat.card σ : ℕ∞) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:157:  rw [varietyDim, ← hm, WithBot.unbotD_coe]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:162:`height (vanishingIdeal Z) = Nat.card σ − varietyDim Z` for an irreducible variety `Z` (`ℕ∞`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:163:subtraction; lossless here since `varietyDim Z ≤ Nat.card σ`). The geometric codimension is the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:165:theorem height_vanishingIdeal_eq_card_sub_varietyDim [Finite σ] {Z : Set (σ → k)}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:167:    (vanishingIdeal k Z).height = (Nat.card σ : ℕ∞) - varietyDim Z := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:168:  have hadd := height_vanishingIdeal_add_varietyDim_eq_card hp
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:169:  have hne : varietyDim Z ≠ ⊤ := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:182:`height_vanishingIdeal_add_varietyDim_eq_card` at `σ := RepCoord d`, `Z := coord '' Z`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:183:theorem codimRep_add_varietyDim_eq_card [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:186:    codimRep coord Z + varietyDim (coord '' Z) = (Nat.card (RepCoord d) : ℕ∞) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:187:  height_vanishingIdeal_add_varietyDim_eq_card hp
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:190:varietyDim (coord '' Z)` for an irreducible variety `coord '' Z`: geometric codimension `=` ambient
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:192:theorem codimRep_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:195:    codimRep coord Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (coord '' Z) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:196:  height_vanishingIdeal_eq_card_sub_varietyDim hp
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:199:`canonicalCoord d`, `codimRepCanonical Z = Nat.card (RepCoord d) − varietyDim (canonicalCoord d ''
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:201:theorem codimRepCanonical_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:205:    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:206:  codimRep_eq_card_sub_varietyDim (canonicalCoord d) Z hp
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:213:theorem vanishingIdeal_univ_eq_bot [IsAlgClosed k] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:225:alg-closed, `σ` finite), the vanishing ideal is `⊥` (prime), `varietyDim = Nat.card σ`, the bridge
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:230:      + varietyDim (Set.univ : Set (σ → k)) = (Nat.card σ : ℕ∞) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:233:  exact height_vanishingIdeal_add_varietyDim_eq_card this

exec
/bin/bash -lc "sed -n '120,180p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean && sed -n '60,105p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
    MvPolynomial.renameEquiv k (Fintype.equivFin σ) with he
  set q : Ideal (MvPolynomial (Fin (Fintype.card σ)) k) :=
    p.map (e : MvPolynomial σ k →+* MvPolynomial (Fin (Fintype.card σ)) k) with hq
  haveI : q.IsPrime := by rw [hq]; exact Ideal.map_isPrime_of_equiv e
  have hheight : q.height = p.height := height_map_algEquiv e p
  have hdim : ringKrullDim (MvPolynomial (Fin (Fintype.card σ)) k ⧸ q)
      = ringKrullDim (MvPolynomial σ k ⧸ p) :=
    ringKrullDim_quotient_map_algEquiv e p
  have key := height_add_ringKrullDim_quotient_eq k (Fintype.card σ) q
  rw [hheight, hdim] at key
  rw [Nat.card_eq_fintype_card]
  exact_mod_cast key

/-! ## The variety dimension and the bridge headline -/

/-- The **variety dimension** of `Z ⊆ (σ → k)`: the Krull dimension of the coordinate ring
`MvPolynomial σ k ⧸ vanishingIdeal Z` of `Z`'s Zariski closure, as an `ℕ∞` (the `⊥` from a trivial
quotient — absent here, since the relevant `vanishingIdeal Z` is prime — defaulting to `0`). It is
the dimension of `Z` itself exactly when `Z` is Zariski-closed (`IsZariskiClosed`). -/
noncomputable def varietyDim (Z : Set (σ → k)) : ℕ∞ :=
  (ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal k Z)).unbotD 0

/-- **The codimension bridge (additive, `ℕ∞`).** For an irreducible variety `Z ⊆ (σ → k)` — i.e.
`(vanishingIdeal Z).IsPrime` — the height of its vanishing ideal plus its variety dimension equals
the ambient dimension `Nat.card σ`: `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ`. The
catenary identity over `σ`, read at the prime `vanishingIdeal Z`. Geometric codimension `=` ambient
`−` variety dimension, in lossless additive form. -/
theorem height_vanishingIdeal_add_varietyDim_eq_card [Finite σ] {Z : Set (σ → k)}
    (hp : (vanishingIdeal k Z : Ideal (MvPolynomial σ k)).IsPrime) :
    (vanishingIdeal k Z).height + varietyDim Z = (Nat.card σ : ℕ∞) := by
  have key := height_add_ringKrullDim_quotient_eq_card (vanishingIdeal k Z)
  haveI : Nontrivial (MvPolynomial σ k ⧸ vanishingIdeal k Z) :=
    Ideal.Quotient.nontrivial_iff.mpr hp.ne_top
  have hne : ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal k Z) ≠ ⊥ :=
    fun h ↦ by simpa [h] using
      ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial σ k ⧸ vanishingIdeal k Z)
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [varietyDim, ← hm, WithBot.unbotD_coe]
  rw [← hm] at key
  exact_mod_cast key

/-- **The codimension bridge (subtraction, `ℕ∞`).** Equivalent reading of the additive bridge:
`height (vanishingIdeal Z) = Nat.card σ − varietyDim Z` for an irreducible variety `Z` (`ℕ∞`
subtraction; lossless here since `varietyDim Z ≤ Nat.card σ`). The geometric codimension is the
ambient dimension minus the variety dimension. -/
theorem height_vanishingIdeal_eq_card_sub_varietyDim [Finite σ] {Z : Set (σ → k)}
    (hp : (vanishingIdeal k Z : Ideal (MvPolynomial σ k)).IsPrime) :
    (vanishingIdeal k Z).height = (Nat.card σ : ℕ∞) - varietyDim Z := by
  have hadd := height_vanishingIdeal_add_varietyDim_eq_card hp
  have hne : varietyDim Z ≠ ⊤ := by
    intro h
    rw [h, add_top] at hadd
    exact (ENat.coe_ne_top (Nat.card σ)) hadd.symm
  exact (ENat.addLECancellable_of_ne_top hne).eq_tsub_of_add_eq hadd

/-! ## Specialisation to `codimRep` (the geometry layer's consumer) -/

variable {N : ℕ}

/-- **The bridge at `codimRep` (additive).** For any coordinatisation `coord` and a subset `Z ⊆
Rep_d` whose image `coord '' Z` is an irreducible variety, the geometric codimension `codimRep coord
`pointToPoint` is irreducible — the point-space irreducibility read through the prime spectrum. -/
def IsZariskiIrreducible (Z : Set (σ → k)) : Prop :=
  IsIrreducible (MvPolynomial.pointToPoint (k := k) (K := k) '' Z)

/-! ## Nullstellensatz pieces (over an algebraically closed field) -/

/-- The vanishing ideal of any subset of `σ → k` is **radical** (over `[IsAlgClosed k]`): by the
strong Nullstellensatz it equals its own radical, via `vanishingIdeal Z = vanishingIdeal (zeroLocus
(vanishingIdeal Z))` `= (vanishingIdeal Z).radical`. -/
theorem vanishingIdeal_isRadical [IsAlgClosed k] [Finite σ] (Z : Set (σ → k)) :
    (vanishingIdeal k Z : Ideal (MvPolynomial σ k)).IsRadical := by
  have h : vanishingIdeal k Z = (vanishingIdeal k Z).radical := by
    conv_lhs =>
      rw [← (zeroLocus_vanishingIdeal_galoisConnection (σ := σ) (k := k) (K := k)).u_l_u_eq_u Z,
        vanishingIdeal_zeroLocus_eq_radical (K := k)]
  rw [h]; exact radical_isRadical _

/-- **Irreducible ⟺ prime vanishing ideal.** `Z` is Zariski-irreducible iff its vanishing ideal is
prime — the algebraic translation of geometric irreducibility, via the `pointToPoint` image and
`PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime`. -/
theorem isZariskiIrreducible_iff_isPrime_vanishingIdeal (Z : Set (σ → k)) :
    IsZariskiIrreducible Z ↔ (vanishingIdeal k Z : Ideal (MvPolynomial σ k)).IsPrime := by
  unfold IsZariskiIrreducible
  rw [PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime, vanishingIdeal_pointToPoint]

/-- **Closed + prime ⟹ nonempty (weak Nullstellensatz).** A Zariski-closed `Z` whose vanishing ideal
is prime (hence proper) is nonempty: if `Z = ∅` then `vanishingIdeal Z = ⊤`, but the strong
Nullstellensatz forces `vanishingIdeal (zeroLocus (vanishingIdeal Z)) = (vanishingIdeal Z).radical`,
contradicting primality. -/
theorem nonempty_of_isZariskiClosed_of_isPrime_vanishingIdeal [IsAlgClosed k] [Finite σ]
    {Z : Set (σ → k)} (hZ : IsZariskiClosed Z)
    (hp : (vanishingIdeal k Z : Ideal (MvPolynomial σ k)).IsPrime) :
    Z.Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro hempty
  have htop : vanishingIdeal k Z = ⊤ := by
    have h2 : zeroLocus k (vanishingIdeal k Z) = (∅ : Set (σ → k)) := hZ ▸ hempty
    have h3 : vanishingIdeal k (zeroLocus k (vanishingIdeal k Z)) = (vanishingIdeal k Z).radical :=
      vanishingIdeal_zeroLocus_eq_radical (K := k) _
    rw [h2, vanishingIdeal_empty] at h3
    exact Ideal.radical_eq_top.mp h3.symm
  exact hp.ne_top htop

/-! ## Finite-index dimension transport: the catenary identity over a `Fintype` index -/

/-- The Krull dimension of `MvPolynomial σ k` over a finite index `σ` is `Nat.card σ` (a field has

codex
One more adversarial point: the project’s `varietyDim` itself says it is the dimension of the Zariski closure unless the set is closed. That is fine for radical-insensitivity, but for chart opens and exact-rank strata you must explicitly account for “open chart has same closure dimension” or use the cited `hClosure` bridge.
exec
/bin/bash -lc "sed -n '1,240p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Fangming Li, Joachim Breitner
-/
module

public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.SuccPred.WithBot
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Order.Atoms
public import Mathlib.Order.RelSeries
public import Mathlib.Tactic.FinCases

/-!
# Krull dimension of a preordered set and height of an element

If `α` is a preordered set, then `krullDim α : WithBot ℕ∞` is defined to be
`sup {n | a₀ < a₁ < ... < aₙ}`.

In case that `α` is empty, then its Krull dimension is defined to be negative infinity; if the
length of all series `a₀ < a₁ < ... < aₙ` is unbounded, then its Krull dimension is defined to be
positive infinity.

For `a : α`, its height (in `ℕ∞`) is defined to be `sup {n | a₀ < a₁ < ... < aₙ ≤ a}`, while its
coheight is defined to be `sup {n | a ≤ a₀ < a₁ < ... < aₙ}` .

## Main results

* The Krull dimension is the same as that of the dual order (`krullDim_orderDual`).

* The Krull dimension is the supremum of the heights of the elements (`krullDim_eq_iSup_height`),
  or their coheights (`krullDim_eq_iSup_coheight`), or their sums of height and coheight
  (`krullDim_eq_iSup_height_add_coheight_of_nonempty`)

* The height in the dual order equals the coheight, and vice versa.

* The height is monotone (`height_mono`), and strictly monotone if finite (`height_strictMono`).

* The coheight is antitone (`coheight_anti`), and strictly antitone if finite
  (`coheight_strictAnti`).

* The height is the supremum of the successor of the height of all smaller elements
  (`height_eq_iSup_lt_height`).

* The elements of height zero are the minimal elements (`height_eq_zero`), and the elements of
  height `n` are minimal among those of height `≥ n` (`height_eq_coe_iff_minimal_le_height`).

* Concrete calculations for the height, coheight and Krull dimension in `ℕ`, `ℤ`, `WithTop`,
  `WithBot` and `ℕ∞`.

## Design notes

Krull dimensions are defined to take value in `WithBot ℕ∞` so that `(-∞) + (+∞)` is
also negative infinity. This is because we want Krull dimensions to be additive with respect
to product of varieties so that `-∞` being the Krull dimension of empty variety is equal to
sum of `-∞` and the Krull dimension of any other varieties.

We could generalize the notion of Krull dimension to an arbitrary binary relation; many results
in this file would generalize as well. But we don't think it would be useful, so we only define
Krull dimension of a preorder.
-/

@[expose] public section

assert_not_exists Field

namespace Order

section definitions

/--
The **Krull dimension** of a preorder `α` is the supremum of the rightmost index of all relation
series of `α` ordered by `<`. If there is no series `a₀ < a₁ < ... < aₙ` in `α`, then its Krull
dimension is defined to be negative infinity; if the length of all series `a₀ < a₁ < ... < aₙ` is
unbounded, its Krull dimension is defined to be positive infinity.
-/
noncomputable def krullDim (α : Type*) [Preorder α] : WithBot ℕ∞ :=
  ⨆ (p : LTSeries α), p.length

/--
The **height** of an element `a` in a preorder `α` is the supremum of the rightmost index of all
relation series of `α` ordered by `<` and ending below or at `a`. In other words, it is
the largest `n` such that there's a series `a₀ < a₁ < ... < aₙ = a` (or `∞` if there is
no largest `n`).
-/
noncomputable def height {α : Type*} [Preorder α] (a : α) : ℕ∞ :=
  ⨆ (p : LTSeries α) (_ : p.last ≤ a), p.length

/--
The **coheight** of an element `a` in a preorder `α` is the supremum of the rightmost index of all
relation series of `α` ordered by `<` and beginning with `a`. In other words, it is
the largest `n` such that there's a series `a = a₀ < a₁ < ... < aₙ` (or `∞` if there is
no largest `n`).

The definition of `coheight` is via the `height` in the dual order, in order to easily transfer
theorems between `height` and `coheight`. See `coheight_eq` for the definition with a
series ordered by `<` and beginning with `a`.
-/
noncomputable def coheight {α : Type*} [Preorder α] (a : α) : ℕ∞ := height (α := αᵒᵈ) a

end definitions

/-!
## Height
-/

section height

variable {α β : Type*}

variable [Preorder α] [Preorder β]

@[simp] lemma height_toDual (x : α) : height (OrderDual.toDual x) = coheight x := rfl
@[simp] lemma height_ofDual (x : αᵒᵈ) : height (OrderDual.ofDual x) = coheight x := rfl
@[simp] lemma coheight_toDual (x : α) : coheight (OrderDual.toDual x) = height x := rfl
@[simp] lemma coheight_ofDual (x : αᵒᵈ) : coheight (OrderDual.ofDual x) = height x := rfl

/--
The **coheight** of an element `a` in a preorder `α` is the supremum of the rightmost index of all
relation series of `α` ordered by `<` and beginning with `a`.

This is not the definition of `coheight`. The definition of `coheight` is via the `height` in the
dual order, in order to easily transfer theorems between `height` and `coheight`.
-/
lemma coheight_eq (a : α) :
    coheight a = ⨆ (p : LTSeries α) (_ : a ≤ p.head), (p.length : ℕ∞) := by
  apply Equiv.iSup_congr ⟨RelSeries.reverse, RelSeries.reverse, fun _ ↦ RelSeries.reverse_reverse _,
    fun _ ↦ RelSeries.reverse_reverse _⟩
  congr! 1

lemma height_le_iff {a : α} {n : ℕ∞} :
    height a ≤ n ↔ ∀ ⦃p : LTSeries α⦄, p.last ≤ a → p.length ≤ n := by
  rw [height, iSup₂_le_iff]

lemma coheight_le_iff {a : α} {n : ℕ∞} :
    coheight a ≤ n ↔ ∀ ⦃p : LTSeries α⦄, a ≤ p.head → p.length ≤ n := by
  rw [coheight_eq, iSup₂_le_iff]

lemma height_le {a : α} {n : ℕ∞} (h : ∀ (p : LTSeries α), p.last = a → p.length ≤ n) :
    height a ≤ n := by
  apply height_le_iff.mpr
  intro p hlast
  wlog hlenpos : p.length ≠ 0
  · simp_all
  -- We replace the last element in the series with `a`
  let p' := p.eraseLast.snoc a (lt_of_lt_of_le (p.eraseLast_last_rel_last (by simp_all)) hlast)
  rw [show p.length = p'.length by simp [p']; lia]
  apply h
  simp [p']

/--
Variant of `height_le_iff` ranging only over those series that end exactly on `a`.
-/
lemma height_le_iff' {a : α} {n : ℕ∞} :
    height a ≤ n ↔ ∀ ⦃p : LTSeries α⦄, p.last = a → p.length ≤ n := by
  constructor
  · rw [height_le_iff]
    exact fun h p hlast => h (le_of_eq hlast)
  · exact height_le

/--
Alternative definition of height, with the supremum ranging only over those series that end at `a`.
-/
lemma height_eq_iSup_last_eq (a : α) :
    height a = ⨆ (p : LTSeries α) (_ : p.last = a), ↑(p.length) := by
  apply eq_of_forall_ge_iff
  intro n
  rw [height_le_iff', iSup₂_le_iff]

set_option backward.isDefEq.respectTransparency false in
/--
Alternative definition of coheight, with the supremum only ranging over those series
that begin at `a`.
-/
lemma coheight_eq_iSup_head_eq (a : α) :
    coheight a = ⨆ (p : LTSeries α) (_ : p.head = a), ↑(p.length) := by
  change height (α := αᵒᵈ) a = ⨆ (p : LTSeries α) (_ : p.head = a), ↑(p.length)
  rw [height_eq_iSup_last_eq]
  apply Equiv.iSup_congr ⟨RelSeries.reverse, RelSeries.reverse, fun _ ↦ RelSeries.reverse_reverse _,
    fun _ ↦ RelSeries.reverse_reverse _⟩
  simp

/--
Variant of `coheight_le_iff` ranging only over those series that begin exactly on `a`.
-/
lemma coheight_le_iff' {a : α} {n : ℕ∞} :
    coheight a ≤ n ↔ ∀ ⦃p : LTSeries α⦄, p.head = a → p.length ≤ n := by
  rw [coheight_eq_iSup_head_eq, iSup₂_le_iff]

lemma coheight_le {a : α} {n : ℕ∞} (h : ∀ (p : LTSeries α), p.head = a → p.length ≤ n) :
    coheight a ≤ n :=
  coheight_le_iff'.mpr h

lemma length_le_height {p : LTSeries α} {x : α} (hlast : p.last ≤ x) :
    p.length ≤ height x := by
  by_cases hlen0 : p.length ≠ 0
  · let p' := p.eraseLast.snoc x (by
      apply lt_of_lt_of_le
      · apply p.step ⟨p.length - 1, by lia⟩
      · convert hlast
        simp only [Fin.succ_mk, RelSeries.last, Fin.last]
        congr; lia)
    suffices p'.length ≤ height x by
      simp only [RelSeries.snoc_length, RelSeries.eraseLast_length, Nat.cast_add, ENat.coe_sub,
        Nat.cast_one, p'] at this
      convert this
      norm_cast
      lia
    refine le_iSup₂_of_le p' ?_ le_rfl
    simp [p']
  · simp_all

set_option backward.isDefEq.respectTransparency false in
lemma length_le_coheight {x : α} {p : LTSeries α} (hhead : x ≤ p.head) :
    p.length ≤ coheight x :=
  length_le_height (α := αᵒᵈ) (p := p.reverse) (by simpa)

/--
The height of the last element in a series is larger or equal to the length of the series.
-/
lemma length_le_height_last {p : LTSeries α} : p.length ≤ height p.last :=
  length_le_height le_rfl

/--
The coheight of the first element in a series is larger or equal to the length of the series.
-/
lemma length_le_coheight_head {p : LTSeries α} : p.length ≤ coheight p.head :=
  length_le_coheight le_rfl

/--
The height of an element in a series is larger or equal to its index in the series.
-/
lemma index_le_height (p : LTSeries α) (i : Fin (p.length + 1)) : i ≤ height (p i) :=
  length_le_height_last (p := p.take i)

/--
The coheight of an element in a series is larger or equal to its reverse index in the series.
-/
lemma rev_index_le_coheight (p : LTSeries α) (i : Fin (p.length + 1)) : i.rev ≤ coheight (p i) := by

exec
/bin/bash -lc "rg -n \"krullDim.*union|union.*krullDim|krullDim.*max|max.*krullDim|iSup.*krullDim|krullDim.*iSup|krullDim.*sum|sum.*krullDim|Order\\.krullDim\" /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Topology /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory -S | head -500" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Length.lean:33:  (Order.krullDim (Submodule R M)).unbot (by simp [Order.krullDim_eq_bot_iff])
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Length.lean:36:    (Module.length R M : WithBot ℕ∞) = Order.krullDim (Submodule R M) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Length.lean:51:    Order.krullDim_eq_zero_iff_of_orderTop, Submodule.subsingleton_iff]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Length.lean:76:  · rw [Order.krullDim, iSup_le_iff]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Length.lean:87:  rw [← WithBot.coe_inj, WithBot.coe_top, coe_length, Order.krullDim_eq_top_iff,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Length.lean:113:  rw [Order.height_eq_krullDim_Iic, coe_length, Order.krullDim_eq_of_orderIso (Submodule.mapIic _)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Length.lean:119:    Order.krullDim_eq_of_orderIso (Submodule.comapMkQRelIso N)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Length.lean:125:    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap e)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Length.lean:133:    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f Function.bijective_id)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Length.lean:275:    Order.krullDim_eq_one_iff_of_boundedOrder, isSimpleModule_iff]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:1280:  Order.krullDim_le_one_iff_of_boundedOrder.mp Order.KrullDimLE.krullDim_le _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:1288:  Order.krullDim_orderDual.symm.trans <| Order.krullDim_eq_of_orderIso
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:68:    ← isArtinianRing_iff_krullDimLE_zero, isArtinianRing_iff_isNilpotent_maximalIdeal,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Height.lean:296:  rw [ringKrullDim, Order.krullDim_eq_iSup_height, iSup_le_iff]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Height.lean:321:  exact Order.krullDim_eq_of_orderIso
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Height.lean:470:lemma Ring.krullDimLE_of_isLocalization_maximal {n : ℕ}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Zero.lean:55:  rw [Ring.KrullDimLE, Order.krullDimLE_iff, le_antisymm_iff, ← ringKrullDim, Nat.cast_zero,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Zero.lean:150:  ⟨Order.krullDim_nonpos_of_subsingleton⟩
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Basic.lean:40:    KrullDimLE n R ↔ ringKrullDim R ≤ n := Order.krullDimLE_iff n (PrimeSpectrum R)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Basic.lean:103:  simp_rw [Ring.KrullDimLE, Order.krullDimLE_iff, Nat.cast_zero,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Basic.lean:104:    Order.krullDim_nonpos_iff_forall_isMax,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Basic.lean:149:  simp_rw [Ring.KrullDimLE, Order.krullDimLE_iff, Nat.cast_one,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Basic.lean:150:    Order.krullDim_le_one_iff, (PrimeSpectrum.equivSubtype R).forall_congr_left,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Basic.lean:161:  simp_rw [Ring.KrullDimLE, Order.krullDimLE_iff, Nat.cast_one,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Basic.lean:162:    Order.krullDim_le_one_iff_forall_isMax, (PrimeSpectrum.equivSubtype R).forall_congr_left,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Polynomial.lean:34:  apply Order.krullDim_le_of_krullDim_preimage_le' (PrimeSpectrum.comap C) ?_ (fun p ↦ ?_)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Polynomial.lean:36:  · rw [show C = (algebraMap R (Polynomial R)) from rfl, Order.krullDim_eq_of_orderIso
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:73:  grw [le_tsub_add (b := p.length) (a := 1), Nat.cast_add_one, supportDim, Order.krullDim,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:86:  simp only [supportDim, Order.krullDim_eq_iSup_length]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Module.lean:100:      simp only [Module.supportDim, gt_iff_lt, Order.krullDim_pos_iff, Subtype.exists,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:33:    ringKrullDim (R ⧸ I) = Order.krullDim (PrimeSpectrum.zeroLocus (R := R) I) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:34:  rw [ringKrullDim, Order.krullDim_eq_of_orderIso I.primeSpectrumQuotientOrderIsoZeroLocus]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:47:  rw [ringKrullDim_quotient, Order.krullDim_eq_iSup_length, ringKrullDim,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:48:    Order.krullDim_eq_iSup_length, ← WithBot.coe_one, ← WithBot.coe_add,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/OrderOfVanishing.lean:164:  rw [isArtinianRing_iff_krullDimLE_zero, Ring.KrullDimLE, Order.krullDimLE_iff,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:32:* The Krull dimension is the supremum of the heights of the elements (`krullDim_eq_iSup_height`),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:33:  or their coheights (`krullDim_eq_iSup_coheight`), or their sums of height and coheight
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:34:  (`krullDim_eq_iSup_height_add_coheight_of_nonempty`)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:579:  rw [eq_bot_iff, krullDim, iSup_le_iff]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:601:  simp only [krullDim, iSup_le_iff, isMax_iff_forall_not_lt]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:613:  simp_rw [isMax_iff_forall_not_lt, isMin_iff_forall_not_lt, krullDim, iSup_le_iff]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:651:    (krullDim_nonpos_iff_forall_isMax.mp H.le ⊥ bot_le), fun _ ↦ Order.krullDim_eq_zero⟩
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:655:  rw [← not_subsingleton_iff_nontrivial, ← Order.krullDim_eq_zero_iff_of_orderBot,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:657:  simp [Order.krullDim_nonneg]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:666:    (krullDim_nonpos_iff_forall_isMin.mp H.le ⊤ le_top), fun _ ↦ Order.krullDim_eq_zero⟩
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:670:  rw [← not_subsingleton_iff_nontrivial, ← Order.krullDim_eq_zero_iff_of_orderTop,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:672:  simp [Order.krullDim_nonneg]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:676:  simp [Order.krullDim_le_one_iff]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:721:lemma krullDim_eq_iSup_length [Nonempty α] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:723:  simp [krullDim, WithBot.coe_iSup (OrderTop.bddAbove _), WithBot.coe_natCast]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:750:  rw [krullDim_eq_iSup_length]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:771:If `α` were empty, then `krullDim α = ⊥`. See `krullDim_eq_iSup_height` for the more general
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:774:lemma krullDim_eq_iSup_height_of_nonempty [Nonempty α] : krullDim α = ↑(⨆ (a : α), height a) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:790:If `α` were empty, then `krullDim α = ⊥`. See `krullDim_eq_iSup_coheight` for the more general
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:793:lemma krullDim_eq_iSup_coheight_of_nonempty [Nonempty α] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:795:  simpa using krullDim_eq_iSup_height_of_nonempty (α := αᵒᵈ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:800:lemma krullDim_eq_iSup_height_add_coheight_of_nonempty [Nonempty α] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:803:  · rw [krullDim_eq_iSup_height_of_nonempty, WithBot.coe_le_coe]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:807:    rw [krullDim_eq_iSup_length, WithBot.coe_le_coe]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:825:If `α` is `Nonempty`, then `krullDim_eq_iSup_height_of_nonempty`, with the coercion from
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:828:lemma krullDim_eq_iSup_height : krullDim α = ⨆ (a : α), ↑(height a) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:830:  | inl h => rw [krullDim_eq_bot, ciSup_of_empty]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:831:  | inr h => rw [krullDim_eq_iSup_height_of_nonempty, WithBot.coe_iSup (OrderTop.bddAbove _)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:836:If `α` is `Nonempty`, then `krullDim_eq_iSup_coheight_of_nonempty`, with the coercion from
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:839:lemma krullDim_eq_iSup_coheight : krullDim α = ⨆ (a : α), ↑(coheight a) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:841:  | inl h => rw [krullDim_eq_bot, ciSup_of_empty]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:842:  | inr h => rw [krullDim_eq_iSup_coheight_of_nonempty, WithBot.coe_iSup (OrderTop.bddAbove _)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:846:  rw [krullDim_eq_iSup_length]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:873:  rw [coheight, ← krullDim_orderDual, Order.krullDim_eq_of_orderIso (OrderIso.refl _)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:922:    Order.krullDim_pos_iff_of_orderBot, isSimpleOrder_iff, and_comm]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:969:  simp [krullDim_eq_iSup_coheight, coheight_of_noMaxOrder]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:972:  simp [krullDim_eq_iSup_height, height_of_noMinOrder]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:1043:  rw [← height_top_eq_krullDim, krullDim_eq_iSup_height_of_nonempty, height_eq_iSup_lt_height]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:1077:variable {m : ℕ} (f : α →o β) (h : ∀ (x : β), Order.krullDim (f ⁻¹' {x}) ≤ m)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:1118:    Order.krullDim α ≤ (m + 1) * Order.krullDim β + m := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:1119:  rw [Order.krullDim_eq_iSup_height, Order.krullDim_eq_iSup_height, iSup_le_iff]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:1127:    (h : ∀ (x : β), Order.krullDim (f ⁻¹' {x}) ≤ m) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:1128:    Order.krullDim α ≤ (m + 1) * Order.krullDim β + m :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:1129:  Order.krullDim_le_of_krullDim_preimage_le ⟨f, h_mono⟩ h
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/LocalProperties/Semilocal.lean:129:    Ring.krullDimLE_of_isLocalization_maximal Rₚ fun P _ => inferInstance

codex
I’m done with the source pass. The verdict is going to be: yes on non-circularity, but no on “mostly Mathlib already has the dimension-rung infrastructure.” The product and finite-glue theorems are the real new work, not reducedness.
codex
**Verdict: YES.** The set-level/`varietyDim` route dodges the R2-3b-4 circularity. The old circularity was specific to building a scheme/ring iso through the *generator* ideal and needing `sigmaIdeal ≤ ker`. If you work with sets and `vanishingIdeal`, the coordinate rings are already reduced-by-definition, and the required ideal containment for pullbacks is the tautological one: “a polynomial vanishing on the target pulls back to one vanishing on the source.”

1. **Radical-insensitivity:** yes. I do not see a prepackaged v4.29 lemma named exactly `ringKrullDim_quotient_radical`, but it is a two-line lemma from Mathlib:
```lean
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

lemma ringKrullDim_quotient_radical {R : Type*} [CommRing R] (I : Ideal R) :
    ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ I.radical) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient, PrimeSpectrum.zeroLocus_radical]
```
The relevant upstream pieces are `ringKrullDim_quotient` and `PrimeSpectrum.zeroLocus_radical`. So `varietyDim` genuinely only sees the radical/closed-set structure.

2. **Set-level chart trivialization:** non-circular, provided you keep it genuinely set/reduced-level. The proof should use:
`A ∈ mult⁻¹(U) ∩ Σ^r`,
the pointwise gauge-normalization,
equivariance of `mult`,
and `mult(gauge_B • A) = E`.
None of that needs `sigmaIdeal ≤ ker`. The warning is different: a bare set bijection does not preserve `varietyDim`; you need the map and inverse to be regular on the pivot chart, typically via localization/principal-open coordinates. That is new chart algebra, but not the old reducedness circularity.

3. **Product dimension:** mathematically yes:
`dim (U × F) = dim U + dim F`
over an algebraically closed field, and reducibility is harmless:
`max_{i,j}(dim X_i + dim Y_j) = max_i dim X_i + max_j dim Y_j`.
But I do not see this as an existing Mathlib v4.29 theorem for `varietyDim`, nor a general
`ringKrullDim (A ⊗[k] B) = ringKrullDim A + ringKrullDim B`.
`trdeg_add_eq` exists, but it is tower additivity, not the tensor-product product theorem. This rung is real new infrastructure.

4. **Finite glue:** mathematically yes:
`dim (⋃ᵢ Zᵢ) = maxᵢ dim Zᵢ` for finite nonempty covers, radical-insensitively. Mathlib has the Spec-level zero-locus/vanishing-ideal union facts, e.g. `PrimeSpectrum.vanishingIdeal_union`, `PrimeSpectrum.vanishingIdeal_iUnion`, `PrimeSpectrum.zeroLocus_inf`, but I do not see a ready `varietyDim_finite_iUnion` theorem. Also note your `varietyDim` sends the empty set to `0` via `unbotD 0`, so state product/union lemmas with the relevant nonemptiness assumptions.

5. **Rung decomposition:**
- Single chart: prove regular set-level trivialization
  `mult⁻¹(U_P) ∩ Σ^r ≅ U_P × F_E`.
  New, but non-circular.
- Per chart: use regular-isomorphism invariance plus product dimension:
  `varietyDim(chart) = varietyDim U_P + varietyDim F = δ + varietyDim F`.
  Product dimension is the main new Mathlib gap.
- Glue: finite pivot cover gives global dimension by finite-union max; use the closure/open-chart bridge carefully because `varietyDim` is closure dimension for arbitrary sets.

So the de-risk claim is correct: radical-insensitivity of `varietyDim` removes the need to prove `fibreGenIdeal = radical fibreGenIdeal` or `sigmaIdeal ≤ ker` for the generator-level scheme iso. The remaining risk is library/build cost for product dimension and finite-glue lemmas, not circularity.
tokens used
151,035
**Verdict: YES.** The set-level/`varietyDim` route dodges the R2-3b-4 circularity. The old circularity was specific to building a scheme/ring iso through the *generator* ideal and needing `sigmaIdeal ≤ ker`. If you work with sets and `vanishingIdeal`, the coordinate rings are already reduced-by-definition, and the required ideal containment for pullbacks is the tautological one: “a polynomial vanishing on the target pulls back to one vanishing on the source.”

1. **Radical-insensitivity:** yes. I do not see a prepackaged v4.29 lemma named exactly `ringKrullDim_quotient_radical`, but it is a two-line lemma from Mathlib:
```lean
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

lemma ringKrullDim_quotient_radical {R : Type*} [CommRing R] (I : Ideal R) :
    ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ I.radical) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient, PrimeSpectrum.zeroLocus_radical]
```
The relevant upstream pieces are `ringKrullDim_quotient` and `PrimeSpectrum.zeroLocus_radical`. So `varietyDim` genuinely only sees the radical/closed-set structure.

2. **Set-level chart trivialization:** non-circular, provided you keep it genuinely set/reduced-level. The proof should use:
`A ∈ mult⁻¹(U) ∩ Σ^r`,
the pointwise gauge-normalization,
equivariance of `mult`,
and `mult(gauge_B • A) = E`.
None of that needs `sigmaIdeal ≤ ker`. The warning is different: a bare set bijection does not preserve `varietyDim`; you need the map and inverse to be regular on the pivot chart, typically via localization/principal-open coordinates. That is new chart algebra, but not the old reducedness circularity.

3. **Product dimension:** mathematically yes:
`dim (U × F) = dim U + dim F`
over an algebraically closed field, and reducibility is harmless:
`max_{i,j}(dim X_i + dim Y_j) = max_i dim X_i + max_j dim Y_j`.
But I do not see this as an existing Mathlib v4.29 theorem for `varietyDim`, nor a general
`ringKrullDim (A ⊗[k] B) = ringKrullDim A + ringKrullDim B`.
`trdeg_add_eq` exists, but it is tower additivity, not the tensor-product product theorem. This rung is real new infrastructure.

4. **Finite glue:** mathematically yes:
`dim (⋃ᵢ Zᵢ) = maxᵢ dim Zᵢ` for finite nonempty covers, radical-insensitively. Mathlib has the Spec-level zero-locus/vanishing-ideal union facts, e.g. `PrimeSpectrum.vanishingIdeal_union`, `PrimeSpectrum.vanishingIdeal_iUnion`, `PrimeSpectrum.zeroLocus_inf`, but I do not see a ready `varietyDim_finite_iUnion` theorem. Also note your `varietyDim` sends the empty set to `0` via `unbotD 0`, so state product/union lemmas with the relevant nonemptiness assumptions.

5. **Rung decomposition:**
- Single chart: prove regular set-level trivialization
  `mult⁻¹(U_P) ∩ Σ^r ≅ U_P × F_E`.
  New, but non-circular.
- Per chart: use regular-isomorphism invariance plus product dimension:
  `varietyDim(chart) = varietyDim U_P + varietyDim F = δ + varietyDim F`.
  Product dimension is the main new Mathlib gap.
- Glue: finite pivot cover gives global dimension by finite-union max; use the closure/open-chart bridge carefully because `varietyDim` is closure dimension for arbitrary sets.

So the de-risk claim is correct: radical-insensitivity of `varietyDim` removes the need to prove `fibreGenIdeal = radical fibreGenIdeal` or `sigmaIdeal ≤ ker` for the generator-level scheme iso. The remaining risk is library/build cost for product dimension and finite-glue lemmas, not circularity.
