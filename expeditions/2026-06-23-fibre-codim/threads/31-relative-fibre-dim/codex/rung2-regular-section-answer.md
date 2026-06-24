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
session id: 019efac4-d415-73b1-9619-78506d57fd65
--------
user
# Codex consult — rung 2: the REGULAR-section gap in the single-chart trivialization (Lean v4.29)

Route (c), rung 2. Goal: a `varietyDim`-preserving (REGULAR, not bare-set) trivialization of one
pivot chart, `mult⁻¹(U_P) ∩ Σ^r ≅_reg U_P × F`, so that `varietyDim(chart) = varietyDim U_P +
varietyDim F = δ + varietyDim F`.

## The gap I hit

The LANDED `exists_baseChange_of_rank_eq` is EXISTENTIAL: for each rank-r target `B` it gives SOME
`P ∈ H = GL_{d_N}×GL_{d_0}` with `P_N·E·P_0⁻¹ = B` (E = the standard rank-r `diag(I_r,0)`). The sweep
`Σ^r = ⋃_P (P•·)''F` is then a set-union. But a per-point existential `P` does NOT give a REGULAR
map `U_P → H` (a section), and Codex's own prior warning was: a bare set bijection does not preserve
`varietyDim`. So the question is whether I can upgrade the existential to a regular section on a
pivot chart.

## The structures available

- `U_P ⊆ Mat^{=r}` = pivot chart where the top-left `r×r` minor `ΔP` is invertible (a principal open
  `D(ΔP)`; `Localization.Away ΔP`). The engine has the deep pivot minor `ΔPdeep` and
  `Localization.Away (ΔPdeep)` already (`DeepChartRing`).
- `H` acts, `mult` is `H`-equivariant (`mult_smul`), `F = mult⁻¹(E)`.
- `varietyDim` is set-level (`ringKrullDim` of `vanishingIdeal`), radical-insensitive (just landed).

## My questions

1. **On the pivot chart `D(ΔP)`, is there a REGULAR (polynomial-in-entries-after-inverting-ΔP)
   normalizing section `σ : U_P → H` with `σ(B)_N · E · σ(B)_0⁻¹ = B` for all `B ∈ U_P`?** For a
   rank-r matrix with invertible top-left r×r block, row/column reduction to `diag(I_r,0)` uses only
   the inverse of that block and its Schur complement — all REGULAR after inverting `ΔP`. So I expect
   YES, a regular section EXISTS on each pivot chart (this is the standard "Bruhat/pivot cell is an
   affine cell with a regular trivialization" fact). Confirm, and tell me the cleanest Lean-shape:
   build `σ` as an explicit `H`-valued regular map via the block inverse, OR is there a slicker route?

2. **Given a regular section `σ`, is the chart iso `Φ : mult⁻¹(U_P) ∩ Σ^r → U_P × F`, `A ↦ (mult A,
   σ(mult A)⁻¹ • A)` a regular iso?** Inverse `(B, A') ↦ σ(B) • A'`. Both directions are regular
   (compositions of `mult`, the regular `σ`, and the `H`-action which is regular). So this should be
   a genuine regular iso, hence `varietyDim`-preserving. Any subtlety (e.g. does `σ(mult A)⁻¹ • A ∈ F`
   need `mult A ∈ U_P` exactly, and is the codomain `U_P × F` or `U_P × (chart∩F)`)?

3. **Is "regular iso ⟹ equal `varietyDim`" cheap in Lean v4.29?** `varietyDim` is
   `ringKrullDim`-of-coordinate-ring; a regular iso of affine varieties induces a `k`-algebra iso of
   coordinate rings, and `ringKrullDim_eq_of_ringEquiv` transports. But the engine's `varietyDim` is
   defined on SUBSETS of a FIXED affine space `RepCoord d → k` via `vanishingIdeal` in THAT ambient
   ring — transporting `varietyDim` across a regular iso between subsets of DIFFERENT ambient spaces
   (`mult⁻¹(U)∩Σ^r ⊆ RepCoord d` vs `U_P × F ⊆ (base coords) × (RepCoord d)`) needs the coordinate-
   ring iso, not just the set iso. Is the cleanest path to (a) define `varietyDim` intrinsically via
   the coordinate-ring `ringKrullDim` and prove a `ringEquiv`-transport lemma, or (b) stay in one
   ambient space (realize `U_P × F` as a subset of `RepCoord d` too)? Which is less Lean friction?

4. **Could I AVOID the regular section entirely?** E.g. is there a cleaner route to `varietyDim Σ^r =
   δ + dim F` that does NOT build the explicit chart trivialization — e.g. (a) the action map `α : H
   × F → Σ^r` regular + surjective, `dim Σ^r = dim(H×F) − dim(generic α-fibre)`, with the generic
   α-fibre = the stabilizer (`dim H − δ`)? That reintroduces a fibre-dim count for `α` but over a
   GROUP (homogeneous, so the generic fibre dim might be computable as a stabilizer dim). Is that
   cheaper than the pivot-chart trivialization, or does it hit the same product-dimension wall?

Give me: confirm the regular section exists on a pivot chart (and the cleanest Lean construction),
the cleanest `varietyDim`-transport shape, and whether the chart route or the action-map route is
cheaper. Be concrete about the Lean friction in transporting set-level `varietyDim` across a regular
iso.

codex
I’ll inspect the local Lean/exposition scaffolding around `varietyDim`, pivot charts, and the landed rank/base-change lemmas so the advice matches the actual API rather than an abstract algebraic-geometry answer.
exec
/bin/bash -lc 'pwd && rg -n "def varietyDim|varietyDim|vanishingIdeal|ringKrullDim|exists_baseChange_of_rank_eq|DeepChartRing|ΔPdeep|mult_smul|baseChange|rank_eq" -S .' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
exec
/bin/bash -lc 'ls -la && find .. -maxdepth 2 -name CLAUDE.md -o -name README.md -o -name AGENTS.md' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
total 1508
drwxrwxr-x 2 ubuntu ubuntu    4096 Jun 24 17:54 .
drwxrwxr-x 3 ubuntu ubuntu    4096 Jun 24 17:51 ..
-rw-rw-r-- 1 ubuntu ubuntu  432309 Jun 24 17:45 noncirc-setlevel-answer.md
-rw-rw-r-- 1 ubuntu ubuntu    5060 Jun 24 17:42 noncirc-setlevel-prompt.md
-rw-rw-r-- 1 ubuntu ubuntu 1066445 Jun 24 17:35 route-choice-answer.md
-rw-rw-r-- 1 ubuntu ubuntu    6557 Jun 24 17:32 route-choice-prompt.md
-rw-rw-r-- 1 ubuntu ubuntu    5236 Jun 24 17:54 rung2-regular-section-answer.md
-rw-rw-r-- 1 ubuntu ubuntu    4417 Jun 24 17:54 rung2-regular-section-prompt.md

 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
./rung2-regular-section-prompt.md:3:Route (c), rung 2. Goal: a `varietyDim`-preserving (REGULAR, not bare-set) trivialization of one
./rung2-regular-section-prompt.md:4:pivot chart, `mult⁻¹(U_P) ∩ Σ^r ≅_reg U_P × F`, so that `varietyDim(chart) = varietyDim U_P +
./rung2-regular-section-prompt.md:5:varietyDim F = δ + varietyDim F`.
./rung2-regular-section-prompt.md:9:The LANDED `exists_baseChange_of_rank_eq` is EXISTENTIAL: for each rank-r target `B` it gives SOME
./rung2-regular-section-prompt.md:13:`varietyDim`. So the question is whether I can upgrade the existential to a regular section on a
./rung2-regular-section-prompt.md:19:  `D(ΔP)`; `Localization.Away ΔP`). The engine has the deep pivot minor `ΔPdeep` and
./rung2-regular-section-prompt.md:20:  `Localization.Away (ΔPdeep)` already (`DeepChartRing`).
./rung2-regular-section-prompt.md:21:- `H` acts, `mult` is `H`-equivariant (`mult_smul`), `F = mult⁻¹(E)`.
./rung2-regular-section-prompt.md:22:- `varietyDim` is set-level (`ringKrullDim` of `vanishingIdeal`), radical-insensitive (just landed).
./rung2-regular-section-prompt.md:37:   a genuine regular iso, hence `varietyDim`-preserving. Any subtlety (e.g. does `σ(mult A)⁻¹ • A ∈ F`
./rung2-regular-section-prompt.md:40:3. **Is "regular iso ⟹ equal `varietyDim`" cheap in Lean v4.29?** `varietyDim` is
./rung2-regular-section-prompt.md:41:   `ringKrullDim`-of-coordinate-ring; a regular iso of affine varieties induces a `k`-algebra iso of
./rung2-regular-section-prompt.md:42:   coordinate rings, and `ringKrullDim_eq_of_ringEquiv` transports. But the engine's `varietyDim` is
./rung2-regular-section-prompt.md:43:   defined on SUBSETS of a FIXED affine space `RepCoord d → k` via `vanishingIdeal` in THAT ambient
./rung2-regular-section-prompt.md:44:   ring — transporting `varietyDim` across a regular iso between subsets of DIFFERENT ambient spaces
./rung2-regular-section-prompt.md:46:   ring iso, not just the set iso. Is the cleanest path to (a) define `varietyDim` intrinsically via
./rung2-regular-section-prompt.md:47:   the coordinate-ring `ringKrullDim` and prove a `ringEquiv`-transport lemma, or (b) stay in one
./rung2-regular-section-prompt.md:50:4. **Could I AVOID the regular section entirely?** E.g. is there a cleaner route to `varietyDim Σ^r =
./rung2-regular-section-prompt.md:58:the cleanest `varietyDim`-transport shape, and whether the chart route or the action-map route is
./rung2-regular-section-prompt.md:59:cheaper. Be concrete about the Lean friction in transporting set-level `varietyDim` across a regular
./rung2-regular-section-answer.md:18:Route (c), rung 2. Goal: a `varietyDim`-preserving (REGULAR, not bare-set) trivialization of one
./rung2-regular-section-answer.md:19:pivot chart, `mult⁻¹(U_P) ∩ Σ^r ≅_reg U_P × F`, so that `varietyDim(chart) = varietyDim U_P +
./rung2-regular-section-answer.md:20:varietyDim F = δ + varietyDim F`.
./rung2-regular-section-answer.md:24:The LANDED `exists_baseChange_of_rank_eq` is EXISTENTIAL: for each rank-r target `B` it gives SOME
./rung2-regular-section-answer.md:28:`varietyDim`. So the question is whether I can upgrade the existential to a regular section on a
./rung2-regular-section-answer.md:34:  `D(ΔP)`; `Localization.Away ΔP`). The engine has the deep pivot minor `ΔPdeep` and
./rung2-regular-section-answer.md:35:  `Localization.Away (ΔPdeep)` already (`DeepChartRing`).
./rung2-regular-section-answer.md:36:- `H` acts, `mult` is `H`-equivariant (`mult_smul`), `F = mult⁻¹(E)`.
./rung2-regular-section-answer.md:37:- `varietyDim` is set-level (`ringKrullDim` of `vanishingIdeal`), radical-insensitive (just landed).
./rung2-regular-section-answer.md:52:   a genuine regular iso, hence `varietyDim`-preserving. Any subtlety (e.g. does `σ(mult A)⁻¹ • A ∈ F`
./rung2-regular-section-answer.md:55:3. **Is "regular iso ⟹ equal `varietyDim`" cheap in Lean v4.29?** `varietyDim` is
./rung2-regular-section-answer.md:56:   `ringKrullDim`-of-coordinate-ring; a regular iso of affine varieties induces a `k`-algebra iso of
./rung2-regular-section-answer.md:57:   coordinate rings, and `ringKrullDim_eq_of_ringEquiv` transports. But the engine's `varietyDim` is
./rung2-regular-section-answer.md:58:   defined on SUBSETS of a FIXED affine space `RepCoord d → k` via `vanishingIdeal` in THAT ambient
./rung2-regular-section-answer.md:59:   ring — transporting `varietyDim` across a regular iso between subsets of DIFFERENT ambient spaces
./rung2-regular-section-answer.md:61:   ring iso, not just the set iso. Is the cleanest path to (a) define `varietyDim` intrinsically via
./rung2-regular-section-answer.md:62:   the coordinate-ring `ringKrullDim` and prove a `ringEquiv`-transport lemma, or (b) stay in one
./rung2-regular-section-answer.md:65:4. **Could I AVOID the regular section entirely?** E.g. is there a cleaner route to `varietyDim Σ^r =
./rung2-regular-section-answer.md:73:the cleanest `varietyDim`-transport shape, and whether the chart route or the action-map route is
./rung2-regular-section-answer.md:74:cheaper. Be concrete about the Lean friction in transporting set-level `varietyDim` across a regular
./rung2-regular-section-answer.md:78:I’ll inspect the local Lean/exposition scaffolding around `varietyDim`, pivot charts, and the landed rank/base-change lemmas so the advice matches the actual API rather than an abstract algebraic-geometry answer.
./noncirc-setlevel-prompt.md:4:`hSweep : varietyDim Σ^r = δ + varietyDim F`. Rung 1 = a single-chart trivialization. The DECISIVE
./noncirc-setlevel-prompt.md:5:de-risk: is the SET-LEVEL / `varietyDim` version non-circular, given a PRIOR attempt (R2-3b-4) at a
./noncirc-setlevel-prompt.md:23:For `hSweep` I do NOT need reducedness. `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`
./noncirc-setlevel-prompt.md:24:and `vanishingIdeal Z` is ALREADY radical (it's a vanishing ideal). Krull dim is RADICAL-INSENSITIVE:
./noncirc-setlevel-prompt.md:25:`ringKrullDim (R⧸I) = ringKrullDim (R⧸√I)`. So `varietyDim` reads only the REDUCED/variety structure;
./noncirc-setlevel-prompt.md:36:1. **Is `varietyDim` genuinely radical-insensitive in Mathlib v4.29** — i.e. is `ringKrullDim (R⧸I) =
./noncirc-setlevel-prompt.md:37:   ringKrullDim (R⧸ I.radical)` available (or `ringKrullDim` factors through `√`)? Name the lemma if
./noncirc-setlevel-prompt.md:43:   chart's normalizing gauge. This is a bijection of SETS / a `varietyDim`-preserving map. Does
./noncirc-setlevel-prompt.md:48:   `varietyDim(U×F) = varietyDim U + varietyDim F` secretly needs flatness/reducedness.
./noncirc-setlevel-prompt.md:50:3. **The product-dimension step `varietyDim(U × F) = varietyDim U + varietyDim F`.** For a product of
./noncirc-setlevel-prompt.md:52:   (as `ringKrullDim (A ⊗_k B) = ringKrullDim A + ringKrullDim B`, or a variety-dimension product)?
./noncirc-setlevel-prompt.md:58:4. **The glue over the finite pivot cover.** `varietyDim(⋃_i Z_i) = max_i varietyDim(Z_i)` for a
./noncirc-setlevel-prompt.md:59:   finite cover — is that radical-insensitive and in Mathlib (or trivial from `ringKrullDim` of a
./noncirc-setlevel-prompt.md:62:5. **Net verdict:** does the SET-LEVEL/`varietyDim` route (c) dodge the R2-3b-4 circularity? If YES,
./noncirc-setlevel-prompt.md:67:The key thing I need from you: a clean YES/NO on whether radical-insensitivity of `varietyDim` lets
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
./route-choice-answer.md:453:./CLAUDE.md:81:  set-level route `vanishingIdeal (shifted) = comap (algEquiv) (vanishingIdeal)` + `height_comap` is
./route-choice-answer.md:466:./DLNFibre/Core/OrbitPullbackDim.lean:6:# `DLNFibre.Core.OrbitPullbackDim` — route-c setup: `varietyDim(Z_M) = ringKrullDim((μ_M^*).range)`
./route-choice-answer.md:467:./DLNFibre/Core/OrbitPullbackDim.lean:16:1. **Ideal identification.** `varietyDim Z_M = ringKrullDim (MvPolynomial (RepCoord d) k ⧸
./route-choice-answer.md:468:./DLNFibre/Core/OrbitPullbackDim.lean:17:   ker μ_M^*)`, immediate from the `varietyDim` definition, the Abeasis–Del Fra ideal equality L6.4
./route-choice-answer.md:469:./DLNFibre/Core/OrbitPullbackDim.lean:18:   (`vanishingIdeal_orbitRankLocus_eq_orbitSet`), and the orbit↔kernel identity
./route-choice-answer.md:470:./DLNFibre/Core/OrbitPullbackDim.lean:19:   (`range_orbitMap` + `vanishingIdeal_range_orbitMap_eq_ker`).
./route-choice-answer.md:471:./DLNFibre/Core/OrbitPullbackDim.lean:25:The headline `varietyDim_eq_ringKrullDim_range_orbitPullback` hands A4 a finitely-generated domain
./route-choice-answer.md:472:./DLNFibre/Core/OrbitPullbackDim.lean:48:`MvPolynomial (RepCoord d) k ⧸ ker μ_M^*`. `varietyDim` definition, then L6.4
./route-choice-answer.md:473:./DLNFibre/Core/OrbitPullbackDim.lean:49:(`vanishingIdeal_orbitRankLocus_eq_orbitSet`) and the orbit↔kernel identity
./route-choice-answer.md:474:./DLNFibre/Core/OrbitPullbackDim.lean:50:(`range_orbitMap` + `vanishingIdeal_range_orbitMap_eq_ker`) rewrite the vanishing ideal to
./route-choice-answer.md:475:./DLNFibre/Core/OrbitPullbackDim.lean:52:theorem varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker [Infinite k]
./route-choice-answer.md:476:./DLNFibre/Core/OrbitPullbackDim.lean:54:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./route-choice-answer.md:477:./DLNFibre/Core/OrbitPullbackDim.lean:57:  rw [varietyDim, vanishingIdeal_orbitRankLocus_eq_orbitSet M, ← range_orbitMap,
./route-choice-answer.md:478:./DLNFibre/Core/OrbitPullbackDim.lean:58:    vanishingIdeal_range_orbitMap_eq_ker M]
./route-choice-answer.md:479:./DLNFibre/Core/OrbitPullbackDim.lean:70:transcendence degree. Combines `varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker` with the
./route-choice-answer.md:480:./DLNFibre/Core/OrbitPullbackDim.lean:74:theorem varietyDim_eq_ringKrullDim_range_orbitPullback [Infinite k] {d : Fin (N + 1) → ℕ}
./route-choice-answer.md:481:./DLNFibre/Core/OrbitPullbackDim.lean:76:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./route-choice-answer.md:482:./DLNFibre/Core/OrbitPullbackDim.lean:78:  rw [varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker M,
./route-choice-answer.md:483:./DLNFibre/Core/OrbitPullbackDim.lean:89:/-- The headline at the concrete `(2,2,2)/ℚ` tuple: `varietyDim (canonicalCoord '' orbitRankLocus
./route-choice-answer.md:484:./DLNFibre/Core/OrbitPullbackDim.lean:93:    varietyDim (canonicalCoord dWitness '' orbitRankLocus tupleWitnessQ)
./route-choice-answer.md:485:./DLNFibre/Core/OrbitPullbackDim.lean:95:  varietyDim_eq_ringKrullDim_range_orbitPullback tupleWitnessQ
./route-choice-answer.md:491:./DLNFibre/DLN/RlctPayoff.lean:132:  -- RHS: ⨅ over corner-0 tuples M, of `codimRepCanonical (Ō_M) = (vanishingIdeal Ō_M).height`.
./route-choice-answer.md:492:./DLNFibre/DLN/RlctPayoff.lean:136:    have hmem : (MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
./route-choice-answer.md:493:./DLNFibre/DLN/RlctPayoff.lean:139:        ≤ MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
./route-choice-answer.md:494:./DLNFibre/DLN/RlctPayoff.lean:142:    haveI : (MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
./route-choice-answer.md:495:./DLNFibre/DLN/RlctPayoff.lean:144:      isPrime_vanishingIdeal_orbitRankLocus M
./route-choice-answer.md:496:./DLNFibre/DLN/RlctPayoff.lean:197:    exact Ideal.height_ne_top (isPrime_vanishingIdeal_orbitRankLocus M).ne_top
./route-choice-answer.md:497:./DLNFibre/DLN/RlctPayoff.lean:226:          (isPrime_vanishingIdeal_orbitRankLocus (realizerD (k := k) hm₀)).ne_top
./route-choice-answer.md:498:./DLNFibre/Core/CCodimCornerMono.lean:329:    exact Ideal.height_ne_top (isPrime_vanishingIdeal_orbitRankLocus _).ne_top
./route-choice-answer.md:499:./DLNFibre/Core/CCodimCornerMono.lean:374:partition. From G3 (`minimalPrimes_sigmaIdeal_eq`) `p = vanishingIdeal (Ō_{M'})` for a corner-`≤ r`
./route-choice-answer.md:500:./DLNFibre/Core/CCodimCornerMono.lean:385:  -- G3: `p` is a corner-`≤ r` orbit ideal `vanishingIdeal (Ō_{M'})`
./route-choice-answer.md:503:./DLNFibre/Core/DeterminantalStratumDim.lean:24:   `isPrime_vanishingIdeal_orbitRankLocus`).
./route-choice-answer.md:506:./DLNFibre/Core/DeterminantalStratumDim.lean:29:4. **The catenary bridge** (LANDED `codimRep_add_varietyDim_eq_card`): `codim + dim = card = m·n`,
./route-choice-answer.md:512:./DLNFibre/Core/DeterminantalStratumDim.lean:196:flattening of) `productRankLocusLE ![n,m] r` is prime — it is `vanishingIdeal (Ō_{M₀})` of a single
./route-choice-answer.md:513:./DLNFibre/Core/DeterminantalStratumDim.lean:197:orbit closure (LANDED `isPrime_vanishingIdeal_orbitRankLocus`). -/
./route-choice-answer.md:514:./DLNFibre/Core/DeterminantalStratumDim.lean:198:theorem isPrime_vanishingIdeal_productRankLocusLE_stratum [IsAlgClosed k] (n m r : ℕ)
./route-choice-answer.md:515:./DLNFibre/Core/DeterminantalStratumDim.lean:200:    (vanishingIdeal k
./route-choice-answer.md:518:./DLNFibre/Core/DeterminantalStratumDim.lean:205:  exact isPrime_vanishingIdeal_orbitRankLocus M₀
./route-choice-answer.md:520:./DLNFibre/Core/DeterminantalStratumDim.lean:224:> `varietyDim (Mat^{rk ≤ r}_{m × n}) = r · (n + m − r)`.
./route-choice-answer.md:521:./DLNFibre/Core/DeterminantalStratumDim.lean:229:theorem varietyDim_productRankLocusLE_stratum [IsAlgClosed k] [CharZero k] (n m r : ℕ)
./route-choice-answer.md:522:./DLNFibre/Core/DeterminantalStratumDim.lean:231:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./route-choice-answer.md:524:./DLNFibre/Core/DeterminantalStratumDim.lean:237:  have hbridge := codimRep_add_varietyDim_eq_card (canonicalCoord (dStratum n m)) Z
./route-choice-answer.md:525:./DLNFibre/Core/DeterminantalStratumDim.lean:238:    (isPrime_vanishingIdeal_productRankLocusLE_stratum (k := k) n m r hn hm)
./route-choice-answer.md:527:./DLNFibre/Core/DeterminantalStratumDim.lean:249:  -- `hbridge : (n−r)(m−r) + varietyDim Z = m·n`
./route-choice-answer.md:528:./DLNFibre/Core/DeterminantalStratumDim.lean:258:  have heq : (((n - r) * (m - r) : ℕ) : ℕ∞) + varietyDim (canonicalCoord (dStratum n m) '' Z)
./route-choice-answer.md:529:./DLNFibre/Core/DeterminantalStratumDim.lean:268:    varietyDim (canonicalCoord (dStratum 2 2) '' productRankLocusLE (k := k) (dStratum 2 2) 1)
./route-choice-answer.md:530:./DLNFibre/Core/DeterminantalStratumDim.lean:270:  have h := varietyDim_productRankLocusLE_stratum (k := k) 2 2 1 (by norm_num) (by norm_num)
./route-choice-answer.md:531:./DLNFibre/Core/RankLocusClosed.lean:263:fact `zeroLocus (vanishingIdeal (zeroLocus I)) = zeroLocus I`). This is the topological content of
./route-choice-answer.md:532:./DLNFibre/Core/RankLocusClosed.lean:268:  exact (MvPolynomial.zeroLocus_vanishingIdeal_galoisConnection
./route-choice-answer.md:533:./DLNFibre/Core/RankLocusClosed.lean:289:/-- **The easy ideal inclusion.** `vanishingIdeal (canonicalCoord '' orbitRankLocus M) ≤
./route-choice-answer.md:534:./DLNFibre/Core/RankLocusClosed.lean:290:vanishingIdeal (O_M)`: at the ideal level the easy orbit inclusion `O_M ⊆ orbitRankLocus M` is the
./route-choice-answer.md:535:./DLNFibre/Core/RankLocusClosed.lean:291:*trivial* containment of vanishing ideals (`vanishingIdeal` is order-reversing). The genuine content
./route-choice-answer.md:536:./DLNFibre/Core/RankLocusClosed.lean:293:theorem vanishingIdeal_orbitRankLocus_le_orbitSet {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
./route-choice-answer.md:537:./DLNFibre/Core/RankLocusClosed.lean:294:    MvPolynomial.vanishingIdeal k (canonicalCoord d '' orbitRankLocus M)
./route-choice-answer.md:538:./DLNFibre/Core/RankLocusClosed.lean:295:      ≤ MvPolynomial.vanishingIdeal k (orbitSet M) :=
./route-choice-answer.md:539:./DLNFibre/Core/RankLocusClosed.lean:296:  MvPolynomial.vanishingIdeal_anti_mono (orbitSet_subset_orbitRankLocus M)
./route-choice-answer.md:544:./DLNFibre/Core/DeepChartRing.lean:48:endpoint-normalization `AlgEquiv`, and the descent of the iso to the reduced chart quotient are
./route-choice-answer.md:545:./DLNFibre/Core/DeepChartRing.lean:52:endpoint-normalization `aeval`-substitution contract is pre-staged below as an `example` block (an
./route-choice-answer.md:546:./DLNFibre/Core/DeepChartRing.lean:133:`sigmaIdeal` is radical (`vanishingIdeal_isRadical`, over `[IsAlgClosed k]`) and localization
./route-choice-answer.md:547:./DLNFibre/Core/DeepChartRing.lean:141:(`vanishingIdeal_isRadical`). -/
./route-choice-answer.md:548:./DLNFibre/Core/DeepChartRing.lean:146:    rw [sigmaIdeal]; exact vanishingIdeal_isRadical _
./route-choice-answer.md:549:./DLNFibre/Core/DeepChartRing.lean:236:  rw [Ideal.mem_comap, sigmaIdeal, mem_vanishingIdeal_iff]
./route-choice-answer.md:550:./DLNFibre/Core/DeepChartRing.lean:239:  rw [mem_productRankLocusLE] at hA
./route-choice-answer.md:551:./DLNFibre/Core/DeepChartRing.lean:242:  rw [sigmaIdeal, mem_vanishingIdeal_iff] at hf
./route-choice-answer.md:552:./DLNFibre/Core/DeepChartRing.lean:244:    rw [mem_productRankLocusLE, mult_singleTuple]; exact hA, rfl⟩
./route-choice-answer.md:553:./DLNFibre/Core/DeepChartRing.lean:355:The endpoint-normalization `AlgEquiv` for R2-3b-3 is an `aeval`-substitution on the **unquotiented**
./route-choice-answer.md:554:./DLNFibre/Core/DeepChartRing.lean:366:`aeval_X`). The endpoint-normalization substitution of R2-3b-3 instantiates this. -/
./route-choice-answer.md:558:./DLNFibre/Core/FibreCodim.lean:32:`canonicalCoord '' (mult⁻¹ B) ⊆ canonicalCoord '' Σ̄^r`; `vanishingIdeal` is order-reversing and
./route-choice-answer.md:559:./DLNFibre/Core/FibreCodim.lean:50:least that of any superset: a larger set has a smaller vanishing ideal (`vanishingIdeal_anti_mono`),
./route-choice-answer.md:560:./DLNFibre/Core/FibreCodim.lean:56:  exact MvPolynomial.vanishingIdeal_anti_mono (Set.image_mono h)
./route-choice-answer.md:572:./DLNFibre/Core/EndpointNormalization.lean:141:by `C`); the interior units telescope away (`mult_smul`). For the endpoint normalization
./route-choice-answer.md:573:./DLNFibre/Core/EndpointNormalization.lean:218:`baseChange_one`) on the generic tuple. The endpoint normalization instantiates `P`. -/
./route-choice-answer.md:576:./DLNFibre/Core/FibreDimFibration.lean:43:(dStratum n m)) k ⧸ vanishingIdeal(…)` is a finite-type domain (the vanishing ideal is prime —
./route-choice-answer.md:577:./DLNFibre/Core/FibreDimFibration.lean:45:`varietyDim = δ`, lifting the `unbotD 0` to the genuine `WithBot ℕ∞` value (the quotient is
./route-choice-answer.md:578:./DLNFibre/Core/FibreDimFibration.lean:51:The thermometer `varietyDim_productRankLocusLE_stratum` gives the `ℕ∞`-via-`unbotD` value; this lifts
./route-choice-answer.md:579:./DLNFibre/Core/FibreDimFibration.lean:54:theorem ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta [IsAlgClosed k] [CharZero k]
./route-choice-answer.md:580:./DLNFibre/Core/FibreDimFibration.lean:57:        MvPolynomial.vanishingIdeal (σ := RepCoord (dStratum n m)) (K := k) k
./route-choice-answer.md:582:./DLNFibre/Core/FibreDimFibration.lean:60:  set I := MvPolynomial.vanishingIdeal (σ := RepCoord (dStratum n m)) (K := k) k
./route-choice-answer.md:584:./DLNFibre/Core/FibreDimFibration.lean:63:    isPrime_vanishingIdeal_productRankLocusLE_stratum (k := k) n m r hn hm
./route-choice-answer.md:585:./DLNFibre/Core/FibreDimFibration.lean:64:  -- the thermometer: `varietyDim = δ`, i.e. `(ringKrullDim (R ⧸ I)).unbotD 0 = δ`.
./route-choice-answer.md:586:./DLNFibre/Core/FibreDimFibration.lean:65:  have hvd : varietyDim (canonicalCoord (dStratum n m) ''
./route-choice-answer.md:588:./DLNFibre/Core/FibreDimFibration.lean:67:    varietyDim_productRankLocusLE_stratum n m r hn hm
./route-choice-answer.md:589:./DLNFibre/Core/FibreDimFibration.lean:68:  rw [varietyDim, ← hI] at hvd
./route-choice-answer.md:590:./DLNFibre/Core/FibreDimFibration.lean:89:vanishingIdeal(…)` has height `δ = r(n + m − r)` — equidimensionality at a closed point of the
./route-choice-answer.md:591:./DLNFibre/Core/FibreDimFibration.lean:91:theorem height_maximal_quotient_vanishingIdeal_stratum_eq_delta [IsAlgClosed k] [CharZero k]
./route-choice-answer.md:592:./DLNFibre/Core/FibreDimFibration.lean:94:        MvPolynomial.vanishingIdeal (σ := RepCoord (dStratum n m)) (K := k) k
./route-choice-answer.md:594:./DLNFibre/Core/FibreDimFibration.lean:98:  haveI : (MvPolynomial.vanishingIdeal (σ := RepCoord (dStratum n m)) (K := k) k
./route-choice-answer.md:596:./DLNFibre/Core/FibreDimFibration.lean:100:    isPrime_vanishingIdeal_productRankLocusLE_stratum (k := k) n m r hn hm
./route-choice-answer.md:597:./DLNFibre/Core/FibreDimFibration.lean:102:    ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta n m r hn hm]
./route-choice-answer.md:598:./DLNFibre/Core/OrbitCodim.lean:19:   engine** (zero-cited): the ideal-level identity `Core.OrbitClosure.vanishingIdeal_orbitRankLocus_eq_orbitSet`
./route-choice-answer.md:599:./DLNFibre/Core/OrbitCodim.lean:23:   vanishing ideal** in the coordinate polynomial ring (`Ideal.height ∘ vanishingIdeal`, the
./route-choice-answer.md:600:./DLNFibre/Core/OrbitCodim.lean:39:**`codimRep` faithfulness.** `codimRep coord Z := (vanishingIdeal k (coord '' Z)).height`: the
./route-choice-answer.md:601:./DLNFibre/Core/OrbitCodim.lean:55:coordinate change on `MvPolynomial`, (ii) `vanishingIdeal (φ ∘ coord '' Z) = comap φ (vanishingIdeal
./route-choice-answer.md:602:./DLNFibre/Core/OrbitCodim.lean:79:`Core.OrbitClosure.vanishingIdeal_orbitRankLocus_eq_orbitSet` and set-level
./route-choice-answer.md:603:./DLNFibre/Core/OrbitCodim.lean:129:    (MvPolynomial.vanishingIdeal (σ := RepCoord d) (k := k) (K := k) (coord '' Z))
./route-choice-answer.md:605:./DLNFibre/Core/EndBaseChangeSweep.lean:16:consequence** `varietyDim (productRankLocus d r) = δ + varietyDim (fibre d E)` is the *one genuinely
./route-choice-answer.md:617:./DLNFibre/Core/OrbitVariety.lean:15:the polynomial orbit map, so `vanishingIdeal O_M = ker μ_M^*` is a kernel into a domain. The
./route-choice-answer.md:618:./DLNFibre/Core/OrbitVariety.lean:316:`μ_M^* g` is zero in the domain `𝒪(G_d)`: `vanishingIdeal (range μ_M) = ker μ_M^*`. The `⊇` is
./route-choice-answer.md:619:./DLNFibre/Core/OrbitVariety.lean:320:theorem vanishingIdeal_range_orbitMap_eq_ker [Infinite k] {d : Fin (N + 1) → ℕ}
./route-choice-answer.md:620:./DLNFibre/Core/OrbitVariety.lean:322:    MvPolynomial.vanishingIdeal k (Set.range (orbitMap M))
./route-choice-answer.md:621:./DLNFibre/Core/OrbitVariety.lean:325:  rw [MvPolynomial.mem_vanishingIdeal_iff, RingHom.mem_ker]
./route-choice-answer.md:622:./DLNFibre/Core/OrbitVariety.lean:369:orbit map `μ_M`, so `vanishingIdeal O_M = ker μ_M^*` (`vanishingIdeal_range_orbitMap_eq_ker`) is a
./route-choice-answer.md:623:./DLNFibre/Core/OrbitVariety.lean:372:theorem isPrime_vanishingIdeal_orbitSet [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./route-choice-answer.md:624:./DLNFibre/Core/OrbitVariety.lean:374:    (MvPolynomial.vanishingIdeal k (orbitSet M) :
./route-choice-answer.md:625:./DLNFibre/Core/OrbitVariety.lean:376:  rw [← range_orbitMap, vanishingIdeal_range_orbitMap_eq_ker]
./route-choice-answer.md:626:./DLNFibre/Core/OrbitVariety.lean:385:  (isZariskiIrreducible_iff_isPrime_vanishingIdeal (orbitSet M)).mpr
./route-choice-answer.md:627:./DLNFibre/Core/OrbitVariety.lean:386:    (isPrime_vanishingIdeal_orbitSet M)
./route-choice-answer.md:628:./DLNFibre/Core/FlatTrivialProductProbe.lean:19:function on `Tuple d`, with codim read through `vanishingIdeal`/`Ideal.height`; no `Spec`, no
./route-choice-answer.md:631:./DLNFibre/Core/DeterminantalBasePresentation.lean:341:    rw [sigmaIdeal]; exact isPrime_vanishingIdeal_productRankLocusLE_stratum q p r hq hp
./route-choice-answer.md:637:./DLNFibre/Core/FibreHeightDirect.lean:11:`fibreGenIdeal d B` (`Core.MultComorphism.vanishingIdeal_image_fibre_eq_radical`). The point of this
./route-choice-answer.md:638:./DLNFibre/Core/FibreHeightDirect.lean:46:`codimRepCanonical (fibre d B) = height (vanishingIdeal (canonicalCoord d '' fibre d B))`
./route-choice-answer.md:639:./DLNFibre/Core/FibreHeightDirect.lean:47:(definition of `codimRepCanonical`/`codimRep`); `vanishingIdeal (…) = (fibreGenIdeal d B).radical`
./route-choice-answer.md:640:./DLNFibre/Core/FibreHeightDirect.lean:48:(`vanishingIdeal_image_fibre_eq_radical`, the Nullstellensatz); `(radical I).height = I.height`
./route-choice-answer.md:641:./DLNFibre/Core/FibreHeightDirect.lean:54:  rw [codimRepCanonical, codimRep, vanishingIdeal_image_fibre_eq_radical, Ideal.height_radical]
./route-choice-answer.md:642:./DLNFibre/Core/NullstellensatzCodim.lean:19:1. **Nullstellensatz pieces** (Mathlib's `MvPolynomial.vanishingIdeal`/`zeroLocus`, strong
./route-choice-answer.md:643:./DLNFibre/Core/NullstellensatzCodim.lean:20:   Nullstellensatz over `[IsAlgClosed k]`): `vanishingIdeal Z` is always **radical**
./route-choice-answer.md:644:./DLNFibre/Core/NullstellensatzCodim.lean:21:   (`vanishingIdeal_isRadical`); `Z` irreducible ⟺ `vanishingIdeal Z` is **prime**
./route-choice-answer.md:645:./DLNFibre/Core/NullstellensatzCodim.lean:22:   (`isZariskiIrreducible_iff_isPrime_vanishingIdeal`, through the `pointToPoint` image and
./route-choice-answer.md:646:./DLNFibre/Core/NullstellensatzCodim.lean:23:   `PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime`); a closed `Z` with prime vanishing
./route-choice-answer.md:647:./DLNFibre/Core/NullstellensatzCodim.lean:24:   ideal is **nonempty** (`nonempty_of_isZariskiClosed_of_isPrime_vanishingIdeal`, weak
./route-choice-answer.md:648:./DLNFibre/Core/NullstellensatzCodim.lean:30:3. **The bridge headline.** For `(vanishingIdeal Z).IsPrime` (the algebraic content of "`Z`
./route-choice-answer.md:649:./DLNFibre/Core/NullstellensatzCodim.lean:31:   irreducible"), `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ` (`ℕ∞`, additive — `ℕ∞`
./route-choice-answer.md:650:./DLNFibre/Core/NullstellensatzCodim.lean:37:`axiom`. `varietyDim Z = ringKrullDim (R ⧸ vanishingIdeal Z)` is the Krull dimension of the
./route-choice-answer.md:651:./DLNFibre/Core/NullstellensatzCodim.lean:57:  Z = zeroLocus k (vanishingIdeal k Z)
./route-choice-answer.md:652:./DLNFibre/Core/NullstellensatzCodim.lean:67:strong Nullstellensatz it equals its own radical, via `vanishingIdeal Z = vanishingIdeal (zeroLocus
./route-choice-answer.md:653:./DLNFibre/Core/NullstellensatzCodim.lean:68:(vanishingIdeal Z))` `= (vanishingIdeal Z).radical`. -/
./route-choice-answer.md:654:./DLNFibre/Core/NullstellensatzCodim.lean:69:theorem vanishingIdeal_isRadical [IsAlgClosed k] [Finite σ] (Z : Set (σ → k)) :
./route-choice-answer.md:655:./DLNFibre/Core/NullstellensatzCodim.lean:70:    (vanishingIdeal k Z : Ideal (MvPolynomial σ k)).IsRadical := by
./route-choice-answer.md:656:./DLNFibre/Core/NullstellensatzCodim.lean:71:  have h : vanishingIdeal k Z = (vanishingIdeal k Z).radical := by
./route-choice-answer.md:657:./DLNFibre/Core/NullstellensatzCodim.lean:73:      rw [← (zeroLocus_vanishingIdeal_galoisConnection (σ := σ) (k := k) (K := k)).u_l_u_eq_u Z,
./route-choice-answer.md:658:./DLNFibre/Core/NullstellensatzCodim.lean:74:        vanishingIdeal_zeroLocus_eq_radical (K := k)]
./route-choice-answer.md:659:./DLNFibre/Core/NullstellensatzCodim.lean:79:`PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime`. -/
./route-choice-answer.md:660:./DLNFibre/Core/NullstellensatzCodim.lean:80:theorem isZariskiIrreducible_iff_isPrime_vanishingIdeal (Z : Set (σ → k)) :
./route-choice-answer.md:661:./DLNFibre/Core/NullstellensatzCodim.lean:81:    IsZariskiIrreducible Z ↔ (vanishingIdeal k Z : Ideal (MvPolynomial σ k)).IsPrime := by
./route-choice-answer.md:662:./DLNFibre/Core/NullstellensatzCodim.lean:83:  rw [PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime, vanishingIdeal_pointToPoint]
./route-choice-answer.md:663:./DLNFibre/Core/NullstellensatzCodim.lean:86:is prime (hence proper) is nonempty: if `Z = ∅` then `vanishingIdeal Z = ⊤`, but the strong
./route-choice-answer.md:664:./DLNFibre/Core/NullstellensatzCodim.lean:87:Nullstellensatz forces `vanishingIdeal (zeroLocus (vanishingIdeal Z)) = (vanishingIdeal Z).radical`,
./route-choice-answer.md:665:./DLNFibre/Core/NullstellensatzCodim.lean:89:theorem nonempty_of_isZariskiClosed_of_isPrime_vanishingIdeal [IsAlgClosed k] [Finite σ]
./route-choice-answer.md:666:./DLNFibre/Core/NullstellensatzCodim.lean:91:    (hp : (vanishingIdeal k Z : Ideal (MvPolynomial σ k)).IsPrime) :
./route-choice-answer.md:667:./DLNFibre/Core/NullstellensatzCodim.lean:95:  have htop : vanishingIdeal k Z = ⊤ := by
./route-choice-answer.md:668:./DLNFibre/Core/NullstellensatzCodim.lean:96:    have h2 : zeroLocus k (vanishingIdeal k Z) = (∅ : Set (σ → k)) := hZ ▸ hempty
./route-choice-answer.md:669:./DLNFibre/Core/NullstellensatzCodim.lean:97:    have h3 : vanishingIdeal k (zeroLocus k (vanishingIdeal k Z)) = (vanishingIdeal k Z).radical :=
./route-choice-answer.md:670:./DLNFibre/Core/NullstellensatzCodim.lean:98:      vanishingIdeal_zeroLocus_eq_radical (K := k) _
./route-choice-answer.md:671:./DLNFibre/Core/NullstellensatzCodim.lean:99:    rw [h2, vanishingIdeal_empty] at h3
./route-choice-answer.md:672:./DLNFibre/Core/NullstellensatzCodim.lean:136:`MvPolynomial σ k ⧸ vanishingIdeal Z` of `Z`'s Zariski closure, as an `ℕ∞` (the `⊥` from a trivial
./route-choice-answer.md:673:./DLNFibre/Core/NullstellensatzCodim.lean:137:quotient — absent here, since the relevant `vanishingIdeal Z` is prime — defaulting to `0`). It is
./route-choice-answer.md:674:./DLNFibre/Core/NullstellensatzCodim.lean:139:noncomputable def varietyDim (Z : Set (σ → k)) : ℕ∞ :=
./route-choice-answer.md:675:./DLNFibre/Core/NullstellensatzCodim.lean:140:  (ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal k Z)).unbotD 0
./route-choice-answer.md:676:./DLNFibre/Core/NullstellensatzCodim.lean:143:`(vanishingIdeal Z).IsPrime` — the height of its vanishing ideal plus its variety dimension equals
./route-choice-answer.md:677:./DLNFibre/Core/NullstellensatzCodim.lean:144:the ambient dimension `Nat.card σ`: `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ`. The
./route-choice-answer.md:678:./DLNFibre/Core/NullstellensatzCodim.lean:145:catenary identity over `σ`, read at the prime `vanishingIdeal Z`. Geometric codimension `=` ambient
./route-choice-answer.md:679:./DLNFibre/Core/NullstellensatzCodim.lean:147:theorem height_vanishingIdeal_add_varietyDim_eq_card [Finite σ] {Z : Set (σ → k)}
./route-choice-answer.md:680:./DLNFibre/Core/NullstellensatzCodim.lean:148:    (hp : (vanishingIdeal k Z : Ideal (MvPolynomial σ k)).IsPrime) :
./route-choice-answer.md:681:./DLNFibre/Core/NullstellensatzCodim.lean:149:    (vanishingIdeal k Z).height + varietyDim Z = (Nat.card σ : ℕ∞) := by
./route-choice-answer.md:682:./DLNFibre/Core/NullstellensatzCodim.lean:150:  have key := height_add_ringKrullDim_quotient_eq_card (vanishingIdeal k Z)
./route-choice-answer.md:683:./DLNFibre/Core/NullstellensatzCodim.lean:151:  haveI : Nontrivial (MvPolynomial σ k ⧸ vanishingIdeal k Z) :=
./route-choice-answer.md:684:./DLNFibre/Core/NullstellensatzCodim.lean:153:  have hne : ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal k Z) ≠ ⊥ :=
./route-choice-answer.md:685:./DLNFibre/Core/NullstellensatzCodim.lean:155:      ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial σ k ⧸ vanishingIdeal k Z)
./route-choice-answer.md:686:./DLNFibre/Core/NullstellensatzCodim.lean:157:  rw [varietyDim, ← hm, WithBot.unbotD_coe]
./route-choice-answer.md:687:./DLNFibre/Core/NullstellensatzCodim.lean:162:`height (vanishingIdeal Z) = Nat.card σ − varietyDim Z` for an irreducible variety `Z` (`ℕ∞`
./route-choice-answer.md:688:./DLNFibre/Core/NullstellensatzCodim.lean:163:subtraction; lossless here since `varietyDim Z ≤ Nat.card σ`). The geometric codimension is the
./route-choice-answer.md:689:./DLNFibre/Core/NullstellensatzCodim.lean:165:theorem height_vanishingIdeal_eq_card_sub_varietyDim [Finite σ] {Z : Set (σ → k)}
./route-choice-answer.md:690:./DLNFibre/Core/NullstellensatzCodim.lean:166:    (hp : (vanishingIdeal k Z : Ideal (MvPolynomial σ k)).IsPrime) :
./route-choice-answer.md:691:./DLNFibre/Core/NullstellensatzCodim.lean:167:    (vanishingIdeal k Z).height = (Nat.card σ : ℕ∞) - varietyDim Z := by
./route-choice-answer.md:692:./DLNFibre/Core/NullstellensatzCodim.lean:168:  have hadd := height_vanishingIdeal_add_varietyDim_eq_card hp
./route-choice-answer.md:693:./DLNFibre/Core/NullstellensatzCodim.lean:169:  have hne : varietyDim Z ≠ ⊤ := by
./route-choice-answer.md:694:./DLNFibre/Core/NullstellensatzCodim.lean:182:`height_vanishingIdeal_add_varietyDim_eq_card` at `σ := RepCoord d`, `Z := coord '' Z`. -/
./route-choice-answer.md:695:./DLNFibre/Core/NullstellensatzCodim.lean:183:theorem codimRep_add_varietyDim_eq_card [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./route-choice-answer.md:696:./DLNFibre/Core/NullstellensatzCodim.lean:185:    (hp : (vanishingIdeal k (coord '' Z) : Ideal (MvPolynomial (RepCoord d) k)).IsPrime) :
./route-choice-answer.md:697:./DLNFibre/Core/NullstellensatzCodim.lean:186:    codimRep coord Z + varietyDim (coord '' Z) = (Nat.card (RepCoord d) : ℕ∞) :=
./route-choice-answer.md:698:./DLNFibre/Core/NullstellensatzCodim.lean:187:  height_vanishingIdeal_add_varietyDim_eq_card hp
./route-choice-answer.md:699:./DLNFibre/Core/NullstellensatzCodim.lean:190:varietyDim (coord '' Z)` for an irreducible variety `coord '' Z`: geometric codimension `=` ambient
./route-choice-answer.md:700:./DLNFibre/Core/NullstellensatzCodim.lean:192:theorem codimRep_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./route-choice-answer.md:701:./DLNFibre/Core/NullstellensatzCodim.lean:194:    (hp : (vanishingIdeal k (coord '' Z) : Ideal (MvPolynomial (RepCoord d) k)).IsPrime) :
./route-choice-answer.md:702:./DLNFibre/Core/NullstellensatzCodim.lean:195:    codimRep coord Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (coord '' Z) :=
./route-choice-answer.md:703:./DLNFibre/Core/NullstellensatzCodim.lean:196:  height_vanishingIdeal_eq_card_sub_varietyDim hp
./route-choice-answer.md:704:./DLNFibre/Core/NullstellensatzCodim.lean:199:`canonicalCoord d`, `codimRepCanonical Z = Nat.card (RepCoord d) − varietyDim (canonicalCoord d ''
./route-choice-answer.md:705:./DLNFibre/Core/NullstellensatzCodim.lean:201:theorem codimRepCanonical_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./route-choice-answer.md:706:./DLNFibre/Core/NullstellensatzCodim.lean:203:    (hp : (vanishingIdeal k (canonicalCoord d '' Z) :
./route-choice-answer.md:707:./DLNFibre/Core/NullstellensatzCodim.lean:205:    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
./route-choice-answer.md:708:./DLNFibre/Core/NullstellensatzCodim.lean:206:  codimRep_eq_card_sub_varietyDim (canonicalCoord d) Z hp
./route-choice-answer.md:709:./DLNFibre/Core/NullstellensatzCodim.lean:213:theorem vanishingIdeal_univ_eq_bot [IsAlgClosed k] :
./route-choice-answer.md:710:./DLNFibre/Core/NullstellensatzCodim.lean:214:    (vanishingIdeal k (Set.univ : Set (σ → k)) : Ideal (MvPolynomial σ k)) = ⊥ := by
./route-choice-answer.md:711:./DLNFibre/Core/NullstellensatzCodim.lean:220:  rw [MvPolynomial.mem_vanishingIdeal_iff] at hp
./route-choice-answer.md:712:./DLNFibre/Core/NullstellensatzCodim.lean:225:alg-closed, `σ` finite), the vanishing ideal is `⊥` (prime), `varietyDim = Nat.card σ`, the bridge
./route-choice-answer.md:713:./DLNFibre/Core/NullstellensatzCodim.lean:229:    (vanishingIdeal k (Set.univ : Set (σ → k)) : Ideal (MvPolynomial σ k)).height
./route-choice-answer.md:714:./DLNFibre/Core/NullstellensatzCodim.lean:230:      + varietyDim (Set.univ : Set (σ → k)) = (Nat.card σ : ℕ∞) := by
./route-choice-answer.md:715:./DLNFibre/Core/NullstellensatzCodim.lean:231:  haveI : (vanishingIdeal k (Set.univ : Set (σ → k)) :
./route-choice-answer.md:716:./DLNFibre/Core/NullstellensatzCodim.lean:232:      Ideal (MvPolynomial σ k)).IsPrime := by rw [vanishingIdeal_univ_eq_bot]; infer_instance
./route-choice-answer.md:717:./DLNFibre/Core/NullstellensatzCodim.lean:233:  exact height_vanishingIdeal_add_varietyDim_eq_card this
./route-choice-answer.md:718:./DLNFibre/Core/OrbitSmooth.lean:12:`M`: the coordinate ring `A = MvPolynomial (RepCoord d) k ⧸ vanishingIdeal(canonicalCoord '' Z_M)`
./route-choice-answer.md:719:./DLNFibre/Core/OrbitSmooth.lean:81:`A = MvPolynomial (RepCoord d) k ⧸ I` with `I = vanishingIdeal (orbitSet M)`. By L6.4
./route-choice-answer.md:720:./DLNFibre/Core/OrbitSmooth.lean:82:(`vanishingIdeal_orbitRankLocus_eq_orbitSet`) this is the coordinate ring of the rank locus
./route-choice-answer.md:721:./DLNFibre/Core/OrbitSmooth.lean:83:`Z_M = canonicalCoord '' orbitRankLocus M`; by L1 (`isPrime_vanishingIdeal_orbitSet`) it is a
./route-choice-answer.md:722:./DLNFibre/Core/OrbitSmooth.lean:86:/-- The vanishing ideal `I = vanishingIdeal (orbitSet M)` we quotient by — the defining ideal of the
./route-choice-answer.md:723:./DLNFibre/Core/OrbitSmooth.lean:90:  MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k (orbitSet M)
./route-choice-answer.md:724:./DLNFibre/Core/OrbitSmooth.lean:96:/-- `A` is a **domain**: `I = vanishingIdeal (orbitSet M)` is prime (L1, orbit irreducible). -/
./route-choice-answer.md:725:./DLNFibre/Core/OrbitSmooth.lean:99:  haveI : (orbitIdeal M).IsPrime := isPrime_vanishingIdeal_orbitSet M
./route-choice-answer.md:726:./DLNFibre/Core/OrbitSmooth.lean:103:(`baseChangePullback_mem_vanishingIdeal_orbitSet`). -/
./route-choice-answer.md:727:./DLNFibre/Core/OrbitSmooth.lean:111:  exact baseChangePullback_mem_vanishingIdeal_orbitSet M P hf
./route-choice-answer.md:728:./DLNFibre/Core/OrbitSmooth.lean:158:`I = vanishingIdeal (orbitSet M)` to `0`, so `eval (canonicalCoord (P • M)) : R → k` descends to a
./route-choice-answer.md:729:./DLNFibre/Core/OrbitSmooth.lean:172:  rw [orbitIdeal, MvPolynomial.mem_vanishingIdeal_iff] at hf
./route-choice-answer.md:730:./DLNFibre/Core/OrbitSmooth.lean:305:orbit point has `g ∈ vanishingIdeal (orbitSet M) = I`, so `mk g = 0`; the vanishing ideal of the
./route-choice-answer.md:731:./DLNFibre/Core/OrbitSmooth.lean:314:`vanishingIdeal (orbitSet M)`-equality through the quotient). A class `mk g` lying in every orbit
./route-choice-answer.md:732:./DLNFibre/Core/OrbitSmooth.lean:316:theorem vanishingIdeal_orbitSpecSet_eq_bot [Infinite k] {d : Fin (N + 1) → ℕ}
./route-choice-answer.md:733:./DLNFibre/Core/OrbitSmooth.lean:318:    PrimeSpectrum.vanishingIdeal (orbitSpecSet M) = ⊥ := by
./route-choice-answer.md:734:./DLNFibre/Core/OrbitSmooth.lean:321:  rw [PrimeSpectrum.mem_vanishingIdeal] at ha
./route-choice-answer.md:735:./DLNFibre/Core/OrbitSmooth.lean:332:    rw [orbitIdeal, MvPolynomial.mem_vanishingIdeal_iff]
./route-choice-answer.md:736:./DLNFibre/Core/OrbitSmooth.lean:340:(`vanishingIdeal_orbitSpecSet_eq_bot`) and `A` is reduced (a domain), so the closure is `univ`. -/
./route-choice-answer.md:737:./DLNFibre/Core/OrbitSmooth.lean:343:  rw [dense_iff_closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
./route-choice-answer.md:738:./DLNFibre/Core/OrbitSmooth.lean:344:    vanishingIdeal_orbitSpecSet_eq_bot M, PrimeSpectrum.zeroLocus_bot]
./route-choice-answer.md:740:./DLNFibre/Core/FibreReducedTrivialization.lean:33:3. **`vanishingIdeal_fibre_eq_fibreGenIdeal_of_trivialization`** — the **radical-collapse** of
./route-choice-answer.md:741:./DLNFibre/Core/FibreReducedTrivialization.lean:34:   `MultComorphism` point 4: with the cut ideal radical, `vanishingIdeal (fibre d B) =
./route-choice-answer.md:744:./DLNFibre/Core/FibreReducedTrivialization.lean:104:a `vanishingIdeal`), the fibre ideal `fibreGenIdeal d B` is **radical**. The certified mechanism:
./route-choice-answer.md:745:./DLNFibre/Core/FibreReducedTrivialization.lean:122:`vanishingIdeal (fibre d B) = radical (fibreGenIdeal d B)` collapses to
./route-choice-answer.md:746:./DLNFibre/Core/FibreReducedTrivialization.lean:123:`vanishingIdeal (fibre d B) = fibreGenIdeal d B`: the `radical (·)` wrapper drops. The clean
./route-choice-answer.md:747:./DLNFibre/Core/FibreReducedTrivialization.lean:126:theorem vanishingIdeal_fibre_eq_fibreGenIdeal_of_trivialization [IsAlgClosed k]
./route-choice-answer.md:748:./DLNFibre/Core/FibreReducedTrivialization.lean:131:    vanishingIdeal k (canonicalCoord d '' fibre d B) = fibreGenIdeal d B := by
./route-choice-answer.md:749:./DLNFibre/Core/FibreReducedTrivialization.lean:132:  rw [vanishingIdeal_image_fibre_eq_radical,
./route-choice-answer.md:784:./DLNFibre/Core/SigmaCodim.lean:67:    have hmem : (MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
./route-choice-answer.md:785:./DLNFibre/Core/SigmaCodim.lean:70:        ≤ MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
./route-choice-answer.md:786:./DLNFibre/Core/SigmaCodim.lean:73:    haveI : (MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
./route-choice-answer.md:787:./DLNFibre/Core/SigmaCodim.lean:75:      isPrime_vanishingIdeal_orbitRankLocus M
./route-choice-answer.md:791:./DLNFibre/Core/SigmaCodim.lean:114:          (isPrime_vanishingIdeal_orbitRankLocus (realizerD (k := k) hm₀)).ne_top
./route-choice-answer.md:796:./DLNFibre/Core/PolynomialCurveLimit.lean:11:point `pt c 0` lies in `zeroLocus (vanishingIdeal Z)` — the Zariski closure of `Z`. Equivalently,
./route-choice-answer.md:797:./DLNFibre/Core/PolynomialCurveLimit.lean:14:The argument is the elementary one: for a fixed `g ∈ vanishingIdeal Z`, substituting the curve into
./route-choice-answer.md:798:./DLNFibre/Core/PolynomialCurveLimit.lean:54:the Zariski closure of `Z`: `curvePoint c 0 ∈ zeroLocus (vanishingIdeal Z)`. -/
./route-choice-answer.md:799:./DLNFibre/Core/PolynomialCurveLimit.lean:55:theorem curvePoint_zero_mem_zeroLocus_vanishingIdeal [Infinite k]
./route-choice-answer.md:800:./DLNFibre/Core/PolynomialCurveLimit.lean:58:    curvePoint c 0 ∈ zeroLocus k (vanishingIdeal k Z) := by
./route-choice-answer.md:801:./DLNFibre/Core/PolynomialCurveLimit.lean:65:    exact (MvPolynomial.mem_vanishingIdeal_iff).mp hg _ (hZ t ht)
./route-choice-answer.md:802:./DLNFibre/Core/PolynomialCurveLimit.lean:75:/-- **L6.0, unfolded.** Restatement of `curvePoint_zero_mem_zeroLocus_vanishingIdeal`: every
./route-choice-answer.md:803:./DLNFibre/Core/PolynomialCurveLimit.lean:77:theorem aeval_curvePoint_zero_eq_zero_of_mem_vanishingIdeal [Infinite k]
./route-choice-answer.md:804:./DLNFibre/Core/PolynomialCurveLimit.lean:80:    {g : MvPolynomial σ k} (hg : g ∈ vanishingIdeal k Z) :
./route-choice-answer.md:805:./DLNFibre/Core/PolynomialCurveLimit.lean:82:  have := curvePoint_zero_mem_zeroLocus_vanishingIdeal c Z hZ
./route-choice-answer.md:806:./DLNFibre/Core/PolynomialCurveLimit.lean:87:/-- **L6.0 for a Zariski-closed target.** If `Z = zeroLocus (vanishingIdeal Z)` (Zariski-closed)
./route-choice-answer.md:807:./DLNFibre/Core/PolynomialCurveLimit.lean:92:    (hZclosed : Z = zeroLocus k (vanishingIdeal k Z))
./route-choice-answer.md:808:./DLNFibre/Core/PolynomialCurveLimit.lean:96:  exact curvePoint_zero_mem_zeroLocus_vanishingIdeal c Z hZ
./route-choice-answer.md:809:./DLNFibre/Core/PolynomialCurveLimit.lean:107:`t` (so in particular for `t ≠ 0`), and its limit `a` lies in `zeroLocus (vanishingIdeal Z)` — a
./route-choice-answer.md:810:./DLNFibre/Core/PolynomialCurveLimit.lean:110:    a ∈ zeroLocus k (vanishingIdeal k Z) := by
./route-choice-answer.md:811:./DLNFibre/Core/PolynomialCurveLimit.lean:115:  have h := curvePoint_zero_mem_zeroLocus_vanishingIdeal (fun x ↦ Polynomial.C (a x)) Z hmem
./route-choice-answer.md:813:./DLNFibre/Core/PolynomialDimension.lean:18:* **L5.5** `ringKrullDim_quotient_eq_noetherRank` — `dim (R ⧸ p)` equals the Noether-normalization
./route-choice-answer.md:820:./DLNFibre/Core/OrbitDifferentialRank.lean:35:Krull-dimension bound) and `varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional`
./route-choice-answer.md:821:./DLNFibre/Core/OrbitDifferentialRank.lean:659:/-- **The AG-half submersion bound `varietyDim Z_M ≤ finrank (range δ⁰)`, UNCONDITIONAL (char 0).**
./route-choice-answer.md:822:./DLNFibre/Core/OrbitDifferentialRank.lean:660:Chaining the unconditional A4.4 with the landed A0 link `varietyDim_eq_ringKrullDim_range_orbitPullback`
./route-choice-answer.md:823:./DLNFibre/Core/OrbitDifferentialRank.lean:664:theorem varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional
./route-choice-answer.md:824:./DLNFibre/Core/OrbitDifferentialRank.lean:666:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./route-choice-answer.md:825:./DLNFibre/Core/OrbitDifferentialRank.lean:668:  varietyDim_orbitRankLocus_le_finrank_range_deformationδ M
./route-choice-answer.md:828:./DLNFibre/Core/DeterminantalChartRing.lean:253:  rw [sigmaIdeal, mem_vanishingIdeal_iff]
./route-choice-answer.md:833:./DLNFibre/Core/DeterminantalChartRing.lean:345:  rw [sigmaIdeal, mem_vanishingIdeal_iff]
./route-choice-answer.md:834:./DLNFibre/Core/DeterminantalChartRing.lean:367:    rw [sigmaIdeal]; exact isPrime_vanishingIdeal_productRankLocusLE_stratum q p r hq hp
./route-choice-answer.md:846:./DLNFibre/Core/RadicalCatenary.lean:27:The headline specialises to `codimRepCanonical Z + varietyDim Z = card` for any **nonempty**
./route-choice-answer.md:847:./DLNFibre/Core/RadicalCatenary.lean:157:/-! ## Specialisation to the geometry layer (`codimRepCanonical Z + varietyDim Z = card`) -/
./route-choice-answer.md:848:./DLNFibre/Core/RadicalCatenary.lean:160:cannot be the unit `1` (which evaluates to `1 ≠ 0`), so `vanishingIdeal Z ≠ ⊤`. -/
./route-choice-answer.md:849:./DLNFibre/Core/RadicalCatenary.lean:161:theorem vanishingIdeal_ne_top_of_nonempty [Finite σ] {Z : Set (σ → k)} (hZ : Z.Nonempty) :
./route-choice-answer.md:850:./DLNFibre/Core/RadicalCatenary.lean:162:    (vanishingIdeal k Z : Ideal (MvPolynomial σ k)) ≠ ⊤ := by
./route-choice-answer.md:851:./DLNFibre/Core/RadicalCatenary.lean:166:  rw [MvPolynomial.mem_vanishingIdeal_iff] at hone
./route-choice-answer.md:852:./DLNFibre/Core/RadicalCatenary.lean:173:/-- **The reducible-locus catenary at `codimRepCanonical`/`varietyDim` (additive, `ℕ∞`).** For a
./route-choice-answer.md:853:./DLNFibre/Core/RadicalCatenary.lean:176:equal the ambient dimension: `codimRepCanonical Z + varietyDim (canonicalCoord d '' Z) = card`. No
./route-choice-answer.md:854:./DLNFibre/Core/RadicalCatenary.lean:179:theorem codimRepCanonical_add_varietyDim_eq_card_of_nonempty {d : Fin (N + 1) → ℕ}
./route-choice-answer.md:855:./DLNFibre/Core/RadicalCatenary.lean:181:    codimRepCanonical Z + varietyDim (canonicalCoord d '' Z)
./route-choice-answer.md:856:./DLNFibre/Core/RadicalCatenary.lean:183:  have hIne : (vanishingIdeal k (canonicalCoord d '' Z) :
./route-choice-answer.md:857:./DLNFibre/Core/RadicalCatenary.lean:185:    vanishingIdeal_ne_top_of_nonempty hZ
./route-choice-answer.md:858:./DLNFibre/Core/RadicalCatenary.lean:187:    (vanishingIdeal k (canonicalCoord d '' Z)) hIne
./route-choice-answer.md:859:./DLNFibre/Core/RadicalCatenary.lean:188:  haveI : Nontrivial (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal k (canonicalCoord d '' Z)) :=
./route-choice-answer.md:860:./DLNFibre/Core/RadicalCatenary.lean:191:      (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal k (canonicalCoord d '' Z)) :=
./route-choice-answer.md:861:./DLNFibre/Core/RadicalCatenary.lean:194:      (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal k (canonicalCoord d '' Z)) ≠ ⊥ :=
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
./route-choice-answer.md:892:./DLNFibre/Core/BoxMoveDegeneration.lean:19:**The engine** `mem_zeroLocus_vanishingIdeal_orbitSet_of_polynomialFamily` is the reusable,
./route-choice-answer.md:893:./DLNFibre/Core/BoxMoveDegeneration.lean:23:    canonicalCoord d D ∈ zeroLocus (vanishingIdeal (orbitSet U))
./route-choice-answer.md:894:./DLNFibre/Core/BoxMoveDegeneration.lean:80:orbit of `U`: `canonicalCoord D ∈ zeroLocus (vanishingIdeal (orbitSet U))`. The L6.0-consumption
./route-choice-answer.md:895:./DLNFibre/Core/BoxMoveDegeneration.lean:82:theorem mem_zeroLocus_vanishingIdeal_orbitSet_of_polynomialFamily [Infinite k]
./route-choice-answer.md:896:./DLNFibre/Core/BoxMoveDegeneration.lean:88:          (MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k (orbitSet U)) := by
./route-choice-answer.md:897:./DLNFibre/Core/BoxMoveDegeneration.lean:92:  refine curvePoint_zero_mem_zeroLocus_vanishingIdeal (tupleCurve Fpoly) (orbitSet U)
./route-choice-answer.md:898:./DLNFibre/Core/BoxMoveDegeneration.lean:208:`mem_zeroLocus_vanishingIdeal_orbitSet_of_polynomialFamily` then lands the headline from the limit
./route-choice-answer.md:899:./DLNFibre/Core/BoxMoveDegeneration.lean:232:`M_{[0,2]} ⊕ M_{[1,1]}`: it is in `zeroLocus (vanishingIdeal (orbitSet upstairs))`. An instance of
./route-choice-answer.md:900:./DLNFibre/Core/BoxMoveDegeneration.lean:233:the degeneration engine `mem_zeroLocus_vanishingIdeal_orbitSet_of_polynomialFamily`: the polynomial
./route-choice-answer.md:901:./DLNFibre/Core/BoxMoveDegeneration.lean:239:          (MvPolynomial.vanishingIdeal (σ := RepCoord boxDim) (K := k) k
./route-choice-answer.md:902:./DLNFibre/Core/BoxMoveDegeneration.lean:241:  refine mem_zeroLocus_vanishingIdeal_orbitSet_of_polynomialFamily boxMoveWitnessUp
./route-choice-answer.md:903:./DLNFibre/Core/MultComorphism.lean:27:4. **`vanishingIdeal(fibre) = radical(fibreGenIdeal)`** — over `[IsAlgClosed k]`, the engine's
./route-choice-answer.md:904:./DLNFibre/Core/MultComorphism.lean:28:   Nullstellensatz (`vanishingIdeal_zeroLocus_eq_radical`) reads the fibre's vanishing ideal as the
./route-choice-answer.md:905:./DLNFibre/Core/MultComorphism.lean:158:closed field, the engine's strong Nullstellensatz (`vanishingIdeal_zeroLocus_eq_radical`) reads the
./route-choice-answer.md:906:./DLNFibre/Core/MultComorphism.lean:160:theorem vanishingIdeal_image_fibre_eq_radical [IsAlgClosed k] (d : Fin (N + 1) → ℕ)
./route-choice-answer.md:907:./DLNFibre/Core/MultComorphism.lean:162:    vanishingIdeal k (canonicalCoord d '' (fibre d B)) = (fibreGenIdeal d B).radical := by
./route-choice-answer.md:908:./DLNFibre/Core/MultComorphism.lean:164:    vanishingIdeal_zeroLocus_eq_radical (K := k)]
./route-choice-answer.md:909:./DLNFibre/Core/FibreNormalForm.lean:111:theorem vanishingIdeal_image_smul [Infinite k] (d : Fin (N + 1) → ℕ)
./route-choice-answer.md:910:./DLNFibre/Core/FibreNormalForm.lean:113:    vanishingIdeal k (canonicalCoord d '' ((fun A ↦ P • A) '' Z))
./route-choice-answer.md:911:./DLNFibre/Core/FibreNormalForm.lean:114:      = (vanishingIdeal k (canonicalCoord d '' Z)).comap
./route-choice-answer.md:912:./DLNFibre/Core/FibreNormalForm.lean:117:  rw [Ideal.mem_comap, MvPolynomial.mem_vanishingIdeal_iff, MvPolynomial.mem_vanishingIdeal_iff]
./route-choice-answer.md:913:./DLNFibre/Core/FibreNormalForm.lean:138:codimRep (canonicalCoord) Z`. The transport `vanishingIdeal_image_smul` reads the shifted vanishing
./route-choice-answer.md:914:./DLNFibre/Core/FibreNormalForm.lean:144:  rw [codimRep, codimRep, vanishingIdeal_image_smul]
./route-choice-answer.md:915:./DLNFibre/Core/BoxMoveGeneral.lean:7:`mem_zeroLocus_vanishingIdeal_orbitSet_of_polynomialFamily`, generalising the certified `(1,2,1)`
./route-choice-answer.md:916:./DLNFibre/Core/BoxMoveGeneral.lean:141:          (MvPolynomial.vanishingIdeal (σ := RepCoord (fun l ↦ d l + d' l)) (K := k) k
./route-choice-answer.md:917:./DLNFibre/Core/BoxMoveGeneral.lean:143:  refine mem_zeroLocus_vanishingIdeal_orbitSet_of_polynomialFamily (dirSum U₀ R) (dirSum D₀ R)
./route-choice-answer.md:918:./DLNFibre/Core/BoxMoveGeneral.lean:194:          (MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k (orbitSet U)) := by
./route-choice-answer.md:919:./DLNFibre/Core/BoxMoveGeneral.lean:195:  refine mem_zeroLocus_vanishingIdeal_orbitSet_of_polynomialFamily U D' (smulPoly Q F) ?_
./route-choice-answer.md:920:./DLNFibre/Core/BoxMoveGeneral.lean:214:          (MvPolynomial.vanishingIdeal (σ := RepCoord (fun l ↦ d l + d' l)) (K := k) k
./route-choice-answer.md:921:./DLNFibre/Core/BoxMoveGeneral.lean:347:`M_{[a,e]}`: it is in `zeroLocus (vanishingIdeal (orbitSet (intervalModule a e)))`. An instance of
./route-choice-answer.md:922:./DLNFibre/Core/BoxMoveGeneral.lean:353:          (MvPolynomial.vanishingIdeal (σ := RepCoord (intervalDim a e)) (K := k) k
./route-choice-answer.md:923:./DLNFibre/Core/BoxMoveGeneral.lean:355:  refine mem_zeroLocus_vanishingIdeal_orbitSet_of_polynomialFamily (intervalModule a e)
./route-choice-answer.md:924:./DLNFibre/Core/BoxMoveGeneral.lean:587:          (MvPolynomial.vanishingIdeal
./route-choice-answer.md:925:./DLNFibre/Core/BoxMoveGeneral.lean:1159:          (MvPolynomial.vanishingIdeal
./route-choice-answer.md:926:./DLNFibre/Core/BoxMoveGeneral.lean:1186:        (MvPolynomial.vanishingIdeal (σ := RepCoord (intervalDim (0 : Fin 3) 2)) (K := ℚ) ℚ
./route-choice-answer.md:927:./DLNFibre/Core/BoxMoveGeneral.lean:1205:        (MvPolynomial.vanishingIdeal
./route-choice-answer.md:928:./DLNFibre/Core/BoxMoveGeneral.lean:1224:        (MvPolynomial.vanishingIdeal
./route-choice-answer.md:929:./DLNFibre/Core/BoxMoveGeneral.lean:1269:          (MvPolynomial.vanishingIdeal
./route-choice-answer.md:934:./DLNFibre/Core/AffineNoetherRank.lean:59:Noether-normalization rank `s`, hence agree: `(ringKrullDim (R ⧸ p)).unbotD 0 = (trdeg k (R ⧸ p)).toNat`.
./route-choice-answer.md:935:./DLNFibre/Core/ChartFlatnessProbe.lean:28:`vanishingIdeal`s — so the Schur section cannot be exhibited as an `AlgEquiv` without first building
./route-choice-answer.md:936:./DLNFibre/Core/ChartFlatnessProbe.lean:92:the trivializing `AlgEquiv` from the engine's opaque `vanishingIdeal`-quotients, not the closer. -/
./route-choice-answer.md:939:./DLNFibre/Core/FibreDimFibrationProbe.lean:37:/-- LANDED: the determinantal-stratum dimension `varietyDim (Mat^{≤r}) = r(n+m−r) = δ`. -/
./route-choice-answer.md:940:./DLNFibre/Core/FibreDimFibrationProbe.lean:39:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./route-choice-answer.md:941:./DLNFibre/Core/FibreDimFibrationProbe.lean:41:  varietyDim_productRankLocusLE_stratum n m r hn hm
./route-choice-answer.md:944:./DLNFibre/Core/FibreDimFibrationProbe.lean:55:/-- LANDED: the catenary closer (PRIMALITY-gated) — `codim Z = card − varietyDim Z`. -/
./route-choice-answer.md:945:./DLNFibre/Core/FibreDimFibrationProbe.lean:57:    (hp : (vanishingIdeal k (canonicalCoord d '' Z) :
./route-choice-answer.md:946:./DLNFibre/Core/FibreDimFibrationProbe.lean:59:    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
./route-choice-answer.md:947:./DLNFibre/Core/FibreDimFibrationProbe.lean:60:  codimRepCanonical_eq_card_sub_varietyDim Z hp
./route-choice-answer.md:949:./DLNFibre/Core/FibreDimFibrationProbe.lean:88:    (vanishingIdeal k (canonicalCoord (dStratum (d 0) (d (Fin.last N))) ''
./route-choice-answer.md:951:./DLNFibre/Core/FibreDimFibrationProbe.lean:91:  isPrime_vanishingIdeal_productRankLocusLE_stratum (d 0) (d (Fin.last N)) r hq hp
./route-choice-answer.md:952:./DLNFibre/Core/FibreDimFibrationProbe.lean:96:MvPolynomial (RepCoord stratum) k ⧸ vanishingIdeal(…)`. From the thermometer (varietyDim = δ) which
./route-choice-answer.md:953:./DLNFibre/Core/FibreDimFibrationProbe.lean:97:unfolds to exactly `(ringKrullDim (… ⧸ vanishingIdeal …)).unbotD 0`, plus the quotient is nontrivial
./route-choice-answer.md:954:./DLNFibre/Core/FibreDimFibrationProbe.lean:100:/-- `varietyDim` unfolds to the `unbotD 0` of the quotient `ringKrullDim`. -/
./route-choice-answer.md:955:./DLNFibre/Core/FibreDimFibrationProbe.lean:102:    varietyDim Z = (ringKrullDim (MvPolynomial (RepCoord (dStratum 2 2)) k ⧸
./route-choice-answer.md:956:./DLNFibre/Core/FibreDimFibrationProbe.lean:103:      MvPolynomial.vanishingIdeal (K := k) k Z)).unbotD 0 := rfl
./route-choice-answer.md:958:./DLNFibre/Core/SigmaComponents.lean:17:  `Σ̄^r` are exactly the inclusion-minimal orbit ideals `vanishingIdeal Ō_M` over the corner-`≤ r`
./route-choice-answer.md:959:./DLNFibre/Core/SigmaComponents.lean:19:  the aggregate ideal `sigmaIdeal d r := vanishingIdeal (canonicalCoord d '' Σ̄^r)` is the `sInf` of
./route-choice-answer.md:960:./DLNFibre/Core/SigmaComponents.lean:20:  the finite family of prime orbit ideals (G2 + `vanishingIdeal` turns unions into infs), so its
./route-choice-answer.md:961:./DLNFibre/Core/SigmaComponents.lean:78:`M ↦ vanishingIdeal (canonicalCoord d '' Ō_M)` over `{M | (mult d M).rank ≤ r}`. -/
./route-choice-answer.md:962:./DLNFibre/Core/SigmaComponents.lean:82:      MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
./route-choice-answer.md:963:./DLNFibre/Core/SigmaComponents.lean:100:/-- The family map `M ↦ vanishingIdeal (Ō_M)` factors through `rpBounded`: equal bounded rank
./route-choice-answer.md:964:./DLNFibre/Core/SigmaComponents.lean:105:        MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
./route-choice-answer.md:965:./DLNFibre/Core/SigmaComponents.lean:117:/-- The orbit-ideal family is finite: `vanishingIdeal (Ō_M)` depends only on `rankPattern M`, which
./route-choice-answer.md:967:./DLNFibre/Core/SigmaComponents.lean:132:  MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
./route-choice-answer.md:969:./DLNFibre/Core/SigmaComponents.lean:136:orbit-ideal family: `vanishingIdeal` turns the G2 union `Σ̄^r = ⋃_M Ō_M` into an intersection. -/
./route-choice-answer.md:970:./DLNFibre/Core/SigmaComponents.lean:145:    rw [mem_vanishingIdeal_iff] at hp ⊢
./route-choice-answer.md:972:./DLNFibre/Core/SigmaComponents.lean:152:    rw [mem_vanishingIdeal_iff]
./route-choice-answer.md:974:./DLNFibre/Core/SigmaComponents.lean:158:    rw [mem_vanishingIdeal_iff] at hmem
./route-choice-answer.md:975:./DLNFibre/Core/SigmaComponents.lean:164:`vanishingIdeal (Ō_M) ≤ vanishingIdeal (Ō_M') ↔ Ō_M' ⊆ Ō_M`. The `←` is `vanishingIdeal_anti_mono`;
./route-choice-answer.md:976:./DLNFibre/Core/SigmaComponents.lean:165:the `→` uses that `Ō_M = zeroLocus (vanishingIdeal Ō_M)` (`isZariskiClosed_orbitRankLocus`). So
./route-choice-answer.md:977:./DLNFibre/Core/SigmaComponents.lean:168:theorem vanishingIdeal_orbitRankLocus_le_iff (d : Fin (N + 1) → ℕ)
./route-choice-answer.md:978:./DLNFibre/Core/SigmaComponents.lean:170:    MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k (canonicalCoord d '' orbitRankLocus M)
./route-choice-answer.md:979:./DLNFibre/Core/SigmaComponents.lean:171:        ≤ MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
./route-choice-answer.md:980:./DLNFibre/Core/SigmaComponents.lean:178:          (MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
./route-choice-answer.md:981:./DLNFibre/Core/SigmaComponents.lean:181:    exact (MvPolynomial.zeroLocus_vanishingIdeal_le _).trans (MvPolynomial.zeroLocus_anti_mono hle)
./route-choice-answer.md:982:./DLNFibre/Core/SigmaComponents.lean:182:  · exact MvPolynomial.vanishingIdeal_anti_mono
./route-choice-answer.md:983:./DLNFibre/Core/SigmaComponents.lean:186:/-- Every member of the orbit-ideal family is prime: it is `vanishingIdeal (Ō_M)`, prime over an
./route-choice-answer.md:984:./DLNFibre/Core/SigmaComponents.lean:187:algebraically closed field (`Core.OrbitClosure.isPrime_vanishingIdeal_orbitRankLocus`). -/
./route-choice-answer.md:985:./DLNFibre/Core/SigmaComponents.lean:191:  exact isPrime_vanishingIdeal_orbitRankLocus M
./route-choice-answer.md:986:./DLNFibre/Core/SigmaComponents.lean:194:`Σ̄^r` are exactly the **inclusion-minimal** orbit ideals `vanishingIdeal (Ō_M)` over the
./route-choice-answer.md:987:./DLNFibre/Core/SigmaComponents.lean:195:corner-`≤ r` family. Since `vanishingIdeal` is order-reversing
./route-choice-answer.md:988:./DLNFibre/Core/SigmaComponents.lean:196:(`vanishingIdeal_orbitRankLocus_le_iff`), "inclusion-minimal orbit ideal" = "maximal orbit closure
./route-choice-answer.md:989:./DLNFibre/Core/SigmaComponents.lean:249:LANDED `codimRepCanonical (orbitRankLocus M)` is exactly `(vanishingIdeal (Ō_M)).height`, the
./route-choice-answer.md:990:./DLNFibre/Core/SigmaComponents.lean:254:      = (MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
./route-choice-answer.md:991:./DLNFibre/Core/SigmaComponents.lean:261:`vanishingIdeal Ō_M' ⊊ vanishingIdeal Ō_M` and the strict-height brick
./route-choice-answer.md:992:./DLNFibre/Core/SigmaComponents.lean:268:    MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k (canonicalCoord d '' orbitRankLocus M)
./route-choice-answer.md:993:./DLNFibre/Core/SigmaComponents.lean:273:  -- `q = vanishingIdeal Ō_M' ≤ vanishingIdeal Ō_M`. If strict, height strictly drops — contra min.
./route-choice-answer.md:994:./DLNFibre/Core/SigmaComponents.lean:277:    haveI : (MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
./route-choice-answer.md:995:./DLNFibre/Core/SigmaComponents.lean:278:        (canonicalCoord d '' orbitRankLocus M')).IsPrime := isPrime_vanishingIdeal_orbitRankLocus M'
./route-choice-answer.md:1000:./DLNFibre/Core/OrbitClosure.lean:12:sets). With L1's `isPrime_vanishingIdeal_orbitSet` this gives the rank locus a prime vanishing ideal
./route-choice-answer.md:1001:./DLNFibre/Core/OrbitClosure.lean:16:is `RankLocusClosed.vanishingIdeal_orbitRankLocus_le_orbitSet`). Architecture (Codex-vetted):
./route-choice-answer.md:1002:./DLNFibre/Core/OrbitClosure.lean:18:1. **Closure operator** `repClosure S = zeroLocus (vanishingIdeal (canonicalCoord '' S))` — the
./route-choice-answer.md:1003:./DLNFibre/Core/OrbitClosure.lean:32:   orbitRankLocus M` at the ideal level — the headline `vanishingIdeal (canonicalCoord ''
./route-choice-answer.md:1004:./DLNFibre/Core/OrbitClosure.lean:33:   orbitRankLocus M) = vanishingIdeal (orbitSet M)`.
./route-choice-answer.md:1005:./DLNFibre/Core/OrbitClosure.lean:34:5. **Primeness** (`isPrime_vanishingIdeal_orbitRankLocus`): the headline + L1.
./route-choice-answer.md:1006:./DLNFibre/Core/OrbitClosure.lean:54:    (MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k S)
./route-choice-answer.md:1007:./DLNFibre/Core/OrbitClosure.lean:59:  MvPolynomial.zeroLocus_vanishingIdeal_le S
./route-choice-answer.md:1008:./DLNFibre/Core/OrbitClosure.lean:64:  MvPolynomial.zeroLocus_anti_mono (MvPolynomial.vanishingIdeal_anti_mono h)
./route-choice-answer.md:1009:./DLNFibre/Core/OrbitClosure.lean:67:`l ∘ u` of the (order-dual) Galois connection `zeroLocus ⊣ vanishingIdeal`, via `u_l_u_eq_u`. -/
./route-choice-answer.md:1010:./DLNFibre/Core/OrbitClosure.lean:71:    ((MvPolynomial.zeroLocus_vanishingIdeal_galoisConnection
./route-choice-answer.md:1011:./DLNFibre/Core/OrbitClosure.lean:199:theorem baseChangePullback_mem_vanishingIdeal_orbitSet {d : Fin (N + 1) → ℕ} (U : Tuple (k := k) d)
./route-choice-answer.md:1012:./DLNFibre/Core/OrbitClosure.lean:201:    (hf : f ∈ MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k (orbitSet U)) :
./route-choice-answer.md:1013:./DLNFibre/Core/OrbitClosure.lean:203:      ∈ MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k (orbitSet U) := by
./route-choice-answer.md:1014:./DLNFibre/Core/OrbitClosure.lean:204:  rw [MvPolynomial.mem_vanishingIdeal_iff] at hf ⊢
./route-choice-answer.md:1015:./DLNFibre/Core/OrbitClosure.lean:228:  have := hmem (baseChangePullback Q f) (baseChangePullback_mem_vanishingIdeal_orbitSet U Q hf)
./route-choice-answer.md:1016:./DLNFibre/Core/OrbitClosure.lean:951:/-- `vanishingIdeal` is invisible to `repClosure`: closure has the same vanishing ideal as `S`
./route-choice-answer.md:1017:./DLNFibre/Core/OrbitClosure.lean:953:theorem vanishingIdeal_repClosure {d : Fin (N + 1) → ℕ} (S : Set (RepCoord d → k)) :
./route-choice-answer.md:1018:./DLNFibre/Core/OrbitClosure.lean:954:    MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k (repClosure S)
./route-choice-answer.md:1019:./DLNFibre/Core/OrbitClosure.lean:955:      = MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k S :=
./route-choice-answer.md:1020:./DLNFibre/Core/OrbitClosure.lean:956:  (MvPolynomial.zeroLocus_vanishingIdeal_galoisConnection
./route-choice-answer.md:1021:./DLNFibre/Core/OrbitClosure.lean:970:orbitRankLocus M` as closed sets. The easy `≤` is `vanishingIdeal_orbitRankLocus_le_orbitSet`; the
./route-choice-answer.md:1022:./DLNFibre/Core/OrbitClosure.lean:972:`vanishingIdeal` (order-reversing) with `vanishingIdeal_repClosure`. -/
./route-choice-answer.md:1023:./DLNFibre/Core/OrbitClosure.lean:973:theorem vanishingIdeal_orbitRankLocus_eq_orbitSet [Infinite k] {d : Fin (N + 1) → ℕ}
./route-choice-answer.md:1024:./DLNFibre/Core/OrbitClosure.lean:975:    MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
./route-choice-answer.md:1025:./DLNFibre/Core/OrbitClosure.lean:977:      = MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k (orbitSet M) := by
./route-choice-answer.md:1026:./DLNFibre/Core/OrbitClosure.lean:978:  refine le_antisymm (vanishingIdeal_orbitRankLocus_le_orbitSet M) ?_
./route-choice-answer.md:1027:./DLNFibre/Core/OrbitClosure.lean:979:  calc MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k (orbitSet M)
./route-choice-answer.md:1028:./DLNFibre/Core/OrbitClosure.lean:980:      = MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k (repClosure (orbitSet M)) :=
./route-choice-answer.md:1029:./DLNFibre/Core/OrbitClosure.lean:981:        (vanishingIdeal_repClosure (orbitSet M)).symm
./route-choice-answer.md:1030:./DLNFibre/Core/OrbitClosure.lean:982:    _ ≤ MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
./route-choice-answer.md:1031:./DLNFibre/Core/OrbitClosure.lean:984:        MvPolynomial.vanishingIdeal_anti_mono (image_orbitRankLocus_subset_repClosure_orbitSet M)
./route-choice-answer.md:1032:./DLNFibre/Core/OrbitClosure.lean:999:  rw [hclosed, repClosure, repClosure, vanishingIdeal_orbitRankLocus_eq_orbitSet M]
./route-choice-answer.md:1033:./DLNFibre/Core/OrbitClosure.lean:1003:/-- **The rank locus has a prime vanishing ideal (L1★, irreducibility).** `vanishingIdeal
./route-choice-answer.md:1034:./DLNFibre/Core/OrbitClosure.lean:1004:(canonicalCoord '' orbitRankLocus M)` is prime: it equals `vanishingIdeal (orbitSet M)`
./route-choice-answer.md:1035:./DLNFibre/Core/OrbitClosure.lean:1005:(`vanishingIdeal_orbitRankLocus_eq_orbitSet`), which is prime because `O_M` is irreducible
./route-choice-answer.md:1036:./DLNFibre/Core/OrbitClosure.lean:1006:(`isPrime_vanishingIdeal_orbitSet`, L1). So the determinantal rank locus `Ō_M = orbitRankLocus M` is
./route-choice-answer.md:1037:./DLNFibre/Core/OrbitClosure.lean:1008:theorem isPrime_vanishingIdeal_orbitRankLocus [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./route-choice-answer.md:1038:./DLNFibre/Core/OrbitClosure.lean:1010:    (MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
./route-choice-answer.md:1039:./DLNFibre/Core/OrbitClosure.lean:1012:  rw [vanishingIdeal_orbitRankLocus_eq_orbitSet M]
./route-choice-answer.md:1040:./DLNFibre/Core/OrbitClosure.lean:1013:  exact isPrime_vanishingIdeal_orbitSet M
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
./route-choice-answer.md:1060:./DLNFibre/Core/VoigtDischarge.lean:65:      (isPrime_vanishingIdeal_orbitRankLocus M)
./route-choice-answer.md:1061:./DLNFibre/Core/VoigtDischarge.lean:66:    rwa [varietyDim_orbitRankLocus_eq_finrank_range_deformationδ M, ← hr] at hadd
./route-choice-answer.md:1062:./DLNFibre/Core/VoigtDischarge.lean:92:PROVED in-engine, `Core.OrbitClosure.vanishingIdeal_orbitRankLocus_eq_orbitSet`) equals the paper's
./route-choice-answer.md:1063:./DLNFibre/Core/OrbitTangentCotangent.lean:14:# `DLNFibre.Core.OrbitTangentCotangent` — A6.1: the reverse inequality `finrank(range δ⁰) ≤ varietyDim Z_M`
./route-choice-answer.md:1064:./DLNFibre/Core/OrbitTangentCotangent.lean:19:`varietyDim Z_M = finrank (range δ⁰)`, the geometric heart of Voigt's lemma.
./route-choice-answer.md:1065:./DLNFibre/Core/OrbitTangentCotangent.lean:22:`I = orbitIdeal M = vanishingIdeal(orbitSet M)` directly — no determinantal minors, no radical. The
./route-choice-answer.md:1066:./DLNFibre/Core/OrbitTangentCotangent.lean:357:    rw [orbitIdeal, ← range_orbitMap, vanishingIdeal_range_orbitMap_eq_ker M] at hf
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
./route-choice-answer.md:1077:./DLNFibre/Core/OrbitTangentCotangent.lean:607:  haveI : (orbitIdeal M).IsPrime := isPrime_vanishingIdeal_orbitSet M
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
./route-choice-answer.md:1112:./DLNFibre/Core/ThetaComponentCount.lean:21:**The bijection.** `m ↦ vanishingIdeal (Ō_{realizerD m})`, where `realizerD m` is the interval
./route-choice-answer.md:1113:./DLNFibre/Core/ThetaComponentCount.lean:184:the count-bijection ranges over): for `m ∈ kostantPartitions d r` it is `vanishingIdeal (Ō_{realizerD
./route-choice-answer.md:1114:./DLNFibre/Core/ThetaComponentCount.lean:191:    MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
./route-choice-answer.md:1115:./DLNFibre/Core/ThetaComponentCount.lean:199:      = MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
./route-choice-answer.md:1116:./DLNFibre/Core/ThetaComponentCount.lean:360:      exact Ideal.height_ne_top (isPrime_vanishingIdeal_orbitRankLocus _).ne_top
./route-choice-answer.md:1117:./DLNFibre/Core/ThetaComponentCount.lean:381:    rw [vanishingIdeal_orbitRankLocus_le_iff] at hle₁ hle₂
./route-choice-answer.md:1165:/-! ## The base-stratum Krull dimension brick: `ringKrullDim O(Mat^{≤r}) = δ`
./route-choice-answer.md:1170:(dStratum n m)) k ⧸ vanishingIdeal(…)` is a finite-type domain (the vanishing ideal is prime —
./route-choice-answer.md:1172:`varietyDim = δ`, lifting the `unbotD 0` to the genuine `WithBot ℕ∞` value (the quotient is
./route-choice-answer.md:1173:nontrivial, so `ringKrullDim ≠ ⊥`). -/
./route-choice-answer.md:1175:/-- **The base-stratum Krull dimension** `ringKrullDim O(Mat^{≤r}) = δ`. For `r ≤ n`, `r ≤ m`, over an
./route-choice-answer.md:1178:The thermometer `varietyDim_productRankLocusLE_stratum` gives the `ℕ∞`-via-`unbotD` value; this lifts
./route-choice-answer.md:1180:is a nontrivial domain, so `ringKrullDim ≠ ⊥`). -/
./route-choice-answer.md:1181:theorem ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta [IsAlgClosed k] [CharZero k]
./route-choice-answer.md:1183:    ringKrullDim (MvPolynomial (RepCoord (dStratum n m)) k ⧸
./route-choice-answer.md:1184:        MvPolynomial.vanishingIdeal (σ := RepCoord (dStratum n m)) (K := k) k
./route-choice-answer.md:1187:  set I := MvPolynomial.vanishingIdeal (σ := RepCoord (dStratum n m)) (K := k) k
./route-choice-answer.md:1190:    isPrime_vanishingIdeal_productRankLocusLE_stratum (k := k) n m r hn hm
./route-choice-answer.md:1191:  -- the thermometer: `varietyDim = δ`, i.e. `(ringKrullDim (R ⧸ I)).unbotD 0 = δ`.
./route-choice-answer.md:1192:  have hvd : varietyDim (canonicalCoord (dStratum n m) ''
./route-choice-answer.md:1194:    varietyDim_productRankLocusLE_stratum n m r hn hm
./route-choice-answer.md:1195:  rw [varietyDim, ← hI] at hvd
./route-choice-answer.md:1196:  -- the quotient is a nontrivial domain, so `ringKrullDim ≠ ⊥`.
./route-choice-answer.md:1199:  have hne : ringKrullDim (MvPolynomial (RepCoord (dStratum n m)) k ⧸ I) ≠ ⊥ :=
./route-choice-answer.md:1201:      ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (RepCoord (dStratum n m)) k ⧸ I)
./route-choice-answer.md:1209:By equidimensionality at a closed point (`OrbitTangentCotangent.height_eq_ringKrullDim_of_isMaximal_fintype`,
./route-choice-answer.md:1216:vanishingIdeal(…)` has height `δ = r(n + m − r)` — equidimensionality at a closed point of the
./route-choice-answer.md:1217:irreducible determinantal base, with `ringKrullDim O(Mat^{≤r}) = δ`. -/
./route-choice-answer.md:1218:theorem height_maximal_quotient_vanishingIdeal_stratum_eq_delta [IsAlgClosed k] [CharZero k]
./route-choice-answer.md:1221:        MvPolynomial.vanishingIdeal (σ := RepCoord (dStratum n m)) (K := k) k
./route-choice-answer.md:1225:  haveI : (MvPolynomial.vanishingIdeal (σ := RepCoord (dStratum n m)) (K := k) k
./route-choice-answer.md:1227:    isPrime_vanishingIdeal_productRankLocusLE_stratum (k := k) n m r hn hm
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
./route-choice-answer.md:1271:import DLNFibre.Core.DeepChartRing
./route-choice-answer.md:1303:/-- LANDED: the determinantal-stratum dimension `varietyDim (Mat^{≤r}) = r(n+m−r) = δ`. -/
./route-choice-answer.md:1305:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./route-choice-answer.md:1307:  varietyDim_productRankLocusLE_stratum n m r hn hm
./route-choice-answer.md:1321:/-- LANDED: the catenary closer (PRIMALITY-gated) — `codim Z = card − varietyDim Z`. -/
./route-choice-answer.md:1323:    (hp : (vanishingIdeal k (canonicalCoord d '' Z) :
./route-choice-answer.md:1325:    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
./route-choice-answer.md:1326:  codimRepCanonical_eq_card_sub_varietyDim Z hp
./route-choice-answer.md:1331:    (p.height : WithBot ℕ∞) + ringKrullDim (((MvPolynomial (Fin n) k) ⧸ I) ⧸ p)
./route-choice-answer.md:1332:      = ringKrullDim ((MvPolynomial (Fin n) k) ⧸ I) :=
./route-choice-answer.md:1333:  affine_domain_height_add_ringKrullDim_quotient_eq k n I p
./route-choice-answer.md:1338:    (m.height : WithBot ℕ∞) = ringKrullDim ((MvPolynomial (Fin n) k) ⧸ I) :=
./route-choice-answer.md:1339:  height_eq_ringKrullDim_of_isMaximal k n I m
./route-choice-answer.md:1354:    (vanishingIdeal k (canonicalCoord (dStratum (d 0) (d (Fin.last N))) ''
./route-choice-answer.md:1357:  isPrime_vanishingIdeal_productRankLocusLE_stratum (d 0) (d (Fin.last N)) r hq hp
./route-choice-answer.md:1359:/-! ## Candidate: the base ringKrullDim = δ (the brick the going-down/00OM route consumes)
./route-choice-answer.md:1361:`ringKrullDim (O(Mat^{≤r})) = δ` over `[IsAlgClosed][CharZero]`, where `O(Mat^{≤r}) =
./route-choice-answer.md:1362:MvPolynomial (RepCoord stratum) k ⧸ vanishingIdeal(…)`. From the thermometer (varietyDim = δ) which
./route-choice-answer.md:1363:unfolds to exactly `(ringKrullDim (… ⧸ vanishingIdeal …)).unbotD 0`, plus the quotient is nontrivial
./route-choice-answer.md:1366:/-- `varietyDim` unfolds to the `unbotD 0` of the quotient `ringKrullDim`. -/
./route-choice-answer.md:1368:    varietyDim Z = (ringKrullDim (MvPolynomial (RepCoord (dStratum 2 2)) k ⧸
./route-choice-answer.md:1369:      MvPolynomial.vanishingIdeal (K := k) k Z)).unbotD 0 := rfl
./route-choice-answer.md:1380:quasi-finite, so heights are preserved along an étale map, reducing `ringKrullDim` of a local ring
./route-choice-answer.md:1792:.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Basic.lean:94:proof_wanted MvPolynomial.fin_ringKrullDim_eq_add_of_isNoetherianRing
./route-choice-answer.md:1828:.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Polynomial.lean:24:* `Polynomial.ringKrullDim_of_isNoetherianRing`: the Krull dimension of `R[X]` is `dim R + 1`.
./route-choice-answer.md:1829:.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Polynomial.lean:25:* `MvPolynomial.ringKrullDim_of_isNoetherianRing`: the Krull dimension of `R[X₁, ..., Xₙ]` is
./route-choice-answer.md:1834:.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Polynomial.lean:106:lemma ringKrullDim_of_isNoetherianRing : ringKrullDim R[X] = ringKrullDim R + 1 := by
./route-choice-answer.md:1836:.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Polynomial.lean:119:lemma MvPolynomial.ringKrullDim_of_isNoetherianRing {ι : Type*} [Finite ι] :
./route-choice-answer.md:1837:.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Polynomial.lean:131:      Polynomial.ringKrullDim_of_isNoetherianRing, IH]
./route-choice-answer.md:2093:.lake/packages/mathlib/Mathlib/RingTheory/Flat/Domain.lean:37:  have H₁ := TensorProduct.map_injective_of_flat_flat (f.baseChange K) (g.baseChange K)
./route-choice-answer.md:2157:.lake/packages/mathlib/Mathlib/RingTheory/Flat/Stability.lean:23:* `Module.Flat.baseChange`: if `M` is a flat `R`-module and `S` is any `R`-algebra,
./route-choice-answer.md:2172:.lake/packages/mathlib/Mathlib/RingTheory/Flat/Stability.lean:87:instance baseChange [Flat R M] : Flat S (S ⊗[R] M) := inferInstance
./route-choice-answer.md:2314:.lake/packages/mathlib/Mathlib/RingTheory/FiniteStability.lean:42:instance baseChange [hfa : FiniteType R A] : Algebra.FiniteType B (B ⊗[R] A) := by
./route-choice-answer.md:2316:.lake/packages/mathlib/Mathlib/RingTheory/FiniteStability.lean:59:  have hgsurj : Function.Surjective g := Algebra.FiniteType.baseChangeAux_surj B hsurj
./route-choice-answer.md:2923:.lake/packages/mathlib/Mathlib/RingTheory/LinearDisjoint.lean:517:theorem rank_eq_one_of_commute_of_flat_of_self_of_inj (H : A.LinearDisjoint A) [Module.Flat R A]
./route-choice-answer.md:2945:.lake/packages/mathlib/Mathlib/RingTheory/LinearDisjoint.lean:692:theorem rank_eq_one_of_flat_of_self_of_inj (H : A.LinearDisjoint A) [Module.Flat R A]
./route-choice-answer.md:2946:.lake/packages/mathlib/Mathlib/RingTheory/LinearDisjoint.lean:694:  H.rank_eq_one_of_commute_of_flat_of_self_of_inj (fun _ _ ↦ mul_comm _ _) hinj
./route-choice-answer.md:2948:.lake/packages/mathlib/Mathlib/RingTheory/LinearDisjoint.lean:733:theorem adjoin_rank_eq_rank_left [Module.Free R A] [Module.Flat R B]
./route-choice-answer.md:2951:.lake/packages/mathlib/Mathlib/RingTheory/LinearDisjoint.lean:745:theorem adjoin_rank_eq_rank_right [Module.Free R B] [Module.Flat R A]
./route-choice-answer.md:3600:.lake/packages/mathlib/Mathlib/RingTheory/Finiteness/Descent.lean:114:  exact FiniteType.baseChangeAux_surj T hf
./route-choice-answer.md:4134:.lake/packages/mathlib/Mathlib/RingTheory/AlgebraicIndependent/RankAndCardinality.lean:56:theorem IsTranscendenceBasis.lift_rank_eq_max_lift
./route-choice-answer.md:4183:.lake/packages/mathlib/Mathlib/RingTheory/LocalRing/Module.lean:393:@[stacks 02M9] theorem nonempty_basis_of_flat_of_finrank_eq [Module.Finite R M] [Flat R M]
./route-choice-answer.md:4186:.lake/packages/mathlib/Mathlib/RingTheory/LocalRing/Module.lean:420:@[stacks 02M9] theorem free_of_flat_of_finrank_eq [Module.Finite R M] [Flat R M]
./route-choice-answer.md:4187:.lake/packages/mathlib/Mathlib/RingTheory/LocalRing/Module.lean:423:  have ⟨b⟩ := nonempty_basis_of_flat_of_finrank_eq R M n rk
./route-choice-answer.md:4253:.lake/packages/mathlib/Mathlib/RingTheory/EssentialFiniteness.lean:168:instance EssFiniteType.baseChange [h : EssFiniteType R S] : EssFiniteType T (T ⊗[R] S) := by
./route-choice-answer.md:4414:/bin/bash -lc "rg -n \"trdeg_add_eq|TranscendenceDegree|transcendenceDegree|trdeg|Algebra\\.IsAlgebraic|EssFiniteType|IsFractionRing|ringKrullDim.*trdeg|trdeg.*ringKrullDim|relative.*dim|fiber|fibre\" .lake/packages/mathlib/Mathlib/RingTheory .lake/packages/mathlib/Mathlib/FieldTheory -S" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean
./route-choice-answer.md:5485:.lake/packages/mathlib/Mathlib/RingTheory/EssentialFiniteness.lean:168:instance EssFiniteType.baseChange [h : EssFiniteType R S] : EssFiniteType T (T ⊗[R] S) := by
./route-choice-answer.md:5852:.lake/packages/mathlib/Mathlib/Geometry/Euclidean/Sphere/OrthRadius.lean:183:attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two
./route-choice-answer.md:5853:.lake/packages/mathlib/Mathlib/Geometry/Euclidean/Sphere/OrthRadius.lean:233:  have : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ hf
./route-choice-answer.md:5855:.lake/packages/mathlib/Mathlib/Geometry/Euclidean/Sphere/Basic.lean:496:theorem eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two [FiniteDimensional ℝ V]
./route-choice-answer.md:5857:.lake/packages/mathlib/Mathlib/Geometry/Euclidean/Sphere/Tangent.lean:140:  have : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ hfr.symm
./route-choice-answer.md:5860:.lake/packages/mathlib/Mathlib/Geometry/Euclidean/Angle/Incenter.lean:83:attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two
./route-choice-answer.md:5879:.lake/packages/mathlib/Mathlib/Geometry/Euclidean/Angle/Bisector.lean:114:attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two
./route-choice-answer.md:5889:.lake/packages/mathlib/Mathlib/Geometry/Euclidean/Angle/Sphere.lean:117:  haveI : FiniteDimensional ℝ V := .of_finrank_eq_succ (Fact.out : finrank ℝ V = 2)
./route-choice-answer.md:5913:.lake/packages/mathlib/Mathlib/Geometry/Euclidean/Basic.lean:176:theorem eq_of_dist_eq_of_dist_eq_of_finrank_eq_two [FiniteDimensional ℝ V] (hd : finrank ℝ V = 2)
./route-choice-answer.md:6406:.lake/packages/mathlib/Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Topology.lean:154:theorem homogeneousIdeal_le_vanishingIdeal_zeroLocus (I : HomogeneousIdeal 𝒜) :
./route-choice-answer.md:7383:.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean:414:theorem FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
./route-choice-answer.md:7384:.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean:420:theorem FiniteDimensional.nonempty_continuousLinearEquiv_iff_finrank_eq :
./route-choice-answer.md:7385:.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean:423:    FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq h⟩
./route-choice-answer.md:7459:.lake/packages/mathlib/Mathlib/Topology/Compactification/OnePoint/Sphere.lean:46:  letI e : V ≃ₜ (ℝ ∙ v)ᗮ := (FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq hV).some
./route-choice-answer.md:7469:/bin/bash -lc 'rg -n "trdeg_add_eq|transcendenceDegree|TranscendenceDegree|trdeg|algebraicIndependent.*trdeg|ringKrullDim_.*trdeg|.*trdeg.*ringKrullDim" .lake/packages/mathlib/Mathlib -S' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean
./route-choice-answer.md:7513:DLNFibre/Core/OrbitPullbackDim.lean:6:# `DLNFibre.Core.OrbitPullbackDim` — route-c setup: `varietyDim(Z_M) = ringKrullDim((μ_M^*).range)`
./route-choice-answer.md:7517:DLNFibre/Core/OrbitImageDim.lean:16:- **A4.1** (landed, `ringKrullDim_range_orbitPullback_unbotD_eq_trdeg_toNat`):
./route-choice-answer.md:7518:DLNFibre/Core/OrbitImageDim.lean:17:  `(ringKrullDim (orbitPullback M).range).unbotD 0 = (Algebra.trdeg k (orbitPullback M).range).toNat`.
./route-choice-answer.md:7525:DLNFibre/Core/OrbitImageDim.lean:77:the A4.3 identity is needed (the chain is `varietyDim = trdeg ≤ genericDifferentialRank ≤ finrank δ⁰`);
./route-choice-answer.md:7527:DLNFibre/Core/OrbitImageDim.lean:87:  rw [ringKrullDim_range_orbitPullback_unbotD_eq_trdeg_toNat M]
./route-choice-answer.md:7552:DLNFibre/Core/DeepChartRing.lean:325:/-! ## R2-3b-2 — the `SchurLoc`-algebra structure on `Sred` and the scalar tower
./route-choice-answer.md:7553:DLNFibre/Core/DeepChartRing.lean:328:structure on `Sred`, with `k → SchurLoc → Sred` a scalar tower. These instances are the
./route-choice-answer.md:7554:DLNFibre/Core/DeepChartRing.lean:339:tower: `algebraMap k Sred` factors through `algebraMap k (SchurLoc …)` (both `schurToSred` and the
./route-choice-answer.md:7557:DLNFibre/Core/AffineNoetherRank.lean:7:# `DLNFibre.Core.AffineNoetherRank` — A4.1: `ringKrullDim = trdeg` for the pullback image
./route-choice-answer.md:7558:DLNFibre/Core/AffineNoetherRank.lean:12:> `(ringKrullDim (orbitPullback M).range).unbotD 0 = (Algebra.trdeg k (orbitPullback M).range).toNat`.
./route-choice-answer.md:7559:DLNFibre/Core/AffineNoetherRank.lean:16:`ringKrullDim (R ⧸ p) = s`, and that same integral injective map forces `trdeg = s` (the quotient is
./route-choice-answer.md:7562:DLNFibre/Core/AffineNoetherRank.lean:20:(`renameEquiv`), so both invariants transport (`ringKrullDim_eq_of_ringEquiv`, `AlgEquiv.trdeg_eq`).
./route-choice-answer.md:7573:DLNFibre/Core/AffineNoetherRank.lean:59:Noether-normalization rank `s`, hence agree: `(ringKrullDim (R ⧸ p)).unbotD 0 = (trdeg k (R ⧸ p)).toNat`.
./route-choice-answer.md:7574:DLNFibre/Core/AffineNoetherRank.lean:61:`k[Fin s] →ₐ (R ⧸ p)` and `ringKrullDim = s`; `trdeg_eq_of_integral_injective` gives `trdeg = s`. -/
./route-choice-answer.md:7575:DLNFibre/Core/AffineNoetherRank.lean:62:theorem ringKrullDim_quotient_unbotD_eq_trdeg_toNat (n : ℕ)
./route-choice-answer.md:7579:DLNFibre/Core/AffineNoetherRank.lean:76:`(ringKrullDim (orbitPullback M).range).unbotD 0 = (Algebra.trdeg k (orbitPullback M).range).toNat`.
./route-choice-answer.md:7580:DLNFibre/Core/AffineNoetherRank.lean:79:`k[Fin n]`; then `ringKrullDim_quotient_unbotD_eq_trdeg_toNat` applies, transported back through
./route-choice-answer.md:7581:DLNFibre/Core/AffineNoetherRank.lean:80:`ringKrullDim_eq_of_ringEquiv` and `AlgEquiv.trdeg_eq`. Char-free. -/
./route-choice-answer.md:7582:DLNFibre/Core/AffineNoetherRank.lean:81:theorem ringKrullDim_range_orbitPullback_unbotD_eq_trdeg_toNat {d : Fin (N + 1) → ℕ}
./route-choice-answer.md:7584:DLNFibre/Core/AffineNoetherRank.lean:104:  rw [ringKrullDim_eq_of_ringEquiv Ψ.toRingEquiv, AlgEquiv.trdeg_eq Ψ,
./route-choice-answer.md:7585:DLNFibre/Core/AffineNoetherRank.lean:105:    ringKrullDim_quotient_unbotD_eq_trdeg_toNat n p]
./route-choice-answer.md:7705:DLNFibre/Core/RouteCAssembly.lean:17:identity `varietyDim Σ^r = δ + varietyDim F` (`hSweep`) — and the Cited closure/density bridge
./route-choice-answer.md:7708:DLNFibre/Core/RouteCAssembly.lean:50:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./route-choice-answer.md:7711:DLNFibre/Core/RouteCAssembly.lean:107:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./route-choice-answer.md:7718:DLNFibre/Core/FibreDimFibrationProbe.lean:93:/-! ## Candidate: the base ringKrullDim = δ (the brick the going-down/00OM route consumes)
./route-choice-answer.md:7721:DLNFibre/Core/SmoothPointRegular.lean:6:dimension bridge (`ringKrullDim R = n` via the étale-over-affine route, *non-circular*); the cotangent
./route-choice-answer.md:7731:DLNFibre/Core/SmoothPointRegular.lean:197:relative dimension `n = ringKrullDim (AtPrime m)`. -/
./route-choice-answer.md:7871:`canonicalCoord '' (mult⁻¹ B) ⊆ canonicalCoord '' Σ̄^r`; `vanishingIdeal` is order-reversing and
./route-choice-answer.md:7889:least that of any superset: a larger set has a smaller vanishing ideal (`vanishingIdeal_anti_mono`),
./route-choice-answer.md:7895:  exact MvPolynomial.vanishingIdeal_anti_mono (Set.image_mono h)
./route-choice-answer.md:7954:telescope away in `mult`), `mult` is `H`-equivariant (`FibreNormalForm.mult_smul`), and any two rank-`r`
./route-choice-answer.md:7955:matrices are `H`-equivalent (`exists_baseChange_of_rank_eq`). Hence the **exact-rank locus is one
./route-choice-answer.md:7961:consequence** `varietyDim (productRankLocus d r) = δ + varietyDim (fibre d E)` is the *one genuinely
./route-choice-answer.md:7983:theorem isUnit_det_baseChangeGroup (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := k) d)
./route-choice-answer.md:7994:        (isUnit_det_baseChangeGroup d P (Fin.last N)),
./route-choice-answer.md:7996:        (by simpa using isUnit_det_baseChangeGroup d P⁻¹ 0)]
./route-choice-answer.md:8007:(`rank_endpoint_conj`). `(→)` `rank(mult A) = r = E.rank`, so `exists_baseChange_of_rank_eq` gives `P`
./route-choice-answer.md:8018:    obtain ⟨P, hP⟩ := exists_baseChange_of_rank_eq d hN E (mult d A) (by rw [hE, hA])
./route-choice-answer.md:8037:E` is `fibre d (P_N·E·P_0⁻¹)`, a rank-`r` fibre; `G1` (`codimRepCanonical_fibre_eq_of_rank_eq`, the
./route-choice-answer.md:8046:  codimRepCanonical_fibre_eq_of_rank_eq d hN _ E (rank_endpoint_conj d P E)
./route-choice-answer.md:8071:function on `Tuple d`, with codim read through `vanishingIdeal`/`Ideal.height`; no `Spec`, no
./route-choice-answer.md:8186:`vanishingIdeal`s — so the Schur section cannot be exhibited as an `AlgEquiv` without first building
./route-choice-answer.md:8250:the trivializing `AlgEquiv` from the engine's opaque `vanishingIdeal`-quotients, not the closer. -/
./route-choice-answer.md:8286:identity `varietyDim Σ^r = δ + varietyDim F` (`hSweep`) — and the Cited closure/density bridge
./route-choice-answer.md:8287:`varietyDim Σ^r = varietyDim Σ̄^r` (`hClosure`, Lehalleur–Rimányi 4.4/4.5) are carried as **explicit
./route-choice-answer.md:8289:relations `codimRepCanonical Z + varietyDim Z = card` are carried as named hypotheses
./route-choice-answer.md:8319:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./route-choice-answer.md:8321:          + varietyDim (canonicalCoord d '' fibre d B))
./route-choice-answer.md:8322:    (hClosure : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./route-choice-answer.md:8323:        = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r))
./route-choice-answer.md:8325:        + varietyDim (canonicalCoord d '' fibre d B) = (Nat.card (RepCoord d) : ℕ∞))
./route-choice-answer.md:8327:        + varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
./route-choice-answer.md:8336:  have hdimSigma : varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
./route-choice-answer.md:8338:        + varietyDim (canonicalCoord d '' fibre d B) := by
./route-choice-answer.md:8341:  have hdimF_ne : varietyDim (canonicalCoord d '' fibre d B) ≠ ⊤ := by
./route-choice-answer.md:8348:  have key : varietyDim (canonicalCoord d '' fibre d B) + codimRepCanonical (fibre d B)
./route-choice-answer.md:8349:      = varietyDim (canonicalCoord d '' fibre d B)
./route-choice-answer.md:8351:    calc varietyDim (canonicalCoord d '' fibre d B) + codimRepCanonical (fibre d B)
./route-choice-answer.md:8352:        = codimRepCanonical (fibre d B) + varietyDim (canonicalCoord d '' fibre d B) := by
./route-choice-answer.md:8357:              + varietyDim (canonicalCoord d '' fibre d B)) := hCatSigma.symm
./route-choice-answer.md:8358:      _ = varietyDim (canonicalCoord d '' fibre d B)
./route-choice-answer.md:8369:`codimRepCanonical_add_varietyDim_eq_card_of_nonempty` (`Core.RadicalCatenary`), given that the
./route-choice-answer.md:8376:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./route-choice-answer.md:8378:          + varietyDim (canonicalCoord d '' fibre d B))
./route-choice-answer.md:8379:    (hClosure : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./route-choice-answer.md:8380:        = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)) :
./route-choice-answer.md:8384:    (codimRepCanonical_add_varietyDim_eq_card_of_nonempty hFne)
./route-choice-answer.md:8385:    (codimRepCanonical_add_varietyDim_eq_card_of_nonempty hSigmaNe)
./route-choice-answer.md:8482:`Core.FibreNormalForm.codimRepCanonical_fibre_eq_of_rank_eq` (LANDED, flatness-free, via the GL×GL
./route-choice-answer.md:8490:closer gives `codim(fibre B*) = v`; G1 (`codimRepCanonical_fibre_eq_of_rank_eq`) transports it. -/
./route-choice-answer.md:8498:  rw [codimRepCanonical_fibre_eq_of_rank_eq d hN B Bstar (by rw [hB, hBstar])]
./route-choice-answer.md:8512:# `DLNFibre.Core.AffineNoetherRank` — A4.1: `ringKrullDim = trdeg` for the pullback image
./route-choice-answer.md:8517:> `(ringKrullDim (orbitPullback M).range).unbotD 0 = (Algebra.trdeg k (orbitPullback M).range).toNat`.
./route-choice-answer.md:8520:`ringKrullDim_quotient_eq_noetherRank` produces an integral injective `k[Fin s] →ₐ (R ⧸ p)` with
./route-choice-answer.md:8521:`ringKrullDim (R ⧸ p) = s`, and that same integral injective map forces `trdeg = s` (the quotient is
./route-choice-answer.md:8525:(`renameEquiv`), so both invariants transport (`ringKrullDim_eq_of_ringEquiv`, `AlgEquiv.trdeg_eq`).
./route-choice-answer.md:8564:Noether-normalization rank `s`, hence agree: `(ringKrullDim (R ⧸ p)).unbotD 0 = (trdeg k (R ⧸ p)).toNat`.
./route-choice-answer.md:8565:The Noether engine (`ringKrullDim_quotient_eq_noetherRank`) supplies the integral injective
./route-choice-answer.md:8566:`k[Fin s] →ₐ (R ⧸ p)` and `ringKrullDim = s`; `trdeg_eq_of_integral_injective` gives `trdeg = s`. -/
./route-choice-answer.md:8567:theorem ringKrullDim_quotient_unbotD_eq_trdeg_toNat (n : ℕ)
./route-choice-answer.md:8569:    (ringKrullDim (MvPolynomial (Fin n) k ⧸ p)).unbotD 0
./route-choice-answer.md:8571:  obtain ⟨s, _, ⟨g, hg_inj, hg_int⟩, hdim⟩ := ringKrullDim_quotient_eq_noetherRank k n p
./route-choice-answer.md:8581:`(ringKrullDim (orbitPullback M).range).unbotD 0 = (Algebra.trdeg k (orbitPullback M).range).toNat`.
./route-choice-answer.md:8584:`k[Fin n]`; then `ringKrullDim_quotient_unbotD_eq_trdeg_toNat` applies, transported back through
./route-choice-answer.md:8585:`ringKrullDim_eq_of_ringEquiv` and `AlgEquiv.trdeg_eq`. Char-free. -/
./route-choice-answer.md:8586:theorem ringKrullDim_range_orbitPullback_unbotD_eq_trdeg_toNat {d : Fin (N + 1) → ℕ}
./route-choice-answer.md:8588:    (ringKrullDim (orbitPullback M).range).unbotD 0
./route-choice-answer.md:8609:  rw [ringKrullDim_eq_of_ringEquiv Ψ.toRingEquiv, AlgEquiv.trdeg_eq Ψ,
./route-choice-answer.md:8610:    ringKrullDim_quotient_unbotD_eq_trdeg_toNat n p]
./route-choice-answer.md:8628:`height_add_ringKrullDim_quotient_eq` (L5, `Core.NoetherMonicPositioning`) to a finite-type domain
./route-choice-answer.md:8631:* `affine_domain_height_add_ringKrullDim_quotient_eq` :
./route-choice-answer.md:8632:    `Ideal.height p + ringKrullDim (A ⧸ p) = ringKrullDim A`  (equidimensionality).
./route-choice-answer.md:8634:* `height_eq_ringKrullDim_of_isMaximal` : for `m` maximal, `Ideal.height m = ringKrullDim A`
./route-choice-answer.md:8637:* `ringKrullDim_localizationAtPrime_isMaximal_eq` : for `m` maximal,
./route-choice-answer.md:8638:  `ringKrullDim (Localization.AtPrime m) = ringKrullDim A` (local ↔ global dimension at a closed
./route-choice-answer.md:8722:`Ideal.height p + ringKrullDim (A ⧸ p) = ringKrullDim A`. Proved by Noether-normalizing `A`,
./route-choice-answer.md:8725:theorem affine_domain_height_add_ringKrullDim_quotient_eq
./route-choice-answer.md:8728:    (p.height : WithBot ℕ∞) + ringKrullDim (((MvPolynomial (Fin n) k) ⧸ I) ⧸ p)
./route-choice-answer.md:8729:      = ringKrullDim ((MvPolynomial (Fin n) k) ⧸ I) := by
./route-choice-answer.md:8741:  have hdimA : ringKrullDim A = (s : WithBot ℕ∞) := by
./route-choice-answer.md:8742:    rw [ringKrullDim_eq_of_integral_injective (f := g.toRingHom) hg_int hg_inj,
./route-choice-answer.md:8743:      ringKrullDim_mvPolynomial_fin_field]
./route-choice-answer.md:8755:  have hdimQuot : ringKrullDim (A ⧸ p) = ringKrullDim (B ⧸ q) := by
./route-choice-answer.md:8756:    have h := ringKrullDim_eq_of_integral_injective
./route-choice-answer.md:8761:  have hL5 : (q.height : WithBot ℕ∞) + ringKrullDim (B ⧸ q) = (s : WithBot ℕ∞) :=
./route-choice-answer.md:8762:    height_add_ringKrullDim_quotient_eq k s q
./route-choice-answer.md:8769:`m` a maximal ideal of `A`, `Ideal.height m = ringKrullDim A` (`A ⧸ m` a field, dimension `0`). -/
./route-choice-answer.md:8770:theorem height_eq_ringKrullDim_of_isMaximal
./route-choice-answer.md:8773:    (m.height : WithBot ℕ∞) = ringKrullDim ((MvPolynomial (Fin n) k) ⧸ I) := by
./route-choice-answer.md:8777:  have h := affine_domain_height_add_ringKrullDim_quotient_eq k n I m
./route-choice-answer.md:8778:  rw [ringKrullDim_eq_zero_of_isField hfield, add_zero] at h
./route-choice-answer.md:8783:`ringKrullDim A`. Feeds the smooth ⟹ regular bridge (L4a). -/
./route-choice-answer.md:8784:theorem ringKrullDim_localizationAtPrime_isMaximal_eq
./route-choice-answer.md:8787:    ringKrullDim (Localization.AtPrime m) = ringKrullDim ((MvPolynomial (Fin n) k) ⧸ I) := by
./route-choice-answer.md:8789:  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m)]
./route-choice-answer.md:8790:  exact height_eq_ringKrullDim_of_isMaximal k n I m
./route-choice-answer.md:8806:      + ringKrullDim (((MvPolynomial (Fin 1) ℚ) ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ))) ⧸
./route-choice-answer.md:8808:      = ringKrullDim ((MvPolynomial (Fin 1) ℚ) ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ))) :=
./route-choice-answer.md:8809:  affine_domain_height_add_ringKrullDim_quotient_eq ℚ 1 ⊥ ⊥
./route-choice-answer.md:8815:    ringKrullDim (Localization.AtPrime m)
./route-choice-answer.md:8816:      = ringKrullDim ((MvPolynomial (Fin 1) ℚ) ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ))) :=
./route-choice-answer.md:8817:  ringKrullDim_localizationAtPrime_isMaximal_eq ℚ 1 ⊥ m
./route-choice-answer.md:8835:`Σ^r` and `F` are not domains in the examples you care about. Your `varietyDim` is `ringKrullDim` of a possibly reducible coordinate ring, hence a **max over components**, while `trdeg_add_eq` is a domain/no-zero-divisors function-field theorem.
./route-choice-answer.md:8843:It does not identify `relative_trdeg` with `varietyDim F_B` at your chosen closed rank-`r` point. The missing input is the no-jump/local-triviality statement:
./route-choice-answer.md:8868:bridge from flat ring maps to set-level varietyDim/fibre ideals
./route-choice-answer.md:8873:The set-level `varietyDim` bridge is not free. `multComap` gives the ring map shape, but exact-rank geometry wants localized quotient rings/pivot charts, not just the global closure ring where lower-rank fibres jump.
./route-choice-answer.md:8899:6. finite-cover/localization gluing for set-level varietyDim
./route-choice-answer.md:8922:`Σ^r` and `F` are not domains in the examples you care about. Your `varietyDim` is `ringKrullDim` of a possibly reducible coordinate ring, hence a **max over components**, while `trdeg_add_eq` is a domain/no-zero-divisors function-field theorem.
./route-choice-answer.md:8930:It does not identify `relative_trdeg` with `varietyDim F_B` at your chosen closed rank-`r` point. The missing input is the no-jump/local-triviality statement:
./route-choice-answer.md:8955:bridge from flat ring maps to set-level varietyDim/fibre ideals
./route-choice-answer.md:8960:The set-level `varietyDim` bridge is not free. `multComap` gives the ring map shape, but exact-rank geometry wants localized quotient rings/pivot charts, not just the global closure ring where lower-rank fibres jump.
./route-choice-answer.md:8986:6. finite-cover/localization gluing for set-level varietyDim
./noncirc-setlevel-answer.md:19:`hSweep : varietyDim Σ^r = δ + varietyDim F`. Rung 1 = a single-chart trivialization. The DECISIVE
./noncirc-setlevel-answer.md:20:de-risk: is the SET-LEVEL / `varietyDim` version non-circular, given a PRIOR attempt (R2-3b-4) at a
./noncirc-setlevel-answer.md:38:For `hSweep` I do NOT need reducedness. `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`
./noncirc-setlevel-answer.md:39:and `vanishingIdeal Z` is ALREADY radical (it's a vanishing ideal). Krull dim is RADICAL-INSENSITIVE:
./noncirc-setlevel-answer.md:40:`ringKrullDim (R⧸I) = ringKrullDim (R⧸√I)`. So `varietyDim` reads only the REDUCED/variety structure;
./noncirc-setlevel-answer.md:51:1. **Is `varietyDim` genuinely radical-insensitive in Mathlib v4.29** — i.e. is `ringKrullDim (R⧸I) =
./noncirc-setlevel-answer.md:52:   ringKrullDim (R⧸ I.radical)` available (or `ringKrullDim` factors through `√`)? Name the lemma if
./noncirc-setlevel-answer.md:58:   chart's normalizing gauge. This is a bijection of SETS / a `varietyDim`-preserving map. Does
./noncirc-setlevel-answer.md:63:   `varietyDim(U×F) = varietyDim U + varietyDim F` secretly needs flatness/reducedness.
./noncirc-setlevel-answer.md:65:3. **The product-dimension step `varietyDim(U × F) = varietyDim U + varietyDim F`.** For a product of
./noncirc-setlevel-answer.md:67:   (as `ringKrullDim (A ⊗_k B) = ringKrullDim A + ringKrullDim B`, or a variety-dimension product)?
./noncirc-setlevel-answer.md:73:4. **The glue over the finite pivot cover.** `varietyDim(⋃_i Z_i) = max_i varietyDim(Z_i)` for a
./noncirc-setlevel-answer.md:74:   finite cover — is that radical-insensitive and in Mathlib (or trivial from `ringKrullDim` of a
./noncirc-setlevel-answer.md:77:5. **Net verdict:** does the SET-LEVEL/`varietyDim` route (c) dodge the R2-3b-4 circularity? If YES,
./noncirc-setlevel-answer.md:82:The key thing I need from you: a clean YES/NO on whether radical-insensitivity of `varietyDim` lets
./noncirc-setlevel-answer.md:93:/bin/bash -lc "rg -n \"varietyDim|ringKrullDim|radical|IsJacobson|KrullDim|tensor|TensorProduct\" . -g '*.lean' -g '*.md' | head -300" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
./noncirc-setlevel-answer.md:95:./route-choice-prompt.md:10:varietyDim (Σ^r)  =  δ  +  varietyDim F
./noncirc-setlevel-answer.md:96:./route-choice-prompt.md:13:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./noncirc-setlevel-answer.md:97:./route-choice-prompt.md:18:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./noncirc-setlevel-answer.md:98:./route-choice-prompt.md:28:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./noncirc-setlevel-answer.md:99:./route-choice-prompt.md:29:   ringKrullDim (R ⧸ ker(pullback)) = ringKrullDim((pullback).range) = trdeg_k(range)` for a
./noncirc-setlevel-answer.md:100:./route-choice-prompt.md:31:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./noncirc-setlevel-answer.md:101:./route-choice-prompt.md:52:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./noncirc-setlevel-answer.md:102:./route-choice-prompt.md:60:max component, i.e. `ringKrullDim`)? Is `ringKrullDim`-additivity over a sweep even true without
./noncirc-setlevel-answer.md:103:./route-choice-prompt.md:73:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./noncirc-setlevel-answer.md:104:./route-choice-prompt.md:75:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./noncirc-setlevel-answer.md:105:./noncirc-setlevel-prompt.md:4:`hSweep : varietyDim Σ^r = δ + varietyDim F`. Rung 1 = a single-chart trivialization. The DECISIVE
./noncirc-setlevel-answer.md:106:./noncirc-setlevel-prompt.md:5:de-risk: is the SET-LEVEL / `varietyDim` version non-circular, given a PRIOR attempt (R2-3b-4) at a
./noncirc-setlevel-answer.md:108:./noncirc-setlevel-prompt.md:23:For `hSweep` I do NOT need reducedness. `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`
./noncirc-setlevel-answer.md:109:./noncirc-setlevel-prompt.md:24:and `vanishingIdeal Z` is ALREADY radical (it's a vanishing ideal). Krull dim is RADICAL-INSENSITIVE:
./noncirc-setlevel-answer.md:110:./noncirc-setlevel-prompt.md:25:`ringKrullDim (R⧸I) = ringKrullDim (R⧸√I)`. So `varietyDim` reads only the REDUCED/variety structure;
./noncirc-setlevel-answer.md:112:./noncirc-setlevel-prompt.md:36:1. **Is `varietyDim` genuinely radical-insensitive in Mathlib v4.29** — i.e. is `ringKrullDim (R⧸I) =
./noncirc-setlevel-answer.md:113:./noncirc-setlevel-prompt.md:37:   ringKrullDim (R⧸ I.radical)` available (or `ringKrullDim` factors through `√`)? Name the lemma if
./noncirc-setlevel-answer.md:114:./noncirc-setlevel-prompt.md:43:   chart's normalizing gauge. This is a bijection of SETS / a `varietyDim`-preserving map. Does
./noncirc-setlevel-answer.md:117:./noncirc-setlevel-prompt.md:48:   `varietyDim(U×F) = varietyDim U + varietyDim F` secretly needs flatness/reducedness.
./noncirc-setlevel-answer.md:118:./noncirc-setlevel-prompt.md:50:3. **The product-dimension step `varietyDim(U × F) = varietyDim U + varietyDim F`.** For a product of
./noncirc-setlevel-answer.md:119:./noncirc-setlevel-prompt.md:52:   (as `ringKrullDim (A ⊗_k B) = ringKrullDim A + ringKrullDim B`, or a variety-dimension product)?
./noncirc-setlevel-answer.md:122:./noncirc-setlevel-prompt.md:58:4. **The glue over the finite pivot cover.** `varietyDim(⋃_i Z_i) = max_i varietyDim(Z_i)` for a
./noncirc-setlevel-answer.md:123:./noncirc-setlevel-prompt.md:59:   finite cover — is that radical-insensitive and in Mathlib (or trivial from `ringKrullDim` of a
./noncirc-setlevel-answer.md:124:./noncirc-setlevel-prompt.md:62:5. **Net verdict:** does the SET-LEVEL/`varietyDim` route (c) dodge the R2-3b-4 circularity? If YES,
./noncirc-setlevel-answer.md:126:./noncirc-setlevel-prompt.md:67:The key thing I need from you: a clean YES/NO on whether radical-insensitivity of `varietyDim` lets
./noncirc-setlevel-answer.md:127:./noncirc-setlevel-answer.md:19:`hSweep : varietyDim Σ^r = δ + varietyDim F`. Rung 1 = a single-chart trivialization. The DECISIVE
./noncirc-setlevel-answer.md:128:./noncirc-setlevel-answer.md:20:de-risk: is the SET-LEVEL / `varietyDim` version non-circular, given a PRIOR attempt (R2-3b-4) at a
./noncirc-setlevel-answer.md:130:./noncirc-setlevel-answer.md:38:For `hSweep` I do NOT need reducedness. `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`
./noncirc-setlevel-answer.md:131:./noncirc-setlevel-answer.md:39:and `vanishingIdeal Z` is ALREADY radical (it's a vanishing ideal). Krull dim is RADICAL-INSENSITIVE:
./noncirc-setlevel-answer.md:132:./noncirc-setlevel-answer.md:40:`ringKrullDim (R⧸I) = ringKrullDim (R⧸√I)`. So `varietyDim` reads only the REDUCED/variety structure;
./noncirc-setlevel-answer.md:134:./noncirc-setlevel-answer.md:51:1. **Is `varietyDim` genuinely radical-insensitive in Mathlib v4.29** — i.e. is `ringKrullDim (R⧸I) =
./noncirc-setlevel-answer.md:135:./noncirc-setlevel-answer.md:52:   ringKrullDim (R⧸ I.radical)` available (or `ringKrullDim` factors through `√`)? Name the lemma if
./noncirc-setlevel-answer.md:136:./noncirc-setlevel-answer.md:58:   chart's normalizing gauge. This is a bijection of SETS / a `varietyDim`-preserving map. Does
./noncirc-setlevel-answer.md:139:./noncirc-setlevel-answer.md:63:   `varietyDim(U×F) = varietyDim U + varietyDim F` secretly needs flatness/reducedness.
./noncirc-setlevel-answer.md:140:./noncirc-setlevel-answer.md:65:3. **The product-dimension step `varietyDim(U × F) = varietyDim U + varietyDim F`.** For a product of
./noncirc-setlevel-answer.md:141:./noncirc-setlevel-answer.md:67:   (as `ringKrullDim (A ⊗_k B) = ringKrullDim A + ringKrullDim B`, or a variety-dimension product)?
./noncirc-setlevel-answer.md:144:./noncirc-setlevel-answer.md:73:4. **The glue over the finite pivot cover.** `varietyDim(⋃_i Z_i) = max_i varietyDim(Z_i)` for a
./noncirc-setlevel-answer.md:145:./noncirc-setlevel-answer.md:74:   finite cover — is that radical-insensitive and in Mathlib (or trivial from `ringKrullDim` of a
./noncirc-setlevel-answer.md:146:./noncirc-setlevel-answer.md:77:5. **Net verdict:** does the SET-LEVEL/`varietyDim` route (c) dodge the R2-3b-4 circularity? If YES,
./noncirc-setlevel-answer.md:148:./noncirc-setlevel-answer.md:82:The key thing I need from you: a clean YES/NO on whether radical-insensitivity of `varietyDim` lets
./noncirc-setlevel-answer.md:149:./route-choice-answer.md:25:varietyDim (Σ^r)  =  δ  +  varietyDim F
./noncirc-setlevel-answer.md:150:./route-choice-answer.md:28:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./noncirc-setlevel-answer.md:151:./route-choice-answer.md:33:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./noncirc-setlevel-answer.md:152:./route-choice-answer.md:43:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./noncirc-setlevel-answer.md:153:./route-choice-answer.md:44:   ringKrullDim (R ⧸ ker(pullback)) = ringKrullDim((pullback).range) = trdeg_k(range)` for a
./noncirc-setlevel-answer.md:154:./route-choice-answer.md:46:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./noncirc-setlevel-answer.md:155:./route-choice-answer.md:67:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./noncirc-setlevel-answer.md:156:./route-choice-answer.md:75:max component, i.e. `ringKrullDim`)? Is `ringKrullDim`-additivity over a sweep even true without
./noncirc-setlevel-answer.md:157:./route-choice-answer.md:88:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./noncirc-setlevel-answer.md:158:./route-choice-answer.md:90:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./noncirc-setlevel-answer.md:159:./route-choice-answer.md:114:./route-choice-prompt.md:31:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./noncirc-setlevel-answer.md:160:./route-choice-answer.md:129:./route-choice-answer.md:46:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./noncirc-setlevel-answer.md:161:./route-choice-answer.md:188:varietyDim (Σ^r)  =  δ  +  varietyDim F
./noncirc-setlevel-answer.md:162:./route-choice-answer.md:191:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./noncirc-setlevel-answer.md:163:./route-choice-answer.md:196:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./noncirc-setlevel-answer.md:164:./route-choice-answer.md:206:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./noncirc-setlevel-answer.md:165:./route-choice-answer.md:207:   ringKrullDim (R ⧸ ker(pullback)) = ringKrullDim((pullback).range) = trdeg_k(range)` for a
./noncirc-setlevel-answer.md:166:./route-choice-answer.md:209:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./noncirc-setlevel-answer.md:167:./route-choice-answer.md:230:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./noncirc-setlevel-answer.md:168:./route-choice-answer.md:238:max component, i.e. `ringKrullDim`)? Is `ringKrullDim`-additivity over a sweep even true without
./noncirc-setlevel-answer.md:169:./route-choice-answer.md:251:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./noncirc-setlevel-answer.md:170:./route-choice-answer.md:253:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./noncirc-setlevel-answer.md:171:./route-choice-answer.md:277:./route-choice-prompt.md:31:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./noncirc-setlevel-answer.md:172:./route-choice-answer.md:292:./route-choice-answer.md:46:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./noncirc-setlevel-answer.md:173:./route-choice-answer.md:325:/bin/bash -lc 'rg -n "Noether.*Norm|Noetherian.*Norm|normalization|GenericFreeness|generic freeness|height_eq_under|FlatQuasiFinite|HasGoingDown|trdeg_add_eq|rankLocus|productRankLocus|varietyDim|vanishingIdeal" -S .' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean
./noncirc-setlevel-answer.md:174:./route-choice-answer.md:450:./DLNFibre.lean:160:-- `codimRepCanonical Z + varietyDim Z = card` for nonempty Z. Discharges the catenary hyps of RouteCAssembly.
./noncirc-setlevel-answer.md:175:./route-choice-answer.md:466:./DLNFibre/Core/OrbitPullbackDim.lean:6:# `DLNFibre.Core.OrbitPullbackDim` — route-c setup: `varietyDim(Z_M) = ringKrullDim((μ_M^*).range)`
./noncirc-setlevel-answer.md:176:./route-choice-answer.md:467:./DLNFibre/Core/OrbitPullbackDim.lean:16:1. **Ideal identification.** `varietyDim Z_M = ringKrullDim (MvPolynomial (RepCoord d) k ⧸
./noncirc-setlevel-answer.md:177:./route-choice-answer.md:468:./DLNFibre/Core/OrbitPullbackDim.lean:17:   ker μ_M^*)`, immediate from the `varietyDim` definition, the Abeasis–Del Fra ideal equality L6.4
./noncirc-setlevel-answer.md:178:./route-choice-answer.md:471:./DLNFibre/Core/OrbitPullbackDim.lean:25:The headline `varietyDim_eq_ringKrullDim_range_orbitPullback` hands A4 a finitely-generated domain
./noncirc-setlevel-answer.md:179:./route-choice-answer.md:472:./DLNFibre/Core/OrbitPullbackDim.lean:48:`MvPolynomial (RepCoord d) k ⧸ ker μ_M^*`. `varietyDim` definition, then L6.4
./noncirc-setlevel-answer.md:180:./route-choice-answer.md:475:./DLNFibre/Core/OrbitPullbackDim.lean:52:theorem varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker [Infinite k]
./noncirc-setlevel-answer.md:181:./route-choice-answer.md:476:./DLNFibre/Core/OrbitPullbackDim.lean:54:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./noncirc-setlevel-answer.md:182:./route-choice-answer.md:477:./DLNFibre/Core/OrbitPullbackDim.lean:57:  rw [varietyDim, vanishingIdeal_orbitRankLocus_eq_orbitSet M, ← range_orbitMap,
./noncirc-setlevel-answer.md:183:./route-choice-answer.md:479:./DLNFibre/Core/OrbitPullbackDim.lean:70:transcendence degree. Combines `varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker` with the
./noncirc-setlevel-answer.md:184:./route-choice-answer.md:480:./DLNFibre/Core/OrbitPullbackDim.lean:74:theorem varietyDim_eq_ringKrullDim_range_orbitPullback [Infinite k] {d : Fin (N + 1) → ℕ}
./noncirc-setlevel-answer.md:185:./route-choice-answer.md:481:./DLNFibre/Core/OrbitPullbackDim.lean:76:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./noncirc-setlevel-answer.md:186:./route-choice-answer.md:482:./DLNFibre/Core/OrbitPullbackDim.lean:78:  rw [varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker M,
./noncirc-setlevel-answer.md:187:./route-choice-answer.md:483:./DLNFibre/Core/OrbitPullbackDim.lean:89:/-- The headline at the concrete `(2,2,2)/ℚ` tuple: `varietyDim (canonicalCoord '' orbitRankLocus
./noncirc-setlevel-answer.md:188:./route-choice-answer.md:484:./DLNFibre/Core/OrbitPullbackDim.lean:93:    varietyDim (canonicalCoord dWitness '' orbitRankLocus tupleWitnessQ)
./noncirc-setlevel-answer.md:189:./route-choice-answer.md:485:./DLNFibre/Core/OrbitPullbackDim.lean:95:  varietyDim_eq_ringKrullDim_range_orbitPullback tupleWitnessQ
./noncirc-setlevel-answer.md:190:./route-choice-answer.md:506:./DLNFibre/Core/DeterminantalStratumDim.lean:29:4. **The catenary bridge** (LANDED `codimRep_add_varietyDim_eq_card`): `codim + dim = card = m·n`,
./noncirc-setlevel-answer.md:191:./route-choice-answer.md:520:./DLNFibre/Core/DeterminantalStratumDim.lean:224:> `varietyDim (Mat^{rk ≤ r}_{m × n}) = r · (n + m − r)`.
./noncirc-setlevel-answer.md:192:./route-choice-answer.md:521:./DLNFibre/Core/DeterminantalStratumDim.lean:229:theorem varietyDim_productRankLocusLE_stratum [IsAlgClosed k] [CharZero k] (n m r : ℕ)
./noncirc-setlevel-answer.md:193:./route-choice-answer.md:522:./DLNFibre/Core/DeterminantalStratumDim.lean:231:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./noncirc-setlevel-answer.md:194:./route-choice-answer.md:524:./DLNFibre/Core/DeterminantalStratumDim.lean:237:  have hbridge := codimRep_add_varietyDim_eq_card (canonicalCoord (dStratum n m)) Z
./noncirc-setlevel-answer.md:195:./route-choice-answer.md:527:./DLNFibre/Core/DeterminantalStratumDim.lean:249:  -- `hbridge : (n−r)(m−r) + varietyDim Z = m·n`
./noncirc-setlevel-answer.md:196:./route-choice-answer.md:528:./DLNFibre/Core/DeterminantalStratumDim.lean:258:  have heq : (((n - r) * (m - r) : ℕ) : ℕ∞) + varietyDim (canonicalCoord (dStratum n m) '' Z)
./noncirc-setlevel-answer.md:197:./route-choice-answer.md:529:./DLNFibre/Core/DeterminantalStratumDim.lean:268:    varietyDim (canonicalCoord (dStratum 2 2) '' productRankLocusLE (k := k) (dStratum 2 2) 1)
./noncirc-setlevel-answer.md:198:./route-choice-answer.md:530:./DLNFibre/Core/DeterminantalStratumDim.lean:270:  have h := varietyDim_productRankLocusLE_stratum (k := k) 2 2 1 (by norm_num) (by norm_num)
./noncirc-setlevel-answer.md:199:./route-choice-answer.md:546:./DLNFibre/Core/DeepChartRing.lean:133:`sigmaIdeal` is radical (`vanishingIdeal_isRadical`, over `[IsAlgClosed k]`) and localization
./noncirc-setlevel-answer.md:200:./route-choice-answer.md:577:./DLNFibre/Core/FibreDimFibration.lean:45:`varietyDim = δ`, lifting the `unbotD 0` to the genuine `WithBot ℕ∞` value (the quotient is
./noncirc-setlevel-answer.md:201:./route-choice-answer.md:578:./DLNFibre/Core/FibreDimFibration.lean:51:The thermometer `varietyDim_productRankLocusLE_stratum` gives the `ℕ∞`-via-`unbotD` value; this lifts
./noncirc-setlevel-answer.md:202:./route-choice-answer.md:579:./DLNFibre/Core/FibreDimFibration.lean:54:theorem ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta [IsAlgClosed k] [CharZero k]
./noncirc-setlevel-answer.md:203:./route-choice-answer.md:585:./DLNFibre/Core/FibreDimFibration.lean:64:  -- the thermometer: `varietyDim = δ`, i.e. `(ringKrullDim (R ⧸ I)).unbotD 0 = δ`.
./noncirc-setlevel-answer.md:204:./route-choice-answer.md:586:./DLNFibre/Core/FibreDimFibration.lean:65:  have hvd : varietyDim (canonicalCoord (dStratum n m) ''
./noncirc-setlevel-answer.md:205:./route-choice-answer.md:588:./DLNFibre/Core/FibreDimFibration.lean:67:    varietyDim_productRankLocusLE_stratum n m r hn hm
./noncirc-setlevel-answer.md:206:./route-choice-answer.md:589:./DLNFibre/Core/FibreDimFibration.lean:68:  rw [varietyDim, ← hI] at hvd
./noncirc-setlevel-answer.md:207:./route-choice-answer.md:597:./DLNFibre/Core/FibreDimFibration.lean:102:    ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta n m r hn hm]
./noncirc-setlevel-answer.md:208:./route-choice-answer.md:605:./DLNFibre/Core/EndBaseChangeSweep.lean:16:consequence** `varietyDim (productRankLocus d r) = δ + varietyDim (fibre d E)` is the *one genuinely
./noncirc-setlevel-answer.md:209:./route-choice-answer.md:637:./DLNFibre/Core/FibreHeightDirect.lean:11:`fibreGenIdeal d B` (`Core.MultComorphism.vanishingIdeal_image_fibre_eq_radical`). The point of this
./noncirc-setlevel-answer.md:210:./route-choice-answer.md:639:./DLNFibre/Core/FibreHeightDirect.lean:47:(definition of `codimRepCanonical`/`codimRep`); `vanishingIdeal (…) = (fibreGenIdeal d B).radical`
./noncirc-setlevel-answer.md:211:./route-choice-answer.md:640:./DLNFibre/Core/FibreHeightDirect.lean:48:(`vanishingIdeal_image_fibre_eq_radical`, the Nullstellensatz); `(radical I).height = I.height`
./noncirc-setlevel-answer.md:212:./route-choice-answer.md:641:./DLNFibre/Core/FibreHeightDirect.lean:54:  rw [codimRepCanonical, codimRep, vanishingIdeal_image_fibre_eq_radical, Ideal.height_radical]
./noncirc-setlevel-answer.md:213:./route-choice-answer.md:643:./DLNFibre/Core/NullstellensatzCodim.lean:20:   Nullstellensatz over `[IsAlgClosed k]`): `vanishingIdeal Z` is always **radical**
./noncirc-setlevel-answer.md:214:./route-choice-answer.md:649:./DLNFibre/Core/NullstellensatzCodim.lean:31:   irreducible"), `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ` (`ℕ∞`, additive — `ℕ∞`
./noncirc-setlevel-answer.md:215:./route-choice-answer.md:650:./DLNFibre/Core/NullstellensatzCodim.lean:37:`axiom`. `varietyDim Z = ringKrullDim (R ⧸ vanishingIdeal Z)` is the Krull dimension of the
./noncirc-setlevel-answer.md:216:./route-choice-answer.md:652:./DLNFibre/Core/NullstellensatzCodim.lean:67:strong Nullstellensatz it equals its own radical, via `vanishingIdeal Z = vanishingIdeal (zeroLocus
./noncirc-setlevel-answer.md:217:./route-choice-answer.md:653:./DLNFibre/Core/NullstellensatzCodim.lean:68:(vanishingIdeal Z))` `= (vanishingIdeal Z).radical`. -/
./noncirc-setlevel-answer.md:218:./route-choice-answer.md:656:./DLNFibre/Core/NullstellensatzCodim.lean:71:  have h : vanishingIdeal k Z = (vanishingIdeal k Z).radical := by
./noncirc-setlevel-answer.md:219:./route-choice-answer.md:658:./DLNFibre/Core/NullstellensatzCodim.lean:74:        vanishingIdeal_zeroLocus_eq_radical (K := k)]
./noncirc-setlevel-answer.md:220:./route-choice-answer.md:664:./DLNFibre/Core/NullstellensatzCodim.lean:87:Nullstellensatz forces `vanishingIdeal (zeroLocus (vanishingIdeal Z)) = (vanishingIdeal Z).radical`,
./noncirc-setlevel-answer.md:221:./route-choice-answer.md:669:./DLNFibre/Core/NullstellensatzCodim.lean:97:    have h3 : vanishingIdeal k (zeroLocus k (vanishingIdeal k Z)) = (vanishingIdeal k Z).radical :=
./noncirc-setlevel-answer.md:222:./route-choice-answer.md:670:./DLNFibre/Core/NullstellensatzCodim.lean:98:      vanishingIdeal_zeroLocus_eq_radical (K := k) _
./noncirc-setlevel-answer.md:223:./route-choice-answer.md:674:./DLNFibre/Core/NullstellensatzCodim.lean:139:noncomputable def varietyDim (Z : Set (σ → k)) : ℕ∞ :=
./noncirc-setlevel-answer.md:224:./route-choice-answer.md:675:./DLNFibre/Core/NullstellensatzCodim.lean:140:  (ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal k Z)).unbotD 0
./noncirc-setlevel-answer.md:225:./route-choice-answer.md:677:./DLNFibre/Core/NullstellensatzCodim.lean:144:the ambient dimension `Nat.card σ`: `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ`. The
./noncirc-setlevel-answer.md:226:./route-choice-answer.md:679:./DLNFibre/Core/NullstellensatzCodim.lean:147:theorem height_vanishingIdeal_add_varietyDim_eq_card [Finite σ] {Z : Set (σ → k)}
./noncirc-setlevel-answer.md:227:./route-choice-answer.md:681:./DLNFibre/Core/NullstellensatzCodim.lean:149:    (vanishingIdeal k Z).height + varietyDim Z = (Nat.card σ : ℕ∞) := by
./noncirc-setlevel-answer.md:228:./route-choice-answer.md:682:./DLNFibre/Core/NullstellensatzCodim.lean:150:  have key := height_add_ringKrullDim_quotient_eq_card (vanishingIdeal k Z)
./noncirc-setlevel-answer.md:229:./route-choice-answer.md:684:./DLNFibre/Core/NullstellensatzCodim.lean:153:  have hne : ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal k Z) ≠ ⊥ :=
./noncirc-setlevel-answer.md:230:./route-choice-answer.md:685:./DLNFibre/Core/NullstellensatzCodim.lean:155:      ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial σ k ⧸ vanishingIdeal k Z)
./noncirc-setlevel-answer.md:231:./route-choice-answer.md:686:./DLNFibre/Core/NullstellensatzCodim.lean:157:  rw [varietyDim, ← hm, WithBot.unbotD_coe]
./noncirc-setlevel-answer.md:232:./route-choice-answer.md:687:./DLNFibre/Core/NullstellensatzCodim.lean:162:`height (vanishingIdeal Z) = Nat.card σ − varietyDim Z` for an irreducible variety `Z` (`ℕ∞`
./noncirc-setlevel-answer.md:233:./route-choice-answer.md:688:./DLNFibre/Core/NullstellensatzCodim.lean:163:subtraction; lossless here since `varietyDim Z ≤ Nat.card σ`). The geometric codimension is the
./noncirc-setlevel-answer.md:234:./route-choice-answer.md:689:./DLNFibre/Core/NullstellensatzCodim.lean:165:theorem height_vanishingIdeal_eq_card_sub_varietyDim [Finite σ] {Z : Set (σ → k)}
./noncirc-setlevel-answer.md:235:./route-choice-answer.md:691:./DLNFibre/Core/NullstellensatzCodim.lean:167:    (vanishingIdeal k Z).height = (Nat.card σ : ℕ∞) - varietyDim Z := by
./noncirc-setlevel-answer.md:236:./route-choice-answer.md:692:./DLNFibre/Core/NullstellensatzCodim.lean:168:  have hadd := height_vanishingIdeal_add_varietyDim_eq_card hp
./noncirc-setlevel-answer.md:237:./route-choice-answer.md:693:./DLNFibre/Core/NullstellensatzCodim.lean:169:  have hne : varietyDim Z ≠ ⊤ := by
./noncirc-setlevel-answer.md:238:./route-choice-answer.md:694:./DLNFibre/Core/NullstellensatzCodim.lean:182:`height_vanishingIdeal_add_varietyDim_eq_card` at `σ := RepCoord d`, `Z := coord '' Z`. -/
./noncirc-setlevel-answer.md:239:./route-choice-answer.md:695:./DLNFibre/Core/NullstellensatzCodim.lean:183:theorem codimRep_add_varietyDim_eq_card [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./noncirc-setlevel-answer.md:240:./route-choice-answer.md:697:./DLNFibre/Core/NullstellensatzCodim.lean:186:    codimRep coord Z + varietyDim (coord '' Z) = (Nat.card (RepCoord d) : ℕ∞) :=
./noncirc-setlevel-answer.md:241:./route-choice-answer.md:698:./DLNFibre/Core/NullstellensatzCodim.lean:187:  height_vanishingIdeal_add_varietyDim_eq_card hp
./noncirc-setlevel-answer.md:242:./route-choice-answer.md:699:./DLNFibre/Core/NullstellensatzCodim.lean:190:varietyDim (coord '' Z)` for an irreducible variety `coord '' Z`: geometric codimension `=` ambient
./noncirc-setlevel-answer.md:243:./route-choice-answer.md:700:./DLNFibre/Core/NullstellensatzCodim.lean:192:theorem codimRep_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./noncirc-setlevel-answer.md:244:./route-choice-answer.md:702:./DLNFibre/Core/NullstellensatzCodim.lean:195:    codimRep coord Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (coord '' Z) :=
./noncirc-setlevel-answer.md:245:./route-choice-answer.md:703:./DLNFibre/Core/NullstellensatzCodim.lean:196:  height_vanishingIdeal_eq_card_sub_varietyDim hp
./noncirc-setlevel-answer.md:246:./route-choice-answer.md:704:./DLNFibre/Core/NullstellensatzCodim.lean:199:`canonicalCoord d`, `codimRepCanonical Z = Nat.card (RepCoord d) − varietyDim (canonicalCoord d ''
./noncirc-setlevel-answer.md:247:./route-choice-answer.md:705:./DLNFibre/Core/NullstellensatzCodim.lean:201:theorem codimRepCanonical_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./noncirc-setlevel-answer.md:248:./route-choice-answer.md:707:./DLNFibre/Core/NullstellensatzCodim.lean:205:    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
./noncirc-setlevel-answer.md:249:./route-choice-answer.md:708:./DLNFibre/Core/NullstellensatzCodim.lean:206:  codimRep_eq_card_sub_varietyDim (canonicalCoord d) Z hp
./noncirc-setlevel-answer.md:250:./route-choice-answer.md:712:./DLNFibre/Core/NullstellensatzCodim.lean:225:alg-closed, `σ` finite), the vanishing ideal is `⊥` (prime), `varietyDim = Nat.card σ`, the bridge
./noncirc-setlevel-answer.md:251:./route-choice-answer.md:714:./DLNFibre/Core/NullstellensatzCodim.lean:230:      + varietyDim (Set.univ : Set (σ → k)) = (Nat.card σ : ℕ∞) := by
./noncirc-setlevel-answer.md:252:./route-choice-answer.md:717:./DLNFibre/Core/NullstellensatzCodim.lean:233:  exact height_vanishingIdeal_add_varietyDim_eq_card this
./noncirc-setlevel-answer.md:253:./route-choice-answer.md:740:./DLNFibre/Core/FibreReducedTrivialization.lean:33:3. **`vanishingIdeal_fibre_eq_fibreGenIdeal_of_trivialization`** — the **radical-collapse** of
./noncirc-setlevel-answer.md:254:./route-choice-answer.md:741:./DLNFibre/Core/FibreReducedTrivialization.lean:34:   `MultComorphism` point 4: with the cut ideal radical, `vanishingIdeal (fibre d B) =
./noncirc-setlevel-answer.md:255:./route-choice-answer.md:744:./DLNFibre/Core/FibreReducedTrivialization.lean:104:a `vanishingIdeal`), the fibre ideal `fibreGenIdeal d B` is **radical**. The certified mechanism:
./noncirc-setlevel-answer.md:256:./route-choice-answer.md:745:./DLNFibre/Core/FibreReducedTrivialization.lean:122:`vanishingIdeal (fibre d B) = radical (fibreGenIdeal d B)` collapses to
./noncirc-setlevel-answer.md:257:./route-choice-answer.md:746:./DLNFibre/Core/FibreReducedTrivialization.lean:123:`vanishingIdeal (fibre d B) = fibreGenIdeal d B`: the `radical (·)` wrapper drops. The clean
./noncirc-setlevel-answer.md:258:./route-choice-answer.md:749:./DLNFibre/Core/FibreReducedTrivialization.lean:132:  rw [vanishingIdeal_image_fibre_eq_radical,
./noncirc-setlevel-answer.md:259:./route-choice-answer.md:813:./DLNFibre/Core/PolynomialDimension.lean:18:* **L5.5** `ringKrullDim_quotient_eq_noetherRank` — `dim (R ⧸ p)` equals the Noether-normalization
./noncirc-setlevel-answer.md:260:./route-choice-answer.md:820:./DLNFibre/Core/OrbitDifferentialRank.lean:35:Krull-dimension bound) and `varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional`
./noncirc-setlevel-answer.md:261:./route-choice-answer.md:821:./DLNFibre/Core/OrbitDifferentialRank.lean:659:/-- **The AG-half submersion bound `varietyDim Z_M ≤ finrank (range δ⁰)`, UNCONDITIONAL (char 0).**
./noncirc-setlevel-answer.md:262:./route-choice-answer.md:822:./DLNFibre/Core/OrbitDifferentialRank.lean:660:Chaining the unconditional A4.4 with the landed A0 link `varietyDim_eq_ringKrullDim_range_orbitPullback`
./noncirc-setlevel-answer.md:263:./route-choice-answer.md:823:./DLNFibre/Core/OrbitDifferentialRank.lean:664:theorem varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional
./noncirc-setlevel-answer.md:264:./route-choice-answer.md:824:./DLNFibre/Core/OrbitDifferentialRank.lean:666:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./noncirc-setlevel-answer.md:265:./route-choice-answer.md:825:./DLNFibre/Core/OrbitDifferentialRank.lean:668:  varietyDim_orbitRankLocus_le_finrank_range_deformationδ M
./noncirc-setlevel-answer.md:266:./route-choice-answer.md:846:./DLNFibre/Core/RadicalCatenary.lean:27:The headline specialises to `codimRepCanonical Z + varietyDim Z = card` for any **nonempty**
./noncirc-setlevel-answer.md:267:./route-choice-answer.md:847:./DLNFibre/Core/RadicalCatenary.lean:157:/-! ## Specialisation to the geometry layer (`codimRepCanonical Z + varietyDim Z = card`) -/
./noncirc-setlevel-answer.md:268:./route-choice-answer.md:852:./DLNFibre/Core/RadicalCatenary.lean:173:/-- **The reducible-locus catenary at `codimRepCanonical`/`varietyDim` (additive, `ℕ∞`).** For a
./noncirc-setlevel-answer.md:269:./route-choice-answer.md:853:./DLNFibre/Core/RadicalCatenary.lean:176:equal the ambient dimension: `codimRepCanonical Z + varietyDim (canonicalCoord d '' Z) = card`. No
./noncirc-setlevel-answer.md:270:./route-choice-answer.md:854:./DLNFibre/Core/RadicalCatenary.lean:179:theorem codimRepCanonical_add_varietyDim_eq_card_of_nonempty {d : Fin (N + 1) → ℕ}
./noncirc-setlevel-answer.md:271:./route-choice-answer.md:855:./DLNFibre/Core/RadicalCatenary.lean:181:    codimRepCanonical Z + varietyDim (canonicalCoord d '' Z)
./noncirc-setlevel-answer.md:272:./route-choice-answer.md:862:./DLNFibre/Core/RadicalCatenary.lean:197:  rw [codimRepCanonical, codimRep, varietyDim, ← hm, WithBot.unbotD_coe]
./noncirc-setlevel-answer.md:273:./route-choice-answer.md:863:./DLNFibre/Core/RadicalCatenary.lean:203:The reducible-locus catenary at `codimRepCanonical`/`varietyDim` fires on the whole space `univ`
./noncirc-setlevel-answer.md:274:./route-choice-answer.md:864:./DLNFibre/Core/RadicalCatenary.lean:208:      + varietyDim (canonicalCoord dWitness ''
./noncirc-setlevel-answer.md:275:./route-choice-answer.md:865:./DLNFibre/Core/RadicalCatenary.lean:211:  codimRepCanonical_add_varietyDim_eq_card_of_nonempty
./noncirc-setlevel-answer.md:276:./route-choice-answer.md:884:./DLNFibre/Core/OrbitImageDim.lean:10:(`varietyDim_eq_ringKrullDim_range_orbitPullback`), discharges the AG-half of `hVoigt`:
./noncirc-setlevel-answer.md:277:./route-choice-answer.md:885:./DLNFibre/Core/OrbitImageDim.lean:15:- **A0** (landed): `varietyDim Z_M = (ringKrullDim (orbitPullback M).range).unbotD 0`.
./noncirc-setlevel-answer.md:278:./route-choice-answer.md:886:./DLNFibre/Core/OrbitImageDim.lean:77:the A4.3 identity is needed (the chain is `varietyDim = trdeg ≤ genericDifferentialRank ≤ finrank δ⁰`);
./noncirc-setlevel-answer.md:279:./route-choice-answer.md:887:./DLNFibre/Core/OrbitImageDim.lean:90:/-- **A4.4 chained with A0: `varietyDim Z_M ≤ finrank (range δ⁰)`.** Combining the landed A0 link
./noncirc-setlevel-answer.md:280:./route-choice-answer.md:888:./DLNFibre/Core/OrbitImageDim.lean:91:(`varietyDim_eq_ringKrullDim_range_orbitPullback`, needs `[Infinite k]`) with the submersion bound,
./noncirc-setlevel-answer.md:281:./route-choice-answer.md:889:./DLNFibre/Core/OrbitImageDim.lean:95:theorem varietyDim_orbitRankLocus_le_finrank_range_deformationδ
./noncirc-setlevel-answer.md:282:./route-choice-answer.md:890:./DLNFibre/Core/OrbitImageDim.lean:101:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./noncirc-setlevel-answer.md:283:./route-choice-answer.md:891:./DLNFibre/Core/OrbitImageDim.lean:103:  rw [varietyDim_eq_ringKrullDim_range_orbitPullback M]
./noncirc-setlevel-answer.md:284:./route-choice-answer.md:903:./DLNFibre/Core/MultComorphism.lean:27:4. **`vanishingIdeal(fibre) = radical(fibreGenIdeal)`** — over `[IsAlgClosed k]`, the engine's
./noncirc-setlevel-answer.md:285:./route-choice-answer.md:904:./DLNFibre/Core/MultComorphism.lean:28:   Nullstellensatz (`vanishingIdeal_zeroLocus_eq_radical`) reads the fibre's vanishing ideal as the
./noncirc-setlevel-answer.md:286:./route-choice-answer.md:905:./DLNFibre/Core/MultComorphism.lean:158:closed field, the engine's strong Nullstellensatz (`vanishingIdeal_zeroLocus_eq_radical`) reads the
./noncirc-setlevel-answer.md:287:./route-choice-answer.md:906:./DLNFibre/Core/MultComorphism.lean:160:theorem vanishingIdeal_image_fibre_eq_radical [IsAlgClosed k] (d : Fin (N + 1) → ℕ)
./noncirc-setlevel-answer.md:288:./route-choice-answer.md:907:./DLNFibre/Core/MultComorphism.lean:162:    vanishingIdeal k (canonicalCoord d '' (fibre d B)) = (fibreGenIdeal d B).radical := by
./noncirc-setlevel-answer.md:289:./route-choice-answer.md:908:./DLNFibre/Core/MultComorphism.lean:164:    vanishingIdeal_zeroLocus_eq_radical (K := k)]
./noncirc-setlevel-answer.md:290:./route-choice-answer.md:934:./DLNFibre/Core/AffineNoetherRank.lean:59:Noether-normalization rank `s`, hence agree: `(ringKrullDim (R ⧸ p)).unbotD 0 = (trdeg k (R ⧸ p)).toNat`.
./noncirc-setlevel-answer.md:291:./route-choice-answer.md:939:./DLNFibre/Core/FibreDimFibrationProbe.lean:37:/-- LANDED: the determinantal-stratum dimension `varietyDim (Mat^{≤r}) = r(n+m−r) = δ`. -/
./noncirc-setlevel-answer.md:292:./route-choice-answer.md:940:./DLNFibre/Core/FibreDimFibrationProbe.lean:39:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./noncirc-setlevel-answer.md:293:./route-choice-answer.md:941:./DLNFibre/Core/FibreDimFibrationProbe.lean:41:  varietyDim_productRankLocusLE_stratum n m r hn hm
./noncirc-setlevel-answer.md:294:./route-choice-answer.md:944:./DLNFibre/Core/FibreDimFibrationProbe.lean:55:/-- LANDED: the catenary closer (PRIMALITY-gated) — `codim Z = card − varietyDim Z`. -/
./noncirc-setlevel-answer.md:295:./route-choice-answer.md:946:./DLNFibre/Core/FibreDimFibrationProbe.lean:59:    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
./noncirc-setlevel-answer.md:296:./route-choice-answer.md:947:./DLNFibre/Core/FibreDimFibrationProbe.lean:60:  codimRepCanonical_eq_card_sub_varietyDim Z hp
./noncirc-setlevel-answer.md:297:./route-choice-answer.md:952:./DLNFibre/Core/FibreDimFibrationProbe.lean:96:MvPolynomial (RepCoord stratum) k ⧸ vanishingIdeal(…)`. From the thermometer (varietyDim = δ) which
./noncirc-setlevel-answer.md:298:./route-choice-answer.md:953:./DLNFibre/Core/FibreDimFibrationProbe.lean:97:unfolds to exactly `(ringKrullDim (… ⧸ vanishingIdeal …)).unbotD 0`, plus the quotient is nontrivial
./noncirc-setlevel-answer.md:299:./route-choice-answer.md:954:./DLNFibre/Core/FibreDimFibrationProbe.lean:100:/-- `varietyDim` unfolds to the `unbotD 0` of the quotient `ringKrullDim`. -/
./noncirc-setlevel-answer.md:300:./route-choice-answer.md:955:./DLNFibre/Core/FibreDimFibrationProbe.lean:102:    varietyDim Z = (ringKrullDim (MvPolynomial (RepCoord (dStratum 2 2)) k ⧸
./noncirc-setlevel-answer.md:301:./route-choice-answer.md:1050:./DLNFibre/Core/VoigtDischarge.lean:8:The capstone of the AG half. The A4 submersion bound `varietyDim Z_M ≤ finrank (range δ⁰)`
./noncirc-setlevel-answer.md:302:./route-choice-answer.md:1051:./DLNFibre/Core/VoigtDischarge.lean:9:(`varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional`, char 0) and the A6.1 reverse
./noncirc-setlevel-answer.md:303:./route-choice-answer.md:1052:./DLNFibre/Core/VoigtDischarge.lean:10:inequality `finrank (range δ⁰) ≤ varietyDim Z_M` (`finrank_range_deformationδ_le_varietyDim`) squeeze
./noncirc-setlevel-answer.md:304:./route-choice-answer.md:1053:./DLNFibre/Core/VoigtDischarge.lean:11:to **equality** `varietyDim Z_M = finrank (range δ⁰)` (the orbit closure is smooth of the expected
./noncirc-setlevel-answer.md:305:./route-choice-answer.md:1054:./DLNFibre/Core/VoigtDischarge.lean:33:/-! ## The squeeze — `varietyDim Z_M = finrank (range δ⁰)` -/
./noncirc-setlevel-answer.md:306:./route-choice-answer.md:1055:./DLNFibre/Core/VoigtDischarge.lean:38:theorem varietyDim_orbitRankLocus_eq_finrank_range_deformationδ
./noncirc-setlevel-answer.md:307:./route-choice-answer.md:1056:./DLNFibre/Core/VoigtDischarge.lean:40:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./noncirc-setlevel-answer.md:308:./route-choice-answer.md:1057:./DLNFibre/Core/VoigtDischarge.lean:43:  refine le_antisymm ?_ (finrank_range_deformationδ_le_varietyDim M)
./noncirc-setlevel-answer.md:309:./route-choice-answer.md:1058:./DLNFibre/Core/VoigtDischarge.lean:44:  exact varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional M
./noncirc-setlevel-answer.md:310:./route-choice-answer.md:1059:./DLNFibre/Core/VoigtDischarge.lean:64:    have hadd := codimRep_add_varietyDim_eq_card (canonicalCoord d) (orbitRankLocus M)
./noncirc-setlevel-answer.md:311:./route-choice-answer.md:1061:./DLNFibre/Core/VoigtDischarge.lean:66:    rwa [varietyDim_orbitRankLocus_eq_finrank_range_deformationδ M, ← hr] at hadd
./noncirc-setlevel-answer.md:312:./route-choice-answer.md:1063:./DLNFibre/Core/OrbitTangentCotangent.lean:14:# `DLNFibre.Core.OrbitTangentCotangent` — A6.1: the reverse inequality `finrank(range δ⁰) ≤ varietyDim Z_M`
./noncirc-setlevel-answer.md:313:./route-choice-answer.md:1064:./DLNFibre/Core/OrbitTangentCotangent.lean:19:`varietyDim Z_M = finrank (range δ⁰)`, the geometric heart of Voigt's lemma.
./noncirc-setlevel-answer.md:314:./route-choice-answer.md:1065:./DLNFibre/Core/OrbitTangentCotangent.lean:22:`I = orbitIdeal M = vanishingIdeal(orbitSet M)` directly — no determinantal minors, no radical. The
./noncirc-setlevel-answer.md:315:./route-choice-answer.md:1067:./DLNFibre/Core/OrbitTangentCotangent.lean:564:/-! ## R6 — chain `finrank (m_M.Cotangent)` to `varietyDim Z_M` -/
./noncirc-setlevel-answer.md:316:./route-choice-answer.md:1068:./DLNFibre/Core/OrbitTangentCotangent.lean:566:/-- `ringKrullDim (orbitRing M)` is a finite natural number `n`, equal to `varietyDim Z_M`:
./noncirc-setlevel-answer.md:317:./route-choice-answer.md:1069:./DLNFibre/Core/OrbitTangentCotangent.lean:571:      ∧ varietyDim (canonicalCoord d '' orbitRankLocus M) = (n : ℕ∞) := by
./noncirc-setlevel-answer.md:318:./route-choice-answer.md:1070:./DLNFibre/Core/OrbitTangentCotangent.lean:579:  -- `varietyDim Z_M = (ringKrullDim (orbitRing M)).unbotD 0` (L6.4 + `varietyDim` def)
./noncirc-setlevel-answer.md:319:./route-choice-answer.md:1071:./DLNFibre/Core/OrbitTangentCotangent.lean:580:  have hvar : varietyDim (canonicalCoord d '' orbitRankLocus M)
./noncirc-setlevel-answer.md:320:./route-choice-answer.md:1072:./DLNFibre/Core/OrbitTangentCotangent.lean:582:    rw [varietyDim, vanishingIdeal_orbitRankLocus_eq_orbitSet M]; rfl
./noncirc-setlevel-answer.md:321:./route-choice-answer.md:1073:./DLNFibre/Core/OrbitTangentCotangent.lean:598:/-- **R6 — `finrank k (m_M.Cotangent) = varietyDim Z_M`.** The cotangent finrank equals the variety
./noncirc-setlevel-answer.md:322:./route-choice-answer.md:1074:./DLNFibre/Core/OrbitTangentCotangent.lean:601:GAP3 (`ringKrullDim (AtPrime m_M) = ringKrullDim (orbitRing M)`), and `varietyDim Z_M =
./noncirc-setlevel-answer.md:323:./route-choice-answer.md:1075:./DLNFibre/Core/OrbitTangentCotangent.lean:603:theorem finrank_cotangent_eq_varietyDim [IsAlgClosed k] (M : Tuple (k := k) d) :
./noncirc-setlevel-answer.md:324:./route-choice-answer.md:1076:./DLNFibre/Core/OrbitTangentCotangent.lean:605:      = varietyDim (canonicalCoord d '' orbitRankLocus M) := by
./noncirc-setlevel-answer.md:325:./route-choice-answer.md:1078:./DLNFibre/Core/OrbitTangentCotangent.lean:635:/-! ## The A6.1 headline — `finrank (range δ⁰) ≤ varietyDim Z_M` -/
./noncirc-setlevel-answer.md:326:./route-choice-answer.md:1079:./DLNFibre/Core/OrbitTangentCotangent.lean:637:/-- **A6.1 (the reverse inequality).** `finrank k (range δ⁰) ≤ varietyDim Z_M`: the orbit tangent
./noncirc-setlevel-answer.md:327:./route-choice-answer.md:1080:./DLNFibre/Core/OrbitTangentCotangent.lean:641:theorem finrank_range_deformationδ_le_varietyDim [IsAlgClosed k] (M : Tuple (k := k) d) :
./noncirc-setlevel-answer.md:328:./route-choice-answer.md:1081:./DLNFibre/Core/OrbitTangentCotangent.lean:643:      ≤ varietyDim (canonicalCoord d '' orbitRankLocus M) := by
./noncirc-setlevel-answer.md:329:./route-choice-answer.md:1082:./DLNFibre/Core/OrbitTangentCotangent.lean:644:  rw [← finrank_cotangent_eq_varietyDim M]
./noncirc-setlevel-answer.md:330:./route-choice-answer.md:1083:./DLNFibre/Core/RouteCAssembly.lean:17:identity `varietyDim Σ^r = δ + varietyDim F` (`hSweep`) — and the Cited closure/density bridge
./noncirc-setlevel-answer.md:331:./route-choice-answer.md:1084:./DLNFibre/Core/RouteCAssembly.lean:18:`varietyDim Σ^r = varietyDim Σ̄^r` (`hClosure`, Lehalleur–Rimányi 4.4/4.5) are carried as **explicit
./noncirc-setlevel-answer.md:332:./route-choice-answer.md:1085:./DLNFibre/Core/RouteCAssembly.lean:20:relations `codimRepCanonical Z + varietyDim Z = card` are carried as named hypotheses
./noncirc-setlevel-answer.md:333:./route-choice-answer.md:1086:./DLNFibre/Core/RouteCAssembly.lean:50:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./noncirc-setlevel-answer.md:334:./route-choice-answer.md:1087:./DLNFibre/Core/RouteCAssembly.lean:52:          + varietyDim (canonicalCoord d '' fibre d B))
./noncirc-setlevel-answer.md:335:./route-choice-answer.md:1088:./DLNFibre/Core/RouteCAssembly.lean:53:    (hClosure : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./noncirc-setlevel-answer.md:336:./route-choice-answer.md:1089:./DLNFibre/Core/RouteCAssembly.lean:54:        = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r))
./noncirc-setlevel-answer.md:337:./route-choice-answer.md:1090:./DLNFibre/Core/RouteCAssembly.lean:56:        + varietyDim (canonicalCoord d '' fibre d B) = (Nat.card (RepCoord d) : ℕ∞))
./noncirc-setlevel-answer.md:338:./route-choice-answer.md:1092:./DLNFibre/Core/RouteCAssembly.lean:58:        + varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
./noncirc-setlevel-answer.md:339:./route-choice-answer.md:1095:./DLNFibre/Core/RouteCAssembly.lean:67:  have hdimSigma : varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
./noncirc-setlevel-answer.md:340:./route-choice-answer.md:1096:./DLNFibre/Core/RouteCAssembly.lean:69:        + varietyDim (canonicalCoord d '' fibre d B) := by
./noncirc-setlevel-answer.md:341:./route-choice-answer.md:1097:./DLNFibre/Core/RouteCAssembly.lean:72:  have hdimF_ne : varietyDim (canonicalCoord d '' fibre d B) ≠ ⊤ := by
./noncirc-setlevel-answer.md:342:./route-choice-answer.md:1098:./DLNFibre/Core/RouteCAssembly.lean:79:  have key : varietyDim (canonicalCoord d '' fibre d B) + codimRepCanonical (fibre d B)
./noncirc-setlevel-answer.md:343:./route-choice-answer.md:1099:./DLNFibre/Core/RouteCAssembly.lean:80:      = varietyDim (canonicalCoord d '' fibre d B)
./noncirc-setlevel-answer.md:344:./route-choice-answer.md:1100:./DLNFibre/Core/RouteCAssembly.lean:82:    calc varietyDim (canonicalCoord d '' fibre d B) + codimRepCanonical (fibre d B)
./noncirc-setlevel-answer.md:345:./route-choice-answer.md:1101:./DLNFibre/Core/RouteCAssembly.lean:83:        = codimRepCanonical (fibre d B) + varietyDim (canonicalCoord d '' fibre d B) := by
./noncirc-setlevel-answer.md:346:./route-choice-answer.md:1102:./DLNFibre/Core/RouteCAssembly.lean:88:              + varietyDim (canonicalCoord d '' fibre d B)) := hCatSigma.symm
./noncirc-setlevel-answer.md:347:./route-choice-answer.md:1103:./DLNFibre/Core/RouteCAssembly.lean:89:      _ = varietyDim (canonicalCoord d '' fibre d B)
./noncirc-setlevel-answer.md:348:./route-choice-answer.md:1104:./DLNFibre/Core/RouteCAssembly.lean:100:`codimRepCanonical_add_varietyDim_eq_card_of_nonempty` (`Core.RadicalCatenary`), given that the
./noncirc-setlevel-answer.md:349:./route-choice-answer.md:1106:./DLNFibre/Core/RouteCAssembly.lean:107:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./noncirc-setlevel-answer.md:350:./route-choice-answer.md:1107:./DLNFibre/Core/RouteCAssembly.lean:109:          + varietyDim (canonicalCoord d '' fibre d B))
./noncirc-setlevel-answer.md:351:./route-choice-answer.md:1108:./DLNFibre/Core/RouteCAssembly.lean:110:    (hClosure : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./noncirc-setlevel-answer.md:352:./route-choice-answer.md:1109:./DLNFibre/Core/RouteCAssembly.lean:111:        = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)) :
./noncirc-setlevel-answer.md:353:./route-choice-answer.md:1110:./DLNFibre/Core/RouteCAssembly.lean:115:    (codimRepCanonical_add_varietyDim_eq_card_of_nonempty hFne)
./noncirc-setlevel-answer.md:354:./route-choice-answer.md:1111:./DLNFibre/Core/RouteCAssembly.lean:116:    (codimRepCanonical_add_varietyDim_eq_card_of_nonempty hSigmaNe)
./noncirc-setlevel-answer.md:355:./route-choice-answer.md:1165:/-! ## The base-stratum Krull dimension brick: `ringKrullDim O(Mat^{≤r}) = δ`
./noncirc-setlevel-answer.md:356:./route-choice-answer.md:1172:`varietyDim = δ`, lifting the `unbotD 0` to the genuine `WithBot ℕ∞` value (the quotient is
./noncirc-setlevel-answer.md:357:./route-choice-answer.md:1173:nontrivial, so `ringKrullDim ≠ ⊥`). -/
./noncirc-setlevel-answer.md:358:./route-choice-answer.md:1175:/-- **The base-stratum Krull dimension** `ringKrullDim O(Mat^{≤r}) = δ`. For `r ≤ n`, `r ≤ m`, over an
./noncirc-setlevel-answer.md:359:./route-choice-answer.md:1178:The thermometer `varietyDim_productRankLocusLE_stratum` gives the `ℕ∞`-via-`unbotD` value; this lifts
./noncirc-setlevel-answer.md:360:./route-choice-answer.md:1180:is a nontrivial domain, so `ringKrullDim ≠ ⊥`). -/
./noncirc-setlevel-answer.md:361:./route-choice-answer.md:1181:theorem ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta [IsAlgClosed k] [CharZero k]
./noncirc-setlevel-answer.md:362:./route-choice-answer.md:1183:    ringKrullDim (MvPolynomial (RepCoord (dStratum n m)) k ⧸
./noncirc-setlevel-answer.md:363:./route-choice-answer.md:1191:  -- the thermometer: `varietyDim = δ`, i.e. `(ringKrullDim (R ⧸ I)).unbotD 0 = δ`.
./noncirc-setlevel-answer.md:364:./route-choice-answer.md:1192:  have hvd : varietyDim (canonicalCoord (dStratum n m) ''
./noncirc-setlevel-answer.md:365:./route-choice-answer.md:1194:    varietyDim_productRankLocusLE_stratum n m r hn hm
./noncirc-setlevel-answer.md:366:./route-choice-answer.md:1195:  rw [varietyDim, ← hI] at hvd
./noncirc-setlevel-answer.md:367:./route-choice-answer.md:1196:  -- the quotient is a nontrivial domain, so `ringKrullDim ≠ ⊥`.
./noncirc-setlevel-answer.md:368:./route-choice-answer.md:1199:  have hne : ringKrullDim (MvPolynomial (RepCoord (dStratum n m)) k ⧸ I) ≠ ⊥ :=
./noncirc-setlevel-answer.md:369:./route-choice-answer.md:1201:      ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (RepCoord (dStratum n m)) k ⧸ I)
./noncirc-setlevel-answer.md:370:./route-choice-answer.md:1209:By equidimensionality at a closed point (`OrbitTangentCotangent.height_eq_ringKrullDim_of_isMaximal_fintype`,
./noncirc-setlevel-answer.md:371:./route-choice-answer.md:1217:irreducible determinantal base, with `ringKrullDim O(Mat^{≤r}) = δ`. -/
./noncirc-setlevel-answer.md:372:./route-choice-answer.md:1228:  rw [height_eq_ringKrullDim_of_isMaximal_fintype,
./noncirc-setlevel-answer.md:373:./route-choice-answer.md:1229:    ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta n m r hn hm]
./noncirc-setlevel-answer.md:374:./route-choice-answer.md:1233:`affine_domain_height_add_ringKrullDim_quotient_eq` is over `MvPolynomial (Fin n) k`. Transport it to
./noncirc-setlevel-answer.md:375:./route-choice-answer.md:1235:`height_eq_ringKrullDim_of_isMaximal_fintype` does for the maximal corollary. This is the engine the
./noncirc-setlevel-answer.md:376:./route-choice-answer.md:1241:`height p + ringKrullDim (A ⧸ p) = ringKrullDim A`. Transports
./noncirc-setlevel-answer.md:377:./route-choice-answer.md:1242:`affine_domain_height_add_ringKrullDim_quotient_eq` through `renameEquiv` and the induced quotient
./noncirc-setlevel-answer.md:378:./route-choice-answer.md:1244:theorem affine_domain_height_add_ringKrullDim_quotient_eq_fintype {σ : Type*} [Finite σ]
./noncirc-setlevel-answer.md:379:./route-choice-answer.md:1246:    (p.height : WithBot ℕ∞) + ringKrullDim ((MvPolynomial σ k ⧸ I) ⧸ p)
./noncirc-setlevel-answer.md:380:./route-choice-answer.md:1247:      = ringKrullDim (MvPolynomial σ k ⧸ I) := by
./noncirc-setlevel-answer.md:381:./route-choice-answer.md:1260:  have hL := affine_domain_height_add_ringKrullDim_quotient_eq k (Fintype.card σ) J p'
./noncirc-setlevel-answer.md:382:./route-choice-answer.md:1263:    ringKrullDim_quotient_map_algEquiv Φ p, hJ, ringKrullDim_quotient_map_algEquiv e I] at hL
./noncirc-setlevel-answer.md:383:./route-choice-answer.md:1303:/-- LANDED: the determinantal-stratum dimension `varietyDim (Mat^{≤r}) = r(n+m−r) = δ`. -/
./noncirc-setlevel-answer.md:384:./route-choice-answer.md:1305:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./noncirc-setlevel-answer.md:385:./route-choice-answer.md:1307:  varietyDim_productRankLocusLE_stratum n m r hn hm
./noncirc-setlevel-answer.md:386:./route-choice-answer.md:1321:/-- LANDED: the catenary closer (PRIMALITY-gated) — `codim Z = card − varietyDim Z`. -/
./noncirc-setlevel-answer.md:387:./route-choice-answer.md:1325:    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
./noncirc-setlevel-answer.md:388:./route-choice-answer.md:1326:  codimRepCanonical_eq_card_sub_varietyDim Z hp
./noncirc-setlevel-answer.md:389:./route-choice-answer.md:1331:    (p.height : WithBot ℕ∞) + ringKrullDim (((MvPolynomial (Fin n) k) ⧸ I) ⧸ p)
./noncirc-setlevel-answer.md:390:./route-choice-answer.md:1332:      = ringKrullDim ((MvPolynomial (Fin n) k) ⧸ I) :=
./noncirc-setlevel-answer.md:391:./route-choice-answer.md:1333:  affine_domain_height_add_ringKrullDim_quotient_eq k n I p
./noncirc-setlevel-answer.md:392:./route-choice-answer.md:1338:    (m.height : WithBot ℕ∞) = ringKrullDim ((MvPolynomial (Fin n) k) ⧸ I) :=
./noncirc-setlevel-answer.md:393:./route-choice-answer.md:1339:  height_eq_ringKrullDim_of_isMaximal k n I m
./noncirc-setlevel-answer.md:394:./route-choice-answer.md:1359:/-! ## Candidate: the base ringKrullDim = δ (the brick the going-down/00OM route consumes)
./noncirc-setlevel-answer.md:445:`hSweep : varietyDim Σ^r = δ + varietyDim F`. Rung 1 = a single-chart trivialization. The DECISIVE
./noncirc-setlevel-answer.md:446:de-risk: is the SET-LEVEL / `varietyDim` version non-circular, given a PRIOR attempt (R2-3b-4) at a
./noncirc-setlevel-answer.md:464:For `hSweep` I do NOT need reducedness. `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`
./noncirc-setlevel-answer.md:465:and `vanishingIdeal Z` is ALREADY radical (it's a vanishing ideal). Krull dim is RADICAL-INSENSITIVE:
./noncirc-setlevel-answer.md:466:`ringKrullDim (R⧸I) = ringKrullDim (R⧸√I)`. So `varietyDim` reads only the REDUCED/variety structure;
./noncirc-setlevel-answer.md:477:1. **Is `varietyDim` genuinely radical-insensitive in Mathlib v4.29** — i.e. is `ringKrullDim (R⧸I) =
./noncirc-setlevel-answer.md:478:   ringKrullDim (R⧸ I.radical)` available (or `ringKrullDim` factors through `√`)? Name the lemma if
./noncirc-setlevel-answer.md:484:   chart's normalizing gauge. This is a bijection of SETS / a `varietyDim`-preserving map. Does
./noncirc-setlevel-answer.md:489:   `varietyDim(U×F) = varietyDim U + varietyDim F` secretly needs flatness/reducedness.
./noncirc-setlevel-answer.md:491:3. **The product-dimension step `varietyDim(U × F) = varietyDim U + varietyDim F`.** For a product of
./noncirc-setlevel-answer.md:493:   (as `ringKrullDim (A ⊗_k B) = ringKrullDim A + ringKrullDim B`, or a variety-dimension product)?
./noncirc-setlevel-answer.md:499:4. **The glue over the finite pivot cover.** `varietyDim(⋃_i Z_i) = max_i varietyDim(Z_i)` for a
./noncirc-setlevel-answer.md:500:   finite cover — is that radical-insensitive and in Mathlib (or trivial from `ringKrullDim` of a
./noncirc-setlevel-answer.md:503:5. **Net verdict:** does the SET-LEVEL/`varietyDim` route (c) dodge the R2-3b-4 circularity? If YES,
./noncirc-setlevel-answer.md:508:The key thing I need from you: a clean YES/NO on whether radical-insensitivity of `varietyDim` lets
./noncirc-setlevel-answer.md:519:/bin/bash -lc "rg -n \"varietyDim|ringKrullDim|radical|IsJacobson|KrullDim|tensor|TensorProduct\" . -g '*.lean' -g '*.md' | head -300" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
./noncirc-setlevel-answer.md:521:./route-choice-prompt.md:10:varietyDim (Σ^r)  =  δ  +  varietyDim F
./noncirc-setlevel-answer.md:522:./route-choice-prompt.md:13:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./noncirc-setlevel-answer.md:523:./route-choice-prompt.md:18:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./noncirc-setlevel-answer.md:524:./route-choice-prompt.md:28:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./noncirc-setlevel-answer.md:525:./route-choice-prompt.md:29:   ringKrullDim (R ⧸ ker(pullback)) = ringKrullDim((pullback).range) = trdeg_k(range)` for a
./noncirc-setlevel-answer.md:526:./route-choice-prompt.md:31:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./noncirc-setlevel-answer.md:527:./route-choice-prompt.md:52:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./noncirc-setlevel-answer.md:528:./route-choice-prompt.md:60:max component, i.e. `ringKrullDim`)? Is `ringKrullDim`-additivity over a sweep even true without
./noncirc-setlevel-answer.md:529:./route-choice-prompt.md:73:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./noncirc-setlevel-answer.md:530:./route-choice-prompt.md:75:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./noncirc-setlevel-answer.md:531:./noncirc-setlevel-prompt.md:4:`hSweep : varietyDim Σ^r = δ + varietyDim F`. Rung 1 = a single-chart trivialization. The DECISIVE
./noncirc-setlevel-answer.md:532:./noncirc-setlevel-prompt.md:5:de-risk: is the SET-LEVEL / `varietyDim` version non-circular, given a PRIOR attempt (R2-3b-4) at a
./noncirc-setlevel-answer.md:534:./noncirc-setlevel-prompt.md:23:For `hSweep` I do NOT need reducedness. `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`
./noncirc-setlevel-answer.md:535:./noncirc-setlevel-prompt.md:24:and `vanishingIdeal Z` is ALREADY radical (it's a vanishing ideal). Krull dim is RADICAL-INSENSITIVE:
./noncirc-setlevel-answer.md:536:./noncirc-setlevel-prompt.md:25:`ringKrullDim (R⧸I) = ringKrullDim (R⧸√I)`. So `varietyDim` reads only the REDUCED/variety structure;
./noncirc-setlevel-answer.md:538:./noncirc-setlevel-prompt.md:36:1. **Is `varietyDim` genuinely radical-insensitive in Mathlib v4.29** — i.e. is `ringKrullDim (R⧸I) =
./noncirc-setlevel-answer.md:539:./noncirc-setlevel-prompt.md:37:   ringKrullDim (R⧸ I.radical)` available (or `ringKrullDim` factors through `√`)? Name the lemma if
./noncirc-setlevel-answer.md:540:./noncirc-setlevel-prompt.md:43:   chart's normalizing gauge. This is a bijection of SETS / a `varietyDim`-preserving map. Does
./noncirc-setlevel-answer.md:543:./noncirc-setlevel-prompt.md:48:   `varietyDim(U×F) = varietyDim U + varietyDim F` secretly needs flatness/reducedness.
./noncirc-setlevel-answer.md:544:./noncirc-setlevel-prompt.md:50:3. **The product-dimension step `varietyDim(U × F) = varietyDim U + varietyDim F`.** For a product of
./noncirc-setlevel-answer.md:545:./noncirc-setlevel-prompt.md:52:   (as `ringKrullDim (A ⊗_k B) = ringKrullDim A + ringKrullDim B`, or a variety-dimension product)?
./noncirc-setlevel-answer.md:548:./noncirc-setlevel-prompt.md:58:4. **The glue over the finite pivot cover.** `varietyDim(⋃_i Z_i) = max_i varietyDim(Z_i)` for a
./noncirc-setlevel-answer.md:549:./noncirc-setlevel-prompt.md:59:   finite cover — is that radical-insensitive and in Mathlib (or trivial from `ringKrullDim` of a
./noncirc-setlevel-answer.md:550:./noncirc-setlevel-prompt.md:62:5. **Net verdict:** does the SET-LEVEL/`varietyDim` route (c) dodge the R2-3b-4 circularity? If YES,
./noncirc-setlevel-answer.md:552:./noncirc-setlevel-prompt.md:67:The key thing I need from you: a clean YES/NO on whether radical-insensitivity of `varietyDim` lets
./noncirc-setlevel-answer.md:553:./noncirc-setlevel-answer.md:19:`hSweep : varietyDim Σ^r = δ + varietyDim F`. Rung 1 = a single-chart trivialization. The DECISIVE
./noncirc-setlevel-answer.md:554:./noncirc-setlevel-answer.md:20:de-risk: is the SET-LEVEL / `varietyDim` version non-circular, given a PRIOR attempt (R2-3b-4) at a
./noncirc-setlevel-answer.md:556:./noncirc-setlevel-answer.md:38:For `hSweep` I do NOT need reducedness. `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`
./noncirc-setlevel-answer.md:557:./noncirc-setlevel-answer.md:39:and `vanishingIdeal Z` is ALREADY radical (it's a vanishing ideal). Krull dim is RADICAL-INSENSITIVE:
./noncirc-setlevel-answer.md:558:./noncirc-setlevel-answer.md:40:`ringKrullDim (R⧸I) = ringKrullDim (R⧸√I)`. So `varietyDim` reads only the REDUCED/variety structure;
./noncirc-setlevel-answer.md:560:./noncirc-setlevel-answer.md:51:1. **Is `varietyDim` genuinely radical-insensitive in Mathlib v4.29** — i.e. is `ringKrullDim (R⧸I) =
./noncirc-setlevel-answer.md:561:./noncirc-setlevel-answer.md:52:   ringKrullDim (R⧸ I.radical)` available (or `ringKrullDim` factors through `√`)? Name the lemma if
./noncirc-setlevel-answer.md:562:./noncirc-setlevel-answer.md:58:   chart's normalizing gauge. This is a bijection of SETS / a `varietyDim`-preserving map. Does
./noncirc-setlevel-answer.md:565:./noncirc-setlevel-answer.md:63:   `varietyDim(U×F) = varietyDim U + varietyDim F` secretly needs flatness/reducedness.
./noncirc-setlevel-answer.md:566:./noncirc-setlevel-answer.md:65:3. **The product-dimension step `varietyDim(U × F) = varietyDim U + varietyDim F`.** For a product of
./noncirc-setlevel-answer.md:567:./noncirc-setlevel-answer.md:67:   (as `ringKrullDim (A ⊗_k B) = ringKrullDim A + ringKrullDim B`, or a variety-dimension product)?
./noncirc-setlevel-answer.md:570:./noncirc-setlevel-answer.md:73:4. **The glue over the finite pivot cover.** `varietyDim(⋃_i Z_i) = max_i varietyDim(Z_i)` for a
./noncirc-setlevel-answer.md:571:./noncirc-setlevel-answer.md:74:   finite cover — is that radical-insensitive and in Mathlib (or trivial from `ringKrullDim` of a
./noncirc-setlevel-answer.md:572:./noncirc-setlevel-answer.md:77:5. **Net verdict:** does the SET-LEVEL/`varietyDim` route (c) dodge the R2-3b-4 circularity? If YES,
./noncirc-setlevel-answer.md:574:./noncirc-setlevel-answer.md:82:The key thing I need from you: a clean YES/NO on whether radical-insensitivity of `varietyDim` lets
./noncirc-setlevel-answer.md:575:./route-choice-answer.md:25:varietyDim (Σ^r)  =  δ  +  varietyDim F
./noncirc-setlevel-answer.md:576:./route-choice-answer.md:28:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./noncirc-setlevel-answer.md:577:./route-choice-answer.md:33:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./noncirc-setlevel-answer.md:578:./route-choice-answer.md:43:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./noncirc-setlevel-answer.md:579:./route-choice-answer.md:44:   ringKrullDim (R ⧸ ker(pullback)) = ringKrullDim((pullback).range) = trdeg_k(range)` for a
./noncirc-setlevel-answer.md:580:./route-choice-answer.md:46:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./noncirc-setlevel-answer.md:581:./route-choice-answer.md:67:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./noncirc-setlevel-answer.md:582:./route-choice-answer.md:75:max component, i.e. `ringKrullDim`)? Is `ringKrullDim`-additivity over a sweep even true without
./noncirc-setlevel-answer.md:583:./route-choice-answer.md:88:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./noncirc-setlevel-answer.md:584:./route-choice-answer.md:90:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./noncirc-setlevel-answer.md:585:./route-choice-answer.md:114:./route-choice-prompt.md:31:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./noncirc-setlevel-answer.md:586:./route-choice-answer.md:129:./route-choice-answer.md:46:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./noncirc-setlevel-answer.md:587:./route-choice-answer.md:188:varietyDim (Σ^r)  =  δ  +  varietyDim F
./noncirc-setlevel-answer.md:588:./route-choice-answer.md:191:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./noncirc-setlevel-answer.md:589:./route-choice-answer.md:196:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./noncirc-setlevel-answer.md:590:./route-choice-answer.md:206:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./noncirc-setlevel-answer.md:591:./route-choice-answer.md:207:   ringKrullDim (R ⧸ ker(pullback)) = ringKrullDim((pullback).range) = trdeg_k(range)` for a
./noncirc-setlevel-answer.md:592:./route-choice-answer.md:209:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./noncirc-setlevel-answer.md:593:./route-choice-answer.md:230:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./noncirc-setlevel-answer.md:594:./route-choice-answer.md:238:max component, i.e. `ringKrullDim`)? Is `ringKrullDim`-additivity over a sweep even true without
./noncirc-setlevel-answer.md:595:./route-choice-answer.md:251:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./noncirc-setlevel-answer.md:596:./route-choice-answer.md:253:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./noncirc-setlevel-answer.md:597:./route-choice-answer.md:277:./route-choice-prompt.md:31:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./noncirc-setlevel-answer.md:598:./route-choice-answer.md:292:./route-choice-answer.md:46:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./noncirc-setlevel-answer.md:599:./route-choice-answer.md:325:/bin/bash -lc 'rg -n "Noether.*Norm|Noetherian.*Norm|normalization|GenericFreeness|generic freeness|height_eq_under|FlatQuasiFinite|HasGoingDown|trdeg_add_eq|rankLocus|productRankLocus|varietyDim|vanishingIdeal" -S .' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean
./noncirc-setlevel-answer.md:600:./route-choice-answer.md:450:./DLNFibre.lean:160:-- `codimRepCanonical Z + varietyDim Z = card` for nonempty Z. Discharges the catenary hyps of RouteCAssembly.
./noncirc-setlevel-answer.md:601:./route-choice-answer.md:466:./DLNFibre/Core/OrbitPullbackDim.lean:6:# `DLNFibre.Core.OrbitPullbackDim` — route-c setup: `varietyDim(Z_M) = ringKrullDim((μ_M^*).range)`
./noncirc-setlevel-answer.md:602:./route-choice-answer.md:467:./DLNFibre/Core/OrbitPullbackDim.lean:16:1. **Ideal identification.** `varietyDim Z_M = ringKrullDim (MvPolynomial (RepCoord d) k ⧸
./noncirc-setlevel-answer.md:603:./route-choice-answer.md:468:./DLNFibre/Core/OrbitPullbackDim.lean:17:   ker μ_M^*)`, immediate from the `varietyDim` definition, the Abeasis–Del Fra ideal equality L6.4
./noncirc-setlevel-answer.md:604:./route-choice-answer.md:471:./DLNFibre/Core/OrbitPullbackDim.lean:25:The headline `varietyDim_eq_ringKrullDim_range_orbitPullback` hands A4 a finitely-generated domain
./noncirc-setlevel-answer.md:605:./route-choice-answer.md:472:./DLNFibre/Core/OrbitPullbackDim.lean:48:`MvPolynomial (RepCoord d) k ⧸ ker μ_M^*`. `varietyDim` definition, then L6.4
./noncirc-setlevel-answer.md:606:./route-choice-answer.md:475:./DLNFibre/Core/OrbitPullbackDim.lean:52:theorem varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker [Infinite k]
./noncirc-setlevel-answer.md:607:./route-choice-answer.md:476:./DLNFibre/Core/OrbitPullbackDim.lean:54:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./noncirc-setlevel-answer.md:608:./route-choice-answer.md:477:./DLNFibre/Core/OrbitPullbackDim.lean:57:  rw [varietyDim, vanishingIdeal_orbitRankLocus_eq_orbitSet M, ← range_orbitMap,
./noncirc-setlevel-answer.md:609:./route-choice-answer.md:479:./DLNFibre/Core/OrbitPullbackDim.lean:70:transcendence degree. Combines `varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker` with the
./noncirc-setlevel-answer.md:610:./route-choice-answer.md:480:./DLNFibre/Core/OrbitPullbackDim.lean:74:theorem varietyDim_eq_ringKrullDim_range_orbitPullback [Infinite k] {d : Fin (N + 1) → ℕ}
./noncirc-setlevel-answer.md:611:./route-choice-answer.md:481:./DLNFibre/Core/OrbitPullbackDim.lean:76:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./noncirc-setlevel-answer.md:612:./route-choice-answer.md:482:./DLNFibre/Core/OrbitPullbackDim.lean:78:  rw [varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker M,
./noncirc-setlevel-answer.md:613:./route-choice-answer.md:483:./DLNFibre/Core/OrbitPullbackDim.lean:89:/-- The headline at the concrete `(2,2,2)/ℚ` tuple: `varietyDim (canonicalCoord '' orbitRankLocus
./noncirc-setlevel-answer.md:614:./route-choice-answer.md:484:./DLNFibre/Core/OrbitPullbackDim.lean:93:    varietyDim (canonicalCoord dWitness '' orbitRankLocus tupleWitnessQ)
./noncirc-setlevel-answer.md:615:./route-choice-answer.md:485:./DLNFibre/Core/OrbitPullbackDim.lean:95:  varietyDim_eq_ringKrullDim_range_orbitPullback tupleWitnessQ
./noncirc-setlevel-answer.md:616:./route-choice-answer.md:506:./DLNFibre/Core/DeterminantalStratumDim.lean:29:4. **The catenary bridge** (LANDED `codimRep_add_varietyDim_eq_card`): `codim + dim = card = m·n`,
./noncirc-setlevel-answer.md:617:./route-choice-answer.md:520:./DLNFibre/Core/DeterminantalStratumDim.lean:224:> `varietyDim (Mat^{rk ≤ r}_{m × n}) = r · (n + m − r)`.
./noncirc-setlevel-answer.md:618:./route-choice-answer.md:521:./DLNFibre/Core/DeterminantalStratumDim.lean:229:theorem varietyDim_productRankLocusLE_stratum [IsAlgClosed k] [CharZero k] (n m r : ℕ)
./noncirc-setlevel-answer.md:619:./route-choice-answer.md:522:./DLNFibre/Core/DeterminantalStratumDim.lean:231:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./noncirc-setlevel-answer.md:620:./route-choice-answer.md:524:./DLNFibre/Core/DeterminantalStratumDim.lean:237:  have hbridge := codimRep_add_varietyDim_eq_card (canonicalCoord (dStratum n m)) Z
./noncirc-setlevel-answer.md:621:./route-choice-answer.md:527:./DLNFibre/Core/DeterminantalStratumDim.lean:249:  -- `hbridge : (n−r)(m−r) + varietyDim Z = m·n`
./noncirc-setlevel-answer.md:622:./route-choice-answer.md:528:./DLNFibre/Core/DeterminantalStratumDim.lean:258:  have heq : (((n - r) * (m - r) : ℕ) : ℕ∞) + varietyDim (canonicalCoord (dStratum n m) '' Z)
./noncirc-setlevel-answer.md:623:./route-choice-answer.md:529:./DLNFibre/Core/DeterminantalStratumDim.lean:268:    varietyDim (canonicalCoord (dStratum 2 2) '' productRankLocusLE (k := k) (dStratum 2 2) 1)
./noncirc-setlevel-answer.md:624:./route-choice-answer.md:530:./DLNFibre/Core/DeterminantalStratumDim.lean:270:  have h := varietyDim_productRankLocusLE_stratum (k := k) 2 2 1 (by norm_num) (by norm_num)
./noncirc-setlevel-answer.md:625:./route-choice-answer.md:546:./DLNFibre/Core/DeepChartRing.lean:133:`sigmaIdeal` is radical (`vanishingIdeal_isRadical`, over `[IsAlgClosed k]`) and localization
./noncirc-setlevel-answer.md:626:./route-choice-answer.md:577:./DLNFibre/Core/FibreDimFibration.lean:45:`varietyDim = δ`, lifting the `unbotD 0` to the genuine `WithBot ℕ∞` value (the quotient is
./noncirc-setlevel-answer.md:627:./route-choice-answer.md:578:./DLNFibre/Core/FibreDimFibration.lean:51:The thermometer `varietyDim_productRankLocusLE_stratum` gives the `ℕ∞`-via-`unbotD` value; this lifts
./noncirc-setlevel-answer.md:628:./route-choice-answer.md:579:./DLNFibre/Core/FibreDimFibration.lean:54:theorem ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta [IsAlgClosed k] [CharZero k]
./noncirc-setlevel-answer.md:629:./route-choice-answer.md:585:./DLNFibre/Core/FibreDimFibration.lean:64:  -- the thermometer: `varietyDim = δ`, i.e. `(ringKrullDim (R ⧸ I)).unbotD 0 = δ`.
./noncirc-setlevel-answer.md:630:./route-choice-answer.md:586:./DLNFibre/Core/FibreDimFibration.lean:65:  have hvd : varietyDim (canonicalCoord (dStratum n m) ''
./noncirc-setlevel-answer.md:631:./route-choice-answer.md:588:./DLNFibre/Core/FibreDimFibration.lean:67:    varietyDim_productRankLocusLE_stratum n m r hn hm
./noncirc-setlevel-answer.md:632:./route-choice-answer.md:589:./DLNFibre/Core/FibreDimFibration.lean:68:  rw [varietyDim, ← hI] at hvd
./noncirc-setlevel-answer.md:633:./route-choice-answer.md:597:./DLNFibre/Core/FibreDimFibration.lean:102:    ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta n m r hn hm]
./noncirc-setlevel-answer.md:634:./route-choice-answer.md:605:./DLNFibre/Core/EndBaseChangeSweep.lean:16:consequence** `varietyDim (productRankLocus d r) = δ + varietyDim (fibre d E)` is the *one genuinely
./noncirc-setlevel-answer.md:635:./route-choice-answer.md:637:./DLNFibre/Core/FibreHeightDirect.lean:11:`fibreGenIdeal d B` (`Core.MultComorphism.vanishingIdeal_image_fibre_eq_radical`). The point of this
./noncirc-setlevel-answer.md:636:./route-choice-answer.md:639:./DLNFibre/Core/FibreHeightDirect.lean:47:(definition of `codimRepCanonical`/`codimRep`); `vanishingIdeal (…) = (fibreGenIdeal d B).radical`
./noncirc-setlevel-answer.md:637:./route-choice-answer.md:640:./DLNFibre/Core/FibreHeightDirect.lean:48:(`vanishingIdeal_image_fibre_eq_radical`, the Nullstellensatz); `(radical I).height = I.height`
./noncirc-setlevel-answer.md:638:./route-choice-answer.md:641:./DLNFibre/Core/FibreHeightDirect.lean:54:  rw [codimRepCanonical, codimRep, vanishingIdeal_image_fibre_eq_radical, Ideal.height_radical]
./noncirc-setlevel-answer.md:639:./route-choice-answer.md:643:./DLNFibre/Core/NullstellensatzCodim.lean:20:   Nullstellensatz over `[IsAlgClosed k]`): `vanishingIdeal Z` is always **radical**
./noncirc-setlevel-answer.md:640:./route-choice-answer.md:649:./DLNFibre/Core/NullstellensatzCodim.lean:31:   irreducible"), `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ` (`ℕ∞`, additive — `ℕ∞`
./noncirc-setlevel-answer.md:641:./route-choice-answer.md:650:./DLNFibre/Core/NullstellensatzCodim.lean:37:`axiom`. `varietyDim Z = ringKrullDim (R ⧸ vanishingIdeal Z)` is the Krull dimension of the
./noncirc-setlevel-answer.md:642:./route-choice-answer.md:652:./DLNFibre/Core/NullstellensatzCodim.lean:67:strong Nullstellensatz it equals its own radical, via `vanishingIdeal Z = vanishingIdeal (zeroLocus
./noncirc-setlevel-answer.md:643:./route-choice-answer.md:653:./DLNFibre/Core/NullstellensatzCodim.lean:68:(vanishingIdeal Z))` `= (vanishingIdeal Z).radical`. -/
./noncirc-setlevel-answer.md:644:./route-choice-answer.md:656:./DLNFibre/Core/NullstellensatzCodim.lean:71:  have h : vanishingIdeal k Z = (vanishingIdeal k Z).radical := by
./noncirc-setlevel-answer.md:645:./route-choice-answer.md:658:./DLNFibre/Core/NullstellensatzCodim.lean:74:        vanishingIdeal_zeroLocus_eq_radical (K := k)]
./noncirc-setlevel-answer.md:646:./route-choice-answer.md:664:./DLNFibre/Core/NullstellensatzCodim.lean:87:Nullstellensatz forces `vanishingIdeal (zeroLocus (vanishingIdeal Z)) = (vanishingIdeal Z).radical`,
./noncirc-setlevel-answer.md:649:/bin/bash -lc 'rg -n "ringKrullDim_quotient|quotient.*radical|radical.*quotient|height_radical|prod|union|TensorProduct|trdeg_add|dimension" noncirc-setlevel-answer.md route-choice-answer.md | head -300' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
./noncirc-setlevel-answer.md:656:route-choice-answer.md:46:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./noncirc-setlevel-answer.md:665:route-choice-answer.md:114:./route-choice-prompt.md:31:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./noncirc-setlevel-answer.md:669:route-choice-answer.md:129:./route-choice-answer.md:46:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./noncirc-setlevel-answer.md:678:route-choice-answer.md:209:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./noncirc-setlevel-answer.md:687:route-choice-answer.md:277:./route-choice-prompt.md:31:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./noncirc-setlevel-answer.md:691:route-choice-answer.md:292:./route-choice-answer.md:46:   `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`). `trdeg_add_eq`
./noncirc-setlevel-answer.md:695:route-choice-answer.md:325:/bin/bash -lc 'rg -n "Noether.*Norm|Noetherian.*Norm|normalization|GenericFreeness|generic freeness|height_eq_under|FlatQuasiFinite|HasGoingDown|trdeg_add_eq|rankLocus|productRankLocus|varietyDim|vanishingIdeal" -S .' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean
./noncirc-setlevel-answer.md:710:route-choice-answer.md:475:./DLNFibre/Core/OrbitPullbackDim.lean:52:theorem varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker [Infinite k]
./noncirc-setlevel-answer.md:711:route-choice-answer.md:479:./DLNFibre/Core/OrbitPullbackDim.lean:70:transcendence degree. Combines `varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker` with the
./noncirc-setlevel-answer.md:712:route-choice-answer.md:482:./DLNFibre/Core/OrbitPullbackDim.lean:78:  rw [varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker M,
./noncirc-setlevel-answer.md:727:route-choice-answer.md:512:./DLNFibre/Core/DeterminantalStratumDim.lean:196:flattening of) `productRankLocusLE ![n,m] r` is prime — it is `vanishingIdeal (Ō_{M₀})` of a single
./noncirc-setlevel-answer.md:728:route-choice-answer.md:514:./DLNFibre/Core/DeterminantalStratumDim.lean:198:theorem isPrime_vanishingIdeal_productRankLocusLE_stratum [IsAlgClosed k] (n m r : ℕ)
./noncirc-setlevel-answer.md:732:route-choice-answer.md:521:./DLNFibre/Core/DeterminantalStratumDim.lean:229:theorem varietyDim_productRankLocusLE_stratum [IsAlgClosed k] [CharZero k] (n m r : ℕ)
./noncirc-setlevel-answer.md:733:route-choice-answer.md:522:./DLNFibre/Core/DeterminantalStratumDim.lean:231:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./noncirc-setlevel-answer.md:735:route-choice-answer.md:525:./DLNFibre/Core/DeterminantalStratumDim.lean:238:    (isPrime_vanishingIdeal_productRankLocusLE_stratum (k := k) n m r hn hm)
./noncirc-setlevel-answer.md:737:route-choice-answer.md:529:./DLNFibre/Core/DeterminantalStratumDim.lean:268:    varietyDim (canonicalCoord (dStratum 2 2) '' productRankLocusLE (k := k) (dStratum 2 2) 1)
./noncirc-setlevel-answer.md:738:route-choice-answer.md:530:./DLNFibre/Core/DeterminantalStratumDim.lean:270:  have h := varietyDim_productRankLocusLE_stratum (k := k) 2 2 1 (by norm_num) (by norm_num)
./noncirc-setlevel-answer.md:739:route-choice-answer.md:550:./DLNFibre/Core/DeepChartRing.lean:239:  rw [mem_productRankLocusLE] at hA
./noncirc-setlevel-answer.md:740:route-choice-answer.md:552:./DLNFibre/Core/DeepChartRing.lean:244:    rw [mem_productRankLocusLE, mult_singleTuple]; exact hA, rfl⟩
./noncirc-setlevel-answer.md:755:route-choice-answer.md:578:./DLNFibre/Core/FibreDimFibration.lean:51:The thermometer `varietyDim_productRankLocusLE_stratum` gives the `ℕ∞`-via-`unbotD` value; this lifts
./noncirc-setlevel-answer.md:756:route-choice-answer.md:579:./DLNFibre/Core/FibreDimFibration.lean:54:theorem ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta [IsAlgClosed k] [CharZero k]
./noncirc-setlevel-answer.md:759:route-choice-answer.md:584:./DLNFibre/Core/FibreDimFibration.lean:63:    isPrime_vanishingIdeal_productRankLocusLE_stratum (k := k) n m r hn hm
./noncirc-setlevel-answer.md:761:route-choice-answer.md:588:./DLNFibre/Core/FibreDimFibration.lean:67:    varietyDim_productRankLocusLE_stratum n m r hn hm
./noncirc-setlevel-answer.md:762:route-choice-answer.md:590:./DLNFibre/Core/FibreDimFibration.lean:89:vanishingIdeal(…)` has height `δ = r(n + m − r)` — equidimensionality at a closed point of the
./noncirc-setlevel-answer.md:765:route-choice-answer.md:596:./DLNFibre/Core/FibreDimFibration.lean:100:    isPrime_vanishingIdeal_productRankLocusLE_stratum (k := k) n m r hn hm
./noncirc-setlevel-answer.md:766:route-choice-answer.md:597:./DLNFibre/Core/FibreDimFibration.lean:102:    ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta n m r hn hm]
./noncirc-setlevel-answer.md:768:route-choice-answer.md:605:./DLNFibre/Core/EndBaseChangeSweep.lean:16:consequence** `varietyDim (productRankLocus d r) = δ + varietyDim (fibre d E)` is the *one genuinely
./noncirc-setlevel-answer.md:780:route-choice-answer.md:631:./DLNFibre/Core/DeterminantalBasePresentation.lean:341:    rw [sigmaIdeal]; exact isPrime_vanishingIdeal_productRankLocusLE_stratum q p r hq hp
./noncirc-setlevel-answer.md:781:route-choice-answer.md:641:./DLNFibre/Core/FibreHeightDirect.lean:54:  rw [codimRepCanonical, codimRep, vanishingIdeal_image_fibre_eq_radical, Ideal.height_radical]
./noncirc-setlevel-answer.md:782:route-choice-answer.md:650:./DLNFibre/Core/NullstellensatzCodim.lean:37:`axiom`. `varietyDim Z = ringKrullDim (R ⧸ vanishingIdeal Z)` is the Krull dimension of the
./noncirc-setlevel-answer.md:783:route-choice-answer.md:676:./DLNFibre/Core/NullstellensatzCodim.lean:143:`(vanishingIdeal Z).IsPrime` — the height of its vanishing ideal plus its variety dimension equals
./noncirc-setlevel-answer.md:784:route-choice-answer.md:677:./DLNFibre/Core/NullstellensatzCodim.lean:144:the ambient dimension `Nat.card σ`: `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ`. The
./noncirc-setlevel-answer.md:785:route-choice-answer.md:678:./DLNFibre/Core/NullstellensatzCodim.lean:145:catenary identity over `σ`, read at the prime `vanishingIdeal Z`. Geometric codimension `=` ambient
./noncirc-setlevel-answer.md:786:route-choice-answer.md:682:./DLNFibre/Core/NullstellensatzCodim.lean:150:  have key := height_add_ringKrullDim_quotient_eq_card (vanishingIdeal k Z)
./noncirc-setlevel-answer.md:787:route-choice-answer.md:688:./DLNFibre/Core/NullstellensatzCodim.lean:163:subtraction; lossless here since `varietyDim Z ≤ Nat.card σ`). The geometric codimension is the
./noncirc-setlevel-answer.md:788:route-choice-answer.md:699:./DLNFibre/Core/NullstellensatzCodim.lean:190:varietyDim (coord '' Z)` for an irreducible variety `coord '' Z`: geometric codimension `=` ambient
./noncirc-setlevel-answer.md:832:route-choice-answer.md:813:./DLNFibre/Core/PolynomialDimension.lean:18:* **L5.5** `ringKrullDim_quotient_eq_noetherRank` — `dim (R ⧸ p)` equals the Noether-normalization
./noncirc-setlevel-answer.md:834:route-choice-answer.md:820:./DLNFibre/Core/OrbitDifferentialRank.lean:35:Krull-dimension bound) and `varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional`
./noncirc-setlevel-answer.md:841:route-choice-answer.md:834:./DLNFibre/Core/DeterminantalChartRing.lean:367:    rw [sigmaIdeal]; exact isPrime_vanishingIdeal_productRankLocusLE_stratum q p r hq hp
./noncirc-setlevel-answer.md:846:route-choice-answer.md:853:./DLNFibre/Core/RadicalCatenary.lean:176:equal the ambient dimension: `codimRepCanonical Z + varietyDim (canonicalCoord d '' Z) = card`. No
./noncirc-setlevel-answer.md:870:route-choice-answer.md:939:./DLNFibre/Core/FibreDimFibrationProbe.lean:37:/-- LANDED: the determinantal-stratum dimension `varietyDim (Mat^{≤r}) = r(n+m−r) = δ`. -/
./noncirc-setlevel-answer.md:871:route-choice-answer.md:940:./DLNFibre/Core/FibreDimFibrationProbe.lean:39:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./noncirc-setlevel-answer.md:872:route-choice-answer.md:941:./DLNFibre/Core/FibreDimFibrationProbe.lean:41:  varietyDim_productRankLocusLE_stratum n m r hn hm
./noncirc-setlevel-answer.md:877:route-choice-answer.md:951:./DLNFibre/Core/FibreDimFibrationProbe.lean:91:  isPrime_vanishingIdeal_productRankLocusLE_stratum (d 0) (d (Fin.last N)) r hq hp
./noncirc-setlevel-answer.md:879:route-choice-answer.md:960:./DLNFibre/Core/SigmaComponents.lean:20:  the finite family of prime orbit ideals (G2 + `vanishingIdeal` turns unions into infs), so its
./noncirc-setlevel-answer.md:882:route-choice-answer.md:969:./DLNFibre/Core/SigmaComponents.lean:136:orbit-ideal family: `vanishingIdeal` turns the G2 union `Σ̄^r = ⋃_M Ō_M` into an intersection. -/
./noncirc-setlevel-answer.md:895:route-choice-answer.md:1086:./DLNFibre/Core/RouteCAssembly.lean:50:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./noncirc-setlevel-answer.md:896:route-choice-answer.md:1088:./DLNFibre/Core/RouteCAssembly.lean:53:    (hClosure : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./noncirc-setlevel-answer.md:897:route-choice-answer.md:1089:./DLNFibre/Core/RouteCAssembly.lean:54:        = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r))
./noncirc-setlevel-answer.md:899:route-choice-answer.md:1092:./DLNFibre/Core/RouteCAssembly.lean:58:        + varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
./noncirc-setlevel-answer.md:902:route-choice-answer.md:1095:./DLNFibre/Core/RouteCAssembly.lean:67:  have hdimSigma : varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
./noncirc-setlevel-answer.md:904:route-choice-answer.md:1106:./DLNFibre/Core/RouteCAssembly.lean:107:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./noncirc-setlevel-answer.md:905:route-choice-answer.md:1108:./DLNFibre/Core/RouteCAssembly.lean:110:    (hClosure : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./noncirc-setlevel-answer.md:906:route-choice-answer.md:1109:./DLNFibre/Core/RouteCAssembly.lean:111:        = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)) :
./noncirc-setlevel-answer.md:915:route-choice-answer.md:1165:/-! ## The base-stratum Krull dimension brick: `ringKrullDim O(Mat^{≤r}) = δ`
./noncirc-setlevel-answer.md:919:route-choice-answer.md:1175:/-- **The base-stratum Krull dimension** `ringKrullDim O(Mat^{≤r}) = δ`. For `r ≤ n`, `r ≤ m`, over an
./noncirc-setlevel-answer.md:921:route-choice-answer.md:1178:The thermometer `varietyDim_productRankLocusLE_stratum` gives the `ℕ∞`-via-`unbotD` value; this lifts
./noncirc-setlevel-answer.md:923:route-choice-answer.md:1181:theorem ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta [IsAlgClosed k] [CharZero k]
./noncirc-setlevel-answer.md:926:route-choice-answer.md:1190:    isPrime_vanishingIdeal_productRankLocusLE_stratum (k := k) n m r hn hm
./noncirc-setlevel-answer.md:928:route-choice-answer.md:1194:    varietyDim_productRankLocusLE_stratum n m r hn hm
./noncirc-setlevel-answer.md:929:route-choice-answer.md:1209:By equidimensionality at a closed point (`OrbitTangentCotangent.height_eq_ringKrullDim_of_isMaximal_fintype`,
./noncirc-setlevel-answer.md:931:route-choice-answer.md:1216:vanishingIdeal(…)` has height `δ = r(n + m − r)` — equidimensionality at a closed point of the
./noncirc-setlevel-answer.md:934:route-choice-answer.md:1227:    isPrime_vanishingIdeal_productRankLocusLE_stratum (k := k) n m r hn hm
./noncirc-setlevel-answer.md:935:route-choice-answer.md:1229:    ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta n m r hn hm]
./noncirc-setlevel-answer.md:937:route-choice-answer.md:1233:`affine_domain_height_add_ringKrullDim_quotient_eq` is over `MvPolynomial (Fin n) k`. Transport it to
./noncirc-setlevel-answer.md:939:route-choice-answer.md:1242:`affine_domain_height_add_ringKrullDim_quotient_eq` through `renameEquiv` and the induced quotient
./noncirc-setlevel-answer.md:940:route-choice-answer.md:1244:theorem affine_domain_height_add_ringKrullDim_quotient_eq_fintype {σ : Type*} [Finite σ]
./noncirc-setlevel-answer.md:941:route-choice-answer.md:1260:  have hL := affine_domain_height_add_ringKrullDim_quotient_eq k (Fintype.card σ) J p'
./noncirc-setlevel-answer.md:942:route-choice-answer.md:1263:    ringKrullDim_quotient_map_algEquiv Φ p, hJ, ringKrullDim_quotient_map_algEquiv e I] at hL
./noncirc-setlevel-answer.md:946:route-choice-answer.md:1303:/-- LANDED: the determinantal-stratum dimension `varietyDim (Mat^{≤r}) = r(n+m−r) = δ`. -/
./noncirc-setlevel-answer.md:947:route-choice-answer.md:1305:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./noncirc-setlevel-answer.md:948:route-choice-answer.md:1307:  varietyDim_productRankLocusLE_stratum n m r hn hm
./noncirc-setlevel-answer.md:953:I found that this directory captured a previous Codex run, but it mostly records repository facts rather than proving the new claim. I’m checking upstream Mathlib now for `ringKrullDim`, quotient, and tensor/product APIs.
./noncirc-setlevel-answer.md:955:web search: site:github.com/leanprover-community/mathlib4 ringKrullDim quotient radical mathlib4
./noncirc-setlevel-answer.md:957:web search: Mathlib RingTheory KrullDimension ringKrullDim radical
./noncirc-setlevel-answer.md:980:/bin/bash -lc 'rg -n "theorem .*radical|ringKrullDim.*radical|radical.*ringKrullDim|height_radical|quotient.*radical|PrimeSpectrum.*quotient|OrderIso.*prime|comap.*radical" /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory -S | head -300' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
./noncirc-setlevel-answer.md:994:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:858:    vanishingIdeal (Set.range (comap f)) = (RingHom.ker f).radical := by
./noncirc-setlevel-answer.md:996:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:867:  rw [← zeroLocus_vanishingIdeal_eq_closure, vanishingIdeal_range_comap, zeroLocus_radical]
./noncirc-setlevel-answer.md:1022:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Basic.lean:210:theorem vanishingIdeal_zeroLocus_eq_radical (I : Ideal R) :
./noncirc-setlevel-answer.md:1024:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Basic.lean:219:@[simp] theorem vanishingIdeal_univ : vanishingIdeal Set.univ = nilradical R := by
./noncirc-setlevel-answer.md:1043:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:15:The main statement of the theorem is `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`.
./noncirc-setlevel-answer.md:1044:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:113:theorem radical_le_vanishingIdeal_zeroLocus (I : Ideal (MvPolynomial σ k)) :
./noncirc-setlevel-answer.md:1045:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:171:theorem vanishingIdeal_zeroLocus_eq_radical (I : Ideal (MvPolynomial σ k)) :
./noncirc-setlevel-answer.md:1090:/bin/bash -lc 'rg -n "ringKrullDim.*TensorProduct|TensorProduct.*ringKrullDim|varietyDim.*prod|zeroLocus.*prod|vanishingIdeal.*union|iSup|iInf|sup.*vanishing|trdeg.*TensorProduct|TensorProduct.*trdeg" /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib -S | head -300' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
./noncirc-setlevel-answer.md:1259:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Functorial.lean:170:  · rw [map, ← le_support_iff_le_vanishingIdeal, TopologicalSpace.Closeds.closure_le]
./noncirc-setlevel-answer.md:1260:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Functorial.lean:173:      range_subschemeι, coe_support_vanishingIdeal]
./noncirc-setlevel-answer.md:1261:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Functorial.lean:174:  · simp [le_map_iff_comap_le, ← le_support_iff_le_vanishingIdeal, ← Set.image_subset_iff,
./noncirc-setlevel-answer.md:1263:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:32:  `support` and `vanishingIdeal` forms a Galois connection.
./noncirc-setlevel-answer.md:1277:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:612:lemma le_support_iff_le_vanishingIdeal {I : X.IdealSheafData} {Z : Closeds X} :
./noncirc-setlevel-answer.md:1278:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:613:    Z ≤ I.support ↔ I ≤ vanishingIdeal Z := by
./noncirc-setlevel-answer.md:1279:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:625:/-- `support` and `vanishingIdeal` forms a Galois connection.
./noncirc-setlevel-answer.md:1280:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:627:lemma gc : @GaloisConnection X.IdealSheafData (Closeds X)ᵒᵈ _ _ (support ·) (vanishingIdeal ·) :=
./noncirc-setlevel-answer.md:1281:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:628:  fun _ _ ↦ le_support_iff_le_vanishingIdeal
./noncirc-setlevel-answer.md:1282:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:648:  rw [← support_bot, vanishingIdeal_support, nilradical]
./noncirc-setlevel-answer.md:1283:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:650:@[simp] lemma vanishingIdeal_iSup {ι : Sort*} (Z : ι → Closeds X) :
./noncirc-setlevel-answer.md:1284:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:651:    vanishingIdeal (iSup Z) = ⨅ i, vanishingIdeal (Z i) := gc.u_iInf
./noncirc-setlevel-answer.md:1287:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:680:  rw [← top_le_iff, le_support_iff_le_vanishingIdeal,
./noncirc-setlevel-answer.md:1427:noncomputable def ringKrullDim (R : Type*) [CommSemiring R] : WithBot ℕ∞ :=
./noncirc-setlevel-answer.md:1437:    KrullDimLE n R ↔ ringKrullDim R ≤ n := Order.krullDimLE_iff n (PrimeSpectrum R)
./noncirc-setlevel-answer.md:1440:lemma ringKrullDim_eq_bot_of_subsingleton [Subsingleton R] :
./noncirc-setlevel-answer.md:1441:    ringKrullDim R = ⊥ :=
./noncirc-setlevel-answer.md:1444:lemma ringKrullDim_nonneg_of_nontrivial [Nontrivial R] :
./noncirc-setlevel-answer.md:1445:    0 ≤ ringKrullDim R :=
./noncirc-setlevel-answer.md:1448:/-- If `f : R →+* S` is surjective, then `ringKrullDim S ≤ ringKrullDim R`. -/
./noncirc-setlevel-answer.md:1449:theorem ringKrullDim_le_of_surjective (f : R →+* S) (hf : Function.Surjective f) :
./noncirc-setlevel-answer.md:1450:    ringKrullDim S ≤ ringKrullDim R :=
./noncirc-setlevel-answer.md:1456:/-- If `I` is an ideal of `R`, then `ringKrullDim (R ⧸ I) ≤ ringKrullDim R`. -/
./noncirc-setlevel-answer.md:1457:theorem ringKrullDim_quotient_le {R : Type*} [CommRing R] (I : Ideal R) :
./noncirc-setlevel-answer.md:1458:    ringKrullDim (R ⧸ I) ≤ ringKrullDim R :=
./noncirc-setlevel-answer.md:1459:  ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective
./noncirc-setlevel-answer.md:1461:/-- If `R` and `S` are isomorphic, then `ringKrullDim R = ringKrullDim S`. -/
./noncirc-setlevel-answer.md:1462:theorem ringKrullDim_eq_of_ringEquiv (e : R ≃+* S) :
./noncirc-setlevel-answer.md:1463:    ringKrullDim R = ringKrullDim S :=
./noncirc-setlevel-answer.md:1464:  le_antisymm (ringKrullDim_le_of_surjective e.symm e.symm.surjective)
./noncirc-setlevel-answer.md:1465:    (ringKrullDim_le_of_surjective e e.surjective)
./noncirc-setlevel-answer.md:1467:alias RingEquiv.ringKrullDim := ringKrullDim_eq_of_ringEquiv
./noncirc-setlevel-answer.md:1474:lemma ringKrullDim_ne_top [FiniteRingKrullDim R] :
./noncirc-setlevel-answer.md:1475:    ringKrullDim R ≠ ⊤ := krullDim_ne_top_of_finiteDimensionalOrder
./noncirc-setlevel-answer.md:1477:lemma ringKrullDim_lt_top [FiniteRingKrullDim R] :
./noncirc-setlevel-answer.md:1478:    ringKrullDim R < ⊤ := ringKrullDim_ne_top.lt_top
./noncirc-setlevel-answer.md:1480:lemma ringKrullDim_ne_bot [FiniteRingKrullDim R] :
./noncirc-setlevel-answer.md:1481:    ringKrullDim R ≠ ⊥ := krullDim_ne_bot_of_finiteDimensionalOrder
./noncirc-setlevel-answer.md:1484:    FiniteRingKrullDim R ↔ (ringKrullDim R ≠ ⊥ ∧ ringKrullDim R ≠ ⊤) :=
./noncirc-setlevel-answer.md:1491:proof_wanted MvPolynomial.fin_ringKrullDim_eq_add_of_isNoetherianRing
./noncirc-setlevel-answer.md:1493:    ringKrullDim (MvPolynomial (Fin n) R) = ringKrullDim R + n
./noncirc-setlevel-answer.md:1581:/bin/bash -lc 'rg -n "def ringKrullDim|theorem ringKrullDim|lemma ringKrullDim|ringKrullDim_quotient|orderIso|PrimeSpectrum.*quotient|quotient.*PrimeSpectrum|comap.*quotient" /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Algebra/Order -S | head -500' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
./noncirc-setlevel-answer.md:1638:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:343:lemma height_le_ringKrullDim_quotient_add_spanFinrank {p I : Ideal R} [p.IsPrime] (h : I ≤ p) :
./noncirc-setlevel-answer.md:1639:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:352:lemma ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank (I : Ideal R)
./noncirc-setlevel-answer.md:1640:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:358:  exact height_le_ringKrullDim_quotient_add_spanFinrank <|
./noncirc-setlevel-answer.md:1641:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:370:lemma Ideal.height_le_ringKrullDim_quotient_add_encard {p : Ideal R} [p.IsPrime]
./noncirc-setlevel-answer.md:1642:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:372:  refine le_trans (height_le_ringKrullDim_quotient_add_spanFinrank (I := .span s) ?_) ?_
./noncirc-setlevel-answer.md:1643:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:381:lemma Ideal.height_le_ringKrullDim_quotient_add_one {r : R} {p : Ideal R} [p.IsPrime]
./noncirc-setlevel-answer.md:1644:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:383:  convert Ideal.height_le_ringKrullDim_quotient_add_encard {r} (by simpa)
./noncirc-setlevel-answer.md:1645:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:386:lemma ringKrullDim_le_ringKrullDim_quotient_add_encard (s : Set R) (hs : s ⊆ Ring.jacobson R) :
./noncirc-setlevel-answer.md:1646:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:388:  refine le_trans (ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank (Ideal.span s) ?_) ?_
./noncirc-setlevel-answer.md:1647:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:392:lemma ringKrullDim_le_ringKrullDim_quotient_add_card (s : Finset R)
./noncirc-setlevel-answer.md:1648:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:395:  convert ringKrullDim_le_ringKrullDim_quotient_add_encard s hs
./noncirc-setlevel-answer.md:1649:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:474:lemma ringKrullDim_le_spanFinrank_maximalIdeal [IsLocalRing R] :
./noncirc-setlevel-answer.md:1664:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Height.lean:294:lemma ringKrullDim_le_iff_height_le {R : Type*} [CommRing R] (n : WithBot ℕ∞) :
./noncirc-setlevel-answer.md:1665:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Height.lean:304:lemma ringKrullDim_le_iff_isMaximal_height_le {R : Type*} [CommRing R] (n : WithBot ℕ∞) :
./noncirc-setlevel-answer.md:1668:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/NatInt.lean:95:theorem ringKrullDim_nat : ringKrullDim ℕ = 2 := by
./noncirc-setlevel-answer.md:1670:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Zero.lean:53:lemma ringKrullDimZero_iff_ringKrullDim_eq_zero [Nontrivial R] :
./noncirc-setlevel-answer.md:1674:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/LocalRing.lean:20:lemma ringKrullDim_eq_one_iff_of_isLocalRing_isDomain {R : Type*}
./noncirc-setlevel-answer.md:1676:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/OrderOfVanishing.lean:167:  exact (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hx).trans (Order.KrullDimLE.krullDim_le)
./noncirc-setlevel-answer.md:1680:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:20:- `ringKrullDim_quotient_succ_le_of_nonZeroDivisor`: If `r` is not a zero divisor, then
./noncirc-setlevel-answer.md:1681:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:32:lemma ringKrullDim_quotient (I : Ideal R) :
./noncirc-setlevel-answer.md:1682:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:34:  rw [ringKrullDim, Order.krullDim_eq_of_orderIso I.primeSpectrumQuotientOrderIsoZeroLocus]
./noncirc-setlevel-answer.md:1683:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:36:lemma ringKrullDim_quotient_succ_le_of_nonZeroDivisor
./noncirc-setlevel-answer.md:1684:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:47:  rw [ringKrullDim_quotient, Order.krullDim_eq_iSup_length, ringKrullDim,
./noncirc-setlevel-answer.md:1685:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:60:lemma ringKrullDim_succ_le_of_surjective (f : R →+* S) (hf : Function.Surjective f)
./noncirc-setlevel-answer.md:1686:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:62:  refine le_trans ?_ (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr)
./noncirc-setlevel-answer.md:1687:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:68:lemma ringKrullDim_succ_le_ringKrullDim_polynomial :
./noncirc-setlevel-answer.md:1688:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:75:lemma ringKrullDim_mvPolynomial_of_isEmpty (σ : Type*) [IsEmpty σ] :
./noncirc-setlevel-answer.md:1689:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:80:lemma ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial (σ : Type*) [Finite σ] :
./noncirc-setlevel-answer.md:1690:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:96:lemma ringKrullDim_add_enatCard_le_ringKrullDim_mvPolynomial (σ : Type*) :
./noncirc-setlevel-answer.md:1691:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:120:lemma ringKrullDim_succ_le_ringKrullDim_powerseries :
./noncirc-setlevel-answer.md:1692:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Field.lean:21:theorem ringKrullDim_eq_zero_of_field (F : Type*) [Field F] : ringKrullDim F = 0 :=
./noncirc-setlevel-answer.md:1693:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Field.lean:24:theorem ringKrullDim_eq_zero_of_isField {F : Type*} [CommRing F] (hF : IsField F) :
./noncirc-setlevel-answer.md:1694:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:120:lemma _root_.ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_jacobson {x : R}
./noncirc-setlevel-answer.md:1695:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:129:lemma ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors {r : R} (hr : r ∈ nonZeroDivisors R)
./noncirc-setlevel-answer.md:1696:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:132:  refine le_antisymm (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr) (h ▸ ?_)
./noncirc-setlevel-answer.md:1697:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:133:  exact Ideal.height_le_ringKrullDim_quotient_add_one hp
./noncirc-setlevel-answer.md:1698:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:149:@[deprecated ringKrullDim_le_ringKrullDim_quotient_add_card (since := "2026-01-12")]
./noncirc-setlevel-answer.md:1699:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:153:  apply ringKrullDim_le_ringKrullDim_quotient_add_card
./noncirc-setlevel-answer.md:1700:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:156:@[deprecated ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank (since := "2026-01-12")]
./noncirc-setlevel-answer.md:1701:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:159:  apply ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank
./noncirc-setlevel-answer.md:1702:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:179:lemma _root_.ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim {x : R}
./noncirc-setlevel-answer.md:1703:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:182:  ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_jacobson reg <| by
./noncirc-setlevel-answer.md:1704:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:187:lemma _root_.ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
./noncirc-setlevel-answer.md:1705:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:190:  ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim
./noncirc-setlevel-answer.md:1706:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Module.lean:49:lemma supportDim_eq_ringKrullDim_quotient_annihilator [Module.Finite R M] :
./noncirc-setlevel-answer.md:1707:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Module.lean:52:  rw [support_eq_zeroLocus, ringKrullDim_quotient]
./noncirc-setlevel-answer.md:1708:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Module.lean:57:  rw [supportDim_eq_ringKrullDim_quotient_annihilator, this]
./noncirc-setlevel-answer.md:1709:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Module.lean:67:  rw [supportDim_eq_ringKrullDim_quotient_annihilator, Ideal.annihilator_quotient]
./noncirc-setlevel-answer.md:1710:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Basic.lean:30:noncomputable def ringKrullDim (R : Type*) [CommSemiring R] : WithBot ℕ∞ :=
./noncirc-setlevel-answer.md:1711:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Basic.lean:43:lemma ringKrullDim_eq_bot_of_subsingleton [Subsingleton R] :
./noncirc-setlevel-answer.md:1712:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Basic.lean:47:lemma ringKrullDim_nonneg_of_nontrivial [Nontrivial R] :
./noncirc-setlevel-answer.md:1713:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Basic.lean:52:theorem ringKrullDim_le_of_surjective (f : R →+* S) (hf : Function.Surjective f) :
./noncirc-setlevel-answer.md:1714:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Basic.lean:60:theorem ringKrullDim_quotient_le {R : Type*} [CommRing R] (I : Ideal R) :
./noncirc-setlevel-answer.md:1715:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Basic.lean:65:theorem ringKrullDim_eq_of_ringEquiv (e : R ≃+* S) :
./noncirc-setlevel-answer.md:1716:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Basic.lean:77:lemma ringKrullDim_ne_top [FiniteRingKrullDim R] :
./noncirc-setlevel-answer.md:1717:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Basic.lean:80:lemma ringKrullDim_lt_top [FiniteRingKrullDim R] :
./noncirc-setlevel-answer.md:1718:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Basic.lean:83:lemma ringKrullDim_ne_bot [FiniteRingKrullDim R] :
./noncirc-setlevel-answer.md:1724:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Polynomial.lean:106:lemma ringKrullDim_of_isNoetherianRing : ringKrullDim R[X] = ringKrullDim R + 1 := by
./noncirc-setlevel-answer.md:1741:The key upstream fact is present, but under a slightly different route: `ringKrullDim_quotient` identifies the quotient dimension with the Krull dimension of the corresponding zero-locus in `Spec`, and `zeroLocus_radical` then gives radical-insensitivity. I’m checking whether there is a one-line wrapper already named for radicals.
./noncirc-setlevel-answer.md:1764:- `ringKrullDim_quotient_succ_le_of_nonZeroDivisor`: If `r` is not a zero divisor, then
./noncirc-setlevel-answer.md:1766:- `ringKrullDim_succ_le_ringKrullDim_polynomial`: `dim R + 1 ≤ dim R[X]`.
./noncirc-setlevel-answer.md:1767:- `ringKrullDim_add_enatCard_le_ringKrullDim_mvPolynomial`: `dim R + #σ ≤ dim R[σ]`.
./noncirc-setlevel-answer.md:1776:lemma ringKrullDim_quotient (I : Ideal R) :
./noncirc-setlevel-answer.md:1777:    ringKrullDim (R ⧸ I) = Order.krullDim (PrimeSpectrum.zeroLocus (R := R) I) := by
./noncirc-setlevel-answer.md:1778:  rw [ringKrullDim, Order.krullDim_eq_of_orderIso I.primeSpectrumQuotientOrderIsoZeroLocus]
./noncirc-setlevel-answer.md:1780:lemma ringKrullDim_quotient_succ_le_of_nonZeroDivisor
./noncirc-setlevel-answer.md:1782:    ringKrullDim (R ⧸ Ideal.span {r}) + 1 ≤ ringKrullDim R := by
./noncirc-setlevel-answer.md:1784:  · rw [hr', ringKrullDim_eq_bot_of_subsingleton]
./noncirc-setlevel-answer.md:1791:  rw [ringKrullDim_quotient, Order.krullDim_eq_iSup_length, ringKrullDim,
./noncirc-setlevel-answer.md:1804:lemma ringKrullDim_succ_le_of_surjective (f : R →+* S) (hf : Function.Surjective f)
./noncirc-setlevel-answer.md:1805:    {r : R} (hr : r ∈ R⁰) (hr' : f r = 0) : ringKrullDim S + 1 ≤ ringKrullDim R := by
./noncirc-setlevel-answer.md:1806:  refine le_trans ?_ (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr)
./noncirc-setlevel-answer.md:1808:  exact ringKrullDim_le_of_surjective (Ideal.Quotient.lift _ f (RingHom.ker f
./noncirc-setlevel-answer.md:1812:lemma ringKrullDim_succ_le_ringKrullDim_polynomial :
./noncirc-setlevel-answer.md:1813:    ringKrullDim R + 1 ≤ ringKrullDim R[X] :=
./noncirc-setlevel-answer.md:1814:  ringKrullDim_succ_le_of_surjective constantCoeff (⟨C ·, coeff_C_zero⟩)
./noncirc-setlevel-answer.md:1819:lemma ringKrullDim_mvPolynomial_of_isEmpty (σ : Type*) [IsEmpty σ] :
./noncirc-setlevel-answer.md:1820:    ringKrullDim (MvPolynomial σ R) = ringKrullDim R :=
./noncirc-setlevel-answer.md:1821:  ringKrullDim_eq_of_ringEquiv (isEmptyRingEquiv _ _)
./noncirc-setlevel-answer.md:1824:lemma ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial (σ : Type*) [Finite σ] :
./noncirc-setlevel-answer.md:1825:    ringKrullDim R + Nat.card σ ≤ ringKrullDim (MvPolynomial σ R) := by
./noncirc-setlevel-answer.md:1830:    · exact ringKrullDim_eq_of_ringEquiv (renameEquiv _ e).toRingEquiv
./noncirc-setlevel-answer.md:1835:    grw [IH, ringKrullDim_succ_le_ringKrullDim_polynomial]
./noncirc-setlevel-answer.md:1836:    exact (ringKrullDim_eq_of_ringEquiv (MvPolynomial.optionEquivLeft _ _).toRingEquiv).ge
./noncirc-setlevel-answer.md:1840:lemma ringKrullDim_add_enatCard_le_ringKrullDim_mvPolynomial (σ : Type*) :
./noncirc-setlevel-answer.md:1841:    ringKrullDim R + ENat.card σ ≤ ringKrullDim (MvPolynomial σ R) := by
./noncirc-setlevel-answer.md:1846:    exact ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial _
./noncirc-setlevel-answer.md:1848:    suffices ringKrullDim (MvPolynomial σ R) = ⊤ by simp_all
./noncirc-setlevel-answer.md:1853:    refine le_trans ?_ (ringKrullDim_le_of_surjective
./noncirc-setlevel-answer.md:1855:    refine le_trans ?_ (ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial _)
./noncirc-setlevel-answer.md:1864:lemma ringKrullDim_succ_le_ringKrullDim_powerseries :
./noncirc-setlevel-answer.md:1865:    ringKrullDim R + 1 ≤ ringKrullDim (PowerSeries R) :=
./noncirc-setlevel-answer.md:1866:  ringKrullDim_succ_le_of_surjective constantCoeff (⟨C ·, rfl⟩)
./noncirc-setlevel-answer.md:1876:/-- `zeroLocus` and `vanishingIdeal` form a Galois connection. -/
./noncirc-setlevel-answer.md:1879:      vanishingIdeal t :=
./noncirc-setlevel-answer.md:1880:  fun I t => subset_zeroLocus_iff_le_vanishingIdeal t I
./noncirc-setlevel-answer.md:1882:/-- `zeroLocus` and `vanishingIdeal` form a Galois connection. -/
./noncirc-setlevel-answer.md:1885:      vanishingIdeal t := by
./noncirc-setlevel-answer.md:1889:theorem subset_zeroLocus_iff_subset_vanishingIdeal (t : Set (PrimeSpectrum R)) (s : Set R) :
./noncirc-setlevel-answer.md:1890:    t ⊆ zeroLocus s ↔ s ⊆ vanishingIdeal t :=
./noncirc-setlevel-answer.md:1895:theorem subset_vanishingIdeal_zeroLocus (s : Set R) : s ⊆ vanishingIdeal (zeroLocus s) :=
./noncirc-setlevel-answer.md:1898:theorem le_vanishingIdeal_zeroLocus (I : Ideal R) : I ≤ vanishingIdeal (zeroLocus I) :=
./noncirc-setlevel-answer.md:1902:theorem vanishingIdeal_zeroLocus_eq_radical (I : Ideal R) :
./noncirc-setlevel-answer.md:1903:    vanishingIdeal (zeroLocus (I : Set R)) = I.radical :=
./noncirc-setlevel-answer.md:1905:    rw [mem_vanishingIdeal, Ideal.radical_eq_sInf, Submodule.mem_sInf]
./noncirc-setlevel-answer.md:1911:@[simp] theorem vanishingIdeal_univ : vanishingIdeal Set.univ = nilradical R := by
./noncirc-setlevel-answer.md:1912:  rw [vanishingIdeal, iInf_univ, nilradical_eq_iInf]
./noncirc-setlevel-answer.md:1916:  vanishingIdeal_zeroLocus_eq_radical I ▸ (gc R).l_u_l_eq_l I
./noncirc-setlevel-answer.md:1918:theorem subset_zeroLocus_vanishingIdeal (t : Set (PrimeSpectrum R)) :
./noncirc-setlevel-answer.md:1919:    t ⊆ zeroLocus (vanishingIdeal t) :=
./noncirc-setlevel-answer.md:1997:/bin/bash -lc 'rg -n "radical.*ringKrullDim|ringKrullDim.*radical|quotient_radical|radical_quotient|ringKrullDim_quotient.*radical|zeroLocus_radical" /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory -S' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
./noncirc-setlevel-answer.md:2000:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:88:* `PrimeSpectrum.isClosed_iff_zeroLocus_radical_ideal`, `PrimeSpectrum.isRadical_vanishingIdeal`,
./noncirc-setlevel-answer.md:2005:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:867:  rw [← zeroLocus_vanishingIdeal_eq_closure, vanishingIdeal_range_comap, zeroLocus_radical]
./noncirc-setlevel-answer.md:2011:So for question 1, the answer is yes mathematically and easy in Lean, but there is no obvious prepackaged lemma named exactly `ringKrullDim_quotient_radical` in v4.29. It is a two-rewrite lemma from `ringKrullDim_quotient` and `PrimeSpectrum.zeroLocus_radical`.
./noncirc-setlevel-answer.md:2103:/bin/bash -lc 'rg -n "TensorProduct.*ringKrullDim|ringKrullDim.*TensorProduct|KrullDim.*Tensor|tensor.*Krull|prod.*Krull|Krull.*prod|Affine.*product|SpecProd|specProd|primeSpectrum.*Prod|primeSpectrum.*Tensor" /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry -S | head -500' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
./noncirc-setlevel-answer.md:2105:/bin/bash -lc 'rg -n "vanishingIdeal.*(union|iUnion|Union|sUnion)|zeroLocus.*(union|iUnion)|union.*vanishingIdeal|iUnion.*vanishingIdeal|vanishingIdeal.*sup|vanishingIdeal.*inf|Ideal.*inf.*vanishing|Set.*prod|prod.*vanishingIdeal" /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre -S | head -500' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
./noncirc-setlevel-answer.md:2129:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Polynomial.lean:38:      ← ringKrullDim_eq_of_ringEquiv (polyEquivTensor R (p.asIdeal.ResidueField)).toRingEquiv,
./noncirc-setlevel-answer.md:2171:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:116:  rw [← supportDim_quotient_eq_ringKrullDim, ← supportDim_self_eq_ringKrullDim]
./noncirc-setlevel-answer.md:2172:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:124:  rw [ringKrullDim_eq_of_ringEquiv (quotientEquivAlgOfEq R h).toRingEquiv,
./noncirc-setlevel-answer.md:2173:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:211:  rw [ringKrullDim_eq_of_ringEquiv (quotientEquivAlgOfEq R eq).toRingEquiv,
./noncirc-setlevel-answer.md:2174:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:212:    ← supportDim_quotient_eq_ringKrullDim, ← supportDim_self_eq_ringKrullDim]
./noncirc-setlevel-answer.md:2301:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:20:  the finite family of prime orbit ideals (G2 + `vanishingIdeal` turns unions into infs), so its
./noncirc-setlevel-answer.md:2302:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:136:orbit-ideal family: `vanishingIdeal` turns the G2 union `Σ̄^r = ⋃_M Ō_M` into an intersection. -/
./noncirc-setlevel-answer.md:2303:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalStratumDim.lean:196:flattening of) `productRankLocusLE ![n,m] r` is prime — it is `vanishingIdeal (Ō_{M₀})` of a single
./noncirc-setlevel-answer.md:2310:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:232:      Ideal (MvPolynomial σ k)).IsPrime := by rw [vanishingIdeal_univ_eq_bot]; infer_instance
./noncirc-setlevel-answer.md:2312:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:126:  ⟨(vanishingIdeal k {x} : Ideal (MvPolynomial σ k)), by infer_instance⟩
./noncirc-setlevel-answer.md:2313:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:133:      (((PrimeSpectrum.mem_vanishingIdeal _ _).1 hp) ⟨vanishingIdeal k {x}, by infer_instance⟩
./noncirc-setlevel-answer.md:2438:/bin/bash -lc 'rg -n "productRankLocus_eq_iUnion_smul_fibre|deepBaseComap_sigmaIdeal_le|nEquiv|nSub_mult|sigmaIdeal ≤|radical|FibreReduced|vanishingIdeal_image_fibre_eq_radical" /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre -S | head -300' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
./noncirc-setlevel-answer.md:2441:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:2:import DLNFibre.Core.FibreReducedTrivialization
./noncirc-setlevel-answer.md:2442:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:9:(`Core.FibreReducedTrivialization`) carries as a hypothesis. The engine's localized determinantal
./noncirc-setlevel-answer.md:2443:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:10:presentation (`Core.DeterminantalBasePresentation`) is `N = 1` only: `basePresentationEquiv` lives
./noncirc-setlevel-answer.md:2444:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:35:6. `deepBaseComap_sigmaIdeal_le` — the (non-circular) ideal direction: `deepBaseComap d` maps the
./noncirc-setlevel-answer.md:2445:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:39:   `aeval_deepBaseComap` + `singleTuple`). It does **not** assume the circular `sigmaIdeal ≤
./noncirc-setlevel-answer.md:2446:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:43:   (`Ideal.quotientMapₐ`), then composed with `basePresentationEquiv.symm` to give a `k`-algebra map
./noncirc-setlevel-answer.md:2447:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:131:`hSred : IsReduced S` (`Core.FibreReducedTrivialization.fibreGenIdeal_isRadical_of_trivialization`).
./noncirc-setlevel-answer.md:2448:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:132:It is **cheap** here: `IadDeep = (sigmaIdeal d r).map (algebraMap …)` is radical because
./noncirc-setlevel-answer.md:2449:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:133:`sigmaIdeal` is radical (`vanishingIdeal_isRadical`, over `[IsAlgClosed k]`) and localization
./noncirc-setlevel-answer.md:2450:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:134:carries radical
./noncirc-setlevel-answer.md:2451:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:135:ideals to radical ideals (`IsLocalization.map_radical`); a quotient by a radical ideal is reduced
./noncirc-setlevel-answer.md:2452:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:138:/-- **`IadDeep` is radical** (`[IsAlgClosed k]`): the localized image of the radical determinantal
./noncirc-setlevel-answer.md:2453:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:139:base ideal `sigmaIdeal d r`. Via `IsLocalization.map_radical`
./noncirc-setlevel-answer.md:2454:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:140:(`(I.map …).radical = I.radical.map …`) and `sigmaIdeal`'s radicality
./noncirc-setlevel-answer.md:2455:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:147:  rw [← Ideal.radical_eq_iff, IadDeep,
./noncirc-setlevel-answer.md:2456:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:148:    ← IsLocalization.map_radical (M := Submonoid.powers (ΔPdeep (k := k) d r hp hq)),
./noncirc-setlevel-answer.md:2457:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:149:    hsig.radical]
./noncirc-setlevel-answer.md:2458:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:152:`Sred = Localization.Away ΔPdeep ⧸ IadDeep` with `IadDeep` radical (`IadDeep_isRadical`); a quotient
./noncirc-setlevel-answer.md:2459:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:153:by a radical ideal is reduced
./noncirc-setlevel-answer.md:2460:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:229:Does **not** assume the circular `sigmaIdeal ≤ fibreGenIdeal`. -/
./noncirc-setlevel-answer.md:2461:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:230:theorem deepBaseComap_sigmaIdeal_le (d : Fin (N + 1) → ℕ) (r : ℕ) :
./noncirc-setlevel-answer.md:2462:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:251:discharged by `deepBaseComap_sigmaIdeal_le`), then composed with `basePresentationEquiv.symm`. -/
./noncirc-setlevel-answer.md:2463:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:291:the base `sigmaIdeal` into the deep one (`deepBaseComap_sigmaIdeal_le`). -/
./noncirc-setlevel-answer.md:2464:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:301:    deepBaseComap_sigmaIdeal_le d r (Ideal.mem_map_of_mem _ hg)
./noncirc-setlevel-answer.md:2465:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:316:`baseQuotMap` precomposed with `basePresentationEquiv.symm`. This is the morphism whose induced
./noncirc-setlevel-answer.md:2466:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:318:R2-3a's product iso `e` needs). `[IsAlgClosed k] [CharZero k]` (for `basePresentationEquiv`). -/
./noncirc-setlevel-answer.md:2467:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:323:    (basePresentationEquiv (k := k) (d 0) (d (Fin.last N)) r hp hq).symm.toAlgHom
./noncirc-setlevel-answer.md:2468:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:417:`CharZero`; `schurToSred` composes this with `basePresentationEquiv.symm`.) -/
./noncirc-setlevel-answer.md:2470:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:22:`I = orbitIdeal M = vanishingIdeal(orbitSet M)` directly — no determinantal minors, no radical. The
./noncirc-setlevel-answer.md:2474:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:33:3. **`vanishingIdeal_fibre_eq_fibreGenIdeal_of_trivialization`** — the **radical-collapse** of
./noncirc-setlevel-answer.md:2475:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:34:   `MultComorphism` point 4: with the cut ideal radical, `vanishingIdeal (fibre d B) =
./noncirc-setlevel-answer.md:2480:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:104:a `vanishingIdeal`), the fibre ideal `fibreGenIdeal d B` is **radical**. The certified mechanism:
./noncirc-setlevel-answer.md:2485:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:122:`vanishingIdeal (fibre d B) = radical (fibreGenIdeal d B)` collapses to
./noncirc-setlevel-answer.md:2486:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:123:`vanishingIdeal (fibre d B) = fibreGenIdeal d B`: the `radical (·)` wrapper drops. The clean
./noncirc-setlevel-answer.md:2487:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:132:  rw [vanishingIdeal_image_fibre_eq_radical,
./noncirc-setlevel-answer.md:2493:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:11:`fibreGenIdeal d B` (`Core.MultComorphism.vanishingIdeal_image_fibre_eq_radical`). The point of this
./noncirc-setlevel-answer.md:2505:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:47:(definition of `codimRepCanonical`/`codimRep`); `vanishingIdeal (…) = (fibreGenIdeal d B).radical`
./noncirc-setlevel-answer.md:2506:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:48:(`vanishingIdeal_image_fibre_eq_radical`, the Nullstellensatz); `(radical I).height = I.height`
./noncirc-setlevel-answer.md:2509:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:54:  rw [codimRepCanonical, codimRep, vanishingIdeal_image_fibre_eq_radical, Ideal.height_radical]
./noncirc-setlevel-answer.md:2510:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:20:   Nullstellensatz over `[IsAlgClosed k]`): `vanishingIdeal Z` is always **radical**
./noncirc-setlevel-answer.md:2512:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:67:strong Nullstellensatz it equals its own radical, via `vanishingIdeal Z = vanishingIdeal (zeroLocus
./noncirc-setlevel-answer.md:2513:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:68:(vanishingIdeal Z))` `= (vanishingIdeal Z).radical`. -/
./noncirc-setlevel-answer.md:2514:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:71:  have h : vanishingIdeal k Z = (vanishingIdeal k Z).radical := by
./noncirc-setlevel-answer.md:2515:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:74:        vanishingIdeal_zeroLocus_eq_radical (K := k)]
./noncirc-setlevel-answer.md:2517:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:87:Nullstellensatz forces `vanishingIdeal (zeroLocus (vanishingIdeal Z)) = (vanishingIdeal Z).radical`,
./noncirc-setlevel-answer.md:2518:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:97:    have h3 : vanishingIdeal k (zeroLocus k (vanishingIdeal k Z)) = (vanishingIdeal k Z).radical :=
./noncirc-setlevel-answer.md:2519:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:98:      vanishingIdeal_zeroLocus_eq_radical (K := k) _
./noncirc-setlevel-answer.md:2546:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:27:4. **`vanishingIdeal(fibre) = radical(fibreGenIdeal)`** — over `[IsAlgClosed k]`, the engine's
./noncirc-setlevel-answer.md:2547:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:28:   Nullstellensatz (`vanishingIdeal_zeroLocus_eq_radical`) reads the fibre's vanishing ideal as the
./noncirc-setlevel-answer.md:2550:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:158:closed field, the engine's strong Nullstellensatz (`vanishingIdeal_zeroLocus_eq_radical`) reads the
./noncirc-setlevel-answer.md:2552:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:160:theorem vanishingIdeal_image_fibre_eq_radical [IsAlgClosed k] (d : Fin (N + 1) → ℕ)
./noncirc-setlevel-answer.md:2553:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:162:    vanishingIdeal k (canonicalCoord d '' (fibre d B)) = (fibreGenIdeal d B).radical := by
./noncirc-setlevel-answer.md:2554:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:164:    vanishingIdeal_zeroLocus_eq_radical (K := k)]
./noncirc-setlevel-answer.md:2639:lemma test_ringKrullDim_quotient_radical (I : Ideal R) :
./noncirc-setlevel-answer.md:2640:    ringKrullDim (R ⧸ I.radical) = ringKrullDim (R ⧸ I) := by
./noncirc-setlevel-answer.md:2641:  rw [ringKrullDim_quotient, ringKrullDim_quotient, zeroLocus_radical]
./noncirc-setlevel-answer.md:2643:lemma test_ringKrullDim_quotient_radical' (I : Ideal R) :
./noncirc-setlevel-answer.md:2644:    ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ I.radical) := by
./noncirc-setlevel-answer.md:2645:  rw [test_ringKrullDim_quotient_radical]
./noncirc-setlevel-answer.md:2656:lemma test_ringKrullDim_quotient_radical (I : Ideal R) :
./noncirc-setlevel-answer.md:2657:    ringKrullDim (R ⧸ I.radical) = ringKrullDim (R ⧸ I) := by
./noncirc-setlevel-answer.md:2658:  rw [ringKrullDim_quotient, ringKrullDim_quotient, zeroLocus_radical]
./noncirc-setlevel-answer.md:2660:lemma test_ringKrullDim_quotient_radical' (I : Ideal R) :
./noncirc-setlevel-answer.md:2661:    ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ I.radical) := by
./noncirc-setlevel-answer.md:2662:  rw [test_ringKrullDim_quotient_radical]
./noncirc-setlevel-answer.md:2672:  rw [← Set.univ_subset_iff, subset_zeroLocus_iff_subset_vanishingIdeal, vanishingIdeal_univ]
./noncirc-setlevel-answer.md:2681:theorem vanishingIdeal_union (t t' : Set (PrimeSpectrum R)) :
./noncirc-setlevel-answer.md:2682:    vanishingIdeal (t ∪ t') = vanishingIdeal t ⊓ vanishingIdeal t' :=
./noncirc-setlevel-answer.md:2700:theorem vanishingIdeal_iUnion {ι : Sort*} (t : ι → Set (PrimeSpectrum R)) :
./noncirc-setlevel-answer.md:2701:    vanishingIdeal (⋃ i, t i) = ⨅ i, vanishingIdeal (t i) :=
./noncirc-setlevel-answer.md:2712:/bin/bash -lc 'rg -n "def vanishingIdeal|theorem vanishingIdeal|lemma vanishingIdeal|zeroLocus_eq|vanishingIdeal.*iUnion|vanishingIdeal.*union|radical|varietyDim" /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean -S | head -300' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
./noncirc-setlevel-answer.md:2714:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:15:The main statement of the theorem is `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`.
./noncirc-setlevel-answer.md:2715:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:61:def vanishingIdeal (V : Set (σ → K)) : Ideal (MvPolynomial σ k) where
./noncirc-setlevel-answer.md:2716:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:73:theorem vanishingIdeal_anti_mono {A B : Set (σ → K)} (h : A ≤ B) :
./noncirc-setlevel-answer.md:2717:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:76:theorem vanishingIdeal_empty : vanishingIdeal k (∅ : Set (σ → K)) = ⊤ :=
./noncirc-setlevel-answer.md:2718:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:113:theorem radical_le_vanishingIdeal_zeroLocus (I : Ideal (MvPolynomial σ k)) :
./noncirc-setlevel-answer.md:2719:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:114:    I.radical ≤ vanishingIdeal k (zeroLocus K I) := by
./noncirc-setlevel-answer.md:2721:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:129:theorem vanishingIdeal_pointToPoint (V : Set (σ → K)) :
./noncirc-setlevel-answer.md:2722:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:171:theorem vanishingIdeal_zeroLocus_eq_radical (I : Ideal (MvPolynomial σ k)) :
./noncirc-setlevel-answer.md:2723:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:172:    vanishingIdeal k (zeroLocus K I) = I.radical := by
./noncirc-setlevel-answer.md:2724:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:173:  refine le_antisymm ?_ (radical_le_vanishingIdeal_zeroLocus _)
./noncirc-setlevel-answer.md:2726:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:182:@[simp high] -- This needs to fire before `vanishingIdeal_zeroLocus_eq_radical`
./noncirc-setlevel-answer.md:2727:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean:185:  Trans.trans (vanishingIdeal_zeroLocus_eq_radical P) h.radical
./noncirc-setlevel-answer.md:2728:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:20:   Nullstellensatz over `[IsAlgClosed k]`): `vanishingIdeal Z` is always **radical**
./noncirc-setlevel-answer.md:2729:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:31:   irreducible"), `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ` (`ℕ∞`, additive — `ℕ∞`
./noncirc-setlevel-answer.md:2730:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:37:`axiom`. `varietyDim Z = ringKrullDim (R ⧸ vanishingIdeal Z)` is the Krull dimension of the
./noncirc-setlevel-answer.md:2732:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:67:strong Nullstellensatz it equals its own radical, via `vanishingIdeal Z = vanishingIdeal (zeroLocus
./noncirc-setlevel-answer.md:2733:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:68:(vanishingIdeal Z))` `= (vanishingIdeal Z).radical`. -/
./noncirc-setlevel-answer.md:2734:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:69:theorem vanishingIdeal_isRadical [IsAlgClosed k] [Finite σ] (Z : Set (σ → k)) :
./noncirc-setlevel-answer.md:2735:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:71:  have h : vanishingIdeal k Z = (vanishingIdeal k Z).radical := by
./noncirc-setlevel-answer.md:2736:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:74:        vanishingIdeal_zeroLocus_eq_radical (K := k)]
./noncirc-setlevel-answer.md:2738:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:87:Nullstellensatz forces `vanishingIdeal (zeroLocus (vanishingIdeal Z)) = (vanishingIdeal Z).radical`,
./noncirc-setlevel-answer.md:2739:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:97:    have h3 : vanishingIdeal k (zeroLocus k (vanishingIdeal k Z)) = (vanishingIdeal k Z).radical :=
./noncirc-setlevel-answer.md:2740:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:98:      vanishingIdeal_zeroLocus_eq_radical (K := k) _
./noncirc-setlevel-answer.md:2742:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:139:noncomputable def varietyDim (Z : Set (σ → k)) : ℕ∞ :=
./noncirc-setlevel-answer.md:2743:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:144:the ambient dimension `Nat.card σ`: `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ`. The
./noncirc-setlevel-answer.md:2744:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:147:theorem height_vanishingIdeal_add_varietyDim_eq_card [Finite σ] {Z : Set (σ → k)}
./noncirc-setlevel-answer.md:2745:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:149:    (vanishingIdeal k Z).height + varietyDim Z = (Nat.card σ : ℕ∞) := by
./noncirc-setlevel-answer.md:2746:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:157:  rw [varietyDim, ← hm, WithBot.unbotD_coe]
./noncirc-setlevel-answer.md:2747:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:162:`height (vanishingIdeal Z) = Nat.card σ − varietyDim Z` for an irreducible variety `Z` (`ℕ∞`
./noncirc-setlevel-answer.md:2748:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:163:subtraction; lossless here since `varietyDim Z ≤ Nat.card σ`). The geometric codimension is the
./noncirc-setlevel-answer.md:2749:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:165:theorem height_vanishingIdeal_eq_card_sub_varietyDim [Finite σ] {Z : Set (σ → k)}
./noncirc-setlevel-answer.md:2750:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:167:    (vanishingIdeal k Z).height = (Nat.card σ : ℕ∞) - varietyDim Z := by
./noncirc-setlevel-answer.md:2751:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:168:  have hadd := height_vanishingIdeal_add_varietyDim_eq_card hp
./noncirc-setlevel-answer.md:2752:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:169:  have hne : varietyDim Z ≠ ⊤ := by
./noncirc-setlevel-answer.md:2753:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:182:`height_vanishingIdeal_add_varietyDim_eq_card` at `σ := RepCoord d`, `Z := coord '' Z`. -/
./noncirc-setlevel-answer.md:2754:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:183:theorem codimRep_add_varietyDim_eq_card [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./noncirc-setlevel-answer.md:2755:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:186:    codimRep coord Z + varietyDim (coord '' Z) = (Nat.card (RepCoord d) : ℕ∞) :=
./noncirc-setlevel-answer.md:2756:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:187:  height_vanishingIdeal_add_varietyDim_eq_card hp
./noncirc-setlevel-answer.md:2757:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:190:varietyDim (coord '' Z)` for an irreducible variety `coord '' Z`: geometric codimension `=` ambient
./noncirc-setlevel-answer.md:2758:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:192:theorem codimRep_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./noncirc-setlevel-answer.md:2759:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:195:    codimRep coord Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (coord '' Z) :=
./noncirc-setlevel-answer.md:2760:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:196:  height_vanishingIdeal_eq_card_sub_varietyDim hp
./noncirc-setlevel-answer.md:2761:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:199:`canonicalCoord d`, `codimRepCanonical Z = Nat.card (RepCoord d) − varietyDim (canonicalCoord d ''
./noncirc-setlevel-answer.md:2762:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:201:theorem codimRepCanonical_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./noncirc-setlevel-answer.md:2763:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:205:    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
./noncirc-setlevel-answer.md:2764:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:206:  codimRep_eq_card_sub_varietyDim (canonicalCoord d) Z hp
./noncirc-setlevel-answer.md:2765:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:213:theorem vanishingIdeal_univ_eq_bot [IsAlgClosed k] :
./noncirc-setlevel-answer.md:2766:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:225:alg-closed, `σ` finite), the vanishing ideal is `⊥` (prime), `varietyDim = Nat.card σ`, the bridge
./noncirc-setlevel-answer.md:2767:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:230:      + varietyDim (Set.univ : Set (σ → k)) = (Nat.card σ : ℕ∞) := by
./noncirc-setlevel-answer.md:2768:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:233:  exact height_vanishingIdeal_add_varietyDim_eq_card this
./noncirc-setlevel-answer.md:2778:  have hdim : ringKrullDim (MvPolynomial (Fin (Fintype.card σ)) k ⧸ q)
./noncirc-setlevel-answer.md:2779:      = ringKrullDim (MvPolynomial σ k ⧸ p) :=
./noncirc-setlevel-answer.md:2780:    ringKrullDim_quotient_map_algEquiv e p
./noncirc-setlevel-answer.md:2781:  have key := height_add_ringKrullDim_quotient_eq k (Fintype.card σ) q
./noncirc-setlevel-answer.md:2789:`MvPolynomial σ k ⧸ vanishingIdeal Z` of `Z`'s Zariski closure, as an `ℕ∞` (the `⊥` from a trivial
./noncirc-setlevel-answer.md:2790:quotient — absent here, since the relevant `vanishingIdeal Z` is prime — defaulting to `0`). It is
./noncirc-setlevel-answer.md:2792:noncomputable def varietyDim (Z : Set (σ → k)) : ℕ∞ :=
./noncirc-setlevel-answer.md:2793:  (ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal k Z)).unbotD 0
./noncirc-setlevel-answer.md:2796:`(vanishingIdeal Z).IsPrime` — the height of its vanishing ideal plus its variety dimension equals
./noncirc-setlevel-answer.md:2797:the ambient dimension `Nat.card σ`: `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ`. The
./noncirc-setlevel-answer.md:2798:catenary identity over `σ`, read at the prime `vanishingIdeal Z`. Geometric codimension `=` ambient
./noncirc-setlevel-answer.md:2800:theorem height_vanishingIdeal_add_varietyDim_eq_card [Finite σ] {Z : Set (σ → k)}
./noncirc-setlevel-answer.md:2801:    (hp : (vanishingIdeal k Z : Ideal (MvPolynomial σ k)).IsPrime) :
./noncirc-setlevel-answer.md:2802:    (vanishingIdeal k Z).height + varietyDim Z = (Nat.card σ : ℕ∞) := by
./noncirc-setlevel-answer.md:2803:  have key := height_add_ringKrullDim_quotient_eq_card (vanishingIdeal k Z)
./noncirc-setlevel-answer.md:2804:  haveI : Nontrivial (MvPolynomial σ k ⧸ vanishingIdeal k Z) :=
./noncirc-setlevel-answer.md:2806:  have hne : ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal k Z) ≠ ⊥ :=
./noncirc-setlevel-answer.md:2808:      ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial σ k ⧸ vanishingIdeal k Z)
./noncirc-setlevel-answer.md:2810:  rw [varietyDim, ← hm, WithBot.unbotD_coe]
./noncirc-setlevel-answer.md:2815:`height (vanishingIdeal Z) = Nat.card σ − varietyDim Z` for an irreducible variety `Z` (`ℕ∞`
./noncirc-setlevel-answer.md:2816:subtraction; lossless here since `varietyDim Z ≤ Nat.card σ`). The geometric codimension is the
./noncirc-setlevel-answer.md:2818:theorem height_vanishingIdeal_eq_card_sub_varietyDim [Finite σ] {Z : Set (σ → k)}
./noncirc-setlevel-answer.md:2819:    (hp : (vanishingIdeal k Z : Ideal (MvPolynomial σ k)).IsPrime) :
./noncirc-setlevel-answer.md:2820:    (vanishingIdeal k Z).height = (Nat.card σ : ℕ∞) - varietyDim Z := by
./noncirc-setlevel-answer.md:2821:  have hadd := height_vanishingIdeal_add_varietyDim_eq_card hp
./noncirc-setlevel-answer.md:2822:  have hne : varietyDim Z ≠ ⊤ := by
./noncirc-setlevel-answer.md:2841:strong Nullstellensatz it equals its own radical, via `vanishingIdeal Z = vanishingIdeal (zeroLocus
./noncirc-setlevel-answer.md:2842:(vanishingIdeal Z))` `= (vanishingIdeal Z).radical`. -/
./noncirc-setlevel-answer.md:2843:theorem vanishingIdeal_isRadical [IsAlgClosed k] [Finite σ] (Z : Set (σ → k)) :
./noncirc-setlevel-answer.md:2844:    (vanishingIdeal k Z : Ideal (MvPolynomial σ k)).IsRadical := by
./noncirc-setlevel-answer.md:2845:  have h : vanishingIdeal k Z = (vanishingIdeal k Z).radical := by
./noncirc-setlevel-answer.md:2847:      rw [← (zeroLocus_vanishingIdeal_galoisConnection (σ := σ) (k := k) (K := k)).u_l_u_eq_u Z,
./noncirc-setlevel-answer.md:2848:        vanishingIdeal_zeroLocus_eq_radical (K := k)]
./noncirc-setlevel-answer.md:2853:`PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime`. -/
./noncirc-setlevel-answer.md:2854:theorem isZariskiIrreducible_iff_isPrime_vanishingIdeal (Z : Set (σ → k)) :
./noncirc-setlevel-answer.md:2855:    IsZariskiIrreducible Z ↔ (vanishingIdeal k Z : Ideal (MvPolynomial σ k)).IsPrime := by
./noncirc-setlevel-answer.md:2857:  rw [PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime, vanishingIdeal_pointToPoint]
./noncirc-setlevel-answer.md:2860:is prime (hence proper) is nonempty: if `Z = ∅` then `vanishingIdeal Z = ⊤`, but the strong
./noncirc-setlevel-answer.md:2861:Nullstellensatz forces `vanishingIdeal (zeroLocus (vanishingIdeal Z)) = (vanishingIdeal Z).radical`,
./noncirc-setlevel-answer.md:2863:theorem nonempty_of_isZariskiClosed_of_isPrime_vanishingIdeal [IsAlgClosed k] [Finite σ]
./noncirc-setlevel-answer.md:2865:    (hp : (vanishingIdeal k Z : Ideal (MvPolynomial σ k)).IsPrime) :
./noncirc-setlevel-answer.md:2869:  have htop : vanishingIdeal k Z = ⊤ := by
./noncirc-setlevel-answer.md:2870:    have h2 : zeroLocus k (vanishingIdeal k Z) = (∅ : Set (σ → k)) := hZ ▸ hempty
./noncirc-setlevel-answer.md:2871:    have h3 : vanishingIdeal k (zeroLocus k (vanishingIdeal k Z)) = (vanishingIdeal k Z).radical :=
./noncirc-setlevel-answer.md:2872:      vanishingIdeal_zeroLocus_eq_radical (K := k) _
./noncirc-setlevel-answer.md:2873:    rw [h2, vanishingIdeal_empty] at h3
./noncirc-setlevel-answer.md:2882:One more adversarial point: the project’s `varietyDim` itself says it is the dimension of the Zariski closure unless the set is closed. That is fine for radical-insensitivity, but for chart opens and exact-rank strata you must explicitly account for “open chart has same closure dimension” or use the cited `hClosure` bridge.
./noncirc-setlevel-answer.md:3143:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Height.lean:296:  rw [ringKrullDim, Order.krullDim_eq_iSup_height, iSup_le_iff]
./noncirc-setlevel-answer.md:3146:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Zero.lean:55:  rw [Ring.KrullDimLE, Order.krullDimLE_iff, le_antisymm_iff, ← ringKrullDim, Nat.cast_zero,
./noncirc-setlevel-answer.md:3148:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Basic.lean:40:    KrullDimLE n R ↔ ringKrullDim R ≤ n := Order.krullDimLE_iff n (PrimeSpectrum R)
./noncirc-setlevel-answer.md:3160:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:33:    ringKrullDim (R ⧸ I) = Order.krullDim (PrimeSpectrum.zeroLocus (R := R) I) := by
./noncirc-setlevel-answer.md:3161:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:34:  rw [ringKrullDim, Order.krullDim_eq_of_orderIso I.primeSpectrumQuotientOrderIsoZeroLocus]
./noncirc-setlevel-answer.md:3162:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:47:  rw [ringKrullDim_quotient, Order.krullDim_eq_iSup_length, ringKrullDim,
./noncirc-setlevel-answer.md:3214:**Verdict: YES.** The set-level/`varietyDim` route dodges the R2-3b-4 circularity. The old circularity was specific to building a scheme/ring iso through the *generator* ideal and needing `sigmaIdeal ≤ ker`. If you work with sets and `vanishingIdeal`, the coordinate rings are already reduced-by-definition, and the required ideal containment for pullbacks is the tautological one: “a polynomial vanishing on the target pulls back to one vanishing on the source.”
./noncirc-setlevel-answer.md:3216:1. **Radical-insensitivity:** yes. I do not see a prepackaged v4.29 lemma named exactly `ringKrullDim_quotient_radical`, but it is a two-line lemma from Mathlib:
./noncirc-setlevel-answer.md:3220:lemma ringKrullDim_quotient_radical {R : Type*} [CommRing R] (I : Ideal R) :
./noncirc-setlevel-answer.md:3221:    ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ I.radical) := by
./noncirc-setlevel-answer.md:3222:  rw [ringKrullDim_quotient, ringKrullDim_quotient, PrimeSpectrum.zeroLocus_radical]
./noncirc-setlevel-answer.md:3224:The relevant upstream pieces are `ringKrullDim_quotient` and `PrimeSpectrum.zeroLocus_radical`. So `varietyDim` genuinely only sees the radical/closed-set structure.
./noncirc-setlevel-answer.md:3231:None of that needs `sigmaIdeal ≤ ker`. The warning is different: a bare set bijection does not preserve `varietyDim`; you need the map and inverse to be regular on the pivot chart, typically via localization/principal-open coordinates. That is new chart algebra, but not the old reducedness circularity.
./noncirc-setlevel-answer.md:3237:But I do not see this as an existing Mathlib v4.29 theorem for `varietyDim`, nor a general
./noncirc-setlevel-answer.md:3238:`ringKrullDim (A ⊗[k] B) = ringKrullDim A + ringKrullDim B`.
./noncirc-setlevel-answer.md:3242:`dim (⋃ᵢ Zᵢ) = maxᵢ dim Zᵢ` for finite nonempty covers, radical-insensitively. Mathlib has the Spec-level zero-locus/vanishing-ideal union facts, e.g. `PrimeSpectrum.vanishingIdeal_union`, `PrimeSpectrum.vanishingIdeal_iUnion`, `PrimeSpectrum.zeroLocus_inf`, but I do not see a ready `varietyDim_finite_iUnion` theorem. Also note your `varietyDim` sends the empty set to `0` via `unbotD 0`, so state product/union lemmas with the relevant nonemptiness assumptions.
./noncirc-setlevel-answer.md:3249:  `varietyDim(chart) = varietyDim U_P + varietyDim F = δ + varietyDim F`.
./noncirc-setlevel-answer.md:3251:- Glue: finite pivot cover gives global dimension by finite-union max; use the closure/open-chart bridge carefully because `varietyDim` is closure dimension for arbitrary sets.
./noncirc-setlevel-answer.md:3253:So the de-risk claim is correct: radical-insensitivity of `varietyDim` removes the need to prove `fibreGenIdeal = radical fibreGenIdeal` or `sigmaIdeal ≤ ker` for the generator-level scheme iso. The remaining risk is library/build cost for product dimension and finite-glue lemmas, not circularity.
./noncirc-setlevel-answer.md:3256:**Verdict: YES.** The set-level/`varietyDim` route dodges the R2-3b-4 circularity. The old circularity was specific to building a scheme/ring iso through the *generator* ideal and needing `sigmaIdeal ≤ ker`. If you work with sets and `vanishingIdeal`, the coordinate rings are already reduced-by-definition, and the required ideal containment for pullbacks is the tautological one: “a polynomial vanishing on the target pulls back to one vanishing on the source.”
./noncirc-setlevel-answer.md:3258:1. **Radical-insensitivity:** yes. I do not see a prepackaged v4.29 lemma named exactly `ringKrullDim_quotient_radical`, but it is a two-line lemma from Mathlib:
./noncirc-setlevel-answer.md:3262:lemma ringKrullDim_quotient_radical {R : Type*} [CommRing R] (I : Ideal R) :
./noncirc-setlevel-answer.md:3263:    ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ I.radical) := by
./noncirc-setlevel-answer.md:3264:  rw [ringKrullDim_quotient, ringKrullDim_quotient, PrimeSpectrum.zeroLocus_radical]
./noncirc-setlevel-answer.md:3266:The relevant upstream pieces are `ringKrullDim_quotient` and `PrimeSpectrum.zeroLocus_radical`. So `varietyDim` genuinely only sees the radical/closed-set structure.
./noncirc-setlevel-answer.md:3273:None of that needs `sigmaIdeal ≤ ker`. The warning is different: a bare set bijection does not preserve `varietyDim`; you need the map and inverse to be regular on the pivot chart, typically via localization/principal-open coordinates. That is new chart algebra, but not the old reducedness circularity.
./noncirc-setlevel-answer.md:3279:But I do not see this as an existing Mathlib v4.29 theorem for `varietyDim`, nor a general
./noncirc-setlevel-answer.md:3280:`ringKrullDim (A ⊗[k] B) = ringKrullDim A + ringKrullDim B`.
./noncirc-setlevel-answer.md:3284:`dim (⋃ᵢ Zᵢ) = maxᵢ dim Zᵢ` for finite nonempty covers, radical-insensitively. Mathlib has the Spec-level zero-locus/vanishing-ideal union facts, e.g. `PrimeSpectrum.vanishingIdeal_union`, `PrimeSpectrum.vanishingIdeal_iUnion`, `PrimeSpectrum.zeroLocus_inf`, but I do not see a ready `varietyDim_finite_iUnion` theorem. Also note your `varietyDim` sends the empty set to `0` via `unbotD 0`, so state product/union lemmas with the relevant nonemptiness assumptions.
./noncirc-setlevel-answer.md:3291:  `varietyDim(chart) = varietyDim U_P + varietyDim F = δ + varietyDim F`.
./noncirc-setlevel-answer.md:3293:- Glue: finite pivot cover gives global dimension by finite-union max; use the closure/open-chart bridge carefully because `varietyDim` is closure dimension for arbitrary sets.
./noncirc-setlevel-answer.md:3295:So the de-risk claim is correct: radical-insensitivity of `varietyDim` removes the need to prove `fibreGenIdeal = radical fibreGenIdeal` or `sigmaIdeal ≤ ker` for the generator-level scheme iso. The remaining risk is library/build cost for product dimension and finite-glue lemmas, not circularity.

codex
The current thread directory contains prior prompt/answer scratch files, and the actual Lean tree is the sibling `lean/` worktree. I’m narrowing the search there now, focused on the definitions that will determine whether a regular-section route pays off.
exec
/bin/bash -lc "sed -n '1,220p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/CLAUDE.md" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
# geometry-of-dln-fibre

AI-assisted math-research + Lean-formalisation harness for **digesting and formalising** the paper
*"Geometry of the fibers of the multiplication map of deep linear neural networks"* (Simon Pepin
Lehalleur & Richárd Rimányi, 2024; `paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/`).
Orientation is in [`README.md`](README.md); this file is the disposition and the working discipline.
The process harness (disposition + policies + roles + skills + the markdown→Lean pipeline) is ported
from the `ai-research-assistant` harness and is **domain-agnostic** — see [`TEMPLATE.md`](TEMPLATE.md)
to instantiate it for another paper.

## Disposition

The work here is research. Not coding, not ticking off a support ticket, not shipping a product. 
The stance: 
- careful, conscientious, objective as a scientist.
- meticulous in calculation as Euler, bold as Grothendieck. 
- methodical as Sherlock Holmes. Observe before theorising. Distinguish data from interpretation. 
- update like a Bayesian; do not collapse to the mode. 


- **Resist the move-fast-and-ship-it instinct.** Stackable, solid progress is the goal; the trap is
  *visible* progress raced ahead of it — a clean doc or confident headline that travels far while leaving
  holes behind. When you reach for a confident headline, that is the moment to look for the confound. Each
  layer should be solid and hole-free before the next stands on it.
- **Fill the layer — completion is your strength.** *The sea rises inexorably, but not in spikes*
  ([`docs/policies/bedrock.md`](docs/policies/bedrock.md)): within a boundary already staked, close the holes
  — the generality a statement promised, the cases it already claims, fidelity to the definition and the
  underlying spirit it invokes — rather than defer them. Such hardening is high-value, and it is where your
  **comparative advantage** lies: your bottleneck is scoping, taste, and direction, not the patient completion
  of well-scoped work — so do not treat that completion capacity, which is *abundant*, as if it were *scarce*.
  **Just do it!** Don't file it as a "chore" (an *unprobed* difficulty claim, not a defer). Surface to move the
  *boundary* — but an **earned** taste-judgment that a gap is the *right* extension is itself direction:
  **Just Do It** if within reach, else **roadmap** it; only a *bare, unargued* extension waits for the operator.
- **Name results for what they are.** A result's name and statement denote exactly what is proven — no more;
  reaching for an impressive name (or "done") is the visible-progress instinct in disguise. Separate Proved /
  Assumed / Cited / Deferred. See [`docs/policies/precision.md`](docs/policies/precision.md). (Here the
  recurring trap: a `rlct_…`-named result that in fact proves only a *codimension* — the `rlct = ½·codim`
  reading needs the cited analytic bound.)
- **Build to bedrock.** A sorry-free build defeats *technical* slop; it never defeats *conceptual* slop —
  "technically correct but subtly wrong, not The Way." **Bedrock is the rock the rising sea rises over**: build
  the theory so the next result can stand on it without re-opening it. Where short feedback loops fail, **beauty
  is the instrument** — a vacuous, mis-scoped, or overclaiming result is *ugly*, and the ugliness is
  information. The **controller holds this taste and judges against it**; a green build is necessary, never
  sufficient. See [`docs/policies/bedrock.md`](docs/policies/bedrock.md).
- **Caveats live next to claims, not in footnotes.** An assumed hypothesis or a cited interface goes in the
  same paragraph as any claim that depends on it.
- **Write to figure out the truth, not to persuade.** Concise and fact-based.
- **Elementary, precisely.** Build explanations up from precise but simple well-chunked objects, established locally in the
  document. "Elementary" does not mean imprecise or dumbed-down or toy analogies: every step stays
  mathematically precise. Introduce the objects you use before you use them; prefer a chain of small exact
  statements over one dense one. Resist over-naming things to do chunking. Reach for an analogy only when it is exact and load-bearing. See
  [`docs/policies/writing-style.md`](docs/policies/writing-style.md).

## Writing and communication discipline (object-level focus)
In writing or in communication, focus on object-level. Resist meta-level pull. 
Remove authorial self-reassurance: `honestly`, `fundamentally`, `this is the whole point`, `this is loadbearing`, `of course`, `simply`, `just`, and selling phrasing.
The full list and the review function that enforces it are in [`docs/policies/review.md`](docs/policies/review.md).

## How research runs here

- **Expeditions** ([`docs/policies/expedition.md`](docs/policies/expedition.md)) are the unit: a central
  question, a controller delegating to thread teammates (explore / formalisation / infra), reviewers, and a
  synthesis at close. Run on the Agent Teams substrate (`CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS=1`); launch with
  cwd = this repo root.
- **Pipeline: markdown → Lean.** Theory develops in markdown (`theory/`, expedition notes). A stable claim is
  formalised in Lean (`lean/`, library `DLNFibre`). The reader-facing digest/expositions live in
  `docs/expositions/`.
  - *Scholium* is a **viewer** (renders these markdown docs with KaTeX + callouts), not an editor; write to its
    conventions in [`docs/policies/scholium-writing-format.md`](docs/policies/scholium-writing-format.md). The
    recurring trap: display math `$$…$$` needs a **blank line before and after**, fences on their own lines
    (indented inside `!!!`/`???` callouts) — packed against text it falls through to markdown and the `_`
    subscripts render as emphasis. A second trap: **fenced code does not render inside a callout** — use an
    indented code block (8-space indent) there; top-level fenced code is fine.
- **Claims** carry kill-conditions; new claims are stress-tested, established/cited results verified against
  source ([`docs/policies/claims.md`](docs/policies/claims.md)).
- **Codex** is the independent second model for strategy and review
  ([`docs/policies/codex-consultation.md`](docs/policies/codex-consultation.md)).

## Team structure

Roles are documented under [`.agent-team/roles/`](.agent-team/roles/):
- `controller` — this lead session: meta-planning, delegation, integration.
- `scout` — explore / reconnaissance threads: map the terrain (Mathlib, the paper, possibility spaces), compute / derive / claims.
- `pen-and-paper` — a specialised `scout`: design-space math adjudicating a truth-value (`witness` / `obstruction` seats), exact algebra, decorrelated Codex; hands a certificate to the formaliser. No Lean.
- `formaliser` — formalisation (tide) threads.
- `reviewer` — controller-spawned independent audit (soundness / fidelity).
- `hardener` — independent principles / taste reviewer (precision, bedrock).

If dispatched into a role, read its role file and agent definition first.

## Branch discipline

- **One remote: `origin = git@github.com:edmund-ukaisi/geometry-of-dln-fibre.git`.** All work lives here.
- **`dev` is the integration branch.** Feature and expedition branches branch off `dev` and PR back into
  `dev`. `master` is the **release** branch — promoted from `dev` deliberately by the operator, never pushed
  to directly.
- Use a **feature branch** for any non-trivial unit of work; you can push here; don't commit to `dev` or `master` directly. One
  expedition runs on one branch (`expedition/<slug>`); PR at close behind signal-and-wait.
- **Pushing feature/expedition branches to `origin` is pre-authorized** (operator standing instruction,
  2026-06-12) — push freely to bank and share work. **Opening/merging PRs and the `dev → master` promotion
  remain operator-gated** (signal-and-wait); the operator performs those. Always confirm the push target is
  `origin`, never a non-`origin` remote.

## Memory

Persistent context lives **in-repo**: this file, the policies in `docs/policies/`, the expedition docs
(`synthesis.md` / statement cards / `thread.md`), `ROADMAP.md`, and `lean/CLAUDE.md`. Save conventions and
decisions there.

**Do NOT write to global Claude memory (`~/.claude/**/memory/`).** It pollutes other workspaces and is
invisible to collaborators reading the repo. This binds the controller **and every teammate** — the harness
may prompt you to save a memory there; do not. If a teammate writes one, the controller deletes it and
re-homes the content in-repo. (Agent-Teams *runtime* state under `~/.claude/teams/` and `~/.claude/tasks/` is
fine — that's the substrate, not persistent context.)

## The destination, plainly

We want, in honest Lean, the paper's results about the **fibres of matrix multiplication** for deep linear
networks:

- the space $\operatorname{Rep}_{\underline d}$ of composable matrix tuples, the multiplication map
  $\operatorname{mult}$, the zero-product / rank-$r$ loci, and the fibres $\operatorname{mult}^{-1}(B)$;
- via the **type-A quiver** translation (orbits ↔ Kostant partitions ↔ rank patterns, Gabriel, orbit-closure
  order, the `Ext` codimension): the codimension $C$ and the number $\theta$ of top-dimensional components,
  in the paper's three forms (Poincaré series, a quadratic integer program, an explicit formula), and the
  surprising **permutation invariance** of $(C,\theta)$;
- the payoff: the real log-canonical threshold of the square-Frobenius loss is $C/2$ — DLNs are "mildly
  singular". The geometric codimension is the new content; the `rlct ≤ ½·codim` direction is **Cited**
  (Aoyagi / Watanabe).

The reusable **engine** (everything before "the payoff") is network-free and lives in `DLNFibre.Core`; the
DLN/RLCT **application** lives in `DLNFibre.DLN`. See [`ROADMAP.md`](ROADMAP.md) for the formalisation ladder.

## Pointers

- [`README.md`](README.md) — orientation, how to launch an expedition, Lean build.
- [`ROADMAP.md`](ROADMAP.md) — the result-map + the Core/DLN formalisation-target ladder.
- [`docs/policies/`](docs/policies/) — expedition, claims, review, precision, bedrock, codex-consultation, statement-cards, writing-style (+ the reader-facing exposition trio).
- [`docs/expositions/`](docs/expositions/) — the curated reader-facing digest (starts with `paper-digest/high-level-overview.md`).
- [`.claude/skills/`](.claude/skills/) — lean-formalisation, local-codex-consult.
- [`lean/CLAUDE.md`](lean/CLAUDE.md) — Lean build + Mathlib conventions; the Core/DLN split.
- [`theory/`](theory/) — markdown theory workspace.
- [`TEMPLATE.md`](TEMPLATE.md) — how to instantiate this harness for a new paper.

exec
/bin/bash -lc "sed -n '1,240p' rung2-regular-section-answer.md" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
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
session id: 019efac4-d415-73b1-9619-78506d57fd65
--------
user
# Codex consult — rung 2: the REGULAR-section gap in the single-chart trivialization (Lean v4.29)

Route (c), rung 2. Goal: a `varietyDim`-preserving (REGULAR, not bare-set) trivialization of one
pivot chart, `mult⁻¹(U_P) ∩ Σ^r ≅_reg U_P × F`, so that `varietyDim(chart) = varietyDim U_P +
varietyDim F = δ + varietyDim F`.

## The gap I hit

The LANDED `exists_baseChange_of_rank_eq` is EXISTENTIAL: for each rank-r target `B` it gives SOME
`P ∈ H = GL_{d_N}×GL_{d_0}` with `P_N·E·P_0⁻¹ = B` (E = the standard rank-r `diag(I_r,0)`). The sweep
`Σ^r = ⋃_P (P•·)''F` is then a set-union. But a per-point existential `P` does NOT give a REGULAR
map `U_P → H` (a section), and Codex's own prior warning was: a bare set bijection does not preserve
`varietyDim`. So the question is whether I can upgrade the existential to a regular section on a
pivot chart.

## The structures available

- `U_P ⊆ Mat^{=r}` = pivot chart where the top-left `r×r` minor `ΔP` is invertible (a principal open
  `D(ΔP)`; `Localization.Away ΔP`). The engine has the deep pivot minor `ΔPdeep` and
  `Localization.Away (ΔPdeep)` already (`DeepChartRing`).
- `H` acts, `mult` is `H`-equivariant (`mult_smul`), `F = mult⁻¹(E)`.
- `varietyDim` is set-level (`ringKrullDim` of `vanishingIdeal`), radical-insensitive (just landed).

## My questions

1. **On the pivot chart `D(ΔP)`, is there a REGULAR (polynomial-in-entries-after-inverting-ΔP)
   normalizing section `σ : U_P → H` with `σ(B)_N · E · σ(B)_0⁻¹ = B` for all `B ∈ U_P`?** For a
   rank-r matrix with invertible top-left r×r block, row/column reduction to `diag(I_r,0)` uses only
   the inverse of that block and its Schur complement — all REGULAR after inverting `ΔP`. So I expect
   YES, a regular section EXISTS on each pivot chart (this is the standard "Bruhat/pivot cell is an
   affine cell with a regular trivialization" fact). Confirm, and tell me the cleanest Lean-shape:
   build `σ` as an explicit `H`-valued regular map via the block inverse, OR is there a slicker route?

2. **Given a regular section `σ`, is the chart iso `Φ : mult⁻¹(U_P) ∩ Σ^r → U_P × F`, `A ↦ (mult A,
   σ(mult A)⁻¹ • A)` a regular iso?** Inverse `(B, A') ↦ σ(B) • A'`. Both directions are regular
   (compositions of `mult`, the regular `σ`, and the `H`-action which is regular). So this should be
   a genuine regular iso, hence `varietyDim`-preserving. Any subtlety (e.g. does `σ(mult A)⁻¹ • A ∈ F`
   need `mult A ∈ U_P` exactly, and is the codomain `U_P × F` or `U_P × (chart∩F)`)?

3. **Is "regular iso ⟹ equal `varietyDim`" cheap in Lean v4.29?** `varietyDim` is
   `ringKrullDim`-of-coordinate-ring; a regular iso of affine varieties induces a `k`-algebra iso of
   coordinate rings, and `ringKrullDim_eq_of_ringEquiv` transports. But the engine's `varietyDim` is
   defined on SUBSETS of a FIXED affine space `RepCoord d → k` via `vanishingIdeal` in THAT ambient
   ring — transporting `varietyDim` across a regular iso between subsets of DIFFERENT ambient spaces
   (`mult⁻¹(U)∩Σ^r ⊆ RepCoord d` vs `U_P × F ⊆ (base coords) × (RepCoord d)`) needs the coordinate-
   ring iso, not just the set iso. Is the cleanest path to (a) define `varietyDim` intrinsically via
   the coordinate-ring `ringKrullDim` and prove a `ringEquiv`-transport lemma, or (b) stay in one
   ambient space (realize `U_P × F` as a subset of `RepCoord d` too)? Which is less Lean friction?

4. **Could I AVOID the regular section entirely?** E.g. is there a cleaner route to `varietyDim Σ^r =
   δ + dim F` that does NOT build the explicit chart trivialization — e.g. (a) the action map `α : H
   × F → Σ^r` regular + surjective, `dim Σ^r = dim(H×F) − dim(generic α-fibre)`, with the generic
   α-fibre = the stabilizer (`dim H − δ`)? That reintroduces a fibre-dim count for `α` but over a
   GROUP (homogeneous, so the generic fibre dim might be computable as a stabilizer dim). Is that
   cheaper than the pivot-chart trivialization, or does it hit the same product-dimension wall?

Give me: confirm the regular section exists on a pivot chart (and the cleanest Lean construction),
the cleanest `varietyDim`-transport shape, and whether the chart route or the action-map route is
cheaper. Be concrete about the Lean friction in transporting set-level `varietyDim` across a regular
iso.

codex
I’ll inspect the local Lean/exposition scaffolding around `varietyDim`, pivot charts, and the landed rank/base-change lemmas so the advice matches the actual API rather than an abstract algebraic-geometry answer.
exec
/bin/bash -lc 'pwd && rg -n "def varietyDim|varietyDim|vanishingIdeal|ringKrullDim|exists_baseChange_of_rank_eq|DeepChartRing|ΔPdeep|mult_smul|baseChange|rank_eq" -S .' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
exec
/bin/bash -lc 'ls -la && find .. -maxdepth 2 -name CLAUDE.md -o -name README.md -o -name AGENTS.md' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
total 1508
drwxrwxr-x 2 ubuntu ubuntu    4096 Jun 24 17:54 .
drwxrwxr-x 3 ubuntu ubuntu    4096 Jun 24 17:51 ..
-rw-rw-r-- 1 ubuntu ubuntu  432309 Jun 24 17:45 noncirc-setlevel-answer.md
-rw-rw-r-- 1 ubuntu ubuntu    5060 Jun 24 17:42 noncirc-setlevel-prompt.md
-rw-rw-r-- 1 ubuntu ubuntu 1066445 Jun 24 17:35 route-choice-answer.md
-rw-rw-r-- 1 ubuntu ubuntu    6557 Jun 24 17:32 route-choice-prompt.md
-rw-rw-r-- 1 ubuntu ubuntu    5236 Jun 24 17:54 rung2-regular-section-answer.md
-rw-rw-r-- 1 ubuntu ubuntu    4417 Jun 24 17:54 rung2-regular-section-prompt.md

 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
./rung2-regular-section-prompt.md:3:Route (c), rung 2. Goal: a `varietyDim`-preserving (REGULAR, not bare-set) trivialization of one
./rung2-regular-section-prompt.md:4:pivot chart, `mult⁻¹(U_P) ∩ Σ^r ≅_reg U_P × F`, so that `varietyDim(chart) = varietyDim U_P +
./rung2-regular-section-prompt.md:5:varietyDim F = δ + varietyDim F`.
./rung2-regular-section-prompt.md:9:The LANDED `exists_baseChange_of_rank_eq` is EXISTENTIAL: for each rank-r target `B` it gives SOME
./rung2-regular-section-prompt.md:13:`varietyDim`. So the question is whether I can upgrade the existential to a regular section on a
./rung2-regular-section-prompt.md:19:  `D(ΔP)`; `Localization.Away ΔP`). The engine has the deep pivot minor `ΔPdeep` and
./rung2-regular-section-prompt.md:20:  `Localization.Away (ΔPdeep)` already (`DeepChartRing`).
./rung2-regular-section-prompt.md:21:- `H` acts, `mult` is `H`-equivariant (`mult_smul`), `F = mult⁻¹(E)`.
./rung2-regular-section-prompt.md:22:- `varietyDim` is set-level (`ringKrullDim` of `vanishingIdeal`), radical-insensitive (just landed).
./rung2-regular-section-prompt.md:37:   a genuine regular iso, hence `varietyDim`-preserving. Any subtlety (e.g. does `σ(mult A)⁻¹ • A ∈ F`
./rung2-regular-section-prompt.md:40:3. **Is "regular iso ⟹ equal `varietyDim`" cheap in Lean v4.29?** `varietyDim` is
./rung2-regular-section-prompt.md:41:   `ringKrullDim`-of-coordinate-ring; a regular iso of affine varieties induces a `k`-algebra iso of
./rung2-regular-section-prompt.md:42:   coordinate rings, and `ringKrullDim_eq_of_ringEquiv` transports. But the engine's `varietyDim` is
./rung2-regular-section-prompt.md:43:   defined on SUBSETS of a FIXED affine space `RepCoord d → k` via `vanishingIdeal` in THAT ambient
./rung2-regular-section-prompt.md:44:   ring — transporting `varietyDim` across a regular iso between subsets of DIFFERENT ambient spaces
./rung2-regular-section-prompt.md:46:   ring iso, not just the set iso. Is the cleanest path to (a) define `varietyDim` intrinsically via
./rung2-regular-section-prompt.md:47:   the coordinate-ring `ringKrullDim` and prove a `ringEquiv`-transport lemma, or (b) stay in one
./rung2-regular-section-prompt.md:50:4. **Could I AVOID the regular section entirely?** E.g. is there a cleaner route to `varietyDim Σ^r =
./rung2-regular-section-prompt.md:58:the cleanest `varietyDim`-transport shape, and whether the chart route or the action-map route is
./rung2-regular-section-prompt.md:59:cheaper. Be concrete about the Lean friction in transporting set-level `varietyDim` across a regular
./rung2-regular-section-answer.md:18:Route (c), rung 2. Goal: a `varietyDim`-preserving (REGULAR, not bare-set) trivialization of one
./rung2-regular-section-answer.md:19:pivot chart, `mult⁻¹(U_P) ∩ Σ^r ≅_reg U_P × F`, so that `varietyDim(chart) = varietyDim U_P +
./rung2-regular-section-answer.md:20:varietyDim F = δ + varietyDim F`.
./rung2-regular-section-answer.md:24:The LANDED `exists_baseChange_of_rank_eq` is EXISTENTIAL: for each rank-r target `B` it gives SOME
./rung2-regular-section-answer.md:28:`varietyDim`. So the question is whether I can upgrade the existential to a regular section on a
./rung2-regular-section-answer.md:34:  `D(ΔP)`; `Localization.Away ΔP`). The engine has the deep pivot minor `ΔPdeep` and
./rung2-regular-section-answer.md:35:  `Localization.Away (ΔPdeep)` already (`DeepChartRing`).
./rung2-regular-section-answer.md:36:- `H` acts, `mult` is `H`-equivariant (`mult_smul`), `F = mult⁻¹(E)`.
./rung2-regular-section-answer.md:37:- `varietyDim` is set-level (`ringKrullDim` of `vanishingIdeal`), radical-insensitive (just landed).
./rung2-regular-section-answer.md:52:   a genuine regular iso, hence `varietyDim`-preserving. Any subtlety (e.g. does `σ(mult A)⁻¹ • A ∈ F`
./rung2-regular-section-answer.md:55:3. **Is "regular iso ⟹ equal `varietyDim`" cheap in Lean v4.29?** `varietyDim` is
./rung2-regular-section-answer.md:56:   `ringKrullDim`-of-coordinate-ring; a regular iso of affine varieties induces a `k`-algebra iso of
./rung2-regular-section-answer.md:57:   coordinate rings, and `ringKrullDim_eq_of_ringEquiv` transports. But the engine's `varietyDim` is
./rung2-regular-section-answer.md:58:   defined on SUBSETS of a FIXED affine space `RepCoord d → k` via `vanishingIdeal` in THAT ambient
./rung2-regular-section-answer.md:59:   ring — transporting `varietyDim` across a regular iso between subsets of DIFFERENT ambient spaces
./rung2-regular-section-answer.md:61:   ring iso, not just the set iso. Is the cleanest path to (a) define `varietyDim` intrinsically via
./rung2-regular-section-answer.md:62:   the coordinate-ring `ringKrullDim` and prove a `ringEquiv`-transport lemma, or (b) stay in one
./rung2-regular-section-answer.md:65:4. **Could I AVOID the regular section entirely?** E.g. is there a cleaner route to `varietyDim Σ^r =
./rung2-regular-section-answer.md:73:the cleanest `varietyDim`-transport shape, and whether the chart route or the action-map route is
./rung2-regular-section-answer.md:74:cheaper. Be concrete about the Lean friction in transporting set-level `varietyDim` across a regular
./rung2-regular-section-answer.md:78:I’ll inspect the local Lean/exposition scaffolding around `varietyDim`, pivot charts, and the landed rank/base-change lemmas so the advice matches the actual API rather than an abstract algebraic-geometry answer.
./noncirc-setlevel-prompt.md:4:`hSweep : varietyDim Σ^r = δ + varietyDim F`. Rung 1 = a single-chart trivialization. The DECISIVE
./noncirc-setlevel-prompt.md:5:de-risk: is the SET-LEVEL / `varietyDim` version non-circular, given a PRIOR attempt (R2-3b-4) at a
./noncirc-setlevel-prompt.md:23:For `hSweep` I do NOT need reducedness. `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`
./noncirc-setlevel-prompt.md:24:and `vanishingIdeal Z` is ALREADY radical (it's a vanishing ideal). Krull dim is RADICAL-INSENSITIVE:
./noncirc-setlevel-prompt.md:25:`ringKrullDim (R⧸I) = ringKrullDim (R⧸√I)`. So `varietyDim` reads only the REDUCED/variety structure;
./noncirc-setlevel-prompt.md:36:1. **Is `varietyDim` genuinely radical-insensitive in Mathlib v4.29** — i.e. is `ringKrullDim (R⧸I) =
./noncirc-setlevel-prompt.md:37:   ringKrullDim (R⧸ I.radical)` available (or `ringKrullDim` factors through `√`)? Name the lemma if
./noncirc-setlevel-prompt.md:43:   chart's normalizing gauge. This is a bijection of SETS / a `varietyDim`-preserving map. Does
./noncirc-setlevel-prompt.md:48:   `varietyDim(U×F) = varietyDim U + varietyDim F` secretly needs flatness/reducedness.
./noncirc-setlevel-prompt.md:50:3. **The product-dimension step `varietyDim(U × F) = varietyDim U + varietyDim F`.** For a product of
./noncirc-setlevel-prompt.md:52:   (as `ringKrullDim (A ⊗_k B) = ringKrullDim A + ringKrullDim B`, or a variety-dimension product)?
./noncirc-setlevel-prompt.md:58:4. **The glue over the finite pivot cover.** `varietyDim(⋃_i Z_i) = max_i varietyDim(Z_i)` for a
./noncirc-setlevel-prompt.md:59:   finite cover — is that radical-insensitive and in Mathlib (or trivial from `ringKrullDim` of a
./noncirc-setlevel-prompt.md:62:5. **Net verdict:** does the SET-LEVEL/`varietyDim` route (c) dodge the R2-3b-4 circularity? If YES,
./noncirc-setlevel-prompt.md:67:The key thing I need from you: a clean YES/NO on whether radical-insensitivity of `varietyDim` lets
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
./route-choice-answer.md:453:./CLAUDE.md:81:  set-level route `vanishingIdeal (shifted) = comap (algEquiv) (vanishingIdeal)` + `height_comap` is
./route-choice-answer.md:466:./DLNFibre/Core/OrbitPullbackDim.lean:6:# `DLNFibre.Core.OrbitPullbackDim` — route-c setup: `varietyDim(Z_M) = ringKrullDim((μ_M^*).range)`
./route-choice-answer.md:467:./DLNFibre/Core/OrbitPullbackDim.lean:16:1. **Ideal identification.** `varietyDim Z_M = ringKrullDim (MvPolynomial (RepCoord d) k ⧸
./route-choice-answer.md:468:./DLNFibre/Core/OrbitPullbackDim.lean:17:   ker μ_M^*)`, immediate from the `varietyDim` definition, the Abeasis–Del Fra ideal equality L6.4
./route-choice-answer.md:469:./DLNFibre/Core/OrbitPullbackDim.lean:18:   (`vanishingIdeal_orbitRankLocus_eq_orbitSet`), and the orbit↔kernel identity
./route-choice-answer.md:470:./DLNFibre/Core/OrbitPullbackDim.lean:19:   (`range_orbitMap` + `vanishingIdeal_range_orbitMap_eq_ker`).
./route-choice-answer.md:471:./DLNFibre/Core/OrbitPullbackDim.lean:25:The headline `varietyDim_eq_ringKrullDim_range_orbitPullback` hands A4 a finitely-generated domain
./route-choice-answer.md:472:./DLNFibre/Core/OrbitPullbackDim.lean:48:`MvPolynomial (RepCoord d) k ⧸ ker μ_M^*`. `varietyDim` definition, then L6.4
./route-choice-answer.md:473:./DLNFibre/Core/OrbitPullbackDim.lean:49:(`vanishingIdeal_orbitRankLocus_eq_orbitSet`) and the orbit↔kernel identity
./route-choice-answer.md:474:./DLNFibre/Core/OrbitPullbackDim.lean:50:(`range_orbitMap` + `vanishingIdeal_range_orbitMap_eq_ker`) rewrite the vanishing ideal to
./route-choice-answer.md:475:./DLNFibre/Core/OrbitPullbackDim.lean:52:theorem varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker [Infinite k]
./route-choice-answer.md:476:./DLNFibre/Core/OrbitPullbackDim.lean:54:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./route-choice-answer.md:477:./DLNFibre/Core/OrbitPullbackDim.lean:57:  rw [varietyDim, vanishingIdeal_orbitRankLocus_eq_orbitSet M, ← range_orbitMap,
./route-choice-answer.md:478:./DLNFibre/Core/OrbitPullbackDim.lean:58:    vanishingIdeal_range_orbitMap_eq_ker M]
./route-choice-answer.md:479:./DLNFibre/Core/OrbitPullbackDim.lean:70:transcendence degree. Combines `varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker` with the
./route-choice-answer.md:480:./DLNFibre/Core/OrbitPullbackDim.lean:74:theorem varietyDim_eq_ringKrullDim_range_orbitPullback [Infinite k] {d : Fin (N + 1) → ℕ}
./route-choice-answer.md:481:./DLNFibre/Core/OrbitPullbackDim.lean:76:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./route-choice-answer.md:482:./DLNFibre/Core/OrbitPullbackDim.lean:78:  rw [varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker M,
./route-choice-answer.md:483:./DLNFibre/Core/OrbitPullbackDim.lean:89:/-- The headline at the concrete `(2,2,2)/ℚ` tuple: `varietyDim (canonicalCoord '' orbitRankLocus
./route-choice-answer.md:484:./DLNFibre/Core/OrbitPullbackDim.lean:93:    varietyDim (canonicalCoord dWitness '' orbitRankLocus tupleWitnessQ)
./route-choice-answer.md:485:./DLNFibre/Core/OrbitPullbackDim.lean:95:  varietyDim_eq_ringKrullDim_range_orbitPullback tupleWitnessQ
./route-choice-answer.md:491:./DLNFibre/DLN/RlctPayoff.lean:132:  -- RHS: ⨅ over corner-0 tuples M, of `codimRepCanonical (Ō_M) = (vanishingIdeal Ō_M).height`.
./route-choice-answer.md:492:./DLNFibre/DLN/RlctPayoff.lean:136:    have hmem : (MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
./route-choice-answer.md:493:./DLNFibre/DLN/RlctPayoff.lean:139:        ≤ MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
./route-choice-answer.md:494:./DLNFibre/DLN/RlctPayoff.lean:142:    haveI : (MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
./route-choice-answer.md:495:./DLNFibre/DLN/RlctPayoff.lean:144:      isPrime_vanishingIdeal_orbitRankLocus M
./route-choice-answer.md:496:./DLNFibre/DLN/RlctPayoff.lean:197:    exact Ideal.height_ne_top (isPrime_vanishingIdeal_orbitRankLocus M).ne_top
./route-choice-answer.md:497:./DLNFibre/DLN/RlctPayoff.lean:226:          (isPrime_vanishingIdeal_orbitRankLocus (realizerD (k := k) hm₀)).ne_top
./route-choice-answer.md:498:./DLNFibre/Core/CCodimCornerMono.lean:329:    exact Ideal.height_ne_top (isPrime_vanishingIdeal_orbitRankLocus _).ne_top
./route-choice-answer.md:499:./DLNFibre/Core/CCodimCornerMono.lean:374:partition. From G3 (`minimalPrimes_sigmaIdeal_eq`) `p = vanishingIdeal (Ō_{M'})` for a corner-`≤ r`
./route-choice-answer.md:500:./DLNFibre/Core/CCodimCornerMono.lean:385:  -- G3: `p` is a corner-`≤ r` orbit ideal `vanishingIdeal (Ō_{M'})`
./route-choice-answer.md:503:./DLNFibre/Core/DeterminantalStratumDim.lean:24:   `isPrime_vanishingIdeal_orbitRankLocus`).
./route-choice-answer.md:506:./DLNFibre/Core/DeterminantalStratumDim.lean:29:4. **The catenary bridge** (LANDED `codimRep_add_varietyDim_eq_card`): `codim + dim = card = m·n`,
./route-choice-answer.md:512:./DLNFibre/Core/DeterminantalStratumDim.lean:196:flattening of) `productRankLocusLE ![n,m] r` is prime — it is `vanishingIdeal (Ō_{M₀})` of a single
./route-choice-answer.md:513:./DLNFibre/Core/DeterminantalStratumDim.lean:197:orbit closure (LANDED `isPrime_vanishingIdeal_orbitRankLocus`). -/
./route-choice-answer.md:514:./DLNFibre/Core/DeterminantalStratumDim.lean:198:theorem isPrime_vanishingIdeal_productRankLocusLE_stratum [IsAlgClosed k] (n m r : ℕ)
./route-choice-answer.md:515:./DLNFibre/Core/DeterminantalStratumDim.lean:200:    (vanishingIdeal k
./route-choice-answer.md:518:./DLNFibre/Core/DeterminantalStratumDim.lean:205:  exact isPrime_vanishingIdeal_orbitRankLocus M₀
./route-choice-answer.md:520:./DLNFibre/Core/DeterminantalStratumDim.lean:224:> `varietyDim (Mat^{rk ≤ r}_{m × n}) = r · (n + m − r)`.
./route-choice-answer.md:521:./DLNFibre/Core/DeterminantalStratumDim.lean:229:theorem varietyDim_productRankLocusLE_stratum [IsAlgClosed k] [CharZero k] (n m r : ℕ)
./route-choice-answer.md:522:./DLNFibre/Core/DeterminantalStratumDim.lean:231:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./route-choice-answer.md:524:./DLNFibre/Core/DeterminantalStratumDim.lean:237:  have hbridge := codimRep_add_varietyDim_eq_card (canonicalCoord (dStratum n m)) Z
./route-choice-answer.md:525:./DLNFibre/Core/DeterminantalStratumDim.lean:238:    (isPrime_vanishingIdeal_productRankLocusLE_stratum (k := k) n m r hn hm)
./route-choice-answer.md:527:./DLNFibre/Core/DeterminantalStratumDim.lean:249:  -- `hbridge : (n−r)(m−r) + varietyDim Z = m·n`
./route-choice-answer.md:528:./DLNFibre/Core/DeterminantalStratumDim.lean:258:  have heq : (((n - r) * (m - r) : ℕ) : ℕ∞) + varietyDim (canonicalCoord (dStratum n m) '' Z)
./route-choice-answer.md:529:./DLNFibre/Core/DeterminantalStratumDim.lean:268:    varietyDim (canonicalCoord (dStratum 2 2) '' productRankLocusLE (k := k) (dStratum 2 2) 1)
./route-choice-answer.md:530:./DLNFibre/Core/DeterminantalStratumDim.lean:270:  have h := varietyDim_productRankLocusLE_stratum (k := k) 2 2 1 (by norm_num) (by norm_num)
./route-choice-answer.md:531:./DLNFibre/Core/RankLocusClosed.lean:263:fact `zeroLocus (vanishingIdeal (zeroLocus I)) = zeroLocus I`). This is the topological content of
./route-choice-answer.md:532:./DLNFibre/Core/RankLocusClosed.lean:268:  exact (MvPolynomial.zeroLocus_vanishingIdeal_galoisConnection
./route-choice-answer.md:533:./DLNFibre/Core/RankLocusClosed.lean:289:/-- **The easy ideal inclusion.** `vanishingIdeal (canonicalCoord '' orbitRankLocus M) ≤
./route-choice-answer.md:534:./DLNFibre/Core/RankLocusClosed.lean:290:vanishingIdeal (O_M)`: at the ideal level the easy orbit inclusion `O_M ⊆ orbitRankLocus M` is the
./route-choice-answer.md:535:./DLNFibre/Core/RankLocusClosed.lean:291:*trivial* containment of vanishing ideals (`vanishingIdeal` is order-reversing). The genuine content
./route-choice-answer.md:536:./DLNFibre/Core/RankLocusClosed.lean:293:theorem vanishingIdeal_orbitRankLocus_le_orbitSet {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :

exec
/bin/bash -lc "rg -n \"def varietyDim|theorem .*varietyDim|ringKrullDim_quotient|radical|vanishingIdeal_isRadical|DeepChartRing|ΔPdeep|pivot|Localization\\.Away|exists_baseChange_of_rank_eq|baseChange|mult_smul|def mult|rank_eq|ProductRank\" -S /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/*.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:101:-- Determinantal pivot-chart presentation (rank-chart build G2-1): the Schur rank criterion
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:106:-- (universal-coefficient route, no invertible pivot), and the Schur expression = an (r+1)-minor ⟹
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:125:-- the open R2-3b wall) — `fibreGenIdeal` radical + the radical-collapse of MultComorphism pt4. The
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:128:-- Deep chart ring (R2-3b-1+2, the residual G2-3 wall foundation): `Sred = Localization.Away(ΔPdeep) ⧸
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:133:import DLNFibre.Core.DeepChartRing
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:135:-- (= landed `BaseChange.baseChange`) on the generic tuple, `gaugeEquiv d P`, over arbitrary CommRing R,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:139:-- HEIGHT-DIRECT route, rung H1 (radical-insensitive retarget): `Ideal.height_radical` (height(radical I)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:141:-- height of the cut ideal, [IsAlgClosed k] only — NO radicality). Decouples the codim from the (off-path)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:142:-- radicality wall: the RLCT payoff needs only this height.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:155:-- via `mult_smul` + `exists_baseChange_of_rank_eq`; every translate same codim (G1). The reachable part
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:159:-- Reducible-locus catenary: `height I + ringKrullDim(R⧸I) = card` for ANY proper I (no radicality), and
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitDifferentialRank.lean:32:5. **Base-change rank** (`finrank_range_baseChange`, landed) + `Submodule.finrank_mono` close the bound.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitDifferentialRank.lean:281:        (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitDifferentialRank.lean:282:          (by rw [Subspace.dual_finrank_eq])).mp traceFun_injective
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitDifferentialRank.lean:320:    exact (Submodule.equivMapOfInjective _ eV.injective _).symm.finrank_eq
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitDifferentialRank.lean:568:its lift factors through `(deltaT M).baseChange K`, so `finrank_K S ≤ finrank_K (range (deltaT.bc)) =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitDifferentialRank.lean:569:finrank_k (range deltaT) = finrank_k (range δ⁰)` (`finrank_range_baseChange` + `finrank_range_deltaT`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitDifferentialRank.lean:629:  -- (3) `finrank_K W ≤ finrank_K (range (deltaT.baseChange K)) = finrank_k (range δ⁰)`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitDifferentialRank.lean:630:  have h2 : finrank K W ≤ finrank K (LinearMap.range ((deltaT M).baseChange K)) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitDifferentialRank.lean:633:        = (pairMC.liftBaseChange K).comp ((deltaT M).baseChange K) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitDifferentialRank.lean:634:      ext x; simp [LinearMap.liftBaseChange_tmul, LinearMap.baseChange_tmul]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitDifferentialRank.lean:637:  have h3 : finrank K (LinearMap.range ((deltaT M).baseChange K))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitDifferentialRank.lean:639:    rw [finrank_range_baseChange, finrank_range_deltaT]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitDifferentialRank.lean:664:theorem varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:5:# `DLNFibre.Core.DeepChartRing` — the deep chart ring `Sred` + the localized base→total map
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:13:on the pivot chart, and the localized base→total `k`-algebra map that gives `Sred` its
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:19:1. `ΔPdeep d r hp hq` — the deep pivot minor: the determinant of the top-left `r×r` submatrix of the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:22:   `Localization.Away (ΔPdeep …)` (the deep analog of `Iad`).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:23:3. `Sred d r hp hq := Localization.Away (ΔPdeep …) ⧸ IadDeep …` — the deep chart quotient ring, with
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:33:   pivot minor `detPivotPoly` to the deep `ΔPdeep` (det commutes with `aeval`, `AlgHom.map_det`),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:41:7. `baseLocMap` / `schurToSred` — the localized base map `Localization.Away detPivotPoly →ₐ[k]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:42:   Localization.Away (ΔPdeep …)` (`IsLocalization.Away.mapₐ`), lifted to the quotients
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:53:arbitrary coefficient ring `R`, via `AlgEquiv.ofAlgHom`, **not** `baseChangeAlgEquiv` which carries
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:104:/-- **The deep pivot minor** `ΔPdeep d r`: the determinant of the top-left `r×r` submatrix of the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:106:inverting it is the pivot chart. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:107:noncomputable def ΔPdeep (d : Fin (N + 1) → ℕ) (r : ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:114:pushed into the localized total ring `Localization.Away (ΔPdeep …)`. The deep analog of `Iad`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:117:    Ideal (Localization.Away (ΔPdeep (k := k) d r hp hq)) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:119:    (Localization.Away (ΔPdeep (k := k) d r hp hq)))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:121:/-- **The deep chart ring** `Sred d r := Localization.Away (ΔPdeep …) ⧸ IadDeep …`: the localized
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:122:chart quotient of the rank-`≤ r` product locus for general `d`, on the pivot chart. The `CommRing` /
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:126:  Localization.Away (ΔPdeep (k := k) d r hp hq) ⧸ IadDeep (k := k) d r hp hq
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:132:It is **cheap** here: `IadDeep = (sigmaIdeal d r).map (algebraMap …)` is radical because
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:133:`sigmaIdeal` is radical (`vanishingIdeal_isRadical`, over `[IsAlgClosed k]`) and localization
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:134:carries radical
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:135:ideals to radical ideals (`IsLocalization.map_radical`); a quotient by a radical ideal is reduced
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:138:/-- **`IadDeep` is radical** (`[IsAlgClosed k]`): the localized image of the radical determinantal
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:139:base ideal `sigmaIdeal d r`. Via `IsLocalization.map_radical`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:140:(`(I.map …).radical = I.radical.map …`) and `sigmaIdeal`'s radicality
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:141:(`vanishingIdeal_isRadical`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:146:    rw [sigmaIdeal]; exact vanishingIdeal_isRadical _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:147:  rw [← Ideal.radical_eq_iff, IadDeep,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:148:    ← IsLocalization.map_radical (M := Submonoid.powers (ΔPdeep (k := k) d r hp hq)),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:149:    hsig.radical]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:152:`Sred = Localization.Away ΔPdeep ⧸ IadDeep` with `IadDeep` radical (`IadDeep_isRadical`); a quotient
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:153:by a radical ideal is reduced
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:163:`deepBaseComap` carries the `N = 1` pivot minor `detPivotPoly` to the deep `ΔPdeep` (making the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:167:/-- **The pivot-minor transport** (load-bearing): `deepBaseComap d` carries the `N = 1` pivot minor
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:168:`detPivotPoly (d 0) (d last) r` to the deep pivot minor `ΔPdeep d r`. The determinant commutes with
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:169:the algebra map (`AlgHom.map_det`); each pivot entry `X ⟨0, (castLE i, castLE j)⟩` goes to
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:176:      = ΔPdeep (k := k) d r hp hq := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:177:  rw [detPivotPoly, ΔPdeep, AlgHom.map_det]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:248:The localized base map `Localization.Away detPivotPoly →ₐ[k] Localization.Away (ΔPdeep …)`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:249:(`IsLocalization.Away.mapₐ deepBaseComap detPivotPoly`, well-typed by the transport
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:253:/-- **The localized base map** `Localization.Away (detPivotPoly …) →ₐ[k]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:254:Localization.Away (ΔPdeep …)`, `IsLocalization.Away.mapₐ` of the deep base comorphism
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:256:codomain localization instance at `deepBaseComap d (detPivotPoly …)` is `ΔPdeep`'s (the transport
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:260:    Localization.Away (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq) →ₐ[k]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:261:      Localization.Away (ΔPdeep (k := k) d r hp hq) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:262:  haveI : IsLocalization.Away
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:264:      (Localization.Away (ΔPdeep (k := k) d r hp hq)) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:266:  exact IsLocalization.Away.mapₐ _ _ (deepBaseComap d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:270:two localization maps (`IsLocalization.Away.mapₐ` / `IsLocalization.map` on the base ring). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:276:          (Localization.Away (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq)) x)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:277:      = algebraMap (MvPolynomial (RepCoord d) k) (Localization.Away (ΔPdeep (k := k) d r hp hq))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:279:  haveI : IsLocalization.Away
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:281:      (Localization.Away (ΔPdeep (k := k) d r hp hq)) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:283:  rw [baseLocMap, IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:304:/-- **The localized base→total map on the quotients** `(Localization.Away detPivotPoly ⧸ Iad) →ₐ[k]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:309:    (Localization.Away (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:357:`baseChangeAlgEquiv`, which carries `[Infinite k]` from polynomial-function ext). The contract — two
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:388:`deepBaseComap_detPivot` at the `N = 1` stratum `dStratum 2 2`, `r = 1`, where the deep pivot minor
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:407:/-- The pivot-minor transport fires at the `N = 1` stratum `dStratum 2 2`, `r = 1`:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:408:`deepBaseComap (detPivotPoly …) = ΔPdeep …`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:412:      = ΔPdeep (k := AlgebraicClosure ℚ) (dStratum 2 2) 1 h h :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:419:    (Localization.Away
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:10:`codimRepCanonical (fibre d B) = Ideal.height (fibreGenIdeal d B)` (H1, radical-insensitive), and
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:95:`Core.FibreNormalForm.codimRepCanonical_fibre_eq_of_rank_eq` (LANDED, flatness-free, via the GL×GL
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:103:closer gives `codim(fibre B*) = v`; G1 (`codimRepCanonical_fibre_eq_of_rank_eq`) transports it. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:111:  rw [codimRepCanonical_fibre_eq_of_rank_eq d hN B Bstar (by rw [hB, hBstar])]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:20:* `baseChange_normalForm` — **the Gabriel normal-form object** (cast-free): every tuple is
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:24:`RankPattern.cumulDiffEquiv` + the realizability in `baseChange_normalForm` assemble into a genuine
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:27:**Typeclass.** `Field k` (the barcode existence; `Tuple`/`baseChange` themselves only need
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:130:theorem baseChange_of_intertwine {d : Fin (N + 1) → ℕ} (A B : Tuple (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:145:  rw [smul_eq_baseChange, baseChange_apply]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:161:intertwiner `φ_t` of the two `mulVecLin` chains, which `baseChange_of_intertwine` turns into the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:250:  refine baseChange_of_intertwine A B φ (fun e ↦ (bvA e.castSucc).ext (fun s ↦ ?_))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:340:theorem baseChange_normalForm {d : Fin (N + 1) → ℕ} (A : Tuple (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:369:list `L` of `baseChange_normalForm` has its multiplicity array pinned by `A`'s rank pattern: there
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:373:`diff_cumul` inversion of the cumulative equality in `baseChange_normalForm`; makes the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:381:  obtain ⟨L, h, P, hP, hbd, hcum⟩ := baseChange_normalForm A
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:403:object `baseChange_normalForm` fires on the witness — so the complete invariant and the Gabriel
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:521:  obtain ⟨L, h, P, hP, _, _⟩ := baseChange_normalForm tupleWitnessRankOneQ
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:528:  obtain ⟨L, h, P, hP, _, _⟩ := baseChange_normalForm tupleWitnessQ
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodim.lean:26:the map *is* flat — a substantial new build (explicit pivot charts, the section `D = C A⁻¹ B`, the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:27:Plus a base-change rank brick (`finrank_range_baseChange`): for a `k`-linear `f` between `k`-spaces
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:28:and a field extension `K/k`, `finrank K (range (f.baseChange K)) = finrank k (range f)` — base
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:104:`range f` finite-dimensional, and a field extension `K/k`, the base-changed map `f.baseChange K`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:105:(`= K ⊗ f`) has `finrank K (range (f.baseChange K)) = finrank k (range f)`. Factor
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:109:`≅ K ⊗ range f`); then `Module.finrank_baseChange`. The rank-side tool for the A4.3 bound. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:110:theorem finrank_range_baseChange {k : Type*} [Field k] {V W : Type*} [AddCommGroup V] [Module k V]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:113:    finrank K (LinearMap.range (f.baseChange K)) = finrank k (LinearMap.range f) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:114:  have hfac : f.baseChange K
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:115:      = (LinearMap.range f).subtype.baseChange K ∘ₗ f.rangeRestrict.baseChange K := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:116:    rw [← LinearMap.baseChange_comp, subtype_comp_codRestrict]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:118:  have hsurj : LinearMap.range (f.rangeRestrict.baseChange K) = ⊤ := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:119:    rw [LinearMap.range_eq_top, LinearMap.baseChange_eq_ltensor]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:122:  have hinj : Function.Injective ((LinearMap.range f).subtype.baseChange K) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:123:    rw [LinearMap.baseChange_eq_ltensor]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:125:  rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_baseChange]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartFlatnessProbe.lean:1:import Mathlib.RingTheory.Localization.Away.Basic
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartFlatnessProbe.lean:14:at the pivot minor and ask whether the chart-localized total ring is **flat** (via free, through the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartFlatnessProbe.lean:23:and the localized comorphism `Localization.Away.mapₐ` is constructible. But the *object* route
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartFlatnessProbe.lean:43:`Localization.Away.mapₐ f a : Localization.Away a →ₐ[R] Localization.Away (f a)` is the localized
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartFlatnessProbe.lean:44:algebra map. Specialised to F1's `multComap d` and a pivot element `Δ` of the base coordinate ring,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartFlatnessProbe.lean:47:/-- **The chart-localized comorphism exists.** For a base-ring element `Δ` (the pivot minor in
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartFlatnessProbe.lean:48:target coords), `Localization.Away.map` builds the localized comorphism of `mult`:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartFlatnessProbe.lean:53:    [IsLocalization.Away Δ Rb]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartFlatnessProbe.lean:55:    [IsLocalization.Away (multComap d Δ) Rt] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartFlatnessProbe.lean:57:  IsLocalization.Away.map Rb Rt (multComap d).toRingHom Δ
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:27:4. **`vanishingIdeal(fibre) = radical(fibreGenIdeal)`** — over `[IsAlgClosed k]`, the engine's
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:28:   Nullstellensatz (`vanishingIdeal_zeroLocus_eq_radical`) reads the fibre's vanishing ideal as the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:29:   radical of `fibreGenIdeal d B = span {multPoly d r c − C (B r c)}`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:75:noncomputable def multPoly (d : Fin (N + 1) → ℕ) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:157:/-- **The fibre's vanishing ideal is the radical of the generator ideal.** Over an algebraically
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:158:closed field, the engine's strong Nullstellensatz (`vanishingIdeal_zeroLocus_eq_radical`) reads the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:159:vanishing ideal of the fibre's image as the radical of `fibreGenIdeal d B`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:160:theorem vanishingIdeal_image_fibre_eq_radical [IsAlgClosed k] (d : Fin (N + 1) → ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:162:    vanishingIdeal k (canonicalCoord d '' (fibre d B)) = (fibreGenIdeal d B).radical := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:164:    vanishingIdeal_zeroLocus_eq_radical (K := k)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:171:noncomputable def multComap (d : Fin (N + 1) → ℕ) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:13:- `submult_baseChange` / `submult_smul` — **telescoping conjugation** of the interval sub-product:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:17:- `rankPattern_baseChange` / `rankPattern_smul` — **rank-pattern base-change invariance**:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:48:def baseChange (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d) : Tuple (k := k) d :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:52:@[simp] theorem baseChange_apply (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:54:    baseChange P A i = Units.val (P i.succ) * A i * Units.val ((P i.castSucc)⁻¹) := rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:57:theorem baseChange_one (A : Tuple (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:58:    baseChange (1 : BaseChangeGroup (k := k) d) A = A := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:60:  simp only [baseChange_apply, Pi.one_apply, Units.val_one, inv_one, Matrix.one_mul, Matrix.mul_one]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:63:theorem baseChange_mul (P Q : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:64:    baseChange (P * Q) A = baseChange P (baseChange Q A) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:66:  simp only [baseChange_apply, Pi.mul_apply, Units.val_mul, _root_.mul_inv_rev, Matrix.mul_assoc]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:70:  smul := baseChange
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:71:  one_smul := baseChange_one
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:72:  mul_smul := baseChange_mul
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:75:@[simp] theorem smul_eq_baseChange (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:76:    P • A = baseChange P A := rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:84:theorem submult_baseChange (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:86:    submult d (baseChange P A) i j hij
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:103:      rw [submult_succ d (baseChange P A) i p hcast, ih hcast, submult_succ d A i p hcast,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:104:          baseChange_apply]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:110:theorem submult_smul (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:114:  submult_baseChange P A i j hij
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:121:theorem rankPattern_baseChange (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:123:    rankPattern d (baseChange P A) i j hij = rankPattern d A i j hij := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:124:  rw [rankPattern, rankPattern, submult_baseChange,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:132:  rankPattern_baseChange P A i j hij
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalStratumDim.lean:229:theorem varietyDim_productRankLocusLE_stratum [IsAlgClosed k] [CharZero k] (n m r : ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:9:telescope away in `mult`), `mult` is `H`-equivariant (`FibreNormalForm.mult_smul`), and any two rank-`r`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:10:matrices are `H`-equivalent (`exists_baseChange_of_rank_eq`). Hence the **exact-rank locus is one
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:38:theorem isUnit_det_baseChangeGroup (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:49:        (isUnit_det_baseChangeGroup d P (Fin.last N)),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:51:        (by simpa using isUnit_det_baseChangeGroup d P⁻¹ 0)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:62:(`rank_endpoint_conj`). `(→)` `rank(mult A) = r = E.rank`, so `exists_baseChange_of_rank_eq` gives `P`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:73:    obtain ⟨P, hP⟩ := exists_baseChange_of_rank_eq d hN E (mult d A) (by rw [hE, hA])
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:92:E` is `fibre d (P_N·E·P_0⁻¹)`, a rank-`r` fibre; `G1` (`codimRepCanonical_fibre_eq_of_rank_eq`, the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:101:  codimRepCanonical_fibre_eq_of_rank_eq d hN _ E (rank_endpoint_conj d P E)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:8:The localized determinantal base ring `A_loc = Localization.Away detΔ` of the rank-`≤ r` stratum, on
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:9:the pivot chart, eliminates the bottom-right `B22` block: the Schur relation forces
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:14:`#B22block = (p−r)(q−r) = C`; `SchurVar = Δ ⊕ B12 ⊕ B21`, `#SchurVar = r(p+q−r) = δ`), so the pivot
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:33:/-- The free Schur coordinates `Δ ⊕ B12 ⊕ B21`: the top-left `r×r` pivot block `Δ`, the top-right
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:73:/-- The pivot split `Fin n ≃ Fin r ⊕ Fin (n−r)` (first `r` ↦ left). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:77:/-- `finSplit` sends a pivot index `castLE i` (`i < r`) to `Sum.inl i`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:96:/-- `finSplit` sends a non-pivot index `cast (natAdd r a)` (`≥ r`) to `Sum.inr a`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:105:/-- A pivot coordinate `⟨0, (castLE i, castLE j)⟩` (pivot row `i`, pivot column `j`, both `< r`)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:106:maps under the reindex into the `Δ`-block of `SchurVar`: `Sum.inr (Sum.inl (i, j))`. So the pivot
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:108:theorem repCoordReindex_pivot (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) (i j : Fin r) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:118:/-- A `B22` coordinate `⟨0, (cast (natAdd r a), cast (natAdd r b))⟩` (non-pivot row `a`, column `b`)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:134:/-- A `B12` coordinate (pivot row `i`, non-pivot column `b`) maps to the `B12`-block of `SchurVar`:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:148:/-- A `B21` coordinate (non-pivot row `a`, pivot column `i`) maps to the `B21`-block of `SchurVar`:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:185:/-! ## The pivot minor `detΔ` lives in the `SchurVar` block
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:187:Under the block reindex `Φ = renameEquiv (repCoordReindex)`, the pivot minor `detΔ = detPivotPoly`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:192:/-- The pivot determinant in the free Schur coordinate ring: `det` of the `Δ`-block coordinate
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:198:/-- Under the reindex `renameEquiv (repCoordReindex)`, the pivot minor `detΔ` maps to
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:200:with the algebra maps; each pivot entry `X ⟨0, (castLE i, castLE j)⟩` maps to the `Δ`-coordinate
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:201:`X (Sum.inr (Sum.inl (i, j)))`, by `repCoordReindex_pivot`.) -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:212:  exact repCoordReindex_pivot q p r hp hq i j
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:223:/-- Under `blockAlgEquiv`, the pivot minor `detΔ` becomes the constant `C detSchurS`: it lives
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:251:/-- `blockAlgEquiv` sends a `Δ`-pivot coordinate to the inner constant `C (X (Sum.inl (i, j)))`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:252:theorem blockAlgEquiv_X_pivot (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) (i j : Fin r) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:255:  rw [blockAlgEquiv, AlgEquiv.trans_apply, renameEquiv_apply, rename_X, repCoordReindex_pivot]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:275:`mvPolynomialX`), nonzero by `det_mvPolynomialX_ne_zero`. So `Sd = Localization.Away detSchurS` is a
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:295:On the pivot chart the Schur relation forces `B22 = B21 Δ⁻¹ B12`. The forced value lives in
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:296:`Sd = Localization.Away detSchurS`: `forcedB22 a b = (B21 · adjugate Δ · B12)_{ab} / detSchurS`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:310:/-- The forced `B22` value in `Sd = Localization.Away detSchurS`: the Schur numerator divided by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:311:`detSchurS` (`= B21 Δ⁻¹ B12` once the pivot det is inverted). The graph map whose ideal `J` the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:315:    [IsLocalization.Away (detSchurS (k := k) q p r) Sd] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:322:`#B22block = (p−r)(q−r) = C` (`height_graphIdeal_localization_eq` at `Sd = Localization.Away
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:326:    [IsLocalization.Away (detSchurS (k := k) q p r) Sd] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:54:theorem ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta [IsAlgClosed k] [CharZero k]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:102:    ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta n m r hn hm]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:106:`affine_domain_height_add_ringKrullDim_quotient_eq` is over `MvPolynomial (Fin n) k`. Transport it to
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:115:`affine_domain_height_add_ringKrullDim_quotient_eq` through `renameEquiv` and the induced quotient
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:117:theorem affine_domain_height_add_ringKrullDim_quotient_eq_fintype {σ : Type*} [Finite σ]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:133:  have hL := affine_domain_height_add_ringKrullDim_quotient_eq k (Fintype.card σ) J p'
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:136:    ringKrullDim_quotient_map_algEquiv Φ p, hJ, ringKrullDim_quotient_map_algEquiv e I] at hL
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:691:    rw [(cochain1Split d e e' (k := k)).finrank_eq, Module.finrank_prod]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:836:    rw [(cochain1SplitL d1 d2 e (k := k)).finrank_eq, Module.finrank_prod]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:164:theorem ringKrullDim_quotient_eq_under_of_monic {A : Type*} [CommRing A]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:232:theorem ringKrullDim_quotient_map_algEquiv {R S : Type*} [CommRing R] [CommRing S] {k : Type*}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:279:        (ringKrullDim_quotient_map_algEquiv Φ p).symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:285:        ringKrullDim_quotient_eq_under_of_monic P hgmon hgP
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:295:        have e1 := ringKrullDim_quotient_eq_coheight
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:297:        have e2 := ringKrullDim_quotient_eq_coheight
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:337:theorem height_add_ringKrullDim_quotient_eq
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:341:  rw [ringKrullDim_quotient_eq_coheight ⟨p, ‹_›⟩, Ideal.height_eq_primeHeight, Ideal.primeHeight]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:346:`primeHeight_add_ringKrullDim_quotient_le`: for a prime `p` of `R = k[x₁,…,xₙ]`,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:348:theorem primeHeight_add_ringKrullDim_quotient_eq
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:353:  exact height_add_ringKrullDim_quotient_eq k n p
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:362:  have := height_add_ringKrullDim_quotient_eq ℚ 2 ⊥
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:379:  have h := height_add_ringKrullDim_quotient_eq ℚ 2 p
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChart.lean:7:# `DLNFibre.Core.DeterminantalChart` — the pivot-chart Schur parametrization of `Mat^{rk=r}`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChart.lean:10:determinantal-presentation build). Over a field `k`, on the **pivot chart** where the top-left
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChart.lean:99:  rw [(Submodule.prodLequiv (LinearMap.range A.mulVecLin) (LinearMap.range D.mulVecLin)).finrank_eq,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChart.lean:106:theorem rank_eq_zero_iff [Fintype n] (A : Matrix m n k) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChart.lean:112:      (Submodule.finrank_eq_zero (R := k) (M := (m → k))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChart.lean:120:/-! ## The pivot-chart Schur iff (the headline) -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChart.lean:122:/-- **The pivot-chart Schur rank criterion.** Over a field, with the top-left block `Δ`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChart.lean:153:    rank_eq_zero_iff, hS, sub_eq_zero]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChart.lean:166:/-! ## The pivot chart and its explicit parametrization -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChart.lean:169:/-- The **pivot rank chart**: the exact-rank-`card m` block matrices whose top-left block `Δ` is
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChart.lean:172:def pivotRankChart [Fintype m] [Fintype n] [DecidableEq m] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChart.lean:176:/-- **The explicit chart parametrization (G2-1 headline).** On the pivot chart, an exact-rank-`r`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChart.lean:181:noncomputable def pivotRankChartEquiv
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChart.lean:183:    {M // M ∈ pivotRankChart k m l n} ≃
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChart.lean:208:The parametrization `pivotRankChartEquiv` identifies the chart with
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChart.lean:218:`Matrix m m k × Matrix m n k × Matrix l m k` of `pivotRankChartEquiv` is
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChart.lean:221:theorem finrank_pivotRankChart_params [Fintype m] [Fintype n] [Fintype l] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChart.lean:230:arithmetic; ties `finrank_pivotRankChart_params` to the thermometer value `δ` of
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChart.lean:245:pivot chart, and its Schur criterion holds: its `(2,2)` entry is the forced value. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineNoetherRank.lean:15:`ringKrullDim_quotient_eq_noetherRank` produces an integral injective `k[Fin s] →ₐ (R ⧸ p)` with
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineNoetherRank.lean:60:The Noether engine (`ringKrullDim_quotient_eq_noetherRank`) supplies the integral injective
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineNoetherRank.lean:62:theorem ringKrullDim_quotient_unbotD_eq_trdeg_toNat (n : ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineNoetherRank.lean:66:  obtain ⟨s, _, ⟨g, hg_inj, hg_int⟩, hdim⟩ := ringKrullDim_quotient_eq_noetherRank k n p
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineNoetherRank.lean:79:`k[Fin n]`; then `ringKrullDim_quotient_unbotD_eq_trdeg_toNat` applies, transported back through
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineNoetherRank.lean:105:    ringKrullDim_quotient_unbotD_eq_trdeg_toNat n p]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntegralDimension.lean:16:identity (`ringKrullDim_quotient_eq_coheight`).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntegralDimension.lean:52:theorem ringKrullDim_quotient_eq_coheight [CommRing R] (p : PrimeSpectrum R) :
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
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/DLN/RlctPayoff.lean:107:  · intro h; exact matrix_eq_zero_of_rank_eq_zero _ h
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:31:4. **Chain composition + assembly** (`box_move_chain_of_le` + `baseChange_normalForm`): `Ō_M ⊆
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:97:    rw [smul_eq_baseChange, baseChange_mul, ← smul_eq_baseChange, ← smul_eq_baseChange, ← hP₀,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:101:    rw [smul_eq_baseChange, baseChange_mul, ← smul_eq_baseChange, ← smul_eq_baseChange, hP₀]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:116:matrix-entry coordinates, so it lifts to an algebra endomorphism `baseChangePullback P` of the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:124:noncomputable def baseChangeSub {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:133:/-- The base-change pullback algebra endomorphism `aeval (baseChangeSub P)`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:134:noncomputable def baseChangePullback {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:136:  MvPolynomial.aeval (baseChangeSub P)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:138:/-- **Evaluation of the pullback is evaluation at the shifted point.** `eval x (baseChangeSub P
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:141:theorem eval_baseChangeSub {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:143:    MvPolynomial.eval x (baseChangeSub P coord)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:145:  rw [baseChangeSub, canonicalCoord_apply, smul_eq_baseChange, baseChange_apply]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:167:/-- The pullback evaluates as the shift: `eval x (baseChangePullback P f) = eval (shifted x) f`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:168:theorem eval_baseChangePullback {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:170:    MvPolynomial.eval x (baseChangePullback P f)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:172:  rw [baseChangePullback,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:173:    show MvPolynomial.eval x (MvPolynomial.aeval (baseChangeSub P) f)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:174:      = (MvPolynomial.eval x).comp ((MvPolynomial.aeval (baseChangeSub P)).toRingHom) f from rfl]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:175:  have hhom : (MvPolynomial.eval x).comp ((MvPolynomial.aeval (baseChangeSub P)).toRingHom)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:179:      show MvPolynomial.eval x (MvPolynomial.aeval (baseChangeSub P) (MvPolynomial.C r)) = _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:183:      show MvPolynomial.eval x (MvPolynomial.aeval (baseChangeSub P) (MvPolynomial.X coord)) = _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:184:      rw [MvPolynomial.aeval_X, MvPolynomial.eval_X, eval_baseChangeSub]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:189:theorem orbitSet_baseChange_stable {d : Fin (N + 1) → ℕ} (U : Tuple (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:194:  · rw [smul_eq_baseChange, baseChange_mul, ← smul_eq_baseChange, ← smul_eq_baseChange, hQ]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:199:theorem baseChangePullback_mem_vanishingIdeal_orbitSet {d : Fin (N + 1) → ℕ} (U : Tuple (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:202:    baseChangePullback P f
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:206:  rw [MvPolynomial.aeval_eq_eval, eval_baseChangePullback, ← MvPolynomial.aeval_eq_eval]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:207:  exact hf _ (orbitSet_baseChange_stable U P hy)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:225:    ← eval_baseChangePullback Q (canonicalCoord d D) f]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:228:  have := hmem (baseChangePullback Q f) (baseChangePullback_mem_vanishingIdeal_orbitSet U Q hf)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntervalModule.lean:146:theorem rank_eq_zero_of_isEmpty_cols [Nontrivial k] {m n : Type*} [Fintype n]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntervalModule.lean:158:theorem rank_eq_zero_of_isEmpty_rows [Nontrivial k] {m n : Type*} [Fintype n]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntervalModule.lean:189:      exact rank_eq_zero_of_isEmpty_cols _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntervalModule.lean:193:      exact rank_eq_zero_of_isEmpty_rows _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntervalModule.lean:267:  rw [(submoduleProdEquiv p q).finrank_eq, Module.finrank_prod]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntervalModule.lean:398:  exact rank_eq_zero_of_isEmpty_rows _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntervalModule.lean:452:def multiplicityArray (L : List (Fin (N + 1) × Fin (N + 1))) : ℤ → ℤ → ℤ :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:141:  exact (LinearEquiv.finrank_eq eCot.symm).trans
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:142:    (LinearEquiv.finrank_eq ((cotangentLocalizationTensorEquiv p).restrictScalars k))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:344:  -- Pin `Module A A` to `Semiring.toModule` so both `baseChange` steps use the same self-module.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:351:    (((KaehlerDifferential.mvPolynomialBasis k σ).baseChange
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:352:      (MvPolynomial σ k ⧸ Ideal.span (Set.range g))).baseChange k).equivFun
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:361:    simp only [Ψ, Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:404:    -- LHS range = `K.baseChange k` = `span k (range tgen)`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:407:      change K.baseChange k = _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:408:      rw [hKspanB, Submodule.baseChange_span, ← Set.range_comp]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:433:  exact (eExact.symm.trans eQuot).finrank_eq
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:449:    (kerCotangentToTensor_split_bijective hsurj_alg)).finrank_eq
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean:18:* **L5.5** `ringKrullDim_quotient_eq_noetherRank` — `dim (R ⧸ p)` equals the Noether-normalization
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean:34:(`primeHeight_add_ringKrullDim_quotient_le`). The catenary `≥` direction `height p ≥ n − dim(R/p)`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean:36:`Core.NoetherMonicPositioning` (`height_add_ringKrullDim_quotient_eq`), which imports this module
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean:55:theorem ringKrullDim_quotient_eq_noetherRank
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean:92:theorem primeHeight_add_ringKrullDim_quotient_le
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean:96:  rw [ringKrullDim_quotient_eq_coheight ⟨p, ‹_›⟩]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean:118:/-- Witness for `ringKrullDim_quotient_eq_noetherRank`: for the zero prime of `k[x]` the Noether
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean:124:  obtain ⟨s, _, _, hdim⟩ := ringKrullDim_quotient_eq_noetherRank k 1 ⊥
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:16:`height_add_ringKrullDim_quotient_eq` (L5, `Core.NoetherMonicPositioning`) to a finite-type domain
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:19:* `affine_domain_height_add_ringKrullDim_quotient_eq` :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:113:theorem affine_domain_height_add_ringKrullDim_quotient_eq
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:150:    height_add_ringKrullDim_quotient_eq k s q
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:165:  have h := affine_domain_height_add_ringKrullDim_quotient_eq k n I m
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:197:  affine_domain_height_add_ringKrullDim_quotient_eq ℚ 1 ⊥ ⊥
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitVariety.lean:4:import Mathlib.RingTheory.Localization.Away.Basic
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitVariety.lean:20:pivot chart L3.0, L6, and the codimension bridge L0 stand on.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitVariety.lean:95:/-- The coordinate ring `𝒪(G_d) := Localization.Away Δ` of `G_d`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitVariety.lean:97:  Localization.Away (groupDenom (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitVariety.lean:129:  groupAlgMap (k := k) d (detCompl d v) * IsLocalization.Away.invSelf (groupDenom (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitVariety.lean:137:    IsLocalization.Away.mul_invSelf]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitVariety.lean:198:  IsLocalization.Away.lift (groupDenom (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitVariety.lean:205:  IsLocalization.Away.lift_eq _ _ _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitVariety.lean:272:    rw [genericOrbitCoord, orbitMap, canonicalCoord_apply, smul_eq_baseChange, baseChange_apply]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitVariety.lean:295:theorem exists_baseChange_of_eval_ne_zero {d : Fin (N + 1) → ℕ} {x : GroupCoord d → k}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitVariety.lean:335:    obtain ⟨n, h, hsurj⟩ := IsLocalization.Away.surj (groupDenom (k := k) d) (orbitPullback M g)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitVariety.lean:341:      · obtain ⟨P, rfl⟩ := exists_baseChange_of_eval_ne_zero hΔx
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitVariety.lean:354:        (IsLocalization.Away.mul_invSelf (groupDenom (k := k) d)))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitVariety.lean:370:kernel into the domain `𝒪(G_d) = Localization.Away Δ` (`groupRing_isDomain`), hence prime
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VoigtDischarge.lean:38:theorem varietyDim_orbitRankLocus_eq_finrank_range_deformationδ
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:19:Schur minor identity**, valid over any commutative ring (no invertibility of the pivot block):
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:55:/-- `BorderedId` holds over a field when the pivot is nonsingular (`det Δ ≠ 0`), via the Mathlib
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:123:fraction field has the (nonzero) generic pivot `det Δ` invertible, where `det_fromBlocks₁₁` applies;
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:141:    -- over the field K, the mapped pivot `Δ'` is nonsingular
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:185:`M : Mat_{p×q}` over a field with `rank M ≤ r`, any choice of pivot rows `pr`, pivot columns `pc`,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:189:`rank M ≤ r`. This is the polynomial that, on the pivot chart (`det M[pr,pc]` inverted), forces the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:274:/-- The pivot minor polynomial: the determinant of the top-left `r×r` submatrix of the generic
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:275:single matrix `multPoly (dStratum q p)`. Inverting it is the pivot chart; `Localization.Away` of it
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:321:theorem mult_chartWitness_pivot_submatrix (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:338:    mult_chartWitness_pivot_submatrix q p r hp hq, det_one]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:341:/-- `detΔ ∉ sigmaIdeal ![q,p] r`: the pivot minor does not vanish on all of the base — it is `1`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:357:prime determinantal-base ideal `sigmaIdeal ![q,p] r` at the pivot minor `detΔ` (which is not in it)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:364:          (Localization.Away (detPivotPoly (k := k) q p r hp hq)))).height
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:383:          (Localization.Away (detPivotPoly (k := k) q p r hp hq)))).height
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:10:`Aᵢ ↦ P_{i+1} · Aᵢ · P_i⁻¹` of `Core.BaseChange.baseChange` on the generic tuple. For the endpoint
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:21:   `⟨i, (r, c)⟩` entry of `baseChange (P.map C) (genericTuple d)`, i.e. the entries of
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:25:   by the group-action laws `baseChange_mul` / `baseChange_one` on the generic tuple.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:28:   transforms by the two end-vertex gauges (interior units telescope away, `mult_smul`). For the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:32:The `N = 1` coincidence (first factor = last factor) is automatic: `baseChange` is defined uniformly
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:38:avoid `baseChangePullback`, which carries `[Infinite k]` from polynomial-function ext).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:80:`baseChange (liftGauge d P) (genericTuple d) i = P_{i+1} · Xᵢ · P_i⁻¹` (units lifted by `C`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:83:  fun x ↦ baseChange (liftGauge d P) (genericTuple d) x.1 x.2.1 x.2.2
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:86:`baseChange (liftGauge d P) (genericTuple d) i`. The generator goes to the corresponding entry by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:91:      = baseChange (liftGauge d P) (genericTuple d) i := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:113:`(Matrix.of (multPoly d)).map (aeval (gaugeSub P)) = mult d (baseChange (liftGauge d P)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:117:      = mult d (baseChange (liftGauge d P) (genericTuple d)) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:122:      = baseChange (liftGauge d P) (genericTuple d) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:130:interior units of the base change telescope away (`submult_baseChange` at the full interval,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:131:through `mult_eq_submult`). The `Core.FibreNormalForm.mult_smul` proof is over a `Field`; this is
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:133:theorem mult_smul_commRing (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:135:    mult d (baseChange P A)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:137:  rw [mult_eq_submult, mult_eq_submult, submult_baseChange]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:141:by `C`); the interior units telescope away (`mult_smul`). For the endpoint normalization
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:152:    mult_smul_commRing d (liftGauge d P) (genericTuple d)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:191:generic factor `baseChange (liftGauge Q) (genericTuple) i` re-gauges by `P` inside: the result is
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:192:`baseChange (liftGauge Q) (baseChange (liftGauge P) (genericTuple)) i`. The constant `C`-lifted
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:195:theorem map_aeval_gaugeSub_baseChange (d : Fin (N + 1) → ℕ) (P Q : BaseChangeGroup (k := R) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:197:    (baseChange (liftGauge d Q) (genericTuple d) i).map (aeval (R := R) (gaugeSub d P))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:198:      = baseChange (liftGauge d Q) (baseChange (liftGauge d P) (genericTuple d)) i := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:199:  rw [baseChange_apply, baseChange_apply, Matrix.map_mul, Matrix.map_mul,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:205:`P`, `Q`, `aeval (gaugeSub P) (gaugeSub Q x)` is the `x`-entry of `baseChange (liftGauge (Q * P))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:210:      = baseChange (liftGauge d (Q * P)) (genericTuple d) x.1 x.2.1 x.2.2 := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:212:      = ((baseChange (liftGauge d Q) (genericTuple d) x.1).map
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:214:  rw [h, map_aeval_gaugeSub_baseChange d P Q x.1, ← baseChange_mul, liftGauge_mul]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:217:`aeval (gaugeSub P⁻¹)`. The round-trips collapse by the group-action laws (`baseChange_mul` /
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:218:`baseChange_one`) on the generic tuple. The endpoint normalization instantiates `P`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:226:        liftGauge_one, baseChange_one, genericTuple_apply])
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:231:        liftGauge_one, baseChange_one, genericTuple_apply])
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:261:  rw [gaugeSub, liftGauge_one, baseChange_one, genericTuple_apply]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:22:`I = orbitIdeal M = vanishingIdeal(orbitSet M)` directly — no determinantal minors, no radical. The
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:79:    height_map_algEquiv Φ m, hJ, ringKrullDim_quotient_map_algEquiv e I] at hL4d
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:99:theorem finrank_eq_finrank_of_residueField_equiv {κ : Type*} [Field κ] [Algebra k κ]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:104:    rw [LinearEquiv.finrank_eq e.toLinearEquiv, finrank_self]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:542:has `finrank ≤ finrank (m_M.Cotangent)` (`Subspace.dual_finrank_eq`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:561:      _ = finrank k ((normalFormIdeal M).Cotangent) := Subspace.dual_finrank_eq
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:577:    refine le_trans (ringKrullDim_quotient_le (orbitIdeal M)) ?_
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:603:theorem finrank_cotangent_eq_varietyDim [IsAlgClosed k] (M : Tuple (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:628:    finrank_eq_finrank_of_residueField_equiv (residueFieldAtPrimeNormalFormEquiv M)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:641:theorem finrank_range_deformationδ_le_varietyDim [IsAlgClosed k] (M : Tuple (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:7:# `DLNFibre.Core.RadicalCatenary` — the catenary identity for a reducible (radical) locus
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:10:`height_add_ringKrullDim_quotient_eq_card`) extended to an **arbitrary proper** ideal `I ≠ ⊤` of a
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:18:`le_antisymm` (no component-decomposition lemma, no radicality needed):
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:28:Zariski-closed `Z` (over an algebraically closed field its vanishing ideal is radical and proper),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:79:theorem exists_minimalPrime_ringKrullDim_quotient_ge {R : Type*} [CommRing R] [IsNoetherianRing R]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:85:    refine ⟨?_, ne_top_of_le_ne_top (ringKrullDim_ne_top (R := R)) (ringKrullDim_quotient_le I)⟩
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:108:  rw [hLlen, ringKrullDim_quotient_eq_coheight (⟨p, ‹_›⟩ : PrimeSpectrum R)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:112:/-! ## The radical-locus catenary -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:117:Direct chain/coheight squeeze; no radicality needed. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:118:theorem height_add_ringKrullDim_quotient_eq_card_of_ne_top [Finite σ]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:126:    height_add_ringKrullDim_quotient_eq_card (k := k) (σ := σ) p
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:136:    obtain ⟨p, hpmem, hpdim⟩ := exists_minimalPrime_ringKrullDim_quotient_ge I hIne
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:175:(its vanishing ideal is radical and proper), the geometric codimension plus the variety dimension
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:179:theorem codimRepCanonical_add_varietyDim_eq_card_of_nonempty {d : Fin (N + 1) → ℕ}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:186:  have key := height_add_ringKrullDim_quotient_eq_card_of_ne_top
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultDifferential.lean:52:def multSuffix (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveDegeneration.lean:183:  rw [smul_eq_baseChange, baseChange_apply]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitCodim.lean:58:dimension theorems (catenary `dim R/I = n − ht I`, determinantal height, Nullstellensatz radical
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitPullbackDim.lean:52:theorem varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker [Infinite k]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitPullbackDim.lean:70:transcendence degree. Combines `varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker` with the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitPullbackDim.lean:74:theorem varietyDim_eq_ringKrullDim_range_orbitPullback [Infinite k] {d : Fin (N + 1) → ℕ}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitPullbackDim.lean:78:  rw [varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker M,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:21:`Core.NullstellensatzCodim` (the field catenary `height_add_ringKrullDim_quotient_eq_card`).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:38:theorem ringKrullDim_quotient_graphIdeal_eq (c : σ → MvPolynomial τ k) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:68:    rw [hmap]; exact ringKrullDim_quotient_map_algEquiv e.symm (graphIdeal c)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:70:  have hcat := height_add_ringKrullDim_quotient_eq_card (k := k) (σ := σ ⊕ τ) J₀
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:71:  rw [hheight, hdim, ringKrullDim_quotient_graphIdeal_eq c, Nat.card_sum] at hcat
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:101:in `MvPolynomial τ k` and `Sd = Localization.Away f`, the `σ`-block coordinate ideal of
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:108:    (Sd : Type u) [CommRing Sd] [Algebra (MvPolynomial τ k) Sd] [IsLocalization.Away f Sd] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:142:Sd` with `Sd = Localization.Away f` (`f ≠ 0` in `MvPolynomial τ k`), `(graphIdeal c).height =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:146:`height J = C` step uses (`σ = B22block`, `Sd = Localization.Away detSchurS`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:148:    (Sd : Type u) [CommRing Sd] [Algebra (MvPolynomial τ k) Sd] [IsLocalization.Away f Sd]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:35:`baseChangePullback P` (from `OrbitClosure`) is `aeval (baseChangeSub P)`, the coordinate-ring
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:40:/-- The pullback composition law (contravariant): `baseChangePullback P (baseChangePullback Q f)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:41:= baseChangePullback (Q * P) f`. Both polynomials evaluate to the same value at every point `x`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:42:(`eval_baseChangePullback`, chasing the `G_d`-shift `shift_Q ∘ shift_P = shift_{Q*P}`), so they are
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:44:theorem baseChangePullback_comp [Infinite k] {d : Fin (N + 1) → ℕ}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:46:    baseChangePullback P (baseChangePullback Q f) = baseChangePullback (Q * P) f := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:48:  rw [eval_baseChangePullback, eval_baseChangePullback, eval_baseChangePullback]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:52:/-- The identity base change pulls back to the identity: `baseChangePullback 1 = id`. The shift by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:54:theorem baseChangePullback_one [Infinite k] {d : Fin (N + 1) → ℕ}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:56:    baseChangePullback (1 : BaseChangeGroup (k := k) d) f = f := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:58:  rw [eval_baseChangePullback, one_smul, Equiv.apply_symm_apply]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:60:/-- **L3.0 — the `G_d`-action as a `k`-algebra automorphism.** `baseChangeAlgEquiv P` is the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:61:coordinate-ring automorphism `aeval (baseChangeSub P)` (= the change of variables `A ↦ P • A`), with
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:64:noncomputable def baseChangeAlgEquiv [Infinite k] {d : Fin (N + 1) → ℕ}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:67:  AlgEquiv.ofAlgHom (baseChangePullback P) (baseChangePullback P⁻¹)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:69:        rw [AlgHom.comp_apply, AlgHom.id_apply, baseChangePullback_comp, inv_mul_cancel,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:70:          baseChangePullback_one])
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:72:        rw [AlgHom.comp_apply, AlgHom.id_apply, baseChangePullback_comp, mul_inv_cancel,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:73:          baseChangePullback_one])
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:75:@[simp] theorem baseChangeAlgEquiv_apply [Infinite k] {d : Fin (N + 1) → ℕ}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:77:    baseChangeAlgEquiv P f = baseChangePullback P f := rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:84:domain. The `G_d`-automorphism `baseChangeAlgEquiv P` stabilises `I`, descending to `A ≃ₐ[k] A`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:102:/-- The orbit ideal is `G_d`-stable: `baseChangeAlgEquiv P` maps `I` into `I`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:103:(`baseChangePullback_mem_vanishingIdeal_orbitSet`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:106:    (orbitIdeal M).map (baseChangeAlgEquiv P : MvPolynomial (RepCoord d) k →+* _)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:111:  exact baseChangePullback_mem_vanishingIdeal_orbitSet M P hf
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:113:/-- The orbit ideal is **invariant** under `baseChangeAlgEquiv P`: `I.map (α_P) = I`. Both `α_P` and
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:117:    (orbitIdeal M).map (baseChangeAlgEquiv P : MvPolynomial (RepCoord d) k →+* _)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:122:      (baseChangeAlgEquiv P⁻¹ : MvPolynomial (RepCoord d) k →+* _) ≤ orbitIdeal M :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:126:          (baseChangeAlgEquiv P⁻¹ : MvPolynomial (RepCoord d) k →+* _)).map
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:127:          (baseChangeAlgEquiv P : MvPolynomial (RepCoord d) k →+* _) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:133:        change f = baseChangePullback P (baseChangePullback P⁻¹ f)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:134:        rw [baseChangePullback_comp, inv_mul_cancel, baseChangePullback_one]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:135:    _ ≤ (orbitIdeal M).map (baseChangeAlgEquiv P : MvPolynomial (RepCoord d) k →+* _) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:139:from the polynomial-ring automorphism `baseChangeAlgEquiv P` (which stabilises `I`,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:144:  Ideal.quotientEquivAlg (orbitIdeal M) (orbitIdeal M) (baseChangeAlgEquiv P)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:152:      = Ideal.Quotient.mk (orbitIdeal M) (baseChangePullback P f) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:228:    show MvPolynomial.eval (canonicalCoord d M) (baseChangePullback P f)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:230:        f from eval_baseChangePullback P (canonicalCoord d M) f,
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
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:17:(`height_add_ringKrullDim_quotient_eq`, "L5"). Here we:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:20:   Nullstellensatz over `[IsAlgClosed k]`): `vanishingIdeal Z` is always **radical**
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:21:   (`vanishingIdeal_isRadical`); `Z` irreducible ⟺ `vanishingIdeal Z` is **prime**
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:28:   transport lemmas (`height_map_algEquiv`, `ringKrullDim_quotient_map_algEquiv`):
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:29:   `height_add_ringKrullDim_quotient_eq_card`, `ringKrullDim (MvPolynomial σ k) = Nat.card σ`.
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
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:113:Transported from the `Fin (card σ)` headline `height_add_ringKrullDim_quotient_eq` (L5) through the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:115:theorem height_add_ringKrullDim_quotient_eq_card [Finite σ] (p : Ideal (MvPolynomial σ k))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:127:    ringKrullDim_quotient_map_algEquiv e p
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:128:  have key := height_add_ringKrullDim_quotient_eq k (Fintype.card σ) q
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:139:noncomputable def varietyDim (Z : Set (σ → k)) : ℕ∞ :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:147:theorem height_vanishingIdeal_add_varietyDim_eq_card [Finite σ] {Z : Set (σ → k)}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:150:  have key := height_add_ringKrullDim_quotient_eq_card (vanishingIdeal k Z)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:165:theorem height_vanishingIdeal_eq_card_sub_varietyDim [Finite σ] {Z : Set (σ → k)}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:183:theorem codimRep_add_varietyDim_eq_card [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:192:theorem codimRep_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:201:theorem codimRepCanonical_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ThetaComponentCount.lean:328:  is the Gabriel normal form (`exists_orbitRankLocus_mem_rankPattern_eq` / `baseChange_normalForm`)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaStratification.lean:42:**Typeclass.** `Field k` (the Gabriel normal-form existence `baseChange_normalForm` needs it; the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaStratification.lean:86:of a normal form `M` (a reindexed interval direct sum `⊕ M_{ab}`, `baseChange_normalForm`) with the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaStratification.lean:93:  obtain ⟨L, h, P, hP, _, _⟩ := baseChange_normalForm A
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaStratification.lean:146:`N = 2`, dimension vector `(2, 2, 2)`, over `ℚ` (a field — `baseChange_normalForm` needs `Field`).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:117:    (Module.finrank_baseChange).trans hΩ
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:127:    [Nontrivial (Localization.Away f)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:128:    [IsStandardSmoothOfRelativeDimension n k (Localization.Away f)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:129:    (hrank : Module.rank (Localization.Away f) (Ω[Localization.Away f⁄k]) = (n : Cardinal)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:132:  haveI : Algebra.FinitePresentation A (Localization.Away f) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:133:    IsLocalization.Away.finitePresentation f
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:134:  haveI : Algebra.FiniteType k (Localization.Away f) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:135:    Algebra.FiniteType.trans (R := k) (S := A) (A := Localization.Away f) inferInstance
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:137:  haveI : IsStandardSmooth k (Localization.Away f) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:139:  haveI : Module.Free (Localization.Away f) (Ω[Localization.Away f⁄k]) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:143:  letI : Algebra (Localization.Away f) (Localization.AtPrime m) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:144:    IsLocalization.localizationAlgebraOfSubmonoidLe (Localization.Away f) (Localization.AtPrime m)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:146:  haveI : IsScalarTower A (Localization.Away f) (Localization.AtPrime m) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:149:  haveI : IsLocalization (m.primeCompl.map (algebraMap A (Localization.Away f)))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:151:    IsLocalization.isLocalization_of_submonoid_le (Localization.Away f) (Localization.AtPrime m)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:153:  haveI : IsScalarTower k (Localization.Away f) (Localization.AtPrime m) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:155:    rw [IsScalarTower.algebraMap_eq k A (Localization.Away f),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:157:      ← IsScalarTower.algebraMap_eq A (Localization.Away f) (Localization.AtPrime m)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:159:    (m.primeCompl.map (algebraMap A (Localization.Away f)))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:160:    (KaehlerDifferential.map k k (Localization.Away f) (Localization.AtPrime m))]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:177:  haveI : IsStandardSmoothOfRelativeDimension n k (Localization.Away f) := hss
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:179:  haveI : (m.map (algebraMap A (Localization.Away f))).IsMaximal :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:180:    IsLocalization.isMaximal_of_isMaximal_disjoint (S := Localization.Away f) f m hm hf
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:181:  haveI : Nontrivial (Localization.Away f) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:182:    nontrivial_of_ne (0 : Localization.Away f) 1 fun h ↦
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:183:      (‹(m.map (algebraMap A (Localization.Away f))).IsMaximal›).ne_top
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:184:        (Ideal.eq_top_of_isUnit_mem _ (h ▸ (m.map (algebraMap A (Localization.Away f))).zero_mem)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:8:# `DLNFibre.Core.VarietyDimRadical` — `varietyDim`/`ringKrullDim` is radical-insensitive
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:12:inclusion `sigmaIdeal ≤ ker`, available only as `≤ radical`. The **dimension** identity `hSweep`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:15:radical (both quotients have the same prime spectrum). So the route-(c) dimension build works
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:16:through `vanishingIdeal` (radical by construction) and never needs `fibreGenIdeal` to be radical.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:19:- `ringKrullDim_quotient_radical` — `ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ I.radical)`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:20:- `ringKrullDim_quotient_eq_of_radical_eq` — same Krull dim for two ideals with equal radical.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:28:only through its radical: `Spec (R ⧸ I) = zeroLocus I = zeroLocus I.radical = Spec (R ⧸ I.radical)`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:30:theorem ringKrullDim_quotient_radical {R : Type*} [CommRing R] (I : Ideal R) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:31:    ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ I.radical) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:32:  rw [ringKrullDim_quotient, ringKrullDim_quotient, PrimeSpectrum.zeroLocus_radical]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:34:/-- Two ideals with the same radical give the same quotient Krull dimension — the form the route-(c)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:36:presentation may hand it the generator ideal `fibreGenIdeal`, equal only up to radical). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:37:theorem ringKrullDim_quotient_eq_of_radical_eq {R : Type*} [CommRing R] {I J : Ideal R}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:38:    (h : I.radical = J.radical) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:40:  rw [ringKrullDim_quotient_radical I, ringKrullDim_quotient_radical J, h]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:44:/-- Non-vacuity witness: in `ℚ[X]`, the square `(X)^2` of the prime `(X)` shares its radical, so the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:50:  apply DLNFibre.Core.ringKrullDim_quotient_eq_of_radical_eq
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:51:  exact Ideal.radical_pow (I := (Ideal.span {Polynomial.X} : Ideal (Polynomial ℚ))) (by norm_num)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitKostant.lean:34:  (`Orbit.baseChange_normalForm`).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibrationProbe.lean:5:import DLNFibre.Core.DeepChartRing
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibrationProbe.lean:67:  affine_domain_height_add_ringKrullDim_quotient_eq k n I p
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitImageDim.lean:43:(`Localization.Away (groupDenom d)`) of the finite-type `MvPolynomial (GroupCoord d) k`, composed
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitImageDim.lean:95:theorem varietyDim_orbitRankLocus_le_finrank_range_deformationδ
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:11:(`Core.BaseChange.baseChange`) specialised to the **two end vertices** `0` and `N` acts on `Rep_d`,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:15:1. **mult-equivariance** (`mult_smul`): `mult d (P • A) = P_N · (mult d A) · P_0⁻¹` — the inner
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:16:   units telescope away (`Core.BaseChange.submult_smul` at the full interval `(0, last)`, through
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:19:2. **codim-invariance** (`codimRep_baseChange_image`): a base change is a *linear* change of the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:20:   matrix-entry coordinates, so it induces the `k`-algebra automorphism `baseChangeAlgEquiv P` of
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:26:(`codimRepCanonical_fibre_baseChange`). With the rank-normal-form fact that any two matrices of the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:27:same rank are `GL × GL`-equivalent (`exists_baseChange_of_rank_eq`), this gives the headline
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:28:`codimRepCanonical_fibre_eq_of_rank_eq`: same rank ⟹ same fibre codimension.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:30:**Typeclass.** `[Field k] [Infinite k]` — `Infinite` carries `baseChangeAlgEquiv` (the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:57:  submult_smul P A 0 (Fin.last N) (Fin.zero_le _)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:63:/-- `eval_baseChangePullback`: pullback evaluates as the `G_d`-shift. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:66:    MvPolynomial.eval x (baseChangePullback P f)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:68:  eval_baseChangePullback P x f
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:75:change telescope away, leaving only the two end-vertex units (`submult_smul` at the full interval
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:77:theorem mult_smul (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:80:  rw [mult_eq_submult, mult_eq_submult, submult_smul]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:94:    rw [mem_fibre, mult_smul]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:100:    rw [mem_fibre, mult_smul, hA]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:108:`(P • ·) '' Z` is the `comap` of the vanishing ideal of `Z` along `baseChangePullback P`: a
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:110:(`eval_baseChangePullback`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:115:          (baseChangePullback P : MvPolynomial (RepCoord d) k →+* _) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:122:    show MvPolynomial.eval (canonicalCoord d A) (baseChangePullback P f) = 0
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:123:    rw [eval_baseChangePullback, Equiv.symm_apply_apply, ← MvPolynomial.aeval_eq_eval]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:133:      ← eval_baseChangePullback P (canonicalCoord d A) f]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:139:ideal as a `comap` along `baseChangeAlgEquiv P` (a ring equiv), and `RingEquiv.height_comap`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:141:theorem codimRep_baseChange_image [Infinite k] (d : Fin (N + 1) → ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:145:  have he : (baseChangePullback P : MvPolynomial (RepCoord d) k →+* _)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:146:      = ((baseChangeAlgEquiv P).toRingEquiv.toRingHom) := rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:148:  exact RingEquiv.height_comap (baseChangeAlgEquiv P).toRingEquiv _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:151:and `codimRep_baseChange_image`: `codimRepCanonical (fibre d (P_N · B · P_0⁻¹)) = codimRepCanonical
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:153:theorem codimRepCanonical_fibre_baseChange [Infinite k] (d : Fin (N + 1) → ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:157:  rw [codimRepCanonical, codimRepCanonical, ← image_smul_fibre, codimRep_baseChange_image]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:279:theorem exists_baseChange_of_rank_eq (d : Fin (N + 1) → ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:322:theorem codimRepCanonical_fibre_eq_of_rank_eq [Infinite k] (d : Fin (N + 1) → ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:326:  obtain ⟨P, hP⟩ := exists_baseChange_of_rank_eq d hN B B' h
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:327:  rw [hP, codimRepCanonical_fibre_baseChange]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:350:  exact codimRepCanonical_fibre_eq_of_rank_eq dWitness hN _ _ hrank
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:4:import Mathlib.RingTheory.Localization.Away.Basic
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:9:The final identification of `G2-2`: the localized determinantal base ring `A_loc = Localization.Away
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:10:detΔ`, modulo its base ideal `Iad`, is the free Schur localization `Sd` (`= Localization.Away
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:46:`Sd := Localization.Away detSchurS`, `Q := MvPolynomial B22block Sd`. We use `Localization` (the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:49:/-- The free Schur localization `Sd = Localization.Away detSchurS` — the downstream-composable base
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:52:  Localization.Away (detSchurS (k := k) q p r)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:57:    Localization.Away (detPivotPoly (k := k) q p r hp hq)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:86:    (Localization.Away (detPivotPoly (k := k) q p r hp hq))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:93:`[pivots, r+a']`, columns `[pivots, r+b']`) lies in the base ideal (an `(r+1)`-minor), and under
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:99:variables of `multPoly`). Pivot block `Δ`, pivot-row × non-pivot-col `u`, non-pivot-row × pivot-col
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:100:`v`, corner `d`. The non-pivot index is the landed reindex form `Fin.cast (natAdd r ·)`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:122:/-- The `SchurVar`-side pivot block `ΔS` (whose determinant is `detSchurS`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:126:/-- The `SchurVar`-side `B12` column `uS` at non-pivot column `b'` (the `b'`-th column of `B12`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:131:/-- The `SchurVar`-side `B21` row `vS` at non-pivot row `a'` (the `a'`-th row of `B21`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:136:/-- The bordered minor `m_b`: the determinant of the `multPoly` submatrix on rows `[pivots, r+a']`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:137:and columns `[pivots, r+b']`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:179:  exact blockAlgEquiv_X_pivot q p r hp hq i j
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:245:          (Localization.Away (detPivotPoly (k := k) q p r hp hq)) x)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:270:base ideal pushed into the localized base ring `A_loc = Localization.Away detΔ`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:272:    Ideal (Localization.Away (detPivotPoly (k := k) q p r hp hq)) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:275:      (Localization.Away (detPivotPoly (k := k) q p r hp hq)))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:289:            (Localization.Away (detPivotPoly (k := k) q p r hp hq))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:315:    (IsLocalization.Away.algebraMap_isUnit (detSchurS (k := k) q p r)).map
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:347:      (S := Localization.Away (detPivotPoly (k := k) q p r hp hq))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:374:base ring `A_loc = Localization.Away detΔ`, modulo its base ideal `Iad = (sigmaIdeal …).map …`, is
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:375:the free Schur localization `Sd = Localization.Away detSchurS` — a regular ring of dimension `δ`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:380:    (Localization.Away (detPivotPoly (k := k) q p r hp hq) ⧸ (Iad (k := k) q p r hp hq))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:382:  have e₁ : (Localization.Away (detPivotPoly (k := k) q p r hp hq) ⧸ (Iad (k := k) q p r hp hq))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:412:    (Localization.Away (detPivotPoly (k := k) 2 2 1 h h) ⧸ Iad (k := k) 2 2 1 h h)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:94:    rw [A.rank_eq_finrank_span_row, ← h1]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:115:  rw [smul_eq_baseChange, baseChange_apply, smul_eq_baseChange, dirSum, dirSum, baseChange_apply]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:171:  rw [smul_eq_baseChange, baseChange_apply, tupleEval, smulPoly,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:315:  rw [smul_eq_baseChange, baseChange_apply, splitBaseChange_val, splitBaseChange_inv_val]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:710:theorem matrix_eq_zero_of_rank_eq_zero {m n : Type*} [Fintype m] [Fintype n]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:712:  rw [Matrix.rank_eq_finrank_span_cols] at h
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:714:    rw [Submodule.finrank_eq_zero] at h; exact h
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:721:`matrix_eq_zero_of_rank_eq_zero`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:725:  · exact absurd (matrix_eq_zero_of_rank_eq_zero A hr) h
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:16:  (L5 `height_add_ringKrullDim_quotient_eq`);
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:52:  exact (Module.finrank_eq_rank S (Ω[S⁄k])).symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:66:theorem ringKrullDim_quotient_comap_etale_eq_zero {n : ℕ} {S : Type*} [CommRing S] [Algebra k S]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:101:  have hL5 := height_add_ringKrullDim_quotient_eq k n (q.comap g)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:102:  rw [ringKrullDim_quotient_comap_etale_eq_zero g hg q, add_zero] at hL5
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:116:      IsStandardSmoothOfRelativeDimension n k (Localization.Away f) ∧
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:117:      Module.rank (Localization.Away f) (Ω[Localization.Away f⁄k]) = (n : Cardinal) ∧
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:126:  set S := Localization.Away f with hS
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:194:      IsStandardSmoothOfRelativeDimension n ℚ (Localization.Away f) ∧
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:195:      Module.rank (Localization.Away f) (Ω[Localization.Away f⁄ℚ]) = (n : Cardinal) ∧
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Setup.lean:37:def multPrefix (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Setup.lean:51:def mult (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) :

codex
The key repo fact so far: `varietyDim` is still the set-level ambient-polynomial definition in `NullstellensatzCodim`, and `VarietyDimRadical` has only radical-insensitivity, not a general “regular isomorphism preserves dimension” layer. That makes the transport choice the main Lean cost, not the existence of the section.
exec
/bin/bash -lc "sed -n '120,230p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean && sed -n '1,80p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
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
Z` plus the variety dimension of `coord '' Z` equals the ambient dimension `Nat.card (RepCoord d)`.
`height_vanishingIdeal_add_varietyDim_eq_card` at `σ := RepCoord d`, `Z := coord '' Z`. -/
theorem codimRep_add_varietyDim_eq_card [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
    (coord : Tuple (k := k) d ≃ (RepCoord d → k)) (Z : Set (Tuple (k := k) d))
    (hp : (vanishingIdeal k (coord '' Z) : Ideal (MvPolynomial (RepCoord d) k)).IsPrime) :
    codimRep coord Z + varietyDim (coord '' Z) = (Nat.card (RepCoord d) : ℕ∞) :=
  height_vanishingIdeal_add_varietyDim_eq_card hp

/-- **The bridge at `codimRep` (subtraction).** `codimRep coord Z = Nat.card (RepCoord d) −
varietyDim (coord '' Z)` for an irreducible variety `coord '' Z`: geometric codimension `=` ambient
`−` variety dimension. -/
theorem codimRep_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
    (coord : Tuple (k := k) d ≃ (RepCoord d → k)) (Z : Set (Tuple (k := k) d))
    (hp : (vanishingIdeal k (coord '' Z) : Ideal (MvPolynomial (RepCoord d) k)).IsPrime) :
    codimRep coord Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (coord '' Z) :=
  height_vanishingIdeal_eq_card_sub_varietyDim hp

/-- **The bridge at `codimRepCanonical` (subtraction).** At the canonical entry-flattening
`canonicalCoord d`, `codimRepCanonical Z = Nat.card (RepCoord d) − varietyDim (canonicalCoord d ''
Z)` for an irreducible variety — the genuine geometric codimension. -/
theorem codimRepCanonical_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
    (Z : Set (Tuple (k := k) d))
    (hp : (vanishingIdeal k (canonicalCoord d '' Z) :
      Ideal (MvPolynomial (RepCoord d) k)).IsPrime) :
    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
  codimRep_eq_card_sub_varietyDim (canonicalCoord d) Z hp

/-! ## Non-vacuity witness -/

/-- The vanishing ideal of the **whole space** `⊤ ⊆ (σ → k)` is `⊥` over any algebraically closed
(hence infinite) field: a polynomial vanishing at every point of `σ → k` is `0`
(`MvPolynomial.funext` over an infinite integral domain). -/
theorem vanishingIdeal_univ_eq_bot [IsAlgClosed k] :
    (vanishingIdeal k (Set.univ : Set (σ → k)) : Ideal (MvPolynomial σ k)) = ⊥ := by
  rw [eq_bot_iff]
  intro p hp
  rw [Ideal.mem_bot]
  refine MvPolynomial.funext (R := k) fun x ↦ ?_
  have hx := hp x (Set.mem_univ x)
  rw [MvPolynomial.mem_vanishingIdeal_iff] at hp
  rw [map_zero, ← MvPolynomial.aeval_eq_eval]
  exact hp x (Set.mem_univ x)

/-- Non-vacuity witness for the bridge: at the **whole space** `Z = univ` of `σ → k` (`k`
alg-closed, `σ` finite), the vanishing ideal is `⊥` (prime), `varietyDim = Nat.card σ`, the bridge
reads `0 + Nat.card σ = Nat.card σ` — a concrete satisfiable instance, the dimension term carrying
the equality. -/
example [IsAlgClosed k] [Finite σ] :
    (vanishingIdeal k (Set.univ : Set (σ → k)) : Ideal (MvPolynomial σ k)).height
      + varietyDim (Set.univ : Set (σ → k)) = (Nat.card σ : ℕ∞) := by
/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.NullstellensatzCodim
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# `DLNFibre.Core.VarietyDimRadical` — `varietyDim`/`ringKrullDim` is radical-insensitive

The formal linchpin of the route-(c) non-circularity de-risk (thread 31). The earlier scheme-level
product-iso route (R2-3b-4) was circular *for reducedness*: the forward map needed the strict ideal
inclusion `sigmaIdeal ≤ ker`, available only as `≤ radical`. The **dimension** identity `hSweep`
(`varietyDim Σ^r = δ + varietyDim F`) never touches that question, because `varietyDim` reads only
the **reduced / closed-set** structure: `ringKrullDim (R ⧸ I)` depends on `I` only through its
radical (both quotients have the same prime spectrum). So the route-(c) dimension build works
through `vanishingIdeal` (radical by construction) and never needs `fibreGenIdeal` to be radical.

## Main results
- `ringKrullDim_quotient_radical` — `ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ I.radical)`.
- `ringKrullDim_quotient_eq_of_radical_eq` — same Krull dim for two ideals with equal radical.
-/

namespace DLNFibre.Core

open PrimeSpectrum

/-- **Radical-insensitivity of the quotient Krull dimension.** `ringKrullDim (R ⧸ I)` depends on `I`
only through its radical: `Spec (R ⧸ I) = zeroLocus I = zeroLocus I.radical = Spec (R ⧸ I.radical)`
as ordered sets, and Krull dimension is a spectrum invariant. -/
theorem ringKrullDim_quotient_radical {R : Type*} [CommRing R] (I : Ideal R) :
    ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ I.radical) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient, PrimeSpectrum.zeroLocus_radical]

/-- Two ideals with the same radical give the same quotient Krull dimension — the form the route-(c)
fibre-dimension build consumes (it reads `varietyDim` off `vanishingIdeal`, while a chart
presentation may hand it the generator ideal `fibreGenIdeal`, equal only up to radical). -/
theorem ringKrullDim_quotient_eq_of_radical_eq {R : Type*} [CommRing R] {I J : Ideal R}
    (h : I.radical = J.radical) :
    ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ J) := by
  rw [ringKrullDim_quotient_radical I, ringKrullDim_quotient_radical J, h]

end DLNFibre.Core

/-- Non-vacuity witness: in `ℚ[X]`, the square `(X)^2` of the prime `(X)` shares its radical, so the
two quotient Krull dimensions agree — a genuinely non-reduced ideal `(X)^2` reduced to `(X)` without
changing the dimension. -/
example :
    ringKrullDim (Polynomial ℚ ⧸ (Ideal.span {Polynomial.X} : Ideal (Polynomial ℚ)) ^ 2)
      = ringKrullDim (Polynomial ℚ ⧸ (Ideal.span {Polynomial.X} : Ideal (Polynomial ℚ))) := by
  apply DLNFibre.Core.ringKrullDim_quotient_eq_of_radical_eq
  exact Ideal.radical_pow (I := (Ideal.span {Polynomial.X} : Ideal (Polynomial ℚ))) (by norm_num)

exec
/bin/bash -lc "sed -n '1,220p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean && sed -n '220,360p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
import DLNFibre.Core.OrbitSmooth

/-!
# `DLNFibre.Core.FibreNormalForm` — same-rank ⟹ same fibre codimension (G1)

The first concrete rung of the Lehalleur–Rimányi Lemma-4.6 fibre-codimension build: the geometric
codimension of the multiplication-map fibre `mult⁻¹(B)` depends on `B` **only through its rank**. So
the whole problem reduces to a single normal-form fibre.

**Mechanism (over any infinite field — no `IsAlgClosed`).** The `G_d` base-change action
(`Core.BaseChange.baseChange`) specialised to the **two end vertices** `0` and `N` acts on `Rep_d`,
fixing the inner factors and multiplying `A_last` by `P_N` on the left, `A_0` by `P_0⁻¹` on the
right. Two facts chain:

1. **mult-equivariance** (`mult_smul`): `mult d (P • A) = P_N · (mult d A) · P_0⁻¹` — the inner
   units telescope away (`Core.BaseChange.submult_smul` at the full interval `(0, last)`, through
   `mult_eq_submult`). Hence the linear automorphism `A ↦ P • A` carries `fibre d B` bijectively
   onto `fibre d (P_N · B · P_0⁻¹)` (`image_smul_fibre`).
2. **codim-invariance** (`codimRep_baseChange_image`): a base change is a *linear* change of the
   matrix-entry coordinates, so it induces the `k`-algebra automorphism `baseChangeAlgEquiv P` of
   the coordinate ring (`Core.OrbitSmooth`); `Ideal.height` of a vanishing ideal is invariant under
   it (`RingEquiv.height_comap`). This fills the gap that `Core.OrbitCodim`'s docstring flagged
   ("linear-coordinate invariance is NOT proved here") for the base-change family of linear isos.

Chaining (1)+(2): `codimRepCanonical (fibre d (P_N · B · P_0⁻¹)) = codimRepCanonical (fibre d B)`
(`codimRepCanonical_fibre_baseChange`). With the rank-normal-form fact that any two matrices of the
same rank are `GL × GL`-equivalent (`exists_baseChange_of_rank_eq`), this gives the headline
`codimRepCanonical_fibre_eq_of_rank_eq`: same rank ⟹ same fibre codimension.

**Typeclass.** `[Field k] [Infinite k]` — `Infinite` carries `baseChangeAlgEquiv` (the
`MvPolynomial.funext` step); the rank-normal-form needs only `Field`. An algebraically closed `k` is
infinite, so the DLN application (`k = ℂ`) satisfies it. **Dependency rule:** `Core` only — never import
`DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## API contracts (durable, pre-staged) -/

section Contracts

/-- `mult` is the full interval sub-product `submult … 0 (last)`. -/
example (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) :
    mult d A = submult d A 0 (Fin.last N) (Fin.zero_le _) := mult_eq_submult d A

/-- The end-factor telescoping: `submult (P • A) 0 (last) = P_last · submult A 0 last · P_0⁻¹`. -/
example (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d) :
    submult d (P • A) 0 (Fin.last N) (Fin.zero_le _)
      = Units.val (P (Fin.last N)) * submult d A 0 (Fin.last N) (Fin.zero_le _)
        * Units.val ((P 0)⁻¹) :=
  submult_smul P A 0 (Fin.last N) (Fin.zero_le _)

/-- `RingEquiv.height_comap`: comap along a ring equiv preserves height. -/
example {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (I : Ideal S) :
    (I.comap e).height = I.height := RingEquiv.height_comap e I

/-- `eval_baseChangePullback`: pullback evaluates as the `G_d`-shift. -/
example [Infinite k] (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := k) d)
    (x : RepCoord d → k) (f : MvPolynomial (RepCoord d) k) :
    MvPolynomial.eval x (baseChangePullback P f)
      = MvPolynomial.eval (canonicalCoord d (P • (canonicalCoord d).symm x)) f :=
  eval_baseChangePullback P x f

end Contracts

/-! ## mult-equivariance under the base-change action -/

/-- **mult-equivariance.** `mult d (P • A) = P_N · (mult d A) · P_0⁻¹`: the inner units of the base
change telescope away, leaving only the two end-vertex units (`submult_smul` at the full interval
`(0, last)`, through `mult_eq_submult`). -/
theorem mult_smul (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d) :
    mult d (P • A)
      = Units.val (P (Fin.last N)) * mult d A * Units.val ((P 0)⁻¹) := by
  rw [mult_eq_submult, mult_eq_submult, submult_smul]

/-! ## The fibre under the base-change action -/

/-- **The base-change image of a fibre is a fibre.** The linear automorphism `A ↦ P • A` carries
`fibre d B` onto `fibre d (P_N · B · P_0⁻¹)`: by mult-equivariance, `mult (P • A) = P_N · B · P_0⁻¹`
iff `mult A = B`. -/
theorem image_smul_fibre (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := k) d)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) :
    (fun A ↦ P • A) '' (fibre d B)
      = fibre d (Units.val (P (Fin.last N)) * B * Units.val ((P 0)⁻¹)) := by
  ext A
  constructor
  · rintro ⟨A₀, hA₀, rfl⟩
    rw [mem_fibre, mult_smul]
    rw [mem_fibre] at hA₀
    rw [hA₀]
  · intro hA
    refine ⟨P⁻¹ • A, ?_, smul_inv_smul P A⟩
    rw [mem_fibre] at hA
    rw [mem_fibre, mult_smul, hA]
    simp only [Pi.inv_apply, inv_inv]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul,
      Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

/-! ## Codim-invariance under the base-change action -/

/-- **The vanishing-ideal transport for a base change.** The vanishing ideal of the image of
`(P • ·) '' Z` is the `comap` of the vanishing ideal of `Z` along `baseChangePullback P`: a
polynomial vanishes on the shifted set iff its pullback vanishes on the original
(`eval_baseChangePullback`). -/
theorem vanishingIdeal_image_smul [Infinite k] (d : Fin (N + 1) → ℕ)
    (P : BaseChangeGroup (k := k) d) (Z : Set (Tuple (k := k) d)) :
    vanishingIdeal k (canonicalCoord d '' ((fun A ↦ P • A) '' Z))
      = (vanishingIdeal k (canonicalCoord d '' Z)).comap
          (baseChangePullback P : MvPolynomial (RepCoord d) k →+* _) := by
  ext f
  rw [Ideal.mem_comap, MvPolynomial.mem_vanishingIdeal_iff, MvPolynomial.mem_vanishingIdeal_iff]
  constructor
  · intro hf x hx
    obtain ⟨A, hA, rfl⟩ := hx
    rw [MvPolynomial.aeval_eq_eval]
    show MvPolynomial.eval (canonicalCoord d A) (baseChangePullback P f) = 0
    rw [eval_baseChangePullback, Equiv.symm_apply_apply, ← MvPolynomial.aeval_eq_eval]
    exact hf _ ⟨P • A, ⟨A, hA, rfl⟩, rfl⟩
  · intro hf x hx
    obtain ⟨y, ⟨A, hA, rfl⟩, rfl⟩ := hx
    have hval := hf (canonicalCoord d A) ⟨A, hA, rfl⟩
    rw [MvPolynomial.aeval_eq_eval] at hval ⊢
    show MvPolynomial.eval (canonicalCoord d (P • A)) f = 0
    rw [show canonicalCoord d (P • A)
        = canonicalCoord d (P • (canonicalCoord d).symm (canonicalCoord d A)) from by
        rw [Equiv.symm_apply_apply],
      ← eval_baseChangePullback P (canonicalCoord d A) f]
    exact hval

/-- **Codim-invariance under a base change.** The geometric codimension at the canonical flattening
is invariant under the linear automorphism `A ↦ P • A`: `codimRep (canonicalCoord) ((P•·) '' Z) =
codimRep (canonicalCoord) Z`. The transport `vanishingIdeal_image_smul` reads the shifted vanishing
ideal as a `comap` along `baseChangeAlgEquiv P` (a ring equiv), and `RingEquiv.height_comap`
preserves height. -/
theorem codimRep_baseChange_image [Infinite k] (d : Fin (N + 1) → ℕ)
    (P : BaseChangeGroup (k := k) d) (Z : Set (Tuple (k := k) d)) :
    codimRep (canonicalCoord d) ((fun A ↦ P • A) '' Z) = codimRep (canonicalCoord d) Z := by
  rw [codimRep, codimRep, vanishingIdeal_image_smul]
  have he : (baseChangePullback P : MvPolynomial (RepCoord d) k →+* _)
      = ((baseChangeAlgEquiv P).toRingEquiv.toRingHom) := rfl
  rw [he]
  exact RingEquiv.height_comap (baseChangeAlgEquiv P).toRingEquiv _

/-- **Codim-invariance of a fibre under the end-factor base change.** Combining `image_smul_fibre`
and `codimRep_baseChange_image`: `codimRepCanonical (fibre d (P_N · B · P_0⁻¹)) = codimRepCanonical
(fibre d B)`. -/
theorem codimRepCanonical_fibre_baseChange [Infinite k] (d : Fin (N + 1) → ℕ)
    (P : BaseChangeGroup (k := k) d) (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) :
    codimRepCanonical (fibre d (Units.val (P (Fin.last N)) * B * Units.val ((P 0)⁻¹)))
      = codimRepCanonical (fibre d B) := by
  rw [codimRepCanonical, codimRepCanonical, ← image_smul_fibre, codimRep_baseChange_image]

/-! ## Rank normal form: equal rank ⟹ end-factor base-change equivalent

The classical fact "two matrices over a field of equal rank are `GL × GL`-equivalent" — there is no
off-the-shelf Mathlib v4.29 lemma, so it is built here at the linear-map level: a rank-`r` map
`f : (Fin n → k) →ₗ (Fin m → k)` restricts to an isomorphism `U ≃ range f` for `U` a complement of
`ker f` (`fU`), and two maps with equal `ker`/`range` finrank are conjugate by linear automorphisms
(`exists_conj`), assembled from the kernel/range complement decompositions and the equal-dimension
isos `LinearEquiv.ofFinrankEq`. -/

/-- The restriction isomorphism `U ≃ range f` for `U` a complement of `ker f`: through the quotient
`U ≃ (Fin n → k) ⧸ ker f` (`quotientEquivOfIsCompl`) and `(Fin n → k) ⧸ ker f ≃ range f`
(`quotKerEquivRange`). -/
noncomputable def fU (f : (Fin n → k) →ₗ[k] (Fin m → k)) (U : Submodule k (Fin n → k))
    (h : IsCompl (LinearMap.ker f) U) : U ≃ₗ[k] (LinearMap.range f) :=
  (Submodule.quotientEquivOfIsCompl _ U h).symm.trans (LinearMap.quotKerEquivRange f)

/-- The restriction iso `fU` agrees with `f` on `U`: `↑(fU u) = f u`. -/
theorem fU_coe (f : (Fin n → k) →ₗ[k] (Fin m → k)) (U : Submodule k (Fin n → k))
    (h : IsCompl (LinearMap.ker f) U) (u : U) :
    ((fU f U h u : LinearMap.range f) : Fin m → k) = f (u : Fin n → k) := by
  unfold fU
  rw [LinearEquiv.trans_apply, Submodule.quotientEquivOfIsCompl_symm_apply,
    LinearMap.quotKerEquivRange_apply_mk]

/-- **Equal ker/range finrank ⟹ conjugate by linear automorphisms.** Two linear maps `f, f' :
(Fin n → k) →ₗ (Fin m → k)` with `finrank (ker f) = finrank (ker f')` and `finrank (range f) =
finrank (range f')` satisfy `f' = eL ∘ f ∘ eR` for linear automorphisms `eL, eR`. Built from the
kernel/range complement decompositions (`prodEquivOfIsCompl`) and the equal-dimension piece-isos
(`LinearEquiv.ofFinrankEq`): `eR` matches the `f'`-decomposition of the domain to the
`f`-decomposition, `eL` the range decompositions, threaded through `fU` so the maps intertwine. -/
theorem exists_conj (f f' : (Fin n → k) →ₗ[k] (Fin m → k))
    (hker : Module.finrank k (LinearMap.ker f) = Module.finrank k (LinearMap.ker f'))
    (hran : Module.finrank k (LinearMap.range f) = Module.finrank k (LinearMap.range f')) :
    ∃ (eL : (Fin m → k) ≃ₗ[k] (Fin m → k)) (eR : (Fin n → k) ≃ₗ[k] (Fin n → k)),
      f' = (eL : (Fin m → k) →ₗ[k] _) ∘ₗ f ∘ₗ (eR : (Fin n → k) →ₗ[k] _) := by
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl (LinearMap.ker f)
  obtain ⟨U', hU'⟩ := Submodule.exists_isCompl (LinearMap.ker f')
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.range f)
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl (LinearMap.range f')
  have hUdim : Module.finrank k U = Module.finrank k U' := by
    have a := Submodule.finrank_add_eq_of_isCompl hU
    have b := Submodule.finrank_add_eq_of_isCompl hU'
    rw [Module.finrank_fin_fun] at a b; omega
  have hWdim : Module.finrank k W = Module.finrank k W' := by
    have a := Submodule.finrank_add_eq_of_isCompl hW
    have b := Submodule.finrank_add_eq_of_isCompl hW'
    rw [Module.finrank_fin_fun] at a b; omega
  set eKer : (LinearMap.ker f) ≃ₗ[k] (LinearMap.ker f') := LinearEquiv.ofFinrankEq _ _ hker
  set eU : U ≃ₗ[k] U' := LinearEquiv.ofFinrankEq U U' hUdim
  set eWc : W ≃ₗ[k] W' := LinearEquiv.ofFinrankEq W W' hWdim
  set rf := fU f U hU with hrf
  set rf' := fU f' U' hU' with hrf'
  set dRf := Submodule.prodEquivOfIsCompl _ U hU with hdRf
  set dRf' := Submodule.prodEquivOfIsCompl _ U' hU' with hdRf'
  set dLf := Submodule.prodEquivOfIsCompl _ W hW with hdLf
  set dLf' := Submodule.prodEquivOfIsCompl _ W' hW' with hdLf'
  set eRange : (LinearMap.range f) ≃ₗ[k] (LinearMap.range f') := rf.symm.trans (eU.trans rf')
    with heRange
  set eR : (Fin n → k) ≃ₗ[k] (Fin n → k) :=
    dRf'.symm.trans ((eKer.symm.prodCongr eU.symm).trans dRf) with heR
  set eL : (Fin m → k) ≃ₗ[k] (Fin m → k) :=
    dLf.symm.trans ((eRange.prodCongr eWc).trans dLf') with heL
    dLf.symm.trans ((eRange.prodCongr eWc).trans dLf') with heL
  refine ⟨eL, eR, ?_⟩
  apply LinearMap.ext
  intro x
  show f' x = eL (f (eR x))
  set c := (dRf'.symm x).1 with hc
  set e := (dRf'.symm x).2 with he
  have hfx : f' x = ((rf' e : LinearMap.range f') : Fin m → k) := by
    have hxe : x = (c : Fin n → k) + (e : Fin n → k) := by
      conv_lhs => rw [← dRf'.apply_symm_apply x]
      rfl
    rw [hxe, map_add, LinearMap.mem_ker.mp c.2, zero_add, fU_coe]
  have heRx : eR x = (eKer.symm c : Fin n → k) + (eU.symm e : Fin n → k) := by
    rw [heR, LinearEquiv.trans_apply, LinearEquiv.trans_apply]
    show (dRf ((eKer.symm.prodCongr eU.symm) (dRf'.symm x))) = _
    rfl
  have hfeRx : f (eR x) = ((rf (eU.symm e) : LinearMap.range f) : Fin m → k) := by
    rw [heRx, map_add, LinearMap.mem_ker.mp (eKer.symm c).2, zero_add, fU_coe]
  rw [hfx, hfeRx]
  have key : eL ((rf (eU.symm e) : LinearMap.range f) : Fin m → k)
      = ((rf' e : LinearMap.range f') : Fin m → k) := by
    rw [heL, LinearEquiv.trans_apply, LinearEquiv.trans_apply]
    have hsub : dLf.symm ((rf (eU.symm e) : LinearMap.range f) : Fin m → k)
        = (rf (eU.symm e), 0) := by
      rw [hdLf, Submodule.prodEquivOfIsCompl_symm_apply_left]
    rw [hsub]
    show dLf' ((eRange.prodCongr eWc) (rf (eU.symm e), 0)) = _
    rw [LinearEquiv.prodCongr_apply]
    simp only [map_zero]
    rw [hdLf', Submodule.coe_prodEquivOfIsCompl']
    simp only [ZeroMemClass.coe_zero, add_zero]
    congr 1
    rw [heRange, LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.apply_symm_apply]
  rw [key]

/-- The unit matrix `toMatrix' e` of a linear automorphism `e` of `(Fin p → k)`, with inverse
`toMatrix' e.symm` (composition of inverse equivs is the identity, whose matrix is `1`). -/
noncomputable def equivUnitMatrix {p : ℕ} (e : (Fin p → k) ≃ₗ[k] (Fin p → k)) :
    (Matrix (Fin p) (Fin p) k)ˣ where
  val := LinearMap.toMatrix' (e : (Fin p → k) →ₗ[k] _)
  inv := LinearMap.toMatrix' (e.symm : (Fin p → k) →ₗ[k] _)
  val_inv := by
    rw [← LinearMap.toMatrix'_comp,
      show (e : (Fin p → k) →ₗ[k] _) ∘ₗ (e.symm : (Fin p → k) →ₗ[k] _) = LinearMap.id from by
        ext x; simp]
    exact LinearMap.toMatrix'_id
  inv_val := by
    rw [← LinearMap.toMatrix'_comp,
      show (e.symm : (Fin p → k) →ₗ[k] _) ∘ₗ (e : (Fin p → k) →ₗ[k] _) = LinearMap.id from by
        ext x; simp]
    exact LinearMap.toMatrix'_id

/-- **Equal rank ⟹ end-factor equivalent.** Two matrices `B, B'` of the same rank are related by an
end-factor base change: `∃ P, B' = P_N · B · P_0⁻¹` (the rank normal form / "matrices of equal rank
are equivalent"). Needs the two end vertices distinct (`hN : 0 ≠ Fin.last N`, i.e. `N ≥ 1`) — for
`N = 0` the multiplication map is constant `1` and the claim is false. Built from `exists_conj` at
`f = toLin' B`, `f' = toLin' B'`, transferred to matrices via `LinearMap.toMatrix'`, with the two
end units `equivUnitMatrix eL` (at `last N`) and `(equivUnitMatrix eR)⁻¹` (at `0`). -/
theorem exists_baseChange_of_rank_eq (d : Fin (N + 1) → ℕ)
    (hN : (0 : Fin (N + 1)) ≠ Fin.last N)
    (B B' : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) (h : B.rank = B'.rank) :
    ∃ P : BaseChangeGroup (k := k) d,
      B' = Units.val (P (Fin.last N)) * B * Units.val ((P 0)⁻¹) := by
  have hran : Module.finrank k (LinearMap.range (toLin' B))
      = Module.finrank k (LinearMap.range (toLin' B')) := h
  have hker : Module.finrank k (LinearMap.ker (toLin' B))
      = Module.finrank k (LinearMap.ker (toLin' B')) := by
    have e1 := LinearMap.finrank_range_add_finrank_ker (toLin' B)
    have e2 := LinearMap.finrank_range_add_finrank_ker (toLin' B')
    omega
  obtain ⟨eL, eR, hconj⟩ := exists_conj (toLin' B) (toLin' B') hker hran
  -- transfer the conjugation to matrices: B' = (toMatrix' eL) * B * (toMatrix' eR)
  have hmat : B' = (equivUnitMatrix eL).val * B * (equivUnitMatrix eR).val := by
    have hc := congrArg LinearMap.toMatrix' hconj
    rw [LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp,
      LinearMap.toMatrix'_toLin', ← Matrix.mul_assoc] at hc
    exact hc
  -- assemble the BaseChangeGroup: `last N ↦ equivUnitMatrix eL`, `0 ↦ (equivUnitMatrix eR)⁻¹`
  set P : BaseChangeGroup (k := k) d :=
    fun v ↦ if hv : v = Fin.last N then (by rw [hv]; exact equivUnitMatrix eL)
      else if hv0 : v = 0 then (by rw [hv0]; exact (equivUnitMatrix eR)⁻¹) else 1 with hP
  refine ⟨P, ?_⟩
  have hPL : P (Fin.last N) = equivUnitMatrix eL := by rw [hP]; simp
  have hP0 : P 0 = (equivUnitMatrix eR)⁻¹ := by
    rw [hP]
    show (if hv : (0 : Fin (N + 1)) = Fin.last N then (by rw [hv]; exact equivUnitMatrix eL)
      else if hv0 : (0 : Fin (N + 1)) = 0 then (by rw [hv0]; exact (equivUnitMatrix eR)⁻¹)
      else 1) = (equivUnitMatrix eR)⁻¹
    rw [dif_neg hN, dif_pos rfl]
    rfl
  rw [hPL, hP0, inv_inv]
  exact hmat

/-! ## The headline: same rank ⟹ same fibre codimension -/

/-- **Same rank ⟹ same fibre codimension.** The geometric codimension of the multiplication-map
fibre depends on the target `B` only through its rank: for `B.rank = B'.rank`,
`codimRepCanonical (fibre d B) = codimRepCanonical (fibre d B')`. Reduces the Lemma-4.6 problem (all
rank-`r` targets) to a single fibre. Needs `N ≥ 1` (`hN : 0 ≠ Fin.last N`): for `N = 0` the
multiplication map is the constant `1`, so the fibre over `1` is everything but the fibre over a
different same-rank `B'` is empty — the claim is genuinely false there. -/
theorem codimRepCanonical_fibre_eq_of_rank_eq [Infinite k] (d : Fin (N + 1) → ℕ)
    (hN : (0 : Fin (N + 1)) ≠ Fin.last N)
    (B B' : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) (h : B.rank = B'.rank) :
    codimRepCanonical (fibre d B) = codimRepCanonical (fibre d B') := by
  obtain ⟨P, hP⟩ := exists_baseChange_of_rank_eq d hN B B' h
  rw [hP, codimRepCanonical_fibre_baseChange]

/-! ## Non-vacuity witness

On the `(2,2,2)` dimension vector over `ℚ` (a `Field` that is `Infinite`), the two distinct rank-1
targets `!![1,0;0,0]` and `!![0,0;1,0]` have equal fibre codimension — the headline applied to a
genuine instance (the two matrices differ; equal rank because the second is a unit-multiple of the
first). The end vertices `0` and `2` are distinct, so `hN` holds. -/

section Witness

/-- The two `(2,2,2)`-witness rank-1 targets have equal fibre codimension. -/
example :
    codimRepCanonical (k := ℚ) (fibre dWitness (!![1, 0; 0, 0]))
      = codimRepCanonical (k := ℚ) (fibre dWitness (!![0, 0; 1, 0])) := by
  have hrank : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ).rank
      = (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ).rank := by
    have hP : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ) * !![1, 0; 0, 0] = !![0, 0; 1, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    have hu : IsUnit (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ).det := by
      rw [Matrix.det_fin_two_of]; norm_num
    rw [← hP, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hu]
  have hN : (0 : Fin (2 + 1)) ≠ Fin.last 2 := by decide
  exact codimRepCanonical_fibre_eq_of_rank_eq dWitness hN _ _ hrank

end Witness

end DLNFibre.Core

exec
/bin/bash -lc "sed -n '1,230p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Setup.lean && sed -n '1,430p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# `DLNFibre.Core.Setup` — ambient objects of the quiver engine

The network-free substrate for the geometry of the DLN fibre (Le Halleur–Rimányi 2024, §2): for
a fixed dimension vector `d = (d₀, …, d_N)` over a `CommRing k`, the space `Rep_d` of composable
matrix tuples, the multiplication map `mult : (A₁,…,A_N) ↦ A_N ⋯ A₁`, the product-rank loci `Σ^r`
/ `Σ^{≤r}`, and the fibre `mult⁻¹(B)`.

**Encoding.** The dimension vector is a fixed parameter `d : Fin (N + 1) → ℕ`, and `Rep_d` is the
product space `Tuple d := ∀ i : Fin N, Matrix (Fin (d i.succ)) (Fin (d i.castSucc)) k` (`Aᵢ` maps
`Fin (d_{i-1}) → Fin (d_i)`). This matches the paper's `Rep_d = ∏ Mat_{dᵢ,d_{i-1}}` directly, so
the rank loci and fibres are honest `Set (Tuple d)` for a *fixed* `d`. The ordered product is
defined through the prefix products `multPrefix`, whose `rfl` step lemmas (`multPrefix_zero`,
`multPrefix_succ`) let downstream lemmas recurse on the product without unfolding `Fin.induction`.

**Typeclass.** `CommRing k` is the weakest class carrying `Matrix.rank` (which is defined over a
`CommRing`); a `Field` is not needed for these definitions. **Dependency rule:** never import
`DLNFibre.DLN`.
-/

namespace DLNFibre.Core

universe u

variable {k : Type u} [CommRing k] {N : ℕ}

/-- `Rep_d`: a composable matrix tuple `(A₁, …, A_N)` for the dimension vector `d`, with
`Aᵢ : Matrix (Fin dᵢ) (Fin d_{i-1}) k`. -/
abbrev Tuple (d : Fin (N + 1) → ℕ) : Type u :=
  ∀ i : Fin N, Matrix (Fin (d i.succ)) (Fin (d i.castSucc)) k

/-- The prefix product `Aⱼ ⋯ A₁ : Matrix (Fin dⱼ) (Fin d₀) k` of the first `j` factors. -/
def multPrefix (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) :
    (j : Fin (N + 1)) → Matrix (Fin (d j)) (Fin (d 0)) k :=
  Fin.induction (1 : Matrix (Fin (d 0)) (Fin (d 0)) k) (fun i prev ↦ A i * prev)

/-- The empty prefix product is the identity. -/
@[simp] theorem multPrefix_zero (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) :
    multPrefix d A 0 = 1 := rfl

/-- The prefix product gains its next factor on the left:
`(prefix to i.succ) = Aᵢ * (prefix to i)`. -/
@[simp] theorem multPrefix_succ (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) (i : Fin N) :
    multPrefix d A i.succ = A i * multPrefix d A i.castSucc := rfl

/-- The multiplication map `mult (A₁,…,A_N) = A_N ⋯ A₁ : Matrix (Fin d_N) (Fin d₀) k`. -/
def mult (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) :
    Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k :=
  multPrefix d A (Fin.last N)

/-- The product-rank-`r` locus `Σ^r = {A | rank (mult A) = r}`. -/
def productRankLocus (d : Fin (N + 1) → ℕ) (r : ℕ) : Set (Tuple (k := k) d) :=
  {A | (mult d A).rank = r}

/-- The product-rank-`≤ r` locus `Σ^{≤r} = {A | rank (mult A) ≤ r}` (the union `⋃_{s ≤ r} Σ^s`). -/
def productRankLocusLE (d : Fin (N + 1) → ℕ) (r : ℕ) : Set (Tuple (k := k) d) :=
  {A | (mult d A).rank ≤ r}

/-- The fibre `mult⁻¹(B) = {A | mult A = B}` over a target matrix `B`. -/
def fibre (d : Fin (N + 1) → ℕ) (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) :
    Set (Tuple (k := k) d) :=
  {A | mult d A = B}

/-- `Σ^r` membership is exactly `rank (mult A) = r`. -/
theorem mem_productRankLocus {d : Fin (N + 1) → ℕ} {r : ℕ} {A : Tuple (k := k) d} :
    A ∈ productRankLocus d r ↔ (mult d A).rank = r := Iff.rfl

/-- `Σ^{≤r}` membership is exactly `rank (mult A) ≤ r`. -/
theorem mem_productRankLocusLE {d : Fin (N + 1) → ℕ} {r : ℕ} {A : Tuple (k := k) d} :
    A ∈ productRankLocusLE d r ↔ (mult d A).rank ≤ r := Iff.rfl

/-- Fibre membership is exactly `mult A = B`. -/
theorem mem_fibre {d : Fin (N + 1) → ℕ} {A : Tuple (k := k) d}
    {B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k} :
    A ∈ fibre d B ↔ mult d A = B := Iff.rfl

/-- The fibre is the preimage of the singleton `{B}` under `mult`, matching the paper's
`mult⁻¹(B)`. -/
theorem fibre_eq_preimage (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) :
    fibre d B = mult d ⁻¹' {B} := rfl

section Witness

/-! ## Non-vacuity witness

`N = 2`, dimension vector `(2, 2, 2)`, over `ℤ`: with `A₁ = [[1,2],[0,1]]` and `A₂ = [[1,0],[3,1]]`,
`mult = A₂ A₁ = [[1,2],[3,7]]`, so this tuple lies in `Σ^2` and in the fibre over
`[[1,2],[3,7]]`. -/

/-- Witness dimension vector `(2, 2, 2)`. -/
def dWitness : Fin 3 → ℕ := ![2, 2, 2]

/-- Witness tuple `(A₁, A₂)` over `ℤ`. -/
def tupleWitness : Tuple (k := ℤ) dWitness := fun i ↦
  match i with
  | 0 => !![1, 2; 0, 1]
  | 1 => !![1, 0; 3, 1]

/-- `mult` computes the ordered product `A₂ A₁` on the witness. -/
example : mult dWitness tupleWitness = !![1, 2; 3, 7] := by
  unfold mult multPrefix tupleWitness dWitness
  decide

/-- The witness lies in the fibre over its own product — the loci and the fibre are inhabited. -/
example : tupleWitness ∈ fibre dWitness (!![1, 2; 3, 7]) := by
  change mult dWitness tupleWitness = !![1, 2; 3, 7]
  unfold mult multPrefix tupleWitness dWitness
  decide

end Witness

end DLNFibre.Core
import DLNFibre.Core.DeterminantalBasePresentation
import DLNFibre.Core.FibreReducedTrivialization

/-!
# `DLNFibre.Core.DeepChartRing` — the deep chart ring `Sred` + the localized base→total map
# (R2-3b-1+2)

The first rungs of the **deep** product trivialization `e` that R2-3a
(`Core.FibreReducedTrivialization`) carries as a hypothesis. The engine's localized determinantal
presentation (`Core.DeterminantalBasePresentation`) is `N = 1` only: `basePresentationEquiv` lives
over `dStratum q p = ![q, p]`, a single matrix. This module builds, for a **general** dimension
vector `d : Fin (N + 1) → ℕ`, the deep localized chart ring `Sred` of the rank-`≤ r` product locus
on the pivot chart, and the localized base→total `k`-algebra map that gives `Sred` its
`SchurLoc`-algebra structure (the `R = SchurLoc`-algebra structure that R2-3a's `e` needs).

The deliverables, with `q = d 0` (source dimension) and `p = d (Fin.last N)` (target dimension):

**R2-3b-1 — the deep chart ring (definitions + instances + bridges).**
1. `ΔPdeep d r hp hq` — the deep pivot minor: the determinant of the top-left `r×r` submatrix of the
   **deep** generic product `Matrix.of (multPoly d)` (the deep analog of `N = 1`'s `detPivotPoly`).
2. `IadDeep d r hp hq` — the localized base ideal `(sigmaIdeal d r).map (algebraMap …)` pushed into
   `Localization.Away (ΔPdeep …)` (the deep analog of `Iad`).
3. `Sred d r hp hq := Localization.Away (ΔPdeep …) ⧸ IadDeep …` — the deep chart quotient ring, with
   its `CommRing` / `Algebra k` instances inherited, and `isReduced_Sred` : `IsReduced (Sred …)`
   (over `[IsAlgClosed k]`, justifying the name — this is R2-3a's `hSred`, now discharged).
4. The **type bridge** `repStratumEquiv : RepCoord (dStratum q p) ≃ Fin p × Fin q` (the
   single-matrix stratum coords), via `Equiv.uniqueSigma` (the `Sigma` over the `Unique` base
   `Fin 1`), and the deep base comorphism `deepBaseComap d` carrying the `N = 1` base coordinate
   ring into the deep total coordinate ring (`multComap d` after the rename).

**R2-3b-2 — the localized base→total map + the `SchurLoc`-algebra structure.**
5. `deepBaseComap_detPivot` — the load-bearing transport: `deepBaseComap d` carries the `N = 1`
   pivot minor `detPivotPoly` to the deep `ΔPdeep` (det commutes with `aeval`, `AlgHom.map_det`),
   making the localized map well-typed.
6. `deepBaseComap_sigmaIdeal_le` — the (non-circular) ideal direction: `deepBaseComap d` maps the
   base `sigmaIdeal (dStratum q p) r` into the deep `sigmaIdeal d r`. Mechanism: a **deep** total
   point
   `A ∈ Σ̄^r_d` maps by `mult` to a single-matrix **base** point in `Σ̄^r_{(q,p)}` (chase via
   `aeval_deepBaseComap` + `singleTuple`). It does **not** assume the circular `sigmaIdeal ≤
   fibreGenIdeal`.
7. `baseLocMap` / `schurToSred` — the localized base map `Localization.Away detPivotPoly →ₐ[k]
   Localization.Away (ΔPdeep …)` (`IsLocalization.Away.mapₐ`), lifted to the quotients
   (`Ideal.quotientMapₐ`), then composed with `basePresentationEquiv.symm` to give a `k`-algebra map
   `SchurLoc q p r →ₐ[k] Sred d r hp hq`. The resulting `SchurLoc`-algebra structure on `Sred`
   (`RingHom.toAlgebra`) + the `IsScalarTower k (SchurLoc …) (Sred …)` instance.

**Scope (what is NOT here).** The full product iso `e : Sred ≃ₐ[k] SchurLoc ⊗_k FibreAlg`, the
endpoint-normalization `AlgEquiv`, and the descent of the iso to the reduced chart quotient are
**R2-3b-3 and R2-3b-4** (later tides). No result here claims `codim (fibre) = C + δ` or discharges
`BundleShiftInterface` — `e` is not yet built. (R2-3a's *other* hypothesis, `IsReduced S`, **is**
discharged here: `isReduced_Sred`, so R2-3b-4 needs only `e` itself.) The R2-3b-3
endpoint-normalization `aeval`-substitution contract is pre-staged below as an `example` block (an
arbitrary coefficient ring `R`, via `AlgEquiv.ofAlgHom`, **not** `baseChangeAlgEquiv` which carries
`[Infinite k]`).

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## R2-3b-1 — the type bridge and the deep base comorphism

For the single-arrow stratum `dStratum q p = ![q, p]`, the coordinate index
`RepCoord (dStratum q p)` is a `Sigma` over `Fin 1`; collapsing it gives `Fin p × Fin q` (the
single-matrix entry coords). The deep base comorphism is the `N = 1` base coordinate map
`multComap d` precomposed with this rename. -/

/-- **The single-matrix stratum-coordinate bridge** `RepCoord (dStratum q p) ≃ Fin p × Fin q`. The
coordinate index of `dStratum q p = ![q, p]` is `Σ i : Fin 1, Fin (dStratum q p i.succ) ×
Fin (dStratum q p i.castSucc)`; over the `Unique` base `Fin 1` this is the single fibre
`Fin p × Fin q` (`default = 0`, `dStratum q p (0).succ = p`, `dStratum q p (0).castSucc = q`). -/
def repStratumEquiv (q p : ℕ) : RepCoord (dStratum q p) ≃ Fin p × Fin q :=
  Equiv.uniqueSigma (fun i : Fin 1 ↦ Fin (dStratum q p i.succ) × Fin (dStratum q p i.castSucc))

@[simp] theorem repStratumEquiv_mk (q p : ℕ) (x : Fin p × Fin q) :
    repStratumEquiv q p ⟨0, x⟩ = x := rfl

/-- **The deep base comorphism** `MvPolynomial (RepCoord (dStratum q p)) k →ₐ[k]
MvPolynomial (RepCoord d) k` (`q = d 0`, `p = d (last N)`): the `mult` comorphism `multComap d`
precomposed with the single-matrix coordinate rename. Carries the `N = 1` base coordinate ring into
the deep total coordinate ring. -/
noncomputable def deepBaseComap (d : Fin (N + 1) → ℕ) :
    MvPolynomial (RepCoord (dStratum (d 0) (d (Fin.last N)))) k →ₐ[k]
      MvPolynomial (RepCoord d) k :=
  (multComap d).comp (renameEquiv k (repStratumEquiv (d 0) (d (Fin.last N)))).toAlgHom

/-- `deepBaseComap d` sends the single-matrix coordinate variable `X ⟨0, (a, b)⟩` to the deep
generic product entry `multPoly d a b`. -/
@[simp] theorem deepBaseComap_X (d : Fin (N + 1) → ℕ)
    (a : Fin (d (Fin.last N))) (b : Fin (d 0)) :
    deepBaseComap (k := k) d (X ⟨0, (a, b)⟩) = multPoly d a b := by
  rw [deepBaseComap]
  simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, renameEquiv_apply,
    rename_X, repStratumEquiv_mk, multComap_X]

/-! ## R2-3b-1 — the deep chart ring `Sred` -/

/-- **The deep pivot minor** `ΔPdeep d r`: the determinant of the top-left `r×r` submatrix of the
deep generic product `Matrix.of (multPoly d)`. The deep analog of `N = 1`'s `detPivotPoly`;
inverting it is the pivot chart. -/
noncomputable def ΔPdeep (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) : MvPolynomial (RepCoord d) k :=
  ((Matrix.of (multPoly d)).submatrix
    (fun i : Fin r ↦ (Fin.castLE hp i : Fin (d (Fin.last N))))
    (fun j : Fin r ↦ (Fin.castLE hq j : Fin (d 0)))).det

/-- **The deep localized base ideal** `IadDeep d r`: the determinantal base ideal `sigmaIdeal d r`
pushed into the localized total ring `Localization.Away (ΔPdeep …)`. The deep analog of `Iad`. -/
noncomputable def IadDeep (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    Ideal (Localization.Away (ΔPdeep (k := k) d r hp hq)) :=
  (sigmaIdeal d r).map (algebraMap (MvPolynomial (RepCoord d) k)
    (Localization.Away (ΔPdeep (k := k) d r hp hq)))

/-- **The deep chart ring** `Sred d r := Localization.Away (ΔPdeep …) ⧸ IadDeep …`: the localized
chart quotient of the rank-`≤ r` product locus for general `d`, on the pivot chart. The `CommRing` /
`Algebra k` instances are inherited from the localization-quotient. -/
noncomputable abbrev Sred (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) : Type u :=
  Localization.Away (ΔPdeep (k := k) d r hp hq) ⧸ IadDeep (k := k) d r hp hq

/-! ## R2-3b-1 — `Sred` is reduced (justifying the name; discharges R2-3a's `hSred`)

The name `Sred` asserts reducedness, and that reducedness is precisely R2-3a's second hypothesis
`hSred : IsReduced S` (`Core.FibreReducedTrivialization.fibreGenIdeal_isRadical_of_trivialization`).
It is **cheap** here: `IadDeep = (sigmaIdeal d r).map (algebraMap …)` is radical because
`sigmaIdeal` is radical (`vanishingIdeal_isRadical`, over `[IsAlgClosed k]`) and localization
carries radical
ideals to radical ideals (`IsLocalization.map_radical`); a quotient by a radical ideal is reduced
(`Ideal.isRadical_iff_quotient_reduced`). No quotient↔localization interchange iso is needed. -/

/-- **`IadDeep` is radical** (`[IsAlgClosed k]`): the localized image of the radical determinantal
base ideal `sigmaIdeal d r`. Via `IsLocalization.map_radical`
(`(I.map …).radical = I.radical.map …`) and `sigmaIdeal`'s radicality
(`vanishingIdeal_isRadical`). -/
theorem IadDeep_isRadical [IsAlgClosed k] (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    (IadDeep (k := k) d r hp hq).IsRadical := by
  have hsig : (sigmaIdeal (k := k) d r).IsRadical := by
    rw [sigmaIdeal]; exact vanishingIdeal_isRadical _
  rw [← Ideal.radical_eq_iff, IadDeep,
    ← IsLocalization.map_radical (M := Submonoid.powers (ΔPdeep (k := k) d r hp hq)),
    hsig.radical]

/-- **`Sred` is reduced** (`[IsAlgClosed k]`), justifying the name.
`Sred = Localization.Away ΔPdeep ⧸ IadDeep` with `IadDeep` radical (`IadDeep_isRadical`); a quotient
by a radical ideal is reduced
(`Ideal.isRadical_iff_quotient_reduced`). This is exactly R2-3a's `hSred : IsReduced S` for
`S = Sred` — so R2-3b-4 needs to build only `e` itself, not also `IsReduced S`. -/
theorem isReduced_Sred [IsAlgClosed k] (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    IsReduced (Sred (k := k) d r hp hq) :=
  (Ideal.isRadical_iff_quotient_reduced _).mp (IadDeep_isRadical d r hp hq)

/-! ## R2-3b-2 — the load-bearing transports

`deepBaseComap` carries the `N = 1` pivot minor `detPivotPoly` to the deep `ΔPdeep` (making the
localized map well-typed), and the base `sigmaIdeal` into the deep `sigmaIdeal` (making the quotient
lift well-typed). -/

/-- **The pivot-minor transport** (load-bearing): `deepBaseComap d` carries the `N = 1` pivot minor
`detPivotPoly (d 0) (d last) r` to the deep pivot minor `ΔPdeep d r`. The determinant commutes with
the algebra map (`AlgHom.map_det`); each pivot entry `X ⟨0, (castLE i, castLE j)⟩` goes to
`multPoly d (castLE i) (castLE j)` (`deepBaseComap_X`), the corresponding entry of `Matrix.of
(multPoly d)`. (Exact analog of the landed `renameEquiv_detPivot`.) -/
theorem deepBaseComap_detPivot (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    deepBaseComap (k := k) d
        (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq)
      = ΔPdeep (k := k) d r hp hq := by
  rw [detPivotPoly, ΔPdeep, AlgHom.map_det]
  congr 1
  funext i j
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply,
    show (Matrix.of (multPoly (k := k) (dStratum (d 0) (d (Fin.last N)))))
        (Fin.castLE hp i) (Fin.castLE hq j)
        = X ⟨0, (Fin.castLE hp i, Fin.castLE hq j)⟩ from multPoly_stratum_apply _ _ _ _,
    deepBaseComap_X]
  rfl

/-! ### The single-matrix tuple and the comorphism chase -/

/-- The **single-matrix tuple** over `dStratum q p` from a matrix `M : Mat (p × q)`: the `N = 1`
`Tuple` whose lone factor is `M`. -/
def singleTuple (k : Type u) [Field k] (q p : ℕ) (M : Matrix (Fin p) (Fin q) k) :
    Tuple (k := k) (dStratum q p) :=
  fun i ↦ match i with | 0 => M

/-- `mult` of the single-matrix tuple is its matrix (the `N = 1` product is the lone factor). -/
theorem mult_singleTuple (q p : ℕ) (M : Matrix (Fin p) (Fin q) k) :
    mult (dStratum q p) (singleTuple k q p M) = M := by
  rw [mult_stratum_eq q p (singleTuple k q p M)]; rfl

/-- **The comorphism chase.** Evaluating `deepBaseComap d f` at the coordinates of a deep tuple `A`
equals evaluating `f` at the coordinates of the single-matrix base tuple of `mult d A`. Both are
`k`-algebra maps in `f`; on the generator `X ⟨0, (a, b)⟩` both give `(mult d A) a b`
(`eval_multPoly`). -/
theorem aeval_deepBaseComap (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d)
    (f : MvPolynomial (RepCoord (dStratum (d 0) (d (Fin.last N)))) k) :
    aeval (canonicalCoord d A) (deepBaseComap d f)
      = aeval (R := k) (canonicalCoord (dStratum (d 0) (d (Fin.last N)))
          (singleTuple k (d 0) (d (Fin.last N)) (mult (k := k) d A))) f := by
  have hgen : (aeval (canonicalCoord d A)).comp (deepBaseComap d)
      = aeval (R := k) (canonicalCoord (dStratum (d 0) (d (Fin.last N)))
          (singleTuple k (d 0) (d (Fin.last N)) (mult (k := k) d A))) := by
    apply MvPolynomial.algHom_ext
    intro x
    obtain ⟨i, a, b⟩ := x
    obtain rfl : i = 0 := Subsingleton.elim i 0
    simp only [AlgHom.comp_apply, deepBaseComap_X]
    rw [show aeval (R := k) (canonicalCoord d A) (multPoly d a b)
          = eval (canonicalCoord d A) (multPoly d a b) from by rw [aeval_def, eval]; rfl,
      eval_multPoly, aeval_X, canonicalCoord_apply]
    rfl
  exact DFunLike.congr_fun hgen f

/-- **The base→deep `sigmaIdeal` direction** (non-circular): `deepBaseComap d` maps the base
`sigmaIdeal (dStratum q p) r` into the deep `sigmaIdeal d r`. Via `Ideal.map_le_iff_le_comap`: a
base generator `f` vanishing on `Σ̄^r_{(q,p)}` pulls back to a polynomial vanishing on `Σ̄^r_d`,
because a **deep** total point `A ∈ Σ̄^r_d` maps by `mult` to a single-matrix **base** point in
`Σ̄^r_{(q,p)}` (`mult_singleTuple`, `rank (mult d A) ≤ r`), where `f` vanishes
(`aeval_deepBaseComap`).
Does **not** assume the circular `sigmaIdeal ≤ fibreGenIdeal`. -/
theorem deepBaseComap_sigmaIdeal_le (d : Fin (N + 1) → ℕ) (r : ℕ) :
    (sigmaIdeal (k := k) (dStratum (d 0) (d (Fin.last N))) r).map
        (deepBaseComap (k := k) d).toRingHom
      ≤ sigmaIdeal (k := k) d r := by
  rw [Ideal.map_le_iff_le_comap]
  intro f hf
  rw [Ideal.mem_comap, sigmaIdeal, mem_vanishingIdeal_iff]
  intro x hx
  obtain ⟨A, hA, rfl⟩ := hx
  rw [mem_productRankLocusLE] at hA
  change aeval (R := k) (canonicalCoord d A) ((deepBaseComap d).toRingHom f) = 0
  rw [show (deepBaseComap d).toRingHom f = deepBaseComap d f from rfl, aeval_deepBaseComap]
  rw [sigmaIdeal, mem_vanishingIdeal_iff] at hf
  exact hf _ ⟨singleTuple k (d 0) (d (Fin.last N)) (mult d A), by
    rw [mem_productRankLocusLE, mult_singleTuple]; exact hA, rfl⟩

/-! ## R2-3b-2 — the localized base map and the `SchurLoc`-algebra structure on `Sred`

The localized base map `Localization.Away detPivotPoly →ₐ[k] Localization.Away (ΔPdeep …)`
(`IsLocalization.Away.mapₐ deepBaseComap detPivotPoly`, well-typed by the transport
`deepBaseComap_detPivot`), lifted to the quotients (`Ideal.quotientMapₐ`, the ideal hypothesis
discharged by `deepBaseComap_sigmaIdeal_le`), then composed with `basePresentationEquiv.symm`. -/

/-- **The localized base map** `Localization.Away (detPivotPoly …) →ₐ[k]
Localization.Away (ΔPdeep …)`, `IsLocalization.Away.mapₐ` of the deep base comorphism
`deepBaseComap d` at `detPivotPoly`. The
codomain localization instance at `deepBaseComap d (detPivotPoly …)` is `ΔPdeep`'s (the transport
`deepBaseComap_detPivot`). -/
noncomputable def baseLocMap (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    Localization.Away (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq) →ₐ[k]
      Localization.Away (ΔPdeep (k := k) d r hp hq) := by
  haveI : IsLocalization.Away
      (deepBaseComap (k := k) d (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq))
      (Localization.Away (ΔPdeep (k := k) d r hp hq)) := by
    rw [deepBaseComap_detPivot]; infer_instance
  exact IsLocalization.Away.mapₐ _ _ (deepBaseComap d)
    (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq)

/-- `baseLocMap` sends `algebraMap … x` to `algebraMap … (deepBaseComap d x)` — it intertwines the
two localization maps (`IsLocalization.Away.mapₐ` / `IsLocalization.map` on the base ring). -/
theorem baseLocMap_algebraMap (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0)
    (x : MvPolynomial (RepCoord (dStratum (d 0) (d (Fin.last N)))) k) :
    baseLocMap (k := k) d r hp hq
        (algebraMap (MvPolynomial (RepCoord (dStratum (d 0) (d (Fin.last N)))) k)
          (Localization.Away (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq)) x)
      = algebraMap (MvPolynomial (RepCoord d) k) (Localization.Away (ΔPdeep (k := k) d r hp hq))
          (deepBaseComap d x) := by
  haveI : IsLocalization.Away
      (deepBaseComap (k := k) d (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq))
      (Localization.Away (ΔPdeep (k := k) d r hp hq)) := by
    rw [deepBaseComap_detPivot]; infer_instance
  rw [baseLocMap, IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map,
    IsLocalization.map_eq]
  rfl

/-- The base ideal `Iad` is carried into `IadDeep` by `baseLocMap`
(`Iad ≤ IadDeep.comap baseLocMap`), the hypothesis the quotient lift needs. `Iad`/`IadDeep` are the
localized images of the base / deep
`sigmaIdeal`s; `baseLocMap` intertwines the localization maps (`baseLocMap_algebraMap`) and carries
the base `sigmaIdeal` into the deep one (`deepBaseComap_sigmaIdeal_le`). -/
theorem Iad_le_comap_IadDeep (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    Iad (k := k) (d 0) (d (Fin.last N)) r hp hq
      ≤ (IadDeep (k := k) d r hp hq).comap (baseLocMap (k := k) d r hp hq) := by
  rw [Iad, Ideal.map_le_iff_le_comap]
  intro g hg
  rw [Ideal.mem_comap, Ideal.mem_comap, baseLocMap_algebraMap, IadDeep]
  -- `deepBaseComap g ∈ sigmaIdeal d r` (the base → deep direction), then push into the localization
  have hmem : deepBaseComap (k := k) d g ∈ sigmaIdeal (k := k) d r :=
    deepBaseComap_sigmaIdeal_le d r (Ideal.mem_map_of_mem _ hg)
  exact Ideal.mem_map_of_mem _ hmem

/-- **The localized base→total map on the quotients** `(Localization.Away detPivotPoly ⧸ Iad) →ₐ[k]
Sred d r`: the quotient lift of `baseLocMap` (`Ideal.quotientMapₐ`, the ideal hypothesis from
`Iad_le_comap_IadDeep`). -/
noncomputable def baseQuotMap (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    (Localization.Away (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq)
        ⧸ Iad (k := k) (d 0) (d (Fin.last N)) r hp hq)
      →ₐ[k] Sred (k := k) d r hp hq :=
  Ideal.quotientMapₐ (IadDeep (k := k) d r hp hq) (baseLocMap (k := k) d r hp hq)
    (Iad_le_comap_IadDeep d r hp hq)

/-- **The base→total `k`-algebra map** `SchurLoc q p r →ₐ[k] Sred d r` (`q = d 0`, `p = d last`):
`baseQuotMap` precomposed with `basePresentationEquiv.symm`. This is the morphism whose induced
algebra structure makes `Sred` a `SchurLoc`-algebra (the `R = SchurLoc`-algebra structure that
R2-3a's product iso `e` needs). `[IsAlgClosed k] [CharZero k]` (for `basePresentationEquiv`). -/
noncomputable def schurToSred [IsAlgClosed k] [CharZero k] (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    SchurLoc (k := k) (d 0) (d (Fin.last N)) r →ₐ[k] Sred (k := k) d r hp hq :=
  (baseQuotMap (k := k) d r hp hq).comp
    (basePresentationEquiv (k := k) (d 0) (d (Fin.last N)) r hp hq).symm.toAlgHom

/-! ## R2-3b-2 — the `SchurLoc`-algebra structure on `Sred` and the scalar tower

The base→total map `schurToSred` induces (via `RingHom.toAlgebra`) the `SchurLoc q p r`-algebra
structure on `Sred`, with `k → SchurLoc → Sred` a scalar tower. These instances are the
`[Algebra R S]` slot that R2-3a's `e : S ≃ₐ[k] R ⊗_k FibreAlg` consumes (`R = SchurLoc q p r`). -/

/-- **The `SchurLoc`-algebra structure on `Sred`**, induced by the base→total map `schurToSred`
(`RingHom.toAlgebra`). The `R = SchurLoc q p r`-algebra structure R2-3a's product iso `e` needs. -/
@[reducible] noncomputable def sredSchurAlgebra [IsAlgClosed k] [CharZero k] (d : Fin (N + 1) → ℕ)
    (r : ℕ) (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    Algebra (SchurLoc (k := k) (d 0) (d (Fin.last N)) r) (Sred (k := k) d r hp hq) :=
  (schurToSred (k := k) d r hp hq).toRingHom.toAlgebra

/-- The induced `SchurLoc`-algebra structure on `Sred` makes `k → SchurLoc q p r → Sred` a scalar
tower: `algebraMap k Sred` factors through `algebraMap k (SchurLoc …)` (both `schurToSred` and the
localization-quotient maps are `k`-algebra maps). -/
theorem sredSchur_isScalarTower [IsAlgClosed k] [CharZero k] (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    @IsScalarTower k (SchurLoc (k := k) (d 0) (d (Fin.last N)) r) (Sred (k := k) d r hp hq)
      _ (sredSchurAlgebra (k := k) d r hp hq).toSMul _ := by
  letI := sredSchurAlgebra (k := k) d r hp hq
  refine IsScalarTower.of_algebraMap_eq (fun x ↦ ?_)
  -- `algebraMap (SchurLoc …) Sred = schurToSred.toRingHom` (by `toAlgebra`); `schurToSred` is a
  -- `k`-algebra map, so it commutes with `algebraMap k (SchurLoc …)` (`AlgHom.commutes`).
  change algebraMap k (Sred (k := k) d r hp hq) x
      = (schurToSred (k := k) d r hp hq).toRingHom (algebraMap k _ x)
  exact (AlgHom.commutes (schurToSred (k := k) d r hp hq) x).symm

/-! ## R2-3b-3 pre-stage (durable contract, NOT proved here)

The endpoint-normalization `AlgEquiv` for R2-3b-3 is an `aeval`-substitution on the **unquotiented**
`MvPolynomial (RepCoord d) R` over an **arbitrary** coefficient ring `R` (Codex: NOT
`baseChangeAlgEquiv`, which carries `[Infinite k]` from polynomial-function ext). The contract — two
`aeval` substitutions that round-trip on generators, assembled by `AlgEquiv.ofAlgHom` — is pinned
here so R2-3b-3 inherits the exact shape. (`example`: the contract, not the genuine
substitution.) -/

/-- **R2-3b-3 pre-stage contract.** Two coordinate substitutions `toSub`, `fromSub : RepCoord d →
MvPolynomial (RepCoord d) R` over an arbitrary commutative ring `R`, mutually inverse on the
generators, assemble to a coordinate-change `AlgEquiv` of `MvPolynomial (RepCoord d) R` via
`AlgEquiv.ofAlgHom` (each direction an `aeval`; the round-trips by `MvPolynomial.algHom_ext` +
`aeval_X`). The endpoint-normalization substitution of R2-3b-3 instantiates this. -/
noncomputable example {R : Type u} [CommRing R] (d : Fin (N + 1) → ℕ)
    (toSub fromSub : RepCoord d → MvPolynomial (RepCoord d) R)
    (h_to_from : ∀ x, aeval toSub (fromSub x) = (X x : MvPolynomial (RepCoord d) R))
    (h_from_to : ∀ x, aeval fromSub (toSub x) = (X x : MvPolynomial (RepCoord d) R)) :
    MvPolynomial (RepCoord d) R ≃ₐ[R] MvPolynomial (RepCoord d) R :=
  AlgEquiv.ofAlgHom (aeval toSub) (aeval fromSub)
    (by
      apply MvPolynomial.algHom_ext
      intro x
      change aeval toSub (aeval fromSub (X x)) = _
      rw [aeval_X]; exact h_to_from x)
    (by
      apply MvPolynomial.algHom_ext
      intro x
      change aeval fromSub (aeval toSub (X x)) = _
      rw [aeval_X]; exact h_from_to x)

/-! ## Non-vacuity witnesses

The deep constructions fire on the `N = 1` specialization `(d 0, d last) = (q, p)`, where they
reproduce the `N = 1` base data. We exhibit (i) the type bridge at `(2, 2)`, (ii) `deepBaseComap` /
`deepBaseComap_detPivot` at the `N = 1` stratum `dStratum 2 2`, `r = 1`, where the deep pivot minor
**is** the `N = 1` `detPivotPoly` (`deepBaseComap` is the identity-up-to-rename there), and (iii)
the localized base→total quotient map `baseQuotMap` available at that anchor over
`AlgebraicClosure ℚ`. -/

section Witness

/-- The type bridge `RepCoord (dStratum 2 2) ≃ Fin 2 × Fin 2` round-trips on a concrete coordinate
(the `(1, 0)` entry of the single matrix). -/
example : repStratumEquiv 2 2 ⟨0, (⟨1, by norm_num⟩, ⟨0, by norm_num⟩)⟩
    = (⟨1, by norm_num⟩, ⟨0, by norm_num⟩) := rfl

/-- `deepBaseComap` at the `N = 1` stratum `dStratum 2 2` sends `X ⟨0, (a, b)⟩` to the deep generic
product entry `multPoly (dStratum 2 2) a b` — non-vacuous (`N = 1` specialization). -/
example (a : Fin (dStratum 2 2 (Fin.last 1))) (b : Fin (dStratum 2 2 0)) :
    deepBaseComap (k := AlgebraicClosure ℚ) (dStratum 2 2) (X ⟨0, (a, b)⟩)
      = multPoly (dStratum 2 2) a b :=
  deepBaseComap_X _ a b

/-- The pivot-minor transport fires at the `N = 1` stratum `dStratum 2 2`, `r = 1`:
`deepBaseComap (detPivotPoly …) = ΔPdeep …`. -/
example (h : (1 : ℕ) ≤ 2) :
    deepBaseComap (k := AlgebraicClosure ℚ) (dStratum 2 2)
        (detPivotPoly (k := AlgebraicClosure ℚ) (dStratum 2 2 0) (dStratum 2 2 (Fin.last 1)) 1 h h)
      = ΔPdeep (k := AlgebraicClosure ℚ) (dStratum 2 2) 1 h h :=
  deepBaseComap_detPivot (dStratum 2 2) 1 h h

/-- The localized base→total quotient map `baseQuotMap` is available at the `N = 1` anchor
`dStratum 2 2`, `r = 1`, over `AlgebraicClosure ℚ` — non-vacuous. (It needs no `IsAlgClosed` /
`CharZero`; `schurToSred` composes this with `basePresentationEquiv.symm`.) -/
noncomputable example (h : (1 : ℕ) ≤ 2) :
    (Localization.Away
          (detPivotPoly (k := AlgebraicClosure ℚ)
            (dStratum 2 2 0) (dStratum 2 2 (Fin.last 1)) 1 h h)
        ⧸ Iad (k := AlgebraicClosure ℚ) (dStratum 2 2 0) (dStratum 2 2 (Fin.last 1)) 1 h h)
      →ₐ[AlgebraicClosure ℚ] Sred (k := AlgebraicClosure ℚ) (dStratum 2 2) 1 h h :=
  baseQuotMap (dStratum 2 2) 1 h h

/-- `Sred` is reduced at the `N = 1` anchor `dStratum 2 2`, `r = 1`, over `AlgebraicClosure ℚ` — the
name is honest there, and R2-3a's `hSred` is discharged. -/
example (h : (1 : ℕ) ≤ 2) :
    IsReduced (Sred (k := AlgebraicClosure ℚ) (dStratum 2 2) 1 h h) :=
  isReduced_Sred (dStratum 2 2) 1 h h

exec
/bin/bash -lc "sed -n '1,430p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
import DLNFibre.Core.DeterminantalBaseElimination
import DLNFibre.Core.DeterminantalChartRing
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# `DLNFibre.Core.DeterminantalBasePresentation` — the localized base presentation `A_loc/Iad ≅ Sd`

The final identification of `G2-2`: the localized determinantal base ring `A_loc = Localization.Away
detΔ`, modulo its base ideal `Iad`, is the free Schur localization `Sd` (`= Localization.Away
detSchurS`) — a regular ring of dimension `δ`. The eliminated `B22` block (`B22 = B21 Δ⁻¹ B12`) is
forced by the Schur relation once `detΔ` is inverted.

**The route (Codex-vetted, thread-13 `codex-g22c-route` consult).** The localized block equivalence
`Ψ : A_loc ≃ₐ[k] MvPolynomial B22block Sd` (localizing the LANDED `blockAlgEquiv` at `detΔ ↦
C detSchurS`) carries `Iad` to a prime of `MvPolynomial B22block Sd`. The forced-block graph ideal
`J = graphIdeal forcedB22` (the genuine forced value `B21 adjΔ B12 / detΔ ∈ Sd`) satisfies:

1. **`height J = C`** — the translation automorphism maps `J` to the coordinate ideal, whose height
   is `#B22block = C` (LANDED `height_coordIdeal_localization_eq`).
2. **`J ⊆ Ψ(Iad)`** — each generator `X_b − C(forcedB22 b)` is, up to the unit `C detSchurS`, the
   image under `Ψ` of the bordered `(r+1)`-minor (LANDED `det_submatrix_multPoly_mem_sigmaIdeal`),
   which lies in `Iad`. This carries the actual Schur content.
3. **`Iad = J`** — by `Ideal.height_strict_mono_of_is_prime` (both prime, `height Ψ(Iad) = height
   Iad = C = height J`, `J ⊆ Ψ(Iad)` ⟹ no strict containment ⟹ equal). This honestly **earns** the
   hard direction `Iad ⊆ J`.

Then `A_loc/Iad ≅ (MvPolynomial B22block Sd)/J ≅ Sd` via `graphIdealQuotientEquiv`. `J` stays
internal; the domain / dimension `δ` follow from `Sd` being a polynomial localization.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

universe u

variable {k : Type u} [Field k]

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-! ## The localized block equivalence `Ψ`

`Sd := Localization.Away detSchurS`, `Q := MvPolynomial B22block Sd`. We use `Localization` (the
canonical localization) so the `k`-algebra instances on `Sd` and `Q` resolve automatically. -/

/-- The free Schur localization `Sd = Localization.Away detSchurS` — the downstream-composable base
ring (a regular ring of dimension `δ`). -/
abbrev SchurLoc (q p r : ℕ) : Type u :=
  Localization.Away (detSchurS (k := k) q p r)

/-- **The localized block equivalence** `Ψ : A_loc ≃ₐ[k] MvPolynomial B22block Sd`, localizing the
LANDED `blockAlgEquiv` at `detΔ` (which maps to `C detSchurS`). -/
noncomputable def blockAlgEquivLoc (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    Localization.Away (detPivotPoly (k := k) q p r hp hq)
      ≃ₐ[k] MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r) := by
  -- the scalar tower `k → B → Q`
  haveI tower : IsScalarTower k (MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k))
      (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)) := by
    refine IsScalarTower.of_algebraMap_eq (fun x ↦ ?_)
    have hkB : (algebraMap k (MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k))) x
        = C (algebraMap k (MvPolynomial (SchurVar q p r) k) x) := by
      rw [IsScalarTower.algebraMap_apply k (MvPolynomial (SchurVar q p r) k)
        (MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k))]; rfl
    have hkQ : (algebraMap k (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))) x
        = C (algebraMap k (SchurLoc (k := k) q p r) x) := by
      rw [IsScalarTower.algebraMap_apply k (SchurLoc (k := k) q p r)
        (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))]; rfl
    rw [hkB, hkQ, algebraMap_def, MvPolynomial.map_C]
    congr 1
  -- `Q` is the localization of `B` at `powers (C detSchurS)`
  haveI hloc : IsLocalization (Submonoid.powers (C (detSchurS (k := k) q p r) :
      MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k)))
      (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)) := by
    simpa [Submonoid.map_powers] using
      (MvPolynomial.isLocalization (σ := B22block q p r)
        (M := Submonoid.powers (detSchurS (k := k) q p r))
        (S := SchurLoc (k := k) q p r))
  have H : Submonoid.map (blockAlgEquiv (k := k) q p r hp hq)
        (Submonoid.powers (detPivotPoly q p r hp hq))
      = Submonoid.powers (C (detSchurS (k := k) q p r)) := by
    rw [Submonoid.map_powers, blockAlgEquiv_detPivot]
  exact IsLocalization.algEquivOfAlgEquiv
    (Localization.Away (detPivotPoly (k := k) q p r hp hq))
    (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))
    (blockAlgEquiv q p r hp hq) H

/-! ## The bordered `(r+1)`-minor `m_b` and its `blockAlgEquiv` image `(*)`

For a `B22` entry `(a', b')` the bordered `(r+1)×(r+1)` minor `m_b` of the generic product (rows
`[pivots, r+a']`, columns `[pivots, r+b']`) lies in the base ideal (an `(r+1)`-minor), and under
`blockAlgEquiv` becomes `C detSchurS · X (a', b') − C (forcedNum a' b')` (the bordered Schur minor
identity, transported). Dividing by the unit `C detSchurS` lands `X (a', b') − C (forcedB22 …)` in
`Ψ(Iad)`. -/

/-- The four blocks of the bordered minor at the `B22` entry `(a', b')` (entries are coordinate
variables of `multPoly`). Pivot block `Δ`, pivot-row × non-pivot-col `u`, non-pivot-row × pivot-col
`v`, corner `d`. The non-pivot index is the landed reindex form `Fin.cast (natAdd r ·)`. -/
noncomputable def borderΔ (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    Matrix (Fin r) (Fin r) (MvPolynomial (RepCoord (dStratum q p)) k) :=
  Matrix.of fun i j ↦ (Matrix.of (multPoly (dStratum q p))) (Fin.castLE hp i) (Fin.castLE hq j)

noncomputable def borderU (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) (b' : Fin (q - r)) :
    Matrix (Fin r) Unit (MvPolynomial (RepCoord (dStratum q p)) k) :=
  Matrix.of fun i _ ↦ (Matrix.of (multPoly (dStratum q p))) (Fin.castLE hp i)
    (Fin.cast (show r + (q - r) = q by omega) (Fin.natAdd r b'))

noncomputable def borderV (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) (a' : Fin (p - r)) :
    Matrix Unit (Fin r) (MvPolynomial (RepCoord (dStratum q p)) k) :=
  Matrix.of fun _ j ↦ (Matrix.of (multPoly (dStratum q p)))
    (Fin.cast (show r + (p - r) = p by omega) (Fin.natAdd r a')) (Fin.castLE hq j)

noncomputable def borderD (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q)
    (a' : Fin (p - r)) (b' : Fin (q - r)) :
    Matrix Unit Unit (MvPolynomial (RepCoord (dStratum q p)) k) :=
  Matrix.of fun _ _ ↦ (Matrix.of (multPoly (dStratum q p)))
    (Fin.cast (show r + (p - r) = p by omega) (Fin.natAdd r a'))
    (Fin.cast (show r + (q - r) = q by omega) (Fin.natAdd r b'))

/-- The `SchurVar`-side pivot block `ΔS` (whose determinant is `detSchurS`). -/
noncomputable def schurΔ (q p r : ℕ) : Matrix (Fin r) (Fin r) (MvPolynomial (SchurVar q p r) k) :=
  Matrix.of fun i j ↦ X (Sum.inl (i, j))

/-- The `SchurVar`-side `B12` column `uS` at non-pivot column `b'` (the `b'`-th column of `B12`). -/
noncomputable def schurU (q p r : ℕ) (b' : Fin (q - r)) :
    Matrix (Fin r) Unit (MvPolynomial (SchurVar q p r) k) :=
  Matrix.of fun i _ ↦ X (Sum.inr (Sum.inl (i, b')))

/-- The `SchurVar`-side `B21` row `vS` at non-pivot row `a'` (the `a'`-th row of `B21`). -/
noncomputable def schurV (q p r : ℕ) (a' : Fin (p - r)) :
    Matrix Unit (Fin r) (MvPolynomial (SchurVar q p r) k) :=
  Matrix.of fun _ j ↦ X (Sum.inr (Sum.inr (a', j)))

/-- The bordered minor `m_b`: the determinant of the `multPoly` submatrix on rows `[pivots, r+a']`
and columns `[pivots, r+b']`. -/
noncomputable def borderMinor (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q)
    (a' : Fin (p - r)) (b' : Fin (q - r)) : MvPolynomial (RepCoord (dStratum q p)) k :=
  ((Matrix.of (multPoly (dStratum q p))).submatrix
    (Sum.elim (fun i : Fin r ↦ Fin.castLE hp i)
      (fun _ : Unit ↦ Fin.cast (show r + (p - r) = p by omega) (Fin.natAdd r a')))
    (Sum.elim (fun j : Fin r ↦ Fin.castLE hq j)
      (fun _ : Unit ↦ Fin.cast (show r + (q - r) = q by omega) (Fin.natAdd r b')))).det

/-- The bordered minor is the determinant of `fromBlocks borderΔ borderU borderV borderD`. -/
theorem borderMinor_eq_fromBlocks (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q)
    (a' : Fin (p - r)) (b' : Fin (q - r)) :
    borderMinor (k := k) q p r hp hq a' b'
      = (Matrix.fromBlocks (borderΔ (k := k) q p r hp hq) (borderU q p r hp hq b')
          (borderV q p r hp hq a') (borderD q p r hp hq a' b')).det := by
  rw [borderMinor]
  congr 1
  refine Matrix.ext (fun i j ↦ ?_)
  cases i <;> cases j <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.submatrix_apply, Sum.elim_inl, Sum.elim_inr,
      borderΔ, borderU, borderV, borderD, Matrix.of_apply]

/-- **The bordered minor lies in the base ideal `sigmaIdeal`** (it is an `(r+1)`-minor of the
product, `det_submatrix_multPoly_mem_sigmaIdeal` after the `Fin r ⊕ Unit ≃ Fin (r+1)` reindex). -/
theorem borderMinor_mem_sigmaIdeal (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q)
    (a' : Fin (p - r)) (b' : Fin (q - r)) :
    borderMinor (k := k) q p r hp hq a' b' ∈ sigmaIdeal (k := k) (dStratum q p) r := by
  rw [borderMinor]
  set e : (Fin r ⊕ Unit) ≃ Fin (r + 1) :=
    (Equiv.sumCongr (Equiv.refl (Fin r)) finOneEquiv.symm).trans finSumFinEquiv with he
  rw [← det_submatrix_equiv_self e.symm, submatrix_submatrix]
  exact det_submatrix_multPoly_mem_sigmaIdeal (dStratum q p) _ _

/-- Each bordered block maps under `blockAlgEquiv` to the `C`-image of its `SchurVar`-side block
landed coordinate-image lemmas), or to the `B22` corner variable. -/
theorem blockAlgEquiv_borderΔ (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    (borderΔ (k := k) q p r hp hq).map (blockAlgEquiv (k := k) q p r hp hq)
      = (schurΔ (k := k) q p r).map C := by
  refine Matrix.ext (fun i j ↦ ?_)
  rw [Matrix.map_apply, Matrix.map_apply, borderΔ, Matrix.of_apply, multPoly_stratum_apply,
    schurΔ, Matrix.of_apply]
  exact blockAlgEquiv_X_pivot q p r hp hq i j

theorem blockAlgEquiv_borderU (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) (b' : Fin (q - r)) :
    (borderU (k := k) q p r hp hq b').map (blockAlgEquiv (k := k) q p r hp hq)
      = (schurU (k := k) q p r b').map C := by
  refine Matrix.ext (fun i u ↦ ?_)
  rw [Matrix.map_apply, Matrix.map_apply, borderU, Matrix.of_apply, multPoly_stratum_apply,
    schurU, Matrix.of_apply]
  exact blockAlgEquiv_X_b12 q p r hp hq i b'

theorem blockAlgEquiv_borderV (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) (a' : Fin (p - r)) :
    (borderV (k := k) q p r hp hq a').map (blockAlgEquiv (k := k) q p r hp hq)
      = (schurV (k := k) q p r a').map C := by
  refine Matrix.ext (fun u j ↦ ?_)
  rw [Matrix.map_apply, Matrix.map_apply, borderV, Matrix.of_apply, multPoly_stratum_apply,
    schurV, Matrix.of_apply]
  exact blockAlgEquiv_X_b21 q p r hp hq a' j

theorem blockAlgEquiv_borderD (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q)
    (a' : Fin (p - r)) (b' : Fin (q - r)) :
    (borderD (k := k) q p r hp hq a' b').map (blockAlgEquiv (k := k) q p r hp hq)
      = Matrix.of fun _ _ : Unit ↦ (X (a', b') : MvPolynomial (B22block q p r)
          (MvPolynomial (SchurVar q p r) k)) := by
  refine Matrix.ext (fun u v ↦ ?_)
  rw [Matrix.map_apply, borderD, Matrix.of_apply, multPoly_stratum_apply, Matrix.of_apply]
  exact blockAlgEquiv_X_b22 q p r hp hq a' b'

/-- The numerator bridge: the bordered Schur numerator (row `a'` of `B21`, `adjugate Δ`, column `b'`
of `B12`) is the `(a', b')` entry of the full `forcedNum = B21 · adjugate Δ · B12`. -/
theorem schurNum_eq_forcedNum (q p r : ℕ) (a' : Fin (p - r)) (b' : Fin (q - r)) :
    (schurV (k := k) q p r a' * (schurΔ (k := k) q p r).adjugate * schurU (k := k) q p r b')
        default default
      = (forcedNum (k := k) q p r) a' b' := by
  rw [forcedNum, schurΔ, schurU, schurV]
  simp [Matrix.mul_apply]

/-- **`(*)` the bordered Schur minor identity, transported.** `blockAlgEquiv (m_b) =
C detSchurS · X (a', b') − C (forcedNum a' b')`. Via `AlgEquiv.map_det` + `Matrix.fromBlocks_map` +
`det_fromBlocks_scalar_eq` on the mapped (`SchurVar`-`C`) blocks; `det (ΔS.map C) = C detSchurS`,
the numerator collapses to `C (forcedNum a' b')` (`schurNum_eq_forcedNum`). -/
theorem blockAlgEquiv_borderMinor (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q)
    (a' : Fin (p - r)) (b' : Fin (q - r)) :
    blockAlgEquiv (k := k) q p r hp hq (borderMinor q p r hp hq a' b')
      = C (detSchurS (k := k) q p r) * X (a', b') - C ((forcedNum (k := k) q p r) a' b') := by
  rw [borderMinor_eq_fromBlocks, AlgEquiv.map_det, AlgEquiv.mapMatrix_apply,
    Matrix.fromBlocks_map, blockAlgEquiv_borderΔ, blockAlgEquiv_borderU, blockAlgEquiv_borderV,
    blockAlgEquiv_borderD, det_fromBlocks_scalar_eq, Matrix.of_apply,
    show ((schurΔ (k := k) q p r).map C).det = C (detSchurS (k := k) q p r) from
      (RingHom.map_det C (schurΔ (k := k) q p r)).symm,
    show ((schurΔ (k := k) q p r).map C).adjugate = ((schurΔ (k := k) q p r).adjugate).map C from
      (RingHom.map_adjugate _ _).symm,
    ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply, schurNum_eq_forcedNum, mul_comm]

/-! ## Step (2): `J ⊆ Ψ(Iad)` — the localized inclusion

`Ψ` carries `algebraMap A_eng A_loc x` to `algebraMap B Q (blockAlgEquiv x)`
(`algEquivOfAlgEquiv_eq`). Each generator `X (a',b') − C (forcedB22 (a',b'))` of `J`, multiplied by
the unit `C (algebraMap detSchurS)`, is the `Ψ`-image of the bordered minor (in `Iad`), so it
`Ψ(Iad)`; dividing by the unit gives the generator. -/

/-- `Ψ` intertwines the two localization maps: `Ψ (algebraMap A_eng A_loc x) = algebraMap B Q
(blockAlgEquiv x)`. (`Ψ = IsLocalization.algEquivOfAlgEquiv blockAlgEquiv`.) -/
theorem blockAlgEquivLoc_algebraMap (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q)
    (x : MvPolynomial (RepCoord (dStratum q p)) k) :
    blockAlgEquivLoc (k := k) q p r hp hq
        (algebraMap (MvPolynomial (RepCoord (dStratum q p)) k)
          (Localization.Away (detPivotPoly (k := k) q p r hp hq)) x)
      = algebraMap (MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k))
          (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))
          (blockAlgEquiv (k := k) q p r hp hq x) := by
  haveI tower : IsScalarTower k (MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k))
      (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)) := by
    refine IsScalarTower.of_algebraMap_eq (fun y ↦ ?_)
    have hkB : (algebraMap k (MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k))) y
        = C (algebraMap k (MvPolynomial (SchurVar q p r) k) y) := by
      rw [IsScalarTower.algebraMap_apply k (MvPolynomial (SchurVar q p r) k)
        (MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k))]; rfl
    have hkQ : (algebraMap k (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))) y
        = C (algebraMap k (SchurLoc (k := k) q p r) y) := by
      rw [IsScalarTower.algebraMap_apply k (SchurLoc (k := k) q p r)
        (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))]; rfl
    rw [hkB, hkQ, algebraMap_def, MvPolynomial.map_C]; congr 1
  haveI hloc : IsLocalization (Submonoid.powers (C (detSchurS (k := k) q p r) :
      MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k)))
      (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)) := by
    simpa [Submonoid.map_powers] using
      (MvPolynomial.isLocalization (σ := B22block q p r)
        (M := Submonoid.powers (detSchurS (k := k) q p r)) (S := SchurLoc (k := k) q p r))
  exact IsLocalization.algEquivOfAlgEquiv_eq _ x

/-- The localized base ideal `Iad = (sigmaIdeal …).map (algebraMap A_eng A_loc)`: the determinantal
base ideal pushed into the localized base ring `A_loc = Localization.Away detΔ`. -/
noncomputable def Iad (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    Ideal (Localization.Away (detPivotPoly (k := k) q p r hp hq)) :=
  (sigmaIdeal (dStratum q p) r).map
    (algebraMap (MvPolynomial (RepCoord (dStratum q p)) k)
      (Localization.Away (detPivotPoly (k := k) q p r hp hq)))

/-- **The cleared Schur relation in `Q = MvPolynomial B22block Sd`.** The unit `C (algebraMap
detSchurS)` times the graph generator `X (a',b') − C (forcedB22 (a',b'))` equals
`Ψ (algebraMap A_eng A_loc (borderMinor …))` — the `Ψ`-image of a bordered minor (hence in
`Ψ(Iad)`). The `mk'` denominator clears: `algebraMap detSchurS · forcedB22 = algebraMap
forcedNum`. -/
theorem unit_mul_graphGen_eq_psi_borderMinor (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q)
    (a' : Fin (p - r)) (b' : Fin (q - r)) :
    C (algebraMap (MvPolynomial (SchurVar q p r) k) (SchurLoc (k := k) q p r)
          (detSchurS (k := k) q p r))
        * (X (a', b') - C (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r) (a', b')))
      = blockAlgEquivLoc (k := k) q p r hp hq
          (algebraMap (MvPolynomial (RepCoord (dStratum q p)) k)
            (Localization.Away (detPivotPoly (k := k) q p r hp hq))
            (borderMinor q p r hp hq a' b')) := by
  rw [blockAlgEquivLoc_algebraMap, blockAlgEquiv_borderMinor, map_sub, map_mul]
  simp only [algebraMap_def, MvPolynomial.map_C, MvPolynomial.map_X]
  rw [mul_sub]
  congr 1
  rw [← C_mul]
  congr 1
  rw [forcedB22,
    IsLocalization.mk'_spec' (SchurLoc (k := k) q p r) ((forcedNum (k := k) q p r) a' b')
      (⟨detSchurS q p r, Submonoid.mem_powers _⟩ : Submonoid.powers (detSchurS (k := k) q p r))]

/-- **Step (2): `J ⊆ Ψ(Iad)`.** Each generator `X (a',b') − C (forcedB22 (a',b'))` of the forced
graph ideal lies in `Ψ(Iad)`: it is the unit `C (algebraMap detSchurS)⁻¹` times the `Ψ`-image of the
bordered minor (which is in `Iad`, `borderMinor_mem_sigmaIdeal`). -/
theorem graphIdeal_forcedB22_le_map_Iad (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r))
      ≤ ((Iad (k := k) q p r hp hq)).map (blockAlgEquivLoc (k := k) q p r hp hq) := by
  rw [graphIdeal, Ideal.span_le]
  rintro _ ⟨ab, rfl⟩
  obtain ⟨a', b'⟩ := ab
  show X (a', b') - C (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r) (a', b'))
      ∈ ((Iad (k := k) q p r hp hq)).map (blockAlgEquivLoc (k := k) q p r hp hq)
  -- the generator × the unit `C (algebraMap detSchurS)` is `Ψ (algebraMap borderMinor) ∈ Ψ(Iad)`
  have hunit : IsUnit (C (algebraMap (MvPolynomial (SchurVar q p r) k) (SchurLoc (k := k) q p r)
      (detSchurS (k := k) q p r)) : MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)) :=
    (IsLocalization.Away.algebraMap_isUnit (detSchurS (k := k) q p r)).map
      (C : SchurLoc (k := k) q p r →+* _)
  rw [← Ideal.unit_mul_mem_iff_mem _ hunit, unit_mul_graphGen_eq_psi_borderMinor q p r hp hq a' b']
  exact Ideal.mem_map_of_mem _
    (Ideal.mem_map_of_mem _ (borderMinor_mem_sigmaIdeal q p r hp hq a' b'))

/-! ## Step (3): the height squeeze `Iad = J` and the presentation `A_loc/Iad ≅ Sd`

Both `Ψ(Iad)` and `J = graphIdeal forcedB22` are prime of height `C`, and `J ⊆ Ψ(Iad)`
(step 2). `Ideal.height_strict_mono_of_is_prime` rules out `J ⊊ Ψ(Iad)`, so `J = Ψ(Iad)` — this
**earns** the hard direction `Iad ⊆ Ψ.symm J` (= injectivity). The presentation `A_loc/Iad ≅ Sd`
then follows from `graphIdealQuotientEquiv`. -/

/-- **`Ψ(Iad) = J`** (`[IsAlgClosed k] [CharZero k]`): the height squeeze. Both ideals are prime;
landed `height Iad = C` (transported by `Ψ`) and `height J = C` are equal; `J ⊆ Ψ(Iad)` (step 2)
plus `height_strict_mono_of_is_prime` forces equality. This is the honest hard direction. -/
theorem map_Iad_eq_graphIdeal_forcedB22 [IsAlgClosed k] [CharZero k] (q p r : ℕ)
    (hp : r ≤ p) (hq : r ≤ q) :
    ((Iad (k := k) q p r hp hq)).map (blockAlgEquivLoc (k := k) q p r hp hq)
      = graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r)) := by
  set Q := MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)
  set K : Ideal Q :=
    ((Iad (k := k) q p r hp hq)).map (blockAlgEquivLoc (k := k) q p r hp hq) with hK
  set J : Ideal Q := graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r)) with hJ
  -- both ideals are prime
  haveI hsigmaPrime : (sigmaIdeal (k := k) (dStratum q p) r).IsPrime := by
    rw [sigmaIdeal]; exact isPrime_vanishingIdeal_productRankLocusLE_stratum q p r hq hp
  haveI hIadPrime : ((Iad (k := k) q p r hp hq)).IsPrime := by
    have hdisj := (Ideal.disjoint_powers_iff_notMem
        (detPivotPoly (k := k) q p r hp hq) hsigmaPrime.isRadical).2
      (detPivotPoly_notMem_sigmaIdeal q p r hp hq)
    exact IsLocalization.isPrime_of_isPrime_disjoint
      (S := Localization.Away (detPivotPoly (k := k) q p r hp hq))
      (Submonoid.powers (detPivotPoly q p r hp hq))
      (sigmaIdeal (dStratum q p) r) hsigmaPrime hdisj
  haveI hKprime : K.IsPrime := Ideal.map_isPrime_of_equiv (blockAlgEquivLoc (k := k) q p r hp hq)
  haveI : IsDomain (SchurLoc (k := k) q p r) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (SchurLoc (k := k) q p r)
      (powers_le_nonZeroDivisors_of_noZeroDivisors (detSchurS_ne_zero (k := k) q p r))
  haveI hJprime : J.IsPrime := graphIdeal_isPrime _
  -- `height K = height Iad` (Ψ an equiv); `height Iad = C` (landed); `height J = C` (landed)
  have hKIad : K.height = ((Iad (k := k) q p r hp hq)).height :=
    height_map_algEquiv (blockAlgEquivLoc (k := k) q p r hp hq) ((Iad (k := k) q p r hp hq))
  have hIadC : ((Iad (k := k) q p r hp hq)).height = ((q - r) * (p - r) : ℕ) := by
    rw [Iad, height_map_sigmaIdeal_away_eq_cCodim q p r hp hq
        (kostantPartitions_stratum_nonempty q p r hq hp), cCodim_stratum_eq q p r hq hp
        (kostantPartitions_stratum_nonempty q p r hq hp), Int.toNat_natCast]
  have hheightJ : J.height = ((p - r) * (q - r) : ℕ) :=
    height_graphIdeal_forcedB22_eq q p r (SchurLoc (k := k) q p r)
  have hJK : J.height = K.height := by
    rw [hheightJ, hKIad, hIadC, Nat.mul_comm]
  -- the squeeze: `J ⊆ K`, equal finite heights, both prime ⟹ `J = K`
  refine (eq_of_le_of_not_lt (graphIdeal_forcedB22_le_map_Iad q p r hp hq) (fun hlt ↦ ?_)).symm
  haveI : J.FiniteHeight := by
    rw [Ideal.finiteHeight_iff]; right; rw [hheightJ]; exact ENat.coe_ne_top _
  exact absurd ((Ideal.height_strict_mono_of_is_prime hlt).trans_le hJK.ge)
    (lt_irrefl _)

/-- **The localized base presentation `A_loc / Iad ≅ₐ[k] Sd`** (`G2-2`). The localized determinantal
base ring `A_loc = Localization.Away detΔ`, modulo its base ideal `Iad = (sigmaIdeal …).map …`, is
the free Schur localization `Sd = Localization.Away detSchurS` — a regular ring of dimension `δ`.
Via the height squeeze `Ψ(Iad) = J` (`map_Iad_eq_graphIdeal_forcedB22`) and the graph-ideal quotient
`Q ⧸ J ≅ Sd` (`graphIdealQuotientEquiv`, the `B22`-block elimination). -/
noncomputable def basePresentationEquiv [IsAlgClosed k] [CharZero k] (q p r : ℕ)
    (hp : r ≤ p) (hq : r ≤ q) :
    (Localization.Away (detPivotPoly (k := k) q p r hp hq) ⧸ (Iad (k := k) q p r hp hq))
      ≃ₐ[k] SchurLoc (k := k) q p r := by
  have e₁ : (Localization.Away (detPivotPoly (k := k) q p r hp hq) ⧸ (Iad (k := k) q p r hp hq))
      ≃ₐ[k] (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)
        ⧸ graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r))) :=
    Ideal.quotientEquivAlg ((Iad (k := k) q p r hp hq))
      (graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r)))
      (blockAlgEquivLoc (k := k) q p r hp hq)
      (map_Iad_eq_graphIdeal_forcedB22 q p r hp hq).symm
  have e₂ : (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)
        ⧸ graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r)))
      ≃ₐ[k] SchurLoc (k := k) q p r :=
    (graphIdealQuotientEquiv (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r))).restrictScalars k
  exact e₁.trans e₂

/-! ## Non-vacuity witness — `(q, p, r) = (2, 2, 1)`

The `2 × 2` rank-`≤ 1` determinantal base: `#B22block = (2−1)(2−1) = 1 = C` eliminated coordinate,
`#SchurVar = 1·(2 + 2 − 1) = 3 = δ` free coordinates. The presentation exhibits `A_loc/Iad` as the
free Schur localization `Sd` (a regular ring of dimension `δ = 3`). -/

/-- **Witness (`2 × 2`, `r = 1`).** `#B22block = 1 = C` (one eliminated `B22` coordinate),
`#SchurVar = 3 = δ` (three free Schur coordinates). -/
example : Nat.card (B22block 2 2 1) = 1 ∧ Nat.card (SchurVar 2 2 1) = 3 := by
  refine ⟨?_, ?_⟩
  · rw [card_B22block]
  · rw [card_SchurVar 2 2 1 (by norm_num) (by norm_num)]

/-- The presentation equivalence is available at `(2, 2, 1)` for any algebraically closed field of
characteristic `0` — non-vacuous. -/
noncomputable example [IsAlgClosed k] [CharZero k]
    (h : (1 : ℕ) ≤ 2) :
    (Localization.Away (detPivotPoly (k := k) 2 2 1 h h) ⧸ Iad (k := k) 2 2 1 h h)
      ≃ₐ[k] SchurLoc (k := k) 2 2 1 :=
  basePresentationEquiv 2 2 1 h h

end DLNFibre.Core

codex
There is already a ring-level pivot chart presentation for the base (`A_loc/Iad ≃ SchurLoc`) and the deep chart ring (`Sred`). That suggests the lowest-friction Lean path is likely not to introduce a general category of regular maps, but to express the trivialization directly as an `AlgEquiv` between localized quotient coordinate rings.
exec
/bin/bash -lc "sed -n '1,280p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
import DLNFibre.Core.MultComorphism
import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# `DLNFibre.Core.FibreReducedTrivialization` — route-(b) reducedness via the trivialization

The route-(b) reducedness chain of `G2-3` (thread 17, R2-3), wired against the **trivialization** of
the rank-`r` chart as a hypothesis. The certified pen-and-paper input (thread 16) is that the fibre
ideal `I_E = (mult(Ã) − E)` is **radical** (`F_E = k[Ã]/I_E` **reduced**), for every `N ≥ 1`, every
dimension vector, every target (it depends only on `rank E`). The MECHANISM is that reducedness is
**inherited** from the reduced ambient rank-locus chart `Sred` via the **faithfully-flat product
trivialization** `S ≅ₐ[k] R ⊗_k F_E` (endpoint normalization), then **descends** to `F_E` over the
field `k`.

This module supplies, sorry-free and unconditionally, the **two ends of that chain** plus the
**closer that consumes it**, leaving the single open rung — the deep product trivialization `e`
itself, together with the reducedness `IsReduced S` of the chart ring — as an explicit
**hypothesis**, not an asserted fact:

1. **`isReduced_of_tensor`** — the tensor-with-a-field reducedness **descent** `F` reduced ⟸
   `R ⊗_k F` reduced (over a field `k`, any nontrivial `k`-algebra `R`). The "one open dependency"
   the thread-16 certificate flagged; here it is the direct `includeRight` injection
   (`Algebra.TensorProduct.includeRight_injective` + `isReduced_of_injective`), **not** the
   geometric `IsGeometricallyReduced` (which descends in the opposite direction).

2. **`fibreGenIdeal_isRadical_of_trivialization`** — the full route-(b) chain: given the
   trivialization `e : S ≃ₐ[k] R ⊗_k FibreAlg d B` and `IsReduced S` (the reduced chart ring),
   `R ⊗_k F_E` is reduced (transfer along `e`), hence `F_E` is reduced (descent (1)), hence
   `fibreGenIdeal d B` is **radical** (`Ideal.isRadical_iff_quotient_reduced`).

3. **`vanishingIdeal_fibre_eq_fibreGenIdeal_of_trivialization`** — the **radical-collapse** of
   `MultComorphism` point 4: with the cut ideal radical, `vanishingIdeal (fibre d B) =
   radical (fibreGenIdeal d B) = fibreGenIdeal d B` — the `radical (·)` wrapper drops. This is the
   identity the height-squeeze (R2-5/R2-6, `height m_B = δ`) consumes.

**What is Proved vs Assumed here.** Everything above is proved sorry-free *given* the trivialization
`e : S ≃ₐ[k] R ⊗_k F_B` and `IsReduced S`, which are carried as **explicit hypotheses** — never as a
`sorry` or a global axiom. The deep trivialization `e` itself (the endpoint-normalization product
iso, built from a deep localized chart ring `S = O(Σ̄^r ∩ chart)`) is **not** constructed here: it
is the **open residual `G2-3` wall, R2-3b** (new scheme-free affine scaffolding — no deep localized
total ring exists in the engine yet, G2-2's machinery is `N = 1` only; ~5–8 modules). No downstream
result may claim `codim (fibre) = C + δ` or discharge `BundleShiftInterface` on the strength of
these conditional theorems while `e` is a hypothesis — that discharge waits for R2-3b to prove `e`.
The theorems here are an honest, clearly-labelled *conditional* pre-build of the downstream: every
consumer of `e` is **already proved against the hypothesis**, so R2-3b closes the chain with no
further reducedness work. (Codex's recommended build order for `e` is recorded in the thread's
`codex/algequiv-answer.md`.)

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial
open scoped TensorProduct

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## The fibre coordinate algebra `F_E` -/

/-- The **fibre coordinate algebra** `F_B = k[Ã] / (mult(Ã) − B)`: the coordinate ring of the cut
scheme `mult⁻¹(B)`, i.e. `MvPolynomial (RepCoord d) k` modulo the fibre generator ideal. (`F_E` in
the certificate is this at the rank normal form `B = E`; the construction is uniform in `B`.) -/
abbrev FibreAlg (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) : Type u :=
  MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d B

/-- `fibreGenIdeal d B` is radical **iff** `F_B` is reduced — the engine restatement of
`Ideal.isRadical_iff_quotient_reduced` for the fibre algebra. The bridge route-(b) crosses (the
geometric reducedness of `F_B` is exactly the radical-collapse the height-squeeze wants). -/
theorem fibreGenIdeal_isRadical_iff_isReduced_fibreAlg (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) :
    (fibreGenIdeal d B).IsRadical ↔ IsReduced (FibreAlg d B) :=
  Ideal.isRadical_iff_quotient_reduced (fibreGenIdeal d B)

/-! ## The tensor-with-a-field reducedness descent (the pinned dependency)

`F` reduced ⟸ `R ⊗_k F` reduced over a field `k`. Direct via the **injection**
`includeRight : F →ₐ[k] R ⊗_k F` (a nonzero `k`-algebra `R` makes `algebraMap k R` injective, and
`F` is `k`-flat as a vector space, so `includeRight` is injective by
`Algebra.TensorProduct.includeRight_injective`), then `isReduced_of_injective`. This is the standard
char-0 descent the certificate named — but it needs only a field base and a nontrivial `R`. -/

/-- **Tensor-with-a-field reducedness descent.** Over a field `k`, for any nontrivial commutative
`k`-algebra `R` and commutative `k`-algebra `F`: if `R ⊗_k F` is reduced then `F` is reduced. The
injection `F ↪ R ⊗_k F` (`includeRight`, injective since `F` is `k`-flat and `algebraMap k R` is
injective) pulls back reducedness. -/
theorem isReduced_of_tensor {R F : Type u} [CommRing R] [Nontrivial R] [CommRing F]
    [Algebra k R] [Algebra k F] (h : IsReduced (R ⊗[k] F)) : IsReduced F :=
  letI := h
  isReduced_of_injective
    (Algebra.TensorProduct.includeRight : F →ₐ[k] R ⊗[k] F)
    (Algebra.TensorProduct.includeRight_injective (algebraMap k R).injective)

/-! ## The route-(b) chain through the trivialization (the open rung as a hypothesis) -/

/-- **Route (b): `fibreGenIdeal` radical, through the trivialization.** Given the chart
trivialization `e : S ≃ₐ[k] R ⊗_k F_B` (the endpoint-normalization product iso) and that the chart
ring `S` is **reduced** (the engine's `Sred = (MvPol / sigmaIdeal)[1/ΔP]` is reduced, `sigmaIdeal`
a `vanishingIdeal`), the fibre ideal `fibreGenIdeal d B` is **radical**. The certified mechanism:
`S` reduced ⟹ `R ⊗_k F_B` reduced (transfer along `e.symm`) ⟹ `F_B` reduced (`isReduced_of_tensor`)
⟹ `fibreGenIdeal d B` radical. `[Nontrivial R]` (`R = SchurLoc` is a domain). -/
theorem fibreGenIdeal_isRadical_of_trivialization
    (d : Fin (N + 1) → ℕ) (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k)
    (R S : Type u) [CommRing R] [Nontrivial R] [CommRing S]
    [Algebra k R] [Algebra k S]
    (e : S ≃ₐ[k] R ⊗[k] FibreAlg d B) (hSred : IsReduced S) :
    (fibreGenIdeal d B).IsRadical := by
  letI := hSred
  -- `S` reduced ⟹ `R ⊗ F_B` reduced (it injects into `S` via `e.symm`)
  have hRF : IsReduced (R ⊗[k] FibreAlg d B) :=
    isReduced_of_injective e.symm.toRingEquiv e.symm.injective
  -- ⟹ `F_B` reduced (tensor-with-a-field descent) ⟹ `fibreGenIdeal` radical
  exact (fibreGenIdeal_isRadical_iff_isReduced_fibreAlg d B).mpr (isReduced_of_tensor (R := R) hRF)

/-- **The radical-collapse of `MultComorphism` point 4** (through the trivialization). With the cut
ideal radical (`fibreGenIdeal_isRadical_of_trivialization`), the engine's
`vanishingIdeal (fibre d B) = radical (fibreGenIdeal d B)` collapses to
`vanishingIdeal (fibre d B) = fibreGenIdeal d B`: the `radical (·)` wrapper drops. The clean
identity the height-squeeze (`height m_B = δ`, R2-5/R2-6) consumes. `[IsAlgClosed k]` (the
Nullstellensatz bridge). -/
theorem vanishingIdeal_fibre_eq_fibreGenIdeal_of_trivialization [IsAlgClosed k]
    (d : Fin (N + 1) → ℕ) (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k)
    (R S : Type u) [CommRing R] [Nontrivial R] [CommRing S]
    [Algebra k R] [Algebra k S]
    (e : S ≃ₐ[k] R ⊗[k] FibreAlg d B) (hSred : IsReduced S) :
    vanishingIdeal k (canonicalCoord d '' fibre d B) = fibreGenIdeal d B := by
  rw [vanishingIdeal_image_fibre_eq_radical,
    (fibreGenIdeal_isRadical_of_trivialization d B R S e hSred).radical]

/-! ## Non-vacuity witnesses

The descent (1) is non-vacuous over any field. The chain (2)/(3) is non-vacuous with `S := R ⊗ F_B`
and the identity equiv `e := AlgEquiv.refl` — exhibiting that the hypotheses are jointly satisfiable
(a reduced `S` admitting the iso), so the conclusions are not vacuously
derived from contradictory hypotheses. -/

section Witness

/-- The tensor-descent fires over `ℚ` (a field) for `R = ℚ`, `F = ℚ`: `ℚ ⊗_ℚ ℚ` reduced ⟹ `ℚ`
reduced — non-vacuous. -/
example (h : IsReduced (ℚ ⊗[ℚ] ℚ)) : IsReduced ℚ := isReduced_of_tensor (k := ℚ) h

/-- The chain's hypotheses are jointly satisfiable: with `S := R ⊗_k F_B`, `R` a nontrivial reduced
domain and `F_B` reduced, the identity equiv `e := AlgEquiv.refl` and `IsReduced S` discharge the
hypotheses of `fibreGenIdeal_isRadical_of_trivialization` — so the theorem is not vacuous. (Here the
content is the *shape* of the contract; the genuine `e` for the rank chart is the deferred rung.) -/
example [IsAlgClosed k] (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) (R : Type u) [CommRing R] [Nontrivial R]
    [Algebra k R] [IsReduced (R ⊗[k] FibreAlg d B)] :
    (fibreGenIdeal d B).IsRadical :=
  fibreGenIdeal_isRadical_of_trivialization d B R (R ⊗[k] FibreAlg d B)
    (AlgEquiv.refl) ‹_›

end Witness

end DLNFibre.Core

exec
/bin/bash -lc 'rg -n "FibreAlg|fibreGenIdeal|BundleShift|Sred|tensor|TensorProduct|height.*ringKrullDim|codim.*varietyDim|Route|fibration|relative" -S /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
exec
/bin/bash -lc 'rg -n "Regular|IsRegular|regular|AlgEquiv.*quotient|varietyDim.*AlgEquiv|varietyDim.*equiv|ringKrullDim.*AlgEquiv|ringKrullDim.*RingEquiv|product.*varietyDim|finite.*union.*varietyDim|iUnion.*varietyDim|Product|Prod" -S /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry | head -n 300' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:91:-- and fibreGenIdeal = Ideal.map multComap (maxIdealOfPoint B) — the fibre-ring quotient F2 consumes.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:123:-- Route-(b) reducedness chain for G2-3 (R2-3a): the tensor-with-a-field reducedness descent (PROVED),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:125:-- the open R2-3b wall) — `fibreGenIdeal` radical + the radical-collapse of MultComorphism pt4. The
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:126:-- final BundleShiftInterface discharge WAITS for R2-3b to prove `e`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:128:-- Deep chart ring (R2-3b-1+2, the residual G2-3 wall foundation): `Sred = Localization.Away(ΔPdeep) ⧸
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:130:-- bridges, and the localized base→total map `schurToSred : SchurLoc → Sred` giving Sred its
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:131:-- SchurLoc-algebra structure (R2-3a's R = SchurLoc, S = Sred). The crux containments (det transport,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:140:-- = height I, no hypotheses) + `codimRepCanonical_fibre_eq_height_fibreGenIdeal` (codim of the fibre =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:154:-- Route-c sweep structure (homogeneous sweep): `Σ^r = H·F` (`productRankLocus_eq_iUnion_smul_fibre`)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:159:-- Reducible-locus catenary: `height I + ringKrullDim(R⧸I) = card` for ANY proper I (no radicality), and
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:160:-- `codimRepCanonical Z + varietyDim Z = card` for nonempty Z. Discharges the catenary hyps of RouteCAssembly.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:165:-- Route-c assembly (conditional bank): `codimRepCanonical(fibre d B) = C + δ` for rank-r B, carrying ONLY
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:168:import DLNFibre.Core.RouteCAssembly
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:172:-- stone for the finite-type-ALGEBRA case (EGA IV 6.9.1, the positive-relative-dim case the fibre needs).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimZeroStrict.lean:13:The route (Route B): reuse the four shortest-split moves and their `codimForm_*_le` ("≤ 0") sign
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:15:The catenary dimension formula `Ideal.height p + ringKrullDim (R ⧸ p) = n` for `R = MvPolynomial
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:17:(`height_add_ringKrullDim_quotient_eq`, "L5"). Here we:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:28:   transport lemmas (`height_map_algEquiv`, `ringKrullDim_quotient_map_algEquiv`):
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:29:   `height_add_ringKrullDim_quotient_eq_card`, `ringKrullDim (MvPolynomial σ k) = Nat.card σ`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:112:`MvPolynomial σ k` (`σ` finite, `k` any field), `height p + ringKrullDim (R ⧸ p) = Nat.card σ`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:113:Transported from the `Fin (card σ)` headline `height_add_ringKrullDim_quotient_eq` (L5) through the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:115:theorem height_add_ringKrullDim_quotient_eq_card [Finite σ] (p : Ideal (MvPolynomial σ k))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:117:    (p.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial σ k ⧸ p) = (Nat.card σ : WithBot ℕ∞) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:128:  have key := height_add_ringKrullDim_quotient_eq k (Fintype.card σ) q
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:150:  have key := height_add_ringKrullDim_quotient_eq_card (vanishingIdeal k Z)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:183:theorem codimRep_add_varietyDim_eq_card [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:186:    codimRep coord Z + varietyDim (coord '' Z) = (Nat.card (RepCoord d) : ℕ∞) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:192:theorem codimRep_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:195:    codimRep coord Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (coord '' Z) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:199:`canonicalCoord d`, `codimRepCanonical Z = Nat.card (RepCoord d) − varietyDim (canonicalCoord d ''
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:201:theorem codimRepCanonical_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:205:    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:206:  codimRep_eq_card_sub_varietyDim (canonicalCoord d) Z hp
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:15:Route: the conormal sequence of the surjection `R ↠ A` (`kerCotangentToTensor k R A`), base-changed to
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:19:identifying `m_A.Cotangent ≅ k ⊗_A Ω[A⁄k]`; and `Ideal.tensorCotangentEquiv` (flat localization)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:38:import Mathlib.LinearAlgebra.TensorProduct.RightExactness
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:39:import Mathlib.LinearAlgebra.TensorProduct.Tower
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:41:open TensorProduct KaehlerDifferential Module IsLocalRing Matrix
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:86:    TensorProduct.mk A (Localization.AtPrime p) p.Cotangent 1
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:96:    (p.map (Algebra.TensorProduct.includeRight.toRingHom :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:101:  set e : T ⊗[A] A ≃ₐ[T] T := Algebra.TensorProduct.rid A T T
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:102:  have hfwd : (p.map (Algebra.TensorProduct.includeRight.toRingHom : A →+* T ⊗[A] A)) ≤
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:107:    rw [show e (Algebra.TensorProduct.includeRight.toRingHom x) = algebraMap A T x from by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:108:      simp [e, Algebra.TensorProduct.rid_tmul, Algebra.smul_def]]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:111:      (p.map (Algebra.TensorProduct.includeRight.toRingHom : A →+* T ⊗[A] A)).comap
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:116:    rw [show e.symm (algebraMap A T x) = Algebra.TensorProduct.includeRight.toRingHom x from by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:117:      apply e.injective; simp [e, Algebra.TensorProduct.rid_tmul, Algebra.smul_def]]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:137:    (Ideal.tensorCotangentEquiv A T p).trans (cotangentTensorRidEquiv p)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:271:range (kerCotangentToTensor)` of `B ⊗[R] Ω[R⁄k]`, tensored by `k ⊗[B] -` and restricted to `k`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:272:theorem tensorKaehler_equiv_quotient_conormal
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:328:theorem finrank_tensor_kaehler_eq_coker (hg : ∀ i, MvPolynomial.eval a (g i) = 0) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:341:  obtain ⟨eExact⟩ := tensorKaehler_equiv_quotient_conormal (k := k)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:446:  rw [hmA, ← finrank_tensor_kaehler_eq_coker g a hg]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:454:equals that of `CotangentSpace (Localization.AtPrime m_A)` via `Ideal.tensorCotangentEquiv` (flat
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitPullbackDim.lean:46:/-- **Route-c first link, ideal form.** The variety dimension of the rank locus `Z_M =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitPullbackDim.lean:67:/-- **Route-c first link, headline.** The variety dimension of the rank locus `Z_M =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:5:# `DLNFibre.Core.DeepChartRing` — the deep chart ring `Sred` + the localized base→total map
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:12:vector `d : Fin (N + 1) → ℕ`, the deep localized chart ring `Sred` of the rank-`≤ r` product locus
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:13:on the pivot chart, and the localized base→total `k`-algebra map that gives `Sred` its
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:23:3. `Sred d r hp hq := Localization.Away (ΔPdeep …) ⧸ IadDeep …` — the deep chart quotient ring, with
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:24:   its `CommRing` / `Algebra k` instances inherited, and `isReduced_Sred` : `IsReduced (Sred …)`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:25:   (over `[IsAlgClosed k]`, justifying the name — this is R2-3a's `hSred`, now discharged).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:40:   fibreGenIdeal`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:41:7. `baseLocMap` / `schurToSred` — the localized base map `Localization.Away detPivotPoly →ₐ[k]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:44:   `SchurLoc q p r →ₐ[k] Sred d r hp hq`. The resulting `SchurLoc`-algebra structure on `Sred`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:45:   (`RingHom.toAlgebra`) + the `IsScalarTower k (SchurLoc …) (Sred …)` instance.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:47:**Scope (what is NOT here).** The full product iso `e : Sred ≃ₐ[k] SchurLoc ⊗_k FibreAlg`, the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:50:`BundleShiftInterface` — `e` is not yet built. (R2-3a's *other* hypothesis, `IsReduced S`, **is**
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:51:discharged here: `isReduced_Sred`, so R2-3b-4 needs only `e` itself.) The R2-3b-3
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:102:/-! ## R2-3b-1 — the deep chart ring `Sred` -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:121:/-- **The deep chart ring** `Sred d r := Localization.Away (ΔPdeep …) ⧸ IadDeep …`: the localized
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:124:noncomputable abbrev Sred (d : Fin (N + 1) → ℕ) (r : ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:128:/-! ## R2-3b-1 — `Sred` is reduced (justifying the name; discharges R2-3a's `hSred`)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:130:The name `Sred` asserts reducedness, and that reducedness is precisely R2-3a's second hypothesis
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:131:`hSred : IsReduced S` (`Core.FibreReducedTrivialization.fibreGenIdeal_isRadical_of_trivialization`).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:151:/-- **`Sred` is reduced** (`[IsAlgClosed k]`), justifying the name.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:152:`Sred = Localization.Away ΔPdeep ⧸ IadDeep` with `IadDeep` radical (`IadDeep_isRadical`); a quotient
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:154:(`Ideal.isRadical_iff_quotient_reduced`). This is exactly R2-3a's `hSred : IsReduced S` for
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:155:`S = Sred` — so R2-3b-4 needs to build only `e` itself, not also `IsReduced S`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:156:theorem isReduced_Sred [IsAlgClosed k] (d : Fin (N + 1) → ℕ) (r : ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:158:    IsReduced (Sred (k := k) d r hp hq) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:229:Does **not** assume the circular `sigmaIdeal ≤ fibreGenIdeal`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:246:/-! ## R2-3b-2 — the localized base map and the `SchurLoc`-algebra structure on `Sred`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:305:Sred d r`: the quotient lift of `baseLocMap` (`Ideal.quotientMapₐ`, the ideal hypothesis from
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:311:      →ₐ[k] Sred (k := k) d r hp hq :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:315:/-- **The base→total `k`-algebra map** `SchurLoc q p r →ₐ[k] Sred d r` (`q = d 0`, `p = d last`):
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:317:algebra structure makes `Sred` a `SchurLoc`-algebra (the `R = SchurLoc`-algebra structure that
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:319:noncomputable def schurToSred [IsAlgClosed k] [CharZero k] (d : Fin (N + 1) → ℕ) (r : ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:321:    SchurLoc (k := k) (d 0) (d (Fin.last N)) r →ₐ[k] Sred (k := k) d r hp hq :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:325:/-! ## R2-3b-2 — the `SchurLoc`-algebra structure on `Sred` and the scalar tower
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:327:The base→total map `schurToSred` induces (via `RingHom.toAlgebra`) the `SchurLoc q p r`-algebra
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:328:structure on `Sred`, with `k → SchurLoc → Sred` a scalar tower. These instances are the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:329:`[Algebra R S]` slot that R2-3a's `e : S ≃ₐ[k] R ⊗_k FibreAlg` consumes (`R = SchurLoc q p r`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:331:/-- **The `SchurLoc`-algebra structure on `Sred`**, induced by the base→total map `schurToSred`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:335:    Algebra (SchurLoc (k := k) (d 0) (d (Fin.last N)) r) (Sred (k := k) d r hp hq) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:336:  (schurToSred (k := k) d r hp hq).toRingHom.toAlgebra
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:338:/-- The induced `SchurLoc`-algebra structure on `Sred` makes `k → SchurLoc q p r → Sred` a scalar
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:339:tower: `algebraMap k Sred` factors through `algebraMap k (SchurLoc …)` (both `schurToSred` and the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:343:    @IsScalarTower k (SchurLoc (k := k) (d 0) (d (Fin.last N)) r) (Sred (k := k) d r hp hq)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:347:  -- `algebraMap (SchurLoc …) Sred = schurToSred.toRingHom` (by `toAlgebra`); `schurToSred` is a
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:349:  change algebraMap k (Sred (k := k) d r hp hq) x
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:350:      = (schurToSred (k := k) d r hp hq).toRingHom (algebraMap k _ x)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:351:  exact (AlgHom.commutes (schurToSred (k := k) d r hp hq) x).symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:417:`CharZero`; `schurToSred` composes this with `basePresentationEquiv.symm`.) -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:423:      →ₐ[AlgebraicClosure ℚ] Sred (k := AlgebraicClosure ℚ) (dStratum 2 2) 1 h h :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:426:/-- `Sred` is reduced at the `N = 1` anchor `dStratum 2 2`, `r = 1`, over `AlgebraicClosure ℚ` — the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:427:name is honest there, and R2-3a's `hSred` is discharged. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:429:    IsReduced (Sred (k := AlgebraicClosure ℚ) (dStratum 2 2) 1 h h) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:430:  isReduced_Sred (dStratum 2 2) 1 h h
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodim.lean:28:**Cited** (`DLN.BundleShiftInterface.cited_bundle_shift`) until that build lands.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodim.lean:79:shift `+ r(d_0+d_N−r)` — is **Cited** (`DLN.BundleShiftInterface.cited_bundle_shift`); it needs the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/QSeriesDurfee.lean:13:`P` is the LANDED inverse-q-Pochhammer of `Core.QSeries`. The proof is Route B (thread 06,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FlatQuasiFiniteHeight.lean:9:quasi-finite, so heights are preserved along an étale map, reducing `ringKrullDim` of a local ring
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartFlatnessProbe.lean:5:import Mathlib.RingTheory.TensorProduct.Free
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartFlatnessProbe.lean:36:open scoped TensorProduct
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartFlatnessProbe.lean:95:the `Algebra.TensorProduct.instFree` lever the corrected Schur trivialization closes on. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibrationProbe.lean:43:/-- LANDED: H1 retarget — `codim(fibre B) = height(fibreGenIdeal B)`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibrationProbe.lean:46:    codimRepCanonical (fibre d B) = (fibreGenIdeal d B).height :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibrationProbe.lean:47:  codimRepCanonical_fibre_eq_height_fibreGenIdeal d B
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibrationProbe.lean:55:/-- LANDED: the catenary closer (PRIMALITY-gated) — `codim Z = card − varietyDim Z`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibrationProbe.lean:59:    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibrationProbe.lean:60:  codimRepCanonical_eq_card_sub_varietyDim Z hp
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibrationProbe.lean:65:    (p.height : WithBot ℕ∞) + ringKrullDim (((MvPolynomial (Fin n) k) ⧸ I) ⧸ p)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibrationProbe.lean:67:  affine_domain_height_add_ringKrullDim_quotient_eq k n I p
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibrationProbe.lean:72:    (m.height : WithBot ℕ∞) = ringKrullDim ((MvPolynomial (Fin n) k) ⧸ I) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibrationProbe.lean:73:  height_eq_ringKrullDim_of_isMaximal k n I m
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:11:`fibreGenIdeal d B` (`Core.MultComorphism.vanishingIdeal_image_fibre_eq_radical`). The point of this
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:16:So `codimRepCanonical (fibre d B) = (fibreGenIdeal d B).height` — **unconditionally** (no radicality
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:17:of `fibreGenIdeal` needed). This decouples the codimension from the scheme-structure / cut-ideal
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:19:never depends on whether `fibreGenIdeal` is its own radical.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:45:ideal `fibreGenIdeal d B = span {multPoly d r c − C (B r c)}`. The chain:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:47:(definition of `codimRepCanonical`/`codimRep`); `vanishingIdeal (…) = (fibreGenIdeal d B).radical`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:49:(`Ideal.height_radical`). The codimension does **not** depend on whether `fibreGenIdeal` is
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:51:theorem codimRepCanonical_fibre_eq_height_fibreGenIdeal [IsAlgClosed k] (d : Fin (N + 1) → ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:53:    codimRepCanonical (fibre d B) = (fibreGenIdeal d B).height := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:61:height of the explicit fibre generator ideal — `codimRepCanonical_fibre_eq_height_fibreGenIdeal` is
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:64:    codimRepCanonical (fibre dWitness B) = (fibreGenIdeal dWitness B).height :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:65:  codimRepCanonical_fibre_eq_height_fibreGenIdeal dWitness B
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:335:`Ideal.height p + ringKrullDim (R ⧸ p) = n`. The catenary identity for affine space — `R` is
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:337:theorem height_add_ringKrullDim_quotient_eq
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:339:    (p.height : WithBot ℕ∞) + ringKrullDim ((MvPolynomial (Fin n) k) ⧸ p)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:353:  exact height_add_ringKrullDim_quotient_eq k n p
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:362:  have := height_add_ringKrullDim_quotient_eq ℚ 2 ⊥
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:379:  have h := height_add_ringKrullDim_quotient_eq ℚ 2 p
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:9:The prime catenary `height p + ringKrullDim (R ⧸ p) = card` (`Core.NullstellensatzCodim`,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:10:`height_add_ringKrullDim_quotient_eq_card`) extended to an **arbitrary proper** ideal `I ≠ ⊤` of a
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:13:> `height I + ringKrullDim (R ⧸ I) = Nat.card σ`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:27:The headline specialises to `codimRepCanonical Z + varietyDim Z = card` for any **nonempty**
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:29:discharging the reducible-locus catenary that `Core.RouteCAssembly` carries as the named hypotheses
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:78:`p`, and the chain's length is `≤ coheight p = ringKrullDim (R ⧸ p)`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:115:proper ideal `I ≠ ⊤`, `height I + ringKrullDim (R ⧸ I) = Nat.card σ` — the per-prime catenary
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:118:theorem height_add_ringKrullDim_quotient_eq_card_of_ne_top [Finite σ]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:120:    (I.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial σ k ⧸ I) = (Nat.card σ : WithBot ℕ∞) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:125:      (p.height : WithBot ℕ∞) + ringKrullDim (R ⧸ p) = n := fun p hp ↦
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:126:    height_add_ringKrullDim_quotient_eq_card (k := k) (σ := σ) p
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:139:    calc (I.height : WithBot ℕ∞) + ringKrullDim (R ⧸ I)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:140:        ≤ (p.height : WithBot ℕ∞) + ringKrullDim (R ⧸ p) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:153:    calc n = (I.height : WithBot ℕ∞) + ringKrullDim (R ⧸ p₀) := this.symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:154:      _ ≤ (I.height : WithBot ℕ∞) + ringKrullDim (R ⧸ I) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:157:/-! ## Specialisation to the geometry layer (`codimRepCanonical Z + varietyDim Z = card`) -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:173:/-- **The reducible-locus catenary at `codimRepCanonical`/`varietyDim` (additive, `ℕ∞`).** For a
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:176:equal the ambient dimension: `codimRepCanonical Z + varietyDim (canonicalCoord d '' Z) = card`. No
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:179:theorem codimRepCanonical_add_varietyDim_eq_card_of_nonempty {d : Fin (N + 1) → ℕ}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:181:    codimRepCanonical Z + varietyDim (canonicalCoord d '' Z)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:186:  have key := height_add_ringKrullDim_quotient_eq_card_of_ne_top
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:197:  rw [codimRepCanonical, codimRep, varietyDim, ← hm, WithBot.unbotD_coe]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:203:The reducible-locus catenary at `codimRepCanonical`/`varietyDim` fires on the whole space `univ`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:211:  codimRepCanonical_add_varietyDim_eq_card_of_nonempty
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:54:`m.height = ringKrullDim A`. Transported from the `Fin (card σ)` headline
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:55:`height_eq_ringKrullDim_of_isMaximal` (L4d) through the `renameEquiv` coordinate relabelling and the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:57:theorem height_eq_ringKrullDim_of_isMaximal_fintype {σ : Type*} [Finite σ]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:59:    (m.height : WithBot ℕ∞) = ringKrullDim (MvPolynomial σ k ⧸ I) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:76:  have hL4d := height_eq_ringKrullDim_of_isMaximal k (Fintype.card σ) J m'
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:79:    height_map_algEquiv Φ m, hJ, ringKrullDim_quotient_map_algEquiv e I] at hL4d
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:86:and the equidimensionality `height_eq_ringKrullDim_of_isMaximal_fintype`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:92:  exact height_eq_ringKrullDim_of_isMaximal_fintype I m
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean:36:`Core.NoetherMonicPositioning` (`height_add_ringKrullDim_quotient_eq`), which imports this module
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Barcode.lean:102:/-- **The splitting fact, relative to an ambient pair `(P, Q)`** (recursion-ready form). If `f`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GenericFreeness.lean:17:to the going-down/relative-dimension machinery.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GenericFreeness.lean:28:for a finitely-generated `R`-*algebra* `B` (relative dimension possibly positive, e.g. `B = R[X]`)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GenericFreeness.lean:88:the relative fibre-dimension rung consumes (flat ⟹ going-down on the dense open `r ≠ 0`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:15:The proof is **homogeneity + Route DENSE** (thread 34/18): the `G_d`-action acts on `Z_M` with a
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:301:/-! ## L3.3 — the orbit's closed points are dense in `Spec A` (Route DENSE)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:313:/-- **The vanishing ideal of the orbit closed points is `⊥`** (Route DENSE core, a rewrite of L6's
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:3:the local Krull dimension equals the local relative dimension (the rank of Kähler differentials
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:7:there is a basic-open chart `S = A[1/f]` (`f ∉ m`) on which `A` is standard smooth of some relative
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:16:  (L5 `height_add_ringKrullDim_quotient_eq`);
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:43:/-! ### The relative-dimension rank of a standard-smooth chart -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:54:/-- A standard-smooth chart is standard smooth of the relative dimension `finrank S Ω[S⁄k]`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:101:  have hL5 := height_add_ringKrullDim_quotient_eq k n (q.comap g)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:109:(`f ∉ m`) on which `A` is standard smooth of relative dimension `n := finrank S Ω[S⁄k]`, with
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:135:  -- Step C: the relative dimension `n := finrank S Ω`, with `rank Ω = n` and the chart standard
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:136:  -- smooth of relative dimension `n`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:157:  -- Step B: transport the height down `A → S`, then read `ringKrullDim (AtPrime m) = m.height`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:189:`A = MvPolynomial (Fin 1) ℚ` (smooth at `m`), there is a chart of relative dimension `n` with
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:21:`Core.NullstellensatzCodim` (the field catenary `height_add_ringKrullDim_quotient_eq_card`).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:70:  have hcat := height_add_ringKrullDim_quotient_eq_card (k := k) (σ := σ ⊕ τ) J₀
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:71:  rw [hheight, hdim, ringKrullDim_quotient_graphIdeal_eq c, Nat.card_sum] at hcat
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:4:import Mathlib.LinearAlgebra.TensorProduct.Tower
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:7:import Mathlib.LinearAlgebra.TensorProduct.RightExactness
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:119:    rw [LinearMap.range_eq_top, LinearMap.baseChange_eq_ltensor]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:123:    rw [LinearMap.baseChange_eq_ltensor]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FlatTrivialProductProbe.lean:6:import Mathlib.LinearAlgebra.TensorProduct.Basis
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FlatTrivialProductProbe.lean:34:open scoped TensorProduct
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FlatTrivialProductProbe.lean:38:/-! ## Free ⟹ flat, and the polynomial / tensor trivial-product shapes -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:13:**inherited** from the reduced ambient rank-locus chart `Sred` via the **faithfully-flat product
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:22:1. **`isReduced_of_tensor`** — the tensor-with-a-field reducedness **descent** `F` reduced ⟸
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:25:   (`Algebra.TensorProduct.includeRight_injective` + `isReduced_of_injective`), **not** the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:28:2. **`fibreGenIdeal_isRadical_of_trivialization`** — the full route-(b) chain: given the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:29:   trivialization `e : S ≃ₐ[k] R ⊗_k FibreAlg d B` and `IsReduced S` (the reduced chart ring),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:31:   `fibreGenIdeal d B` is **radical** (`Ideal.isRadical_iff_quotient_reduced`).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:33:3. **`vanishingIdeal_fibre_eq_fibreGenIdeal_of_trivialization`** — the **radical-collapse** of
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:35:   radical (fibreGenIdeal d B) = fibreGenIdeal d B` — the `radical (·)` wrapper drops. This is the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:44:result may claim `codim (fibre) = C + δ` or discharge `BundleShiftInterface` on the strength of
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:57:open scoped TensorProduct
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:68:abbrev FibreAlg (d : Fin (N + 1) → ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:70:  MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d B
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:72:/-- `fibreGenIdeal d B` is radical **iff** `F_B` is reduced — the engine restatement of
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:75:theorem fibreGenIdeal_isRadical_iff_isReduced_fibreAlg (d : Fin (N + 1) → ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:77:    (fibreGenIdeal d B).IsRadical ↔ IsReduced (FibreAlg d B) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:78:  Ideal.isRadical_iff_quotient_reduced (fibreGenIdeal d B)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:80:/-! ## The tensor-with-a-field reducedness descent (the pinned dependency)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:85:`Algebra.TensorProduct.includeRight_injective`), then `isReduced_of_injective`. This is the standard
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:92:theorem isReduced_of_tensor {R F : Type u} [CommRing R] [Nontrivial R] [CommRing F]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:96:    (Algebra.TensorProduct.includeRight : F →ₐ[k] R ⊗[k] F)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:97:    (Algebra.TensorProduct.includeRight_injective (algebraMap k R).injective)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:101:/-- **Route (b): `fibreGenIdeal` radical, through the trivialization.** Given the chart
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:103:ring `S` is **reduced** (the engine's `Sred = (MvPol / sigmaIdeal)[1/ΔP]` is reduced, `sigmaIdeal`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:104:a `vanishingIdeal`), the fibre ideal `fibreGenIdeal d B` is **radical**. The certified mechanism:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:105:`S` reduced ⟹ `R ⊗_k F_B` reduced (transfer along `e.symm`) ⟹ `F_B` reduced (`isReduced_of_tensor`)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:106:⟹ `fibreGenIdeal d B` radical. `[Nontrivial R]` (`R = SchurLoc` is a domain). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:107:theorem fibreGenIdeal_isRadical_of_trivialization
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:111:    (e : S ≃ₐ[k] R ⊗[k] FibreAlg d B) (hSred : IsReduced S) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:112:    (fibreGenIdeal d B).IsRadical := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:113:  letI := hSred
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:115:  have hRF : IsReduced (R ⊗[k] FibreAlg d B) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:117:  -- ⟹ `F_B` reduced (tensor-with-a-field descent) ⟹ `fibreGenIdeal` radical
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:118:  exact (fibreGenIdeal_isRadical_iff_isReduced_fibreAlg d B).mpr (isReduced_of_tensor (R := R) hRF)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:121:ideal radical (`fibreGenIdeal_isRadical_of_trivialization`), the engine's
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:122:`vanishingIdeal (fibre d B) = radical (fibreGenIdeal d B)` collapses to
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:123:`vanishingIdeal (fibre d B) = fibreGenIdeal d B`: the `radical (·)` wrapper drops. The clean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:126:theorem vanishingIdeal_fibre_eq_fibreGenIdeal_of_trivialization [IsAlgClosed k]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:130:    (e : S ≃ₐ[k] R ⊗[k] FibreAlg d B) (hSred : IsReduced S) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:131:    vanishingIdeal k (canonicalCoord d '' fibre d B) = fibreGenIdeal d B := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:133:    (fibreGenIdeal_isRadical_of_trivialization d B R S e hSred).radical]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:144:/-- The tensor-descent fires over `ℚ` (a field) for `R = ℚ`, `F = ℚ`: `ℚ ⊗_ℚ ℚ` reduced ⟹ `ℚ`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:146:example (h : IsReduced (ℚ ⊗[ℚ] ℚ)) : IsReduced ℚ := isReduced_of_tensor (k := ℚ) h
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:150:hypotheses of `fibreGenIdeal_isRadical_of_trivialization` — so the theorem is not vacuous. (Here the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:154:    [Algebra k R] [IsReduced (R ⊗[k] FibreAlg d B)] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:155:    (fibreGenIdeal d B).IsRadical :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:156:  fibreGenIdeal_isRadical_of_trivialization d B R (R ⊗[k] FibreAlg d B)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalStratumDim.lean:29:4. **The catenary bridge** (LANDED `codimRep_add_varietyDim_eq_card`): `codim + dim = card = m·n`,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalStratumDim.lean:237:  have hbridge := codimRep_add_varietyDim_eq_card (canonicalCoord (dStratum n m)) Z
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:10:`codimRepCanonical (fibre d B) = Ideal.height (fibreGenIdeal d B)` (H1, radical-insensitive), and
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:18:* `hge : ∀ J ∈ (fibreGenIdeal d B).minimalPrimes, v ≤ J.height` — every component has codim `≥ v`;
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:19:* `hle : ∃ J ∈ (fibreGenIdeal d B).minimalPrimes, J.height ≤ v` — one (top) component has codim `≤ v`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:62:per-component height bounds on `fibreGenIdeal d B` — every minimal prime `height ≥ v`, one `≤ v` — the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:64:height (fibreGenIdeal d B)`) and the min-over-components closer. The route-B tide discharges `hge`/`hle`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:68:    (hge : ∀ J ∈ (fibreGenIdeal d B).minimalPrimes, v ≤ J.height)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:69:    (hle : ∃ J ∈ (fibreGenIdeal d B).minimalPrimes, J.height ≤ v) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:71:  rw [codimRepCanonical_fibre_eq_height_fibreGenIdeal]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:72:  exact height_eq_of_minimalPrimes_bounds (fibreGenIdeal d B) v hge hle
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:77:target `B` over an algebraically closed field, given that every minimal prime of `fibreGenIdeal d B`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:85:    (hge : ∀ J ∈ (fibreGenIdeal d B).minimalPrimes,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:87:    (hle : ∃ J ∈ (fibreGenIdeal d B).minimalPrimes,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:108:    (hge : ∀ J ∈ (fibreGenIdeal d Bstar).minimalPrimes, v ≤ J.height)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:109:    (hle : ∃ J ∈ (fibreGenIdeal d Bstar).minimalPrimes, J.height ≤ v) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:12:the multiplication-map fibre `mult⁻¹(E)` over a rank-`r` normal form `E`, via the fibration
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:40:The base of the fibration is the rank-`≤ r` determinantal variety in the target matrices
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:82:By equidimensionality at a closed point (`OrbitTangentCotangent.height_eq_ringKrullDim_of_isMaximal_fintype`,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:101:  rw [height_eq_ringKrullDim_of_isMaximal_fintype,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:106:`affine_domain_height_add_ringKrullDim_quotient_eq` is over `MvPolynomial (Fin n) k`. Transport it to
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:108:`height_eq_ringKrullDim_of_isMaximal_fintype` does for the maximal corollary. This is the engine the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:114:`height p + ringKrullDim (A ⧸ p) = ringKrullDim A`. Transports
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:115:`affine_domain_height_add_ringKrullDim_quotient_eq` through `renameEquiv` and the induced quotient
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:117:theorem affine_domain_height_add_ringKrullDim_quotient_eq_fintype {σ : Type*} [Finite σ]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:119:    (p.height : WithBot ℕ∞) + ringKrullDim ((MvPolynomial σ k ⧸ I) ⧸ p)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:133:  have hL := affine_domain_height_add_ringKrullDim_quotient_eq k (Fintype.card σ) J p'
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreJacobian.lean:21:* **`fibreGen`** — the generator family; `span (range (fibreGen d B)) = fibreGenIdeal d B`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreJacobian.lean:62:/-- The span of the fibre generators is the fibre generator ideal `fibreGenIdeal d B`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreJacobian.lean:65:    Ideal.span (Set.range (fibreGen d B)) = fibreGenIdeal d B := rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreJacobian.lean:113:localisation of `fibreGenIdeal d B` (`span (range (fibreGen d B)) = fibreGenIdeal d B`) at `A`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:27:4. **`vanishingIdeal(fibre) = radical(fibreGenIdeal)`** — over `[IsAlgClosed k]`, the engine's
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:29:   radical of `fibreGenIdeal d B = span {multPoly d r c − C (B r c)}`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:31:   `fibreGenIdeal d B = Ideal.map (multComap d) (maxIdealOfPoint B)`: the fibre generator-ideal is
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:153:noncomputable def fibreGenIdeal (d : Fin (N + 1) → ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:159:vanishing ideal of the fibre's image as the radical of `fibreGenIdeal d B`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:162:    vanishingIdeal k (canonicalCoord d '' (fibre d B)) = (fibreGenIdeal d B).radical := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:163:  rw [image_fibre_eq_zeroLocus, fibreGenIdeal,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:188:`fibreGenIdeal d B = Ideal.map (multComap d) (maxIdealOfPoint d B)`: the fibre coordinate ring is
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:190:theorem fibreGenIdeal_eq_map_maxIdealOfPoint (d : Fin (N + 1) → ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:192:    fibreGenIdeal d B = Ideal.map (multComap d).toRingHom (maxIdealOfPoint d B) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:193:  rw [maxIdealOfPoint, Ideal.map_span, fibreGenIdeal, fibreGenSet]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CThetaThetaBridge.lean:142:`d`, the Kostant-side component count `numTop d 0` equals `θ = C(m, |δ|)` (`cTheta d`). Routes
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineNoetherRank.lean:9:Route-c second link: for the finitely-generated `k`-domain `Aimg = (orbitPullback M).range`,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:32:import Mathlib.RingTheory.TensorProduct.Finite
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:41:open Algebra IsLocalRing TensorProduct
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:57:/-! ### The local relative-dimension rank at a smooth point -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:59:/-- On the standard-smooth chart `S = A[1/f]`, `Ω[S⁄k]` is free of finite rank equal to the relative
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:72:field, the cotangent space `m/m²` has `κ(m)`-dimension at most the local relative dimension `n`: the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:123:/-- The local relative dimension at a smooth point: `Ω[Localization.AtPrime m⁄k]` is free of rank
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:197:relative dimension `n = ringKrullDim (AtPrime m)`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:16:through `vanishingIdeal` (radical by construction) and never needs `fibreGenIdeal` to be radical.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:36:presentation may hand it the generator ideal `fibreGenIdeal`, equal only up to radical). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VoigtDischarge.lean:64:    have hadd := codimRep_add_varietyDim_eq_card (canonicalCoord d) (orbitRankLocus M)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:7:# `DLNFibre.Core.RouteCAssembly` — route-c assembly `codim(fibre d B) = C + δ` (conditional bank)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:20:relations `codimRepCanonical Z + varietyDim Z = card` are carried as named hypotheses
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:41:/-- **Route-c assembly: `codim(fibre d B) = C + δ` (conditional bank).** For a rank-`r` target `B`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:83:        = codimRepCanonical (fibre d B) + varietyDim (canonicalCoord d '' fibre d B) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:96:/-- **Route-c assembly with the catenary hypotheses discharged.** For a rank-`r` target `B`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:100:`codimRepCanonical_add_varietyDim_eq_card_of_nonempty` (`Core.RadicalCatenary`), given that the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:115:    (codimRepCanonical_add_varietyDim_eq_card_of_nonempty hFne)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:116:    (codimRepCanonical_add_varietyDim_eq_card_of_nonempty hSigmaNe)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:16:`height_add_ringKrullDim_quotient_eq` (L5, `Core.NoetherMonicPositioning`) to a finite-type domain
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:19:* `affine_domain_height_add_ringKrullDim_quotient_eq` :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:20:    `Ideal.height p + ringKrullDim (A ⧸ p) = ringKrullDim A`  (equidimensionality).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:22:* `height_eq_ringKrullDim_of_isMaximal` : for `m` maximal, `Ideal.height m = ringKrullDim A`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:29:## Route — Noether normalization + integral height transport (reusing L5, no catenary re-induction)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:110:`Ideal.height p + ringKrullDim (A ⧸ p) = ringKrullDim A`. Proved by Noether-normalizing `A`,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:113:theorem affine_domain_height_add_ringKrullDim_quotient_eq
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:116:    (p.height : WithBot ℕ∞) + ringKrullDim (((MvPolynomial (Fin n) k) ⧸ I) ⧸ p)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:149:  have hL5 : (q.height : WithBot ℕ∞) + ringKrullDim (B ⧸ q) = (s : WithBot ℕ∞) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:150:    height_add_ringKrullDim_quotient_eq k s q
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:157:`m` a maximal ideal of `A`, `Ideal.height m = ringKrullDim A` (`A ⧸ m` a field, dimension `0`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:158:theorem height_eq_ringKrullDim_of_isMaximal
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:161:    (m.height : WithBot ℕ∞) = ringKrullDim ((MvPolynomial (Fin n) k) ⧸ I) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:165:  have h := affine_domain_height_add_ringKrullDim_quotient_eq k n I m
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:178:  exact height_eq_ringKrullDim_of_isMaximal k n I m
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:197:  affine_domain_height_add_ringKrullDim_quotient_eq ℚ 1 ⊥ ⊥

 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Pullbacks.lean:563:      (Equiv.sigmaEquivProd _ _).symm fun _ => Iso.refl _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Pullbacks.lean:598:      ((Equiv.prodPUnit 𝒰.I₀).symm.trans (Equiv.sigmaEquivProd 𝒰.I₀ PUnit).symm) fun _ => Iso.refl _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Pullbacks.lean:718:open TensorProduct Algebra.TensorProduct CommRingCat RingHomClass
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Pullbacks.lean:789:  simp [Algebra.TensorProduct.algebraMap_def]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Pullbacks.lean:810:      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S).toRingHom) ≫
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Pullbacks.lean:814:  · congr 1; ext x; change x = Algebra.TensorProduct.lmul' R (S := S) (x ⊗ₜ[R] 1); simp
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Pullbacks.lean:815:  · congr 1; ext x; change x = Algebra.TensorProduct.lmul' R (S := S) (1 ⊗ₜ[R] x); simp
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/PullbackCarrier.lean:31:open CategoryTheory Limits TopologicalSpace IsLocalRing TensorProduct
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Normalization.lean:591:open TensorProduct in
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Normalization.lean:616:  let e₀ := (CommRingCat.isPushout_tensorProduct ..).flip.isoPushout ≪≫
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Normalization.lean:621:        change (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ e₀.hom) r =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Normalization.lean:627:    e.mapIntegralClosure.toAlgHom.comp (TensorProduct.toIntegralClosure _ _ _)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Normalization.lean:629:    TensorProduct.toIntegralClosure_bijective_of_smooth
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Normalization.lean:635:    (CommRingCat.isPushout_tensorProduct ..).flip.isoPushout.inv ≫
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Normalization.lean:664:      trans (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫ e₀.hom) x
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Properties.lean:262:    (X.sheaf.isProductOfDisjoint ⟨_, hS.1⟩ ⟨_, hT.1⟩ ?_).conePointUniqueUpToIso
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Length.lean:218:    rw [(LinearEquiv.piOptionEquivProd _).length_eq, Module.length_prod, IH, add_comm,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EffectiveEpi.lean:23:* `isRegularEpi_of_flat_of_surjective_of_isAffine`: The map `π : X ⟶ Y` is a regular epimorphism
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EffectiveEpi.lean:68:  obtain ⟨u, hu⟩ := IsRegularEpi.exists_of_isKernelPair
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EffectiveEpi.lean:87:    apply IsRegularEpi.exists_of_isKernelPair _ (IsPullback.of_hasPullback _ _)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EffectiveEpi.lean:116:regular epimorphism in the category of schemes. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EffectiveEpi.lean:118:lemma isRegularEpi_of_flat_of_surjective_of_isAffine
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EffectiveEpi.lean:120:    IsRegularEpi π := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/FormallyUnramified.lean:38:    IsOpenImmersion (Spec.map (CommRingCat.ofHom (TensorProduct.lmul' R (S := S)).toRingHom)) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/FormallyUnramified.lean:97:  let F := (Algebra.TensorProduct.lmul' R (S := S)).toRingHom
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean:77:open scoped TensorProduct in
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Separated.lean:11:public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Separated.lean:109:    (Algebra.TensorProduct.lmul'_apply_tmul (R := R) (S := S) 1 x).trans (one_mul x)⟩
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Descent.lean:37:open TensorProduct CategoryTheory Limits
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Descent.lean:114:  refine hQQ'.algebraMap_tensorProduct (R := R) (S := T) (T := S) _ (H₁ h) ?_
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Finite.lean:10:public import Mathlib.RingTheory.Finiteness.Prod
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/PiTopology.lean:15:/-! # Product topology on power series
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/PiTopology.lean:187:section Prod
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/PiTopology.lean:214:end Prod
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/PiTopology.lean:216:section ProdOneSubPow
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/PiTopology.lean:236:end ProdOneSubPow
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/UniversallyOpen.lean:170:  convert_to topologically _ (Spec.map <| CommRingCat.ofHom (algebraMap R (TensorProduct K R S)))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/UniversallyOpen.lean:173:  exact PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/QuasiSeparated.lean:387:    use (X.sheaf.objSupIsoProdEqLocus S U.1).inv ⟨⟨_ * _, _ * _⟩, this⟩
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/QuasiSeparated.lean:388:    refine (X.sheaf.objSupIsoProdEqLocus_inv_eq_iff _ _ _ (X.basicOpen_res _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean:241:open TensorProduct in
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean:276:  have hψ' : Function.Injective (Algebra.TensorProduct.map (AlgHom.id Γ(T, UT) Γ(T, UT)) ψ) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean:283:      ((CommRingCat.isPushout_tensorProduct _ _ _).flip.isoPushout.hom.hom.comp
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean:284:      (by exact Pi.evalRingHom _ _))).comp (Algebra.TensorProduct.piRight _ Γ(S, US) _ _).toRingHom
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean:288:    refine .comp ?_ (Algebra.TensorProduct.piRight _ Γ(S, US) _ _).injective
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean:289:    exact .piMap fun i ↦ (hV _).comp <| CommRingCat.isPushout_tensorProduct _ _ _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean:293:    (CommRingCat.isPushout_tensorProduct _ _ _).flip.isoPushout.symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean:297:      (Algebra.TensorProduct.map (AlgHom.id Γ(T, UT) Γ(T, UT)) ψ).toRingHom by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean:302:  · have H₁ : e.inv.hom.comp Algebra.TensorProduct.includeLeftRingHom =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean:304:      congr($((CommRingCat.isPushout_tensorProduct _ _ _).flip.inr_isoPushout_hom).hom)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean:307:        ($((CommRingCat.isPushout_tensorProduct ↑Γ(S, US)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean:312:  · have H₁ : e.inv.hom.comp Algebra.TensorProduct.includeRight.toRingHom =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean:314:      congr($((CommRingCat.isPushout_tensorProduct _ _ _).flip.inl_isoPushout_hom).hom)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean:317:        ($((CommRingCat.isPushout_tensorProduct ↑Γ(S, US)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimZeroStrict.lean:86:        rw [hkey, Prod.ext_iff, Fin.ext_iff, Fin.ext_iff]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/Basic.lean:550:    simp only [coeff_mk, Prod.forall, mem_antidiagonal]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:178:  preservesBinaryBiproducts_of_preservesBinaryProducts
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/Order.lean:410:      · exact False.elim (h (by simp [Prod.ext_iff, h'.1, h'.2]))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/FractionalIdeal/Basic.lean:134:noncomputable abbrev equivNumOfIsSMulRegular [FaithfulSMul R P] {I : FractionalIdeal S P}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/FractionalIdeal/Basic.lean:135:    (reg : IsSMulRegular P I.den) : I ≃ₗ[R] I.num := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/FractionalIdeal/Basic.lean:152:  equivNumOfIsSMulRegular (smul_right_injective P h_nz)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/FractionalIdeal/Basic.lean:158:  equivNumOfIsSMulRegular (smul_bijective ..).1
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean:45:open TensorProduct in
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean:79:      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean:111:  · trans hV.fromSpec ⟨P'.comap Algebra.TensorProduct.includeRight.toRingHom, inferInstance⟩
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Cover/MorphismProperty.lean:161:    ((Equiv.punitProd _).symm.trans (Equiv.sigmaEquivProd PUnit 𝒰.I₀).symm) (fun _ => Iso.refl _)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/OreLocalization/OreSet.lean:9:public import Mathlib.Algebra.Ring.Regular
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:48:endpoint-normalization `AlgEquiv`, and the descent of the iso to the reduced chart quotient are
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:355:The endpoint-normalization `AlgEquiv` for R2-3b-3 is an `aeval`-substitution on the **unquotiented**
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Proper.lean:40:      (Algebra.TensorProduct.lift (awayMapₐ 𝒜 hg hx) (awayMapₐ 𝒜 hf (hx.trans (mul_comm _ _)))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Proper.lean:71:  simp only [Algebra.TensorProduct.lift_tmul, awayMapₐ_apply, val_mul,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Proper.lean:82:open TensorProduct in
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Proper.lean:92:        Spec (.of <| TensorProduct (𝒜 0) (Away 𝒜 (i.2 : A)) (Away 𝒜 (j.2 : A))) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Proper.lean:102:    (Algebra.TensorProduct.lift (awayMapₐ 𝒜 j.2.2 rfl) (awayMapₐ 𝒜 i.2.2 (mul_comm _ _))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Proper.lean:116:    exact DFunLike.congr_fun (Algebra.TensorProduct.lift_comp_includeLeft
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Proper.lean:125:    exact DFunLike.congr_fun (Algebra.TensorProduct.lift_comp_includeRight
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/RingHomProperties.lean:13:public import Mathlib.RingTheory.IsTensorProduct
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/RingHomProperties.lean:34:open CategoryTheory Opposite CategoryTheory.Limits TensorProduct
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/RingHomProperties.lean:145:  let f' := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom R R' S')
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/RingHomProperties.lean:155:attribute [local instance] Algebra.TensorProduct.rightAlgebra
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/RingHomProperties.lean:252:lemma CodescendsAlong.algebraMap_tensorProduct (hPQ : CodescendsAlong P Q)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/RingHomProperties.lean:255:  let _ : Algebra T (S ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/RingHomProperties.lean:259:    (H : P ((Algebra.TensorProduct.includeRight.toRingHom : T →+* S ⊗[R] T))) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/RingHomProperties.lean:261:  let _ : Algebra T (S ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/Algebra/Basic.lean:221:/-- Product of two integral algebras is an integral algebra. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/Algebra/Basic.lean:229:section TensorProduct
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/Algebra/Basic.lean:233:open TensorProduct
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/Algebra/Basic.lean:239:    (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/Algebra/Basic.lean:240:    Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/Algebra/Basic.lean:244:instance Algebra.IsIntegral.tensorProduct [CommRing B]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/Algebra/Basic.lean:249:end TensorProduct
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:16:consequence** `varietyDim (productRankLocus d r) = δ + varietyDim (fibre d E)` is the *one genuinely
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/SurjectiveOnStalks.lean:10:public import Mathlib.RingTheory.Spectrum.Prime.TensorProduct
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/SurjectiveOnStalks.lean:125:      (PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks R A B H)).comp
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/SurjectiveOnStalks.lean:152:    simp only [SetLike.mem_coe, TopologicalSpace.Opens.mem_iSup, Sigma.exists, Prod.exists]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/ZMod/UnitsCyclic.lean:256:section Products
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/ZMod/UnitsCyclic.lean:322:end Products
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Algebraic/Integral.lean:280:  rw [← mul_one s, ← smul_eq_mul, ← TensorProduct.smul_tmul']
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Algebraic/Integral.lean:284:  rw [← Algebra.TensorProduct.includeRight_apply, ← AlgHom.coe_toRingHom (A := A),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Algebraic/Integral.lean:573:open TensorProduct in
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Algebraic/Integral.lean:574:instance Algebra.IsAlgebraic.tensorProduct : Algebra.IsAlgebraic R' (R' ⊗[R] S) where
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Sites/Representability.lean:13:public import Mathlib.CategoryTheory.Limits.Shapes.Products
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FlatQuasiFiniteHeight.lean:8:This is the height-preservation brick of the étale route to "smooth ⟹ regular": étale ⟹ flat +
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean:14:public import Mathlib.RingTheory.TensorProduct.MvPolynomial
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Algebraic/StronglyTranscendental.lean:24:open scoped TensorProduct nonZeroDivisors
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Sites/Fpqc.lean:89:    have : IsRegularEpi (Spec.map f) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Sites/Fpqc.lean:90:      isRegularEpi_of_flat_of_surjective_of_isAffine _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntervalModule.lean:251:noncomputable def submoduleProdEquiv {R M M' : Type*} [Semiring R]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntervalModule.lean:267:  rw [(submoduleProdEquiv p q).finrank_eq, Module.finrank_prod]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntervalModule.lean:276:  let Er := LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin c) K K
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntervalModule.lean:277:  let Ec := LinearEquiv.sumArrowLequivProdArrow (Fin b) (Fin d) K K
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntervalModule.lean:280:  -- the block-diagonal map is `g` conjugated by the `Sum ≃ Prod` reindexings of the function spaces
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntervalModule.lean:284:    apply Prod.ext
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntervalModule.lean:288:        add_zero, LinearEquiv.sumArrowLequivProdArrow_apply_fst]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntervalModule.lean:293:        zero_add, LinearEquiv.sumArrowLequivProdArrow_apply_snd]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/TwoSidedIdeal/BigOperators.lean:47:lemma listProd_mem {ι : Type*} (l : List ι) (f : ι → R) (hl : ∃ x ∈ l, f x ∈ I) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/TwoSidedIdeal/BigOperators.lean:63:lemma multiSetProd_mem {ι : Type*} (s : Multiset ι) (f : ι → R) (hs : ∃ x ∈ s, f x ∈ I) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/TwoSidedIdeal/BigOperators.lean:66:  simpa using listProd_mem (hl := hs)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/TwoSidedIdeal/BigOperators.lean:68:lemma finsetProd_mem {ι : Type*} (s : Finset ι) (f : ι → R) (hs : ∃ x ∈ s, f x ∈ I) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/TwoSidedIdeal/BigOperators.lean:71:  simpa using multiSetProd_mem (hs := hs)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/PiTensorProduct.lean:8:public import Mathlib.LinearAlgebra.PiTensorProduct
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/PiTensorProduct.lean:11:public import Mathlib.Data.Finset.NoncommProd
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/PiTensorProduct.lean:24:open TensorProduct Function
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/PiTensorProduct.lean:28:namespace PiTensorProduct
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/PiTensorProduct.lean:55:  PiTensorProduct.piTensorHomMap₂ <| tprod R fun _ ↦ LinearMap.mul _ _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/PiTensorProduct.lean:99:  induction x using PiTensorProduct.induction_on with
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/PiTensorProduct.lean:104:  induction x using PiTensorProduct.induction_on with
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/PiTensorProduct.lean:110:  one_mul := PiTensorProduct.one_mul
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/PiTensorProduct.lean:111:  mul_one := PiTensorProduct.mul_one
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/PiTensorProduct.lean:114:/-- `PiTensorProduct.tprod` as a `MonoidHom`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/PiTensorProduct.lean:140:  mul_assoc := PiTensorProduct.mul_assoc
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/PiTensorProduct.lean:213:@[simp] lemma tprod_noncommProd {κ : Type*} (s : Finset κ) (x : κ → Π i, A i) (hx) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/PiTensorProduct.lean:214:    tprod R (s.noncommProd x hx) = s.noncommProd (fun k => tprod R (x k))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/PiTensorProduct.lean:216:  Finset.map_noncommProd s x _ (tprodMonoidHom R)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/PiTensorProduct.lean:224:  AlgHom.toLinearMap_injective <| PiTensorProduct.ext <| MultilinearMap.ext fun x =>
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/PiTensorProduct.lean:255:  mul_comm := PiTensorProduct.mul_comm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/PiTensorProduct.lean:316:end PiTensorProduct
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/IsIntegral/Basic.lean:240:section Prod
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/IsIntegral/Basic.lean:253:    Prod.zero_eq_mk]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/IsIntegral/Basic.lean:259:end Prod
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean:126:  rw [← hdim, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Limits.lean:8:public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Limits.lean:490:    ((X ⨿ Y).sheaf.isProductOfDisjoint _ _ h₂).conePointUniqueUpToIso (limit.isLimit _) ≪≫
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Limits.lean:525:    coprodSpec R S (coprodMk _ _ x) = (PrimeSpectrum.primeSpectrumProd R S).symm x := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Limits.lean:536:    coprodSpec R S x = (PrimeSpectrum.primeSpectrumProd R S).symm ((coprodMk _ _).symm x) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Limits.lean:564:    PrimeSpectrum.primeSpectrumProdHomeo.trans (coprodMk (Spec <| .of R) (Spec <| .of S))).inv
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Limits.lean:573:      (opProdIsoCoprod R S).unop.inv)) = coprodSpec R S := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Limits.lean:576:        ← Spec.map_comp, Category.assoc, Iso.unop_inv, opProdIsoCoprod_inv_inl,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Limits.lean:580:        ← Spec.map_comp, Category.assoc, Iso.unop_inv, opProdIsoCoprod_inv_inr,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Limits.lean:729:instance : CartesianMonoidalCategory Scheme := .ofHasFiniteProducts
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/Field.lean:46:open scoped TensorProduct
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/NonUnitalSubsemiring/Basic.lean:15:public import Mathlib.Algebra.Ring.Prod
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/NonUnitalSubsemiring/Basic.lean:596:/-- Product of non-unital subsemirings is isomorphic to their product as semigroups. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/NonUnitalSubsemiring/Basic.lean:703:  NonUnitalRingHom.srange_eq_top_of_surjective (fst R S) Prod.fst_surjective
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/NonUnitalSubsemiring/Basic.lean:707:  NonUnitalRingHom.srange_eq_top_of_surjective (snd R S) <| Prod.snd_surjective
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Sites/BigZariski.lean:110:  refine Presieve.preservesProduct_of_isSheafFor F ?_ initialIsInitial
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/NonUnitalSubring/Basic.lean:49:* `Prod A B : NonUnitalSubring (R × S)` : the product of non-unital subrings
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/NonUnitalSubring/Basic.lean:669:/-- Product of `NonUnitalSubring`s is isomorphic to their product as rings. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/Basic.lean:32:open scoped TensorProduct
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/Basic.lean:154:open scoped TensorProduct
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/DividedPowerAlgebra/Init.lean:127:        simp only [dp_def, Prod.mk.eta, mkAlgHom, AlgHom.coe_mk]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:10:result is available to *prove* smooth ⟹ regular non-circularly):
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:112:identity, so this is available to prove smooth ⟹ regular without circularity. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/AdjoinRoot.lean:300:/-- Produce an algebra homomorphism `AdjoinRoot f →ₐ[R] S` sending `root f` to
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/AdjoinRoot.lean:329:/-- Produce an algebra homomorphism `AdjoinRoot f →ₐ[R] S` sending `root f` to
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/QuasiFinite.lean:29:open TensorProduct
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/QuasiFinite.lean:43:    ((Algebra.TensorProduct.cancelBaseChange _ _ q.ResidueField _ _).restrictScalars _).trans
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/QuasiFinite.lean:44:      (Algebra.TensorProduct.congr (.symm <| .ofBijective (Algebra.ofId _ _) H) .refl)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/QuasiFinite.lean:52:      (RingHomClass.toRingHom Algebra.TensorProduct.includeRight) = Q.1 := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/QuasiFinite.lean:63:      Q.1.comap Algebra.TensorProduct.includeRight := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/QuasiFinite.lean:70:    (H₂ : P₁.comap Algebra.TensorProduct.includeRight.toRingHom =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/QuasiFinite.lean:71:      P₂.comap Algebra.TensorProduct.includeRight.toRingHom) : P₁ = P₂ := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/QuasiFinite.lean:143:attribute [local instance high] Algebra.TensorProduct.leftAlgebra IsScalarTower.right
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/QuasiFinite.lean:209:      (_ : Algebra.TensorProduct.map (.id R' R') (integralClosure R S).val e₀ = e)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/QuasiFinite.lean:211:        Algebra.TensorProduct.includeRight.toRingHom = q ∧ e ∉ P' ∧
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/QuasiFinite.lean:215:            P'.comap (Algebra.TensorProduct.map (.id R' R') (integralClosure R S).val).toRingHom) ∧
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/QuasiFinite.lean:240:    show aeval (Algebra.TensorProduct.includeRight s) f = 0 by rw [aeval_algHom_apply, hf, map_zero]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/QuasiFinite.lean:242:    show aeval (Algebra.TensorProduct.includeRight s₀) f = 0 by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/QuasiFinite.lean:251:  let φ := Algebra.TensorProduct.map (.id R' R') (integralClosure R S).val
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/QuasiFinite.lean:256:  have hP'q : P'.1.comap Algebra.TensorProduct.includeRight.toRingHom = q :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/QuasiFinite.lean:277:      Algebra.TensorProduct.map_restrictScalars_comp_includeRight]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/QuasiFinite.lean:306:    (he₀e : Algebra.TensorProduct.map (.id R' R') (IsScalarTower.toAlgHom R R'' S) e₀ = e)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/QuasiFinite.lean:308:    (hP'q : P'.comap Algebra.TensorProduct.includeRight.toRingHom = q)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/QuasiFinite.lean:310:      P'.comap (Algebra.TensorProduct.map (.id R' R') (IsScalarTower.toAlgHom R R'' S)).toRingHom)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/QuasiFinite.lean:314:      ((Algebra.TensorProduct.map (Algebra.ofId R' (Localization.Away f)) (AlgHom.id R S)) e)) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/QuasiFinite.lean:319:    (Localization.awayMapₐ (Algebra.TensorProduct.map (.id R' R')
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/QuasiFinite.lean:334:      simp only [map_add, map_mul, map_pow, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/QuasiFinite.lean:339:    have := H (m.comap (Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap _ _)))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/QuasiFinite.lean:340:      inferInstance (m.comap_liesOver P (Algebra.TensorProduct.includeRight.comp
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/QuasiFinite.lean:342:        (Ideal.notMem_of_isUnit (m.comap Algebra.TensorProduct.includeRight)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/QuasiFinite.lean:349:    Algebra.TensorProduct.map (Algebra.ofId _ _) (.id _ _)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/QuasiFinite.lean:354:    refine IsLocalization.tensorProduct_tensorProduct _ _ _ _ ?_
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/QuasiFinite.lean:389:        Algebra.TensorProduct.includeRight.toRingHom = q ∧ e ∉ P' ∧
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/QuasiFinite.lean:404:    Algebra.TensorProduct.map (Algebra.ofId _ _) (.id _ _)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/QuasiFinite.lean:410:    refine IsLocalization.tensorProduct_tensorProduct _ _ _ _ ?_
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/QuasiFinite.lean:425:    .trans _ P _, Algebra.TensorProduct.map (Algebra.ofId _ _) (.id _ _) e,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Unramified/LocalStructure.lean:43:open Polynomial TensorProduct Algebra
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Unramified/LocalStructure.lean:96:  · dsimp [-TensorProduct.algebraMap_apply]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Unramified/LocalStructure.lean:101:attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Unramified/LocalStructure.lean:118:    simpa using TensorProduct.adjoin_one_tmul_image_eq_top (A := P.ResidueField) _ hp₂
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Unramified/LocalStructure.lean:124:  · simp [← TensorProduct.right_algebraMap_apply, ← IsScalarTower.algebraMap_apply]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Unramified/LocalStructure.lean:216:  set φ : p.Fiber S →ₐ[p.ResidueField] Q.ResidueField := TensorProduct.lift
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Unramified/LocalStructure.lean:235:    let φ' : p.Fiber S →ₐ[p.ResidueField] Q'.ResidueField := TensorProduct.lift
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:71:* `PrimeSpectrum.primeSpectrumProdHomeo`: the prime spectrum of a product semiring is homeomorphic
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:455:section SpecProd
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:459:lemma primeSpectrumProd_symm_inl (x) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:460:    (primeSpectrumProd R S).symm (.inl x) = comap (RingHom.fst R S) x := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:463:lemma primeSpectrumProd_symm_inr (x) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:464:    (primeSpectrumProd R S).symm (.inr x) = comap (RingHom.snd R S) x := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:486:  (isClosedEmbedding_iff _).mpr ⟨isEmbedding_comap_of_surjective _ _ Prod.fst_surjective, by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:490:  (isClosedEmbedding_iff _).mpr ⟨isEmbedding_comap_of_surjective _ _ Prod.snd_surjective, by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:496:def primeSpectrumProdHomeo :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:498:  refine ((primeSpectrumProd R S).symm.toHomeomorphOfIsInducing ?_).symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:502:    simp only [Function.comp_def, primeSpectrumProd_symm_inl, primeSpectrumProd_symm_inr]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:504:  · simp_rw [isClosedMap_sum, primeSpectrumProd_symm_inl, primeSpectrumProd_symm_inr]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:507:end SpecProd
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Unramified/Locus.lean:69:open _root_.TensorProduct in
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Unramified/Locus.lean:76:    (hQ' : Q = Q'.comap Algebra.TensorProduct.includeRight.toRingHom) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Unramified/Locus.lean:83:    Algebra.TensorProduct.lift (Algebra.ofId _ _) f₀ fun _ _ ↦ .all _ _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/Kaehler.lean:31:open TensorProduct
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/Kaehler.lean:110:      exact (TensorProduct.mk _ _ _ 1).restrictScalars P.Ring ∘ₗ
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/Kaehler.lean:111:        (TensorProduct.mk _ _ _ 1).restrictScalars P.Ring)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/Kaehler.lean:133:        LinearMap.liftBaseChange _ _) x = ((TensorProduct.mk _ _ _ 1) ∘ₗ
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/Kaehler.lean:154:      ((TensorProduct.mk _ _ _ 1).restrictScalars _ ∘ₗ Cotangent.mk)) ∘ₗ e.symm.toLinearMap
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/Kaehler.lean:180:        rw [TensorProduct.smul_tmul', mul_smul, f.mapKer_apply_coe, ← halg,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/Kaehler.lean:181:          algebraMap_smul, ← TensorProduct.tmul_smul, h₂, tmul_zero, smul_zero]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/Kaehler.lean:196:  change ((TensorProduct.mk _ _ _ 1).restrictScalars _ ∘ₗ Cotangent.mk).liftBaseChange _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Etale/Kaehler.lean:219:        simp [algebraMap_eq_smul_one, TensorProduct.smul_tmul']
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitKostant.lean:477:    Equiv.subtypeEquivRight fun lam ↦ by rw [Prod.ext_iff]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:273:noncomputable def quotientInfEquivQuotientProd (I J : Ideal R) (coprime : IsCoprime I J) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:285:theorem quotientInfEquivQuotientProd_fst (I J : Ideal R) (coprime : IsCoprime I J) (x : R ⧸ I ⊓ J) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:286:    (quotientInfEquivQuotientProd I J coprime x).fst =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:291:theorem quotientInfEquivQuotientProd_snd (I J : Ideal R) (coprime : IsCoprime I J) (x : R ⧸ I ⊓ J) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:292:    (quotientInfEquivQuotientProd I J coprime x).snd =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:297:theorem fst_comp_quotientInfEquivQuotientProd (I J : Ideal R) (coprime : IsCoprime I J) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:299:        (quotientInfEquivQuotientProd I J coprime : R ⧸ I ⊓ J →+* (R ⧸ I) × R ⧸ J) =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:304:theorem snd_comp_quotientInfEquivQuotientProd (I J : Ideal R) (coprime : IsCoprime I J) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:306:        (quotientInfEquivQuotientProd I J coprime : R ⧸ I ⊓ J →+* (R ⧸ I) × R ⧸ J) =
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
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:833:def AlgEquiv.quotientBot [CommSemiring R] [Ring S] [Algebra R S] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:839:lemma AlgEquiv.quotientBot_mk [CommSemiring R] [CommRing S] [Algebra R S] (s : S) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:840:    AlgEquiv.quotientBot R S (Ideal.Quotient.mk ⊥ s) = s :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:844:lemma AlgEquiv.quotientBot_symm_mk [CommSemiring R] [CommRing S] [Algebra R S]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Operations.lean:845:    (s : S) : (AlgEquiv.quotientBot R S).symm s = s :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Unramified/LocalRing.lean:102:  rw [← subsingleton_tensorProduct (R := S)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Unramified/LocalRing.lean:112:  | add x y hx hy _ _ => simp [*, TensorProduct.tmul_add]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Unramified/LocalRing.lean:115:    simp [*, TensorProduct.tmul_add, TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Unramified/LocalRing.lean:255:    simp only [localRingHom_mk', Prod.exists, Subtype.exists, Ideal.mem_primeCompl_iff,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Unramified/Field.lean:36:open scoped TensorProduct
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Unramified/Field.lean:74:    (Algebra.TensorProduct.congr AlgEquiv.refl e.symm).trans (Algebra.TensorProduct.rid K A A)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Unramified/Field.lean:81:    apply _root_.TensorProduct.ext'
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Unramified/Field.lean:127:  let f := (Algebra.TensorProduct.includeRight (R := K) (A := AlgebraicClosure K) (B := A))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Unramified/Field.lean:130:        (Algebra.TensorProduct.lid K A).symm.toLinearMap := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Unramified/Field.lean:135:      exact this.comp (Algebra.TensorProduct.lid K A).symm.injective
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Unramified/Field.lean:165:    rw [← not_subsingleton_iff_nontrivial, ← rank_zero_iff (R := K), rank_tensorProduct',
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Unramified/Field.lean:174:    rw [sub_pow_expChar_pow, TensorProduct.tmul_pow, one_pow, TensorProduct.tmul_pow, one_pow]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Unramified/Field.lean:176:    rw [← hr, algebraMap_eq_smul_one, TensorProduct.smul_tmul, sub_self]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Unramified/Field.lean:191:      (DFunLike.congr_arg ((Basis.extend h).tensorProduct (Basis.extend h)).repr H) (a, b)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Unramified/Field.lean:192:    simp only [Basis.tensorProduct_repr_tmul_apply, ← ha, ← hb, Basis.repr_self, smul_eq_mul,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/ScaleRoots.lean:202:    simp only [Finset.mem_antidiagonal, coeff_scaleRoots, Prod.forall]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/ScaleRoots.lean:329:lemma rootMultiplicity_scaleRoots (p : R[X]) {r a : R} (hr : IsLeftRegular r) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/ScaleRoots.lean:355:    rootMultiplicity_scaleRoots _ hr.isRegular.left]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/ChineseRemainder.lean:8:public import Mathlib.LinearAlgebra.TensorProduct.Pi
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/ChineseRemainder.lean:9:public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/ChineseRemainder.lean:25:open TensorProduct LinearMap
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/ChineseRemainder.lean:29:      .pi (fun i ↦ TensorProduct.mk R (R ⧸ I i) M 1) ∘ₗ TensorProduct.lid R M := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/ChineseRemainder.lean:39:theorem pi_tensorProductMk_quotient_surjective :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/ChineseRemainder.lean:40:    Surjective (LinearMap.pi fun i ↦ TensorProduct.mk R (R ⧸ I i) M 1) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/ChineseRemainder.lean:48:theorem ker_tensorProductMk_quotient :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/ChineseRemainder.lean:49:    ker (LinearMap.pi fun i ↦ TensorProduct.mk R (R ⧸ I i) M 1) =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/ChineseRemainder.lean:52:  rw [← (TensorProduct.lid R M).conj_exact_iff_exact, exact_iff] at this
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Unramified/Basic.lean:12:public import Mathlib.RingTheory.TensorProduct.Quotient
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Unramified/Basic.lean:39:open scoped TensorProduct
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Unramified/Basic.lean:104:    let f := RingHom.ker (TensorProduct.lmul' R (S := A)).kerSquareLift.toRingHom
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Unramified/Basic.lean:106:      (RingHom.ker (TensorProduct.lmul' R (S := A)).kerSquareLift.toRingHom) ?_ ?_
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Unramified/Basic.lean:110:      apply RingHom.kerLift_injective (TensorProduct.lmul' R (S := A)).kerSquareLift.toRingHom
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Unramified/Basic.lean:272:open scoped TensorProduct
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Unramified/Basic.lean:289:  .of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B p).symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Index.lean:12:public import Mathlib.LinearAlgebra.TensorProduct.Quotient
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Index.lean:13:public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Index.lean:16:public import Mathlib.RingTheory.TensorProduct.Finite
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Index.lean:36:open TensorProduct in
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Quotient/Index.lean:61:open TensorProduct in
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/IsTensorProduct.lean:8:public import Mathlib.RingTheory.TensorProduct.Maps
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/IsTensorProduct.lean:15:- `IsTensorProduct`: A predicate on `f : M₁ →ₗ[R] M₂ →ₗ[R] M` expressing that `f` realizes `M` as
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/IsTensorProduct.lean:29:- `TensorProduct.isBaseChange`: `S ⊗[R] M` is the base change of `M` along `R → S`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/IsTensorProduct.lean:38:open TensorProduct
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/IsTensorProduct.lean:40:section IsTensorProduct
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/IsTensorProduct.lean:51:/-- Given a bilinear map `f : M₁ →ₗ[R] M₂ →ₗ[R] M`, `IsTensorProduct f` means that
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/IsTensorProduct.lean:55:def IsTensorProduct : Prop :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/IsTensorProduct.lean:56:  Function.Bijective (TensorProduct.lift f)

codex
A useful distinction is emerging: the repository already has route-b machinery phrased exactly as `Sred ≃ₐ[k] SchurLoc ⊗ FibreAlg`, which is the ring form of the pivot trivialization. The route-c set-level goal can reuse that shape if you add dimension transport lemmas for coordinate rings, but a pointwise `σ : U → H` alone will not plug into existing APIs.
exec
/bin/bash -lc "sed -n '1,180p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean && sed -n '1,200p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
import DLNFibre.Core.EndBaseChangeSweep
import DLNFibre.Core.SigmaCodim
import DLNFibre.Core.NullstellensatzCodim
import DLNFibre.Core.RadicalCatenary

/-!
# `DLNFibre.Core.RouteCAssembly` — route-c assembly `codim(fibre d B) = C + δ` (conditional bank)

The downstream **arithmetic assembly** of the equivariant homogeneous-sweep route (thread 27/28
certificate): from the sweep dimension identity, the closure/density bridge, and the
dimension/codimension relations, the fibre codimension is the combinatorial codimension `C` plus the
matrix-stratum shift `δ`:

> `codimRepCanonical (fibre d B) = (cCodim d r).toNat + r·(d_N + d_0 − r)`   (`B` rank `r`).

**The conditional-bank pattern.** The one genuinely-hard rung — the homogeneous-sweep dimension
identity `varietyDim Σ^r = δ + varietyDim F` (`hSweep`) — and the Cited closure/density bridge
`varietyDim Σ^r = varietyDim Σ̄^r` (`hClosure`, Lehalleur–Rimányi 4.4/4.5) are carried as **explicit
named hypotheses**, so everything *around* them is machine-checked. The two dimension/codimension
relations `codimRepCanonical Z + varietyDim Z = card` are carried as named hypotheses
`hCatFibre`/`hCatSigma` in the base theorem; the primed variant discharges them from the
reducible-locus catenary `Core.RadicalCatenary` (true for any nonempty subset of affine space),
leaving ONLY the sweep + closure. Nothing in this module claims the sweep or the closure.

The arithmetic is **purely additive** (no `ℕ∞` truncated subtraction): chaining
`C + δ + dim F = C + dim Σ̄^r = card = codim F + dim F` and cancelling the finite `dim F`.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial Ideal

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## The route-c assembly (conditional bank) -/

/-- **Route-c assembly: `codim(fibre d B) = C + δ` (conditional bank).** For a rank-`r` target `B`
(`N ≥ 1`, alg-closed char 0), the geometric codimension of the fibre `mult⁻¹(B)` is `C = cCodim d r`
plus the matrix-stratum shift `δ = r·(d_N + d_0 − r)` — carrying the homogeneous-sweep dimension
identity `hSweep`, the Cited closure bridge `hClosure`, and the two reducible-locus catenary
relations `hCatFibre`/`hCatSigma` as explicit named hypotheses. The proof is the additive chain
`C + δ + dim F = C + dim Σ̄^r = card = codim F + dim F`, cancelling the finite `dim F`. -/
theorem codimRepCanonical_fibre_eq_cCodim_add_shift_of_sweep [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 1) → ℕ) (r : ℕ) (h : (kostantPartitions d r).Nonempty)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) (hB : B.rank = r)
    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
        = ((r * (d (Fin.last N) + d 0 - r) : ℕ) : ℕ∞)
          + varietyDim (canonicalCoord d '' fibre d B))
    (hClosure : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
        = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r))
    (hCatFibre : codimRepCanonical (fibre d B)
        + varietyDim (canonicalCoord d '' fibre d B) = (Nat.card (RepCoord d) : ℕ∞))
    (hCatSigma : codimRepCanonical (productRankLocusLE (k := k) d r)
        + varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
          = (Nat.card (RepCoord d) : ℕ∞)) :
    codimRepCanonical (fibre d B)
      = ((cCodim d r h).toNat : ℕ∞) + ((r * (d (Fin.last N) + d 0 - r) : ℕ) : ℕ∞) := by
  -- `codim Σ̄^r = C` (LANDED Brick A).
  have hCsigma : codimRepCanonical (productRankLocusLE (k := k) d r)
      = ((cCodim d r h).toNat : ℕ∞) :=
    codimRepCanonical_productRankLocusLE_eq_cCodim_enat d r h
  -- `dim Σ̄^r = dim Σ^r = δ + dim F` (closure then sweep).
  have hdimSigma : varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
      = ((r * (d (Fin.last N) + d 0 - r) : ℕ) : ℕ∞)
        + varietyDim (canonicalCoord d '' fibre d B) := by
    rw [← hClosure, hSweep]
  -- `dim F` is finite (`hCatFibre`: `codim F + dim F = card`, a finite total).
  have hdimF_ne : varietyDim (canonicalCoord d '' fibre d B) ≠ ⊤ := by
    intro htop
    rw [htop, add_top] at hCatFibre
    exact (ENat.coe_ne_top (Nat.card (RepCoord d))) hCatFibre.symm
  -- substitute `codim Σ̄^r = C`, `dim Σ̄^r = δ + dim F` into `hCatSigma`: `C + (δ + dim F) = card`.
  rw [hCsigma, hdimSigma] at hCatSigma
  -- additive chain `(dim F) + codim F = card = (dim F) + (C + δ)`; left-cancel the finite `dim F`.
  have key : varietyDim (canonicalCoord d '' fibre d B) + codimRepCanonical (fibre d B)
      = varietyDim (canonicalCoord d '' fibre d B)
        + (((cCodim d r h).toNat : ℕ∞) + ((r * (d (Fin.last N) + d 0 - r) : ℕ) : ℕ∞)) := by
    calc varietyDim (canonicalCoord d '' fibre d B) + codimRepCanonical (fibre d B)
        = codimRepCanonical (fibre d B) + varietyDim (canonicalCoord d '' fibre d B) := by
          rw [add_comm]
      _ = (Nat.card (RepCoord d) : ℕ∞) := hCatFibre
      _ = ((cCodim d r h).toNat : ℕ∞)
            + (((r * (d (Fin.last N) + d 0 - r) : ℕ) : ℕ∞)
              + varietyDim (canonicalCoord d '' fibre d B)) := hCatSigma.symm
      _ = varietyDim (canonicalCoord d '' fibre d B)
            + (((cCodim d r h).toNat : ℕ∞) + ((r * (d (Fin.last N) + d 0 - r) : ℕ) : ℕ∞)) := by
          rw [← add_assoc, add_comm]
  exact ENat.add_right_injective_of_ne_top hdimF_ne key

/-! ## The catenary hypotheses discharged (only the sweep + closure remain) -/

/-- **Route-c assembly with the catenary hypotheses discharged.** For a rank-`r` target `B`
(`N ≥ 1`, alg-closed char 0), `codimRepCanonical (fibre d B) = C + δ`, carrying ONLY the
homogeneous-sweep dimension identity `hSweep` and the Cited closure bridge `hClosure` as named
hypotheses — the two reducible-locus catenary relations are now **proved** from
`codimRepCanonical_add_varietyDim_eq_card_of_nonempty` (`Core.RadicalCatenary`), given that the
fibre and `Σ̄^r` are nonempty (their canonical flattenings have a point). -/
theorem codimRepCanonical_fibre_eq_cCodim_add_shift_of_sweep' [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 1) → ℕ) (r : ℕ) (h : (kostantPartitions d r).Nonempty)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) (hB : B.rank = r)
    (hFne : (canonicalCoord d '' fibre d B).Nonempty)
    (hSigmaNe : (canonicalCoord d '' productRankLocusLE (k := k) d r).Nonempty)
    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
        = ((r * (d (Fin.last N) + d 0 - r) : ℕ) : ℕ∞)
          + varietyDim (canonicalCoord d '' fibre d B))
    (hClosure : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
        = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)) :
    codimRepCanonical (fibre d B)
      = ((cCodim d r h).toNat : ℕ∞) + ((r * (d (Fin.last N) + d 0 - r) : ℕ) : ℕ∞) :=
  codimRepCanonical_fibre_eq_cCodim_add_shift_of_sweep d r h B hB hSweep hClosure
    (codimRepCanonical_add_varietyDim_eq_card_of_nonempty hFne)
    (codimRepCanonical_add_varietyDim_eq_card_of_nonempty hSigmaNe)

end DLNFibre.Core
import DLNFibre.Core.NullstellensatzCodim
import DLNFibre.Core.IntegralDimension
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# `DLNFibre.Core.RadicalCatenary` — the catenary identity for a reducible (radical) locus

The prime catenary `height p + ringKrullDim (R ⧸ p) = card` (`Core.NullstellensatzCodim`,
`height_add_ringKrullDim_quotient_eq_card`) extended to an **arbitrary proper** ideal `I ≠ ⊤` of a
polynomial ring `R = MvPolynomial σ k` (`σ` finite, `k` any field):

> `height I + ringKrullDim (R ⧸ I) = Nat.card σ`.

Geometrically: a reducible variety `V(I) = ⋃ V(pᵢ)` has codimension `= min` component codimension
and dimension `= max` component dimension, and the polynomial ring is catenary, so the two are dual.
The proof is a direct order/chain argument over `PrimeSpectrum`, two inequalities squeezed by
`le_antisymm` (no component-decomposition lemma, no radicality needed):

* **upper bound** `height I + dim (R ⧸ I) ≤ card`: a longest prime chain of `R ⧸ I` maps into the
  primes `⊇ I` of `R`; its head contains a minimal prime `p`, so `dim (R ⧸ I) ≤ coheight p =
  dim (R ⧸ p)`, while `height I ≤ height p`, and the per-prime catenary closes `≤ card`;
* **lower bound** `card ≤ height I + dim (R ⧸ I)`: a minimal prime `p₀` realises `height I`; the
  quotient surjection `R ⧸ I ↠ R ⧸ p₀` gives `dim (R ⧸ p₀) ≤ dim (R ⧸ I)`, and the per-prime
  catenary for `p₀` reads `card = height I + dim (R ⧸ p₀) ≤ height I + dim (R ⧸ I)`.

The headline specialises to `codimRepCanonical Z + varietyDim Z = card` for any **nonempty**
Zariski-closed `Z` (over an algebraically closed field its vanishing ideal is radical and proper),
discharging the reducible-locus catenary that `Core.RouteCAssembly` carries as the named hypotheses
`hCatFibre`/`hCatSigma`.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

open MvPolynomial Ideal Order

namespace DLNFibre.Core

universe u

variable {k : Type u} [Field k] {σ : Type*}

/-! ## A minimal prime realising the height -/

/-- **A minimal prime realises `I.height`.** For a Noetherian ring and a proper ideal `I ≠ ⊤`, some
minimal prime `p ∈ I.minimalPrimes` has `p.height = I.height`. The infimum `I.height = ⨅_{p}
primeHeight p` over the finite nonempty set of minimal primes is attained. -/
theorem exists_minimalPrime_height_eq_height {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (hIne : I ≠ ⊤) :
    ∃ p ∈ I.minimalPrimes, p.height = I.height := by
  obtain ⟨p₀, hp₀⟩ := Ideal.nonempty_minimalPrimes hIne
  obtain ⟨p, hp, hpmin⟩ :=
    Set.exists_min_image _ (fun J ↦ J.height)
      I.finite_minimalPrimes_of_isNoetherianRing ⟨p₀, hp₀⟩
  refine ⟨p, hp, ?_⟩
  haveI := Ideal.minimalPrimes_isPrime hp
  apply le_antisymm
  · -- `height p ≤ height I`: `p` minimises `height` over the minimal primes (the `⨅`).
    rw [Ideal.height]
    refine le_iInf₂ (fun J hJ ↦ ?_)
    haveI := Ideal.minimalPrimes_isPrime hJ
    have : @Ideal.primeHeight _ _ J (Ideal.minimalPrimes_isPrime hJ) = J.height :=
      (Ideal.height_eq_primeHeight J).symm
    rw [this]
    exact hpmin J hJ
  · -- `height I ≤ height p`: `height I` is the `⨅`, `p` is one of the minimal primes.
    rw [Ideal.height]
    refine iInf₂_le_of_le p hp ?_
    exact le_of_eq (by rw [← Ideal.height_eq_primeHeight])

/-! ## A top-dimensional component -/

/-- **A minimal prime carries the full quotient dimension.** For a finite-dimensional Noetherian
ring `R` and a proper ideal `I ≠ ⊤`, some minimal prime `p ∈ I.minimalPrimes` has
`ringKrullDim (R ⧸ I) ≤ ringKrullDim (R ⧸ p)` — a top-dimensional component. A longest prime chain
of `R ⧸ I` maps (via the
quotient `comap`, strictly monotone) into the primes `⊇ I` of `R`; its head contains a minimal prime
`p`, and the chain's length is `≤ coheight p = ringKrullDim (R ⧸ p)`. -/
theorem exists_minimalPrime_ringKrullDim_quotient_ge {R : Type*} [CommRing R] [IsNoetherianRing R]
    [FiniteRingKrullDim R] (I : Ideal R) (hIne : I ≠ ⊤) :
    ∃ p ∈ I.minimalPrimes, ringKrullDim (R ⧸ I) ≤ ringKrullDim (R ⧸ p) := by
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  haveI : FiniteRingKrullDim (R ⧸ I) := by
    rw [finiteRingKrullDim_iff_ne_bot_and_top (R := R ⧸ I)]
    refine ⟨?_, ne_top_of_le_ne_top (ringKrullDim_ne_top (R := R)) (ringKrullDim_quotient_le I)⟩
    exact fun h ↦ by simpa [h] using ringKrullDim_nonneg_of_nontrivial (R := R ⧸ I)
  haveI : FiniteDimensionalOrder (PrimeSpectrum (R ⧸ I)) := by
    rw [Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top (α := PrimeSpectrum (R ⧸ I))]
    exact ⟨ringKrullDim_ne_bot, ringKrullDim_ne_top⟩
  -- a longest chain `L` of `Spec (R ⧸ I)`, realising the Krull dimension.
  set L := LTSeries.longestOf (PrimeSpectrum (R ⧸ I)) with hL
  have hLlen : ringKrullDim (R ⧸ I) = (L.length : WithBot ℕ∞) := by
    rw [ringKrullDim, Order.krullDim_eq_length_of_finiteDimensionalOrder]
  -- map the chain into `Spec R` via the (strictly monotone) quotient comap.
  have hsm : StrictMono (PrimeSpectrum.comap (Ideal.Quotient.mk I)) :=
    RingHom.strictMono_comap_of_surjective Ideal.Quotient.mk_surjective
  set Lmap := L.map (PrimeSpectrum.comap (Ideal.Quotient.mk I)) hsm with hLmap
  -- the head of the mapped chain is a prime `⊇ I`; pick a minimal prime `p` below it.
  have hheadge : I ≤ Lmap.head.asIdeal := by
    rw [hLmap, LTSeries.head_map, PrimeSpectrum.comap_asIdeal]
    exact (Ideal.mk_ker (I := I)).symm.trans_le (Ideal.ker_le_comap (Ideal.Quotient.mk I))
  obtain ⟨p, hpmem, hple⟩ := Ideal.exists_minimalPrimes_le hheadge
  haveI : p.IsPrime := Ideal.minimalPrimes_isPrime hpmem
  refine ⟨p, hpmem, ?_⟩
  -- `L.length ≤ coheight ⟨p⟩ = dim (R ⧸ p)`.
  have hlen_le : (Lmap.length : ℕ∞) ≤ Order.coheight (⟨p, ‹_›⟩ : PrimeSpectrum R) :=
    Order.length_le_coheight (x := (⟨p, ‹_›⟩ : PrimeSpectrum R)) (p := Lmap) hple
  rw [hLlen, ringKrullDim_quotient_eq_coheight (⟨p, ‹_›⟩ : PrimeSpectrum R)]
  rw [hLmap, LTSeries.map_length] at hlen_le
  exact_mod_cast hlen_le

/-! ## The radical-locus catenary -/

/-- **The reducible-locus catenary.** For `R = MvPolynomial σ k` (`σ` finite, `k` any field) and a
proper ideal `I ≠ ⊤`, `height I + ringKrullDim (R ⧸ I) = Nat.card σ` — the per-prime catenary
carried across the components: `dim (R ⧸ I) = max` dim `= card − min` height `= card − height I`.
Direct chain/coheight squeeze; no radicality needed. -/
theorem height_add_ringKrullDim_quotient_eq_card_of_ne_top [Finite σ]
    (I : Ideal (MvPolynomial σ k)) (hIne : I ≠ ⊤) :
    (I.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial σ k ⧸ I) = (Nat.card σ : WithBot ℕ∞) := by
  set R := MvPolynomial σ k with hR
  set n : WithBot ℕ∞ := (Nat.card σ : WithBot ℕ∞) with hn
  -- the per-prime catenary, restated as `dim (R ⧸ p) = card − height p` in the additive form.
  have hprime : ∀ p : Ideal R, p.IsPrime →
      (p.height : WithBot ℕ∞) + ringKrullDim (R ⧸ p) = n := fun p hp ↦
    height_add_ringKrullDim_quotient_eq_card (k := k) (σ := σ) p
  -- `R = MvPolynomial σ k` has finite Krull dimension `Nat.card σ`.
  have hRdim : ringKrullDim R = ((Nat.card σ : ℕ∞) : WithBot ℕ∞) := ringKrullDim_mvPolynomial_finite
  haveI : FiniteRingKrullDim R := by
    rw [finiteRingKrullDim_iff_ne_bot_and_top (R := R), hRdim]
    refine ⟨WithBot.coe_ne_bot, ?_⟩
    rw [Ne, WithBot.coe_eq_top]
    exact ENat.coe_ne_top (Nat.card σ)
  apply le_antisymm
  · -- upper bound: a top-dimensional component `p` has `dim (R ⧸ I) ≤ dim (R ⧸ p)`.
    obtain ⟨p, hpmem, hpdim⟩ := exists_minimalPrime_ringKrullDim_quotient_ge I hIne
    haveI : p.IsPrime := Ideal.minimalPrimes_isPrime hpmem
    have hIp : I ≤ p := hpmem.1.2
    calc (I.height : WithBot ℕ∞) + ringKrullDim (R ⧸ I)
        ≤ (p.height : WithBot ℕ∞) + ringKrullDim (R ⧸ p) :=
          add_le_add (WithBot.coe_le_coe.mpr (Ideal.height_mono hIp)) hpdim
      _ = n := hprime p ‹_›
  · -- lower bound: a minimal prime `p₀` realising `height I`, with `R ⧸ I ↠ R ⧸ p₀`.
    obtain ⟨p₀, hp₀mem, hp₀ht⟩ := exists_minimalPrime_height_eq_height I hIne
    haveI : p₀.IsPrime := Ideal.minimalPrimes_isPrime hp₀mem
    have hIp₀ : I ≤ p₀ := hp₀mem.1.2
    -- `dim (R ⧸ p₀) ≤ dim (R ⧸ I)` from the quotient surjection `R ⧸ I ↠ R ⧸ p₀`.
    have hdimle : ringKrullDim (R ⧸ p₀) ≤ ringKrullDim (R ⧸ I) :=
      ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hIp₀)
    -- the per-prime catenary for `p₀`, with `height p₀ = height I`.
    have := hprime p₀ ‹_›
    rw [hp₀ht] at this
    calc n = (I.height : WithBot ℕ∞) + ringKrullDim (R ⧸ p₀) := this.symm
      _ ≤ (I.height : WithBot ℕ∞) + ringKrullDim (R ⧸ I) := by
          gcongr

/-! ## Specialisation to the geometry layer (`codimRepCanonical Z + varietyDim Z = card`) -/

/-- The vanishing ideal of a **nonempty** set is proper: a polynomial vanishing on a point `x ∈ Z`
cannot be the unit `1` (which evaluates to `1 ≠ 0`), so `vanishingIdeal Z ≠ ⊤`. -/
theorem vanishingIdeal_ne_top_of_nonempty [Finite σ] {Z : Set (σ → k)} (hZ : Z.Nonempty) :
    (vanishingIdeal k Z : Ideal (MvPolynomial σ k)) ≠ ⊤ := by
  obtain ⟨x, hx⟩ := hZ
  rw [Ideal.ne_top_iff_one]
  intro hone
  rw [MvPolynomial.mem_vanishingIdeal_iff] at hone
  have := hone x hx
  rw [map_one] at this
  exact one_ne_zero this

variable {N : ℕ}

/-- **The reducible-locus catenary at `codimRepCanonical`/`varietyDim` (additive, `ℕ∞`).** For a
**nonempty** subset `Z ⊆ Rep_d` whose canonical flattening `canonicalCoord d '' Z` is Zariski-closed
(its vanishing ideal is radical and proper), the geometric codimension plus the variety dimension
equal the ambient dimension: `codimRepCanonical Z + varietyDim (canonicalCoord d '' Z) = card`. No
irreducibility hypothesis — the reducible-locus catenary converted to `ℕ∞` (the quotient is
nontrivial, so `ringKrullDim ≠ ⊥`). -/
theorem codimRepCanonical_add_varietyDim_eq_card_of_nonempty {d : Fin (N + 1) → ℕ}
    {Z : Set (Tuple (k := k) d)} (hZ : (canonicalCoord d '' Z).Nonempty) :
    codimRepCanonical Z + varietyDim (canonicalCoord d '' Z)
      = (Nat.card (RepCoord d) : ℕ∞) := by
  have hIne : (vanishingIdeal k (canonicalCoord d '' Z) :
      Ideal (MvPolynomial (RepCoord d) k)) ≠ ⊤ :=
    vanishingIdeal_ne_top_of_nonempty hZ
  have key := height_add_ringKrullDim_quotient_eq_card_of_ne_top
    (vanishingIdeal k (canonicalCoord d '' Z)) hIne
  haveI : Nontrivial (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal k (canonicalCoord d '' Z)) :=
    Ideal.Quotient.nontrivial_iff.mpr hIne
  have hnn : (0 : WithBot ℕ∞) ≤ ringKrullDim
      (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal k (canonicalCoord d '' Z)) :=
    ringKrullDim_nonneg_of_nontrivial
  have hne : ringKrullDim
      (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal k (canonicalCoord d '' Z)) ≠ ⊥ :=
    fun h ↦ by rw [h] at hnn; exact absurd hnn (by simp)
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [codimRepCanonical, codimRep, varietyDim, ← hm, WithBot.unbotD_coe]
  rw [← hm] at key
  exact_mod_cast key


exec
/bin/bash -lc 'rg -n "productRankLocus_eq_iUnion_smul_fibre|iUnion_smul|smul_fibre|Sigma|rank.*fibre|BaseChangeGroup" -S /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:45:    (P : BaseChangeGroup (k := k) d) (h : P • A = B) (i j : Fin (N + 1)) (hij : i ≤ j) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:134:    ∃ P : BaseChangeGroup (k := k) d, P • A = B := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:166:    ∃ P : BaseChangeGroup (k := k) d, P • A = B := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:269:      ↔ ∃ P : BaseChangeGroup (k := k) d, P • A = B :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:341:    ∃ (L : List (Fin (N + 1) × Fin (N + 1))) (h : foldDim L = d) (P : BaseChangeGroup (k := k) d),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:376:    ∃ (L : List (Fin (N + 1) × Fin (N + 1))) (h : foldDim L = d) (P : BaseChangeGroup (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:414:def witnessBaseChangeQ : BaseChangeGroup (k := ℚ) dWitness :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:423:example : ∃ Q : BaseChangeGroup (k := ℚ) dWitness,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:432:    ↔ ∃ Q : BaseChangeGroup (k := ℚ) dWitness,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:519:    (P : BaseChangeGroup (k := ℚ) dWitness),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean:527:    (P : BaseChangeGroup (k := ℚ) dWitness), P • tupleWitnessQ = h ▸ intervalDirectSum L := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibrationProbe.lean:1:import DLNFibre.Core.SigmaCodim
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:27:   single-matrix stratum coords), via `Equiv.uniqueSigma` (the `Sigma` over the `Unique` base
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:70:`RepCoord (dStratum q p)` is a `Sigma` over `Fin 1`; collapsing it gives `Fin p × Fin q` (the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:79:  Equiv.uniqueSigma (fun i : Fin 1 ↦ Fin (dStratum q p i.succ) × Fin (dStratum q p i.castSucc))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodim.lean:1:import DLNFibre.Core.SigmaCodim
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodim.lean:22:fibre dimension *jumps* as the rank drops (witness `(2,2,2)`: the rank-`1` fibre has dimension `4`,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodim.lean:23:the rank-`0` fibre `mult⁻¹(0) = Σ̄^0` has dimension `5`), so the going-down additivity
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodim.lean:31:stand on. Mechanism: `mult⁻¹(B) ⊆ Σ̄^r` (rank of the product on the fibre is `rank B = r ≤ r`), so
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodim.lean:73:codimension of the closed rank-`≤ r` product locus `Σ̄^r` is at most that of the fibre `mult⁻¹(B)`:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodim.lean:80:exact-rank fibre-bundle structure absent from Mathlib v4.29 (see the module docstring). No closure /
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/QSeriesThm55.lean:54:    simp only [Sigma.mk.injEq, Nat.add_sub_cancel_left, heq_eq_eq, and_true, true_and]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaCodim.lean:4:# `DLNFibre.Core.SigmaCodim` — the geometric codimension of the closed rank-`≤ r` locus
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaCodim.lean:15:`Core.SigmaComponents`); the per-orbit Voigt codim; the realizer of a minimising Kostant partition
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaCodim.lean:56:and `minimalPrimes_sigmaIdeal_eq` are both general in `r` (`Core.SigmaComponents`). `[IsAlgClosed k]`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:41:abbrev BaseChangeGroup (d : Fin (N + 1) → ℕ) : Type u :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:48:def baseChange (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d) : Tuple (k := k) d :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:52:@[simp] theorem baseChange_apply (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:58:    baseChange (1 : BaseChangeGroup (k := k) d) A = A := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:63:theorem baseChange_mul (P Q : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:69:instance : MulAction (BaseChangeGroup (k := k) d) (Tuple (k := k) d) where
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:75:@[simp] theorem smul_eq_baseChange (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:84:theorem submult_baseChange (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:110:theorem submult_smul (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:121:theorem rankPattern_baseChange (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:129:theorem rankPattern_smul (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean:152:def witnessBaseChange : BaseChangeGroup (k := ℤ) dWitness :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:99:    (P : BaseChangeGroup (k := k) d) : BaseChangeGroup (k := k) (fun l ↦ d l + d' l) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:112:    (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d) (B : Tuple (k := k) d') :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:138:    (horb : ∀ t : k, t ≠ 0 → ∃ P : BaseChangeGroup (k := k) d, P • U₀ = tupleEval F₀ t) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:160:noncomputable def smulPoly {d : Fin (N + 1) → ℕ} (Q : BaseChangeGroup (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:167:theorem tupleEval_smulPoly {d : Fin (N + 1) → ℕ} (Q : BaseChangeGroup (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:189:    (U D₀ D' : Tuple (k := k) d) (F : Tuple (k := Polynomial k) d) (Q : BaseChangeGroup (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:191:    (horb : ∀ t : k, t ≠ 0 → ∃ P : BaseChangeGroup (k := k) d, P • U = tupleEval F t) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:209:    (Q : BaseChangeGroup (k := k) (fun l ↦ d l + d' l)) (D' : Tuple (k := k) (fun l ↦ d l + d' l))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:211:    (horb : ∀ t : k, t ≠ 0 → ∃ P : BaseChangeGroup (k := k) d, P • U₀ = tupleEval F₀ t) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:288:    BaseChangeGroup (k := k) (intervalDim a e) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:340:    ∃ P : BaseChangeGroup (k := k) (intervalDim a e),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:512:    ∃ P : BaseChangeGroup (k := k) (intervalDim a e),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:558:    ∃ Q : BaseChangeGroup (k := k) (fun l ↦ intervalDim a e l + foldDim rest l),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:1092:    ∃ P : BaseChangeGroup (k := k) (fun l ↦ intervalDim a e l + intervalDim c b.castSucc l),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:1101:    ∃ Q : BaseChangeGroup (k := k) (fun l ↦ intervalDim a e l + intervalDim c b.castSucc l),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:1125:    ∃ Q : BaseChangeGroup (k := k)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:1192:example : ∃ P : BaseChangeGroup (k := ℚ) (intervalDim (0 : Fin 3) 2),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:1251:    ∃ P : BaseChangeGroup (k := ℚ) (fun l ↦ intervalDim (0 : Fin 3) 2 l + intervalDim 1 1 l),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:277:    {A | ∃ P : BaseChangeGroup (k := k) d, P • M = A} ⊆ orbitRankLocus M := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CThetaGeometric.lean:35:(`Core.SigmaStratification`); (ii) its irreducible components are the maximal orbit closures
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CThetaGeometric.lean:36:(`Core.SigmaComponents.minimalPrimes_sigmaIdeal_eq`); (iii) codimension-of-a-union =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CThetaGeometric.lean:38:(`Core.SigmaCodim.codimRepCanonical_productRankLocusLE_eq_cCodim`) and the top-component count
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Setup.lean:16:the rank loci and fibres are honest `Set (Tuple d)` for a *fixed* `d`. The ordered product is
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:8:`Rep_d` through the two end factors (here the full base-change group `BaseChangeGroup`; the inner units
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:37:/-- The det of a `BaseChangeGroup` value (a `Units` of the matrix ring) is a unit. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:38:theorem isUnit_det_baseChangeGroup (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:42:/-- **Rank of the endpoint-conjugated target is unchanged.** For `P : BaseChangeGroup` and any target
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:45:theorem rank_endpoint_conj (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:55:/-- **The exact-rank locus is the `H`-sweep of one fibre.** For a fixed rank-`r` target `E` and
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:63:with `mult A = P_N · E · P_0⁻¹`, and `image_smul_fibre` packages `A` as a translate of `fibre E`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:69:      ∃ P : BaseChangeGroup (k := k) d, A ∈ (fun A' ↦ P • A') '' (fibre d E) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:74:    exact ⟨P, by rw [image_smul_fibre, mem_fibre, ← hP]⟩
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:76:    rw [image_smul_fibre, mem_fibre] at hPA
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:81:theorem productRankLocus_eq_iUnion_smul_fibre (d : Fin (N + 1) → ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:85:      = ⋃ P : BaseChangeGroup (k := k) d, (fun A' ↦ P • A') '' (fibre d E) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:91:/-- **All rank-`r` fibres have the same codimension as `mult⁻¹(E)`.** Each `H`-translate of `fibre d
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:92:E` is `fibre d (P_N·E·P_0⁻¹)`, a rank-`r` fibre; `G1` (`codimRepCanonical_fibre_eq_of_rank_eq`, the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:98:    (P : BaseChangeGroup (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:2:import DLNFibre.Core.SigmaCodim
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:23:`rank(fibreJacobian) ≥ C+δ` generically on every component, those hypotheses discharge — via
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:102:rank-`r` target `B*`, then **every** rank-`r` target `B` has `codimRepCanonical (fibre d B) = v`. The
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:86:(`Equiv.uniqueSigma`), splits `Fin p ≃ Fin r ⊕ Fin (p−r)` and `Fin q ≃ Fin r ⊕ Fin (q−r)`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:90:  (Equiv.uniqueSigma _).trans <|
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:1:import DLNFibre.Core.SigmaStratification
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:7:# `DLNFibre.Core.SigmaComponents` — components of `Σ̄^r` and the count `θ` (Phase G3 / θ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean:10:set-level orbit stratification `Σ̄^r = ⋃_M Ō_M` (G2, `Core.SigmaStratification`) and the per-orbit
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ThetaComponentCount.lean:1:import DLNFibre.Core.SigmaComponents
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ThetaComponentCount.lean:7:`Core.SigmaComponents`), the combinatorial engine (`Core.CTheta`: `cCodim`, `numTop`,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CTheta.lean:34:closures) — is **now also formalised**: `Σ̄^r = ⋃_M Ō_M` (`Core.SigmaStratification`), its irreducible
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CTheta.lean:35:components are the orbit closures (`Core.SigmaComponents.minimalPrimes_sigmaIdeal_eq`),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CTheta.lean:36:`codim Σ̄^r = cCodim d r` (`Core.SigmaCodim.codimRepCanonical_productRankLocusLE_eq_cCodim`), and
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CTheta.lean:157:`Σ̄^r = productRankLocusLE d r` (`Core.SigmaCodim.codimRepCanonical_productRankLocusLE_eq_cCodim`,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CThetaGeometricPerm.lean:1:import DLNFibre.Core.SigmaCodim
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CThetaGeometricPerm.lean:12:* `codimRepCanonical_productRankLocusLE_eq_cCodim_enat` (`SigmaCodim`) — `codim Σ̄^r = (cCodim d r).toNat`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:2:import DLNFibre.Core.SigmaCodim
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:21:`hCatFibre`/`hCatSigma` in the base theorem; the primed variant discharges them from the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:45:relations `hCatFibre`/`hCatSigma` as explicit named hypotheses. The proof is the additive chain
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:57:    (hCatSigma : codimRepCanonical (productRankLocusLE (k := k) d r)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:67:  have hdimSigma : varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:76:  -- substitute `codim Σ̄^r = C`, `dim Σ̄^r = δ + dim F` into `hCatSigma`: `C + (δ + dim F) = card`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:77:  rw [hCsigma, hdimSigma] at hCatSigma
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:88:              + varietyDim (canonicalCoord d '' fibre d B)) := hCatSigma.symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:106:    (hSigmaNe : (canonicalCoord d '' productRankLocusLE (k := k) d r).Nonempty)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:116:    (codimRepCanonical_add_varietyDim_eq_card_of_nonempty hSigmaNe)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalStratumDim.lean:1:import DLNFibre.Core.SigmaCodim
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalStratumDim.lean:3:import DLNFibre.Core.SigmaStratification
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartFlatnessProbe.lean:13:probe for route **M-goingdown** of the rank-chart fibre-codimension build: localize F1's `multComap`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:1:import DLNFibre.Core.SigmaCodim
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:21:exact-rank good locus where the fibre dimension does not jump — generic flatness / generic
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:54:noncomputable def liftGauge (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:55:    BaseChangeGroup (k := MvPolynomial (RepCoord d) R) d :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:61:theorem liftGauge_mul (d : Fin (N + 1) → ℕ) (P Q : BaseChangeGroup (k := R) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:67:    liftGauge d (1 : BaseChangeGroup (k := R) d) = 1 := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:71:theorem liftGauge_inv (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:81:noncomputable def gaugeSub (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:88:theorem aeval_gaugeSub_genericTuple (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:115:theorem map_aeval_gaugeSub_mult (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:133:theorem mult_smul_commRing (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:143:theorem aeval_gaugeSub_multPoly (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:159:theorem liftGauge_val_eq (d : Fin (N + 1) → ℕ) (Q : BaseChangeGroup (k := R) d) (v : Fin (N + 1)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:167:theorem liftGauge_inv_val_eq (d : Fin (N + 1) → ℕ) (Q : BaseChangeGroup (k := R) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:177:theorem map_aeval_gaugeSub_liftGauge (d : Fin (N + 1) → ℕ) (P Q : BaseChangeGroup (k := R) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:195:theorem map_aeval_gaugeSub_baseChange (d : Fin (N + 1) → ℕ) (P Q : BaseChangeGroup (k := R) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:207:theorem aeval_gaugeSub_gaugeSub (d : Fin (N + 1) → ℕ) (P Q : BaseChangeGroup (k := R) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:219:noncomputable def gaugeEquiv (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:234:@[simp] theorem gaugeEquiv_apply (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:242:theorem gaugeEquiv_multPoly (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:260:    gaugeSub d (1 : BaseChangeGroup (k := R) d) x = X x := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:266:    gaugeEquiv d (1 : BaseChangeGroup (k := R) d) p = p := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:268:  have : aeval (R := R) (gaugeSub d (1 : BaseChangeGroup (k := R) d))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:280:def witnessGauge : BaseChangeGroup (k := ℤ) dConst := fun _ ↦ witnessUnit
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:9:import DLNFibre.Core.SigmaComponents
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:10:import DLNFibre.Core.SigmaCodim
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:4:# `DLNFibre.Core.FibreNormalForm` — same-rank ⟹ same fibre codimension (G1)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:18:   onto `fibre d (P_N · B · P_0⁻¹)` (`image_smul_fibre`).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:28:`codimRepCanonical_fibre_eq_of_rank_eq`: same rank ⟹ same fibre codimension.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:53:example (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:64:example [Infinite k] (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:77:theorem mult_smul (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:87:theorem image_smul_fibre (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:112:    (P : BaseChangeGroup (k := k) d) (Z : Set (Tuple (k := k) d)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:142:    (P : BaseChangeGroup (k := k) d) (Z : Set (Tuple (k := k) d)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:150:/-- **Codim-invariance of a fibre under the end-factor base change.** Combining `image_smul_fibre`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:154:    (P : BaseChangeGroup (k := k) d) (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:157:  rw [codimRepCanonical, codimRepCanonical, ← image_smul_fibre, codimRep_baseChange_image]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:282:    ∃ P : BaseChangeGroup (k := k) d,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:298:  -- assemble the BaseChangeGroup: `last N ↦ equivUnitMatrix eL`, `0 ↦ (equivUnitMatrix eR)⁻¹`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:299:  set P : BaseChangeGroup (k := k) d :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:314:/-! ## The headline: same rank ⟹ same fibre codimension -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:316:/-- **Same rank ⟹ same fibre codimension.** The geometric codimension of the multiplication-map
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:319:rank-`r` targets) to a single fibre. Needs `N ≥ 1` (`hN : 0 ≠ Fin.last N`): for `N = 0` the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:338:/-- The two `(2,2,2)`-witness rank-1 targets have equal fibre codimension. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:30:`hCatFibre`/`hCatSigma`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitCodim.lean:105:`Equiv.piCurry` (Sigma-currying `∀ i, (… × … → k) ↔ (RepCoord d → k)`). This is the coordinatisation
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveDegeneration.lean:85:    (horb : ∀ t : k, t ≠ 0 → ∃ P : BaseChangeGroup (k := k) d, P • U = tupleEval Fpoly t) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveDegeneration.lean:172:def boxMoveBaseChange {t : k} (ht : t ≠ 0) : BaseChangeGroup (k := k) boxDim :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveDegeneration.lean:201:    ∃ P : BaseChangeGroup (k := k) boxDim, P • boxMoveWitnessUp = boxMoveWitnessFamily t :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultDifferential.lean:108:    have hne : (⟨j', r, u⟩ : RepCoord d) ≠ ⟨i, s, t⟩ := fun h ↦ hj'i (congrArg Sigma.fst h)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultDifferential.lean:131:    have hne : (⟨j', u, c⟩ : RepCoord d) ≠ ⟨i, s, t⟩ := fun h ↦ hj'i (congrArg Sigma.fst h)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitKostant.lean:71:    rankFn d A = rankFn d B ↔ ∃ P : BaseChangeGroup (k := k) d, P • A = B := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitKostant.lean:89:  r A B := ∃ P : BaseChangeGroup (k := k) d, P • A = B
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitVariety.lean:36:  canonicalCoord d '' { A | ∃ P : BaseChangeGroup (k := k) d, P • M = A }
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitVariety.lean:40:    BaseChangeGroup (k := k) d → (RepCoord d → k) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitVariety.lean:174:def groupPoint {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d) : GroupCoord d → k :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitVariety.lean:178:theorem eval_genericMat {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d) (v : Fin (N + 1)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitVariety.lean:186:theorem isUnit_eval_groupDenom {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitVariety.lean:196:noncomputable def evalGroupRing {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitVariety.lean:202:@[simp] theorem evalGroupRing_algebraMap {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitVariety.lean:208:@[simp] theorem evalGroupRing_algebraMap_base {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitVariety.lean:216:theorem evalGroupRing_genericUnit {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitVariety.lean:226:    (P : BaseChangeGroup (k := k) d) (i : Fin N) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitVariety.lean:233:theorem evalGroupRing_genericUnitInv {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitVariety.lean:266:    (P : BaseChangeGroup (k := k) d) (g : MvPolynomial (RepCoord d) k) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitVariety.lean:297:    ∃ P : BaseChangeGroup (k := k) d, groupPoint P = x := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitVariety.lean:330:    have hzero : ∀ P : BaseChangeGroup (k := k) d, evalGroupRing P (orbitPullback M g) = 0 := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:45:    (P Q : BaseChangeGroup (k := k) d) (f : MvPolynomial (RepCoord d) k) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:56:    baseChangePullback (1 : BaseChangeGroup (k := k) d) f = f := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:65:    (P : BaseChangeGroup (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:76:    (P : BaseChangeGroup (k := k) d) (f : MvPolynomial (RepCoord d) k) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:105:    (P : BaseChangeGroup (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:116:    (P : BaseChangeGroup (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:142:    (P : BaseChangeGroup (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:150:    (P : BaseChangeGroup (k := k) d) (f : MvPolynomial (RepCoord d) k) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:164:    (P : BaseChangeGroup (k := k) d) : canonicalCoord d (P • M) ∈ orbitSet M :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:170:    (P : BaseChangeGroup (k := k) d) {f : MvPolynomial (RepCoord d) k} (hf : f ∈ orbitIdeal M) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:179:    (P : BaseChangeGroup (k := k) d) : orbitRing M →ₐ[k] k :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:186:    (P : BaseChangeGroup (k := k) d) (f : MvPolynomial (RepCoord d) k) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:195:    (P : BaseChangeGroup (k := k) d) : Ideal (orbitRing M) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:206:    (P : BaseChangeGroup (k := k) d) : (orbitPointIdeal M P).IsMaximal := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:213:    (P : BaseChangeGroup (k := k) d) : (orbitPointIdeal M P).IsPrime :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:220:    (P : BaseChangeGroup (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:236:    (P : BaseChangeGroup (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:255:    (P : BaseChangeGroup (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:278:    (M : Tuple (k := k) d) (P : BaseChangeGroup (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:297:    (P : BaseChangeGroup (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:311:  { p | ∃ P : BaseChangeGroup (k := k) d, p.asIdeal = orbitPointIdeal M P }
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:324:  have hg : ∀ P : BaseChangeGroup (k := k) d,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:488:    ∃ P : BaseChangeGroup (k := k) d, Algebra.IsSmoothAt k (orbitPointIdeal M P) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:10:the rank-`r` chart as a hypothesis. The certified pen-and-paper input (thread 16) is that the fibre
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:124:noncomputable def baseChangeSub {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:134:noncomputable def baseChangePullback {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:141:theorem eval_baseChangeSub {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:168:theorem eval_baseChangePullback {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:190:    (P : BaseChangeGroup (k := k) d) {y : RepCoord d → k} (hy : y ∈ orbitSet U) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean:200:    (P : BaseChangeGroup (k := k) d) {f : MvPolynomial (RepCoord d) k}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaStratification.lean:5:# `DLNFibre.Core.SigmaStratification` — the orbit stratification of `Σ̄^r` (Phase G2)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreJacobian.lean:28:* **`finrank_cotangentSpace_fibre_eq_finrank_ker`** (the tangent = ker identity) — the local
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreJacobian.lean:29:  cotangent space of the fibre ring at `A` has `k`-dimension `= finrank (ker (fibreJacobian))`,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreJacobian.lean:32:* **`finrank_ker_add_rank_fibreJacobianMatrix`** — the card-rank reading
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreJacobian.lean:110:equal to `finrank (ker (fibreJacobian d B A))`. Unconditional (no smoothness, no genericity),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreJacobian.lean:114:theorem finrank_cotangentSpace_fibre_eq_finrank_ker (d : Fin (N + 1) → ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreJacobian.lean:119:      = finrank k (LinearMap.ker (fibreJacobian d B A)) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreJacobian.lean:120:  finrank_cotangentSpace_eq_finrank_ker_jacobian (fibreGen d B) (canonicalCoord d A)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreJacobian.lean:123:/-- **The card-rank reading.** `finrank (ker (fibreJacobian)) + rank (fibreJacobianMatrix) =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreJacobian.lean:124:card (RepCoord d)`. H3b supplies `rank (fibreJacobianMatrix) = C + δ` at a generic `A`, giving
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreJacobian.lean:128:theorem finrank_ker_add_rank_fibreJacobianMatrix (d : Fin (N + 1) → ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreJacobian.lean:130:    finrank k (LinearMap.ker (fibreJacobian d B A)) + (fibreJacobianMatrix d B A).rank
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreJacobian.lean:132:  have h : finrank k (LinearMap.range (fibreJacobian d B A))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreJacobian.lean:133:      + finrank k (LinearMap.ker (fibreJacobian d B A)) = Fintype.card (RepCoord d) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreJacobian.lean:135:  have hr : finrank k (LinearMap.range (fibreJacobian d B A)) = (fibreJacobianMatrix d B A).rank :=

exec
/bin/bash -lc "sed -n '1,220p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ProductRankLocusSweep.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 exited 2 in 0ms:
sed: can't read /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ProductRankLocusSweep.lean: No such file or directory

codex
One correction to the target shape: the chart you get from `D(Δ)` is naturally a chart of the exact-rank stratum inside the closed rank-`≤ r` locus. Since `varietyDim` is closure dimension, you must keep track of whether the localized ring is for `Σ^{≤r} ∩ D(Δ)` or for `Σ^r ∩ D(Δ)`; on `D(Δ)` these have the same points because rank `≤ r` plus the nonzero `r`-minor implies rank exactly `r`.
exec
/bin/bash -lc "sed -n '1,140p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
import DLNFibre.Core.FibreNormalForm

/-!
# `DLNFibre.Core.EndBaseChangeSweep` — the homogeneous sweep `Σ^r = H·F` (route c scaffolding)

The structural scaffolding of the **equivariant homogeneous sweep** route to Lehalleur–Rimányi Lemma
4.6's fibre dimension (thread 27's certificate). The endpoint group `H = GL_{d_N} × GL_{d_0}` acts on
`Rep_d` through the two end factors (here the full base-change group `BaseChangeGroup`; the inner units
telescope away in `mult`), `mult` is `H`-equivariant (`FibreNormalForm.mult_smul`), and any two rank-`r`
matrices are `H`-equivalent (`exists_baseChange_of_rank_eq`). Hence the **exact-rank locus is one
`H`-sweep of a single fibre**:

> `productRankLocus d r = ⋃_{P} (P • ·) '' (fibre d E)`   for any fixed rank-`r` target `E` (`N ≥ 1`).

This module proves that sweep identity (the reachable structural part of route c). The **dimension
consequence** `varietyDim (productRankLocus d r) = δ + varietyDim (fibre d E)` is the *one genuinely
hard rung* — an orbit/quotient-dimension count; whether it is buildable from the engine's
`OrbitPullbackDim` orbit-dimension method or needs a Mathlib-absent base-change/product-dimension
theorem is under adjudication. It is **NOT** proved here; the downstream `codim F = C+δ` assembly
(`codimRepCanonical_fibre_eq_cCodim_add_shift_of_sweep`) carries it (and the closure/density bridge
`dim Σ^r = dim Σ̄^r`) as **explicit named hypotheses** (the conditional-bank pattern), so everything
*around* the residual is machine-checked. Nothing here claims the dimension identity.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## Rank is invariant under the endpoint base change -/

/-- The det of a `BaseChangeGroup` value (a `Units` of the matrix ring) is a unit. -/
theorem isUnit_det_baseChangeGroup (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := k) d)
    (v : Fin (N + 1)) : IsUnit (Units.val (P v)).det :=
  (P v).isUnit.map (Matrix.detMonoidHom)

/-- **Rank of the endpoint-conjugated target is unchanged.** For `P : BaseChangeGroup` and any target
`B`, `rank (P_N · B · P_0⁻¹) = rank B`: left/right multiplication by the invertible end-vertex units
preserves rank (`rank_mul_eq_right_of_isUnit_det` / `rank_mul_eq_left_of_isUnit_det`). -/
theorem rank_endpoint_conj (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := k) d)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) :
    (Units.val (P (Fin.last N)) * B * Units.val ((P 0)⁻¹)).rank = B.rank := by
  rw [Matrix.mul_assoc, Matrix.rank_mul_eq_right_of_isUnit_det _ _
        (isUnit_det_baseChangeGroup d P (Fin.last N)),
      Matrix.rank_mul_eq_left_of_isUnit_det _ _
        (by simpa using isUnit_det_baseChangeGroup d P⁻¹ 0)]

/-! ## The sweep identity `Σ^r = H · F` -/

/-- **The exact-rank locus is the `H`-sweep of one fibre.** For a fixed rank-`r` target `E` and
`N ≥ 1`, the exact-rank locus `productRankLocus d r = {A : rank(mult A) = r}` is exactly the union,
over the endpoint base-change group, of the translates of the fibre `mult⁻¹(E)`:

> `A ∈ productRankLocus d r ↔ ∃ P, A ∈ (P • ·) '' (fibre d E)`.

`(←)` `mult` carries a translate of `fibre E` to `P_N · E · P_0⁻¹`, of rank `= rank E = r`
(`rank_endpoint_conj`). `(→)` `rank(mult A) = r = E.rank`, so `exists_baseChange_of_rank_eq` gives `P`
with `mult A = P_N · E · P_0⁻¹`, and `image_smul_fibre` packages `A` as a translate of `fibre E`. -/
theorem mem_productRankLocus_iff_mem_sweep (d : Fin (N + 1) → ℕ)
    (hN : (0 : Fin (N + 1)) ≠ Fin.last N)
    (E : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) {r : ℕ} (hE : E.rank = r)
    (A : Tuple (k := k) d) :
    A ∈ productRankLocus d r ↔
      ∃ P : BaseChangeGroup (k := k) d, A ∈ (fun A' ↦ P • A') '' (fibre d E) := by
  constructor
  · intro hA
    rw [mem_productRankLocus] at hA
    obtain ⟨P, hP⟩ := exists_baseChange_of_rank_eq d hN E (mult d A) (by rw [hE, hA])
    exact ⟨P, by rw [image_smul_fibre, mem_fibre, ← hP]⟩
  · rintro ⟨P, hPA⟩
    rw [image_smul_fibre, mem_fibre] at hPA
    rw [mem_productRankLocus, hPA, rank_endpoint_conj, hE]

/-- **The sweep identity (set form).** `productRankLocus d r = ⋃_P (P • ·) '' (fibre d E)` for a fixed
rank-`r` target `E`. The set-level statement of `mem_productRankLocus_iff_mem_sweep`. -/
theorem productRankLocus_eq_iUnion_smul_fibre (d : Fin (N + 1) → ℕ)
    (hN : (0 : Fin (N + 1)) ≠ Fin.last N)
    (E : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) {r : ℕ} (hE : E.rank = r) :
    productRankLocus d r
      = ⋃ P : BaseChangeGroup (k := k) d, (fun A' ↦ P • A') '' (fibre d E) := by
  ext A
  rw [Set.mem_iUnion, mem_productRankLocus_iff_mem_sweep d hN E hE]

/-! ## Each translate is isomorphic to the fibre `F` (codim-preserving) -/

/-- **All rank-`r` fibres have the same codimension as `mult⁻¹(E)`.** Each `H`-translate of `fibre d
E` is `fibre d (P_N·E·P_0⁻¹)`, a rank-`r` fibre; `G1` (`codimRepCanonical_fibre_eq_of_rank_eq`, the
landed flatness-free homogeneity) makes its codimension equal to that of `mult⁻¹(E)`. The
codim-constancy that lets the sweep reduce to a single fibre. -/
theorem codimRepCanonical_fibre_translate_eq [Infinite k] (d : Fin (N + 1) → ℕ)
    (hN : (0 : Fin (N + 1)) ≠ Fin.last N)
    (E : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k)
    (P : BaseChangeGroup (k := k) d) :
    codimRepCanonical (fibre d (Units.val (P (Fin.last N)) * E * Units.val ((P 0)⁻¹)))
      = codimRepCanonical (fibre d E) :=
  codimRepCanonical_fibre_eq_of_rank_eq d hN _ E (rank_endpoint_conj d P E)

end DLNFibre.Core

exec
/bin/bash -lc "sed -n '1,220p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.MvPolynomial.Rename
import DLNFibre.Core.RankLocusClosed
import DLNFibre.Core.MultComorphism
import DLNFibre.Core.SigmaComponents
import DLNFibre.Core.SigmaCodim
import DLNFibre.Core.DeterminantalStratumDim
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.RingTheory.Ideal.Height

/-!
# `DLNFibre.Core.DeterminantalChartRing` — the bordered Schur minor (G2-2 foundation)

The ring-level lift of G2-1's matrix Schur relation. The genuinely new piece is the **bordered
Schur minor identity**, valid over any commutative ring (no invertibility of the pivot block):

> `det [[Δ, u], [v, d]] = d · det Δ − (v · adjugate Δ · u)`  (the `r×r` block `Δ`, a column `u`,
> a row `v`, a scalar corner `d`).

This is the polynomial that, on the determinantal locus `Mat^{rk ≤ r}`, forces the Schur relation
`B22 = B21 Δ⁻¹ B12` once `det Δ` is inverted: each entry `d·B22_{ab} − (B21 adjΔ B12)_{ab}` is an
`(r+1)×(r+1)` minor, hence vanishes on `Σ̄^r` (rank `≤ r`). It is the generator-free handle on the
localized base presentation — it avoids any determinantal-ideal generating-set theory (absent in
Mathlib v4.29), reducing the base presentation to this single explicit minor + height comparison.

**The route to the identity (no `Invertible Δ`).** Both sides are integer-polynomial identities in
the entries: over the universal `MvPolynomial` matrix ring (a domain) the identity holds in the
fraction field, where `Δ` is invertible and `det_fromBlocks₁₁` applies; specialize back by the ring
hom into the target. We use the `mul_adjugate` form (`Δ · adjΔ = det Δ • 1`) so the statement makes
sense over any commutative ring.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

universe u

variable {α : Type u} [CommRing α] {r : ℕ}

/-! ## The bordered Schur minor identity (over any commutative ring) -/

/-- The bordered Schur minor identity as a predicate on the four blocks, so it transfers along ring
homs (`fromBlocks`, `det`, `adjugate`, `*`, `-` all commute with `RingHom.mapMatrix`). -/
def BorderedId {β : Type*} [CommRing β] (Δ : Matrix (Fin r) (Fin r) β) (u : Matrix (Fin r) Unit β)
    (v : Matrix Unit (Fin r) β) (d : Matrix Unit Unit β) : Prop :=
  (fromBlocks Δ u v d).det = d () () * Δ.det - (v * Δ.adjugate * u) () ()

/-- `BorderedId` holds over a field when the pivot is nonsingular (`det Δ ≠ 0`), via the Mathlib
Schur determinant `det_fromBlocks₁₁` and the adjugate relation `det Δ • Δ⁻¹ = adjugate Δ`. -/
theorem borderedId_of_det_ne_zero {K : Type*} [Field K] (Δ : Matrix (Fin r) (Fin r) K)
    (u : Matrix (Fin r) Unit K) (v : Matrix Unit (Fin r) K) (d : Matrix Unit Unit K)
    (hΔ : Δ.det ≠ 0) : BorderedId Δ u v d := by
  haveI : Invertible Δ := Δ.invertibleOfIsUnitDet (Ne.isUnit hΔ)
  unfold BorderedId
  rw [det_fromBlocks₁₁,
    show (d - v * ⅟Δ * u).det = (d - v * ⅟Δ * u) () () from by simp [det_unique]]
  have hadj : Δ.det • (⅟Δ : Matrix (Fin r) (Fin r) K) = Δ.adjugate := by
    have h1 : Δ * Δ.adjugate = Δ.det • (1 : Matrix (Fin r) (Fin r) K) := mul_adjugate Δ
    have : (⅟Δ : Matrix (Fin r) (Fin r) K) * (Δ * Δ.adjugate) = ⅟Δ * (Δ.det • 1) := by rw [h1]
    rw [← mul_assoc, invOf_mul_self, one_mul, Matrix.mul_smul, Matrix.mul_one] at this
    exact this.symm
  have hvu : Δ.det • (v * ⅟Δ * u) = v * Δ.adjugate * u := by
    rw [← hadj, Matrix.mul_smul, Matrix.smul_mul]
  rw [Matrix.sub_apply, mul_sub]
  congr 1
  · ring
  · have := congrArg (fun M : Matrix Unit Unit K => M () ()) hvu
    simpa [Matrix.smul_apply, mul_comm] using this

/-- `BorderedId` transfers along a ring hom `f : β →+* γ`: a polynomial identity in the entries,
built from `fromBlocks`, `det`, `adjugate`, `*`, `-`, all commuting with `RingHom.mapMatrix`. -/
theorem borderedId_map {β γ : Type*} [CommRing β] [CommRing γ] (f : β →+* γ)
    {Δ : Matrix (Fin r) (Fin r) β} {u : Matrix (Fin r) Unit β}
    {v : Matrix Unit (Fin r) β} {d : Matrix Unit Unit β}
    (h : BorderedId Δ u v d) :
    BorderedId (Δ.map f) (u.map f) (v.map f) (d.map f) := by
  unfold BorderedId at h ⊢
  -- both sides equal `f` applied to the corresponding un-mapped piece
  have hlhs : (fromBlocks (Δ.map f) (u.map f) (v.map f) (d.map f)).det
      = f (fromBlocks Δ u v d).det := by
    rw [← fromBlocks_map Δ u v d f]; exact (RingHom.map_det f (fromBlocks Δ u v d)).symm
  have hrhs : (d.map f) () () * (Δ.map f).det - (v.map f * (Δ.map f).adjugate * u.map f) () ()
      = f (d () () * Δ.det - (v * Δ.adjugate * u) () ()) := by
    have hadj : (Δ.map f).adjugate = (Δ.adjugate).map f := (RingHom.map_adjugate f Δ).symm
    have hdet : (Δ.map f).det = f Δ.det := (RingHom.map_det f Δ).symm
    rw [hadj, ← Matrix.map_mul, ← Matrix.map_mul, hdet]
    simp only [map_sub, map_mul, Matrix.map_apply]
  rw [hlhs, hrhs, h]

/-- `BorderedId` reflects along an injective ring hom: if it holds for the `f`-images of the blocks
and `f` is injective, it holds for the blocks. (Both sides of `BorderedId` are `f`-images of the
corresponding un-mapped pieces, so `f`-injectivity cancels.) -/
theorem borderedId_of_map {β γ : Type*} [CommRing β] [CommRing γ] (f : β →+* γ)
    (hf : Function.Injective f) {Δ : Matrix (Fin r) (Fin r) β} {u : Matrix (Fin r) Unit β}
    {v : Matrix Unit (Fin r) β} {d : Matrix Unit Unit β}
    (h : BorderedId (Δ.map f) (u.map f) (v.map f) (d.map f)) :
    BorderedId Δ u v d := by
  unfold BorderedId at h ⊢
  apply hf
  rw [map_sub, map_mul]
  rw [show f (fromBlocks Δ u v d).det
          = (fromBlocks (Δ.map f) (u.map f) (v.map f) (d.map f)).det from by
        rw [← fromBlocks_map Δ u v d f]; exact RingHom.map_det f (fromBlocks Δ u v d),
      show f Δ.det = (Δ.map f).det from RingHom.map_det f Δ,
      show f (d () ()) = (d.map f) () () from rfl,
      show f ((v * Δ.adjugate * u) () ())
          = (v.map f * (Δ.map f).adjugate * u.map f) () () from by
        rw [show (Δ.map f).adjugate = (Δ.adjugate).map f from (RingHom.map_adjugate f Δ).symm,
          ← Matrix.map_mul, ← Matrix.map_mul]; rfl]
  exact h

/-- **Bordered Schur minor identity (general commutative ring).** The determinant of the bordered
`(r+1)×(r+1)` matrix `[[Δ, u], [v, d]]` (`r×r` block `Δ`, column `u`, row `v`, scalar corner `d`) is
`d · det Δ − v ⬝ adjugate Δ ⬝ u`. Valid over any commutative ring — no invertibility of `Δ`. Proved
by the universal-coefficient route: the generic `(r+1)×(r+1)` matrix over `ℤ` is a domain whose
fraction field has the (nonzero) generic pivot `det Δ` invertible, where `det_fromBlocks₁₁` applies;
the identity then descends (injective `algebraMap`) and specialises (entry evaluation). -/
theorem det_fromBlocks_scalar_eq (Δ : Matrix (Fin r) (Fin r) α) (u : Matrix (Fin r) Unit α)
    (v : Matrix Unit (Fin r) α) (d : Matrix Unit Unit α) :
    BorderedId Δ u v d := by
  classical
  -- the generic (r+1)×(r+1) matrix `A'` over `ℤ`, and its four blocks
  set D := MvPolynomial ((Fin r ⊕ Unit) × (Fin r ⊕ Unit)) ℤ with hD
  set A' : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) D := mvPolynomialX _ _ ℤ with hA'
  set Δ' := A'.toBlocks₁₁ with hΔ'
  set u' := A'.toBlocks₁₂ with hu'
  set v' := A'.toBlocks₂₁ with hv'
  set d' := A'.toBlocks₂₂ with hd'
  -- Step 1: `BorderedId Δ' u' v' d'` over the domain `D`, via its fraction field `K`.
  have hgen : BorderedId Δ' u' v' d' := by
    have hinj : Function.Injective (algebraMap D (FractionRing D)) :=
      IsFractionRing.injective D (FractionRing D)
    refine borderedId_of_map (algebraMap D (FractionRing D)) hinj ?_
    -- over the field K, the mapped pivot `Δ'` is nonsingular
    apply borderedId_of_det_ne_zero
    -- det (Δ'.map (algebraMap D K)) = algebraMap _ _ (det Δ') ≠ 0, since det Δ' ≠ 0 in the domain D
    rw [show (Δ'.map (algebraMap D (FractionRing D))).det
          = algebraMap D (FractionRing D) Δ'.det from (RingHom.map_det _ Δ').symm]
    rw [Ne, IsFractionRing.to_map_eq_zero_iff (R := D) (K := FractionRing D)]
    -- det Δ' ≠ 0: `Δ'` is the top-left generic block = renamed generic `r×r` matrix.
    have hren : Δ' = (mvPolynomialX (Fin r) (Fin r) ℤ).map
        (rename (fun p : Fin r × Fin r => (Sum.inl p.1, Sum.inl p.2))) := by
      ext i j
      simp [hΔ', hA', Matrix.toBlocks₁₁, mvPolynomialX_apply, rename_X]
    rw [hren, show ((mvPolynomialX (Fin r) (Fin r) ℤ).map
          (rename (fun p : Fin r × Fin r => (Sum.inl p.1, Sum.inl p.2)))).det
        = rename (fun p : Fin r × Fin r => (Sum.inl p.1, Sum.inl p.2))
            (mvPolynomialX (Fin r) (Fin r) ℤ).det from
          (AlgHom.map_det (rename (fun p : Fin r × Fin r => (Sum.inl p.1, Sum.inl p.2))) _).symm]
    rw [rename_eq_zero_iff_of_injective]
    · exact det_mvPolynomialX_ne_zero (Fin r) ℤ
    · intro a b hab
      have h2 : a.1 = b.1 ∧ a.2 = b.2 := by simpa using hab
      exact Prod.ext h2.1 h2.2
  -- Step 2: specialise `A'` to the given blocks via the entry-evaluation ring hom.
  set e : D →+* α := MvPolynomial.eval₂Hom (Int.castRingHom α)
    (fun p : (Fin r ⊕ Unit) × (Fin r ⊕ Unit) => (fromBlocks Δ u v d) p.1 p.2) with he
  have hmap : A'.map e = fromBlocks Δ u v d := by
    have := mvPolynomialX_map_eval₂ (Int.castRingHom α)
      (S := α) (m := Fin r ⊕ Unit) (n := Fin r ⊕ Unit) (fromBlocks Δ u v d)
    simpa [hA', he, MvPolynomial.eval₂Hom, MvPolynomial.eval₂] using this
  -- the four blocks map correctly (each is a `toBlocks` of `A'`, and `A'.map e = fromBlocks …`)
  have hentry : ∀ x y, (A'.map e) x y = (fromBlocks Δ u v d) x y := fun x y => by rw [hmap]
  have hbΔ : Δ'.map e = Δ := by
    rw [hΔ']; ext i j; simpa [Matrix.toBlocks₁₁] using hentry (Sum.inl i) (Sum.inl j)
  have hbu : u'.map e = u := by
    rw [hu']; ext i j; simpa [Matrix.toBlocks₁₂] using hentry (Sum.inl i) (Sum.inr j)
  have hbv : v'.map e = v := by
    rw [hv']; ext i j; simpa [Matrix.toBlocks₂₁] using hentry (Sum.inr i) (Sum.inl j)
  have hbd : d'.map e = d := by
    rw [hd']; ext i j; simpa [Matrix.toBlocks₂₂] using hentry (Sum.inr i) (Sum.inr j)
  have := borderedId_map e hgen
  rwa [hbΔ, hbu, hbv, hbd] at this

/-! ## The Schur relation vanishes on the rank-`≤ r` locus (the bridge to the base ideal) -/

/-- **The Schur expression is an `(r+1)`-minor, hence vanishes on `Mat^{rk ≤ r}`.** For a matrix
`M : Mat_{p×q}` over a field with `rank M ≤ r`, any choice of pivot rows `pr`, pivot columns `pc`,
and one extra row `a`, column `b`, the Schur expression
`M a b · det (M[pr,pc]) − (M[a,−]ᵀ ⬝ adjugate M[pr,pc] ⬝ M[−,b])` is zero: it is (by the bordered
Schur minor identity) the determinant of the `(r+1)×(r+1)` bordered submatrix, which vanishes since
`rank M ≤ r`. This is the polynomial that, on the pivot chart (`det M[pr,pc]` inverted), forces the
Schur relation `B22 = B21 Δ⁻¹ B12`. -/
theorem schur_expr_eq_zero_of_rank_le {k : Type u} [Field k] {p q r : ℕ}
    {M : Matrix (Fin p) (Fin q) k} (hr : M.rank ≤ r)
    (pr : Fin r → Fin p) (pc : Fin r → Fin q) (a : Fin p) (b : Fin q) :
    (Matrix.of (fun _ _ : Unit ↦ M a b) : Matrix Unit Unit k) () ()
        * (M.submatrix pr pc).det
      - ((Matrix.of (fun _ : Unit ↦ fun j : Fin r ↦ M a (pc j)) : Matrix Unit (Fin r) k)
          * (M.submatrix pr pc).adjugate
          * (Matrix.of (fun i : Fin r ↦ fun _ : Unit ↦ M (pr i) b) : Matrix (Fin r) Unit k))
            () () = 0 := by
  -- the bordered submatrix over `Fin r ⊕ Unit`
  set Δ : Matrix (Fin r) (Fin r) k := M.submatrix pr pc with hΔ
  set u : Matrix (Fin r) Unit k := Matrix.of (fun i _ ↦ M (pr i) b) with hu
  set v : Matrix Unit (Fin r) k := Matrix.of (fun _ j ↦ M a (pc j)) with hv
  set d : Matrix Unit Unit k := Matrix.of (fun _ _ ↦ M a b) with hd
  -- `fromBlocks Δ u v d` is the bordered `(r+1)×(r+1)` submatrix of `M`
  have hborder : fromBlocks Δ u v d
      = M.submatrix (Sum.elim pr (fun _ ↦ a)) (Sum.elim pc (fun _ ↦ b)) := by
    ext i j; cases i <;> cases j <;> rfl
  -- its determinant is the Schur expression (bordered Schur minor identity)
  have hid : (fromBlocks Δ u v d).det = d () () * Δ.det - (v * Δ.adjugate * u) () () :=
    det_fromBlocks_scalar_eq Δ u v d
  -- and it vanishes, being an `(r+1)`-minor of a rank-`≤ r` matrix
  have hzero : (fromBlocks Δ u v d).det = 0 := by
    rw [hborder]
    -- reindex `Fin r ⊕ Unit ≃ Fin (r+1)` to apply `submatrix_det_eq_zero_of_rank_le`
    have e : (Fin r ⊕ Unit) ≃ Fin (r + 1) :=
      (Equiv.sumCongr (Equiv.refl (Fin r)) finOneEquiv.symm).trans finSumFinEquiv
    rw [← det_submatrix_equiv_self e.symm, submatrix_submatrix]
    exact submatrix_det_eq_zero_of_rank_le hr _ _
  rw [hid] at hzero; exact hzero

exec
/bin/bash -lc "sed -n '1,330p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
import DLNFibre.Core.MultComorphism
import DLNFibre.Core.BaseChange

/-!
# `DLNFibre.Core.EndpointNormalization` — the gauge-change `AlgEquiv` (R2-3b-3)

The second rung of the deep product trivialization `e`. On the **unquotiented** coordinate ring
`MvPolynomial (RepCoord d) R` over an **arbitrary** commutative ring `R`, the gauge-change map is the
linear coordinate substitution implementing the vertex-unit conjugation action
`Aᵢ ↦ P_{i+1} · Aᵢ · P_i⁻¹` of `Core.BaseChange.baseChange` on the generic tuple. For the endpoint
normalization of the paper's route, the gauge `P` is identity at every interior vertex and carries
`H` at the source vertex `0`, `L⁻¹` at the target vertex `Fin.last N`: then
`mult(Ã) = L⁻¹ · mult(A) · H⁻¹`, normalizing the two endpoint factors only. Kept GENERAL in the gauge
`P` (one invertible matrix per vertex over `R`) so R2-3b-4 instantiates it with the Schur-data
unipotents.

The deliverables, for a fixed dimension vector `d : Fin (N + 1) → ℕ` over `[CommRing R]` and a gauge
`P : ∀ v, (Matrix (Fin (d v)) (Fin (d v)) R)ˣ`:

1. `gaugeSub d P` — the coordinate substitution `RepCoord d → MvPolynomial (RepCoord d) R`: the
   `⟨i, (r, c)⟩` entry of `baseChange (P.map C) (genericTuple d)`, i.e. the entries of
   `P_{i+1} · Xᵢ · P_i⁻¹` with the unit matrices pushed into the coefficient ring by `C`.
2. `gaugeEquiv d P` — the coordinate-change `AlgEquiv` of `MvPolynomial (RepCoord d) R`, assembled by
   `AlgEquiv.ofAlgHom` from `aeval (gaugeSub P)` and `aeval (gaugeSub P⁻¹)`. The round-trips collapse
   by the group-action laws `baseChange_mul` / `baseChange_one` on the generic tuple.
3. The **mult-transport** `aeval_gaugeSub_multPoly` : `aeval (gaugeSub P) (multPoly d r c) =
   (P_last.val.map C · Matrix.of (multPoly d) · (P 0)⁻¹.val.map C) r c` — the generic product matrix
   transforms by the two end-vertex gauges (interior units telescope away, `mult_smul`). For the
   endpoint normalization this is `L⁻¹ · multPoly · H⁻¹` (the bridge R2-3b-4 needs to turn
   `mult(A) = LEH` into `mult(Ã) = E`).

The `N = 1` coincidence (first factor = last factor) is automatic: `baseChange` is defined uniformly
per edge from both endpoint vertices, so the single edge `0` of `Fin 1` already carries both end
gauges.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`. The gauge is over the arbitrary
coefficient ring `R`; nothing here needs a field, `IsAlgClosed`, or `Infinite` (in particular we
avoid `baseChangePullback`, which carries `[Infinite k]` from polynomial-function ext).
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

universe u

variable {R : Type u} [CommRing R] {N : ℕ}

/-! ## Lifting a gauge into the coefficient ring -/

/-- Lift a gauge `P : ∀ v, (Matrix (Fin (d v)) (Fin (d v)) R)ˣ` to one over the coordinate ring
`MvPolynomial (RepCoord d) R` by pushing each unit matrix through `C` (the `RingHom.mapMatrix` of the
inclusion `C : R →+* MvPolynomial (RepCoord d) R`). -/
noncomputable def liftGauge (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d) :
    BaseChangeGroup (k := MvPolynomial (RepCoord d) R) d :=
  fun v ↦ Units.map (RingHom.mapMatrix (C : R →+* MvPolynomial (RepCoord d) R)).toMonoidHom (P v)

/-- `liftGauge` is a group homomorphism on the gauge group (it lifts `Units.map` of a monoid hom,
pointwise). Stated as the two facts the round-trip needs: it preserves `1` and `⁻¹` pointwise via the
defining `Units.map`. -/
theorem liftGauge_mul (d : Fin (N + 1) → ℕ) (P Q : BaseChangeGroup (k := R) d) :
    liftGauge d (P * Q) = liftGauge d P * liftGauge d Q := by
  funext v
  simp only [liftGauge, Pi.mul_apply, map_mul]

@[simp] theorem liftGauge_one (d : Fin (N + 1) → ℕ) :
    liftGauge d (1 : BaseChangeGroup (k := R) d) = 1 := by
  funext v
  simp only [liftGauge, Pi.one_apply, map_one]

theorem liftGauge_inv (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d) :
    liftGauge d (P⁻¹) = (liftGauge d P)⁻¹ := by
  funext v
  simp only [liftGauge, Pi.inv_apply, map_inv]

/-! ## The gauge substitution -/

/-- **The gauge substitution** `gaugeSub d P : RepCoord d → MvPolynomial (RepCoord d) R`: the
`⟨i, (r, c)⟩` coordinate maps to the `(r, c)` entry of the gauged generic factor
`baseChange (liftGauge d P) (genericTuple d) i = P_{i+1} · Xᵢ · P_i⁻¹` (units lifted by `C`). -/
noncomputable def gaugeSub (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d) :
    RepCoord d → MvPolynomial (RepCoord d) R :=
  fun x ↦ baseChange (liftGauge d P) (genericTuple d) x.1 x.2.1 x.2.2

/-- `aeval (gaugeSub P)` carries the generic factor `genericTuple i` to the gauged factor
`baseChange (liftGauge d P) (genericTuple d) i`. The generator goes to the corresponding entry by
definition of `gaugeSub`; `aeval_X` evaluates it. -/
theorem aeval_gaugeSub_genericTuple (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
    (i : Fin N) :
    (genericTuple d i).map (aeval (R := R) (gaugeSub d P))
      = baseChange (liftGauge d P) (genericTuple d) i := by
  funext r c
  rw [Matrix.map_apply, genericTuple_apply, aeval_X, gaugeSub]

/-! ## The ring hom commutes with the prefix product -/

/-- A coordinate substitution commutes with the generic prefix product: applying `aeval φ`
(rectangular `Matrix.map`) to `multPrefix (genericTuple d) j` gives the prefix product of the image
tuple `Ã i = (genericTuple d i).map (aeval φ)`. The `aeval`-analog of
`Core.MultComorphism.map_eval_multPrefix`. -/
theorem map_aeval_multPrefix (d : Fin (N + 1) → ℕ)
    (φ : RepCoord d → MvPolynomial (RepCoord d) R) (j : Fin (N + 1)) :
    (multPrefix d (genericTuple d) j).map (aeval (R := R) φ)
      = multPrefix d (fun i ↦ (genericTuple d i).map (aeval (R := R) φ)) j := by
  induction j using Fin.induction with
  | zero =>
    simp only [multPrefix_zero]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  | succ i ih =>
    rw [multPrefix_succ, multPrefix_succ, Matrix.map_mul, ih]

/-- The full generic product under `aeval (gaugeSub P)` is `mult` of the gauged generic tuple:
`(Matrix.of (multPoly d)).map (aeval (gaugeSub P)) = mult d (baseChange (liftGauge d P)
(genericTuple d))`. Combines `map_aeval_multPrefix` with `aeval_gaugeSub_genericTuple`. -/
theorem map_aeval_gaugeSub_mult (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d) :
    (Matrix.of (multPoly d)).map (aeval (R := R) (gaugeSub d P))
      = mult d (baseChange (liftGauge d P) (genericTuple d)) := by
  have hof : (Matrix.of (multPoly d) : Matrix _ _ (MvPolynomial (RepCoord d) R))
      = multPrefix d (genericTuple d) (Fin.last N) := by
    funext r c; rfl
  have htup : (fun i ↦ (genericTuple d i).map (aeval (R := R) (gaugeSub d P)))
      = baseChange (liftGauge d P) (genericTuple d) := by
    funext i; exact aeval_gaugeSub_genericTuple d P i
  rw [hof, map_aeval_multPrefix d (gaugeSub d P) (Fin.last N), htup]
  rfl

/-! ## The mult-transport -/

/-- **mult-equivariance over a `CommRing`.** `mult d (P • A) = P_last · mult d A · P_0⁻¹`: the
interior units of the base change telescope away (`submult_baseChange` at the full interval,
through `mult_eq_submult`). The `Core.FibreNormalForm.mult_smul` proof is over a `Field`; this is
the same statement over the weaker `CommRing` (the proof uses only `CommRing` facts). -/
theorem mult_smul_commRing (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
    (A : Tuple (k := R) d) :
    mult d (baseChange P A)
      = Units.val (P (Fin.last N)) * mult d A * Units.val ((P 0)⁻¹) := by
  rw [mult_eq_submult, mult_eq_submult, submult_baseChange]

/-- **The mult-transport.** Applying `aeval (gaugeSub P)` to the generic product entry `multPoly d r
c` gives the `(r, c)` entry of `P_last · Matrix.of (multPoly d) · P_0⁻¹` (the end-vertex units lifted
by `C`); the interior units telescope away (`mult_smul`). For the endpoint normalization
(`P_0 = H`, `P_last = L⁻¹`, interior `= 1`) this is `L⁻¹ · multPoly · H⁻¹`. -/
theorem aeval_gaugeSub_multPoly (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
    (r : Fin (d (Fin.last N))) (c : Fin (d 0)) :
    aeval (R := R) (gaugeSub d P) (multPoly d r c)
      = ((Units.val (liftGauge d P (Fin.last N)) * Matrix.of (multPoly d)
            * Units.val ((liftGauge d P 0)⁻¹)
          : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) (MvPolynomial (RepCoord d) R)) r c) := by
  have h : aeval (R := R) (gaugeSub d P) (multPoly d r c)
      = ((Matrix.of (multPoly d)).map (aeval (R := R) (gaugeSub d P))) r c := rfl
  rw [h, map_aeval_gaugeSub_mult d P,
    mult_smul_commRing d (liftGauge d P) (genericTuple d)]
  rfl

/-! ## The composition law and the gauge `AlgEquiv` -/

/-- The entries of `Units.val (liftGauge d Q v)` are `C`-images: `(liftGauge d Q v).val = (Q v).val.map
C` (it is `Units.map (C.mapMatrix)` of `Q v`). -/
theorem liftGauge_val_eq (d : Fin (N + 1) → ℕ) (Q : BaseChangeGroup (k := R) d) (v : Fin (N + 1)) :
    Units.val (liftGauge d Q v)
      = (Units.val (Q v)).map (C : R →+* MvPolynomial (RepCoord d) R) := by
  show Units.val (Units.map _ (Q v)) = _
  rw [Units.coe_map]
  rfl

/-- The entries of `Units.val ((liftGauge d Q v)⁻¹)` are `C`-images: `= (Q v)⁻¹.val.map C`. -/
theorem liftGauge_inv_val_eq (d : Fin (N + 1) → ℕ) (Q : BaseChangeGroup (k := R) d)
    (v : Fin (N + 1)) :
    Units.val ((liftGauge d Q v)⁻¹)
      = (Units.val ((Q v)⁻¹)).map (C : R →+* MvPolynomial (RepCoord d) R) := by
  show Units.val (Units.map _ (Q v))⁻¹ = _
  rw [Units.coe_map_inv]
  rfl

/-- A `C`-lifted (constant) gauge matrix is fixed by `aeval (gaugeSub P)`: its entries are `C`-images
in the coefficient ring, and `aeval` fixes constants (`aeval_C`). -/
theorem map_aeval_gaugeSub_liftGauge (d : Fin (N + 1) → ℕ) (P Q : BaseChangeGroup (k := R) d)
    (v : Fin (N + 1)) :
    (Units.val (liftGauge d Q v)).map (aeval (R := R) (gaugeSub d P)) = Units.val (liftGauge d Q v)
    ∧ (Units.val ((liftGauge d Q v)⁻¹)).map (aeval (R := R) (gaugeSub d P))
        = Units.val ((liftGauge d Q v)⁻¹) := by
  refine ⟨?_, ?_⟩
  · rw [liftGauge_val_eq]
    funext a b
    rw [Matrix.map_apply, Matrix.map_apply, aeval_C, MvPolynomial.algebraMap_eq]
  · rw [liftGauge_inv_val_eq]
    funext a b
    rw [Matrix.map_apply, Matrix.map_apply, aeval_C, MvPolynomial.algebraMap_eq]

/-- **The composition law on the generic tuple.** Applying `aeval (gaugeSub P)` to the gauged
generic factor `baseChange (liftGauge Q) (genericTuple) i` re-gauges by `P` inside: the result is
`baseChange (liftGauge Q) (baseChange (liftGauge P) (genericTuple)) i`. The constant `C`-lifted
`Q`-matrices are fixed (`map_aeval_gaugeSub_liftGauge`), the variable block re-gauges
(`aeval_gaugeSub_genericTuple`). -/
theorem map_aeval_gaugeSub_baseChange (d : Fin (N + 1) → ℕ) (P Q : BaseChangeGroup (k := R) d)
    (i : Fin N) :
    (baseChange (liftGauge d Q) (genericTuple d) i).map (aeval (R := R) (gaugeSub d P))
      = baseChange (liftGauge d Q) (baseChange (liftGauge d P) (genericTuple d)) i := by
  rw [baseChange_apply, baseChange_apply, Matrix.map_mul, Matrix.map_mul,
    (map_aeval_gaugeSub_liftGauge d P Q i.succ).1,
    (map_aeval_gaugeSub_liftGauge d P Q i.castSucc).2,
    aeval_gaugeSub_genericTuple d P i]

/-- The two `aeval (gaugeSub …)` directions compose to the identity on the generators: for any gauges
`P`, `Q`, `aeval (gaugeSub P) (gaugeSub Q x)` is the `x`-entry of `baseChange (liftGauge (Q * P))
(genericTuple)`. Specialized to `Q = P⁻¹` (resp. `P = Q⁻¹`) it collapses to `X x`. -/
theorem aeval_gaugeSub_gaugeSub (d : Fin (N + 1) → ℕ) (P Q : BaseChangeGroup (k := R) d)
    (x : RepCoord d) :
    aeval (R := R) (gaugeSub d P) (gaugeSub d Q x)
      = baseChange (liftGauge d (Q * P)) (genericTuple d) x.1 x.2.1 x.2.2 := by
  have h : aeval (R := R) (gaugeSub d P) (gaugeSub d Q x)
      = ((baseChange (liftGauge d Q) (genericTuple d) x.1).map
          (aeval (R := R) (gaugeSub d P))) x.2.1 x.2.2 := rfl
  rw [h, map_aeval_gaugeSub_baseChange d P Q x.1, ← baseChange_mul, liftGauge_mul]

/-- **The gauge `AlgEquiv`** of `MvPolynomial (RepCoord d) R`: `aeval (gaugeSub P)`, with inverse
`aeval (gaugeSub P⁻¹)`. The round-trips collapse by the group-action laws (`baseChange_mul` /
`baseChange_one`) on the generic tuple. The endpoint normalization instantiates `P`. -/
noncomputable def gaugeEquiv (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d) :
    MvPolynomial (RepCoord d) R ≃ₐ[R] MvPolynomial (RepCoord d) R :=
  AlgEquiv.ofAlgHom (aeval (gaugeSub d P)) (aeval (gaugeSub d P⁻¹))
    (by
      apply MvPolynomial.algHom_ext
      intro x
      rw [AlgHom.comp_apply, AlgHom.id_apply, aeval_X, aeval_gaugeSub_gaugeSub, inv_mul_cancel,
        liftGauge_one, baseChange_one, genericTuple_apply])
    (by
      apply MvPolynomial.algHom_ext
      intro x
      rw [AlgHom.comp_apply, AlgHom.id_apply, aeval_X, aeval_gaugeSub_gaugeSub, mul_inv_cancel,
        liftGauge_one, baseChange_one, genericTuple_apply])

/-- `gaugeEquiv d P` acts as `aeval (gaugeSub d P)` (the forward `AlgHom` of the `ofAlgHom`). -/
@[simp] theorem gaugeEquiv_apply (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
    (p : MvPolynomial (RepCoord d) R) :
    gaugeEquiv d P p = aeval (R := R) (gaugeSub d P) p := rfl

/-- **The mult-transport, in `gaugeEquiv` form.** `gaugeEquiv d P` sends the generic product entry
`multPoly d r c` to the `(r, c)` entry of `P_last · multPoly · P_0⁻¹`. This is the bridge R2-3b-4
needs: with the endpoint gauge (`P_0 = H`, `P_last = L⁻¹`), it turns the chart target `mult(A) = LEH`
into `mult(Ã) = E`. -/
theorem gaugeEquiv_multPoly (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
    (r : Fin (d (Fin.last N))) (c : Fin (d 0)) :
    gaugeEquiv d P (multPoly d r c)
      = ((Units.val (liftGauge d P (Fin.last N)) * Matrix.of (multPoly d)
            * Units.val ((liftGauge d P 0)⁻¹)
          : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) (MvPolynomial (RepCoord d) R)) r c) := by
  rw [gaugeEquiv_apply, aeval_gaugeSub_multPoly]

/-! ## Non-vacuity witnesses

(i) The identity gauge `P = 1` reproduces the identity `AlgEquiv` — the construction is honest at
`H = L = 1`. (ii) The transport on the `(2,2,2)` witness with a non-identity end-vertex gauge over
`ℚ` is the genuine conjugation `P_last · M · P_0⁻¹` of the generic product. -/

section Witness

/-- The identity gauge substitution is the identity on coordinates: `gaugeSub d 1 x = X x`. -/
theorem gaugeSub_one (d : Fin (N + 1) → ℕ) (x : RepCoord d) :
    gaugeSub d (1 : BaseChangeGroup (k := R) d) x = X x := by
  rw [gaugeSub, liftGauge_one, baseChange_one, genericTuple_apply]

/-- At the identity gauge the `AlgEquiv` is the identity (`H = L = 1` reproduces the identity) —
the construction is non-vacuous and honest. -/
example (d : Fin (N + 1) → ℕ) (p : MvPolynomial (RepCoord d) R) :
    gaugeEquiv d (1 : BaseChangeGroup (k := R) d) p = p := by
  rw [gaugeEquiv_apply]
  have : aeval (R := R) (gaugeSub d (1 : BaseChangeGroup (k := R) d))
      = AlgHom.id R (MvPolynomial (RepCoord d) R) := by
    apply MvPolynomial.algHom_ext
    intro x
    rw [aeval_X, gaugeSub_one, AlgHom.id_apply]
  rw [this, AlgHom.id_apply]

/-- The constant dimension vector `(2, 2, 2)` (every `d v = 2` definitionally, so the uniform gauge
type-checks without `![…]`-reduction friction). -/
def dConst : Fin 3 → ℕ := fun _ ↦ 2

/-- The uniform `(2,2,2)` gauge over `ℤ` carrying `witnessUnit` (`!![1,1;0,1]`) at every vertex. -/
def witnessGauge : BaseChangeGroup (k := ℤ) dConst := fun _ ↦ witnessUnit

/-- The gauge `AlgEquiv` is available at the concrete non-identity `(2,2,2)` gauge `witnessGauge` over
`ℤ` — the construction is non-vacuous at a genuine `!![1,1;0,1]`-conjugation. -/
noncomputable example :
    MvPolynomial (RepCoord dConst) ℤ ≃ₐ[ℤ] MvPolynomial (RepCoord dConst) ℤ :=
  gaugeEquiv dConst witnessGauge

/-- The mult-transport fires at the concrete non-identity gauge `witnessGauge`: `gaugeEquiv` carries
each generic product entry to the conjugation `P_last · multPoly · P_0⁻¹` of the generic product.
Non-vacuous (the gauge is the genuine `!![1,1;0,1]` at every vertex, not the identity). -/
example (r : Fin (dConst (Fin.last 2))) (c : Fin (dConst 0)) :
    gaugeEquiv (R := ℤ) dConst witnessGauge (multPoly dConst r c)
      = aeval (R := ℤ) (gaugeSub dConst witnessGauge) (multPoly dConst r c) :=
  gaugeEquiv_apply dConst witnessGauge (multPoly dConst r c)

end Witness

end DLNFibre.Core

codex
I’ve got enough local context now. I’m going to give the verdict in terms of the repo’s current modules: the math section exists, but the clean Lean implementation should be ring/comorphism-first, not pointwise-section-first.
exec
/bin/bash -lc "nl -ba /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean | sed -n '136,160p'; nl -ba /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean | sed -n '24,42p'; nl -ba /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean | sed -n '104,130p'; nl -ba /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean | sed -n '315,345p'" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
   136	`MvPolynomial σ k ⧸ vanishingIdeal Z` of `Z`'s Zariski closure, as an `ℕ∞` (the `⊥` from a trivial
   137	quotient — absent here, since the relevant `vanishingIdeal Z` is prime — defaulting to `0`). It is
   138	the dimension of `Z` itself exactly when `Z` is Zariski-closed (`IsZariskiClosed`). -/
   139	noncomputable def varietyDim (Z : Set (σ → k)) : ℕ∞ :=
   140	  (ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal k Z)).unbotD 0
   141	
   142	/-- **The codimension bridge (additive, `ℕ∞`).** For an irreducible variety `Z ⊆ (σ → k)` — i.e.
   143	`(vanishingIdeal Z).IsPrime` — the height of its vanishing ideal plus its variety dimension equals
   144	the ambient dimension `Nat.card σ`: `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ`. The
   145	catenary identity over `σ`, read at the prime `vanishingIdeal Z`. Geometric codimension `=` ambient
   146	`−` variety dimension, in lossless additive form. -/
   147	theorem height_vanishingIdeal_add_varietyDim_eq_card [Finite σ] {Z : Set (σ → k)}
   148	    (hp : (vanishingIdeal k Z : Ideal (MvPolynomial σ k)).IsPrime) :
   149	    (vanishingIdeal k Z).height + varietyDim Z = (Nat.card σ : ℕ∞) := by
   150	  have key := height_add_ringKrullDim_quotient_eq_card (vanishingIdeal k Z)
   151	  haveI : Nontrivial (MvPolynomial σ k ⧸ vanishingIdeal k Z) :=
   152	    Ideal.Quotient.nontrivial_iff.mpr hp.ne_top
   153	  have hne : ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal k Z) ≠ ⊥ :=
   154	    fun h ↦ by simpa [h] using
   155	      ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial σ k ⧸ vanishingIdeal k Z)
   156	  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hne
   157	  rw [varietyDim, ← hm, WithBot.unbotD_coe]
   158	  rw [← hm] at key
   159	  exact_mod_cast key
   160	
    24	
    25	open PrimeSpectrum
    26	
    27	/-- **Radical-insensitivity of the quotient Krull dimension.** `ringKrullDim (R ⧸ I)` depends on `I`
    28	only through its radical: `Spec (R ⧸ I) = zeroLocus I = zeroLocus I.radical = Spec (R ⧸ I.radical)`
    29	as ordered sets, and Krull dimension is a spectrum invariant. -/
    30	theorem ringKrullDim_quotient_radical {R : Type*} [CommRing R] (I : Ideal R) :
    31	    ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ I.radical) := by
    32	  rw [ringKrullDim_quotient, ringKrullDim_quotient, PrimeSpectrum.zeroLocus_radical]
    33	
    34	/-- Two ideals with the same radical give the same quotient Krull dimension — the form the route-(c)
    35	fibre-dimension build consumes (it reads `varietyDim` off `vanishingIdeal`, while a chart
    36	presentation may hand it the generator ideal `fibreGenIdeal`, equal only up to radical). -/
    37	theorem ringKrullDim_quotient_eq_of_radical_eq {R : Type*} [CommRing R] {I J : Ideal R}
    38	    (h : I.radical = J.radical) :
    39	    ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ J) := by
    40	  rw [ringKrullDim_quotient_radical I, ringKrullDim_quotient_radical J, h]
    41	
    42	end DLNFibre.Core
   104	/-- **The deep pivot minor** `ΔPdeep d r`: the determinant of the top-left `r×r` submatrix of the
   105	deep generic product `Matrix.of (multPoly d)`. The deep analog of `N = 1`'s `detPivotPoly`;
   106	inverting it is the pivot chart. -/
   107	noncomputable def ΔPdeep (d : Fin (N + 1) → ℕ) (r : ℕ)
   108	    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) : MvPolynomial (RepCoord d) k :=
   109	  ((Matrix.of (multPoly d)).submatrix
   110	    (fun i : Fin r ↦ (Fin.castLE hp i : Fin (d (Fin.last N))))
   111	    (fun j : Fin r ↦ (Fin.castLE hq j : Fin (d 0)))).det
   112	
   113	/-- **The deep localized base ideal** `IadDeep d r`: the determinantal base ideal `sigmaIdeal d r`
   114	pushed into the localized total ring `Localization.Away (ΔPdeep …)`. The deep analog of `Iad`. -/
   115	noncomputable def IadDeep (d : Fin (N + 1) → ℕ) (r : ℕ)
   116	    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
   117	    Ideal (Localization.Away (ΔPdeep (k := k) d r hp hq)) :=
   118	  (sigmaIdeal d r).map (algebraMap (MvPolynomial (RepCoord d) k)
   119	    (Localization.Away (ΔPdeep (k := k) d r hp hq)))
   120	
   121	/-- **The deep chart ring** `Sred d r := Localization.Away (ΔPdeep …) ⧸ IadDeep …`: the localized
   122	chart quotient of the rank-`≤ r` product locus for general `d`, on the pivot chart. The `CommRing` /
   123	`Algebra k` instances are inherited from the localization-quotient. -/
   124	noncomputable abbrev Sred (d : Fin (N + 1) → ℕ) (r : ℕ)
   125	    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) : Type u :=
   126	  Localization.Away (ΔPdeep (k := k) d r hp hq) ⧸ IadDeep (k := k) d r hp hq
   127	
   128	/-! ## R2-3b-1 — `Sred` is reduced (justifying the name; discharges R2-3a's `hSred`)
   129	
   130	The name `Sred` asserts reducedness, and that reducedness is precisely R2-3a's second hypothesis
   315	/-- **The base→total `k`-algebra map** `SchurLoc q p r →ₐ[k] Sred d r` (`q = d 0`, `p = d last`):
   316	`baseQuotMap` precomposed with `basePresentationEquiv.symm`. This is the morphism whose induced
   317	algebra structure makes `Sred` a `SchurLoc`-algebra (the `R = SchurLoc`-algebra structure that
   318	R2-3a's product iso `e` needs). `[IsAlgClosed k] [CharZero k]` (for `basePresentationEquiv`). -/
   319	noncomputable def schurToSred [IsAlgClosed k] [CharZero k] (d : Fin (N + 1) → ℕ) (r : ℕ)
   320	    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
   321	    SchurLoc (k := k) (d 0) (d (Fin.last N)) r →ₐ[k] Sred (k := k) d r hp hq :=
   322	  (baseQuotMap (k := k) d r hp hq).comp
   323	    (basePresentationEquiv (k := k) (d 0) (d (Fin.last N)) r hp hq).symm.toAlgHom
   324	
   325	/-! ## R2-3b-2 — the `SchurLoc`-algebra structure on `Sred` and the scalar tower
   326	
   327	The base→total map `schurToSred` induces (via `RingHom.toAlgebra`) the `SchurLoc q p r`-algebra
   328	structure on `Sred`, with `k → SchurLoc → Sred` a scalar tower. These instances are the
   329	`[Algebra R S]` slot that R2-3a's `e : S ≃ₐ[k] R ⊗_k FibreAlg` consumes (`R = SchurLoc q p r`). -/
   330	
   331	/-- **The `SchurLoc`-algebra structure on `Sred`**, induced by the base→total map `schurToSred`
   332	(`RingHom.toAlgebra`). The `R = SchurLoc q p r`-algebra structure R2-3a's product iso `e` needs. -/
   333	@[reducible] noncomputable def sredSchurAlgebra [IsAlgClosed k] [CharZero k] (d : Fin (N + 1) → ℕ)
   334	    (r : ℕ) (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
   335	    Algebra (SchurLoc (k := k) (d 0) (d (Fin.last N)) r) (Sred (k := k) d r hp hq) :=
   336	  (schurToSred (k := k) d r hp hq).toRingHom.toAlgebra
   337	
   338	/-- The induced `SchurLoc`-algebra structure on `Sred` makes `k → SchurLoc q p r → Sred` a scalar
   339	tower: `algebraMap k Sred` factors through `algebraMap k (SchurLoc …)` (both `schurToSred` and the
   340	localization-quotient maps are `k`-algebra maps). -/
   341	theorem sredSchur_isScalarTower [IsAlgClosed k] [CharZero k] (d : Fin (N + 1) → ℕ) (r : ℕ)
   342	    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
   343	    @IsScalarTower k (SchurLoc (k := k) (d 0) (d (Fin.last N)) r) (Sred (k := k) d r hp hq)
   344	      _ (sredSchurAlgebra (k := k) d r hp hq).toSMul _ := by
   345	  letI := sredSchurAlgebra (k := k) d r hp hq

exec
/bin/bash -lc "nl -ba /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean | sed -n '75,100p'; nl -ba /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean | sed -n '279,330p'; nl -ba /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean | sed -n '55,90p'" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
    75	change telescope away, leaving only the two end-vertex units (`submult_smul` at the full interval
    76	`(0, last)`, through `mult_eq_submult`). -/
    77	theorem mult_smul (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d) :
    78	    mult d (P • A)
    79	      = Units.val (P (Fin.last N)) * mult d A * Units.val ((P 0)⁻¹) := by
    80	  rw [mult_eq_submult, mult_eq_submult, submult_smul]
    81	
    82	/-! ## The fibre under the base-change action -/
    83	
    84	/-- **The base-change image of a fibre is a fibre.** The linear automorphism `A ↦ P • A` carries
    85	`fibre d B` onto `fibre d (P_N · B · P_0⁻¹)`: by mult-equivariance, `mult (P • A) = P_N · B · P_0⁻¹`
    86	iff `mult A = B`. -/
    87	theorem image_smul_fibre (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := k) d)
    88	    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) :
    89	    (fun A ↦ P • A) '' (fibre d B)
    90	      = fibre d (Units.val (P (Fin.last N)) * B * Units.val ((P 0)⁻¹)) := by
    91	  ext A
    92	  constructor
    93	  · rintro ⟨A₀, hA₀, rfl⟩
    94	    rw [mem_fibre, mult_smul]
    95	    rw [mem_fibre] at hA₀
    96	    rw [hA₀]
    97	  · intro hA
    98	    refine ⟨P⁻¹ • A, ?_, smul_inv_smul P A⟩
    99	    rw [mem_fibre] at hA
   100	    rw [mem_fibre, mult_smul, hA]
   279	theorem exists_baseChange_of_rank_eq (d : Fin (N + 1) → ℕ)
   280	    (hN : (0 : Fin (N + 1)) ≠ Fin.last N)
   281	    (B B' : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) (h : B.rank = B'.rank) :
   282	    ∃ P : BaseChangeGroup (k := k) d,
   283	      B' = Units.val (P (Fin.last N)) * B * Units.val ((P 0)⁻¹) := by
   284	  have hran : Module.finrank k (LinearMap.range (toLin' B))
   285	      = Module.finrank k (LinearMap.range (toLin' B')) := h
   286	  have hker : Module.finrank k (LinearMap.ker (toLin' B))
   287	      = Module.finrank k (LinearMap.ker (toLin' B')) := by
   288	    have e1 := LinearMap.finrank_range_add_finrank_ker (toLin' B)
   289	    have e2 := LinearMap.finrank_range_add_finrank_ker (toLin' B')
   290	    omega
   291	  obtain ⟨eL, eR, hconj⟩ := exists_conj (toLin' B) (toLin' B') hker hran
   292	  -- transfer the conjugation to matrices: B' = (toMatrix' eL) * B * (toMatrix' eR)
   293	  have hmat : B' = (equivUnitMatrix eL).val * B * (equivUnitMatrix eR).val := by
   294	    have hc := congrArg LinearMap.toMatrix' hconj
   295	    rw [LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp,
   296	      LinearMap.toMatrix'_toLin', ← Matrix.mul_assoc] at hc
   297	    exact hc
   298	  -- assemble the BaseChangeGroup: `last N ↦ equivUnitMatrix eL`, `0 ↦ (equivUnitMatrix eR)⁻¹`
   299	  set P : BaseChangeGroup (k := k) d :=
   300	    fun v ↦ if hv : v = Fin.last N then (by rw [hv]; exact equivUnitMatrix eL)
   301	      else if hv0 : v = 0 then (by rw [hv0]; exact (equivUnitMatrix eR)⁻¹) else 1 with hP
   302	  refine ⟨P, ?_⟩
   303	  have hPL : P (Fin.last N) = equivUnitMatrix eL := by rw [hP]; simp
   304	  have hP0 : P 0 = (equivUnitMatrix eR)⁻¹ := by
   305	    rw [hP]
   306	    show (if hv : (0 : Fin (N + 1)) = Fin.last N then (by rw [hv]; exact equivUnitMatrix eL)
   307	      else if hv0 : (0 : Fin (N + 1)) = 0 then (by rw [hv0]; exact (equivUnitMatrix eR)⁻¹)
   308	      else 1) = (equivUnitMatrix eR)⁻¹
   309	    rw [dif_neg hN, dif_pos rfl]
   310	    rfl
   311	  rw [hPL, hP0, inv_inv]
   312	  exact hmat
   313	
   314	/-! ## The headline: same rank ⟹ same fibre codimension -/
   315	
   316	/-- **Same rank ⟹ same fibre codimension.** The geometric codimension of the multiplication-map
   317	fibre depends on the target `B` only through its rank: for `B.rank = B'.rank`,
   318	`codimRepCanonical (fibre d B) = codimRepCanonical (fibre d B')`. Reduces the Lemma-4.6 problem (all
   319	rank-`r` targets) to a single fibre. Needs `N ≥ 1` (`hN : 0 ≠ Fin.last N`): for `N = 0` the
   320	multiplication map is the constant `1`, so the fibre over `1` is everything but the fibre over a
   321	different same-rank `B'` is empty — the claim is genuinely false there. -/
   322	theorem codimRepCanonical_fibre_eq_of_rank_eq [Infinite k] (d : Fin (N + 1) → ℕ)
   323	    (hN : (0 : Fin (N + 1)) ≠ Fin.last N)
   324	    (B B' : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) (h : B.rank = B'.rank) :
   325	    codimRepCanonical (fibre d B) = codimRepCanonical (fibre d B') := by
   326	  obtain ⟨P, hP⟩ := exists_baseChange_of_rank_eq d hN B B' h
   327	  rw [hP, codimRepCanonical_fibre_baseChange]
   328	
   329	/-! ## Non-vacuity witness
   330	
    55	/-- **The exact-rank locus is the `H`-sweep of one fibre.** For a fixed rank-`r` target `E` and
    56	`N ≥ 1`, the exact-rank locus `productRankLocus d r = {A : rank(mult A) = r}` is exactly the union,
    57	over the endpoint base-change group, of the translates of the fibre `mult⁻¹(E)`:
    58	
    59	> `A ∈ productRankLocus d r ↔ ∃ P, A ∈ (P • ·) '' (fibre d E)`.
    60	
    61	`(←)` `mult` carries a translate of `fibre E` to `P_N · E · P_0⁻¹`, of rank `= rank E = r`
    62	(`rank_endpoint_conj`). `(→)` `rank(mult A) = r = E.rank`, so `exists_baseChange_of_rank_eq` gives `P`
    63	with `mult A = P_N · E · P_0⁻¹`, and `image_smul_fibre` packages `A` as a translate of `fibre E`. -/
    64	theorem mem_productRankLocus_iff_mem_sweep (d : Fin (N + 1) → ℕ)
    65	    (hN : (0 : Fin (N + 1)) ≠ Fin.last N)
    66	    (E : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) {r : ℕ} (hE : E.rank = r)
    67	    (A : Tuple (k := k) d) :
    68	    A ∈ productRankLocus d r ↔
    69	      ∃ P : BaseChangeGroup (k := k) d, A ∈ (fun A' ↦ P • A') '' (fibre d E) := by
    70	  constructor
    71	  · intro hA
    72	    rw [mem_productRankLocus] at hA
    73	    obtain ⟨P, hP⟩ := exists_baseChange_of_rank_eq d hN E (mult d A) (by rw [hE, hA])
    74	    exact ⟨P, by rw [image_smul_fibre, mem_fibre, ← hP]⟩
    75	  · rintro ⟨P, hPA⟩
    76	    rw [image_smul_fibre, mem_fibre] at hPA
    77	    rw [mem_productRankLocus, hPA, rank_endpoint_conj, hE]
    78	
    79	/-- **The sweep identity (set form).** `productRankLocus d r = ⋃_P (P • ·) '' (fibre d E)` for a fixed
    80	rank-`r` target `E`. The set-level statement of `mem_productRankLocus_iff_mem_sweep`. -/
    81	theorem productRankLocus_eq_iUnion_smul_fibre (d : Fin (N + 1) → ℕ)
    82	    (hN : (0 : Fin (N + 1)) ≠ Fin.last N)
    83	    (E : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) {r : ℕ} (hE : E.rank = r) :
    84	    productRankLocus d r
    85	      = ⋃ P : BaseChangeGroup (k := k) d, (fun A' ↦ P • A') '' (fibre d E) := by
    86	  ext A
    87	  rw [Set.mem_iUnion, mem_productRankLocus_iff_mem_sweep d hN E hE]
    88	
    89	/-! ## Each translate is isomorphic to the fibre `F` (codim-preserving) -/
    90	

exec
/bin/bash -lc "nl -ba /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean | sed -n '374,386p'; nl -ba /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean | sed -n '84,118p'; nl -ba /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean | sed -n '41,62p'; nl -ba /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean | sed -n '219,250p'" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
   374	base ring `A_loc = Localization.Away detΔ`, modulo its base ideal `Iad = (sigmaIdeal …).map …`, is
   375	the free Schur localization `Sd = Localization.Away detSchurS` — a regular ring of dimension `δ`.
   376	Via the height squeeze `Ψ(Iad) = J` (`map_Iad_eq_graphIdeal_forcedB22`) and the graph-ideal quotient
   377	`Q ⧸ J ≅ Sd` (`graphIdealQuotientEquiv`, the `B22`-block elimination). -/
   378	noncomputable def basePresentationEquiv [IsAlgClosed k] [CharZero k] (q p r : ℕ)
   379	    (hp : r ≤ p) (hq : r ≤ q) :
   380	    (Localization.Away (detPivotPoly (k := k) q p r hp hq) ⧸ (Iad (k := k) q p r hp hq))
   381	      ≃ₐ[k] SchurLoc (k := k) q p r := by
   382	  have e₁ : (Localization.Away (detPivotPoly (k := k) q p r hp hq) ⧸ (Iad (k := k) q p r hp hq))
   383	      ≃ₐ[k] (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)
   384	        ⧸ graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r))) :=
   385	    Ideal.quotientEquivAlg ((Iad (k := k) q p r hp hq))
   386	      (graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r)))
    84	`F` is `k`-flat as a vector space, so `includeRight` is injective by
    85	`Algebra.TensorProduct.includeRight_injective`), then `isReduced_of_injective`. This is the standard
    86	char-0 descent the certificate named — but it needs only a field base and a nontrivial `R`. -/
    87	
    88	/-- **Tensor-with-a-field reducedness descent.** Over a field `k`, for any nontrivial commutative
    89	`k`-algebra `R` and commutative `k`-algebra `F`: if `R ⊗_k F` is reduced then `F` is reduced. The
    90	injection `F ↪ R ⊗_k F` (`includeRight`, injective since `F` is `k`-flat and `algebraMap k R` is
    91	injective) pulls back reducedness. -/
    92	theorem isReduced_of_tensor {R F : Type u} [CommRing R] [Nontrivial R] [CommRing F]
    93	    [Algebra k R] [Algebra k F] (h : IsReduced (R ⊗[k] F)) : IsReduced F :=
    94	  letI := h
    95	  isReduced_of_injective
    96	    (Algebra.TensorProduct.includeRight : F →ₐ[k] R ⊗[k] F)
    97	    (Algebra.TensorProduct.includeRight_injective (algebraMap k R).injective)
    98	
    99	/-! ## The route-(b) chain through the trivialization (the open rung as a hypothesis) -/
   100	
   101	/-- **Route (b): `fibreGenIdeal` radical, through the trivialization.** Given the chart
   102	trivialization `e : S ≃ₐ[k] R ⊗_k F_B` (the endpoint-normalization product iso) and that the chart
   103	ring `S` is **reduced** (the engine's `Sred = (MvPol / sigmaIdeal)[1/ΔP]` is reduced, `sigmaIdeal`
   104	a `vanishingIdeal`), the fibre ideal `fibreGenIdeal d B` is **radical**. The certified mechanism:
   105	`S` reduced ⟹ `R ⊗_k F_B` reduced (transfer along `e.symm`) ⟹ `F_B` reduced (`isReduced_of_tensor`)
   106	⟹ `fibreGenIdeal d B` radical. `[Nontrivial R]` (`R = SchurLoc` is a domain). -/
   107	theorem fibreGenIdeal_isRadical_of_trivialization
   108	    (d : Fin (N + 1) → ℕ) (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k)
   109	    (R S : Type u) [CommRing R] [Nontrivial R] [CommRing S]
   110	    [Algebra k R] [Algebra k S]
   111	    (e : S ≃ₐ[k] R ⊗[k] FibreAlg d B) (hSred : IsReduced S) :
   112	    (fibreGenIdeal d B).IsRadical := by
   113	  letI := hSred
   114	  -- `S` reduced ⟹ `R ⊗ F_B` reduced (it injects into `S` via `e.symm`)
   115	  have hRF : IsReduced (R ⊗[k] FibreAlg d B) :=
   116	    isReduced_of_injective e.symm.toRingEquiv e.symm.injective
   117	  -- ⟹ `F_B` reduced (tensor-with-a-field descent) ⟹ `fibreGenIdeal` radical
   118	  exact (fibreGenIdeal_isRadical_iff_isReduced_fibreAlg d B).mpr (isReduced_of_tensor (R := R) hRF)
    41	/-- **Route-c assembly: `codim(fibre d B) = C + δ` (conditional bank).** For a rank-`r` target `B`
    42	(`N ≥ 1`, alg-closed char 0), the geometric codimension of the fibre `mult⁻¹(B)` is `C = cCodim d r`
    43	plus the matrix-stratum shift `δ = r·(d_N + d_0 − r)` — carrying the homogeneous-sweep dimension
    44	identity `hSweep`, the Cited closure bridge `hClosure`, and the two reducible-locus catenary
    45	relations `hCatFibre`/`hCatSigma` as explicit named hypotheses. The proof is the additive chain
    46	`C + δ + dim F = C + dim Σ̄^r = card = codim F + dim F`, cancelling the finite `dim F`. -/
    47	theorem codimRepCanonical_fibre_eq_cCodim_add_shift_of_sweep [IsAlgClosed k] [CharZero k]
    48	    (d : Fin (N + 1) → ℕ) (r : ℕ) (h : (kostantPartitions d r).Nonempty)
    49	    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) (hB : B.rank = r)
    50	    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
    51	        = ((r * (d (Fin.last N) + d 0 - r) : ℕ) : ℕ∞)
    52	          + varietyDim (canonicalCoord d '' fibre d B))
    53	    (hClosure : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
    54	        = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r))
    55	    (hCatFibre : codimRepCanonical (fibre d B)
    56	        + varietyDim (canonicalCoord d '' fibre d B) = (Nat.card (RepCoord d) : ℕ∞))
    57	    (hCatSigma : codimRepCanonical (productRankLocusLE (k := k) d r)
    58	        + varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
    59	          = (Nat.card (RepCoord d) : ℕ∞)) :
    60	    codimRepCanonical (fibre d B)
    61	      = ((cCodim d r h).toNat : ℕ∞) + ((r * (d (Fin.last N) + d 0 - r) : ℕ) : ℕ∞) := by
    62	  -- `codim Σ̄^r = C` (LANDED Brick A).
   219	noncomputable def gaugeEquiv (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d) :
   220	    MvPolynomial (RepCoord d) R ≃ₐ[R] MvPolynomial (RepCoord d) R :=
   221	  AlgEquiv.ofAlgHom (aeval (gaugeSub d P)) (aeval (gaugeSub d P⁻¹))
   222	    (by
   223	      apply MvPolynomial.algHom_ext
   224	      intro x
   225	      rw [AlgHom.comp_apply, AlgHom.id_apply, aeval_X, aeval_gaugeSub_gaugeSub, inv_mul_cancel,
   226	        liftGauge_one, baseChange_one, genericTuple_apply])
   227	    (by
   228	      apply MvPolynomial.algHom_ext
   229	      intro x
   230	      rw [AlgHom.comp_apply, AlgHom.id_apply, aeval_X, aeval_gaugeSub_gaugeSub, mul_inv_cancel,
   231	        liftGauge_one, baseChange_one, genericTuple_apply])
   232	
   233	/-- `gaugeEquiv d P` acts as `aeval (gaugeSub d P)` (the forward `AlgHom` of the `ofAlgHom`). -/
   234	@[simp] theorem gaugeEquiv_apply (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
   235	    (p : MvPolynomial (RepCoord d) R) :
   236	    gaugeEquiv d P p = aeval (R := R) (gaugeSub d P) p := rfl
   237	
   238	/-- **The mult-transport, in `gaugeEquiv` form.** `gaugeEquiv d P` sends the generic product entry
   239	`multPoly d r c` to the `(r, c)` entry of `P_last · multPoly · P_0⁻¹`. This is the bridge R2-3b-4
   240	needs: with the endpoint gauge (`P_0 = H`, `P_last = L⁻¹`), it turns the chart target `mult(A) = LEH`
   241	into `mult(Ã) = E`. -/
   242	theorem gaugeEquiv_multPoly (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
   243	    (r : Fin (d (Fin.last N))) (c : Fin (d 0)) :
   244	    gaugeEquiv d P (multPoly d r c)
   245	      = ((Units.val (liftGauge d P (Fin.last N)) * Matrix.of (multPoly d)
   246	            * Units.val ((liftGauge d P 0)⁻¹)
   247	          : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) (MvPolynomial (RepCoord d) R)) r c) := by
   248	  rw [gaugeEquiv_apply, aeval_gaugeSub_multPoly]
   249	
   250	/-! ## Non-vacuity witnesses

exec
/bin/bash -lc 'rg -n "ringKrullDim.*RingEquiv|ringKrullDim.*AlgEquiv|krullDim.*orderIso|ringKrullDim_eq" -S /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core | head -n 80' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:130:    rw [ringKrullDim_eq_of_integral_injective (f := g.toRingHom) hg_int hg_inj,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:144:    have h := ringKrullDim_eq_of_integral_injective
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:166:  rw [ringKrullDim_eq_zero_of_isField hfield, add_zero] at h
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:177:  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:41:  rw [ringKrullDim_eq_of_ringEquiv (graphIdealQuotientEquiv c).toRingEquiv,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:42:    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean:12:dimension-invariance headline `ringKrullDim_eq_of_integral_injective` (L5.4) and the polynomial
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean:63:  rw [ringKrullDim_eq_of_integral_injective (f := g.toRingHom) hg_int hg_inj,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean:126:  rw [← hdim, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntegralDimension.lean:14:`ringKrullDim_eq_of_integral_injective`. Two supporting general facts are also recorded:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntegralDimension.lean:33:  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field k, zero_add]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntegralDimension.lean:54:  rw [ringKrullDim, Order.krullDim_eq_of_orderIso (primeSpectrumQuotientOrderIsoIci p),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntegralDimension.lean:123:theorem ringKrullDim_eq_of_integral_injective [CommRing A] [CommRing S] {f : A →+* S}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntegralDimension.lean:140:  ringKrullDim_eq_of_integral_injective
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitPullbackDim.lean:22:   (`ringKrullDim_eq_of_ringEquiv`). The range is a subalgebra of the domain `groupRing d`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitPullbackDim.lean:72:`ringKrullDim_eq_of_ringEquiv`. Needs only `[Infinite k]` (the link uses no algebraic closure: the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitPullbackDim.lean:79:    ringKrullDim_eq_of_ringEquiv (quotientKerEquivRangeOrbitPullback M).toRingEquiv]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:109:  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineNoetherRank.lean:20:(`renameEquiv`), so both invariants transport (`ringKrullDim_eq_of_ringEquiv`, `AlgEquiv.trdeg_eq`).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineNoetherRank.lean:80:`ringKrullDim_eq_of_ringEquiv` and `AlgEquiv.trdeg_eq`. Char-free. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineNoetherRank.lean:104:  rw [ringKrullDim_eq_of_ringEquiv Ψ.toRingEquiv, AlgEquiv.trdeg_eq Ψ,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:170:  exact ringKrullDim_eq_of_integral_injective hint Ideal.quotientMap_injective
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:235:  ringKrullDim_eq_of_ringEquiv
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:369:  rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:85:L4d's `ringKrullDim_localizationAtPrime_isMaximal_eq`, via `IsLocalization.AtPrime.ringKrullDim_eq_height`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:91:  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:19:  (`IsLocalization.AtPrime.ringKrullDim_eq_height`).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:90:    ringKrullDim_eq_of_integral_injective hqmint Ideal.quotientMap_injective
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:91:  rw [← hdim, ringKrullDim_eq_zero_of_isField (Field.toIsField (S ⧸ q))]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:162:  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m), hmheight]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Length.lean:113:  rw [Order.height_eq_krullDim_Iic, coe_length, Order.krullDim_eq_of_orderIso (Submodule.mapIic _)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Length.lean:119:    Order.krullDim_eq_of_orderIso (Submodule.comapMkQRelIso N)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Length.lean:125:    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap e)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Length.lean:133:    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f Function.bijective_id)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:66:    ← IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean:67:    WithBot.coe_zero, ← ringKrullDimZero_iff_ringKrullDim_eq_zero,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Height.lean:321:  exact Order.krullDim_eq_of_orderIso
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Height.lean:336:theorem IsLocalization.AtPrime.ringKrullDim_eq_height (I : Ideal R) [I.IsPrime] (A : Type*)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Height.lean:352:  have := ringKrullDim_eq_of_ringEquiv (IsLocalization.algEquiv p.primeCompl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Height.lean:354:  rw [AtPrime.ringKrullDim_eq_height P, AtPrime.ringKrullDim_eq_height p] at this
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Height.lean:478:  rw [← IsLocalization.AtPrime.ringKrullDim_eq_height P (Rₚ P)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/PID.lean:37:theorem IsPrincipalIdealRing.ringKrullDim_eq_one (R : Type*) [CommRing R] [IsDomain R]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/PID.lean:52:    rw [← IsPrincipalIdealRing.ringKrullDim_eq_one _ h]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Spectrum/Prime/Topology.lean:1288:  Order.krullDim_orderDual.symm.trans <| Order.krullDim_eq_of_orderIso
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Zero.lean:53:lemma ringKrullDimZero_iff_ringKrullDim_eq_zero [Nontrivial R] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/LocalRing.lean:20:lemma ringKrullDim_eq_one_iff_of_isLocalRing_isDomain {R : Type*}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/LocalRing.lean:24:  · exact zero_ne_one ((ringKrullDim_eq_zero_of_isField h') ▸ h)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Field.lean:21:theorem ringKrullDim_eq_zero_of_field (F : Type*) [Field F] : ringKrullDim F = 0 :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Field.lean:24:theorem ringKrullDim_eq_zero_of_isField {F : Type*} [CommRing F] (hF : IsField F) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Basic.lean:43:lemma ringKrullDim_eq_bot_of_subsingleton [Subsingleton R] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Basic.lean:65:theorem ringKrullDim_eq_of_ringEquiv (e : R ≃+* S) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Basic.lean:70:alias RingEquiv.ringKrullDim := ringKrullDim_eq_of_ringEquiv
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Basic.lean:94:proof_wanted MvPolynomial.fin_ringKrullDim_eq_add_of_isNoetherianRing
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Polynomial.lean:36:  · rw [show C = (algebraMap R (Polynomial R)) from rfl, Order.krullDim_eq_of_orderIso
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Polynomial.lean:38:      ← ringKrullDim_eq_of_ringEquiv (polyEquivTensor R (p.asIdeal.ResidueField)).toRingEquiv,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Polynomial.lean:124:    · exact ringKrullDim_eq_of_ringEquiv (renameEquiv _ e).toRingEquiv
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Polynomial.lean:130:    rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.optionEquivLeft _ _).toRingEquiv,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:124:  rw [ringKrullDim_eq_of_ringEquiv (quotientEquivAlgOfEq R h).toRingEquiv,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Regular.lean:211:  rw [ringKrullDim_eq_of_ringEquiv (quotientEquivAlgOfEq R eq).toRingEquiv,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/Module.lean:58:  exact (RingEquiv.ringKrullDim (RingEquiv.quotientBot R))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:34:  rw [ringKrullDim, Order.krullDim_eq_of_orderIso I.primeSpectrumQuotientOrderIsoZeroLocus]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:40:  · rw [hr', ringKrullDim_eq_bot_of_subsingleton]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:77:  ringKrullDim_eq_of_ringEquiv (isEmptyRingEquiv _ _)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:86:    · exact ringKrullDim_eq_of_ringEquiv (renameEquiv _ e).toRingEquiv
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/KrullDimension/NonZeroDivisors.lean:92:    exact (ringKrullDim_eq_of_ringEquiv (MvPolynomial.optionEquivLeft _ _).toRingEquiv).ge
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/RegularLocalRing/Defs.lean:61:  rwa [isRegularLocalRing_iff, ← ringKrullDim_eq_of_ringEquiv e, ← map_ringEquiv_maximalIdeal e,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/RegularLocalRing/Defs.lean:75:    simpa only [(IsPrincipalIdealRing.ringKrullDim_eq_one R) isf,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:740:lemma krullDim_eq_of_orderIso (f : α ≃o β) : krullDim α = krullDim β :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/Order/KrullDimension.lean:873:  rw [coheight, ← krullDim_orderDual, Order.krullDim_eq_of_orderIso (OrderIso.refl _)]

codex
**Verdict:** yes, the regular section exists on the pivot chart, but in this repo the cheapest Lean shape is not a pointwise `σ : U_P → H`. Build the universal endpoint gauge over the localized chart ring and use its induced `AlgEquiv`.

For a rank-`r` target matrix on the top-left pivot chart, write

```text
B = [ A  C ]
    [ D  F ]
```

with `A` the invertible `r × r` pivot block. On rank `≤ r`, the Schur relation gives `F = D A⁻¹ C`. Then

```text
B =
[ A  0 ] · E · [ I  A⁻¹ C ]
[ D  I ]       [ 0    I    ]
```

so take

```text
σ_N(B) = [ A  0 ]
         [ D  I ]

σ_0(B) = [ I  -A⁻¹ C ]
         [ 0     I    ]
```

because `σ_0(B)⁻¹ = [I A⁻¹C; 0 I]`. Entries of `A⁻¹C` are `adj(A) C / det(A)`, hence regular on `D(det A)`. This is the standard pivot-cell section.

In Lean, avoid the existential `exists_baseChange_of_rank_eq`; it is the wrong object for regularity. The repo already has the right ingredients:

- `ΔPdeep` and `Sred = Localization.Away ΔPdeep ⧸ IadDeep` for the deep chart: [DeepChartRing.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:104).
- `basePresentationEquiv : A_loc/Iad ≃ₐ[k] SchurLoc`, so the base chart is already the Schur/free chart: [DeterminantalBasePresentation.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:378).
- `schurToSred` makes `Sred` a `SchurLoc`-algebra: [DeepChartRing.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:319).
- `gaugeEquiv` is already the universal coordinate-change `AlgEquiv` for a `BaseChangeGroup` over any `CommRing`: [EndpointNormalization.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:219).

So define the section as a `BaseChangeGroup (k := SchurLoc …) d` whose endpoint units are the two block units above and whose interior units are `1`. Then instantiate `gaugeEquiv` with that universal gauge. This is the slicker route: it proves regularity by construction, as an algebra map over the localization.

Given this section, the set map is exactly as you wrote:

```text
Φ(A) = (mult A, σ(mult A)⁻¹ • A)
Ψ(B, A') = σ(B) • A'
```

and the codomain is `U_P × F`, not `U_P × (chart ∩ F)`. If `mult A ∈ U_P`, then

```text
mult (σ(mult A)⁻¹ • A) = E
```

by `mult_smul`, so the second component is in `F`. Conversely `mult (σ(B) • A') = B`. The existing equivariance facts are [FibreNormalForm.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:77) and [FibreNormalForm.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:87).

The `varietyDim` transport is the real Lean friction. `varietyDim` is set-level, defined as

```lean
(ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal k Z)).unbotD 0
```

at [NullstellensatzCodim.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:139). Once you already have a coordinate-ring `AlgEquiv`, dimension transport is cheap via `ringKrullDim_eq_of_ringEquiv`. But constructing that coordinate-ring equivalence from a “regular set iso” is not cheap unless you build a whole regular-map API.

I would add only the small intrinsic lemma:

```lean
abbrev coordRing (Z : Set (σ → k)) :=
  MvPolynomial σ k ⧸ vanishingIdeal k Z

lemma varietyDim_eq_of_coordRingEquiv
    (e : coordRing k Z ≃ₐ[k] coordRing k W) :
    varietyDim Z = varietyDim W := by
  unfold varietyDim coordRing
  rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
```

Then prove the specific chart coordinate-ring equivalence directly. Do not try to realize `U_P × F` as a subset of the same ambient `RepCoord d`; that hides the product algebra and still leaves you proving the same coordinate-ring statement.

The action-map route is not cheaper. It replaces an explicit pivot chart trivialization with a generic image-dimension theorem, product dimension for `H × F`, and a stabilizer/fibre-dimension computation. Those APIs are much farther from the current repo than the chart ring machinery. The chart route still has a product-dimension wall, but it is the concrete one:

```text
ringKrullDim (SchurLoc q p r ⊗[k] FibreAlg d E)
  = δ + ringKrullDim (FibreAlg d E)
```

which is a better target than a general quotient-by-group or generic-fibre theorem.

So: build the explicit universal section/gauge; transport by coordinate-ring `AlgEquiv`; keep the set-level `varietyDim` bridge small and specific.
tokens used
164,084
**Verdict:** yes, the regular section exists on the pivot chart, but in this repo the cheapest Lean shape is not a pointwise `σ : U_P → H`. Build the universal endpoint gauge over the localized chart ring and use its induced `AlgEquiv`.

For a rank-`r` target matrix on the top-left pivot chart, write

```text
B = [ A  C ]
    [ D  F ]
```

with `A` the invertible `r × r` pivot block. On rank `≤ r`, the Schur relation gives `F = D A⁻¹ C`. Then

```text
B =
[ A  0 ] · E · [ I  A⁻¹ C ]
[ D  I ]       [ 0    I    ]
```

so take

```text
σ_N(B) = [ A  0 ]
         [ D  I ]

σ_0(B) = [ I  -A⁻¹ C ]
         [ 0     I    ]
```

because `σ_0(B)⁻¹ = [I A⁻¹C; 0 I]`. Entries of `A⁻¹C` are `adj(A) C / det(A)`, hence regular on `D(det A)`. This is the standard pivot-cell section.

In Lean, avoid the existential `exists_baseChange_of_rank_eq`; it is the wrong object for regularity. The repo already has the right ingredients:

- `ΔPdeep` and `Sred = Localization.Away ΔPdeep ⧸ IadDeep` for the deep chart: [DeepChartRing.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:104).
- `basePresentationEquiv : A_loc/Iad ≃ₐ[k] SchurLoc`, so the base chart is already the Schur/free chart: [DeterminantalBasePresentation.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:378).
- `schurToSred` makes `Sred` a `SchurLoc`-algebra: [DeepChartRing.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:319).
- `gaugeEquiv` is already the universal coordinate-change `AlgEquiv` for a `BaseChangeGroup` over any `CommRing`: [EndpointNormalization.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:219).

So define the section as a `BaseChangeGroup (k := SchurLoc …) d` whose endpoint units are the two block units above and whose interior units are `1`. Then instantiate `gaugeEquiv` with that universal gauge. This is the slicker route: it proves regularity by construction, as an algebra map over the localization.

Given this section, the set map is exactly as you wrote:

```text
Φ(A) = (mult A, σ(mult A)⁻¹ • A)
Ψ(B, A') = σ(B) • A'
```

and the codomain is `U_P × F`, not `U_P × (chart ∩ F)`. If `mult A ∈ U_P`, then

```text
mult (σ(mult A)⁻¹ • A) = E
```

by `mult_smul`, so the second component is in `F`. Conversely `mult (σ(B) • A') = B`. The existing equivariance facts are [FibreNormalForm.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:77) and [FibreNormalForm.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:87).

The `varietyDim` transport is the real Lean friction. `varietyDim` is set-level, defined as

```lean
(ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal k Z)).unbotD 0
```

at [NullstellensatzCodim.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:139). Once you already have a coordinate-ring `AlgEquiv`, dimension transport is cheap via `ringKrullDim_eq_of_ringEquiv`. But constructing that coordinate-ring equivalence from a “regular set iso” is not cheap unless you build a whole regular-map API.

I would add only the small intrinsic lemma:

```lean
abbrev coordRing (Z : Set (σ → k)) :=
  MvPolynomial σ k ⧸ vanishingIdeal k Z

lemma varietyDim_eq_of_coordRingEquiv
    (e : coordRing k Z ≃ₐ[k] coordRing k W) :
    varietyDim Z = varietyDim W := by
  unfold varietyDim coordRing
  rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
```

Then prove the specific chart coordinate-ring equivalence directly. Do not try to realize `U_P × F` as a subset of the same ambient `RepCoord d`; that hides the product algebra and still leaves you proving the same coordinate-ring statement.

The action-map route is not cheaper. It replaces an explicit pivot chart trivialization with a generic image-dimension theorem, product dimension for `H × F`, and a stabilizer/fibre-dimension computation. Those APIs are much farther from the current repo than the chart ring machinery. The chart route still has a product-dimension wall, but it is the concrete one:

```text
ringKrullDim (SchurLoc q p r ⊗[k] FibreAlg d E)
  = δ + ringKrullDim (FibreAlg d E)
```

which is a better target than a general quotient-by-group or generic-fibre theorem.

So: build the explicit universal section/gauge; transport by coordinate-ring `AlgEquiv`; keep the set-level `varietyDim` bridge small and specific.
